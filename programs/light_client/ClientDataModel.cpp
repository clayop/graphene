#include "ClientDataModel.hpp"

#include <graphene/app/api.hpp>
#include <graphene/chain/protocol/protocol.hpp>

#include <fc/rpc/websocket_api.hpp>

#include <QMetaObject>

using namespace graphene::app;

template<typename T>
QString idToString(T id) {
   return QString("%1.%2.%3").arg(T::space_id).arg(T::type_id).arg(ObjectId(id.instance));
}
QString idToString(graphene::db::object_id_type id) {
   return QString("%1.%2.%3").arg(id.space(), id.type(), ObjectId(id.instance()));
}

ChainDataModel::ChainDataModel(fc::thread& t, QObject* parent)
:QObject(parent),m_rpc_thread(&t){}

Asset* ChainDataModel::getAsset(ObjectId id)
{
   auto& by_id_idx = m_assets.get<by_id>();
   auto itr = by_id_idx.find(id);
   if (itr == by_id_idx.end())
   {
      auto result = m_assets.insert(new Asset(id, QString::number(--m_account_query_num), 0, this));
      assert(result.second);

      // Run in RPC thread
      m_rpc_thread->async([this,id,result]{ getAssetImpl(idToString(asset_id_type(id)), &*result.first); });
      return *result.first;
   }
   return *itr;
}

Asset* ChainDataModel::getAsset(QString symbol)
{
   auto& by_symbol_idx = m_assets.get<by_symbol_name>();
   auto itr = by_symbol_idx.find(symbol);
   if (itr == by_symbol_idx.end())
   {
      auto result = m_assets.insert(new Asset(--m_account_query_num, symbol, 0, this));
      assert(result.second);

      // Run in RPC thread
      m_rpc_thread->async([this,symbol,result](){ getAssetImpl(symbol, &*result.first); });
      return *result.first;
   }
   return *itr;
}

void ChainDataModel::getAssetImpl(QString assetIdentifier, Asset* const * assetInContainer)
{
   try {
      ilog("Fetching asset ${asset}", ("asset", assetIdentifier.toStdString()));
      auto result = m_db_api->lookup_asset_symbols({assetIdentifier.toStdString()});

      // Run in main thread
      Q_EMIT queueExecute([this,result,assetInContainer](){
         ilog("Processing result ${r}", ("r", result));
         auto itr = m_assets.iterator_to(*assetInContainer);

         if (result.size() == 0 || !result.front()) {
            (*itr)->deleteLater();
            m_assets.erase(itr);
         } else {
            m_assets.modify(itr,
                            [=](Asset* a){
               a->setProperty("symbol", QString::fromStdString(result.front()->symbol));
               a->setProperty("id", ObjectId(result.front()->id.instance()));
               a->setProperty("precision", result.front()->precision);
            });
         }
      });
   }
   catch ( const fc::exception& e )
   {
      Q_EMIT exceptionThrown(QString::fromStdString(e.to_string()));
   }
}

void ChainDataModel::getAccountImpl(QString accountIdentifier, Account* const * accountInContainer)
{
   try {
      ilog("Fetching account ${acct}", ("acct", accountIdentifier.toStdString()));
      auto result = m_db_api->get_full_accounts([](const fc::variant& v) {
         idump((v));
      }, {accountIdentifier.toStdString()});
      fc::variant_object accountPackage;

      if (result.count(accountIdentifier.toStdString())) {
         accountPackage = result.begin()->second.as<variant_object>();

         // Fetch all necessary assets
         auto balances = accountPackage["balances"].as<vector<account_balance_object>>();
         QList<asset_id_type> assetsToFetch;
         QList<Asset* const *> assetPlaceholders;
         assetsToFetch.reserve(balances.size());
         // Get list of asset IDs the account has a balance in
         std::transform(balances.begin(), balances.end(), std::back_inserter(assetsToFetch),
                        [](const account_balance_object& b) { return b.asset_type; });
         auto function = [this,&assetsToFetch,&assetPlaceholders] {
            auto itr = assetsToFetch.begin();
            const auto& assets_by_id = m_assets.get<by_id>();
            // Filter out assets I already have, create placeholders for the ones I don't.
            while (itr != assetsToFetch.end()) {
               if (assets_by_id.count(itr->instance))
                  itr = assetsToFetch.erase(itr);
               else {
                  assetPlaceholders.push_back(&*m_assets.insert(new Asset(itr->instance, QString(), 0, this)).first);
                  ++itr;
               }
            }
         };
         QMetaObject::invokeMethod(parent(), "execute", Qt::BlockingQueuedConnection,
                                   Q_ARG(const std::function<void()>&, function));
         assert(assetsToFetch.size() == assetPlaceholders.size());

         // Blocking call to fetch and complete initialization for all the assets
         for (int i = 0; i < assetsToFetch.size(); ++i)
            getAssetImpl(idToString(assetsToFetch[i]), assetPlaceholders[i]);
      }

      // Run in main thread
      Q_EMIT queueExecute([this,accountPackage,accountInContainer](){
         ilog("Processing result ${r}", ("r", accountPackage));
         auto itr = m_accounts.iterator_to(*accountInContainer);

         if (!accountPackage.size()) {
            (*itr)->deleteLater();
            m_accounts.erase(itr);
         } else {
            m_accounts.modify(itr, [=](Account* a){
               account_object account = accountPackage["account"].as<account_object>();
               a->setProperty("id", ObjectId(account.id.instance()));
               a->setProperty("name", QString::fromStdString(account.name));

               // Set balances
               QList<Balance*> balances;
               auto balanceObjects = accountPackage["balances"].as<vector<account_balance_object>>();
               std::transform(balanceObjects.begin(), balanceObjects.end(), std::back_inserter(balances),
                              [this](const account_balance_object& b) {
                  Balance* bal = new Balance;
                  bal->setParent(this);
                  bal->setProperty("amount", QVariant::fromValue(b.balance.value));
                  bal->setProperty("type", QVariant::fromValue(getAsset(ObjectId(b.asset_type.instance))));
                  return bal;
               });
               a->setBalances(balances);
            });
         }
      });
   }
   catch (const fc::exception& e)
   {
      Q_EMIT exceptionThrown(QString::fromStdString(e.to_string()));
   }
}

Account* ChainDataModel::getAccount(ObjectId id)
{
   auto& by_id_idx = m_accounts.get<by_id>();
   auto itr = by_id_idx.find(id);
   if( itr == by_id_idx.end() )
   {
      auto tmp = new Account(id, tr("Account #%1").arg(--m_account_query_num), this);
      auto result = m_accounts.insert(tmp);
      assert(result.second);

      // Run in RPC thread
      m_rpc_thread->async([this, id, result]{getAccountImpl(idToString(account_id_type(id)), &*result.first);});
      return *result.first;
   }
   return *itr;
}

Account* ChainDataModel::getAccount(QString name)
{
   auto& by_name_idx = m_accounts.get<by_account_name>();
   auto itr = by_name_idx.find(name);
   if( itr == by_name_idx.end() )
   {
      auto tmp = new Account(--m_account_query_num, name, this);
      auto result = m_accounts.insert(tmp);
      assert(result.second);

      // Run in RPC thread
      m_rpc_thread->async([this, name, result]{getAccountImpl(name, &*result.first);});
      return *result.first;
   }
   return *itr;
}

QQmlListProperty<Balance> Account::balances()
{
   auto count = [](QQmlListProperty<Balance>* list) {
      return reinterpret_cast<Account*>(list->data)->m_balances.size();
   };
   auto at = [](QQmlListProperty<Balance>* list, int index) {
      return reinterpret_cast<Account*>(list->data)->m_balances[index];
   };

   return QQmlListProperty<Balance>(this, this, count, at);
}

GrapheneApplication::GrapheneApplication(QObject* parent)
:QObject(parent),m_thread("app")
{
   connect(this, &GrapheneApplication::queueExecute,
           this, &GrapheneApplication::execute);

   m_model = new ChainDataModel(m_thread, this);

   connect(m_model, &ChainDataModel::queueExecute,
           this, &GrapheneApplication::execute);

   connect(m_model, &ChainDataModel::exceptionThrown,
           this, &GrapheneApplication::exceptionThrown);
}

GrapheneApplication::~GrapheneApplication()
{
}

void GrapheneApplication::setIsConnected(bool v)
{
   if (v != m_isConnected)
   {
      m_isConnected = v;
      Q_EMIT isConnectedChanged(m_isConnected);
   }
}

void GrapheneApplication::start(QString apiurl, QString user, QString pass)
{
   if (!m_thread.is_current())
   {
      m_done = m_thread.async([=](){ return start(apiurl, user, pass); });
      return;
   }
   try {
      m_client = std::make_shared<fc::http::websocket_client>();
      ilog("connecting...${s}", ("s",apiurl.toStdString()));
      auto con = m_client->connect(apiurl.toStdString());
      m_connectionClosed = con->closed.connect([this]{queueExecute([this]{setIsConnected(false);});});
      auto apic = std::make_shared<fc::rpc::websocket_api_connection>(*con);
      auto remote_api = apic->get_remote_api<login_api>(1);
      auto db_api = apic->get_remote_api<database_api>(0);
      if (!remote_api->login(user.toStdString(), pass.toStdString()))
      {
         elog("login failed");
         Q_EMIT loginFailed();
         return;
      }

      ilog("connecting...");
      queueExecute([=](){
         m_model->setDatabaseAPI(db_api);
      });

      queueExecute([=](){ setIsConnected(true); });
   } catch (const fc::exception& e)
   {
      Q_EMIT exceptionThrown(QString::fromStdString(e.to_string()));
   }
}
Q_SLOT void GrapheneApplication::execute(const std::function<void()>& func)const
{
   func();
}
