#pragma once

#include <graphene/chain/account_object.hpp>

namespace graphene { namespace app {
   using namespace graphene::chain;

   struct full_account
   {
      account_object                   account;
      account_statistics_object        statistics;
      string                           registrar_name;
      string                           referrer_name;
      string                           lifetime_referrer_name;
      optional<vesting_balance_object> cashback_balance;
      vector<account_balance_object>   balances;
      vector<vesting_balance_object>   vesting_balances;
      vector<limit_order_object>       limit_orders;
      vector<call_order_object>        call_orders;
   };

} }

FC_REFLECT( graphene::app::full_account, 
            (account)
            (statistics)
            (registrar_name)
            (referrer_name)
            (lifetime_referrer_name)
            (cashback_balance)
            (balances)
            (vesting_balances)
            (limit_orders)
            (call_orders) )
