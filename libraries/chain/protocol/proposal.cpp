/* Copyright (C) Cryptonomex, Inc - All Rights Reserved **/
#include <graphene/chain/protocol/operations.hpp>
#include <graphene/chain/protocol/fee_schedule.hpp>

namespace graphene { namespace chain {

proposal_create_operation proposal_create_operation::committee_proposal(const chain_parameters& global_params, fc::time_point_sec head_block_time )
{
   proposal_create_operation op;
   op.expiration_time = head_block_time + global_params.maximum_proposal_lifetime;
   op.review_period_seconds = global_params.committee_proposal_review_period;
   return op;
}

void proposal_create_operation::validate() const
{
   FC_ASSERT( !proposed_ops.empty() );
   for( const auto& op : proposed_ops ) operation_validate( op.op );
}

share_type proposal_create_operation::calculate_fee(const fee_parameters_type& k) const
{
   return k.fee + calculate_data_fee( fc::raw::pack_size(*this), k.price_per_kbyte );
}

void proposal_update_operation::validate() const
{
   FC_ASSERT(fee.amount >= 0);
   FC_ASSERT(!(active_approvals_to_add.empty() && active_approvals_to_remove.empty() &&
               owner_approvals_to_add.empty() && owner_approvals_to_remove.empty() &&
               key_approvals_to_add.empty() && key_approvals_to_remove.empty()));
   for( auto a : active_approvals_to_add )
   {
      FC_ASSERT(active_approvals_to_remove.find(a) == active_approvals_to_remove.end(),
                "Cannot add and remove approval at the same time.");
   }
   for( auto a : owner_approvals_to_add )
   {
      FC_ASSERT(owner_approvals_to_remove.find(a) == owner_approvals_to_remove.end(),
                "Cannot add and remove approval at the same time.");
   }
   for( auto a : key_approvals_to_add )
   {
      FC_ASSERT(key_approvals_to_remove.find(a) == key_approvals_to_remove.end(),
                "Cannot add and remove approval at the same time.");
   }
}

void proposal_delete_operation::validate() const
{
   FC_ASSERT( fee.amount >= 0 );
}

share_type proposal_update_operation::calculate_fee(const fee_parameters_type& k) const
{
   return k.fee + calculate_data_fee( fc::raw::pack_size(*this), k.price_per_kbyte );
}
void proposal_create_operation::get_impacted_accounts( flat_set<account_id_type>& i )const
{
   vector<authority> other;
   for( const auto& op : proposed_ops )
      operation_get_required_authorities( op.op, i, i, other );
   for( auto& o : other )
      add_authority_accounts( i, o );
}

void proposal_update_operation::get_required_authorities( vector<authority>& o )const
{
   authority auth;
   for( const auto& k : key_approvals_to_add )
      auth.key_auths[k] = 1;
   for( const auto& k : key_approvals_to_remove )
      auth.key_auths[k] = 1;
   auth.weight_threshold = auth.key_auths.size();

   o.emplace_back( std::move(auth) );
}
void proposal_update_operation::get_required_active_authorities( flat_set<account_id_type>& a )const
{
   for( const auto& i : active_approvals_to_add )    a.insert(i);
   for( const auto& i : active_approvals_to_remove ) a.insert(i);
}
void proposal_update_operation::get_required_owner_authorities( flat_set<account_id_type>& a )const
{
   for( const auto& i : owner_approvals_to_add )    a.insert(i);
   for( const auto& i : owner_approvals_to_remove ) a.insert(i);
}
} } // graphene::chain
