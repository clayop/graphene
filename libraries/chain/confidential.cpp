#include <graphene/chain/confidential.hpp>
#include <graphene/chain/confidential_evaluator.hpp>
#include <graphene/chain/database.hpp>

namespace graphene { namespace chain {

account_id_type transfer_to_blind_operation::fee_payer()const
{
    return from;
}

void transfer_to_blind_operation::get_required_auth( flat_set<account_id_type>& active_auth_set, flat_set<account_id_type>& )const
{
    active_auth_set.insert( from );
}

void transfer_to_blind_operation::validate()const
{
   FC_ASSERT( fee.amount > 0 );
   FC_ASSERT( amount.amount > 0 );

   vector<commitment_type> in;
   vector<commitment_type> out(outputs.size());
   int64_t                 net_public = amount.amount.value;
   for( uint32_t i = 0; i < out.size(); ++i )
   {
      out[i] = outputs[i].commitment;
      /// require all outputs to be sorted prevents duplicates AND prevents implementations
      /// from accidentally leaking information by how they arrange commitments.
      if( i > 0 ) FC_ASSERT( out[i-1] < out[i] );
   }
   FC_ASSERT( out.size(), "there must be at least one output" );
   FC_ASSERT( fc::ecc::verify_sum( in, out, net_public ) );

   if( outputs.size() > 1 )
   {
      for( auto out : outputs )
      {
         auto info = fc::ecc::range_get_info( out.range_proof );
         FC_ASSERT( info.min_value >= 0 );
         FC_ASSERT( info.max_value <= GRAPHENE_MAX_SHARE_SUPPLY );
      }
   }
}

share_type transfer_to_blind_operation::calculate_fee( const fee_schedule_type& k )const
{
    return (fc::raw::pack_size(*this) * k.blind_data_fee)/1024;
}


account_id_type transfer_from_blind_operation::fee_payer()const
{
   return to;
}

void transfer_from_blind_operation::get_required_auth( flat_set<account_id_type>& active_auth_set, flat_set<account_id_type>& )const
{
   active_auth_set.insert( fee_payer() );
}

void transfer_from_blind_operation::validate()const
{
   FC_ASSERT( amount.amount > 0 );
   FC_ASSERT( fee.amount > 0 );
   FC_ASSERT( inputs.size() > 0 );
   FC_ASSERT( amount.asset_id == fee.asset_id );


   vector<commitment_type> in(inputs.size());
   vector<commitment_type> out;
   int64_t                 net_public = -fee.amount.value - amount.amount.value;
   for( uint32_t i = 0; i < in.size(); ++i )
   {
      in[i] = inputs[i].commitment;
      /// by requiring all inputs to be sorted we also prevent duplicate commitments on the input
      if( i > 0 ) FC_ASSERT( in[i-1] < in[i] );
   }
   FC_ASSERT( in.size(), "there must be at least one input" );
   FC_ASSERT( fc::ecc::verify_sum( in, out, net_public ) );
}

share_type transfer_from_blind_operation::calculate_fee( const fee_schedule_type& k )const
{
    return (fc::raw::pack_size(*this) * k.blind_data_fee)/1024;
}

/**
 *  If fee_payer = temp_account_id, then the fee is paid by the surplus balance of inputs-outputs and
 *  100% of the fee goes to the network.
 */
account_id_type blind_transfer_operation::fee_payer()const
{
   return GRAPHENE_TEMP_ACCOUNT;
}

void blind_transfer_operation::get_required_auth( flat_set<account_id_type>& active_auth_set, flat_set<account_id_type>& )const
{
   active_auth_set.insert( fee_payer() );
}

/**
 *  This method can be computationally intensive because it verifies that input commitments - output commitments add up to 0
 */
void blind_transfer_operation::validate()const
{ try {
   vector<commitment_type> in(inputs.size());
   vector<commitment_type> out(outputs.size());
   int64_t                 net_public = -fee.amount.value;//from_amount.value - to_amount.value;
   for( uint32_t i = 0; i < in.size(); ++i )
   {
      in[i] = inputs[i].commitment;
      /// by requiring all inputs to be sorted we also prevent duplicate commitments on the input
      if( i > 0 ) FC_ASSERT( in[i-1] < in[i] );
   }
   for( uint32_t i = 0; i < out.size(); ++i )
   {
      out[i] = outputs[i].commitment;
      if( i > 0 ) FC_ASSERT( out[i-1] < out[i] );
   }
   FC_ASSERT( in.size(), "there must be at least one input" );
   FC_ASSERT( fc::ecc::verify_sum( in, out, net_public ) );

   if( outputs.size() > 1 )
   {
      for( auto out : outputs )
      {
         auto info = fc::ecc::range_get_info( out.range_proof );
         FC_ASSERT( info.min_value >= 0 );
         FC_ASSERT( info.max_value <= GRAPHENE_MAX_SHARE_SUPPLY );
      }
   }
} FC_CAPTURE_AND_RETHROW( (*this) ) }

share_type blind_transfer_operation::calculate_fee( const fee_schedule_type& k )const
{
    return (fc::raw::pack_size(*this) * k.blind_data_fee)/1024;
}






void_result transfer_to_blind_evaluator::do_evaluate( const transfer_to_blind_operation& o )
{ try {
   const auto& d = db();

   const auto& atype = o.fee.asset_id(db());  // verify fee is a legit asset 
   FC_ASSERT( atype.allow_confidential() );
   FC_ASSERT( !atype.is_transfer_restricted() );
   FC_ASSERT( !atype.enforce_white_list() );

   for( const auto& out : o.outputs )
   {
      for( const auto& a : out.owner.account_auths )
         a.first(d); // verify all accounts exist and are valid
   }
   return void_result();
} FC_CAPTURE_AND_RETHROW( (o) ) }


void_result transfer_to_blind_evaluator::do_apply( const transfer_to_blind_operation& o ) 
{ try {
   db().adjust_balance( o.from, -o.amount ); 

   for( const auto& out : o.outputs )
   {
      db().create<blinded_balance_object>( [&]( blinded_balance_object& obj ){
          obj.asset_id   = o.amount.asset_id;
          obj.owner      = out.owner;
          obj.commitment = out.commitment;
      });
   }
   return void_result();
} FC_CAPTURE_AND_RETHROW( (o) ) }


void_result transfer_from_blind_evaluator::do_evaluate( const transfer_from_blind_operation& o )
{ try {
   const auto& d = db();
   o.fee.asset_id(d);  // verify fee is a legit asset 
   const auto& bbi = d.get_index_type<blinded_balance_index>();
   const auto& cidx = bbi.indices().get<by_commitment>();
   for( const auto& in : o.inputs )
   {
      auto itr = cidx.find( in.commitment );
      FC_ASSERT( itr != cidx.end() );
      FC_ASSERT( itr->asset_id == o.fee.asset_id );
      FC_ASSERT( itr->owner == in.owner );
   }
   return void_result();
} FC_CAPTURE_AND_RETHROW( (o) ) }

void_result transfer_from_blind_evaluator::do_apply( const transfer_from_blind_operation& o ) 
{ try {
   db().adjust_balance( o.fee_payer(), o.amount ); 
   const auto& bbi = db().get_index_type<blinded_balance_index>();
   const auto& cidx = bbi.indices().get<by_commitment>();
   for( const auto& in : o.inputs )
   {
      auto itr = cidx.find( in.commitment );
      FC_ASSERT( itr != cidx.end() );
      db().remove( *itr );
   }
   return void_result();
} FC_CAPTURE_AND_RETHROW( (o) ) }





void_result blind_transfer_evaluator::do_evaluate( const blind_transfer_operation& o )
{ try {
   const auto& d = db();
   o.fee.asset_id(db());  // verify fee is a legit asset 
   const auto& bbi = db().get_index_type<blinded_balance_index>();
   const auto& cidx = bbi.indices().get<by_commitment>();
   for( const auto& out : o.outputs )
   {
      for( const auto& a : out.owner.account_auths )
         a.first(d); // verify all accounts exist and are valid
   }
   for( const auto& in : o.inputs )
   {
      auto itr = cidx.find( in.commitment );
      FC_ASSERT( itr != cidx.end() );
      FC_ASSERT( itr->asset_id == o.fee.asset_id );
      FC_ASSERT( itr->owner == in.owner );
   }
   return void_result();
} FC_CAPTURE_AND_RETHROW( (o) ) }

void_result blind_transfer_evaluator::do_apply( const blind_transfer_operation& o ) 
{ try {
   db().adjust_balance( o.fee_payer(), o.fee ); // deposit the fee to the temp account
   const auto& bbi = db().get_index_type<blinded_balance_index>();
   const auto& cidx = bbi.indices().get<by_commitment>();
   for( const auto& in : o.inputs )
   {
      auto itr = cidx.find( in.commitment );
      FC_ASSERT( itr != cidx.end() );
      db().remove( *itr );
   }
   for( const auto& out : o.outputs )
   {
      db().create<blinded_balance_object>( [&]( blinded_balance_object& obj ){
          obj.asset_id   = o.fee.asset_id;
          obj.owner      = out.owner;
          obj.commitment = out.commitment;
      });
   }
   return void_result();
} FC_CAPTURE_AND_RETHROW( (o) ) }


} } // graphene::chain
