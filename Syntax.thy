(******
Syntax for Yul language
Copyright (C) 2020  Ning Han, Ximeng Li

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Library General Public
License as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Library General Public License for more details.
******)

theory "Syntax" 

imports 
  Main
  "$ISABELLE_HOME/src/HOL/Word/Word"
  (*"./utils/Keccak"  *)

begin 
 
type_synonym id0 = int

datatype type_name =
    Bool
  | S256
  | S128
  | S64
  | S32
  | S8
  | U256
  | U128
  | U64
  | U32
  | U8
  | Address160

datatype lit_content =
    TrueLiteral                   ("TL")
  | FalseLiteral                  ("FL")
  | StringLiteral "(8 word) list" ("SL _" [100] 100)
  | NumberLiteral int             ("NL _" [100] 100)


datatype literal = 
  Literal "lit_content" "type_name"            ("(_ :L _)" [100, 100] 100)

datatype 
    block = Blk "expr list"                     ("BEGIN/ _/ END" [60] 60)
and expr =
    EId id0                                     ("ID _" [0] 1000)
  | ELit literal                            ("LIT _" [0] 1000)
  | EFunCall id0 "expr list"                ("CALL _/ _" [1000, 62] 62)
  | EFunDef id0 "(id0 * type_name) list" "(id0 * type_name) list" block  
                                                ("FUN _/ _/ _ IS/ _" [1000, 61, 61] 61)
  | EVarDecl "(id0 * type_name) list" expr      ("VAR _ ::-/ _" [0, 61] 61)
  | EEmptyVarDecl "(id0 * type_name) list"      ("VAR _" [0] 61) 
  | EAssg "id0 list" expr                       ("_ ::=/ _" [0, 61] 61) 
  | EIf expr block                              ("(IF _/ THEN/ _)" [0, 61] 61)
  | ESwitch expr "(literal * block) list" "block option"  
                                                ("(SWITCH _/ CASES/ _/ DEFAULT/ _)" [0, 61, 61] 61) 
  | EFor block expr block block                 ("(FOR/ _/ _/ _/ _)" [61, 61, 61, 61] 61)
  | EStop                                       ("STOP") 
  | EImLit literal
  | EImFunCall id0 "expr list"                    
  | EGasJumpDest                                ("GJUMPDEST") 
  | EGasPush                                    ("GPUSH")
  | EGasJump                                    ("GJUMP")
  | EGasPop                                     ("GPOP")
  | EGasSwap                                    ("GSWAP")
  | ECond expr block                            ("(COND _/ _)" [0, 61] 61)
  | ERetId "(id0 * type_name)"                  
  | EList "expr list"         


(* IDs FOR BUILTIN FUNCTIONS *)
(*bi-operation*)
datatype opbuiltin =
  Convert " type_name " " type_name "
  (* functions for arithmetic and bitwise bi-operations *) 
  | Add
  | Sub 
  | Mul
  | SDiv
  | Div
  | Mod
  | SMod
  | Exp
  | And
  | Or
  | Xor
    (* functions for comparison *)
  | Lt
  | SLt
  | Gt
  | SGt
  | Eq 
  | Shl
  | Shr
  | Sar
    (* functions for logical bi-operations *) 
  | LAnd
  | LOr
  | LXor
  | Byte
  | Signextend
  | LNot 
  | Not
  | IsZero   
  | AddMod
  | MulMod


datatype callbuiltin = 
     Call
    | CallCode
    | DelegateCall
    | Return
    | Revert
    | Selfdestruct
    | Stop
    | Invalid
  

(*other*)
datatype rbuiltin =
    MSize
  | Gas
  | Balance
  | Address

  | CalldataSize
  | Keccak256 
  | Callvalue
  | Caller
  | Create
  | CodeSize
  | ExtCodeSize

  | MLoad
  | SLoad
  | CalldataLoad

datatype hdrbuiltin =
   Difficulty
  | Number
  | Timestamp
  | CoinBase
  | GasLimit
  | GasPrice
  | Origin

datatype wbuiltin =
   MStore
  | MStore8
  | SStore
  | Log " nat " 
  | Pop
  | CalldataCopy
(* IDs for built-in functions for logical/arithmetic operations *) 

definition b_lnot_id :: id0 where "b_lnot_id = 1" 
definition b_land_id :: id0 where "b_land_id = 2" 
definition b_lor_id :: id0 where "b_lor_id = 3" 
definition b_lxor_id :: id0 where "b_lxor_id = 4" 

definition b_add_id :: id0 where "b_add_id = 11" 
definition b_sub_id :: id0 where "b_sub_id = 12"
definition b_mul_id :: id0 where "b_mul_id = 13" 
definition b_div_id :: id0 where "b_div_id = 14"
definition b_sdiv_id :: id0 where "b_sdiv_id = 15"
definition b_mod_id :: id0 where "b_mod_id = 16"
definition b_smod_id :: id0 where "b_smod_id = 17" 
definition b_signextend_id :: id0 where "b_signextend_id = 18" 
definition b_exp_id :: id0 where "b_exp_id = 19" 
definition b_addmod_id :: id0 where "b_addmod_id = 20"
definition b_mulmod_id :: id0 where "b_mulmod_id = 21" 
definition b_lt_id :: id0 where "b_lt_id = 22"
definition b_gt_id :: id0 where "b_gt_id = 23" 
definition b_slt_id :: id0 where "b_slt_id = 24"
definition b_sgt_id :: id0 where "b_sgt_id = 25" 
definition b_eq_id :: id0 where "b_eq_id = 26"
definition b_iszero_id :: id0 where "b_iszero_id = 27"

definition b_not_id :: id0 where "b_not_id = 28" 
definition b_and_id :: id0 where "b_and_id = 29"
definition b_or_id :: id0 where "b_or_id = 30"
definition b_xor_id :: id0 where "b_xor_id = 31" 
(* definition b_shl_id *) (* definition b_shr_id *) 
definition b_shl_id :: id0 where "b_shl_id = 32"
definition b_shr_id :: id0 where "b_shr_id = 33"
definition b_byte_id :: id0 where "b_byte_id = 34"
definition b_sar_id :: id0 where "b_sar_id = 35"


(* IDs for built-in functions for memory and storage operations *) 

definition b_mload_id :: id0 where "b_mload_id = 51" 
definition b_mstore_id :: id0 where "b_mstore_id = 52"
definition b_mstore8_id :: id0 where "b_mstore8_id = 53" 
definition b_sload_id :: id0 where "b_sload_id = 54" 
definition b_sstore_id :: id0 where "b_sstore_id = 55" 
definition b_msize_id :: id0 where "b_msize_id = 56" 

(* IDs for built-in functions for execution control *)

definition b_create_id :: id0 where "b_create_id = 101" 
(* definition b_create2_id *) 
definition b_call_id :: id0 where "b_call_id = 103" 
definition b_callcode_id :: id0 where "b_callcode_id = 104" 
definition b_delegatecall_id :: id0 where "b_delegatecall_id = 105" 
definition b_abort_id :: id0 where "b_abort_id = 106"  (* INVALID of Eth *)
definition b_return_id :: id0 where "b_return_id = 107" 
definition b_revert_id :: id0 where "b_revert_id = 108" 
definition b_selfdestruct_id :: id0 where "b_selfdestruct_id = 109" 
definition b_log0_id :: id0 where "b_log0_id = 110" 
definition b_log1_id :: id0 where "b_log1_id = 111" 
definition b_log2_id :: id0 where "b_log2_id = 112"
definition b_log3_id :: id0 where "b_log3_id = 113" 
definition b_log4_id :: id0 where "b_log4_id = 114" 

(* IDs for built-in functions for state queries *) 

definition b_coinbase_id :: id0 where "b_coinbase_id = 150" 
definition b_difficulty_id :: id0 where "b_difficulty_id = 151" 
definition b_gaslimit_id :: id0 where "b_gaslimit_id = 152" 
definition b_blockhash_id :: id0 where "b_blockhash_id = 153" 
definition b_number_id :: id0 where "b_number_id = 154"  (* NUMBER of Eth *)
definition b_timestamp_id :: id0 where "b_timestamp_id = 155" 
definition b_origin_id :: id0 where "b_origin_id = 156" 
definition b_gasprice_id :: id0 where "b_gasprice_id = 157" 
definition b_gas_id :: id0 where "b_gas_id = 158"
definition b_balance_id :: id0 where "b_balance_id = 159" 
definition b_this_id :: id0 where "b_this_id = 160" 
definition b_caller_id :: id0 where "b_caller_id = 161" 
definition b_callvalue_id :: id0 where "b_callvalue_id = 162" 
definition b_calldataload_id :: id0 where "b_calldataload_id = 163" 
definition b_calldatasize_id :: id0 where "b_calldatasize_id = 164"  
definition b_calldatacopy_id :: id0 where "b_calldatacopy_id = 165" 
definition b_codesize_id :: id0 where "b_codesize_id = 166" 
definition b_codecopy_id :: id0 where "b_codecopy_id = 167" 
definition b_codehash_id :: id0 where "b_codehash_id = 168" 
definition b_extcodesize_id :: id0 where "b_extcodesize_id = 169" 
definition b_address_id :: id0 where "b_address_id = 170"

(* definition b_discard_id *) (* definition b_discardu256_id *) 
(* definition b_splitu256tou64_id *) (* definition b_combineu64tou256_id *)
definition b_keccak256_id :: id0 where "b_keccak256_id = 204" 
definition b_pop_id :: id0 where "b_pop_id = 205" 
definition b_stop_id :: id0 where "b_stop_id = 206" 
definition b_invalid_id :: id0 where "b_invalid_id = 207" 
(* IDs for built-in functions for object access *) 

definition b_datasize_id :: id0 where "b_datasize_id = 250" 
definition b_dataoffset_id :: id0 where "b_dataoffset_id = 251" 
definition b_datacopy_id :: id0 where "b_datacopy_id = 252" 

end
