(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*    Louis-Emile Ploix                                                     *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Libsail

open Ast
open Ast_util
open Jib
open Jib_compile
open Jib_util
open Value2
open PPrint
open Printf
open Smt_exp
open Jib_smt

open Generate_primop

type verilate_mode = Verilator_none | Verilator_compile | Verilator_run

let opt_verilate = ref Verilator_none

let opt_line_directives = ref false

(* FIXME: Add these to SMT *)
let verilog_options =
  [
    ( "-sv_verilate",
      Arg.String
        (fun opt ->
          if opt = "run" then opt_verilate := Verilator_run
          else if opt = "compile" then opt_verilate := Verilator_compile
          else
            raise
              (Reporting.err_general Parse_ast.Unknown
                 "Invalid argument for -sv_verilate option. Valid options are either 'run' or 'compile'."
              )
        ),
      "<compile|run> Invoke verilator on generated output"
    );
    ("-sv_lines", Arg.Set opt_line_directives, " output `line directives");
  ]

let verilog_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "c"]);
    ("realize_mappings", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("truncate_hex_literals", []);
    ("mono_rewrites", [If_flag opt_mono_rewrites]);
    ("recheck_defs", [If_flag opt_mono_rewrites]);
    ("toplevel_nexps", [If_mono_arg]);
    ("monomorphise", [String_arg "c"; If_mono_arg]);
    ("atoms_to_singletons", [String_arg "c"; If_mono_arg]);
    ("recheck_defs", [If_mono_arg]);
    ("undefined", [Bool_arg false]);
    ("vector_string_pats_to_bit_list", []);
    ("remove_not_pats", []);
    ("remove_vector_concat", []);
    ("remove_bitvector_pats", []);
    ("pattern_literals", [Literal_arg "all"]);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_struct_assignments", []);
    ("exp_lift_assign", []);
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("constant_fold", [String_arg "c"]);
  ]

module Verilog_config : Jib_compile.Config = struct
  open Type_check
  open Jib_compile

  let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
  let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

  let rec convert_typ ctx typ =
    let (Typ_aux (typ_aux, l) as typ) = Env.expand_synonyms ctx.local_env typ in
    match typ_aux with
    | Typ_id id when string_of_id id = "bit" -> CT_bit
    | Typ_id id when string_of_id id = "bool" -> CT_bool
    | Typ_id id when string_of_id id = "int" -> CT_lint
    | Typ_id id when string_of_id id = "nat" -> CT_lint
    | Typ_id id when string_of_id id = "unit" -> CT_unit
    | Typ_id id when string_of_id id = "string" -> CT_string
    | Typ_id id when string_of_id id = "real" -> CT_real
    | Typ_id id when string_of_id id = "float16" -> CT_float 16
    | Typ_id id when string_of_id id = "float32" -> CT_float 32
    | Typ_id id when string_of_id id = "float64" -> CT_float 64
    | Typ_id id when string_of_id id = "float128" -> CT_float 128
    | Typ_id id when string_of_id id = "float_rounding_mode" -> CT_rounding_mode
    | Typ_app (id, _) when string_of_id id = "atom_bool" -> CT_bool
    | Typ_app (id, args) when string_of_id id = "itself" -> convert_typ ctx (Typ_aux (Typ_app (mk_id "atom", args), l))
    | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" || string_of_id id = "implicit" ->
      begin
        match destruct_range Env.empty typ with
        | None -> assert false (* Checked if range type in guard *)
        | Some (kids, constr, n, m) -> (
            let ctx =
              {
                ctx with
                local_env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env;
              }
            in
            match (nexp_simp n, nexp_simp m) with
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _) when Big_int.equal n m -> CT_constant n
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
              when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
                CT_fint 64
            | n, m ->
                if
                  prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n)
                  && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64)))
                then CT_fint 64
                else CT_lint
          )
      end
    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> CT_list (ctyp_suprema (convert_typ ctx typ))
    (* When converting a sail bitvector type into C, we have three options in order of efficiency:
       - If the length is obviously static and smaller than 64, use the fixed bits type (aka uint64_t), fbits.
       - If the length is less than 64, then use a small bits type, sbits.
       - If the length may be larger than 64, use a large bits type lbits. *)
    | Typ_app (id, [A_aux (A_nexp n, _); A_aux (A_order _, _)]) when string_of_id id = "bitvector" ->
        let direction = true in
        (* match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in *)
        begin
          match solve_unique ctx.local_env n with
          | Some n -> CT_fbits (Big_int.to_int n, direction)
          | _ -> CT_lbits direction
        end
    | Typ_app (id, [A_aux (A_nexp n, _); A_aux (A_order _, _); A_aux (A_typ typ, _)]) when string_of_id id = "vector" ->
        let direction = true in
        (* let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in *)
        begin
          match nexp_simp n with
          | Nexp_aux (Nexp_constant c, _) -> CT_fvector (Big_int.to_int c, direction, convert_typ ctx typ)
          | _ -> CT_vector (direction, convert_typ ctx typ)
        end
    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "register" -> CT_ref (convert_typ ctx typ)
    | Typ_id id when Bindings.mem id ctx.records ->
        CT_struct (id, Bindings.find id ctx.records |> snd |> Bindings.bindings)
    | Typ_app (id, typ_args) when Bindings.mem id ctx.records ->
        let typ_params, fields = Bindings.find id ctx.records in
        let quants =
          List.fold_left2
            (fun quants typ_param typ_arg ->
              match typ_arg with
              | A_aux (A_typ typ, _) -> KBindings.add typ_param (convert_typ ctx typ) quants
              | _ -> Reporting.unreachable l __POS__ "Non-type argument for record here should be impossible"
            )
            ctx.quants typ_params (List.filter is_typ_arg_typ typ_args)
        in
        let fix_ctyp ctyp = if is_polymorphic ctyp then ctyp_suprema (subst_poly quants ctyp) else ctyp in
        CT_struct (id, Bindings.map fix_ctyp fields |> Bindings.bindings)
    | Typ_id id when Bindings.mem id ctx.variants ->
        CT_variant (id, Bindings.find id ctx.variants |> snd |> Bindings.bindings)
    | Typ_app (id, typ_args) when Bindings.mem id ctx.variants ->
        let typ_params, ctors = Bindings.find id ctx.variants in
        let quants =
          List.fold_left2
            (fun quants typ_param typ_arg ->
              match typ_arg with
              | A_aux (A_typ typ, _) -> KBindings.add typ_param (convert_typ ctx typ) quants
              | _ -> Reporting.unreachable l __POS__ "Non-type argument for variant here should be impossible"
            )
            ctx.quants typ_params (List.filter is_typ_arg_typ typ_args)
        in
        let fix_ctyp ctyp = if is_polymorphic ctyp then ctyp_suprema (subst_poly quants ctyp) else ctyp in
        CT_variant (id, Bindings.map fix_ctyp ctors |> Bindings.bindings)
    | Typ_id id when Bindings.mem id ctx.enums -> CT_enum (id, Bindings.find id ctx.enums |> IdSet.elements)
    | Typ_tuple typs -> CT_tup (List.map (convert_typ ctx) typs)
    | Typ_exist _ -> begin
        (* Use Type_check.destruct_exist when optimising with SMT, to
           ensure that we don't cause any type variable clashes in
           local_env, and that we can optimize the existential based
           upon it's constraints. *)
        match destruct_exist (Env.expand_synonyms ctx.local_env typ) with
        | Some (kids, nc, typ) ->
            let env = add_existential l kids nc ctx.local_env in
            convert_typ { ctx with local_env = env } typ
        | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
      end
    | Typ_var kid -> CT_poly kid
    | _ -> Reporting.unreachable l __POS__ ("No C type for type " ^ string_of_typ typ)

  let optimize_anf _ aexp = aexp

  let unroll_loops = None
  let specialize_calls = false
  let ignore_64 = true
  let struct_value = false
  let tuple_value = false
  let track_throw = true
  let branch_coverage = None
  let use_real = false
end

let variable_decls_to_top instrs =
  let decls, others =
    List.fold_left
      (fun (decls, others) instr ->
        match instr with
        | I_aux (I_decl (ctyp, id), (_, l)) -> (idecl l ctyp id :: decls, others)
        | I_aux (I_init (ctyp, id, cval), (_, l)) ->
            (idecl l ctyp id :: decls, icopy l (CL_id (id, ctyp)) cval :: others)
        | other -> (decls, other :: others)
      )
      ([], []) instrs
  in
  List.rev decls @ List.rev others

type function_footprint = { register_reads : IdSet.t; register_writes : IdSet.t }

let rec instr_footprint (I_aux (aux, _)) = ()

and instrs_footprint instrs = ()

let max_integer_width = 128

let sv_reserved_words =
  [
    "accept_on";
    "alias";
    "always_comb";
    "always_if";
    "always_latch";
    "assert";
    "assume";
    "automatic";
    "before";
    "bind";
    "bins";
    "binsof";
    "bit";
    "break";
    "byte";
    "chandle";
    "checker";
    "class";
    "clocking";
    "config";
    "const";
    "constraint";
    "context";
    "continue";
    "cover";
    "covergroup";
    "cross";
    "dist";
    "do";
    "endchecker";
    "endclass";
    "endclocking";
    "endfunction";
    "endinterface";
    "endpackage";
    "endprogram";
    "endproperty";
    "endsequence";
    "enum";
    "eventually";
    "expect";
    "export";
    "extends";
    "extern";
    "final";
    "first_match";
    "foreach";
    "forkjoin";
    "global";
    "iff";
    "ignore_bins";
    "illegal_bins";
    "implies";
    "import";
    "inside";
    "int";
    "interface";
    "intersect";
    "join_any";
    "join_none";
    "let";
    "local";
    "logic";
    "longint";
    "matches";
    "modport";
    "new";
    "nexttime";
    "null";
    "package";
    "packed";
    "priority";
    "program";
    "property";
    "protected";
    "pure";
    "rand";
    "randc";
    "randcase";
    "randsequence";
    "reg";
    "reject_on";
    "ref";
    "restrict";
    "return";
    "s_always";
    "s_eventually";
    "s_nexttime";
    "s_until";
    "s_until_with";
    "sequence";
    "shortint";
    "solve";
    "static";
    "string";
    "strong";
    "struct";
    "super";
    "sync_accept_on";
    "sync_reject_on";
    "tagged";
    "this";
    "throughout";
    "timeprecision";
    "timeunit";
    "type";
    "typedef";
    "union";
    "unique";
    "unique0";
    "until";
    "until_with";
    "untyped";
    "var";
    "virtual";
    "void";
    "wait_order";
    "weak";
    "wildcard";
    "with";
    "within";
  ]
  |> StringSet.of_list

let valid_sv_identifier_regexp : Str.regexp option ref = ref None

let valid_sv_identifier s =
  let regexp =
    match !valid_sv_identifier_regexp with
    | Some regexp -> regexp
    | None ->
        let regexp = Str.regexp "^[A-Za-z_][A-Za-z0-9_]*$" in
        valid_sv_identifier_regexp := Some regexp;
        regexp
  in
  Str.string_match regexp s 0

let sv_id_string id =
  let s = string_of_id id in
  if valid_sv_identifier s && not (StringSet.mem s sv_reserved_words) then s else Util.zencode_string s

let sv_id id = string (sv_id_string id)

let sv_name = function
  | Name (id, _) -> sv_id id
  | Global (id, _) -> sv_id id
  | Have_exception _ -> string "sail_have_exception"
  | Current_exception _ -> string "sail_current_exception"
  | Throw_location _ -> string "sail_throw_location"
  | Return _ -> string "sail_return"

let rec is_packed = function
  | CT_fbits _ | CT_unit | CT_bit | CT_bool | CT_fint _ | CT_lbits _ | CT_lint | CT_enum _ | CT_constant _ -> true
  | CT_variant (_, ctors) -> List.for_all (fun (_, ctyp) -> is_packed ctyp) ctors
  | CT_struct (_, fields) -> List.for_all (fun (_, ctyp) -> is_packed ctyp) fields
  | _ -> false

let rec sv_smt_ctyp = function
  | Smtlib.Bitvec width -> ksprintf string "logic [%d:0]" (width - 1)
  | Bool -> string "bit"
  | String -> string "string"
  | Real -> string "real"
  | Datatype (nm, _) when nm = "Unit" -> string "sail_unit"
  | Datatype (nm, _) -> string nm
  | Tuple _ -> failwith "tuple"
  | Array _ -> failwith "array"

let rec sv_ctyp = function
  | CT_bool -> string "bit"
  | CT_bit -> string "logic"
  | CT_fbits (width, is_dec) ->
      if is_dec then ksprintf string "logic [%d:0]" (width - 1) else ksprintf string "logic [0:%d]" (width - 1)
  | CT_sbits (max_width, is_dec) ->
      let logic = if is_dec then sprintf "logic [%d:0]" (max_width - 1) else sprintf "logic [0:%d]" (max_width - 1) in
      ksprintf string "struct packed { logic [7:0] size; %s bits; }" logic
  | CT_lbits _ -> string "sail_bits"
  | CT_fint width -> ksprintf string "logic [%d:0]" (width - 1)
  | CT_lint -> ksprintf string "logic [%d:0]" (max_integer_width - 1)
  | CT_string -> string "string"
  | CT_unit -> string "sail_unit"
  | CT_variant (id, _) | CT_struct (id, _) | CT_enum (id, _) -> sv_id id
  | CT_constant c ->
      let width = required_width c in
      ksprintf string "logic [%d:0]" (width - 1)
  | _ -> empty

let sv_ctyp_default = function CT_bool -> string "0" | CT_bit -> string "1'bX" | _ -> string "DEFAULT"

let sv_type_def = function
  | CTD_enum (id, ids) ->
      string "typedef" ^^ space ^^ string "enum" ^^ space
      ^^ group (lbrace ^^ nest 4 (hardline ^^ separate_map (comma ^^ hardline) sv_id ids) ^^ hardline ^^ rbrace)
      ^^ space ^^ sv_id id ^^ semi
  | CTD_struct (id, fields) ->
      let sv_field (id, ctyp) = sv_ctyp ctyp ^^ space ^^ sv_id id in
      let can_be_packed = List.for_all (fun (_, ctyp) -> is_packed ctyp) fields in
      string "typedef" ^^ space ^^ string "struct"
      ^^ (if can_be_packed then space ^^ string "packed" else empty)
      ^^ space
      ^^ group
           (lbrace ^^ nest 4 (hardline ^^ separate_map (semi ^^ hardline) sv_field fields) ^^ semi ^^ hardline ^^ rbrace)
      ^^ space ^^ sv_id id ^^ semi
  | CTD_variant (id, ctors) ->
      let exception_boilerplate =
        if Id.compare id (mk_id "exception") = 0 then
          twice hardline ^^ ksprintf string "%s sail_current_exception;" (sv_id_string id)
        else empty
      in
      let kind_id (id, _) = string_of_id id |> Util.zencode_string |> String.uppercase_ascii |> string in
      let sv_ctor (id, ctyp) = sv_ctyp ctyp ^^ space ^^ sv_id id in
      let tag_type = string ("sailtag_" ^ sv_id_string id) in
      let value_type = string ("sailunion_" ^ sv_id_string id) in
      let kind_enum =
        separate space
          [
            string "typedef";
            string "enum";
            group (lbrace ^^ nest 4 (hardline ^^ separate_map (comma ^^ hardline) kind_id ctors) ^^ hardline ^^ rbrace);
            tag_type ^^ semi;
          ]
      in
      (* At least verilator only allows unions for packed types (which
         is roughly equivalent to types that can be represented as
         finite bitvectors). *)
      let can_be_packed = List.for_all (fun (_, ctyp) -> is_packed ctyp) ctors in
      kind_enum ^^ twice hardline
      ^^
      if can_be_packed then (
        let constructors =
          List.map
            (fun (ctor_id, ctyp) ->
              separate space [string "function"; string "automatic"; sv_id id; sv_id ctor_id]
              ^^ parens (sv_ctyp ctyp ^^ space ^^ char 'v')
              ^^ semi
              ^^ nest 4
                   (hardline ^^ sv_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
                   ^^ string ("sailunion_" ^ sv_id_string id)
                   ^^ space ^^ string "u" ^^ semi ^^ hardline
                   ^^ separate space
                        [
                          string "r.tag";
                          equals;
                          string_of_id ctor_id |> Util.zencode_string |> String.uppercase_ascii |> string;
                        ]
                   ^^ semi ^^ hardline
                   ^^ separate space [char 'u' ^^ dot ^^ sv_id ctor_id; equals; char 'v']
                   ^^ semi ^^ hardline
                   ^^ separate space [string "r.value"; equals; char 'u']
                   ^^ semi ^^ hardline ^^ string "return" ^^ space ^^ char 'r' ^^ semi
                   )
              ^^ hardline ^^ string "endfunction"
            )
            ctors
        in
        separate space
          [
            string "typedef";
            string "union";
            string "packed";
            group
              (lbrace
              ^^ nest 4 (hardline ^^ separate_map (semi ^^ hardline) sv_ctor ctors)
              ^^ semi ^^ hardline ^^ rbrace
              );
            value_type ^^ semi;
          ]
        ^^ twice hardline
        ^^ separate space
             [
               string "typedef";
               string "struct";
               string "packed";
               group
                 (lbrace
                 ^^ nest 4
                      (hardline ^^ tag_type ^^ space ^^ string "tag" ^^ semi ^^ hardline ^^ value_type ^^ space
                     ^^ string "value"
                      )
                 ^^ semi ^^ hardline ^^ rbrace
                 );
               sv_id id ^^ semi;
             ]
        ^^ twice hardline
        ^^ separate (twice hardline) constructors
        ^^ exception_boilerplate
      )
      else (
        let constructors =
          List.map
            (fun (ctor_id, ctyp) ->
              separate space [string "function"; string "automatic"; sv_id id; sv_id ctor_id]
              ^^ parens (sv_ctyp ctyp ^^ space ^^ char 'v')
              ^^ semi
              ^^ nest 4
                   (hardline ^^ sv_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
                   ^^ separate space
                        [
                          string "r.tag";
                          equals;
                          string_of_id ctor_id |> Util.zencode_string |> String.uppercase_ascii |> string;
                        ]
                   ^^ semi ^^ hardline
                   ^^ separate space [char 'r' ^^ dot ^^ sv_id ctor_id; equals; char 'v']
                   ^^ semi ^^ hardline ^^ string "return" ^^ space ^^ char 'r' ^^ semi
                   )
              ^^ hardline ^^ string "endfunction"
            )
            ctors
        in
        separate space
          [
            string "typedef";
            string "struct";
            group
              (lbrace
              ^^ nest 4
                   (hardline ^^ tag_type ^^ space ^^ string "tag" ^^ semi ^^ hardline
                   ^^ separate_map (semi ^^ hardline) sv_ctor ctors
                   )
              ^^ semi ^^ hardline ^^ rbrace
              );
            sv_id id ^^ semi;
          ]
        ^^ twice hardline
        ^^ separate (twice hardline) constructors
        ^^ exception_boilerplate
      )

let sv_smt_type_def = function
  | Smtlib.Declare_datatypes (nm, ctors) ->
      if List.length ctors = 1 then (
        let ctor_nm, fields = List.hd ctors in
        separate space [string "typedef"; string "struct"; string "packed"]
        ^^ space
        ^^ group
             (lbrace
             ^^ nest 4
                  (hardline
                  ^^ separate hardline (List.map (fun (nm, ty) -> sv_smt_ctyp ty ^^ space ^^ string nm ^^ semi) fields)
                  )
             ^^ hardline ^^ rbrace
             )
        ^^ space ^^ string ctor_nm ^^ semi
      )
      else failwith "Todo union"
  | _ -> failwith "Not a datatype"

module Smt =
  Smt_builtins.Make
    (struct
      let max_unknown_integer_width = 128
      let max_unknown_bitvector_width = 128
      let union_ctyp_classify = is_packed
    end)
    (struct
      let print_bits = function
        | CT_lbits _ -> "sail_print_bits"
        | CT_fbits (sz, _) -> Generate_primop.print_fbits sz
        | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "print_bits"
    end)

let ( let* ) = Smt_builtins.bind
let return = Smt_builtins.return

let rec mapM f = function
  | [] -> return []
  | x :: xs ->
      let* x = f x in
      let* xs = mapM f xs in
      return (x :: xs)

let sv_signed x = string "signed'" ^^ parens x

let string_of_bitU = function Sail2_values.B0 -> "0" | Sail2_values.B1 -> "1" | Sail2_values.BU -> "X"

let has_undefined_bit = List.exists (function Sail2_values.BU -> true | _ -> false)

let rec hex_bitvector bits =
  let open Sail2_values in
  match bits with
  | B0 :: B0 :: B0 :: B0 :: rest -> "0" ^ hex_bitvector rest
  | B0 :: B0 :: B0 :: B1 :: rest -> "1" ^ hex_bitvector rest
  | B0 :: B0 :: B1 :: B0 :: rest -> "2" ^ hex_bitvector rest
  | B0 :: B0 :: B1 :: B1 :: rest -> "3" ^ hex_bitvector rest
  | B0 :: B1 :: B0 :: B0 :: rest -> "4" ^ hex_bitvector rest
  | B0 :: B1 :: B0 :: B1 :: rest -> "5" ^ hex_bitvector rest
  | B0 :: B1 :: B1 :: B0 :: rest -> "6" ^ hex_bitvector rest
  | B0 :: B1 :: B1 :: B1 :: rest -> "7" ^ hex_bitvector rest
  | B1 :: B0 :: B0 :: B0 :: rest -> "8" ^ hex_bitvector rest
  | B1 :: B0 :: B0 :: B1 :: rest -> "9" ^ hex_bitvector rest
  | B1 :: B0 :: B1 :: B0 :: rest -> "A" ^ hex_bitvector rest
  | B1 :: B0 :: B1 :: B1 :: rest -> "B" ^ hex_bitvector rest
  | B1 :: B1 :: B0 :: B0 :: rest -> "C" ^ hex_bitvector rest
  | B1 :: B1 :: B0 :: B1 :: rest -> "D" ^ hex_bitvector rest
  | B1 :: B1 :: B1 :: B0 :: rest -> "E" ^ hex_bitvector rest
  | B1 :: B1 :: B1 :: B1 :: rest -> "F" ^ hex_bitvector rest
  | _ -> ""

let sv_name_for_smt_name = Str.global_replace (Str.regexp "/") "_$_"

(* Convert a SMTLIB expression into SystemVerilog *)
let rec sv_smt ?(need_parens = false) =
  let sv_smt_parens exp = sv_smt ~need_parens:true exp in
  let opt_parens doc = if need_parens then parens doc else doc in
  function
  | Smtlib.Bitvec_lit bits ->
      let len = List.length bits in
      if len mod 4 = 0 && not (has_undefined_bit bits) then ksprintf string "%d'h%s" len (hex_bitvector bits)
      else ksprintf string "%d'b%s" len (Util.string_of_list "" string_of_bitU bits)
  | Bool_lit true -> string "1"
  | Bool_lit false -> string "0"
  | String_lit s -> ksprintf string "\"%s\"" s
  | Enum "unit" -> string "SAIL_UNIT"
  | Fn ("Bits", [size; bv]) -> squote ^^ lbrace ^^ sv_smt size ^^ comma ^^ space ^^ sv_smt bv ^^ rbrace
  | Fn ("concat", xs) -> lbrace ^^ separate_map (comma ^^ space) sv_smt xs ^^ rbrace
  | Fn ("not", [Fn ("not", [x])]) -> sv_smt ~need_parens x
  | Fn ("not", [Fn ("=", [x; y])]) -> opt_parens (separate space [sv_smt_parens x; string "!="; sv_smt_parens y])
  | Fn ("not", [x]) -> opt_parens (char '!' ^^ sv_smt_parens x)
  | Fn ("=", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string "=="; sv_smt_parens y])
  | Fn ("and", xs) -> opt_parens (separate_map (space ^^ string "&&" ^^ space) sv_smt_parens xs)
  | Fn ("or", xs) -> opt_parens (separate_map (space ^^ string "||" ^^ space) sv_smt_parens xs)
  | Fn ("bvnot", [x]) -> opt_parens (char '~' ^^ sv_smt_parens x)
  | Fn ("bvneg", [x]) -> opt_parens (char '-' ^^ sv_smt_parens x)
  | Fn ("bvand", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '&'; sv_smt_parens y])
  | Fn ("bvnand", [x; y]) ->
      opt_parens (char '~' ^^ parens (separate space [sv_smt_parens x; char '&'; sv_smt_parens y]))
  | Fn ("bvor", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '|'; sv_smt_parens y])
  | Fn ("bvnor", [x; y]) -> opt_parens (char '~' ^^ parens (separate space [sv_smt_parens x; char '|'; sv_smt_parens y]))
  | Fn ("bvxor", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '^'; sv_smt_parens y])
  | Fn ("bvxnor", [x; y]) ->
      opt_parens (char '~' ^^ parens (separate space [sv_smt_parens x; char '^'; sv_smt_parens y]))
  | Fn ("bvadd", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '+'; sv_smt_parens y])
  | Fn ("bvsub", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '-'; sv_smt_parens y])
  | Fn ("bvult", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '<'; sv_smt_parens y])
  | Fn ("bvule", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string "<="; sv_smt_parens y])
  | Fn ("bvugt", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '>'; sv_smt_parens y])
  | Fn ("bvuge", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string ">="; sv_smt_parens y])
  | Fn ("bvslt", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); char '<'; sv_signed (sv_smt y)])
  | Fn ("bvsle", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); string "<="; sv_signed (sv_smt y)])
  | Fn ("bvsgt", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); char '>'; sv_signed (sv_smt y)])
  | Fn ("bvsge", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); string ">="; sv_signed (sv_smt y)])
  | Fn ("bvshl", [x; y]) -> opt_parens (separate space [sv_smt x; string "<<"; sv_signed (sv_smt y)])
  | Fn ("bvlshr", [x; y]) -> opt_parens (separate space [sv_smt x; string ">>"; sv_signed (sv_smt y)])
  | Fn ("bvashr", [x; y]) -> opt_parens (separate space [sv_smt x; string ">>>"; sv_signed (sv_smt y)])
  | Fn ("contents", [x]) -> sv_smt_parens x ^^ dot ^^ string "bits"
  | Fn ("len", [x]) -> sv_smt_parens x ^^ dot ^^ string "size"
  | SignExtend (len, x) -> ksprintf string "unsigned'(%d'(signed'({" len ^^ sv_smt x ^^ string "})))"
  (* | ZeroExtend (len, x) -> ksprintf string "%d'({" len ^^ sv_smt x ^^ string "})" *)
  | Extract (n, m, Bitvec_lit bits) ->
      sv_smt (Bitvec_lit (Sail2_operators_bitlists.subrange_vec_dec bits (Big_int.of_int n) (Big_int.of_int m)))
  (* | Extract (n, m, Var v) ->
      if n = m then sv_name v ^^ lbracket ^^ string (string_of_int n) ^^ rbracket
      else sv_name v ^^ lbracket ^^ string (string_of_int n) ^^ colon ^^ string (string_of_int m) ^^ rbracket *)
  | Extract (n, m, x) ->
      if n = m then braces (sv_smt x) ^^ lbracket ^^ string (string_of_int n) ^^ rbracket
      else braces (sv_smt x) ^^ lbracket ^^ string (string_of_int n) ^^ colon ^^ string (string_of_int m) ^^ rbracket
  | Fn (f, args) -> string f ^^ parens (separate_map (comma ^^ space) sv_smt args)
  | Syntactic (x, _) -> sv_smt x
  | Var v -> string (sv_name_for_smt_name v)
  | Tester (ctor, v) ->
      opt_parens (separate space [sv_smt v ^^ dot ^^ string "tag"; string "=="; string (ctor |> String.uppercase_ascii)])
  (* | Unwrap (ctor, packed, v) ->
         if packed then sv_smt v ^^ dot ^^ string "value" ^^ dot ^^ sv_id ctor else sv_smt v ^^ dot ^^ sv_id ctor
     | Field (_, field, v) -> sv_smt v ^^ dot ^^ sv_id field *)
  | Ite (cond, then_exp, else_exp) ->
      separate space [sv_smt_parens cond; char '?'; sv_smt_parens then_exp; char ':'; sv_smt_parens else_exp]
  | Enum e -> failwith "Unknown enum"
  | Real_lit _ -> failwith "todo: real lit"
  | Shared _ -> failwith "todo: shared"
  | Read_res _ -> failwith "todo: read res"
  | Ctor (nm, args) -> string nm ^^ parens (separate_map (comma ^^ space) sv_smt args)
  | Struct (nm, fields) ->
      string "'"
      ^^ braces
           (separate (comma ^^ space) (List.map (fun (nm, v) -> string nm ^^ string ":" ^^ space ^^ sv_smt v) fields))
  | Field (nm, obj) -> sv_smt obj ^^ string "." ^^ string nm
  | Forall _ -> failwith "todo: forall"

(* let sv_cval cval =
   let* smt = Smt.smt_cval cval in
   return (sv_smt smt) *)

let rec sv_clexp = function
  | CL_id (id, _) -> sv_name id
  | CL_field (clexp, field) -> sv_clexp clexp ^^ dot ^^ sv_id field
  | _ -> string "CLEXP"

(* let clexp_conversion clexp cval =
   let ctyp_to = clexp_ctyp clexp in
   let ctyp_from = cval_ctyp cval in
   let* smt = Smt.smt_cval cval in
   if ctyp_equal ctyp_to ctyp_from then return (separate space [sv_clexp clexp; equals; sv_smt smt])
   else (
     match (ctyp_to, ctyp_from) with
     | CT_fint sz, CT_constant c ->
         let n = required_width c in
         let extended = SignExtend (sz, sz - n, smt) in
         return (separate space [sv_clexp clexp; equals; sv_smt extended])
     | CT_lint, CT_constant c ->
         let n = required_width c in
         let extended = SignExtend (128, 128 - n, smt) in
         return (separate space [sv_clexp clexp; equals; sv_smt extended])
     | CT_lint, CT_fint sz ->
         let extended = SignExtend (128, 128 - sz, smt) in
         return (separate space [sv_clexp clexp; equals; sv_smt extended])
     | CT_fint sz, CT_lint ->
         let* adjusted = Smt_builtins.force_size sz 128 smt in
         return (separate space [sv_clexp clexp; equals; sv_smt adjusted])
     | CT_constant c, _ ->
         return (separate space [sv_clexp clexp; equals; sv_smt (Smt_builtins.bvint (required_width c) c)])
     | CT_fbits (sz, _), CT_lbits _ ->
         let extracted = Extract (sz - 1, 0, Fn ("contents", [smt])) in
         return (separate space [sv_clexp clexp; equals; sv_smt extracted])
     | CT_lbits _, CT_fbits (sz, _) when sz <= 128 ->
         let variable_width =
           Fn ("Bits", [Smt_builtins.bvpint 8 (Big_int.of_int sz); ZeroExtend (128, 128 - sz, smt)])
         in
         return (separate space [sv_clexp clexp; equals; sv_smt variable_width])
     | _, _ -> failwith ("Unknown conversion from " ^ string_of_ctyp ctyp_from ^ " to " ^ string_of_ctyp ctyp_to)
   ) *)

(* let sv_update_fbits = function
   | [bv; index; bit] -> begin
       match (cval_ctyp bv, cval_ctyp index) with
       | CT_fbits (sz, _), CT_constant c ->
           let c = Big_int.to_int c in
           let* bv_smt = Smt.smt_cval bv in
           let bv_smt_1 = Extract (sz - 1, c + 1, bv_smt) in
           let bv_smt_2 = Extract (c - 1, 0, bv_smt) in
           let* bit_smt = Smt.smt_cval bit in
           let smt =
             if c = 0 then Fn ("concat", [bv_smt_1; bit_smt])
             else if c = sz - 1 then Fn ("concat", [bit_smt; bv_smt_2])
             else Fn ("concat", [bv_smt_1; bit_smt; bv_smt_2])
           in
           return (sv_smt smt)
       | _, _ -> failwith "update_fbits 1"
     end
   | _ -> failwith "update_fbits 2" *)

(* let cval_for_ctyp = function CT_unit -> V_lit (VL_unit, CT_unit) *)

let sv_line_directive l =
  match Reporting.simp_loc l with
  | Some (p1, _) when !opt_line_directives -> ksprintf string "`line %d \"%s\" 0" p1.pos_lnum p1.pos_fname ^^ hardline
  | _ -> empty

let sv_fn_ret_typ fn res_typ globals =
  CT_struct (mk_id (fn ^ "_$_res"), (mk_id "res", res_typ) :: List.map (fun (ty, nm) -> (nm, ty)) globals)

(* let sv_fn_ret_typ ctx fn res_typ globals = Jib_smt.smt_ctyp ctx (sv_fn_ret_typ fn res_typ globals) *)

let sv_fn_ret_typ_def fn res_typ globals =
  CTD_struct (mk_id (fn ^ "_$_res"), (mk_id "res", res_typ) :: List.map (fun (ty, nm) -> (nm, ty)) globals)

let sv_make_instances ctx line_nm exp fn_ctyps globals =
  let instances = Queue.create () in
  let new_exp =
    Smtlib.fold_smt_exp
      (fun exp ->
        match exp with
        | Ctor (nm, args) ->
            let fn_nm = String.sub nm 1 (String.length nm - 1) in
            Queue.add
              ( match Bindings.find_opt (Id_aux (Id fn_nm, Unknown)) fn_ctyps with
              | Some (_, ret_ctyp) ->
                  let ty = sv_fn_ret_typ fn_nm ret_ctyp globals in
                  sv_smt_ctyp (Jib_smt.smt_ctyp ctx ty)
                  ^^ space
                  ^^ string (sv_name_for_smt_name line_nm ^ "_$_" ^ fn_nm)
                  ^^ semi ^^ hardline ^^ string fn_nm ^^ space
                  ^^ string (sv_name_for_smt_name line_nm ^ "_$_" ^ fn_nm ^ "_$_i")
                  ^^ parens
                       (separate (comma ^^ space)
                          (string (sv_name_for_smt_name line_nm ^ "_$_" ^ fn_nm) :: List.map sv_smt args)
                       )
                  ^^ semi ^^ hardline
              | None -> failwith ("Could not find type for call of " ^ fn_nm)
              )
              instances;
            Var (sv_name_for_smt_name line_nm ^ "_$_" ^ fn_nm)
        | _ -> exp
      )
      exp
  in
  (instances, new_exp)

let sv_end_assignment name code =
  name ^ "/"
  ^ string_of_int
      (List.fold_left max 0
         (List.filter_map
            (function
              | Smtlib.Define_const (nm, ty, exp) ->
                  if String.starts_with ~prefix:(name ^ "/") nm then
                    Some
                      (int_of_string
                         (String.sub nm (1 + String.length name) (String.length nm - String.length name - 1))
                      )
                  else None
              | _ -> None
              )
            code
         )
      )

let sv_end_assignmentz name code =
  "z" ^ name ^ "/"
  ^ string_of_int
      (List.fold_left max 0
         (List.filter_map
            (function
              | Smtlib.Define_const (nm, ty, exp) ->
                  if String.starts_with ~prefix:("z" ^ name ^ "/") nm then
                    Some
                      (int_of_string
                         (String.sub nm (2 + String.length name) (String.length nm - String.length name - 2))
                      )
                  else None
              | _ -> None
              )
            code
         )
      )

let sv_inject_function_state_args globals this_res_typ this_orig_res_type (I_aux (instr, x)) =
  match instr with
  | I_funcall (CL_id (i, res_typ), ext, (Id_aux (Id fn, _), argtyps), args) when not (fn = "add_bits_int") ->
      let ty = sv_fn_ret_typ fn res_typ globals in
      let tmp = name (mk_id (fn ^ "_$_res_tmp")) in
      [
        I_aux
          ( I_funcall
              ( CL_id (tmp, ty),
                ext,
                ( mk_id fn,
                  argtyps
                  (* FIXME: Should include extra types here, but that changes function signature and therefore name, so type lookup fails later *)
                  (* @ List.map fst globals *)
                ),
                args @ List.map (fun (gty, nm) -> V_id (global nm, gty)) globals
              ),
            x
          );
        I_aux (I_copy (CL_id (i, res_typ), V_field (V_id (tmp, ty), mk_id "res")), x);
      ]
      @ List.map (fun (gty, id) -> I_aux (I_copy (CL_id (global id, gty), V_field (V_id (tmp, ty), id)), x)) globals
  | I_copy (CL_id (nm, _), exp) when string_of_name nm = "return" ->
      let struc =
        V_struct ((mk_id "res", exp) :: List.map (fun (gty, id) -> (id, V_id (global id, gty))) globals, this_res_typ)
      in
      [I_aux (I_copy (CL_id (nm, this_res_typ), struc), x)]
  | _ -> [I_aux (instr, x)]

let sv_fundef ctx f params param_ctyps ret_ctyp body all_cdefs this_cdef fn_ctyps globals =
  let arg_ctyps, ret_ctyps =
    match Bindings.find_opt f fn_ctyps with
    | Some (arg_ctyps, ret_ctyp) -> (arg_ctyps, ret_ctyp)
    | _ -> failwith "Could not find type"
  in
  let real_res_typ = sv_fn_ret_typ (string_of_id f) ret_ctyps globals in
  let real_res_typ_def = Jib_smt.smt_ctype_def ctx (sv_fn_ret_typ_def (string_of_id f) ret_ctyps globals) in
  let instrs =
    let open Jib_optimize in
    body
    |> List.map (map_instr (Jib_smt.expand_reg_deref ctx.tc_env ctx.register_map))
    |> flatten_instrs |> remove_unused_labels |> remove_pointless_goto
    |> List.map (sv_inject_function_state_args globals real_res_typ ret_ctyps)
    |> List.concat
  in
  let stack, _, _ = Jib_smt.smt_instr_list (sv_id_string f) ctx all_cdefs instrs in
  let code = Jib_smt.smt_header ctx all_cdefs @ List.rev (Stack.fold (fun x y -> y :: x) [] stack) in
  let code_doc, code =
    List.fold_right
      (fun def (code_doc, code) ->
        output_string stdout (Smtlib.string_of_smt_def def);
        output_string stdout "\n";
        match def with
        | Smtlib.Define_const (nm, ty, exp) ->
            let new_modules, new_expr = sv_make_instances ctx nm exp fn_ctyps globals in
            let assign =
              separate space [string "assign"; string (sv_name_for_smt_name nm); equals; sv_smt new_expr]
              ^^ semi ^^ hardline in
            (code_doc ^^ Queue.fold ( ^^ ) empty new_modules ^^ assign, Smtlib.Define_const (nm, ty, new_expr) :: code)
        | _ -> (code_doc, def :: code)
      )
      code (empty, [])
  in
  let final_return = sv_end_assignment "return" code in
  let decl_doc =
    List.fold_left
      (fun doc def ->
        match def with
        | Smtlib.Define_const (nm, ty, exp) ->
            separate space [sv_smt_ctyp ty; string (sv_name_for_smt_name nm)] ^^ semi ^^ hardline ^^ doc
        | _ -> doc
      )
      empty code
  in
  let param_docs =
    try
      List.map2
        (fun param ctyp ->
          string "input" ^^ space
          ^^ sv_smt_ctyp (Jib_smt.smt_ctyp ctx ctyp)
          ^^ space ^^ string "z" ^^ sv_id param ^^ string "_$_0"
        )
        params param_ctyps
    with Invalid_argument _ -> Reporting.unreachable (id_loc f) __POS__ "Function arity mismatch"
  in
  let return_doc =
    string "output" ^^ space ^^ sv_smt_ctyp (Jib_smt.smt_ctyp ctx real_res_typ) ^^ space ^^ string "return_$_end"
  in
  let state_docs =
    List.map
      (fun (ty, nm) ->
        string "input" ^^ space
        ^^ sv_smt_ctyp (Jib_smt.smt_ctyp ctx ty)
        ^^ space
        ^^ string ("z" ^ sv_name_for_smt_name (sv_id_string nm) ^ "_$_0")
      )
      globals
  in
  sv_smt_type_def (List.hd real_res_typ_def)
  ^^ twice hardline ^^ string "interface" ^^ space ^^ sv_id f
  ^^ parens (separate (comma ^^ space) ((return_doc :: param_docs) @ state_docs))
  ^^ semi
  ^^ nest 4
       (hardline ^^ decl_doc ^^ hardline ^^ code_doc
       ^^ separate space
            [
              string "assign";
              string (sv_name_for_smt_name "return_$_end");
              equals;
              string (sv_name_for_smt_name final_return);
            ]
       ^^ semi
       )
  ^^ hardline ^^ string "endinterface"

let filter_clear = filter_instrs (function I_aux (I_clear _, _) -> false | _ -> true)

(* let sv_setup_function ctx name setup =
   let setup =
     Jib_optimize.(
       setup |> flatten_instrs |> remove_dead_code |> variable_decls_to_top |> structure_control_flow_block
       |> filter_clear
     )
   in
   separate space [string "function"; string "automatic"; string "void"; string name]
   ^^ string "()" ^^ semi
   ^^ nest 4 (hardline ^^ separate_map hardline (sv_checked_instr ctx) setup)
   ^^ hardline ^^ string "endfunction" ^^ twice hardline *)

type sv_cdef_loc = CDLOC_Out | CDLOC_In

let sv_cdef ctx fn_ctyps setup_calls all_cdefs cdef globals =
  match cdef with
  (* | CDEF_register (id, ctyp, setup) ->
      let binding_doc = sv_ctyp ctyp ^^ space ^^ sv_id id ^^ semi ^^ twice hardline in
      let name = sprintf "sail_setup_reg_%s" (sv_id_string id) in
      (binding_doc, fn_ctyps, name :: setup_calls, CDLOC_In) *)
  (* | CDEF_type td -> (sv_type_def td ^^ twice hardline, fn_ctyps, setup_calls, CDLOC_Out) *)
  | CDEF_val (f, _, param_ctyps, ret_ctyp) ->
      (empty, Bindings.add f (param_ctyps, ret_ctyp) fn_ctyps, setup_calls, CDLOC_In)
  | CDEF_fundef (f, _, params, body) ->
      let body =
        Jib_optimize.(
          body |> flatten_instrs |> remove_dead_code |> variable_decls_to_top |> structure_control_flow_block
          |> filter_clear
        )
      in
      begin
        match Bindings.find_opt f fn_ctyps with
        | Some (param_ctyps, ret_ctyp) ->
            ( sv_fundef ctx f params param_ctyps ret_ctyp body all_cdefs cdef fn_ctyps globals ^^ twice hardline,
              fn_ctyps,
              setup_calls,
              CDLOC_Out
            )
        | None -> Reporting.unreachable (id_loc f) __POS__ ("No function type found for " ^ string_of_id f)
      end
  (* | CDEF_let (n, bindings, setup) ->
      let bindings_doc =
        separate_map (semi ^^ hardline) (fun (id, ctyp) -> sv_ctyp ctyp ^^ space ^^ sv_id id) bindings
        ^^ semi ^^ twice hardline
      in
      let name = sprintf "sail_setup_let_%d" n in
      (bindings_doc, fn_ctyps, name :: setup_calls, CDLOC_In) *)
  | _ -> (empty, fn_ctyps, setup_calls, CDLOC_In)

let register_types cdefs =
  List.fold_left
    (fun acc cdef -> match cdef with CDEF_register (id, ctyp, _) -> Bindings.add id ctyp acc | _ -> acc)
    Bindings.empty cdefs

let jib_of_ast env ast effect_info =
  let open Jib_compile in
  let module Jibc = Make (Verilog_config) in
  let env, effect_info = add_special_functions env effect_info in
  let ctx = initial_ctx env effect_info in
  Jibc.compile_ast ctx ast

let wrap_module pre mod_name ins_outs doc =
  pre ^^ hardline ^^ string "module" ^^ space ^^ string mod_name
  ^^ parens (nest 4 (hardline ^^ separate (comma ^^ hardline) ins_outs) ^^ hardline)
  ^^ semi
  ^^ nest 4 (hardline ^^ doc)
  ^^ hardline ^^ string "endmodule" ^^ hardline

let verilator_cpp_wrapper name =
  [
    sprintf "#include \"V%s.h\"" name;
    "#include \"verilated.h\"";
    "int main(int argc, char** argv) {";
    "    VerilatedContext* contextp = new VerilatedContext;";
    "    contextp->commandArgs(argc, argv);";
    sprintf "    V%s* top = new V%s{contextp};" name name;
    "    while (!contextp->gotFinish()) { top -> eval(); }";
    "    delete top;";
    "    delete contextp;";
    "    return 0;";
    "}";
  ]

let make_genlib_file filename =
  let common_primops = Generate_primop.common_primops 128 128 in
  let defs = Generate_primop.get_generated_primops () in
  let ((out_chan, _, _, _) as file_info) = Util.open_output_with_check_unformatted None filename in
  output_string out_chan "`ifndef SAIL_LIBRARY_GENERATED\n";
  output_string out_chan "`define SAIL_LIBRARY_GENERATED\n\n";
  output_string out_chan common_primops;
  List.iter
    (fun def ->
      List.iter
        (fun line ->
          output_string out_chan line;
          output_char out_chan '\n'
        )
        def;
      output_char out_chan '\n'
    )
    defs;
  output_string out_chan "`endif\n";
  Util.close_output_with_check file_info

let main_args main fn_ctyps globals =
  match main with
  | Some (CDEF_fundef (f, _, params, body)) -> begin
      match Bindings.find_opt f fn_ctyps with
      | Some (param_ctyps, ret_ctyp) -> begin
          let main_args =
            List.map2
              (fun param param_ctyp -> match param_ctyp with CT_unit -> string "SAIL_UNIT" | _ -> sv_id param)
              params param_ctyps
          in
          let non_unit =
            List.filter_map
              (fun x -> x)
              (List.map2
                 (fun param param_ctyp -> match param_ctyp with CT_unit -> None | _ -> Some (param, param_ctyp))
                 params param_ctyps
              )
          in
          let module_main_in =
            List.map
              (fun (param, param_ctyp) -> string "input" ^^ space ^^ sv_ctyp param_ctyp ^^ space ^^ sv_id param)
              non_unit
          in
          let result = sv_fn_ret_typ "main" ret_ctyp globals in
          match ret_ctyp with
          | CT_unit -> (main_args, None, module_main_in, result)
          | _ ->
              ( main_args,
                Some (string "main_result"),
                (string "output" ^^ space ^^ sv_ctyp ret_ctyp ^^ space ^^ string "main_result") :: module_main_in,
                result
              )
        end
      | None -> Reporting.unreachable (id_loc f) __POS__ ("No function type found for " ^ string_of_id f)
    end
  | _ -> ([], None, [], CT_bit)

let sv_globals cdefs = List.filter_map (function CDEF_register (nm, ty, _) -> Some (ty, nm) | _ -> None) cdefs

let verilog_target _ default_sail_dir out_opt ast effect_info env =
  let sail_dir = Reporting.get_sail_dir default_sail_dir in
  let sail_sv_libdir = Filename.concat (Filename.concat sail_dir "lib") "sv" in
  let out = match out_opt with None -> "out" | Some name -> name in

  let cdefs, _, ctx = Jib_smt.compile env effect_info ast in
  let registers = register_types cdefs in

  let include_doc =
    string "`include \"sail.sv\"" ^^ hardline ^^ ksprintf string "`include \"sail_genlib_%s.sv\"" out ^^ twice hardline
  in

  let globals = sv_globals cdefs in

  let in_doc, out_doc, fn_ctyps, setup_calls =
    List.fold_left
      (fun (doc_in, doc_out, fn_ctyps, setup_calls) cdef ->
        let cdef_doc, fn_ctyps, setup_calls, loc = sv_cdef ctx fn_ctyps setup_calls cdefs cdef globals in
        match loc with
        | CDLOC_In -> (doc_in ^^ cdef_doc, doc_out, fn_ctyps, setup_calls)
        | CDLOC_Out -> (doc_in, doc_out ^^ cdef_doc, fn_ctyps, setup_calls)
      )
      (empty, include_doc, Bindings.empty, [])
      cdefs
  in

  let main = List.find_opt (function CDEF_fundef (id, _, _, _) -> sv_id_string id = "main" | _ -> false) cdefs in
  let main_args, main_result, module_main_in_out, real_main_result = main_args main fn_ctyps globals in
  let real_main_result = Jib_smt.smt_ctyp ctx real_main_result in

  let main_instance =
    sv_smt_ctyp real_main_result ^^ space ^^ string "main_out" ^^ semi ^^ hardline ^^ string "main" ^^ space
    ^^ string "main_i"
    ^^ parens
         (separate (comma ^^ space)
            ((string "main_out" :: main_args) @ List.map (fun (gty, nm) -> string (string_of_id nm ^ "_in")) globals)
         )
    ^^ semi ^^ hardline ^^ hardline
  in

  let real_main_result_nm, real_main_result_fields =
    match real_main_result with
    | Datatype (_, [(nm, fields)]) -> (nm, List.tl fields)
    | _ -> failwith "unreachable, non datatype result"
  in

  let drive_outputs =
    separate hardline
      (List.map2
         (fun (_, gnm) (nm, _) ->
           separate space
             [
               string "assign";
               string (string_of_id gnm ^ "_out");
               equals;
               (* FIXME: Don't hardcode this *)
               string "main_out." ^^ string real_main_result_nm ^^ string "_" ^^ string nm;
             ]
           ^^ semi
         )
         globals real_main_result_fields
      )
  in

  let sv_output =
    Pretty_print_sail.to_string
      (wrap_module out_doc ("sail_" ^ out)
         (module_main_in_out
         @ List.flatten
             (List.map
                (fun (gty, nm) ->
                  [
                    string "input" ^^ space ^^ sv_ctyp gty ^^ space ^^ string (string_of_id nm ^ "_in");
                    string "output" ^^ space ^^ sv_ctyp gty ^^ space ^^ string (string_of_id nm ^ "_out");
                  ]
                )
                globals
             )
         )
         (in_doc ^^ main_instance ^^ drive_outputs)
      )
  in
  make_genlib_file (sprintf "sail_genlib_%s.sv" out);

  let ((out_chan, _, _, _) as file_info) = Util.open_output_with_check_unformatted None (out ^ ".sv") in
  output_string out_chan sv_output;
  Util.close_output_with_check file_info;

  begin
    match !opt_verilate with
    | Verilator_compile | Verilator_run ->
        let ((out_chan, _, _, _) as file_info) = Util.open_output_with_check_unformatted None ("sim_" ^ out ^ ".cpp") in
        List.iter
          (fun line ->
            output_string out_chan line;
            output_char out_chan '\n'
          )
          (verilator_cpp_wrapper out);
        Util.close_output_with_check file_info;

        Reporting.system_checked
          (sprintf "verilator --cc --exe --build -j 0 -I%s sim_%s.cpp %s.sv" sail_sv_libdir out out);
        begin
          match !opt_verilate with Verilator_run -> Reporting.system_checked (sprintf "obj_dir/V%s" out) | _ -> ()
        end
    | _ -> ()
  end
