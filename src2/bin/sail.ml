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

let opt_file_arguments : string list ref = ref []
let opt_file_out : string option ref = ref None
let opt_just_check : bool ref = ref false
let opt_auto_interpreter_rewrites : bool ref = ref false
let opt_interactive_script : string option ref = ref None
let opt_splice : string list ref = ref []
let opt_print_version = ref false

(* Allow calling all options as either -foo_bar or -foo-bar *)
let rec fix_options = function
  | (flag, spec, doc) :: opts -> (flag, spec, doc) :: (String.map (function '_' -> '-' | c -> c) flag, spec, "") :: fix_options opts
  | [] -> []

let load_plugin opts plugin =
  Dynlink.loadfile_private plugin;
  opts := Arg.align (!opts @ fix_options (Target.extract_options ()))

let version =
  let open Manifest in
  let default = Printf.sprintf "Sail %s @ %s" branch commit in
  (* version is parsed from the output of git describe *)
  match String.split_on_char '-' version with
  | (vnum :: _) ->
     Printf.sprintf "Sail %s (%s @ %s)" vnum branch commit
  | _ -> default
            
let usage_msg =
  version
  ^ "\nusage: sail <options> <file1.sail> ... <fileN.sail>\n"

let help options = raise (Arg.Help (Arg.usage_string options usage_msg))

let rec options = ref ([
  ( "-o",
    Arg.String (fun f -> opt_file_out := Some f),
    "<prefix> select output filename prefix");
  ( "-i",
    Arg.Tuple [Arg.Set Interactive.opt_interactive;
               Arg.Set opt_auto_interpreter_rewrites;
               Arg.Set Initial_check.opt_undefined_gen],
    " start interactive interpreter");
  ( "-is",
    Arg.Tuple [Arg.Set Interactive.opt_interactive;
               Arg.Set opt_auto_interpreter_rewrites;
               Arg.Set Initial_check.opt_undefined_gen;
               Arg.String (fun s -> opt_interactive_script := Some s)],
    "<filename> start interactive interpreter and execute commands in script");
  ( "-interact_custom",
    Arg.Set Interactive.opt_interactive,
    " drop to an interactive session after running Sail. Differs from \
     -i in that it does not set up the interpreter in the interactive \
     shell.");
  ( "-no_warn",
    Arg.Clear Reporting.opt_warnings,
    " do not print warnings");
  ( "-plugin",
    Arg.String (fun plugin -> load_plugin options plugin),
    "<file> load a Sail plugin");
  ( "-just_check",
    Arg.Set opt_just_check,
    " terminate immediately after typechecking");
  ( "-undefined_gen",
    Arg.Set Initial_check.opt_undefined_gen,
    " generate undefined_type functions for types in the specification");
  ( "-splice",
    Arg.String (fun s -> opt_splice := s :: !opt_splice),
    "<filename> add functions from file, replacing existing definitions where necessary");
  ( "-ddump_initial_ast",
    Arg.Set Frontend.opt_ddump_initial_ast,
    " (debug) dump the initial ast to stdout");
  ( "-ddump_tc_ast",
    Arg.Set Frontend.opt_ddump_tc_ast,
    " (debug) dump the typechecked ast to stdout");
  ( "-dtc_verbose",
    Arg.Int (fun verbosity -> Type_check.opt_tc_debug := verbosity),
    "<verbosity> (debug) verbose typechecker output: 0 is silent");
  ( "-dsmt_verbose",
    Arg.Set Constraint.opt_smt_verbose,
    " (debug) print SMTLIB constraints sent to SMT solver");
  ( "-dmagic_hash",
    Arg.Set Initial_check.opt_magic_hash,
    " (debug) allow special character # in identifiers");
  ( "-dprofile",
    Arg.Set Profile.opt_profile,
    " (debug) provide basic profiling information for rewriting passes within Sail");
  ( "-v",
    Arg.Set opt_print_version,
    " print version");
  ( "-help",
    Arg.Unit (fun () -> help !options),
    " Display this list of options. Also available as -h or --help");
  ( "-h", Arg.Unit (fun () -> help !options), "");
  ( "--help", Arg.Unit (fun () -> help !options), "");
])

let register_default_target () =
  Target.register ~name:"default" (fun _ _ _ _ -> ())
  
let run_sail tgt =
  Target.run_pre_parse_hook tgt ();
  let ast, env, effect_info = Frontend.load_files ~target:(Target.name tgt) !options Type_check.initial_env !opt_file_arguments in
  let ast, env = Frontend.descatter effect_info env ast in
  let _ast, _env =
    List.fold_right (fun file (ast, _) -> Splice.splice ast file)
      (!opt_splice) (ast, env)
  in
  Reporting.opt_warnings := false; (* Don't show warnings during re-writing for now *)

  Target.run_pre_rewrites_hook tgt ast effect_info env;
  let ast, effect_info, env = Rewrites.rewrite effect_info env (Target.rewrites tgt) ast in

  Target.action tgt !opt_file_out ast effect_info env;

  (ast, env, effect_info)
 
let main () =
  begin match Sys.getenv_opt "SAIL_NO_PLUGINS" with
  | Some _ -> ()
  | None ->
     match Libsail_sites.Sites.plugins with
     | dir :: _ ->
        List.iter
          (fun plugin ->
            let path = Filename.concat dir plugin in
            load_plugin options path)
          (Array.to_list (Sys.readdir dir))
     | [] -> ()
  end;

  options := Arg.align !options;
  
  Arg.parse_dynamic options
    (fun s ->
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg;
  
  if !opt_print_version then (
    print_endline version;
    exit 0
  );
 
  let default_target = register_default_target () in
    
  let ast, env, effect_info = match Target.get_the_target () with
    | Some target when not !opt_just_check -> run_sail target
    | _ -> run_sail default_target
  in
    
  if !Interactive.opt_interactive then (
    Repl.start_repl ~auto_rewrites:(!opt_auto_interpreter_rewrites) ~options:!(options) env effect_info ast
  )

let () =
  try (
    try main ()
    with Failure s -> raise (Reporting.err_general Parse_ast.Unknown ("Failure " ^ s))
  ) with
  | Reporting.Fatal_error e ->
     Reporting.print_error e;
     exit 1