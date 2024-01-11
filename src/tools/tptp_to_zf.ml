(* This file is free software, part of Zipperposition. See file "license" for more details. *)

(** {1 Convert from TPTP to ZF} *)

open Logtk
open Logtk_parsers
open CCResult.Infix
module T = TypedSTerm

(* TODO: also pick statement printer based on Options.output *)
let pp_stmt out s =
   let pp_t =
      match !Options.output with
         | Logtk.Options.O_none | Logtk.Options.O_zf -> T.ZF.pp_inner
         | Logtk.Options.O_normal -> T.pp_inner
         | Logtk.Options.O_tptp -> T.TPTP.pp
   in
      Statement.pp pp_t pp_t pp_t out s

let pp_stmts out seq = CCVector.pp ~pp_sep:(CCFormat.return "@,") pp_stmt out seq

let declare_term out () =
   let id = ID.make "term" in
   let st = Statement.ty_decl ~proof:(Proof.Step.intro (Proof.Src.internal []) Proof.R_decl) id T.Ty.tType in
      pp_stmt out st

let process file =
   let input = Input_format.I_tptp in
      Util_tptp.parse_file ~recursive:true file
      >|= Iter.map Util_tptp.to_ast
      >>= TypeInference.infer_statements ?ctx:None ~on_var:(Input_format.on_var input)
            ~on_undef:(Input_format.on_undef_id input) ~on_shadow:(Input_format.on_shadow input)
            ~implicit_ty_args:(Input_format.implicit_ty_args input)
      >|= fun stmts ->
      (* declare "term" then proceed *)
      Format.printf "@[<v>%a@,%a@]@." declare_term () pp_stmts stmts;
      ()

let options = Arg.align @@ Options.make ()

let () =
   CCFormat.set_color_default true;
   let files = ref [] in
   let add_file f = files := f :: !files in
      Arg.parse options add_file "tptp_to_zf [options] [file|stdin]";
      let file =
         match !files with [] -> "stdin" | [ f ] -> f | _ :: _ -> failwith "expected at most one file"
      in
      let res = process file in
         match res with
            | CCResult.Ok () -> ()
            | CCResult.Error msg ->
               print_endline msg;
               exit 1
