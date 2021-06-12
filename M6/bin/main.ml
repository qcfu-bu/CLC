open M6
open Parser
open Context
open Tcheck
open Equality
open Eval

let _ =
  let _ = is_debug := true in
  let fname = Sys.argv.(1) in
  let ch = open_in fname in
  let t = parse_ch ch in
  let pre_ctx = empty in
  Format.printf "checking\n";
  Format.printf "t  := %a\n\n" Terms.pp t;
  let ty, post_ctx = infer pre_ctx t in
  let () = assert_msg (Context.same pre_ctx post_ctx) "main" in
  Format.printf "complete\n";
  Format.printf "post_ctx := %a@." pp post_ctx;
  Format.printf "t  := %a\n" Terms.pp (eval t);
  Format.printf "ty := %a\n" Terms.pp (whnf ty)