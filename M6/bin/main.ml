open M6
open Parser
open Context
open Tcheck
open Equality
open Eval
open Format

let _ =
  let _ = is_debug := true in
  if Array.length Sys.argv < 1 then
    printf "input file expected\n"
  else
    let fname = Sys.argv.(1) in
    let ch = open_in fname in
    let t = parse_ch ch in
    let pre_ctx = empty in
    printf "checking\n";
    printf "t  := %a\n\n" Terms.pp t;
    let ty, post_ctx = infer pre_ctx t in
    let () = assert_msg (Context.same pre_ctx post_ctx) "Pre/Post Context" in
    printf "complete\n";
    printf "post_ctx := %a@." pp post_ctx;
    printf "t  := %a\n" Terms.pp (eval t);
    printf "ty := %a\n" Terms.pp (whnf ty)