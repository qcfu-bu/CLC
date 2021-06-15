open M6
open Parser
open Context
open Tcheck
open Eval
open Format

let _ =
  let _ = Tcheck.is_debug := false in
  if Array.length Sys.argv < 1 then
    printf "input file expected@."
  else
    let fname = Sys.argv.(1) in
    let ch = open_in fname in
    let t = parse_ch ch in
    let pre_ctx = empty in
    printf "checking@.";
    printf "@[t  :=@;<1 2>%a@]@." Terms.pp t;
    let ty, post_ctx = infer pre_ctx t in
    let () = assert_msg (Context.same pre_ctx post_ctx) "Pre/Post Context" in
    printf "complete@.";
    printf "post_ctx := %a@." pp post_ctx;
    printf "@[ty :=@;<1 2>%a@]@." Terms.pp (nf ty);
    printf "evaluate@.";
    printf "@[t  :=@;<1 2>%a@]@." Terms.pp (eval t);
    printf "heap := %a@." Heap.pp Heap.heap;