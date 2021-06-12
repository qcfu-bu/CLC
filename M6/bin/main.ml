open M6
open Parser
open Context
open Tcheck

let _ =
  let _ = is_debug := true in
  let t = (parse "
    let f = (fun A x => x) : (A : Type) -> A -> A in
    f




  
    ")
  in
  let pre_ctx = empty in
  let ty, post_ctx = infer pre_ctx t in
  let () = assert_msg (Context.same pre_ctx post_ctx) "main" in
  Format.printf "complete\n";
  Format.printf "post_ctx := %a@." pp post_ctx;
  Format.printf "ty := %a\n" Terms.pp ty