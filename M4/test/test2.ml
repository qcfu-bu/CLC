open Bindlib
open M4
open Terms
open Constr
open Norms
open Context
open Tcheck

let f = mk "f"
let f_constr = mk "f_constr"
let g = mk "g"
let g_constr = mk "g_constr"
let t = mk "t"
let x = mk "x"
let y = mk "y"
let _A = mk "A"
let _B = mk "B"
let a = mk "a"
let b = mk "b"
let n = mk "n"
let m = mk "m"
let pf = mk "pf"

let t1 = 
  axiom g (li --> ty) @@
  axiom g_constr (forall a li @@
                    !a --> (!g $ !a)) @@
  axiom f (forall a ty @@
            (!a --> li) --> li) @@
  pack @@
  axiom f_constr (forall a ty @@
                    forall m (!a --> li) @@
                      forall x !a @@ 
                        ((!m $ !x) ->> (!f $ !a $ !m)))
  @@
  !f_constr

let test () =
  let () = is_debug := true in
  let t = unbox t1
  in
  let ty = infer_i empty t in
  Format.printf "complete@.";
  Format.printf "@[t  :=@;<1 2>%a@]@." pp (nf t);
  Format.printf "@[ty :=@;<1 2>%a@]@." pp (nf ty)