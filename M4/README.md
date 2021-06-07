# M4

## Functional fragment of LNLD. 

## Typing rules

### Type Formation
```
                                             Γ ⊢ e : Uᵢ        Γ ⊢ e : Lᵢ
-------------         --------------        ------------       ------------
Γ ⊢ Uᵢ : Uᵢ₊₁         Γ ⊢ Lᵢ : Uᵢ₊₁         Γ ⊢ e type        Γ ⊢ e linear


Γ ⊢ X : Uᵢ  Γ ⊢ e : X  Γ ⊢ e' : X
----------------------------------
       Γ ⊢ e =ₓ e' : Uᵢ


Γ ⊢ X : Uᵢ  Γ,x:X ⊢ Y : Uᵢ      Γ ⊢ X : Uᵢ  Γ,x:X ⊢ A : Lᵢ     Γ ⊢ A : Lᵢ  Γ ⊢ B : Lᵢ
---------------------------     ---------------------------     -----------------------
     Γ ⊢ Πx:X.Y : Uᵢ                  Γ ⊢ Πx:X.A : Lᵢ               Γ ⊢ A ⊸ B : Lᵢ


Γ ⊢ X : Uᵢ  Γ,x:X ⊢ Y : Uᵢ      Γ ⊢ A : Lᵢ  Γ ⊢ B : Lᵢ       Γ ⊢ A : Lᵢ  Γ ⊢ B : Lᵢ
---------------------------     ------------------------      -----------------------
      Γ ⊢ Σx:X.Y : Uᵢ                Γ ⊢ A ⊗ B : Lᵢ               Γ ⊢ A & B : Lᵢ


----------     ----------     -----------
Γ ⊢ 1 : Uᵢ     Γ ⊢ I : Lᵢ     Γ ⊢ ⊤ : Lᵢ


 Γ ⊢ A : Lᵢ      Γ ⊢ X : Uᵢ  Γ,x:X ⊢ A : Lᵢ
------------     ---------------------------
Γ ⊢ G A : Uᵢ          Γ ⊢ Fx:X.A : Lᵢ
```

### Intuitionistic Typing
The elimination rule for intensional =ₓ is omitted, refer to HoTT book for details.
```
                         Γ ⊢ e : Y    Γ ⊢ X ≡ Y type
-----------------        ----------------------------
Γ,x:X,Γ' ⊢ x : X                 Γ ⊢ e : X


Γ ⊢ e : X    Γ ⊢ e' : [e/x]Y      Γ ⊢ e : Σx:X.Y        Γ ⊢ e : Σx:X.Y
-----------------------------     ---------------     ---------------------
    Γ ⊢ (e, e') : Σx:X.Y           Γ ⊢ π₁ e : X       Γ ⊢ π₂ e : [π₁ e/x]Y


Γ ⊢ Πx:X.Y type    Γ,x:X Γ e : Y       Γ ⊢ e : Πx:X.Y    Γ ⊢ e' : X
---------------------------------      ------------------------------
     Γ ⊢ λx.e : Πx.X.Y                     Γ ⊢ e e' : [e'/x]Y


Γ ⊢ e ≡ e' : X            Γ;⋅ ⊢ e : A
------------------       --------------       -----------
Γ ⊢ refl : e =ₓ e'       Γ ⊢ G e : G A        Γ ⊢ () : 1
```

### Linear Typing
```
                        Γ;Δ ⊢ e : B     Γ ⊢ A ≡ B linear
--------------          ---------------------------------
Γ;a:A ⊢ a : A                     Γ;Δ ⊢ e : A


Γ;Δ ⊢ e : I    Γ;Δ' ⊢ e' : C
------------------------------
Γ;Δ,Δ' ⊢ let () = e in e' : C


Γ;Δ ⊢ e : A    Γ;Δ' ⊢ e' : B       Γ;Δ ⊢ e : A ⊗ B   Γ;Δ',a:A,b:B ⊢ e' : C
-----------------------------      ----------------------------------------
   Γ;Δ,Δ' ⊢ (e, e') : A ⊗ B           Γ;Δ,Δ' ⊢ let (a, b) = e in e' : C


Γ;Δ ⊢ e₁ : A₁   Γ;Δ ⊢ e₂ : A₂      Γ;Δ ⊢ e : A & B       Γ;Δ ⊢ e : A & B
------------------------------     -----------------      ----------------
Γ;Δ ⊢ (e₁, e₂) : A₁ & A₂            Γ;Δ ⊢ π₁ e : A        Γ;Δ ⊢ π₂ e : B


Γ;Δ,a:A ⊢ e : B          Γ;Δ ⊢ e : A ⊸ B   Γ;Δ' ⊢ e' : A
-------------------      ----------------------------------
Γ;Δ ⊢ λa.e : A ⊸ B              Γ;Δ,Δ' ⊢ e e' : B


Γ,x:X;Δ ⊢ e : A          Γ;Δ ⊢ e : Πx:X.A    Γ ⊢ e' : X
--------------------     -------------------------------
Γ;Δ ⊢ λ̂x.e : Πx:X.A           Γ;Δ ⊢ e e' : [e'/x]A


Γ ⊢ e : X   Γ;Δ ⊢ t : [e/x]A     Γ;Δ ⊢ e : Fx:X.A    Γ,x:X;Δ',a:A ⊢ e' : C
-----------------------------    -------------------------------------------
  Γ;Δ ⊢ F (e, t) : Fx:X.A            Γ;Δ,Δ' ⊢ let F (x, a) = e in e' : C


Γ ⊢ e : G A
----------------      -------------      -------------
Γ;⋅ ⊢ G⁻¹ e : A       Γ;⋅ ⊢ () : I       Γ;Δ ⊢ () : ⊤
```

## Shortcomings
The type system is quite bulky, requiring F and G to map between modalities. 
This adds complexity to extending with user defined data types.

## Planned Changes
The existence of F and G imply a tantalizing possibility of generalizing user
defined data types. Ideally, data types and their respective constructors 
only need to adhere to some well behavedness criterion in the style of Dybjer.

### Type Formation
```
data F (X : Uᵢ) (C : X -> Lᵢ) : Lᵢ =
   | F_intro : (X : Uᵢ) -> X -> C X -> F X C

data G (X : Lᵢ) : Uᵢ =
   | G_intro : X -> G X

data Sigma (X : Uᵢ) (C : X -> Uᵢ) : Uᵢ =
   | Simga_intro : X -> C X -> Sigma X C

data Tensor (X : Lᵢ) (Y : Lᵢ) : Lᵢ =
   | Tensor_intro : X -> Y -> Tensor X Y

data Vec (X : Uᵢ) : Nat -> Uᵢ =
   | Vec_nil  : Vec X Z
   | Vec_cons : forall n, X -> Vec X n -> Vec X (S n)

data Vec_vt (X : Lᵢ) : Nat -> Lᵢ =
   | Vec_vt_nil  : Vec_vt X Z
   | Vec_vt_cons : forall n, X -> Vec_vt X n -> Vec_vt X (S n)
```

### Term Introduction
```
Γ,X:Uᵢ,C:X->Uᵢ ⊢ Lᵢ type      Γ ⊢ X : Uᵢ   Γ ⊢ x : X   Γ;Δ ⊢ cx : C x
-------------------------     -----------------------------------------
Γ ⊢ F : ΠX:Uᵢ.ΠC:X->Uᵢ.Lᵢ           Γ;Δ ⊢ F_intro X x cx : F X C


Γ,X:Lᵢ ⊢ Uᵢ type          Γ;⋅ ⊢ x : X
-----------------     --------------------
Γ ⊢ G : ΠX:Lᵢ.Uᵢ      Γ ⊢ G_intro x : G X


Γ,X:Uᵢ,C:X->Uᵢ ⊢ Uᵢ type      Γ ⊢ X : Uᵢ   Γ ⊢ x : X   Γ ⊢ cx : C x
-------------------------     ---------------------------------------
Γ ⊢ Sigma : ΠX:Uᵢ.C:X->Uᵢ       Γ ⊢ Sigma_intro X x cx : Sigma X C


   Γ,X:Lᵢ,Y:Lᵢ ⊢ Lᵢ type         Γ ⊢ X : Lᵢ   Γ ⊢ Y : Lᵢ   Γ;Δ ⊢ x : X    Γ;Δ' ⊢ y : Y
----------------------------     -------------------------------------------------------
Γ ⊢ Tensor : ΠX:Lᵢ.ΠY:Lᵢ.Lᵢ            Γ;Δ,Δ' ⊢ Tensor_intro X Y x y : Tensor X Y


Γ,X:Uᵢ ⊢ Nat -> Uᵢ type
------------------------
Γ ⊢ Vec : ΠX:Uᵢ.Nat->Uᵢ


Γ ⊢ X : Uᵢ   Γ ⊢ Z : Nat     Γ ⊢ X : Uᵢ   Γ ⊢ n : Nat   Γ ⊢ x : X    Γ ⊢ v : Vec X n
-------------------------     ---------------------------------------------------------
 Γ ⊢ Vec_nil : Vec X Z                 Γ ⊢ Vec_cons X n x v : Vec X (S n)


  Γ,X:Lᵢ ⊢ Nat -> Lᵢ type       
----------------------------
Γ ⊢ Vec_vt : ΠX:Lᵢ.Nat -> Lᵢ

   Γ ⊢ X : Lᵢ   Γ ⊢ Z : Nat
--------------------------------
Γ;⋅ ⊢ Vec_vt_nil X : Vec_vt X Z

Γ ⊢ X : Lᵢ   Γ ⊢ n : Nat   Γ;Δ ⊢ x : X   Γ;Δ' ⊢ v : Vec_vt X n   
----------------------------------------------------------------
      Γ;Δ,Δ' ⊢ Vec_vt_cons X n x v : Vec_vt X (S n)
```

### Type Criterion
```
data D : ΠΘ.T =
   | C : 


                 Γ ⊢ X : Uᵢ   Γ,x:X ⊢ Θ typeᵢ
-----------      ----------------------------
Γ ⊢ ⋅ typeᵢ            Γ ⊢ Θ,x:X typeᵢ


Γ ⊢ Θ typeᵢ    Γ,Θ ⊢ T : Uᵢ
----------------------------
       Γ ⊢ D : ΠΘ.T


Γ ⊢ D : ΠΘ.T   Γ,D:ΠΘ.T ⊢ Θ' ok   Γ,D:ΠΘ.T,Θ' ⊢ D x̅ : Uᵢ   x̅ ∈ Θ'
------------------------------------------------------------------
                    Γ ⊢ C : Θ' -> D x̅
```


## References
* https://link.springer.com/chapter/10.1007/3-540-52335-9_47
* https://link.springer.com/article/10.1007/BF01211308
* https://homotopytypetheory.org/book/
* https://www.cs.cmu.edu/~fp/courses/15816-f01/handouts/linfp.pdf
* https://dl.acm.org/doi/10.1145/2775051.2676969
* https://gist.github.com/gabriel-barrett/0de85a606b64886052854422fb05ce0c
* https://gist.github.com/gabriel-barrett/11988a272bc52f0e848db6eceb03417a
* https://richarde.dev/papers/2020/quantitative/quantitative.pdf
* https://www.type-driven.org.uk/edwinb/papers/idris2.pdf
* https://bentnib.org/quantitative-type-theory.pdf
* https://link.springer.com/chapter/10.1007/978-3-319-30936-1_12