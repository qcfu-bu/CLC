# M4

## Functional fragment of LNLD. 

## Typing rules

### Type Formation
```
-------------         --------------
Γ ⊢ Uᵢ : Uᵢ₊₁         Γ ⊢ Lᵢ : Uᵢ₊₁


Γ ⊢ X : Uᵢ  Γ ⊢ e : X  Γ ⊢ e' : X
----------------------------------
Γ ⊢ e =ₓ e' : Uᵢ


Γ ⊢ X : Uᵢ  Γ,x:X ⊢ Y : Uᵢ      Γ ⊢ X : Uᵢ  Γ,x:X ⊢ A : Lᵢ      Γ ⊢ A : Lᵢ  Γ ⊢ B : Lᵢ
---------------------------     ---------------------------      -----------------------
     Γ ⊢ Πx:X.Y : Uᵢ                  Γ ⊢ Πx:X.A : Lᵢ                Γ ⊢ A ⊸ B : Lᵢ


Γ ⊢ X : Uᵢ  Γ,x:X ⊢ Y : Uᵢ      Γ ⊢ A : Lᵢ  Γ ⊢ B : Lᵢ       Γ ⊢ A : Lᵢ  Γ ⊢ B : Lᵢ
---------------------------     ------------------------      -----------------------
      Γ ⊢ Σx:X.Y : Uᵢ                Γ ⊢ A ⊗ B : Lᵢ               Γ ⊢ A & B : Lᵢ


----------     ----------     -----------
Γ ⊢ 1 : Uᵢ     Γ ⊢ I : Lᵢ     Γ ⊢ ⊤ : Lᵢ


Γ ⊢ A : Lᵢ       Γ ⊢ X : Uᵢ  Γ,x:X ⊢ A : Lᵢ
------------     ---------------------------
Γ ⊢ G A : Uᵢ          Γ ⊢ Fx:X.A : Lᵢ
```

### Intuitionistic Typing
The elimination rule for =ₓ is omitted, refer to HoTT book for details.
```
-----------------         -----------
Γ,x:X,Γ' ⊢ x : X          Γ ⊢ () : 1


Γ ⊢ e : Y    Γ ⊢ X ≡ Y type
----------------------------
        Γ ⊢ e : X


Γ ⊢ e ≡ e' : X
------------------
Γ ⊢ refl : e =ₓ e'


Γ ⊢ e : X    Γ ⊢ e' : [e/x]Y      Γ ⊢ e : Σx:X.Y        Γ ⊢ e : Σx:X.Y
-----------------------------     ---------------     ---------------------
    Γ ⊢ (e, e') : Σx:X.Y           Γ ⊢ π₁ e : X       Γ ⊢ π₂ e : [π₁ e/x]Y


Γ ⊢ Πx:X.Y type    Γ,x:X Γ e : Y       Γ ⊢ e : Πx:X.Y    Γ ⊢ e' : X
---------------------------------      ------------------------------
     Γ ⊢ λx.e : Πx.X.Y                     Γ ⊢ e e' : [e'/x]Y


Γ;⋅ ⊢ e : A
--------------
Γ ⊢ G e : G A
```

### Linear Typing



## References
* https://homotopytypetheory.org/book/
* https://www.cs.cmu.edu/~fp/courses/15816-f01/handouts/linfp.pdf
* https://dl.acm.org/doi/10.1145/2775051.2676969
* https://gist.github.com/gabriel-barrett/0de85a606b64886052854422fb05ce0c
* https://gist.github.com/gabriel-barrett/11988a272bc52f0e848db6eceb03417a
* https://richarde.dev/papers/2020/quantitative/quantitative.pdf
* https://www.type-driven.org.uk/edwinb/papers/idris2.pdf
* https://bentnib.org/quantitative-type-theory.pdf
* https://link.springer.com/chapter/10.1007/978-3-319-30936-1_12