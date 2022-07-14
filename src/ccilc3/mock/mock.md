## concrete syntax

### non-linear functions
```lean
∀ (x : A) -> B
A -> B
```

### linear functions
```lean
∀ (x : A) -o B
A -o B
```

### session types
```lean
!(x : A) >> B
!A >> B

?(x : A) >> B
?A >> B

ch<?(x : A) >> end>
hc<!(x : A) >> end>
```

### match expressions
```lean
case x, y of
  | zero, (succ y) => y
```

### functions
```lean
fun x y => y

fun
  | _ (cons hd tl) => tl

fun foo
  | _ (cons hd tl) => foo tl

fun : ∀ (n : nat) -> vec (S n) -> vec n 
  | _ (cons hd tl) => tl

fun foo : ∀ (n : nat) -> vec (S n) -> vec n 
  | _ (cons hd tl) => foo tl
```

### definitions
```lean
def foo : ∀ (n : nat) -> vec (S n) -> vec n
  | cons x => cons
  | nil y => nil

def bar : nat := foo 1 (cons 1 nil)
```

### inductive types
```lean
data vec (A : U) : nat -> U
  | nil : vec A 0
  | cons : ∀ (n : nat) -> A -> vec A n -> vec A (S n)
```