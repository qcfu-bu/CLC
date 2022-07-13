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
match x, y
  | zero, (succ y) => y

match x, y : ∀ (n : nat) -> vec (S n) -> vec n
  | _, cons hd tl => tl

match y : ∀ {n : nat} -> vec (S n) -> vec n
  | cons hd tl => tl
```

### functions
```lean
fun x y => y

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