open Nat
-- def sub1 : Nat → Nat
--   | zero   => zero
--   | succ x => x
-- def isZero : Nat → Bool
--   | zero   => true
--   | succ x => false
def sub1 : Nat → Nat
  | 0   => 0
  | x+1 => x
def isZero : Nat → Bool
  | 0   => true
  | x+1 => false

example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl
example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl
example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl

def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0

namespace Hidden
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => rfl  -- proof that not (not true) = true
  | false => rfl  -- proof that not (not false) = false
end Hidden

example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq

def sub2 : Nat → Nat
  | 0   => 0
  | 1   => 0
  | x+2 => x
example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl
example : sub2 5 = 3 := rfl

def sub2_2 : Nat → Nat :=
  fun x =>
    match x with
    | 0   => 0
    | 1   => 0
    | x+2 => x

example (p q : α → Prop) : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def spam : Nat × Nat → Nat
  | (0, n)     => 0
  | (m+1, 0)   => 1
  | (m+1, n+1) => 2

def ham : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2

def egg : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b

namespace Hidden
def and : Bool → Bool → Bool
  | true,  a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | true,  _ => true
  | false, a => a

def cond : Bool → α → α → α
  | true,  x, y => x
  | false, x, y => y
end Hidden

def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as

-- wildcards
def spam2 : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2

def spam3 : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
example : spam3 0     0     = 0 := rfl
example : spam3 0     (n+1) = 0 := rfl
example : spam3 (m+1) 0     = 1 := rfl
example : spam3 (m+1) (n+1) = 2 := rfl

def spam4 : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- the "incomplete" case

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl

def bar2 : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b

def foo2 : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1

open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat)   : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

theorem zero_add2 : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]

def mul : Nat → Nat → Nat
  | n, zero   => zero
  | n, succ m => add (mul n m) n

def add2 (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add2 m n)

def add3 (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add3 m n)

def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl
example : fib 7 = 21 := rfl

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100 -- 573147844013817084101

def fibFast2 (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2

variable (C : Nat → Type u)
#check (@Nat.below C : Nat → Type u)
#reduce @Nat.below C (3 : Nat)
#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)

def append : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => a :: append as bs
example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl

def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs
#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10] -- [5, 7, 9]

def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []
#check @replicate.loop -- {α : Type} → α → Nat → List α → List α

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
    : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n]; rw [Nat.add_succ, Nat.succ_add]
  exact aux n []

def replicate2 (n : Nat) (a : α) : List α := loop n []
  where
    loop : Nat → List α → List α
      | 0,   as => as
      | n+1, as => loop n (a::as)

theorem length_replicate2 (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α): (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n]; rw [Nat.add_succ, Nat.succ_add]

-- well founded recursion
namespace WellFoundedRecursion
variable (α : Sort u)
variable (r : α → α → Prop)
#check (Acc r : α → Prop)
#check (WellFounded r : Prop)

noncomputable def f {α : Sort u}
  (r : α → α → Prop)
  (h : WellFounded r)
  (C : α → Sort v)
  (F : (x : α) → ((y : α) → r y x → C y) → C x)
  : (x : α) → C x := WellFounded.fix h F
end WellFoundedRecursion

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_lemma h) y + 1
  else zero

noncomputable def div := WellFounded.fix (measure id).wf div.F
#reduce div 8 2 -- 4

namespace DivExample
def div (x y : Nat) : Nat :=
 if h : 0 < y ∧ y ≤ x then
   have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
   div (x - y) y + 1
 else
   0

example (x y : Nat) : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 := by
  conv => lhs; unfold div; simp -- unfold occurrence in the left-hand-side of the equation

example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div; simp [h]
end DivExample

def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    -- have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2]
#eval natToBin 1234567

instance (priority := low) [SizeOf α] : WellFoundedRelation α := sizeOfWFRel

def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as.get ⟨i, h⟩
      if p a then go (i+1) (r.push a) else r
    else r
  termination_by as.size - i

namespace DivExample2
  theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
    fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos
  def div (x y : Nat) : Nat := if h : 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0
  decreasing_by apply div_lemma; assumption
end DivExample2

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y) -- lexical ordering is well-founded
decreasing_by
  all_goals simp_wf -- unfolds well-founded recursion auxiliary definitions
  · apply Prod.Lex.left; simp_arith
  · apply Prod.Lex.right; simp_arith
  · apply Prod.Lex.left; simp_arith

#eval ack 2 2 -- this is dangerous! ack 4 4 destroys Lean server!

def natToBin2 : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 => natToBin2 ((n + 2) / 2) ++ [n % 2]
decreasing_by sorry -- "trust me bro"
#eval natToBin 1234567

def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry
#check unsound 0 -- `unsound 0` is a proof of `False`
#print axioms unsound -- 'unsound' depends on axioms: [sorryAx]

-- mutual recursion again
mutual
  def even : Nat → Bool
    | 0   => true
    | n+1 => odd n

  def odd : Nat → Bool
    | 0   => false
    | n+1 => even n
end

example : even (a + 1) = odd a := by simp [even]
example : odd (a + 1) = even a := by simp [odd]
theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a; induction a
  . simp [even, odd]
  . simp [even, odd, *]

mutual
 inductive Even : Nat → Prop where
   | even_zero : Even 0
   | even_succ : ∀ n, Odd n → Even (n + 1)
 inductive Odd : Nat → Prop where
   | odd_succ : ∀ n, Even n → Odd (n + 1)
end

open Even Odd
theorem not_odd_zero : ¬ Odd 0 := fun h => nomatch h
theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
  | _, odd_succ n h => h
theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
  | _, even_succ n h => h

inductive Term where
  | const : String → Term
  | app   : String → List Term → Term

namespace Term
mutual
  def numConsts : Term → Nat
    | const _  => 1
    | app _ cs => numConstsLst cs
  def numConstsLst : List Term → Nat
    | []      => 0
    | c :: cs => numConsts c + numConstsLst cs
end

def sample := app "f" [app "g" [const "x"], const "y"]
#eval numConsts sample -- 2

mutual
  def replaceConst (a b : String) : Term → Term
    | const c  => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)
  def replaceConstLst (a b : String) : List Term → List Term
    | []      => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end
mutual
  theorem numConsts_replaceConst (a b : String) (e : Term)
    : numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c  => simp [replaceConst]; split <;> simp [numConsts]
    | app f cs => simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]

  theorem numConsts_replaceConstLst (a b : String) (es : List Term)
    : numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | []      => simp [replaceConstLst, numConstsLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
            numConsts_replaceConstLst a b cs]
end
end Term

-- Dependent pattern matching
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector
#check @Vector.casesOn
/-
  {α : Type u}
  → {motive : (a : Nat) → Vector α a → Sort v} →
  → {a : Nat} → (t : Vector α a)
  → motive 0 nil
  → ((a : α) → {n : Nat} → (a_1 : Vector α n) → motive (n + 1) (cons a a_1))
  → motive a t
-/

def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
      fun (h : m + 1 = n + 1) =>
        Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n := tailAux v rfl

def head : {n : Nat} → Vector α (n+1) → α
  | n, cons a as => a

def tail2 : {n : Nat} → Vector α (n+1) → Vector α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vector α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : {n : Nat} → Vector α n → Vector β n → Vector (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)

def map2 (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map2 f as bs)

#print map
#print map.match_1
end Vector

-- Inaccessible patterns
namespace Inaccessible

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def add1 [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add1 as bs)

def add2 [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | .(_), nil,       nil       => nil -- _ is also OK instead of .(_)
  | .(_), cons a as, cons b bs => cons (a + b) (add2 as bs)

def add3 [Add α] {n : Nat} : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add3 as bs)

def add4 [Add α] : Vector α n → Vector α n → Vector α n -- auto bound implicits
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add4 as bs)

def head : Vector α (n+1) → α
  | cons a as => a

def tail : Vector α (n+1) → Vector α n
  | cons a as => as

theorem eta : (v : Vector α (n+1)) → cons (head v) (tail v) = v
  | cons a as => rfl

def map (f : α → β → γ) : Vector α n → Vector β n → Vector γ n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : Vector α n → Vector β n → Vector (α × β) n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a, b) (zip as bs)

end Vector
end Inaccessible

-- Match expressions
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true

def filter (p : α → Bool) : List α → List α
  | []      => []
  | a :: as =>
    match p a with
    | true  => a :: filter p as
    | false => filter p as

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl

def foo1 (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
    | 0,   true  => 0
    | m+1, true  => m + 7
    | 0,   false => 5
    | m+1, false => m + 3

#eval foo1 7 true false
example : foo1 7 true false = 9 := rfl

def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n

namespace DestructProps
variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩
end DestructProps

-- Local Rec
namespace LocalRec
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop -- {α : Type} → α → Nat → List α → List α

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n]; rw[Nat.add_succ, Nat.succ_add]
  exact aux n []

def replicate1 (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate1 (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n]; rw [Nat.add_succ, Nat.succ_add]

end LocalRec

-- Exercises
namespace Exercises
-- Open a namespace Hidden to avoid naming conflicts, and use the equation compiler
-- to define addition, multiplication, and exponentiation on the natural numbers.
-- Then use the equation compiler to derive some of their basic properties.
namespace HiddenNat

def add : Nat → Nat → Nat
| m, 0     => m
| m, n + 1 => (add m n) + 1

def mul : Nat → Nat → Nat
| _, 0     => 0
| m, n + 1 => add (mul m n) m

def exp : Nat → Nat → Nat
| _, 0      => 1
| m, succ n => mul (exp m n) m

theorem add_zero : ∀ n : Nat, add n 0 = n
  | _   => rfl

-- this is written in direct tactic style
theorem add_one_inj {a b : Nat} : a + 1 = b + 1 ↔ a = b :=
  by apply Iff.intro <;> simp

-- these are written with universal quantifiers, in equational style
theorem zero_add : ∀ n, add 0 n = n
  | 0     => rfl
  | n + 1 => by rw [add, add_one_inj, zero_add]

theorem add_succ : ∀ m n : Nat, add m (succ n) = succ (add m n)
  | _, _ => rfl

theorem succ_add : ∀ m n : Nat, add (succ m) n = succ (add m n)
  | m, 0     => rfl
  | m, n + 1 => by rw [add, succ_add, add_one_inj]; rfl

theorem add_assoc : ∀ a b c : Nat, add a (add b c) = add (add a b) c
  | _, _, 0     => rfl
  | a, b, c + 1 => by rw [add, add, add, add_one_inj, add_assoc]

-- this is written in direct induction tactic style
theorem add_comm (m n : Nat) : add m n = add n m := by
  induction n with
  | zero      => rw [add, zero_add]
  | succ n ih => rw [add, succ_add, ih]

-- this is needed in succ_mul
theorem add_add_comm (a b c : Nat) : add (add a b) c = add (add a c) b := by
  induction c with
  | zero      => rfl
  | succ c ih => rw [add, add, ih, succ_add]

-- And similarly, I keep changing style back and forth below.
theorem mul_zero (m : Nat): mul m zero = zero := rfl

theorem zero_mul: ∀ m : Nat, mul zero m = zero
  | 0     => rfl
  | m + 1 => by rw [mul, add, zero_mul]

theorem mul_one (m : Nat): mul m 1 = m := by rw [mul, mul_zero, zero_add]
theorem one_mul : ∀ m : Nat, mul 1 m = m
  | 0     => rfl
  | m + 1 => by rw [mul, add, add_one_inj, add_zero, one_mul]

theorem mul_succ (m n : Nat) : mul m (succ n) = add (mul m n) m := rfl
theorem succ_mul (m n : Nat) : mul (succ m) n = add (mul m n) n := by
  induction n with
  | zero      => simp; rfl
  | succ n ih => rw [mul, mul, ih, add, add, add_one_inj, add_add_comm]

theorem mul_add (a b c : Nat) : mul a (add b c) = add (mul a b) (mul a c) := by
  induction c with
  | zero      => rw [mul_zero, add_zero, add_zero]
  | succ c ih => rw [add, mul, mul, ih, add_assoc]

theorem mul_assoc (a b c : Nat) : mul a (mul b c) = mul (mul a b) c := by
  induction c with
  | zero      => rfl
  | succ c ih => rw [mul, mul_add, ih, mul]

theorem mul_comm (m n : Nat) : mul m n = mul n m := by
  induction n with
  | zero      => rw [mul_zero, zero_mul]
  | succ n ih => rw [mul, succ_mul, ih]

theorem exp_zero : ∀ n : Nat, exp n 0 = 1
  | 0     => rfl
  | n + 1 => rfl

theorem zero_exp : ∀ n : Nat, exp 0 (n + 1) = 0
  | _ => rfl

theorem exp_one (n : Nat) : exp n 1 = n := by
  induction n with
  | zero   => rfl
  | succ n => rw [exp, exp_zero, one_mul]

theorem one_exp : ∀ n : Nat, exp 1 n = 1
  | 0     => rfl
  | n + 1 => by rw [exp, one_exp, mul_one]

theorem exp_succ : ∀ m n : Nat, exp m (n+1) = mul (exp m n) m
  | 0, _     => rfl
  | m + 1, n => by rw [exp]

theorem exp_add : ∀ a b c : Nat, exp a (b+c) = mul (exp a b) (exp a c)
  | a, b, 0     => by simp [exp_zero, mul_one]
  | a, b, c + 1 =>
    calc  exp a (b + (c + 1))
      _ = exp a ((b + c) + 1)             := by rw [Nat.add_assoc]
      _ = mul (exp a (b + c)) a           := by rw [exp]
      _ = mul (mul (exp a b) (exp a c)) a := by rw [exp_add] -- ih
      _ = mul (exp a b) (mul (exp a c) a) := by rw [mul_assoc]
      _ = mul (exp a b) (exp a (c + 1))   := by rw [exp]

theorem exp_mul : ∀ a b c : Nat, exp a (b*c) = exp (exp a b) c
  | a, b, 0     => by simp [mul_zero, exp_zero]
  | a, b, c + 1 =>
    calc  exp a (b * (c + 1))
      _ = exp a (b * c + b)               := by rw [Nat.mul_add, Nat.mul_one]
      _ = mul (exp a (b * c)) (exp a b)   := by rw [exp_add]
      _ = mul (exp (exp a b) c) (exp a b) := by rw [exp_mul] -- ih
-- I think this much is enough! :)
end HiddenNat

-- Similarly, use the equation compiler to define some basic operations on lists
-- (like the reverse function) and prove theorems about lists by induction
-- (such as the fact that reverse (reverse xs) = xs for any list xs).
namespace HiddenList

def len : List α → Nat
  | []      => 0
  | _ :: xs => 1 + len xs

def rev : List α → List α
  | []      => []
  | x :: xs => rev xs ++ [x]

-- written in different style, without "induction xs with"
theorem len_append : ∀ xs ys : List α, len (xs ++ ys) = len xs + len ys
  | [], _       => by simp; rfl
  | x :: xs, ys =>
    calc  len (x :: xs ++ ys)
      _ = len (x :: (xs ++ ys))  := by rfl
      _ = 1 + len (xs ++ ys)     := by rfl
      _ = 1 + (len xs + len ys)  := by rw [len_append] -- inductive hypothesis!
      _ = (1 + len xs) + len ys  := by rw [Nat.add_assoc]
      _ = len (x :: xs) + len ys := by rfl

theorem len_rev (xs : List α) : len (rev xs) = len xs := by
  induction xs with
  | nil          => rfl
  | cons x xs ih =>
    calc  len (rev (x :: xs))
      _ = len (rev xs ++ [x])    := by rfl
      _ = len (rev xs) + len [x] := by rw [len_append]
      _ = len (rev xs) + 1       := by rfl
      _ = 1 + len (rev xs)       := by rw [Nat.add_comm]
      _ = 1 + len xs             := by rw [ih]
      _ = len (x :: xs)          := by rfl

theorem rev_append (y : α) (xs : List α) : rev (xs ++ [y]) = rev [y] ++ rev xs := by
  induction xs with
  | nil          => rfl
  | cons x xs ih =>
    calc rev (x :: xs ++ [y])
      _ = rev (x :: (xs ++ [y]))   := by rfl
      _ = rev (xs ++ [y]) ++ [x]   := by rfl
      _ = rev [y] ++ rev xs ++ [x] := by rw [ih]
      _ = rev [y] ++ rev (x :: xs) := by rfl

theorem rev_rev (xs : List α) : rev (rev xs) = xs := by
  induction xs with
  | nil          => rfl
  | cons x xs ih =>
    calc  rev (rev (x :: xs))
      _ = rev (rev xs ++ [x])     := by rfl
      _ = rev [x] ++ rev (rev xs) := by rw [rev_append]
      _ = rev [x] ++ xs           := by rw [ih]
      _ = x :: xs                 := by rfl
end HiddenList

-- Define your own function to carry out
-- course-of-value recursion on the natural numbers.
-- Similarly, see if you can figure out how to define WellFounded.fix on your own.
-- NOT SURE HOW TO DO THIS!

-- Following the examples in Section Dependent Pattern Matching,
-- define a function that will append two vectors.
-- This is tricky; you will have to define an auxiliary function.
-- NOT SURE HOW TO DO THIS!

-- Consider the following type of arithmetic expressions.
-- The idea is that var n is a variable, vₙ, and
-- const n is the constant whose value is n.
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
deriving Repr

open Expr
def sampleExpr : Expr := plus (times (var 0) (const 7)) (times (const 2) (var 1))

-- Here sampleExpr represents (v₀ * 7) + (2 * v₁).
-- Write a function that evaluates such an expression, evaluating each var n to v n.
def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n -- sorry
  | var n       => v n
  | plus  e₁ e₂ => (eval v e₁) + (eval v e₂)-- sorry
  | times e₁ e₂ => (eval v e₁) * (eval v e₂)-- sorry

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr -- 47

-- Implement "constant fusion," a procedure that simplifies subterms like 5 + 7 to 12.
def simpConst : Expr → Expr
  | plus  (const n₁) (const n₂) => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

#eval simpConst (plus (const 3) (const 4)) -- const 7

-- Using the auxiliary function simpConst, define a function "fuse":
-- to simplify a plus or a times, first simplify the arguments recursively,
-- and then apply simpConst to try to simplify the result.
def fuse : Expr → Expr
  | plus  e₁ e₂ => simpConst (plus  (fuse e₁) (fuse e₂))
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))
  | e           => e

-- The last two theorems show that the definitions preserve the value.
theorem simpConst_eq (v : Nat → Nat)
  : ∀ e : Expr, eval v (simpConst e) = eval v e
  | const n                       => rfl
  | var n                         => rfl
  | plus  (const _)   (const _)   => by rw [simpConst]; repeat rw [eval]
  | plus  (const _)   (var _)
  | plus  (const _)   (plus _ _)
  | plus  (const _)   (times _ _)
  | plus  (var _)     _
  | plus  (plus _ _)  _
  | plus  (times _ _) _           => rfl
  | times (const _)   (const _)   => by rw [simpConst]; repeat rw [eval]
  | times (const _)   (var _)
  | times (const _)   (plus _ _)
  | times (const _)   (times _ _)
  | times (var _)     _
  | times (plus _ _)  _
  | times (times _ _) _           => rfl

theorem fuse_eq (v : Nat → Nat)
  : ∀ e : Expr, eval v (fuse e) = eval v e
  | const n     => rfl
  | var n       => rfl
  | plus  e₁ e₂
  | times e₁ e₂ => by rw [fuse, simpConst_eq, eval, fuse_eq, fuse_eq]; rfl
end Exercises
