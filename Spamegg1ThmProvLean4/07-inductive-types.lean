-- inductive Foo where
--   | constructor₁ : ... → Foo
--   | constructor₂ : ... → Foo
--   ...
--   | constructorₙ : ... → Foo

inductive Weekday where
  | sunday -- : Weekday (this is optional)
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

#check Weekday.sunday
#check Weekday.monday

open Weekday
#check sunday
#check monday
#eval tuesday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1
#eval numberOfDay Weekday.monday  -- 2
#eval numberOfDay Weekday.tuesday -- 3

-- set_option pp.all true
#print numberOfDay -- ... numberOfDay.match_1
-- #print numberOfDay.match_1 -- ... Weekday.casesOn ... -- does not work with Repr
#print Weekday.casesOn -- ... Weekday.rec ...
#check @Weekday.rec

namespace Weekday -- useful to have namespace same name as data type
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday
example : next (previous tuesday) = tuesday := rfl

def next_previous_1 (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

-- tactics version of the same proof
def next_previous_2 (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl
end Weekday

namespace Hidden
inductive Bool where
  | false : Bool
  | true  : Bool

def and (a b : Bool) : Bool :=
  match a with
  | Bool.true  => b
  | Bool.false => Bool.false

def or (a b : Bool) : Bool :=
  match a with
  | Bool.true  => Bool.true
  | Bool.false => b

def not (a : Bool) : Bool :=
  match a with
  | Bool.true  => Bool.false
  | Bool.false => Bool.true

-- inductive Prod (α : Type u) (β : Type v)
--   | mk : α → β → Prod α β

-- inductive Sum (α : Type u) (β : Type v) where
--   | inl : α → Sum α β
--   | inr : β → Sum α β

-- def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
--   match p with
--   | Prod.mk a b => a

-- def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
--   match p with
--   | Prod.mk a b => b

-- with named arguments
inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β

structure Prod2 (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)

inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β

inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α

-- Inductively Defined Propositions
inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p

structure Subtype1 {α : Sort u} (p : α → Prop) where
  val : α
  property : p val

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
deriving Repr

#check @Nat.rec
-- @Nat.recOn :
--   {motive : Nat → Sort u}
--   → (t : Nat)
--   → motive Nat.zero
--   → ((n : Nat) → motive n → motive (Nat.succ n))
--   → motive t

namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

#eval add (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero) -- 2 + 1 = 3

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl
end Nat

inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α

namespace List
def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as := rfl

theorem cons_append (a : α) (as bs : List α):
  append (cons a as) bs = cons a (append as bs) := rfl

-- As an exercise, prove the following:
theorem append_nil (as : List α) : List.append as nil = as := by
  induction as with
  | nil          => rfl
  | cons a as ih => rw [cons_append, ih]

theorem append_assoc (as bs cs : List α):
  List.append (List.append as bs) cs = List.append as (List.append bs cs) := by
  induction as with
  | nil          => repeat rw [nil_append]
  | cons a as ih =>
      calc ((cons a as).append bs).append cs
        _ = (cons a (as.append bs)).append cs := by rw [cons_append]
        _ = cons a ((as.append bs).append cs) := by rw [cons_append]
        _ = cons a (as.append (bs.append cs)) := by rw [ih]

-- Try also defining the function length : {α : Type u} → List α → Nat
-- that returns the length of a list, and prove that it behaves as expected
-- (for example, length (append as bs) = length as + length bs).
def length : List α → _root_.Nat
| nil       => 0
| cons a as => 1 + length as

theorem length_append (as bs : List α):
  length (append as bs) = length as + length bs := by
  induction as with
  | nil          => rw [nil_append, length]; simp
  | cons a as ih => rw [cons_append, length, length, ih, Nat.add_assoc]

end List
end Hidden

def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)

structure Color where
  red : Nat
  green : Nat
  blue : Nat
deriving Repr

def yellow := Color.mk 255 255 0
#eval Color.red yellow

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    (show 0 + 0 = 0 from rfl)
    (fun (n : Nat) (ih : 0 + n = n) =>
      show 0 + Nat.succ n = Nat.succ n from
        calc 0 + Nat.succ n
        _ = Nat.succ (0 + n) := rfl
        _ = Nat.succ n       := by rw [ih]
    )

theorem zero_add2 (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl -- base case
    (fun n ih => by simp)

theorem zero_add3 (n : Nat) : 0 + n = n := by
  induction n with
  | zero      => rfl
  | succ n ih => rw [Nat.add_succ, ih]

theorem zero_add4 (n : Nat) : 0 + n = n := by
  induction n
  case zero      => rfl
  case succ n ih => rw [Nat.add_succ, ih]

theorem zero_add5 (n : Nat) : 0 + n = n := by
  induction n <;> simp -- simp [*, Nat.add_zero, Nat.add_succ]

-- theorem succ_add (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
--   induction n <;> simp [*, add_zero, add_succ]

-- theorem add_comm (m n : Nat) : m + n = n + m := by
--   induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

-- theorem add_assoc2 (m n k : Nat) : m + n + k = m + (n + k) := by
--   induction k <;> simp [*, add_zero, add_succ]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + Nat.succ k = m + (n + Nat.succ k) from
      calc m + n + Nat.succ k
        _ = Nat.succ (m + n + k)   := rfl
        _ = Nat.succ (m + (n + k)) := by rw [ih]
        _ = m + Nat.succ (n + k)   := rfl
        _ = m + (n + Nat.succ k)   := rfl)

theorem add_assoc2 (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k with
  | zero      => simp
  | succ k ih => rw [← Nat.succ_eq_add_one, Nat.add_succ]; rw [ih]; rfl

theorem succ_add (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) :=
  Nat.recOn (motive := fun x => Nat.succ n + x = Nat.succ (n + x)) m
    (show Nat.succ n + 0 = Nat.succ (n + 0) from rfl)
    (fun (m : Nat) (ih : Nat.succ n + m = Nat.succ (n + m)) =>
     show Nat.succ n + Nat.succ m = Nat.succ (n + Nat.succ m) from
     calc Nat.succ n + Nat.succ m
       _ = Nat.succ (Nat.succ n + m)   := rfl
       _ = Nat.succ (Nat.succ (n + m)) := by rw [ih]
       _ = Nat.succ (n + Nat.succ m)   := rfl)

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + Nat.succ n = Nat.succ n + m from
    calc m + Nat.succ n
      _ = Nat.succ (m + n) := rfl
      _ = Nat.succ (n + m) := by rw [ih]
      _ = Nat.succ n + m   := by rw [succ_add])

theorem succ_add2 (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) :=
  Nat.recOn (motive := fun x => Nat.succ n + x = Nat.succ (n + x)) m
    rfl
    (fun m ih => by simp only [Nat.add_succ, ih])

theorem add_comm2 (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp)
    (fun m ih => by simp only [Nat.add_succ, succ_add2, ih])

theorem add_comm3 (m n : Nat) : m + n = n + m := by
  induction n with
  | zero      => simp
  | succ n ih => rw [← Nat.succ_eq_add_one, succ_add, Nat.add_succ, ih]

inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

inductive CBTree where
  | leaf : CBTree
  | sup  : (Nat → CBTree) → CBTree

namespace CBTree
def succ (t : CBTree) : CBTree := sup (fun _ => t)
def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)
def omega : CBTree := sup toCBTree
end CBTree

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : Nat ⊢ p (succ a)

example (n : Nat) (h : n ≠ 0) : Nat.succ (Nat.pred n) = n := by
  cases n with
  | zero   => -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m => -- goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl -- simp also works

def f (n : Nat) : Nat := by cases n; exact 3; exact 7
example : f 0 = 3 := rfl
example : f 5 = 7 := rfl

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f2 {n : Nat} (t : Tuple α n) : Nat := by cases n; exact 3; exact 7
def myTuple : Tuple Nat 3 := ⟨[0, 1, 2], rfl⟩
example : f2 myTuple = 7 := rfl

inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b   => exact b

def silly2 (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b   => exact b

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  -- generalize m + 3 * k = n
  -- cases n
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)

example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  -- have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  -- cases h
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne

/-
theorem Nat.mod.inductionOn
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
-/
example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption

example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2

example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]

example (m n k : Nat) (h : Nat.succ (Nat.succ m) = Nat.succ (Nat.succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']

example (m n : Nat) (h : Nat.succ m = 0) : n = n + 7 := by injection h
example (m n : Nat) (h : Nat.succ m = 0) : n = n + 7 := by contradiction
example (h : 7 = 4) : False := by contradiction

-- Inductive Families
-- inductive foo : ... → Sort u where
--   | constructor₁ : ... → foo ...
--   | constructor₂ : ... → foo ...
--   ...
--   | constructorₙ : ... → foo ...

namespace Hidden2
inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

-- inductive Eq {α : Sort u} (a : α) : α → Prop where
--   | refl : Eq a a

theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁

theorem subst2 {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

theorem subst3 {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

-- set_option pp.all true
-- #print subst         -- ... subst.match_1 ...
-- #print subst.match_1 -- ... Eq.casesOn ...
-- #print Eq.casesOn    -- ... Eq.rec ...
end Hidden2

universe u v
#check (@Eq.rec : {α : Sort u} → {a : α} → {motive : (x : α) → a = x → Sort v}
  → motive a rfl → {b : α} → (h : a = b) → motive b h)

-- Mutual inductive families
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

mutual
  inductive Tree (α : Type u) where
    | node : α → TreeList α → Tree α
  inductive TreeList (α : Type u) where
    | nil  : TreeList α
    | cons : Tree α → TreeList α → TreeList α
end

inductive Tree2 (α : Type u) where
  | mk : α → List (Tree2 α) → Tree2 α

namespace Exercises
-- In the following example, we prove symm and leave as
-- exercises the theorems trans and congr (congruence).
theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  match h₂ with
  | rfl => h₁

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  match h with
  | rfl => rfl

-- Try defining other operations on the natural numbers, such as multiplication,
-- the predecessor function (with pred 0 = 0), truncated subtraction
-- (with n - m = 0 when m is greater than or equal to n), and exponentiation.
-- Then try proving some of their basic properties,
-- building on the theorems we have already proved.
-- Since many of these are already defined in Lean's core library,
-- you should work within a namespace named Hidden, or something like that,
-- in order to avoid name clashes.
namespace Hidden1
end Hidden1

-- Define some operations on lists, like a length function or the reverse function.
-- Prove some properties, such as the following:
-- a. length (s ++ t) = length s + length t
-- b. length (reverse t) = length t
-- c. reverse (reverse t) = t
namespace Hidden2
def lenHelp (xs : List α) (acc : Nat) : Nat :=
  match xs with
  | []      => acc
  | _ :: xs => lenHelp xs (acc + 1)
-- def len (xs : List α) : Nat := lenHelp xs 0
def len (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: xs => 1 + len xs

def revHelp (xs : List α) (acc : List α) : List α :=
  match xs with
  | []      => acc
  | x :: xs => revHelp xs (x :: acc)
-- def rev (xs : List α) : List α := revHelp xs []
def rev (xs : List α) : List α :=
  match xs with
  | []      => []
  | x :: xs => rev xs ++ [x]

theorem len_append (xs ys : List α) : len (xs ++ ys) = len xs + len ys := by
  induction xs with
  | nil          => simp; rfl
  | cons x xs ih =>
    calc  len (x :: xs ++ ys)
      _ = len (x :: (xs ++ ys))  := by rfl
      _ = 1 + len (xs ++ ys)     := by rfl
      _ = 1 + (len xs + len ys)  := by rw [ih]
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
end Hidden2

-- Define an inductive data type consisting of terms
-- built up from the following constructors:
--     const n, a constant denoting the natural number n
--     var n, a variable, numbered n
--     plus s t, denoting the sum of s and t
--     times s t, denoting the product of s and t
inductive Term where
| const : Nat → Term
| var   : Nat → Term
| plus  : Term → Term → Term
| times : Term → Term → Term
deriving Repr

-- Recursively define a function that evaluates any such term with respect
-- to an assignment of values to the variables.
def evalT (t : Term) (asgn : Nat → Nat) : Nat :=
  match t with
  | Term.const n   => n
  | Term.var n     => asgn n
  | Term.plus s t  => (evalT s asgn) + (evalT t asgn)
  | Term.times s t => (evalT s asgn) * (evalT t asgn)

def four := Term.const 4
def five := Term.var 1
def nine := Term.var 2
def asgnT (n : Nat) := if n = 1 then 5 else if n = 2 then 9 else 0
#eval evalT (Term.times nine (Term.plus four five)) asgnT -- 81

-- Similarly, define the type of propositional formulas, as well as
-- functions on the type of such formulas: an evaluation function,
-- functions that measure the complexity of a formula,
-- and a function that substitutes another formula for a given variable.
inductive Fm where
| f    : Fm
| t    : Fm
| var  : Nat → Fm
| and  : Fm → Fm → Fm
| or   : Fm → Fm → Fm
| not  : Fm → Fm
| cond : Fm → Fm → Fm
| bic  : Fm → Fm → Fm
deriving Repr

def evalF (fm : Fm) (asgn : Nat → Bool) : Bool :=
  match fm with
  | Fm.f        => false
  | Fm.t        => true
  | Fm.var n    => asgn n
  | Fm.and g h  => (evalF g asgn) && (evalF h asgn)
  | Fm.or g h   => (evalF g asgn) || (evalF h asgn)
  | Fm.not g    => !(evalF g asgn)
  | Fm.cond g h => if (evalF g asgn) then (evalF h asgn) else true
  | Fm.bic g h  => (evalF g asgn) == (evalF h asgn)

def f1 := Fm.and (Fm.var 1) (Fm.var 2)
def f2 := Fm.bic f1 f1
def f3 := Fm.cond f1 f2
def f4 := Fm.cond f2 f1
def asgn (n : Nat) : Bool := if n == 1 then true else false
#eval evalF f3 asgn -- true
#eval evalF f4 asgn -- false

def comp (fm : Fm) : Nat :=
  match fm with
  | Fm.f        => 0
  | Fm.t        => 0
  | Fm.var _    => 0
  | Fm.and g h  => comp g + comp h + 1
  | Fm.or g h   => comp g + comp h + 1
  | Fm.not g    => comp g + 1
  | Fm.cond g h => comp g + comp h + 1
  | Fm.bic g h  => comp g + comp h + 1

#eval comp f4 -- 5 b/c ((P ∧ Q) ⇔ (P ∧ Q)) → (P ∧ Q)

def sub (fm : Fm) (m : Nat) (subFm : Fm) : Fm :=
  match fm with
  | Fm.f        => fm
  | Fm.t        => fm
  | Fm.var n    => if m == n then subFm else fm
  | Fm.and g h  => Fm.and (sub g m subFm) (sub h m subFm)
  | Fm.or g h   => Fm.or (sub g m subFm) (sub h m subFm)
  | Fm.not g    => Fm.not (sub g m subFm)
  | Fm.cond g h => Fm.cond (sub g m subFm) (sub h m subFm)
  | Fm.bic g h  => Fm.bic (sub g m subFm) (sub h m subFm)

-- f4 is: ((P ∧ Q) ⇔ (P ∧ Q)) → (P ∧ Q), we wanna sub Q = false
#eval sub f4 2 Fm.f -- ((P ∧ f) ⇔ (P ∧ f)) → (P ∧ f)

end Exercises
