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

namespace Exercises
-- Try defining other operations on the natural numbers, such as multiplication,
-- the predecessor function (with pred 0 = 0), truncated subtraction
-- (with n - m = 0 when m is greater than or equal to n), and exponentiation.
-- Then try proving some of their basic properties,
-- building on the theorems we have already proved.
-- Since many of these are already defined in Lean's core library,
-- you should work within a namespace named Hidden, or something like that,
-- in order to avoid name clashes.

-- Define some operations on lists, like a length function or the reverse function.
-- Prove some properties, such as the following:
-- a. length (s ++ t) = length s + length t
-- b. length (reverse t) = length t
-- c. reverse (reverse t) = t

-- Define an inductive data type consisting of terms
-- built up from the following constructors:
--     const n, a constant denoting the natural number n
--     var n, a variable, numbered n
--     plus s t, denoting the sum of s and t
--     times s t, denoting the product of s and t

-- Recursively define a function that evaluates any such term with respect
-- to an assignment of values to the variables.

-- Similarly, define the type of propositional formulas, as well as
-- functions on the type of such formulas: an evaluation function,
-- functions that measure the complexity of a formula,
-- and a function that substitutes another formula for a given variable.
end Exercises
