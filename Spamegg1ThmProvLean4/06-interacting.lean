-- import Bar.Baz.Blah
-- This imports Bar/Baz/Blah.olean
-- Importing is transitive.

section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]
end

-- def Foo.bar : Nat := 1 -- this is a macro, it expands to:
namespace Foo
def bar : Nat := 1
end Foo

open Foo
#check bar
#check Foo.bar

def String.add (a b : String) : String := a ++ b
def Bool.add (a b : Bool) : Bool := a != b
def add (α β : Type) : Type := Sum α β

open Bool
open String
-- #check add -- ambiguous
#check String.add           -- String → String → String
#check Bool.add             -- Bool → Bool → Bool
#check _root_.add           -- Type → Type → Type

#check add "hello" "world"  -- String
#check add true false       -- Bool
#check add Nat Nat          -- Type

protected def Spam.bar : Nat := 1 -- disable short name bar
open Spam
-- #check bar -- error
#check Spam.bar

namespace OpenCloseNamespace
open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3

open Nat hiding succ gcd
#check zero     -- Nat
-- #eval gcd 15 6  -- error
#eval Nat.gcd 15 6  -- 3

open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3  -- 7

-- export Nat (succ add sub)
end OpenCloseNamespace

namespace Simp1
  def isPrefix (l₁ : List α) (l₂ : List α) : Prop := ∃ t, l₁ ++ t = l₂
  @[simp]
  theorem List.isPrefix_self (as : List α) : isPrefix as as :=
    ⟨[], by simp⟩
  example : isPrefix [1, 2, 3] [1, 2, 3] := by simp
end Simp1

namespace Simp2
  def isPrefix (l₁ : List α) (l₂ : List α) : Prop := ∃ t, l₁ ++ t = l₂
  theorem List.isPrefix_self (as : List α) : isPrefix as as :=
    ⟨[], by simp⟩
  attribute [simp] List.isPrefix_self
end Simp2

namespace Simp3
  def isPrefix (l₁ : List α) (l₂ : List α) : Prop := ∃ t, l₁ ++ t = l₂
  theorem List.isPrefix_self (as : List α) : isPrefix as as := ⟨[], by simp⟩
  attribute [local simp] List.isPrefix_self
  example : isPrefix [1, 2, 3] [1, 2, 3] := by simp
  -- Error:
  -- example : isPrefix [1, 2, 3] [1, 2, 3] := by
  --  simp
end Simp3

namespace Simp4
  def isPrefix (l₁ : List α) (l₂ : List α) : Prop := ∃ t, l₁ ++ t = l₂
  instance : LE (List α) where le := isPrefix
  theorem List.isPrefix_self (as : List α) : as ≤ as := ⟨[], by simp⟩
end Simp4

namespace Simp5
def isPrefix (l₁ : List α) (l₂ : List α) : Prop := ∃ t, l₁ ++ t = l₂
def instLe : LE (List α) := { le := isPrefix }

section
  attribute [local instance] instLe
  example (as : List α) : as ≤ as := ⟨[], by simp⟩
end

-- Error:
-- example (as : List α) : as ≤ as :=
--  ⟨[], by simp⟩
end Simp5

namespace Implicit1
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 th2 (th1 reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- r ?m1 ?m2 → r ?m1 ?m3 → r ?m2 ?m3

end Implicit1

namespace Implicit2
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- euclidean r
end Implicit2

namespace Notation
-- infixl:65   " + " => HAdd.hAdd  -- left-associative
-- infix:50    " = " => Eq         -- non-associative
-- infixr:80   " ^ " => HPow.hPow  -- right-associative
-- prefix:100  "-"   => Neg.neg
-- set_option quotPrecheck false
-- postfix:max "⁻¹"  => Inv.inv

-- notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
-- notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
-- notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
-- notation:100 "-" arg:100 => Neg.neg arg
-- notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- `max` is a shorthand for precedence 1024
-- notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs -- default right assoc
-- notation:max "(" e ")" => e
-- notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
-- notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0

end Notation

-- coercions
variable (m n : Nat)
variable (i j : Int)
#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int

-- displaying
-- examples with equality
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

-- examples with And
#check And
#check And.intro
#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo

namespace SettingOptions
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1
end SettingOptions

#check Nat.succ_ne_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.le_of_succ_le_succ
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec
#check @And.intro
#check @And.casesOn
#check @And.left
#check @And.right
#check @Or.inl
#check @Or.inr
#check @Or.elim
#check @Exists.intro
#check @Exists.elim
#check @Eq.refl
#check @Eq.subst

namespace AutoBoundImplicit
-- universe u v w -- avoid this
-- def compose.{u, v, w} -- by writing this
--             {α : Type u} {β : Type v} {γ : Type w}
--             (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)

def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x) -- ambiguous
#check @compose
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
set_option autoImplicit false
end AutoBoundImplicit

namespace ImplicitLambdas
variable (ρ : Type) (m : Type → Type) [Monad m]
-- instance : Monad (ReaderT ρ m) where
--   pure := ReaderT.pure
--   bind := ReaderT.bind
end ImplicitLambdas

namespace ex2
def id1 : {α : Type} → α → α := fun x => x
def listId : List ({α : Type} → α → α) := (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before `fun`
def id2 : {α : Type} → α → α := @fun α (x : α) => id1 x
def id3 : {α : Type} → α → α := @fun α x => id1 x
def id4 : {α : Type} → α → α := fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α := fun {α} x => id1 x
end ex2

namespace ex3
#check (· + 1) -- fun a => a + 1
#check (2 - ·) -- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (·*·) 1 -- 120
def f (x y z : Nat) := x + y + z
#check (f · 1 ·) -- fun a b => f a 1 b
#eval [(1, 2), (3, 4), (5, 6)].map (·.1) -- [1, 3, 5]
end ex3

namespace NamedArguments
def sum (xs : List Nat) := xs.foldl (init := 0) (·+·)
#eval sum [1, 2, 3, 4] -- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b := Eq.subst (motive := fun x => p a x b) h₂ h₁
end NamedArguments

namespace ex5
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) := x + y + w - z
example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl
example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl
example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl
example : f = (fun x z => x + 1 + 2 - z) := rfl
example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl
example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl
def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]
example : g = fun (a c : α) => a + c := rfl
example (x : α) : g (c := x) = fun (a : α) => a + x := rfl
example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl
example (x : α) : g x = fun (c : α) => x + c := rfl
example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
end ex5

inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | app    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none

example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
