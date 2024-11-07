/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

-- Types as objects
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type

#check List α    -- Type
#check List Nat  -- Type

#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5

#check List    -- List.{u} (α : Type u) : Type u
#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)

-- universe u
def H.{u} (α : Type u) : Type u := Prod α α
#check H    -- Type u → Type u

#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred
#eval (λ x : Nat => x + 5) 10    -- 15

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun _ : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

#check (fun x : Nat => x) 1     -- Nat
#check (fun _ : Nat => true) 1  -- Bool

def h (n : Nat) : String := toString n
def j (s : String) : Bool := s.length > 0
#check (fun (α β γ: Type) (u: β → γ) (v: α → β) (x: α) => u (v x)) Nat String Bool j h 0
#eval (fun x : Nat => x) 1     -- 1
#eval (fun _ : Nat => true) 1  -- true

def double (x : Nat) : Nat := x + x
#eval double 3    -- 6
def double2 : Nat → Nat := fun x => x + x
#eval double2 3    -- 6
def double3 := fun (x : Nat) => x + x

def add (x y : Nat) := x + y
#eval add 3 2               -- 5
def add2 (x : Nat) (y : Nat) := x + y
#eval add2 (double 3) (7 + 9)  -- 22

def greater (x y : Nat) := if x > y then x else y

def doTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
#eval doTwice double 2   -- 8

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def square (x : Nat) : Nat := x * x
#eval compose Nat Nat Nat double square 3  -- 18

#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16
def twice_double (x : Nat) : Nat := let y := x + x; y * y
#eval twice_double 2   -- 16

#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64

def t (x : Nat) : Nat :=
  let y := x + x
  y * y

def foo := let a := Nat; fun x : a => x + 2
-- def bar := (fun a => fun x : a => x + 2) Nat -- ERROR
-- the type of x is not known to be Nat, so + is not defined.
-- because it has to work no matter what type a is (Nat, String, List etc.)

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)
  def compose3 := g (f x)
  def doTwice3 := h (h x)
  def doThrice3 := h (h (h x))
  #print compose3
  #print doTwice3
  #print doThrice3
end useful

#check List.nil
#check List.cons
#check List.map

open List

#check nil
#check cons
#check map

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7
  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)
    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
#check Bar.ffa

namespace Spam
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Spam -- closed here

#check Spam.a
#check Spam.f

namespace Spam -- can be opened again!
  def ffa : Nat := f (f a)
end Spam

namespace Dependent
  def cons (α : Type) (a : α) (as : List α) : List α := List.cons a as
  #check cons Nat        -- Nat → List Nat → List Nat
  #check cons Bool       -- Bool → List Bool → List Bool
  #check cons            -- (α : Type) → α → List α → List α
end Dependent

#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α

universe u v
def f1 (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a := ⟨a, b⟩
def g1 (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a := Sigma.mk a b

def h1 (x : Nat) : Nat := (f1 Type (fun α => α) Nat x).2
#eval h1 5 -- 5

def h2 (x : Nat) : Nat := (g1 Type (fun α => α) Nat x).2
#eval h2 5 -- 5

namespace Lst
  def Lst (α : Type u) : Type u := List α
  def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
  def Lst.nil (α : Type u) : Lst α := List.nil
  def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
  #check Lst          -- Lst.{u} (α : Type u) : Type u
  #check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
  #check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
  #check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α

  #check Lst.cons Nat 0 (Lst.nil Nat) -- Lst Nat
  def as : Lst Nat := Lst.nil Nat
  def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)
  #check Lst.append Nat as bs
end Lst

namespace Underscore
  def Lst (α : Type u) : Type u := List α
  def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
  def Lst.nil (α : Type u) : Lst α := List.nil
  def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
  #check Lst          -- Type u_1 → Type u_1
  #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
  #check Lst.nil      -- (α : Type u_1) → Lst α
  #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
  #check Lst.cons _ 0 (Lst.nil _)

  def as : Lst Nat := Lst.nil _
  def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

  #check Lst.append _ as bs
end Underscore

namespace Implicit
  def Lst (α : Type u) : Type u := List α
  def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
  def Lst.nil {α : Type u} : Lst α := List.nil
  def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

  #check Lst.cons 0 Lst.nil

  def as : Lst Nat := Lst.nil
  def bs : Lst Nat := Lst.cons 5 Lst.nil

  #check Lst.append as bs
end Implicit

namespace Ident
  def ident {α : Type u} (x : α) := x
  #check ident         -- ?m → ?m
  #check ident 1       -- Nat
  #check ident "hello" -- String
  #check @ident        -- {α : Type u_1} → α → α
end Ident

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
  #check ident
  #check ident 4
  #check ident "hello"
end

#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat

#check 2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int

#check @id        -- {α : Sort u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool
