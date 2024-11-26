structure Pt (α : Type u) where
  mk :: (x : α) (y : α)

#check Pt       -- a Type
#check @Pt.rec  -- the eliminator
#check @Pt.mk   -- the constructor
#check @Pt.x    -- a projection
#check @Pt.y    -- a projection

structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point
example (a b : α) : x (mk a b) = a := rfl
example (a b : α) : y (mk a b) = b := rfl

def a := Point.mk 10 20
#check a.x  -- Nat
#eval a.x   -- 10
#eval a.y   -- 20

def Point.add (p q : Point Nat) := mk (p.x + q.x) (p.y + q.y)
def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4
#eval p.add q  -- {x := 4, y := 6}

def Point.smul (n : Nat) (p : Point Nat) := Point.mk (n * p.x) (n * p.y)
def r : Point Nat := Point.mk 1 2
#eval r.smul 3  -- {x := 3, y := 6}

#check @List.map
def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x
#eval xs.map f  -- [1, 4, 9]

#check { x := 10, y := 20 : Point Nat }  -- Point ℕ
#check { y := 20, x := 10 : Point _ }
#check ({ x := 10, y := 20 } : Point Nat)
example : Point Nat := { y := 20, x := 10 }

structure MyStruct where
  {α : Type u}
  {β : Type v}
  a : α
  b : β
#check { a := 10, b := true : MyStruct }

def p2 : Point Nat := { x := 1, y := 2 }
#eval { p2 with y := 3 }  -- { x := 1, y := 3 }
#eval { p2 with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q3 : Point3 Nat := { x := 5, y := 5, z := 5 }
def r3 : Point3 Nat := { p2, q3 with x := 6 }

example : r3.x = 6 := rfl
example : r3.y = 2 := rfl
example : r3.z = 5 := rfl

inductive Color where | red | green | blue
structure ColorPoint (α : Type u) extends Point α where c : Color

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p3 : Point3 Nat := { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p3 with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
