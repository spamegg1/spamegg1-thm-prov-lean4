def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop

structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof : Prop → Type

axiom And_comm (p q : Prop) : Proof (Implies (And p q) (And q p))
variable (p q : Prop)
#check And_comm p q     -- Proof (Implies (And p q) (And q p))

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun _ : q => show p from hp -- just hp also works
#print t1

theorem t2 (hp : p) (_ : q) : p := hp
#print t2    -- p → q → p

theorem t3 (hp : p) (_ : q) : p := hp
axiom hp : p
theorem t4 : q → p := t1 hp

axiom unsound : False -- Everything follows from false
theorem ex : 1 = 0 := False.elim unsound

theorem t5 {p q : Prop} (hp : p) (_ : q) : p := hp
#print t5

theorem t6 : ∀ {p q : Prop}, p → q → p := fun {p q : Prop} (hp : p) (_ : q) => hp
