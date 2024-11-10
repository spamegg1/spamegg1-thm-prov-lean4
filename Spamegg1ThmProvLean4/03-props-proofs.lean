namespace OneWayToDefineProofs

def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r s : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop

structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof : Prop → Type

axiom And_comm (p q : Prop) : Proof (Implies (And p q) (And q p))
#check And_comm p q     -- Proof (Implies (And p q) (And q p))

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

end OneWayToDefineProofs

variable (p q r s : Prop)
variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun _ : q => show p from hp -- just hp also works
#print t1

theorem t12 (hp : p) (_ : q) : p := hp
#print t12    -- p → q → p

theorem t13 (hp : p) (_ : q) : p := hp
axiom hp : p
theorem t14 : q → p := t1 hp

axiom unsound : False -- Everything follows from false
theorem ex : 1 = 0 := False.elim unsound

theorem t15 {p q : Prop} (hp : p) (_ : q) : p := hp
#print t15

theorem t16 : ∀ {p q : Prop}, p → q → p := fun {p q : Prop} (hp : p) (_ : q) => hp
#check t16

theorem t17 : p → q → p := fun (hp : p) (_ : q) => hp

variable (hp : p) (hq : q)
theorem t18 : q → p := fun (_ : q) => hp
#print t18

theorem t19 (p q : Prop) (hp : p) (_ : q) : p := hp
#check t19 p q                -- p → q → p
#check t19 r s                -- r → s → r
#check t19 (r → s) (s → r)    -- (r → s) → (s → r) → r → s
variable (h : r → s)
#check t19 (r → s) (s → r) h  -- (s → r) → r → s

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p => show r from h₁ (h₂ h₃)

-- Prop Logic
#check p → q → p ∧ q
-- #eval p → q → p ∧ q -- error, no Decidable instance
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check fun (hp : p) (hq : q) => And.intro hp hq

example (h : p ∧ q) : p     := And.left h
example (h : p ∧ q) : q     := And.right h
example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

#check (⟨hp, hq⟩ : p ∧ q) -- avoid writing And.intro

variable (xs : List Nat)
#check List.length xs
#check xs.length -- syntactic sugar

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩ -- using dot notation
example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, ⟨h.left, h.right⟩⟩
example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, h.left, h.right⟩ -- sugar to avoid nesting

example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p => show q ∨ p from Or.intro_right q hp)
    (fun hq : q => show q ∨ p from Or.intro_left p hq)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq) -- same

example (h : p ∨ q) : q ∨ p := -- same
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p => show False from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
example (hp : p) (hnp : ¬p) : q := absurd hp hnp
example (hnp : ¬p) (hq : q) (hqp : q → p) : r := absurd (hqp hq) hnp

variable (p q : Prop)
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p => show p ∧ q from And.intro (And.right h) (And.left h))
#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

theorem and_swap2 : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩
example (h : p ∧ q) : q ∧ p := (and_swap2 p q).mp h

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp -- backwards reasoning
  show q from And.right h

open Classical
#check em p -- excluded middle: p or not p

theorem dne {p : Prop} (h : ¬¬p) : p := -- double negation elimination
  Or.elim (em p) (fun hp : p => hp) (fun hnp : ¬p => absurd hnp h)

example (h : ¬¬p) : p := byCases (fun h1 : p => h1) (fun h1 : ¬p => absurd h1 h)
example (h : ¬¬p) : p := byContradiction (fun h1 : ¬p => show False from h h1)
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p  => Or.inr (show ¬q from fun hq : q => h ⟨hp, hq⟩))
    (fun hp : ¬p => Or.inl hp)

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q) -- here is the classical usage
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)

-- EXERCISES
-- Prove the following identities, replacing the "sorry" placeholders with actual proofs.
-- commutativity of ∧ and ∨
theorem swap_and (h : x ∧ y) : y ∧ x := And.intro h.right h.left
example : p ∧ q ↔ q ∧ p := Iff.intro swap_and swap_and

theorem swap_or (h : x ∨ y) : y ∨ x := Or.elim h Or.inr Or.inl
example : p ∨ q ↔ q ∨ p := Iff.intro swap_or swap_or

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  have forward := fun h : (p ∧ q) ∧ r =>
    have pq : p ∧ q := h.left
    And.intro pq.left (And.intro pq.right h.right)
  have backward := fun h : p ∧ (q ∧ r) =>
    have qr : q ∧ r := h.right
    And.intro (And.intro h.left qr.left) qr.right
  Iff.intro forward backward

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  have forward := fun h : (p ∨ q) ∨ r =>
    have dpq := fun hpq => hpq.elim Or.inl (Or.inr ∘ Or.inl)
    have dr  := Or.inr ∘ Or.inr
    h.elim dpq dr
  have backward := fun h : p ∨ (q ∨ r) =>
    have dp  := Or.inl ∘ Or.inl
    have dqr := fun hqr => hqr.elim (Or.inl ∘ Or.inr) Or.inr
    h.elim dp dqr
  Iff.intro forward backward

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have forward := fun h : p ∧ (q ∨ r) =>
    have dq := fun hq => Or.inl (And.intro h.left hq)
    have dr := fun hr => Or.inr (And.intro h.left hr)
    h.right.elim dq dr
  have backward := fun h : (p ∧ q) ∨ (p ∧ r) =>
    have dpq := fun h1 => And.intro h1.left (Or.inl h1.right)
    have dpr := fun h2 => And.intro h2.left (Or.inr h2.right)
    h.elim dpq dpr
  Iff.intro forward backward

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  have forward := fun h : p ∨ (q ∧ r) =>
    have d1 := fun h1 => And.intro (Or.inl h1) (Or.inl h1)
    have d2 := fun h2 => And.intro (Or.inr h2.left) (Or.inr h2.right)
    h.elim d1 d2
  have backward := fun h : (p ∨ q) ∧ (p ∨ r) =>
    have if_q := fun hq : q =>
      have if_r := fun hr : r => Or.inr (And.intro hq hr)
      h.right.elim Or.inl if_r
    h.left.elim Or.inl if_q
  Iff.intro forward backward

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  have forward  := fun h => fun hpq => h hpq.left hpq.right
  have backward := fun h => fun hp  => (fun hq => h (And.intro hp hq))
  Iff.intro forward backward

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  have forward := fun h : ((p ∨ q) → r) =>
    have pr := fun hp => h (Or.inl hp)
    have qr := fun hr => h (Or.inr hr)
    And.intro pr qr
  have backward := fun h => fun hpq => Or.elim hpq h.left h.right
  Iff.intro forward backward

-- de Morgan laws
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  have forward := fun h : ¬(p ∨ q) =>
    have not_p := fun hp => absurd (Or.inl hp) h
    have not_q := fun hq => absurd (Or.inr hq) h
    And.intro not_p not_q
  have backward := fun h : ¬p ∧ ¬q => fun hpq =>
    have pc : p → ¬(p ∨ q) := fun hp => absurd hp h.left
    have qc : q → ¬(p ∨ q) := fun hq => absurd hq h.right
    absurd hpq (hpq.elim pc qc)
  Iff.intro forward backward

example : ¬p ∨ ¬q → ¬(p ∧ q) := fun hnpnq => fun hpq =>
  have c1 := fun not_p => absurd (hpq.left) not_p
  have c2 := fun not_q => absurd (hpq.right) not_q
  hnpnq.elim c1 c2

example : ¬(p ∧ ¬p) := fun h => absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) := fun h : p ∧ ¬q =>
  fun pq => absurd (pq h.left) h.right

example : ¬p → (p → q) := fun h: ¬p => fun hp : p => absurd hp h

example : (¬p ∨ q) → (p → q) := fun h : ¬p ∨ q =>
  have if_notp := fun notp => fun hp : p => absurd hp notp
  have if_q := fun hq => fun _ => hq
  h.elim if_notp if_q

example : p ∨ False ↔ p := Iff.intro (fun h => h.elim id False.elim) Or.inl
example : p ∧ False ↔ False := Iff.intro And.right False.elim

example : (p → q) → (¬q → ¬p) := fun hpq : p → q =>
  fun notq : ¬q => fun hp : p => absurd (hpq hp) notq

-- these require classical reasoning
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := fun h : p → q ∨ r =>
  have if_p := fun hp : p =>
    have if_q := fun hq => Or.inl (fun _ : p => hq)
    have if_r := fun hr => Or.inr (fun _ : p => hr)
    Or.elim (h hp) if_q if_r
  have if_notp := fun notp : ¬p => Or.inl (fun h : p => absurd h notp)
  Or.elim (em p) if_p if_notp

-- de Morgan
example : ¬(p ∧ q) → ¬p ∨ ¬q := fun h : ¬(p ∧ q) =>
  have if_p := fun hp : p =>
    have if_q := fun hq : q => absurd (And.intro hp hq) h
    Or.elim (em q) if_q Or.inr
  Or.elim (em p) if_p Or.inl

example : ¬(p → q) → p ∧ ¬q := fun h : ¬(p → q) =>
  have if_p := fun hp : p =>
    have if_q    := fun hq :  q => absurd (fun _ => hq) h
    have if_notq := fun nq : ¬q => And.intro hp nq
    Or.elim (em q) if_q if_notq
  have if_notp := fun np : ¬p => absurd (fun hp : p => absurd hp np) h
  Or.elim (em p) if_p if_notp

example : (p → q) → (¬p ∨ q) := fun h : p → q =>
  Or.elim (em p) (fun hp => Or.inr (h hp)) Or.inl

example : (¬q → ¬p) → (p → q) := fun h : ¬q → ¬p => fun hp : p =>
  have if_notq := fun nq : ¬q => absurd hp (h nq)
  Or.elim (em q) id if_notq

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := fun h : ((p → q) → p) =>
  have if_notp := fun np : ¬p => h (fun hp : p => absurd hp np)
  Or.elim (em p) id if_notp

-- Prove ¬(p ↔ ¬p) without using classical logic.
example : ¬(p ↔ ¬p) := fun h : p ↔ ¬p =>
  have not_p : ¬p := fun hp : p => absurd hp (h.mp hp)
  absurd (h.mpr not_p) not_p
