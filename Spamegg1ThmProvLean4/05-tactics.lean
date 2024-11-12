theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
#print test

theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
#print test2

theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left  => exact hp
  case right =>
    apply And.intro
    case left  => exact hq
    case right => exact hp

theorem test4 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left  => exact hq
    case right => exact hp
  case left => exact hp

theorem test5 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h.right
    . intro hq
      apply Or.inl
      apply And.intro
      . exact h.left
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact h.left
      . exact hr
  . intro g
    apply Or.elim g
    . intro hpq
      apply And.intro
      . exact hpq.left
      . apply Or.inl
        exact hpq.right
    . intro hpr
      apply And.intro
      . exact hpr.left
      . apply Or.inr
        exact hpr.right

example (α : Type) : α → α := by intro a; exact a
example (α : Type) : ∀ x : α, x = x := by intro x; exact Eq.refl x
