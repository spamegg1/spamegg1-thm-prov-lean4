theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro -- apply is function application
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
  . intro h -- intro is like fun x => e
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

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁ -- here, the second argument is the goal, x = w
  apply Eq.trans h₂ -- goal was transformed into y = w, so that's the 2nd arg now.
  assumption   -- applied h₃

-- assumption unifies meta variables
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans  -- notice we haven't provided ANY arguments to it.
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

-- rely on Lean's auto generated variable names
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

example (y : Nat) : (fun x : Nat => 0) y = 0 := by rfl

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

example (x : Nat) : x = x := by
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- goal is x y : Nat ⊢ x = y → y = x
  intro h₁
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption

-- reverting x brings h along with it, since h depends on x
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- goal is y : Nat ⊢ ∀ (x : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x y -- you can revert multiple at once
  -- goal is ⊢ ∀ (x y : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption

-- revert only works on local context / variables.
-- generalize can be used on the goal itself.
example : 3 = 3 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ x = x
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl

-- generalization does not always work, can give unprovable (false) statement
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ 2 + x = 5
  admit -- this is like sorry

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x

def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption

open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this

example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }

example (p q : Prop) (hp : p) : p ∨ q := by apply Or.inl; assumption
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by constructor <;> assumption

example (p q : Prop) (hp : p) : p ∨ q := by -- 1st one Or.inl succeeds
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by -- 2nd one Or.inr succeeds
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0

example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (_ : p y) (hq : q) : p x := by
  rw [h hq]; assumption

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]

example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t

example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption

open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]

example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption

attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption

example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption

def f (m n : Nat) : Nat := m + n + m
example {m n : Nat} (h : n = 1) (g : 0 = m) : (f m n) = n := by simp [h, ←g, f]

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

example (p q : Prop) (hp : p) : p ∧ q ↔ q := by simp [*]
example (p q : Prop) (hp : p) : p ∨ q := by simp [*]
example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by simp [*]

example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]

def mk_symm (xs : List α) := xs ++ xs.reverse

-- @[simp]
theorem reverse_mk_symm (xs : List α) : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section
attribute [simp] reverse_mk_symm -- or add @[simp] before theorem

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption -- don't simp the theorem

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption -- don't simp the theorem
end -- attribute is trapped above in the section

example : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true })

example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp (config := { contextual := true })

example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by simp_arith

def f1 (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f1 x y w = 1 := by
  intros
  simp [f1]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f1 x y w = 1 := by
  intros; simp [f1]; split <;> first | contradiction | rfl

def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, c] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp_arith at h

-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by triv
example (x : α) (h : p) : x = x ∧ p := by apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by triv

-- EXERCISES
-- Use tactic combinators to obtain a one line proof of the following:
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by simp [*]
  -- constructor
  -- . apply Or.inl
  --   assumption
  -- . constructor
  --   . apply Or.inr
  --     apply Or.inl
  --     assumption
  --   . apply Or.inr
  --     apply Or.inr
  --     assumption

-- Go back to the exercises in Chapter Propositions and Proofs and
-- Chapter Quantifiers and Equality and redo as many as you can now
-- with tactic proofs, using also rw and simp as appropriate.

-- 3. Propositions and Proofs exercises
-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro <;> (intro h; constructor; exact h.right; exact h.left)

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro <;> intro h <;> cases h <;> simp [*]
  -- first | apply Or.inl; assumption | apply Or.inr; assumption

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro <;> intro <;> simp [*]

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro forward
    cases forward
    . case inl hpq =>
      cases hpq
      . case inl hp => simp [*] -- apply Or.inl; assumption
      . case inr hq => simp [*] -- apply Or.inr; apply Or.inl; assumption
    . case inr hr => simp [*] -- (repeat apply Or.inr); assumption
  . intro backward
    cases backward
    . case inl hp  => simp [*] -- (repeat apply Or.inl); assumption
    . case inr hqr =>
      cases hqr
      . case inl hq => simp [*] -- apply Or.inl; apply Or.inr; assumption
      . case inr hr => simp [*] -- apply Or.inr; assumption

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h -- intro is like fun x => e
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

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    apply And.intro <;>
    . apply Or.elim h <;>
      . intro hp; simp [*] -- apply Or.inl; exact hp
      -- . intro hqr; simp [*] -- apply Or.inr; exact hqr.left
    -- . apply Or.elim h
    --   . intro hp;  simp[*] -- apply Or.inl; exact hp
    --   . intro hqr; simp[*] -- apply Or.inr; exact hqr.right
  . intro g
    apply Or.elim g.left
    . intro hp; simp [*] -- apply Or.inl; exact hp
    . intro hq
      apply Or.elim g.right <;>
      . intro hp; simp [*] -- apply Or.inl; exact hp
      -- . intro hr; simp [*] -- apply Or.inr; exact And.intro hq hr

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro <;> (intros; simp [*])
  -- . intro h; intro hpq; exact (h hpq.left) hpq.right
  -- . intro h; intro hp; intro hq; exact h (And.intro hp hq)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    apply And.intro <;> (intro; simp [*])
    -- . intro hp; exact h (Or.inl hp)
    -- . intro hq; exact h (Or.inr hq)
  . intro h
    intro hpq
    apply Or.elim hpq <;> (intro; simp [*])
    -- . intro hp; exact h.left hp
    -- . intro hq; exact h.right hq

-- de Morgan laws
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro hp; exact h (Or.inl hp)
    . intro hq; exact h (Or.inr hq)
  . intro h
    intro hpq
    apply Or.elim hpq
    . intro hp; exact h.left hp
    . intro hq; exact h.right hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h
  apply Or.elim h <;> (intros; simp [*])
  -- . intro hnp
  --   intro hpq
  --   exact hnp hpq.left
  -- . intro hnq
  --   intro hpq
  --   exact hnq hpq.right

example : ¬(p ∧ ¬p) := by simp
  -- intro hpnp
  -- exact absurd hpnp.left hpnp.right

example : p ∧ ¬q → ¬(p → q) := by simp
  -- intro hpnq
  -- intro hpq
  -- exact absurd (hpq hpnq.left) hpnq.right

example : ¬p → (p → q) := by
  intro hnp
  intro hp
  exact absurd hp hnp

example : (¬p ∨ q) → (p → q) := by
  intro h
  intro
  apply Or.elim h <;> simp [*]
  -- . intro hnp
  --   exact absurd hp hnp
  -- . intro q
  --   exact q

example : p ∨ False ↔ p := by simp [*]
  -- apply Iff.intro
  -- . intro h
  --   apply Or.elim h
  --   . intro hp; assumption
  --   . intro fl; trivial
  -- . exact Or.inl

example : p ∧ False ↔ False := by simp [*]
  -- apply Iff.intro
  -- . exact And.right
  -- . intro f; apply And.intro;
  --   . trivial
  --   . trivial

example : (p → q) → (¬q → ¬p) := by
  intro h
  intro hnq
  intro hp
  exact absurd hp (absurd (h hp) hnq)

-- these require classical reasoning
open Classical
variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  apply Or.elim (em p)
  . intro hp
    apply Or.elim (h hp)
    . intro hq; apply Or.inl (fun _ : p => hq)
    . intro hr; apply Or.inr (fun _ : p => hr)
  . intro hnp
    apply Or.inl (fun hp' : p => absurd hp' hnp)

-- de Morgan
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  apply Or.elim (em p)
  . intro hp
    apply Or.elim (em q)
    . intro hq; apply absurd (And.intro hp hq) h
    . intro hnq; apply Or.inr hnq
  . intro hnp; apply Or.inl hnp

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  apply Or.elim (em p)
  . intro hp
    apply Or.elim (em q)
    . intro hq; exact absurd (fun _ : p => hq) h
    . intro hnq; exact And.intro hp hnq
  . intro hnp
    exact absurd (fun hp : p => absurd hp hnp) h

example : (p → q) → (¬p ∨ q) := by
  intro h
  apply Or.elim (em p)
  . intro hp; apply Or.inr (h hp)
  . intro hnp; apply Or.inl hnp

example : (¬q → ¬p) → (p → q) := by
  intro h
  intro hp
  apply Or.elim (em q)
  . simp -- intro hq; exact hq
  . intro hnq; exact absurd hp (h hnq)

example : p ∨ ¬p := by
  apply Or.elim (em p)
  . apply Or.inl
  . apply Or.inr

example : (((p → q) → p) → p) := by
  intro h
  apply Or.elim (em p)
  . simp -- intro hp; assumption
  . intro hnp
    exact absurd (h (fun hp : p => absurd hp hnp)) hnp

-- Prove ¬(p ↔ ¬p) without using classical logic.
example : ¬(p ↔ ¬p) := by
  intro h
  let notp : ¬p := (fun hp : p => absurd hp (h.mp hp))
  exact absurd (h.mpr notp) notp

-- 4. Quantifiers and Equality exercises
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro x; exact (h x).left
    . intro x; exact (h x).right
  . intro ⟨hp, hq⟩
    intro x
    exact And.intro (hp x) (hq x)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h
  intro hp
  intro x
  exact (h x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h
  apply Or.elim h
  . intro hp
    intro x
    exact Or.inl (hp x)
  . intro hq
    intro x
    exact Or.inr (hq x)

example : α → ((∀ x : α, r) ↔ r) := by
  intro h
  apply Iff.intro
  . intro hxr; exact hxr h
  . intro hr; intro x; exact hr

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by -- needs classical
  apply Iff.intro
  . intro h
    apply Or.elim (em r)
    . apply Or.inr
    . intro nr
      apply Or.inl
      intro x
      exact Or.elim (h x) id (fun hr : r => absurd hr nr)
  . intro h
    apply Or.elim h
    . intro hp
      intro x
      exact Or.inl (hp x)
    . intro hr
      intro x
      exact Or.inr hr

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h
    intro hr
    intro x
    exact (h x) hr
  . intro h
    intro x
    intro hr
    exact (h hr) x

section BarberParadox
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)
  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
    let not_self : ¬(shaves barber barber) :=
      fun hsbb : shaves barber barber => absurd hsbb ((h barber).mp hsbb)
    let self : shaves barber barber := (h barber).mpr not_self
    exact absurd self not_self
end BarberParadox

example : (∃ x : α, r) → r := by intro ⟨_, hw⟩; exact hw
example (a : α) : r → (∃ x : α, r) := by intro h; exact ⟨a, h⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro ⟨witness, hpxr⟩
    exact ⟨⟨witness, hpxr.left⟩, hpxr.right⟩
  . intro ⟨⟨witness, hpx⟩, hr⟩
    exact ⟨witness, ⟨hpx, hr⟩⟩

-- backward direction requires classical (LEM)
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    intro ⟨falsewitness, hnpx⟩
    exact absurd (h falsewitness) hnpx
  . intro h
    intro x
    apply Or.elim (em (p x))
    . exact id
    . intro npx
      exact absurd ⟨x, npx⟩ h

-- backward direction requires classical (LEM)
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro ⟨witness, hp⟩
    intro hnp
    exact absurd hp (hnp witness)
  . intro h
    apply Or.elim (em (∃ x, p x))
    . simp
    . intro hnp
      have nh : ∀ x, ¬ p x := fun x =>
        fun px: p x => absurd ⟨x, px⟩ hnp
      exact absurd nh h

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    intro x
    intro hpx
    exact absurd ⟨x, hpx⟩ h
  . intro h
    intro ⟨witness, hp⟩
    exact absurd hp (h witness)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    apply Or.elim (em (∃ x, ¬ p x))
    . simp
    . intro hnenpx
      have nh : ∀ x, p x := fun x => byContradiction
        fun npx : ¬ p x => absurd ⟨x, npx⟩ hnenpx
      exact absurd nh h
  . intro ⟨witness, hnp⟩
    intro hp
    exact absurd (hp witness) hnp

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  . intro h
    intro ⟨witness, hpx⟩
    exact (h witness) hpx
  . intro h
    intro x
    intro hpx
    exact h ⟨x, hpx⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  . intro ⟨witness, hrpx⟩
    intro hr
    exact ⟨witness, hrpx hr⟩
  . intro h
    apply Or.elim (em r)
    . intro hr
      let ⟨witness, hpx⟩ := h hr
      exact ⟨witness, fun _ : r => hpx⟩
    . intro nr
      exact ⟨a, fun hr : r => absurd hr nr⟩

-- hard one! copy-pasted and edited given solution
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro ⟨witness, hpq⟩
    apply Or.elim hpq
    . intro hp
      apply Or.inl
      exact ⟨witness, hp⟩
    . intro hq
      apply Or.inr
      exact ⟨witness, hq⟩
  . intro h
    apply Or.elim h
    . intro ⟨witness, hp⟩
      exact ⟨witness, Or.inl hp⟩
    . intro ⟨witness, hq⟩
      exact ⟨witness, Or.inr hq⟩

-- hard one! copy-pasted and edited from given
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro ⟨witness, hpr⟩
    intro hp
    exact hpr (hp witness)
  . intro hpr
    apply Or.elim (em (∀ x, p x))
    . intro hap
      exact ⟨a, fun _ => hpr hap⟩
    . intro nap
      apply Or.elim (em (∃ x, p x → r))
      . simp
      . intro nepr
        have hap : ∀ x, p x := fun x =>
          have npx := fun npx : ¬ p x =>
            have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp npx)⟩
            absurd hex nepr
          Or.elim (em (p x)) id npx
        exact absurd hap nap
