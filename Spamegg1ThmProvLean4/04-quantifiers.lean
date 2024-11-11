example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : (∀ x : α, p x ∧ q x) =>
  fun y : α =>
  show p y from (h y).left

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α => -- using z instead of y, because it's just dummy
  show p z from And.left (h z)

namespace Transitivity
  variable (α : Type) (r : α → α → Prop)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  variable (a b c : α)
  variable (hab : r a b) (hbc : r b c)

  #check trans_r -- unknown variables whose types are not inferred yet
  #check trans_r hab -- still has 1 variable type not inferred
  #check trans_r hab hbc -- r a c : now every type is inferred
end Transitivity

namespace EquivalenceRelation

variable (α : Type) (r : α → α → Prop)
variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

#check Eq.refl    -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
#check Eq.symm    -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a
#check Eq.trans   -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c

universe u
#check @Eq.refl.{u}   -- @Eq.refl : ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- @Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- @Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

end EquivalenceRelation

namespace Example1
  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)
  example : a = d := Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
  example : a = d := (hab.trans hcb.symm).trans hcd
end Example1

namespace Reflexivity
  variable (α β : Type)
  example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
  example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
  example : 2 + 3 = 5 := Eq.refl _
  example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
  example (a : α) (b : β) : (a, b).1 = a := rfl
  example : 2 + 3 = 5 := rfl
end Reflexivity

example (α : Type)(a b : α)(p : α → Prop)(h1 : a = b)(h2 : p a) : p b := Eq.subst h1 h2
example (α : Type)(a b : α)(p : α → Prop)(h1 : a = b)(h2 : p a) : p b := h1 ▸ h2

namespace Auxiliary

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

end Auxiliary

namespace CommonIdentities

variable (a b c : Nat)
example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y := Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

end CommonIdentities

namespace CalcExample
-- this doesn't work! Have to manually supply these to theorems.
-- variable (a b c d e : Nat)
-- variable (h1 : a = b)
-- variable (h2 : b = c + 1)
-- variable (h3 : c = d)
-- variable (h4 : e = 1 + d)

theorem T
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

theorem T2
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

theorem T3
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

theorem T4
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]

theorem T5
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]

end CalcExample

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

namespace TeachTransitivity

def divides (x y : Nat) : Prop := ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) := ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

-- infix:50 " ∣ " => divides -- this doesn't work!

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    -- x ∣ y   := h₁ -- this doesn't work!
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..
    -- _ | 2*z := divides_mul .. -- this doesn't work!
end TeachTransitivity

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

-- Existential quantifier
example : ∃ x : Nat, x > 0 := have h : 1 > 0 := Nat.zero_lt_succ 0; Exists.intro 1 h
example (x : Nat) (h : x > 0) : ∃ y, y < x := Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro -- ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p

example : ∃ x : Nat, x > 0 := have h : 1 > 0 := Nat.zero_lt_succ 0; ⟨1, h⟩
example (x : Nat) (h : x > 0) : ∃ y, y < x := ⟨0, h⟩
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z := ⟨y, hxy, hyz⟩

-- variable (g : Nat → Nat → Nat) -- these don't work!
-- variable (hg : g 0 0 = 0)

theorem gex1 (g : Nat → Nat → Nat) (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (g : Nat → Nat → Nat) (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (g : Nat → Nat → Nat) (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (g : Nat → Nat → Nat) (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

namespace ExistElim

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with -- here, w is the "witness" and hw is the prop that it satisfies.
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with -- with type annotations
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with -- destructured even further
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h -- another way to destructure
  ⟨w, hqw, hpw⟩

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩ -- implicit use of match

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even1 (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
end ExistElim

namespace ClassicalExists

open Classical
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)

-- These two hard exercises come with solutions provided:
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
end ClassicalExists

namespace MoreProofLang

variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1) -- here, this = h 0
  show f 0 ≤ f 3 from Nat.le_trans this (h 2) -- here, this = prev line's expression

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1) -- similar to this
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

-- notation "‹" p "›" => show p by assumption -- fill in the proof

-- we can refer to nameless assumptions with ‹ ›
example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

example (n : Nat) : Nat := ‹Nat›
end MoreProofLang

-- EXERCISES: some require classical reasoning!
namespace Exercises
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  have forward := fun h : ∀ x, p x ∧ q x =>
    have hp := fun x => (h x).left
    have hq := fun x => (h x).right
    And.intro hp hq
  have backward := fun h : (∀ x, p x) ∧ (∀ x, q x) =>
    let ⟨hp, hq⟩ := h
    fun x => And.intro (hp x) (hq x)
  Iff.intro forward backward

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq => fun hp => fun x => (hpq x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := fun h =>
  have left  := fun hp : (∀ x, p x) => fun x => Or.inl (hp x)
  have right := fun hq : (∀ x, q x) => fun x => Or.inr (hq x)
  Or.elim h left right

example : α → ((∀ x : α, r) ↔ r) := fun a =>
  have forward  := fun h : (∀ x : α, r) => h a
  have backward := fun h : r => fun x => h
  Iff.intro forward backward

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := -- needs classical
  have forward := fun h : ∀ x, p x ∨ r =>
    have notr : ¬r -> (∀ x, p x) ∨ r := fun nr =>
      have all_px : ∀ x, p x := fun x =>
        Or.elim (h x) id (fun hr : r => absurd hr nr)
      Or.inl all_px
    Or.elim (em r) Or.inr notr
  have backward := fun h : (∀ x, p x) ∨ r =>
    have left  := fun hp : ∀ x, p x => fun x => Or.inl (hp x)
    have right := fun hr : r => fun x => Or.inr hr
    Or.elim h left right
  Iff.intro forward backward

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  have forward := fun h : ∀ x, r → p x => sorry
  have backward := fun h : r → ∀ x, p x => sorry
  Iff.intro forward backward

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry

def even (n : Nat) : Prop := sorry
def prime (n : Nat) : Prop := sorry
def infinitely_many_primes : Prop := sorry
def Fermat_prime (n : Nat) : Prop := sorry
def infinitely_many_Fermat_primes : Prop := sorry
def goldbach_conjecture : Prop := sorry
def Goldbach's_weak_conjecture : Prop := sorry
def Fermat's_last_theorem : Prop := sorry
example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry
example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry

end Exercises
