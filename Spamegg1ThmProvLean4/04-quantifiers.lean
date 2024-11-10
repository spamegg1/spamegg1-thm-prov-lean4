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
