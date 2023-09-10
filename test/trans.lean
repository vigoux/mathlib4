import Mathlib.Tactic.Relation.Trans
import Std.Data.Nat.Lemmas

set_option autoImplicit true

attribute [trans] Setoid.trans

section EqOn

def Set (α : Type u) := α → Prop

protected def Set.Mem (a : α) (s : Set α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

-- Doesn't like that `s` comes last. Possible solutions:
-- 1. Reorder the arguments of `EqOn`.
-- 2. Make `trans` more flexible.
@[trans]
theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun _ hx =>
  (h₁ hx).trans (h₂ hx)

end EqOn

-- testing that the attribute is recognized and used
def nleq (a b : Nat) : Prop := a ≤ b

@[trans] def nleq_trans : nleq a b → nleq b c → nleq a c := Nat.le_trans

example (a b c : Nat) : nleq a b → nleq b c → nleq a c := by
  intro h₁ h₂
  trans b
  assumption
  assumption

example (a b c : Nat) : nleq a b → nleq b c → nleq a c := by intros; trans <;> assumption

-- using `Trans` typeclass
@[trans] def eq_trans {a b c : α} : a = b → b = c → a = c := by
  intro h₁ h₂
  apply Eq.trans h₁ h₂

example (a b c : Nat) : a = b → b = c → a = c := by intros; trans <;> assumption

example (a b c : Nat) : a = b → b = c → a = c := by
  intro h₁ h₂
  trans b
  assumption
  assumption

example : @Trans Nat Nat Nat (· ≤ ·) (· ≤ ·) (· ≤ ·) := inferInstance

example (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by
  intros h₁ h₂
  trans ?b
  case b => exact b
  exact h₁
  exact h₂

example (a b c : α) (R : α → α → Prop) [Trans R R R] : R a b → R b c → R a c := by
  intros h₁ h₂
  trans ?b
  case b => exact b
  exact h₁
  exact h₂

example (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by
  intros h₁ h₂
  trans
  exact h₁
  exact h₂

example (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by intros; trans <;> assumption

example (a b c : Nat) : a < b → b < c → a < c := by
  intro h₁ h₂
  trans b
  assumption
  assumption

example (a b c : Nat) : a < b → b < c → a < c := by intros; trans <;> assumption

example (x n p : Nat) (h₁ : n * Nat.succ p ≤ x) : n * p ≤ x := by
  trans
  · apply Nat.mul_le_mul_left; apply Nat.le_succ
  · apply h₁

example (a : α) (c : γ) : ∀ b : β, HEq a b → HEq b c → HEq a c := by
    intro b h₁ h₂
    trans b
    assumption
    assumption

def MyLE (n m : Nat) := ∃ k, n + k = m

@[trans] theorem MyLE.trans {n m k : Nat} (h1 : MyLE n m) (h2 : MyLE m k) : MyLE n k := by
  cases h1
  cases h2
  subst_vars
  exact ⟨_, Eq.symm <| Nat.add_assoc _ _ _⟩

example {n m k : Nat} (h1 : MyLE n m) (h2 : MyLE m k) : MyLE n k := by
  trans <;> assumption
