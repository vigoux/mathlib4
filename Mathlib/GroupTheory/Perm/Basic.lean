/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupPower.IterateHom
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.Common

/-!
# The group of permutations (self-equivalences) of a type `α`

This file defines the `Group` structure on `Equiv.Perm α`.
-/


universe u v

namespace Equiv

variable {α : Type u} {β : Type v}

namespace Perm

instance instOne : One (Perm α) where one := Equiv.refl _
instance instMul : Mul (Perm α) where mul f g := Equiv.trans g f
instance instInv : Inv (Perm α) where inv := Equiv.symm
instance instPowNat : Pow (Perm α) ℕ where
  pow f n := ⟨f^[n], f.symm^[n], f.left_inv.iterate _, f.right_inv.iterate _⟩

instance permGroup : Group (Perm α) where
  mul_assoc f g h := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_left_inv := self_trans_symm
  npow n f := f ^ n
  npow_succ n f := coe_fn_injective $ Function.iterate_succ _ _
  zpow := zpowRec fun n f ↦ f ^ n
  zpow_succ' n f := coe_fn_injective $ Function.iterate_succ _ _

@[simp]
theorem default_eq : (default : Perm α) = 1 :=
  rfl

/-- The permutation of a type is equivalent to the units group of the endomorphisms monoid of this
type. -/
@[simps]
def equivUnitsEnd : Perm α ≃* Units (Function.End α) where
  -- Porting note: needed to add `.toFun`.
  toFun e := ⟨e.toFun, e.symm.toFun, e.self_comp_symm, e.symm_comp_self⟩
  invFun u :=
    ⟨(u : Function.End α), (↑u⁻¹ : Function.End α), congr_fun u.inv_val, congr_fun u.val_inv⟩
  left_inv _ := ext fun _ => rfl
  right_inv _ := Units.ext rfl
  map_mul' _ _ := rfl

/-- Lift a monoid homomorphism `f : G →* Function.End α` to a monoid homomorphism
`f : G →* Equiv.Perm α`. -/
@[simps!]
def _root_.MonoidHom.toHomPerm {G : Type*} [Group G] (f : G →* Function.End α) : G →* Perm α :=
  equivUnitsEnd.symm.toMonoidHom.comp f.toHomUnits

theorem mul_apply (f g : Perm α) (x) : (f * g) x = f (g x) :=
  Equiv.trans_apply _ _ _

theorem one_apply (x) : (1 : Perm α) x = x :=
  rfl

@[simp]
theorem inv_apply_self (f : Perm α) (x) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

@[simp]
theorem apply_inv_self (f : Perm α) (x) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem one_def : (1 : Perm α) = Equiv.refl α :=
  rfl

theorem mul_def (f g : Perm α) : f * g = g.trans f :=
  rfl

theorem inv_def (f : Perm α) : f⁻¹ = f.symm :=
  rfl

@[simp, norm_cast] lemma coe_one : ⇑(1 : Perm α) = id := rfl

@[simp, norm_cast] lemma coe_mul (f g : Perm α) : ⇑(f * g) = f ∘ g := rfl

@[norm_cast] lemma coe_pow (f : Perm α) (n : ℕ) : ⇑(f ^ n) = f^[n] := rfl

@[simp] lemma iterate_eq_pow (f : Perm α) (n : ℕ) : f^[n] = ⇑(f ^ n) := rfl

theorem eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
  f.eq_symm_apply

theorem inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y :=
  f.symm_apply_eq

theorem zpow_apply_comm {α : Type*} (σ : Perm α) (m n : ℤ) {x : α} :
    (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, zpow_mul_comm]

@[simp] lemma image_inv (f : Perm α) (s : Set α) : ↑f⁻¹ '' s = f ⁻¹' s := f⁻¹.image_eq_preimage _

@[simp] lemma preimage_inv (f : Perm α) (s : Set α) : ↑f⁻¹ ⁻¹' s = f '' s :=
  (f.image_eq_preimage _).symm

/-! Lemmas about mixing `Perm` with `Equiv`. Because we have multiple ways to express
`Equiv.refl`, `Equiv.symm`, and `Equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/


@[simp]
theorem trans_one {α : Sort*} {β : Type*} (e : α ≃ β) : e.trans (1 : Perm β) = e :=
  Equiv.trans_refl e

@[simp]
theorem mul_refl (e : Perm α) : e * Equiv.refl α = e :=
  Equiv.trans_refl e

@[simp]
theorem one_symm : (1 : Perm α).symm = 1 :=
  Equiv.refl_symm

@[simp]
theorem refl_inv : (Equiv.refl α : Perm α)⁻¹ = 1 :=
  Equiv.refl_symm

@[simp]
theorem one_trans {α : Type*} {β : Sort*} (e : α ≃ β) : (1 : Perm α).trans e = e :=
  Equiv.refl_trans e

@[simp]
theorem refl_mul (e : Perm α) : Equiv.refl α * e = e :=
  Equiv.refl_trans e

@[simp]
theorem inv_trans_self (e : Perm α) : e⁻¹.trans e = 1 :=
  Equiv.symm_trans_self e

@[simp]
theorem mul_symm (e : Perm α) : e * e.symm = 1 :=
  Equiv.symm_trans_self e

@[simp]
theorem self_trans_inv (e : Perm α) : e.trans e⁻¹ = 1 :=
  Equiv.self_trans_symm e

@[simp]
theorem symm_mul (e : Perm α) : e.symm * e = 1 :=
  Equiv.self_trans_symm e

/-! Lemmas about `Equiv.Perm.sumCongr` re-expressed via the group structure. -/


@[simp]
theorem sumCongr_mul {α β : Type*} (e : Perm α) (f : Perm β) (g : Perm α) (h : Perm β) :
    sumCongr e f * sumCongr g h = sumCongr (e * g) (f * h) :=
  sumCongr_trans g h e f

@[simp]
theorem sumCongr_inv {α β : Type*} (e : Perm α) (f : Perm β) :
    (sumCongr e f)⁻¹ = sumCongr e⁻¹ f⁻¹ :=
  sumCongr_symm e f

@[simp]
theorem sumCongr_one {α β : Type*} : sumCongr (1 : Perm α) (1 : Perm β) = 1 :=
  sumCongr_refl

/-- `Equiv.Perm.sumCongr` as a `MonoidHom`, with its two arguments bundled into a single `Prod`.

This is particularly useful for its `MonoidHom.range` projection, which is the subgroup of
permutations which do not exchange elements between `α` and `β`. -/
@[simps]
def sumCongrHom (α β : Type*) : Perm α × Perm β →* Perm (α ⊕ β) where
  toFun a := sumCongr a.1 a.2
  map_one' := sumCongr_one
  map_mul' _ _ := (sumCongr_mul _ _ _ _).symm

theorem sumCongrHom_injective {α β : Type*} : Function.Injective (sumCongrHom α β) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk.inj_iff]
  constructor <;> ext i
  · simpa using Equiv.congr_fun h (Sum.inl i)
  · simpa using Equiv.congr_fun h (Sum.inr i)

@[simp]
theorem sumCongr_swap_one {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : α) :
    sumCongr (Equiv.swap i j) (1 : Perm β) = Equiv.swap (Sum.inl i) (Sum.inl j) :=
  sumCongr_swap_refl i j

@[simp]
theorem sumCongr_one_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : β) :
    sumCongr (1 : Perm α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) :=
  sumCongr_refl_swap i j

/-! Lemmas about `Equiv.Perm.sigmaCongrRight` re-expressed via the group structure. -/


@[simp]
theorem sigmaCongrRight_mul {α : Type*} {β : α → Type*} (F : ∀ a, Perm (β a))
    (G : ∀ a, Perm (β a)) : sigmaCongrRight F * sigmaCongrRight G = sigmaCongrRight (F * G) :=
  sigmaCongrRight_trans G F

@[simp]
theorem sigmaCongrRight_inv {α : Type*} {β : α → Type*} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F)⁻¹ = sigmaCongrRight fun a => (F a)⁻¹ :=
  sigmaCongrRight_symm F

@[simp]
theorem sigmaCongrRight_one {α : Type*} {β : α → Type*} :
    sigmaCongrRight (1 : ∀ a, Equiv.Perm <| β a) = 1 :=
  sigmaCongrRight_refl

/-- `Equiv.Perm.sigmaCongrRight` as a `MonoidHom`.

This is particularly useful for its `MonoidHom.range` projection, which is the subgroup of
permutations which do not exchange elements between fibers. -/
@[simps]
def sigmaCongrRightHom {α : Type*} (β : α → Type*) : (∀ a, Perm (β a)) →* Perm (Σa, β a) where
  toFun := sigmaCongrRight
  map_one' := sigmaCongrRight_one
  map_mul' _ _ := (sigmaCongrRight_mul _ _).symm

theorem sigmaCongrRightHom_injective {α : Type*} {β : α → Type*} :
    Function.Injective (sigmaCongrRightHom β) := by
  intro x y h
  ext a b
  simpa using Equiv.congr_fun h ⟨a, b⟩

/-- `Equiv.Perm.subtypeCongr` as a `MonoidHom`. -/
@[simps]
def subtypeCongrHom (p : α → Prop) [DecidablePred p] :
    Perm { a // p a } × Perm { a // ¬p a } →* Perm α where
  toFun pair := Perm.subtypeCongr pair.fst pair.snd
  map_one' := Perm.subtypeCongr.refl
  map_mul' _ _ := (Perm.subtypeCongr.trans _ _ _ _).symm

theorem subtypeCongrHom_injective (p : α → Prop) [DecidablePred p] :
    Function.Injective (subtypeCongrHom p) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk.inj_iff]
  constructor <;> ext i <;> simpa using Equiv.congr_fun h i

/-- If `e` is also a permutation, we can write `permCongr`
completely in terms of the group structure. -/
@[simp]
theorem permCongr_eq_mul (e p : Perm α) : e.permCongr p = e * p * e⁻¹ :=
  rfl

section ExtendDomain

/-! Lemmas about `Equiv.Perm.extendDomain` re-expressed via the group structure. -/


variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

@[simp]
theorem extendDomain_one : extendDomain 1 f = 1 :=
  extendDomain_refl f

@[simp]
theorem extendDomain_inv : (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f :=
  rfl

@[simp]
theorem extendDomain_mul (e e' : Perm α) :
    e.extendDomain f * e'.extendDomain f = (e * e').extendDomain f :=
  extendDomain_trans _ _ _

/-- `extendDomain` as a group homomorphism -/
@[simps]
def extendDomainHom : Perm α →* Perm β where
  toFun e := extendDomain e f
  map_one' := extendDomain_one f
  map_mul' e e' := (extendDomain_mul f e e').symm

theorem extendDomainHom_injective : Function.Injective (extendDomainHom f) :=
  (injective_iff_map_eq_one (extendDomainHom f)).mpr fun e he =>
    ext fun x => f.injective <|
      Subtype.ext ((extendDomain_apply_image e f x).symm.trans (Perm.ext_iff.mp he (f x)))

@[simp]
theorem extendDomain_eq_one_iff {e : Perm α} {f : α ≃ Subtype p} : e.extendDomain f = 1 ↔ e = 1 :=
  (injective_iff_map_eq_one' (extendDomainHom f)).mp (extendDomainHom_injective f) e

@[simp]
lemma extendDomain_pow (n : ℕ) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  map_pow (extendDomainHom f) _ _

@[simp]
lemma extendDomain_zpow (n : ℤ) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  map_zpow (extendDomainHom f) _ _

end ExtendDomain

section Subtype

variable {p : α → Prop} {f : Perm α}

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
def subtypePerm (f : Perm α) (h : ∀ x, p x ↔ p (f x)) : Perm { x // p x } where
  toFun := fun x => ⟨f x, (h _).1 x.2⟩
  invFun := fun x => ⟨f⁻¹ x, (h (f⁻¹ x)).2 <| by simpa using x.2⟩
  left_inv _ := by simp only [Perm.inv_apply_self, Subtype.coe_eta, Subtype.coe_mk]
  right_inv _ := by simp only [Perm.apply_inv_self, Subtype.coe_eta, Subtype.coe_mk]

@[simp]
theorem subtypePerm_apply (f : Perm α) (h : ∀ x, p x ↔ p (f x)) (x : { x // p x }) :
    subtypePerm f h x = ⟨f x, (h _).1 x.2⟩ :=
  rfl

@[simp]
theorem subtypePerm_one (p : α → Prop) (h := fun _ => Iff.rfl) : @subtypePerm α p 1 h = 1 :=
  rfl

@[simp]
theorem subtypePerm_mul (f g : Perm α) (hf hg) :
    (f.subtypePerm hf * g.subtypePerm hg : Perm { x // p x }) =
      (f * g).subtypePerm fun _ => (hg _).trans <| hf _ :=
  rfl

private theorem inv_aux : (∀ x, p x ↔ p (f x)) ↔ ∀ x, p x ↔ p (f⁻¹ x) :=
  f⁻¹.surjective.forall.trans <| by simp_rw [f.apply_inv_self, Iff.comm]

/-- See `Equiv.Perm.inv_subtypePerm`-/
theorem subtypePerm_inv (f : Perm α) (hf) :
    f⁻¹.subtypePerm hf = (f.subtypePerm <| inv_aux.2 hf : Perm { x // p x })⁻¹ :=
  rfl

/-- See `Equiv.Perm.subtypePerm_inv`-/
@[simp]
theorem inv_subtypePerm (f : Perm α) (hf) :
    (f.subtypePerm hf : Perm { x // p x })⁻¹ = f⁻¹.subtypePerm (inv_aux.1 hf) :=
  rfl

private theorem pow_aux (hf : ∀ x, p x ↔ p (f x)) : ∀ {n : ℕ} (x), p x ↔ p ((f ^ n) x)
  | 0, _ => Iff.rfl
  | _ + 1, _ => (hf _).trans (pow_aux hf _)

@[simp]
theorem subtypePerm_pow (f : Perm α) (n : ℕ) (hf) :
    (f.subtypePerm hf : Perm { x // p x }) ^ n = (f ^ n).subtypePerm (pow_aux hf) := by
  induction' n with n ih
  · simp
  · simp_rw [pow_succ', ih, subtypePerm_mul]

private theorem zpow_aux (hf : ∀ x, p x ↔ p (f x)) : ∀ {n : ℤ} (x), p x ↔ p ((f ^ n) x)
  | Int.ofNat n => pow_aux hf
  | Int.negSucc n => by
    rw [zpow_negSucc]
    exact inv_aux.1 (pow_aux hf)

@[simp]
theorem subtypePerm_zpow (f : Perm α) (n : ℤ) (hf) :
    (f.subtypePerm hf ^ n : Perm { x // p x }) = (f ^ n).subtypePerm (zpow_aux hf) := by
  induction' n with n ih
  · exact subtypePerm_pow _ _ _
  · simp only [zpow_negSucc, subtypePerm_pow, subtypePerm_inv]

variable [DecidablePred p] {a : α}

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def ofSubtype : Perm (Subtype p) →* Perm α where
  toFun f := extendDomain f (Equiv.refl (Subtype p))
  map_one' := Equiv.Perm.extendDomain_one _
  map_mul' f g := (Equiv.Perm.extendDomain_mul _ f g).symm

theorem ofSubtype_subtypePerm {f : Perm α} (h₁ : ∀ x, p x ↔ p (f x)) (h₂ : ∀ x, f x ≠ x → p x) :
    ofSubtype (subtypePerm f h₁) = f :=
  Equiv.ext fun x => by
    by_cases hx : p x
    · exact (subtypePerm f h₁).extendDomain_apply_subtype _ hx
    · rw [ofSubtype, MonoidHom.coe_mk]
      -- Porting note: added `dsimp`
      dsimp only [OneHom.coe_mk]
      rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hx]
      exact not_not.mp fun h => hx (h₂ x (Ne.symm h))

theorem ofSubtype_apply_of_mem (f : Perm (Subtype p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩ :=
  extendDomain_apply_subtype _ _ ha

@[simp]
theorem ofSubtype_apply_coe (f : Perm (Subtype p)) (x : Subtype p) : ofSubtype f x = f x :=
  Subtype.casesOn x fun _ => ofSubtype_apply_of_mem f

theorem ofSubtype_apply_of_not_mem (f : Perm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a :=
  extendDomain_apply_not_subtype _ _ ha

theorem mem_iff_ofSubtype_apply_mem (f : Perm (Subtype p)) (x : α) :
    p x ↔ p ((ofSubtype f : α → α) x) :=
  if h : p x then by
    simpa only [h, true_iff_iff, MonoidHom.coe_mk, ofSubtype_apply_of_mem f h] using (f ⟨x, h⟩).2
  else by simp [h, ofSubtype_apply_of_not_mem f h]

@[simp]
theorem subtypePerm_ofSubtype (f : Perm (Subtype p)) :
    subtypePerm (ofSubtype f) (mem_iff_ofSubtype_apply_mem f) = f :=
  Equiv.ext fun x => Subtype.coe_injective (ofSubtype_apply_coe f x)

/-- Permutations on a subtype are equivalent to permutations on the original type that fix pointwise
the rest. -/
@[simps]
protected def subtypeEquivSubtypePerm (p : α → Prop) [DecidablePred p] :
    Perm (Subtype p) ≃ { f : Perm α // ∀ a, ¬p a → f a = a } where
  toFun f := ⟨ofSubtype f, fun _ => f.ofSubtype_apply_of_not_mem⟩
  invFun f :=
    (f : Perm α).subtypePerm fun a =>
      ⟨Decidable.not_imp_not.1 fun hfa => f.val.injective (f.prop _ hfa) ▸ hfa,
        Decidable.not_imp_not.1 fun ha hfa => ha <| f.prop a ha ▸ hfa⟩
  left_inv := Equiv.Perm.subtypePerm_ofSubtype
  right_inv f :=
    Subtype.ext ((Equiv.Perm.ofSubtype_subtypePerm _) fun a => Not.decidable_imp_symm <| f.prop a)

theorem subtypeEquivSubtypePerm_apply_of_mem (f : Perm (Subtype p)) (h : p a) :
    -- Porting note: was `Perm.subtypeEquivSubtypePerm p f a`
    ((Perm.subtypeEquivSubtypePerm p).toFun f).1 a = f ⟨a, h⟩ :=
  f.ofSubtype_apply_of_mem h

theorem subtypeEquivSubtypePerm_apply_of_not_mem (f : Perm (Subtype p)) (h : ¬p a) :
    -- Porting note: was `Perm.subtypeEquivSubtypePerm p f a`
    ((Perm.subtypeEquivSubtypePerm p).toFun f).1 a = a :=
  f.ofSubtype_apply_of_not_mem h

end Subtype

end Perm

section Swap

variable [DecidableEq α]

@[simp]
theorem swap_inv (x y : α) : (swap x y)⁻¹ = swap x y :=
  rfl

@[simp]
theorem swap_mul_self (i j : α) : swap i j * swap i j = 1 :=
  swap_swap i j

theorem swap_mul_eq_mul_swap (f : Perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
  Equiv.ext fun z => by
    simp only [Perm.mul_apply, swap_apply_def]
    split_ifs <;>
      simp_all only [Perm.apply_inv_self, Perm.eq_inv_iff_eq, eq_self_iff_true, not_true]

theorem mul_swap_eq_swap_mul (f : Perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f := by
  rw [swap_mul_eq_mul_swap, Perm.inv_apply_self, Perm.inv_apply_self]

theorem swap_apply_apply (f : Perm α) (x y : α) : swap (f x) (f y) = f * swap x y * f⁻¹ := by
  rw [mul_swap_eq_swap_mul, mul_inv_cancel_right]

@[simp]
theorem swap_smul_self_smul [MulAction (Perm α) β] (i j : α) (x : β) :
    swap i j • swap i j • x = x := by simp [smul_smul]

theorem swap_smul_involutive [MulAction (Perm α) β] (i j : α) :
    Function.Involutive (swap i j • · : β → β) := swap_smul_self_smul i j

/-- Left-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
theorem swap_mul_self_mul (i j : α) (σ : Perm α) : Equiv.swap i j * (Equiv.swap i j * σ) = σ :=
  swap_smul_self_smul i j σ

/-- Right-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
theorem mul_swap_mul_self (i j : α) (σ : Perm α) : σ * Equiv.swap i j * Equiv.swap i j = σ := by
  rw [mul_assoc, swap_mul_self, mul_one]

/-- A stronger version of `mul_right_injective` -/
@[simp]
theorem swap_mul_involutive (i j : α) : Function.Involutive (Equiv.swap i j * ·) :=
  swap_mul_self_mul i j

/-- A stronger version of `mul_left_injective` -/
@[simp]
theorem mul_swap_involutive (i j : α) : Function.Involutive (· * Equiv.swap i j) :=
  mul_swap_mul_self i j

@[simp]
theorem swap_eq_one_iff {i j : α} : swap i j = (1 : Perm α) ↔ i = j :=
  swap_eq_refl_iff

theorem swap_mul_eq_iff {i j : α} {σ : Perm α} : swap i j * σ = σ ↔ i = j := by
  rw [mul_left_eq_self, swap_eq_one_iff]

theorem mul_swap_eq_iff {i j : α} {σ : Perm α} : σ * swap i j = σ ↔ i = j := by
  rw [mul_right_eq_self, swap_eq_one_iff]

theorem swap_mul_swap_mul_swap {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) :
    swap y z * swap x y * swap y z = swap z x := by
  nth_rewrite 3 [← swap_inv]
  rw [← swap_apply_apply, swap_apply_left, swap_apply_of_ne_of_ne hxy hxz, swap_comm]

end Swap

section AddGroup
variable [AddGroup α] (a b : α)

@[simp] lemma addLeft_zero : Equiv.addLeft (0 : α) = 1 := ext zero_add

@[simp] lemma addRight_zero : Equiv.addRight (0 : α) = 1 := ext add_zero

@[simp] lemma addLeft_add : Equiv.addLeft (a + b) = Equiv.addLeft a * Equiv.addLeft b :=
  ext <| add_assoc _ _

@[simp] lemma addRight_add : Equiv.addRight (a + b) = Equiv.addRight b * Equiv.addRight a :=
  ext fun _ ↦ (add_assoc _ _ _).symm

@[simp] lemma inv_addLeft : (Equiv.addLeft a)⁻¹ = Equiv.addLeft (-a) := Equiv.coe_inj.1 rfl

@[simp] lemma inv_addRight : (Equiv.addRight a)⁻¹ = Equiv.addRight (-a) := Equiv.coe_inj.1 rfl

@[simp] lemma pow_addLeft (n : ℕ) : Equiv.addLeft a ^ n = Equiv.addLeft (n • a) := by
  ext; simp [Perm.coe_pow]

@[simp] lemma pow_addRight (n : ℕ) : Equiv.addRight a ^ n = Equiv.addRight (n • a) := by
  ext; simp [Perm.coe_pow]

@[simp] lemma zpow_addLeft (n : ℤ) : Equiv.addLeft a ^ n = Equiv.addLeft (n • a) :=
  (map_zsmul ({ toFun := Equiv.addLeft, map_zero' := addLeft_zero, map_add' := addLeft_add } :
    α →+ Additive (Perm α)) _ _).symm

@[simp] lemma zpow_addRight : ∀ (n : ℤ), Equiv.addRight a ^ n = Equiv.addRight (n • a)
  | Int.ofNat n => by simp
  | Int.negSucc n => by simp

end AddGroup

section Group
variable [Group α] (a b : α)

@[to_additive existing (attr := simp)]
lemma mulLeft_one : Equiv.mulLeft (1 : α) = 1 := ext one_mul

@[to_additive existing (attr := simp)]
lemma mulRight_one : Equiv.mulRight (1 : α) = 1 := ext mul_one

@[to_additive existing (attr := simp)]
lemma mulLeft_mul : Equiv.mulLeft (a * b) = Equiv.mulLeft a * Equiv.mulLeft b :=
  ext <| mul_assoc _ _

@[to_additive existing (attr := simp)]
lemma mulRight_mul : Equiv.mulRight (a * b) = Equiv.mulRight b * Equiv.mulRight a :=
  ext fun _ ↦ (mul_assoc _ _ _).symm

@[to_additive existing (attr := simp) inv_addLeft]
lemma inv_mulLeft : (Equiv.mulLeft a)⁻¹ = Equiv.mulLeft a⁻¹ := Equiv.coe_inj.1 rfl

@[to_additive existing (attr := simp) inv_addRight]
lemma inv_mulRight : (Equiv.mulRight a)⁻¹ = Equiv.mulRight a⁻¹ := Equiv.coe_inj.1 rfl

@[to_additive existing (attr := simp) pow_addLeft]
lemma pow_mulLeft (n : ℕ) : Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n) := by
  ext; simp [Perm.coe_pow]

@[to_additive existing (attr := simp) pow_addRight]
lemma pow_mulRight (n : ℕ) : Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n) := by
  ext; simp [Perm.coe_pow]

@[to_additive existing (attr := simp) zpow_addLeft]
lemma zpow_mulLeft (n : ℤ) : Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n) :=
  (map_zpow ({ toFun := Equiv.mulLeft, map_one' := mulLeft_one, map_mul' := mulLeft_mul } :
              α →* Perm α) _ _).symm

@[to_additive existing (attr := simp) zpow_addRight]
lemma zpow_mulRight : ∀ n : ℤ, Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n)
  | Int.ofNat n => by simp
  | Int.negSucc n => by simp

end Group
end Equiv

open Equiv Function

namespace Set
variable {α : Type*} {f : Perm α} {s : Set α}

lemma BijOn.perm_inv (hf : BijOn f s s) : BijOn ↑(f⁻¹) s s := hf.symm f.invOn

lemma MapsTo.perm_pow : MapsTo f s s → ∀ n : ℕ, MapsTo (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact MapsTo.iterate
lemma SurjOn.perm_pow : SurjOn f s s → ∀ n : ℕ, SurjOn (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact SurjOn.iterate
lemma BijOn.perm_pow : BijOn f s s → ∀ n : ℕ, BijOn (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact BijOn.iterate

lemma BijOn.perm_zpow (hf : BijOn f s s) : ∀ n : ℤ, BijOn (f ^ n) s s
  | Int.ofNat n => hf.perm_pow n
  | Int.negSucc n => (hf.perm_pow (n + 1)).perm_inv

end Set
