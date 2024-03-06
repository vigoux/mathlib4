/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Algebra.Spectrum

/-!
# Quasiregularity and quasispectrum

For a non-unital ring `R`, an element `r : R` is *quasiregular* if it is invertible in the monoid
`(R, ∘)` where `x ∘ y := y + x + x * y` with identity `0 : R`. We implement this both as a type
synonym `Quasiregular` which has an associated `Monoid` instance (note: *not* an `AddMonoid`
instance despite the fact that `0 : R` is the identity in this monoid) so that one may access
the quasiregular elements of `R` as `(Quasiregular R)ˣ`, but also as a predicate `IsQuasiregular`.

Quasiregularity is closely tied to invertibility. Indeed, `(Quasiregular A)ˣ` is isomorphic to the
subgroup of `Unitization R A` whose scalar part is `1`, whenever `A` is a non-unital `R`-algebra,
and moreover this isomorphism is implemented by the map `(x : A) ↦ (1 + x : Unitization R A)`. It
is because of this isomorphism, and the assoicated ties with multiplicative invertibility, that we
choose a `Monoid` (as opposed to an `AddMonoid`) structure on `Quasiregular`.  In addition,
in unital rings, we even have `IsQuasiregular x ↔ IsUnit (1 + x)`.

The *quasispectrum* of `a : A` (with respect to `R`) is defined in terms of quasiregularity, and
this is the natural analogue of the `spectrum` for non-unital rings. Indeed, it is true that
`quasiSpectrum R a = spectrum R a ∪ {0}` when `A` is unital.

In Mathlib, the quasispectrum is the domain of the continuous functions associated to the
*non-unital* continuous functional calculus.

## Main definitions

+ `Quasiregular R`: a structure wrapping `R` that inherits a distinct `Monoid` instance when `R`
  is a non-unital semiring.
+ `Unitization.unitsFstOne`: the subgroup with carrier `{ x : (Unitization R A)ˣ | x.fst = 1 }`.
+ `unitsFstOne_mulEquiv_unitsQuasiregular`: the group isomorphism between `Unitization.unitsFstOne`
  and the units of `Quasiregular` which sends `(1, x) ↦ x`.
+ `IsQuasiregular x`: the proposition that `x : R` is a unit with respect to the monoid structure on
  `Quasiregular R`, i.e., there is some `u : (Quasiregular R)ˣ` such that `u.val` is identified with
  `x` (via the natural equivalence between `R` and `Quasiregular R`).
+ `quasiSpectrum R a`: in an algebra over the semifield `R`, this is the set
  `{ r : R | r = 0 ∨ ¬ IsQuasiregular (-(r⁻¹ • a)) }`, which should be thought of as a version of
  the `spectrum` which is applicable in non-unital algebras.

## Main theorems

+ `isQuasiregular_iff_isUnit`: in a unital ring, `x` is quasiregular if and only if `1 + x` is
  a unit.
+ `quasiSpectrum_eq_spectrum_union`: in a unital `R`-algebra `A`, the quasispectrum of `a : A`
  is just the `spectrum` with zero added.
+ `Unitization.isQuasiregular_inr_iff`: `a : A` is quasiregular if and only if it is quasiregular
  in `Unitization R A` (via the coercion `Unitization.inr`).

-/

structure Quasiregular (R : Type*) where
  val : R

namespace Quasiregular

variable {R : Type*} [NonUnitalSemiring R]

@[simps]
def equiv : R ≃ Quasiregular R where
  toFun := .mk
  invFun := Quasiregular.val
  left_inv _ := rfl
  right_inv _ := rfl

instance instOne : One (Quasiregular R) where
  one := equiv 0

@[simp]
lemma val_one : (1 : Quasiregular R).val = 0 := rfl

instance instMul : Mul (Quasiregular R) where
  mul x y := .mk (y.val + x.val + x.val * y.val)

@[simp]
lemma val_mul (x y : Quasiregular R) : (x * y).val = y.val + x.val + x.val * y.val := rfl

instance instMonoid : Monoid (Quasiregular R) where
  one := equiv 0
  mul x y := .mk (y.val + x.val + x.val * y.val)
  mul_one _ := equiv.symm.injective <| by simp [-EmbeddingLike.apply_eq_iff_eq]
  one_mul _ := equiv.symm.injective <| by simp [-EmbeddingLike.apply_eq_iff_eq]
  mul_assoc x y z := equiv.symm.injective <| by simp [mul_add, add_mul, mul_assoc]; abel

@[simp]
lemma inv_add_add_mul_eq_zero (u : (Quasiregular R)ˣ) :
    u⁻¹.val.val + u.val.val + u.val.val * u⁻¹.val.val = 0 := by
  simpa [-Units.mul_inv] using congr($(u.mul_inv).val)

@[simp]
lemma add_inv_add_mul_eq_zero (u : (Quasiregular R)ˣ) :
    u.val.val + u⁻¹.val.val + u⁻¹.val.val * u.val.val = 0 := by
  simpa [-Units.inv_mul] using congr($(u.inv_mul).val)

end Quasiregular

namespace Unitization
open Quasiregular

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

variable (R A) in
/-- The subgroup of the units of `Unitization R A` whose scalar part is `1`. -/
def unitsFstOne : Subgroup (Unitization R A)ˣ where
  carrier := {x | x.val.fst = 1}
  one_mem' := rfl
  mul_mem' {x} {y} (hx : fst x.val = 1) (hy : fst y.val = 1) := by simp [hx, hy]
  inv_mem' {x} (hx : fst x.val = 1) := by
    simpa [-Units.mul_inv, hx] using congr(fstHom R A $(x.mul_inv))

@[simp]
lemma mem_unitsFstOne {x : (Unitization R A)ˣ} : x ∈ unitsFstOne R A ↔ x.val.fst = 1 := Iff.rfl

@[simp]
lemma unitsFstOne_val_val_fst (x : (unitsFstOne R A)) : x.val.val.fst = 1 :=
  mem_unitsFstOne.mp x.property

@[simp]
lemma unitsFstOne_val_inv_val_fst (x : (unitsFstOne R A)) : x.val⁻¹.val.fst = 1 :=
  mem_unitsFstOne.mp x⁻¹.property

variable (R) in
/-- this whole thing is gross -/
@[simps]
def unitsFstOne_mulEquiv_unitsQuasiregular : unitsFstOne R A ≃* (Quasiregular A)ˣ where
  toFun x :=
    { val := equiv x.val.val.snd
      inv := equiv x⁻¹.val.val.snd
      val_inv := equiv.symm.injective <| by
        simpa [-Units.mul_inv] using congr(snd $(x.val.mul_inv))
      inv_val := equiv.symm.injective <| by
        simpa [-Units.inv_mul] using congr(snd $(x.val.inv_mul)) }
  invFun x :=
    { val :=
      { val := 1 + equiv.symm x.val
        inv := 1 + equiv.symm x⁻¹.val
        val_inv := by
          convert congr((1 + $(inv_add_add_mul_eq_zero x) : Unitization R A)) using 1
          · simp only [mul_one, equiv_symm_apply, one_mul, inr_zero, add_zero, mul_add, add_mul,
              inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero]
        inv_val := by
          convert congr((1 + $(add_inv_add_mul_eq_zero x) : Unitization R A)) using 1
          · simp only [mul_one, equiv_symm_apply, one_mul, inr_zero, add_zero, mul_add, add_mul,
              inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero] }
      property := by simp }
  left_inv x := Subtype.ext <| Units.ext <| by simpa using x.val.val.inl_fst_add_inr_snd_eq
  right_inv x := Units.ext <| by simp [-equiv_symm_apply]
  map_mul' x y := by
    ext
    simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul, snd_mul,
      InvMemClass.coe_inv]
    apply equiv.symm.injective
    rw [x.property, y.property, one_smul, one_smul R]
    simp

end Unitization

section Quasiregular

open Quasiregular

variable {R : Type*} [NonUnitalSemiring R]

def IsQuasiregular (x : R) : Prop :=
  ∃ u : (Quasiregular R)ˣ, equiv.symm u.val = x

@[simp]
lemma isQuasiregular_zero : IsQuasiregular 0 := ⟨1, rfl⟩

lemma isQuasiregular_iff {x : R} :
    IsQuasiregular x ↔ ∃ y, y + x + x * y = 0 ∧ x + y + y * x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨equiv.symm u⁻¹.val, ⟨congr(equiv.symm $(u.mul_inv)), congr(equiv.symm $(u.inv_mul))⟩⟩
  · rintro ⟨y, hy₁, hy₂⟩
    refine ⟨⟨equiv x, equiv y, ?_, ?_⟩, rfl⟩
    all_goals
      apply equiv.symm.injective
      assumption

end Quasiregular

lemma IsQuasiregular.map {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) {x : R} (hx : IsQuasiregular x) :
    IsQuasiregular (f x) := by
  rw [isQuasiregular_iff] at hx ⊢
  obtain ⟨y, hy₁, hy₂⟩ := hx
  exact ⟨f y, by simpa using And.intro congr(f $(hy₁)) congr(f $(hy₂))⟩

lemma IsQuasiregular.isUnit_one_add_self {R : Type*} [Semiring R] {x : R} (hx : IsQuasiregular x) :
    IsUnit (1 + x) := by
  obtain ⟨y, hy₁, hy₂⟩ := isQuasiregular_iff.mp hx
  refine ⟨⟨1 + x, 1 + y, ?_, ?_⟩, rfl⟩
  · convert congr(1 + $(hy₁)) using 1 <;> first | noncomm_ring | simp
  · convert congr(1 + $(hy₂)) using 1 <;> first | noncomm_ring | simp

lemma isQuasiregular_iff_isUnit {R : Type*} [Ring R] {x : R} :
    IsQuasiregular x ↔ IsUnit (1 + x) := by
  refine ⟨IsQuasiregular.isUnit_one_add_self, fun hx ↦ ?_⟩
  rw [isQuasiregular_iff]
  use hx.unit⁻¹ - 1
  constructor
  case' h.left => have := congr($(hx.mul_val_inv) - 1)
  case' h.right => have := congr($(hx.val_inv_mul) - 1)
  all_goals
    rw [← sub_add_cancel (↑hx.unit⁻¹ : R) 1, sub_self] at this
    convert this using 1
    noncomm_ring

-- interestingly, this holds even in the semiring case.
lemma isQuasiregular_iff_isUnit' (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {x : A} :
    IsQuasiregular x ↔ IsUnit (1 + x : Unitization R A) := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨u, rfl⟩
    exact (Unitization.unitsFstOne_mulEquiv_unitsQuasiregular R).symm u |>.val.isUnit
  · exact ⟨(Unitization.unitsFstOne_mulEquiv_unitsQuasiregular R) ⟨hx.unit, by simp⟩, by simp⟩

variable (R : Type*) {A : Type*} [Semifield R] [NonUnitalRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

def quasiSpectrum (a : A) : Set R := { r : R | r = 0 ∨ ¬ IsQuasiregular (-(r⁻¹ • a)) }

lemma quasiSpectrum.zero_mem (a : A) : 0 ∈ quasiSpectrum R a := by
  rw [quasiSpectrum]; simp

instance quasiSpectrum.instZero (a : A) : Zero (quasiSpectrum R a) where
  zero := ⟨0, quasiSpectrum.zero_mem R a⟩

@[simp]
lemma quasiSpectrum.coe_zero (a : A) : (0 : quasiSpectrum R a) = (0 : R) := rfl

lemma quasiSpectrum.mem_of_not_quasiregular (a : A) {r : R} (hr : ¬ IsQuasiregular (-(r⁻¹ • a))) :
    r ∈ quasiSpectrum R a :=
  .inr hr

lemma smul_left_cancel_iff₀ {G α : Type*} [GroupWithZero G] [MulAction G α] {a b : α} {g : G}
    (hg : g ≠ 0) : g • a = g • b ↔ a = b :=
  hg.isUnit.smul_left_cancel

lemma quasiSpectrum_eq_spectrum_union (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A]
    (a : A) : quasiSpectrum R a = spectrum R a ∪ {0} := by
  ext r
  rw [quasiSpectrum]
  simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, spectrum.mem_iff]
  apply or_congr_right' fun (hr : r ≠ 0) ↦ ?_
  rw [not_iff_not, isQuasiregular_iff_isUnit, ← sub_eq_add_neg]
  lift r to Rˣ using hr.isUnit
  rw [← r.val_inv_eq_inv_val, Algebra.algebraMap_eq_smul_one]
  exact (IsUnit.smul_sub_iff_sub_inv_smul r a).symm

-- MOVE ME to `Algebra.Algebra.Unitization`
instance Unitization.instCanLift :
    CanLift (Unitization R A) A Unitization.inr (fun x ↦ x.fst = 0) where
  prf x hx := ⟨x.snd, Unitization.ext (by simp [hx]) rfl⟩

lemma Unitization.isQuasiregular_inr_iff (a : A) :
    IsQuasiregular (a : Unitization R A) ↔ IsQuasiregular a := by
  refine ⟨fun ha ↦ ?_, IsQuasiregular.map (inrNonUnitalAlgHom R A)⟩
  rw [isQuasiregular_iff] at ha ⊢
  obtain ⟨y, hy₁, hy₂⟩ := ha
  lift y to A using by simpa using congr(fstHom R A $(hy₁))
  refine ⟨y, ?_, ?_⟩ <;> exact inr_injective (R := R) <| by simpa

-- we need this for `R := ℝ≥0`, `S := ℝ`.
lemma Unitization.quasiSpectrum_eq_spectrum_union (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasiSpectrum R a = spectrum R (a : Unitization S A) ∪ {0} := by
  ext r
  rw [← _root_.quasiSpectrum_eq_spectrum_union]
  apply or_congr_right
  rw [not_iff_not, ← inr_smul, ← inr_neg, isQuasiregular_inr_iff]
