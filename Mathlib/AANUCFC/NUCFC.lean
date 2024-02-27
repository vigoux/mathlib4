import Mathlib.Topology.ContinuousFunction.FunctionalCalculus
import Mathlib.Algebra.Algebra.Unitization

structure Quasi (R : Type*) where
  val : R

namespace Quasi

variable {R : Type*} [NonUnitalSemiring R]

@[simps]
def equiv : R ≃ Quasi R where
  toFun := .mk
  invFun := Quasi.val
  left_inv _ := rfl
  right_inv _ := rfl

instance instOne : One (Quasi R) where
  one := equiv 0

@[simp]
lemma val_one : (1 : Quasi R).val = 0 := rfl

instance instMul : Mul (Quasi R) where
  mul x y := .mk (y.val + x.val + x.val * y.val)

@[simp]
lemma val_mul (x y : Quasi R) : (x * y).val = y.val + x.val + x.val * y.val := rfl

instance instMonoid : Monoid (Quasi R) where
  one := equiv 0
  mul x y := .mk (y.val + x.val + x.val * y.val)
  mul_one _ := equiv.symm.injective <| by simp [-EmbeddingLike.apply_eq_iff_eq]
  one_mul _ := equiv.symm.injective <| by simp [-EmbeddingLike.apply_eq_iff_eq]
  mul_assoc x y z := equiv.symm.injective <| by simp [mul_add, add_mul, mul_assoc]; abel

end Quasi

namespace Unitization

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
lemma mem_unitsFst_one (x : (Unitization R A)ˣ) : x ∈ unitsFstOne R A ↔ x.val.fst = 1 := Iff.rfl

variable (R) in
/-- this whole thing is gross -/
def unitsFstOne_mulEquiv_quasiUnits : unitsFstOne R A ≃* (Quasi A)ˣ where
  toFun x :=
    { val := Quasi.equiv x.val.val.snd
      inv := Quasi.equiv x⁻¹.val.val.snd
      val_inv := Quasi.equiv.symm.injective <| by
        have hx_inv : x.val⁻¹.val.fst = 1 := by
          have := congr($(x.val.mul_inv).fst)
          rwa [fst_mul, fst_one, x.property, one_mul] at this
        simp only [InvMemClass.coe_inv, Quasi.equiv_symm_apply, Quasi.val_mul,
          Quasi.equiv_apply_val, Quasi.val_one]
        have := congr(snd $(x.val.mul_inv))
        simp [-Units.mul_inv] at this
        rwa [x.property, hx_inv, one_smul, one_smul] at this
      inv_val := Quasi.equiv.symm.injective <| by
        have hx_inv : x.val⁻¹.val.fst = 1 := by
          have := congr($(x.val.mul_inv).fst)
          rwa [fst_mul, fst_one, x.property, one_mul] at this
        simp only [InvMemClass.coe_inv, Quasi.equiv_symm_apply, Quasi.val_mul,
          Quasi.equiv_apply_val, Quasi.val_one]
        have := congr(snd $(x.val.inv_mul))
        simp [-Units.inv_mul] at this
        rwa [x.property, hx_inv, one_smul, one_smul] at this }
  invFun x :=
    { val :=
      { val := addEquiv R A |>.symm (1, Quasi.equiv.symm x.val)
        inv := addEquiv R A |>.symm (1, Quasi.equiv.symm x⁻¹.val)
        val_inv := by
          ext
          exact mul_one 1 -- gross
          change 1 • Quasi.equiv.symm _ + 1 • Quasi.equiv.symm _ + -- gross
            Quasi.equiv.symm _ * Quasi.equiv.symm _ = _
          simpa [-Units.mul_inv] using congr($(x.mul_inv).val)
        inv_val := by
          ext
          exact mul_one 1 -- gross
          change 1 • Quasi.equiv.symm _ + 1 • Quasi.equiv.symm _ + -- gross
            Quasi.equiv.symm _ * Quasi.equiv.symm _ = _
          simpa [-Units.inv_mul] using congr($(x.inv_mul).val) }
      property := by simp; rfl } -- gross
  left_inv x := by
    ext
    · exact x.property.symm
    · rfl
  right_inv x := rfl
  map_mul' x y := by
    ext
    simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul, snd_mul,
      InvMemClass.coe_inv]
    apply Quasi.equiv.symm.injective
    rw [x.property, y.property, one_smul, one_smul R]
    simp

end Unitization

section Quasiregular

variable {R : Type*} [NonUnitalSemiring R]

def IsQuasiregular (x : R) : Prop :=
  ∃ u : (Quasi R)ˣ, Quasi.equiv.symm u.val = x

@[simp]
lemma isQuasiregular_zero : IsQuasiregular 0 := ⟨1, rfl⟩

lemma isQuasiregular_iff {x : R} :
    IsQuasiregular x ↔ ∃ y, y + x + x * y = 0 ∧ x + y + y * x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    use Quasi.equiv.symm u⁻¹.val
    exact ⟨congr(Quasi.equiv.symm $(u.mul_inv)), congr(Quasi.equiv.symm $(u.inv_mul))⟩
  · rintro ⟨y, hy₁, hy₂⟩
    refine ⟨⟨Quasi.equiv x, Quasi.equiv y, ?_, ?_⟩, rfl⟩
    all_goals
      apply Quasi.equiv.symm.injective
      assumption

end Quasiregular

lemma IsQuasiregular.map {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) {x : R} (hx : IsQuasiregular x) :
    IsQuasiregular (f x) := by
  rw [isQuasiregular_iff] at hx ⊢
  obtain ⟨y, hy₁, hy₂⟩ := hx
  exact ⟨f y, by simpa using And.intro congr(f $(hy₁)) congr(f $(hy₂))⟩

-- holds for semirings
lemma IsQuasiregular.isUnit_one_add_self {R : Type*} [Semiring R] {x : R} (hx : IsQuasiregular x) :
    IsUnit (1 + x) := by
  obtain ⟨y, hy₁, hy₂⟩ := isQuasiregular_iff.mp hx
  refine ⟨⟨1 + x, 1 + y, ?_, ?_⟩, rfl⟩
  · convert congr(1 + $(hy₁)) using 1 <;> first | noncomm_ring | simp
  · convert congr(1 + $(hy₂)) using 1 <;> first | noncomm_ring | simp

-- holds for rings
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
    IsQuasiregular x ↔ IsUnit ((Unitization.addEquiv R A).symm (1, x)) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (Unitization.unitsFstOne_mulEquiv_quasiUnits R).symm u |>.val.isUnit
  · intro hx
    let u : Unitization.unitsFstOne R A := ⟨hx.unit, rfl⟩
    exact ⟨(Unitization.unitsFstOne_mulEquiv_quasiUnits R) u, rfl⟩

variable (R : Type*) {A : Type*} [Semifield R] [NonUnitalRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

def quasiSpectrum (a : A) : Set R := { r : R | r = 0 ∨ ¬ IsQuasiregular (-(r⁻¹ • a)) }

lemma quasiSpectrum.zero_mem (a : A) : 0 ∈ quasiSpectrum R a := by
  rw [quasiSpectrum]; simp

instance quasiSpectrum.instZero (a : A) : Zero (quasiSpectrum R a) where
  zero := ⟨0, quasiSpectrum.zero_mem R a⟩

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

#exit

-- (0, a) quasiregular? exists (s, b), 0 = (0, a) ∘ (s, b) = (0, a) + (s, b) + (s, b) * (0, a)
#exit


structure Quasiunits (R : Type*) [NonUnitalRing R] where
  val : R
  inv : R
  val_inv : inv + val = val * inv
  inv_val : val + inv = inv * val

namespace Quasiunits

variable {R : Type*} [NonUnitalRing R]

#help tactic polyrith

instance Quasiunits.instMul : Mul (Quasiunits R) where
  mul x y :=
    { val := y.val + x.val + x.val * y.val
      inv := x.inv + y.inv + y.inv * x.inv
      val_inv := by
        have h₁ := x.val_inv
        have h₂ := x.inv_val
        simp [mul_add, add_mul]
        rw [mul_assoc x.val y.val y.inv, ← y.val_inv]
        rw [← mul_assoc _ y.inv, ← mul_assoc _ y.inv, ← mul_assoc _ y.inv,
          ← y.val_inv, mul_assoc x.val y.val y.inv, ← y.val_inv]
        simp [mul_add, add_mul]

        sorry
      inv_val := sorry  }


@[simps]
def Quasiunits.swap (x : Quasiunits R) : Quasiunits R where
  val := x.inv
  inv := x.val
  val_inv := x.inv_val
  inv_val := x.val_inv

def IsQuasiunit (x : R) : Prop := ∃ u : Quasiunits R, u.val = x

namespace Unitization

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

lemma isUnit_fst {x : Unitization R A} (hx : IsUnit x) : IsUnit x.fst :=
  hx.map <| fstHom R A

variable (R) in
def unitsFstOne : {x : (Unitization R A)ˣ // x.val.fst = 1} ≃ Quasiunits A where
  toFun x :=
    { val := x.val.val.snd
      inv := x.val⁻¹.val.snd
      val_inv := sorry
      inv_val := sorry }

  invFun := sorry
  left_inv := sorry
  right_inv := sorry

#exit

lemma isUnit_of_fst_one (x : (Unitization R A)ˣ) (hx_fst : x.val.fst = 1) :
    x⁻¹.val.snd + x.val.snd + x.val.snd * x⁻¹.val.snd = 0 := by
  have hx_inv_fst : x⁻¹.val.fst = 1 := by
    simpa [-Units.mul_inv, hx_fst] using congr(fstHom R A $(x.mul_inv))
  have := congr($(x.mul_inv).snd)
  simp [-Units.mul_inv, snd_one, hx_fst, hx_inv_fst] at this
  --have : x⁻¹.val.fst = (Units.map (fstHom R A) x)⁻¹ := sorry
  sorry



#exit

end Unitization
namespace v1

def quasiSpectrum (R : Type*) {A : Type*} [Semifield R] [NonUnitalRing A] [Module R A]
    (a : A) : Set R :=
  { r : R | ¬ ∃ b, r⁻¹ • a + b = r⁻¹ • a * b ∧ r⁻¹ • a + b = b * r⁻¹ • a }

variable (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A]

namespace quasiSpectrum

lemma quasiSpectrum_eq (a : A) : quasiSpectrum R a = spectrum R a := by
  ext r
  constructor
  · rintro ⟨b, hb₁, hb₂⟩

    sorry
  · sorry
#exit

-- 1 = (1 - r⁻¹ • a) * b = b - r⁻¹ • a * b
-- set b = 1 - c, then we find 1 = (1 - c) - r⁻¹ • a * (1 - c) = 1 - c - r⁻¹ • a + r⁻¹ • a * c


-- `(1 + b)` is a unit in `Unitization R A`. Then `∃ x, (1 + b) x = 1`, but notice,
-- we must have `x = 1 + y` for some `y` (trivial, even in semirings).
-- so `1 = (1 + b) * (1 + y) = 1 + b + y + b * y` so `b + y + b * y = 0`.

-- So take `(1 + b)` and `(1 + a)` both invertible, and suppose they have inverses
-- `(1 + x)` and `(1 + y)`, in reverse order, respectively.

-- `(1 + b) * (1 + a) = 1 + a + b + b * a`
-- `(1 + x) * (1 + y) = 1 + y * x + x * y`

-- so, if `b` is the unit in `A₁`, then `1 - c` is the unit in `A`.

-- 1 = b * (1 - r⁻¹ • a) = b - r⁻¹ • b * a

  -- [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

-- yuck we need `Semifield`

end v1

namespace v2

abbrev spectrumₙ (R : Type*) {S : outParam Type*} {A : Type*} [CommSemiring R] [CommRing S]
    [NonUnitalRing A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [Algebra R S] [DistribMulAction R A] [IsScalarTower R S A] (a : A) : Set R :=
  spectrum R (a : Unitization S A)

variable (R : Type*) {S A : Type*} [CommSemiring R] [CommRing S]
    [NonUnitalRing A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [Algebra R S] [DistribMulAction R A] [IsScalarTower R S A] (a : A)

variable (a : A)

end v2

#exit

/-
plan:

1. define the quasispectrum (over a semifield) and show that it is equal to the spectrum when the
  ring is unital.
2. define the nonunital cfc class in terms of this.



-/
