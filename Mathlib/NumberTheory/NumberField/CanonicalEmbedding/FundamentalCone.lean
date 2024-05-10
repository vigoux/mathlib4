/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Fundamental Cone

Let `K` be a number field of signature `(r₁, r₂)`. We define an action of the units `(𝓞 K)ˣ` on
the space `ℝ^r₁ × ℂ^r₂`. The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂` that is a fundamental
domain for the action of `(𝓞 K)ˣ` up to roots of unity.

## Main definitions and results

* `NumberField.mixedEmbedding.unitSMul`: the action of `(𝓞 K)ˣ` on `ℝ^r₁ × ℂ^r₂` defined, for
`u : (𝓞 K)ˣ`, by multiplication component by component with `mixedEmbedding K u`.

* `NumberField.mixedEmbedding.fundamentalCone`: a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset fixed
by multiplication by a scalar, see `smul_mem_of_mem`--, that is also a fundamental domain for the
action of `(𝓞 K)ˣ` up to roots of unity, see `exists_unitSMul_me` and
`torsion_unitSMul_mem_of_mem`.

* `NumberField.mixedEmbedding.fundamentalCone.integralPoint`: the subset of elements of the
fundamental cone that are images by `mixedEmbedding` of algebraic integers of `K`.

* `NumberField.mixedEmbedding.fundamentalCone.integralPointQuotEquivIsPrincipal`: the equivalence
between `fundamentalCone.integralPoint K / torsion K` and the non-zero principal ideals of `𝓞 K`.

* `NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_norm_mul`: for `n` positive, the
number of principal ideals in `𝓞 K` of norm `n` multiplied by the number of roots of unity is
equal to the number of `fundamentalCone.integralPoint K` of norm `n`.

## Tags

number field, canonical embedding, principal ideals
-/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

noncomputable section UnitSMul

/-- The action of `(𝓞 K)ˣ` on `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ`, by multiplication components
by components with `mixedEmbedding K u`. -/
@[simps]
instance unitSMul : SMul (𝓞 K)ˣ (E K) where
  smul := fun u x ↦ (mixedEmbedding K u) * x

instance : MulAction (𝓞 K)ˣ (E K) where
  one_smul := fun _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, Units.coe_mul, map_mul, mul_assoc]

instance : SMulZeroClass (𝓞 K)ˣ (E K) where
  smul_zero := fun _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, mul_zero]

variable [NumberField K]

theorem unitSMul_eq_iff_mul_eq {x y : (𝓞 K)} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u * x = y := by
  rw [unitSMul_smul, ← map_mul, Function.Injective.eq_iff, ← RingOfIntegers.coe_eq_algebraMap,
    ← map_mul, ← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K

theorem norm_unit (u : (𝓞 K)ˣ) :
    mixedEmbedding.norm (mixedEmbedding K u) = 1 := by
  rw [norm_eq_norm, show |(Algebra.norm ℚ) (u : K)| = 1
      by exact NumberField.isUnit_iff_norm.mp (Units.isUnit u), Rat.cast_one]

theorem norm_unitSMul (u : (𝓞 K)ˣ) (x : E K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by
  rw [unitSMul_smul, map_mul, norm_unit, one_mul]

theorem unitSMul_eq_zero (u : (𝓞 K)ˣ) (x : E K) :
    u • x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext w
    · have := congr_fun (congr_arg Prod.fst h) w
      rw [unitSMul_smul, Prod.fst_mul, Pi.mul_apply, Prod.fst_zero, Pi.zero_apply, mul_eq_zero]
        at this
      refine this.resolve_left (by simp)
    · have := congr_fun (congr_arg Prod.snd h) w
      rw [unitSMul_smul, Prod.snd_mul, Pi.mul_apply, Prod.snd_zero, Pi.zero_apply, mul_eq_zero]
        at this
      refine this.resolve_left (by simp)
  · rw [h, smul_zero]

end UnitSMul

noncomputable section logMap

open NumberField.Units NumberField.Units.dirichletUnitTheorem FiniteDimensional

variable [NumberField K] {K}

open Classical in
/-- The map from `ℝ^r₁ × ℂ^r₂` to `{w : InfinitePlace K // w ≠ w₀} → ℝ` (with `w₀` a fixed place)
define in such way that: 1) it factors the map `logEmbedding`, see `logMap_eq_logEmbedding`;
2) it is constant on the lines `{c • x | c ∈ ℝ}`, see `logMap_smul`. -/
def logMap (x : E K) : {w : InfinitePlace K // w ≠ w₀} → ℝ := fun w ↦
    if hw : IsReal w.val then
      Real.log ‖x.1 ⟨w.val, hw⟩‖ - Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹
    else
      2 * (Real.log ‖x.2 ⟨w.val, not_isReal_iff_isComplex.mp hw⟩‖ -
        Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹)

theorem logMap_zero : logMap (0 : E K) = 0 := by
  ext
  simp_rw [logMap, Prod.fst_zero, Prod.snd_zero, map_zero, Pi.zero_apply, norm_zero, Real.log_zero,
    zero_mul, sub_zero, mul_zero, dite_eq_ite, ite_self]

theorem logMap_mul {x y : E K} (hx : mixedEmbedding.norm x ≠ 0) (hy : mixedEmbedding.norm y ≠ 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap]
  split_ifs with hw
  · rw [Prod.fst_mul, Pi.mul_apply, norm_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
    · ring
    · exact norm_ne_zero_iff.mpr <| (mixedEmbedding.norm_ne_zero_iff.mp hx).1 ⟨_, hw⟩
    · exact norm_ne_zero_iff.mpr <| (mixedEmbedding.norm_ne_zero_iff.mp hy).1 ⟨_, hw⟩
  · replace hw := not_isReal_iff_isComplex.mp hw
    rw [Prod.snd_mul, Pi.mul_apply, norm_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
    · ring
    · exact norm_ne_zero_iff.mpr <| (mixedEmbedding.norm_ne_zero_iff.mp hx).2 ⟨_, hw⟩
    · exact norm_ne_zero_iff.mpr <| (mixedEmbedding.norm_ne_zero_iff.mp hy).2 ⟨_, hw⟩

theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
    logMap (mixedEmbedding K u) = logEmbedding K u := by
  ext
  simp_rw [logMap, mixedEmbedding.norm_unit, Real.log_one, zero_mul, sub_zero, logEmbedding,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, mult, Nat.cast_ite, ite_mul, Nat.cast_one, one_mul,
    Nat.cast_ofNat, mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply, norm_embedding_eq,
    norm_embedding_of_isReal]
  rfl

theorem logMap_unitSMul (u : (𝓞 K)ˣ) {x : E K} (hx : mixedEmbedding.norm x ≠ 0) :
    logMap (u • x) = logEmbedding K u + logMap x := by
  rw [unitSMul_smul, logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

theorem logMap_torsion_unitSMul (x : E K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    logMap (ζ • x) = logMap x := by
  ext
  simp_rw [logMap, unitSMul_smul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, map_mul,
    norm_eq_norm, mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply,
    show |(Algebra.norm ℚ) (ζ : K)| = 1 by exact NumberField.isUnit_iff_norm.mp (Units.isUnit ζ),
    Rat.cast_one, one_mul, norm_embedding_eq, norm_embedding_of_isReal, (mem_torsion K).mp hζ,
    one_mul]

theorem logMap_smul {x : E K} (hx : mixedEmbedding.norm x ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    logMap (c • x) = logMap x := by
  rw [show c • x = ((fun _ ↦ c, fun _ ↦ c) : (E K)) * x by rfl, logMap_mul _ hx, add_left_eq_self]
  ext
  have hr : (finrank ℚ K : ℝ) ≠ 0 :=  Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
  simp_rw [logMap, Pi.zero_apply, norm_real, Real.log_pow, mul_comm, inv_mul_cancel_left₀ hr,
    Real.norm_eq_abs, Complex.norm_eq_abs,  Complex.abs_ofReal, sub_self, mul_zero, dite_eq_ite,
    ite_self]
  rw [norm_real]
  exact pow_ne_zero _ (abs_ne_zero.mpr hc)

end logMap

noncomputable section

open NumberField.Units NumberField.Units.dirichletUnitTheorem nonZeroDivisors

variable [NumberField K]

open Classical
/-- The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset fixed by multiplication by
a scalar, see `smul_mem_of_mem`--, that is also a fundamental domain for the action of `(𝓞 K)ˣ` up
to roots of unity, see `exists_unitSMul_mem` and `torsion_unitSMul_mem_of_mem`. -/
def fundamentalCone : Set (E K) :=
  logMap⁻¹' (Zspan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _)) \
      {x | mixedEmbedding.norm x = 0}

namespace fundamentalCone

variable {K}

theorem smul_mem_of_mem {x : E K} (hx : x ∈ fundamentalCone K) {c : ℝ} (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_smul hx.2 hc]
    exact hx.1
  · rw [Set.mem_setOf_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
    exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩

theorem exists_unitSMul_mem {x : E K} (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ fundamentalCone K := by
  classical
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : ∃ e : unitLattice K, e + logMap x ∈ Zspan.fundamentalDomain B
  · exact ⟨u, by rwa [Set.mem_preimage, logMap_unitSMul u hx], by simp [hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Basis.ofZlatticeBasis_span ℝ (unitLattice K)]⟩, h₂⟩

theorem torsion_unitSMul_mem_of_mem {x : E K} (hx : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_torsion_unitSMul _ hζ]
    exact hx.1
  · simpa only [unitSMul_smul, Set.mem_setOf_eq, map_mul, norm_eq_norm, Rat.cast_abs, mul_eq_zero,
    abs_eq_zero, Rat.cast_eq_zero, Algebra.norm_eq_zero_iff, RingOfIntegers.coe_eq_zero_iff,
    Units.ne_zero, false_or] using hx.2

theorem unitSMul_mem_iff_mem_torsion {x : E K} (hx' : x ∈ fundamentalCone K) (u : (𝓞 K)ˣ) :
    u • x ∈ fundamentalCone K ↔ u ∈ torsion K := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← logEmbedding_eq_zero_iff]
    let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
    refine (Subtype.mk_eq_mk (h := ?_) (h' := ?_)).mp <|
      ExistsUnique.unique (Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)) ?_ ?_
    · change logEmbedding K u ∈ (Submodule.span ℤ (Set.range B)).toAddSubgroup
      rw [Basis.ofZlatticeBasis_span ℝ (unitLattice K)]
      exact ⟨u, trivial, rfl⟩
    · exact Submodule.zero_mem _
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, ← logMap_unitSMul _ hx'.2]
      exact h.1
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
      exact hx'.1
  · exact torsion_unitSMul_mem_of_mem hx' h

variable (K) in
/-- The set of images by `mixedEmbedding` of algebraic integers of `K` contained in the
fundamental cone. -/
def integralPoint : Set (E K) :=
  fundamentalCone K ∩ mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))

theorem exists_unique_preimage_of_integralPoint {x : E K} (hx : x ∈ integralPoint K) :
    ∃! a : (𝓞 K), mixedEmbedding K a = x := by
  refine ⟨hx.2.choose_spec.1.choose, ?_, fun _ h ↦ ?_⟩
  · convert hx.2.choose_spec.2
    exact hx.2.choose_spec.1.choose_spec
  · rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, h]
    convert hx.2.choose_spec.2.symm
    exact hx.2.choose_spec.1.choose_spec

theorem integralPoint_ne_zero (a : integralPoint K) :
    (a : E K) ≠ 0 := by
  by_contra!
  exact a.prop.1.2 (this.symm ▸ mixedEmbedding.norm.map_zero')

/-- For `a : fundamentalCone K`, the unique non-zero algebraic integer which image by
`mixedEmbedding` is equal to `a`. -/
def preimageOfIntegralPoint (a : integralPoint K) : (𝓞 K)⁰ :=
  ⟨a.prop.2.choose_spec.1.choose, by
    simp_rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, RingOfIntegers.ext_iff,
      a.prop.2.choose_spec.1.choose_spec, ← (mixedEmbedding_injective K).eq_iff, map_zero,
      a.prop.2.choose_spec.2, integralPoint_ne_zero a, not_false_eq_true]⟩

@[simp]
theorem mixedEmbedding_preimageOfIntegralPoint (a : integralPoint K) :
    mixedEmbedding K (preimageOfIntegralPoint a : 𝓞 K) = (a : E K) := by
  rw [RingOfIntegers.coe_eq_algebraMap, ← a.prop.2.choose_spec.2, preimageOfIntegralPoint,
    a.prop.2.choose_spec.1.choose_spec]

theorem preimageOfIntegralPoint_mixedEmbedding {x : (𝓞 K)⁰}
    (hx : mixedEmbedding K (x : 𝓞 K) ∈ integralPoint K) :
    preimageOfIntegralPoint (⟨mixedEmbedding K (x : 𝓞 K), hx⟩) = x := by
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfIntegralPoint]

theorem exists_unitSMul_mem_integralPoint {x : E K} (hx : x ≠ 0)
    (hx' : x ∈ mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ integralPoint K := by
  replace hx : mixedEmbedding.norm x ≠ 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx')).not.mpr hx
  obtain ⟨u, hu⟩ := exists_unitSMul_mem hx
  obtain ⟨_, ⟨⟨x, rfl⟩, ⟨_, rfl⟩⟩⟩ := hx'
  exact ⟨u, hu, (u * x : K), ⟨u * x, rfl⟩, by simp_rw [unitSMul_smul, ← map_mul]⟩

theorem torsion_unitSMul_mem_integralPoint {x : E K} {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
    (hx : x ∈ integralPoint K) :
    ζ • x ∈ integralPoint K := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx.2
  refine ⟨torsion_unitSMul_mem_of_mem hx.1 hζ, ⟨ζ * a, ?_, ?_⟩⟩
  · exact ⟨ζ * a, rfl⟩
  · rw [unitSMul_smul, map_mul]

variable (K) in
/-- The map that sends an element of `a : fundamentalCone K` to the associates class
of its preimage in `(𝓞 K)⁰`. By quotienting by the kernel of the map, which is equal to the group
of roots of unity, we get the equivalence `integralPointQuotEquivAssociates`. -/
def integralPointToAssociates (a : integralPoint K) : Associates (𝓞 K)⁰ :=
  ⟦preimageOfIntegralPoint a⟧

@[simp]
theorem integralPointToAssociates_apply (a : integralPoint K) :
    (integralPointToAssociates K a) = ⟦preimageOfIntegralPoint a⟧ := rfl

variable (K) in
theorem integralPointToAssociates_surjective :
    Function.Surjective (integralPointToAssociates K) := by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, u • mixedEmbedding K (x : 𝓞 K) ∈ integralPoint K := by
    refine exists_unitSMul_mem_integralPoint ?_  ⟨(x : 𝓞 K), Set.mem_range_self _, rfl⟩
    rw [map_ne_zero, RingOfIntegers.coe_ne_zero_iff]
    exact nonZeroDivisors.coe_ne_zero _
  refine ⟨⟨u • mixedEmbedding K (x : 𝓞 K), hu⟩,
    Quotient.sound ⟨(nonZeroDivisorsUnitsEquiv (𝓞 K)).symm u⁻¹, ?_⟩⟩
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    Submonoid.coe_mul, map_mul, mixedEmbedding_preimageOfIntegralPoint,
    nonZeroDivisorsUnitsEquiv_symm_apply, unitSMul_smul, ← map_mul, mul_comm,
    Units.mul_inv_cancel_right]

@[simps]
instance integralPoint_torsionSMul: SMul (torsion K) (integralPoint K) where
  smul := fun ⟨ζ, hζ⟩ ⟨x, hx⟩ ↦ ⟨ζ • x, torsion_unitSMul_mem_integralPoint hζ hx⟩

instance : MulAction (torsion K) (integralPoint K) where
  one_smul := fun _ ↦ by
    rw [Subtype.mk_eq_mk, integralPoint_torsionSMul_smul_coe, OneMemClass.coe_one, one_smul]
  mul_smul := fun _ _ _ ↦ by
    rw [Subtype.mk_eq_mk]
    simp_rw [integralPoint_torsionSMul_smul_coe, Submonoid.coe_mul, mul_smul]

theorem integralPointToAssociates_eq_iff (a b : integralPoint K) :
    integralPointToAssociates K a = integralPointToAssociates K b ↔
      ∃ ζ : torsion K, ζ • a = b := by
  simp_rw [integralPointToAssociates_apply, Associates.quotient_mk_eq_mk,
    Associates.mk_eq_mk_iff_associated, Associated, mul_comm, Subtype.ext_iff,
    RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, Submonoid.coe_mul, map_mul,
    mixedEmbedding_preimageOfIntegralPoint, integralPoint_torsionSMul_smul_coe]
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun ⟨⟨ζ, _⟩, h⟩ ↦ ?_⟩
  · refine ⟨⟨(nonZeroDivisorsUnitsEquiv (𝓞 K)) u, ?_⟩, by simp [hu]⟩
    exact (unitSMul_mem_iff_mem_torsion a.prop.1 _).mp (by simp [hu, b.prop.1])
  · exact ⟨(nonZeroDivisorsUnitsEquiv (𝓞 K)).symm ζ, by rwa [nonZeroDivisorsUnitsEquiv_symm_apply]⟩

variable (K) in
/-- The equivalence between `fundamentalCone.integralPoint K / torsion K` and
`Associates (𝓞 K)⁰`. -/
def integralPointQuotEquivAssociates :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) ≃ Associates (𝓞 K)⁰ := by
  refine Equiv.ofBijective
    (Quotient.lift (integralPointToAssociates K)
      fun _ _ h ↦ ((integralPointToAssociates_eq_iff _ _).mpr h).symm)
    ⟨by
      convert Setoid.ker_lift_injective (integralPointToAssociates K)
      all_goals
      · ext a b
        rw [Setoid.ker_def, eq_comm, integralPointToAssociates_eq_iff b a,
        MulAction.orbitRel_apply, MulAction.mem_orbit_iff],
      (Quot.surjective_lift _).mpr (integralPointToAssociates_surjective K)⟩

@[simp]
theorem integralPointQuotEquivAssociates_apply (a : integralPoint K) :
    integralPointQuotEquivAssociates K ⟦a⟧ = ⟦preimageOfIntegralPoint a⟧ := rfl

theorem integralPoint_torsionSMul_stabilizer {a : integralPoint K} :
    MulAction.stabilizer (torsion K) a = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ ↦ ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integralPoint_torsionSMul_smul_coe,
    unitSMul_smul, ← mixedEmbedding_preimageOfIntegralPoint, ← map_mul,
    (mixedEmbedding_injective K).eq_iff, ← map_mul, ← RingOfIntegers.ext_iff, mul_eq_right₀,
    Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  exact nonZeroDivisors.coe_ne_zero _

open Submodule Ideal

variable (K) in
def integralPointEquiv :
    integralPoint K ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} × torsion K :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integralPoint K)).trans
    ((Equiv.sigmaEquivProdOfEquiv (by
        intro _
        simp_rw [integralPoint_torsionSMul_stabilizer]
        exact QuotientGroup.quotientBot.toEquiv)).trans
      (Equiv.prodCongrLeft (fun _ ↦ (integralPointQuotEquivAssociates K).trans
        (associatesNonZeroDivisorsEquivIsPrincipal (𝓞 K)))))

@[simp]
theorem integralPointEquiv_apply_fst (a : integralPoint K) :
    ((integralPointEquiv K a).1 : Ideal (𝓞 K)) = span {(preimageOfIntegralPoint a : 𝓞 K)} := by
  simp_rw [← associatesNonZeroDivisorsEquivIsPrincipal_apply,
    ← integralPointQuotEquivAssociates_apply]
  rfl

/-- The `mixedEmbedding.norm` of `a : integralPoint K` as a natural integer, see `intNorm_coe` . -/
def intNorm (a : integralPoint K) : ℕ := (Algebra.norm ℤ (preimageOfIntegralPoint a : 𝓞 K)).natAbs

@[simp]
theorem intNorm_coe (a : integralPoint K) :
    (intNorm a : ℝ) = mixedEmbedding.norm (a : E K) := by
  rw [intNorm, Int.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, Algebra.coe_norm_int,
    ← norm_eq_norm, mixedEmbedding_preimageOfIntegralPoint]

/-- The norm `intNorm` defined on `fundamentalCone.integralPoint K` lifts to a function
on the classes of `fundamentalCone.integralPoint K` modulo `torsion K`. -/
def quotIntNorm :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) → ℕ :=
  Quotient.lift (fun x ↦ intNorm x) fun a b ⟨u, hu⟩ ↦ by
    rw [← Nat.cast_inj (R := ℝ), intNorm_coe, intNorm_coe, ← hu, integralPoint_torsionSMul_smul_coe,
      norm_unitSMul]

@[simp]
theorem quotIntNorm_apply (a : integralPoint K) : quotIntNorm ⟦a⟧ = intNorm a := rfl

variable (K) in
def integralPointEquivNorm (n : ℕ) :
    {a : integralPoint K // intNorm a = n} ≃
      {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
  calc {a // intNorm a = n}
      ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} × torsion K //
          absNorm (I.1 : Ideal (𝓞 K)) = n} :=
      (Equiv.subtypeEquiv (integralPointEquiv K) fun _ ↦ by simp [intNorm, absNorm_span_singleton])
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} // absNorm (I.1 : Ideal (𝓞 K)) = n} ×
          torsion K := by
      convert Equiv.trans (Equiv.subtypeProdEquivProd (q := fun _ : torsion K ↦ True))
        (Equiv.prodCongrRight fun _ ↦ (Equiv.Set.univ _).symm).symm
      rw [and_true]
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
      Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1) (fun I ↦ absNorm I.1 = n))

@[simp]
theorem integralPointEquivNorm_apply_fst {n : ℕ} {a : integralPoint K} (ha : intNorm a = n) :
    ((integralPointEquivNorm K n ⟨a, ha⟩).1 : Ideal (𝓞 K)) =
      span {(preimageOfIntegralPoint a : 𝓞 K)} := by
  simp_rw [← associatesNonZeroDivisorsEquivIsPrincipal_apply,
    ← integralPointQuotEquivAssociates_apply]
  rfl


#exit

  let e := Equiv.subtypeSigmaEquiv
    (fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} ↦ torsion K)
    (fun I ↦ absNorm (I.1 : Ideal (𝓞 K)) = n)
  refine Equiv.trans e ?_
  sorry

variable (K) in
def iso2 {n : ℕ} (hn : 0 < n) :
    {a : integralPoint K // intNorm a = n} ≃
      {I : Ideal (𝓞 K) // IsPrincipal I ∧ absNorm I = n} × (torsion K) := by
  refine (Equiv.subtypeEquiv (p := fun a ↦ intNorm a = n)
    (q := fun σ ↦ Ideal.absNorm σ.1.val = n) (iso1 K)
    (fun _ ↦ by simp_rw [iso1_apply_fst, absNorm_span_singleton, intNorm])).trans
    ?_
  -- Defining everything in one go gives a timeout so we split the construction into two parts
  refine Equiv.trans ((Equiv.subtypeSigmaEquiv
    (fun I : { I : Ideal (𝓞 K) // IsPrincipal I } ↦ (torsion K ⧸ idealStab K I))
    (fun I ↦ absNorm I.val = n)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter (fun I ↦ IsPrincipal I)
        (fun I ↦ absNorm I = n)).sigmaCongr fun ⟨I, hI⟩ ↦ ?_)) (Equiv.sigmaEquivProd _ _)
  rw [idealStab, if_neg (by rw [← absNorm_eq_zero_iff, hI]; linarith)]
  exact QuotientGroup.quotientBot.toEquiv

theorem iso2_apply_fst {n : ℕ} (hn : 0 < n) {a : integralPoint K} (ha : intNorm a = n):
    (iso2 K hn ⟨a, ha⟩).fst = span { preimageOfIntegralPoint a} := by
  unfold iso2
  simp_rw [← associatesEquivIsPrincipal_apply, ← integralPointQuotEquivAssociates_apply]
  rfl

variable (K)

/-- For `n` positive, the number of `fundamentalCone.integralPoint K` of
norm `n` is equal to the number of principal ideals in `𝓞 K` of norm `n` multiplied by the number
of roots of unity in `K`. -/
theorem card_isPrincipal_norm_eq {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I = n} * torsionOrder K =
        Nat.card {a : integralPoint K | intNorm a = n} := by
  rw [torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  refine Nat.card_congr ?_
  exact (iso2 K hn).symm

theorem finite1 (n : ℕ) : Finite {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I = n} := by
  by_cases hn : n = 0
  · simp_rw [hn, absNorm_eq_zero_iff]
    refine Set.Finite.subset (Set.finite_singleton ⊥) (by simp)
  · exact Set.Finite.subset (finite_setOf_absNorm_eq (Nat.pos_of_ne_zero hn)) (by simp)

theorem finite2 (n : ℕ) : Finite {a : integralPoint K | intNorm a = n} := by
  by_cases hn : n = 0
  · simp_rw [hn, intNorm, Int.natAbs_eq_zero, Algebra.norm_eq_zero_iff,
      preimageOfIntegralPoint_eq_zero_iff]
    exact Set.finite_singleton _
  · convert Finite.of_equiv _ (iso2 K (Nat.pos_of_ne_zero hn)).symm
    exact @Finite.instProd _ _ (finite1 K n) (Finite.of_fintype (torsion K))

open nonZeroDivisors

theorem card_isPrincipal_norm_le (n : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal I.val ∧ absNorm I.val ≤ n} * torsionOrder K =
      Nat.card {a : integralPoint K | intNorm a ≤ n} := by sorry

theorem card_isPrincipal_norm_in_Icc (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ∈ Finset.Icc 1 n} * torsionOrder K =
      Nat.card {a : integralPoint K | intNorm a ∈ Finset.Icc 1 n} := by
  have : ∀ i, Fintype {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I = i} :=
    fun i ↦ @Fintype.ofFinite _ (finite1 K i)
  have : ∀ i, Fintype {a : integralPoint K | intNorm a = i} :=
    fun i ↦ @Fintype.ofFinite _ (finite2 K i)
  have : Fintype {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ∈ Finset.Icc 1 n} := by
    rw [show {I | IsPrincipal I ∧ absNorm I ∈ Finset.Icc 1 n} =
          (⋃ i ∈ Set.Icc 1 n, {I | IsPrincipal I ∧ absNorm I = i}) by ext; simp]
    exact @Fintype.ofFinite _ <| Set.Finite.biUnion (Set.finite_Icc _ _) (fun _ _ ↦ Set.toFinite _)
  have : Fintype {a : integralPoint K | intNorm a ∈ Finset.Icc 1 n} := by
    rw [show {a | intNorm a ∈ Finset.Icc 1 n} =
          (⋃ i ∈ Set.Icc 1 n, {a | intNorm a = i}) by ext; simp]
    exact @Fintype.ofFinite _ <| Set.Finite.biUnion (Set.finite_Icc _ _) (fun _ _ ↦ Set.toFinite _)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Set.toFinset_card, ← Set.toFinset_card,
    Finset.card_eq_sum_card_fiberwise fun _ h ↦ by convert (Set.mem_toFinset.mp h).2,
    Finset.sum_mul, Finset.card_eq_sum_card_fiberwise fun _ h ↦ by convert (Set.mem_toFinset.mp h)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  convert card_isPrincipal_norm_eq K (Finset.mem_Icc.mp hi).1
  · rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr; ext
    simpa only [Finset.mem_Icc, Finset.mem_filter, Set.mem_toFinset, Set.mem_setOf_eq,
      and_congr_left_iff, and_iff_left_iff_imp] using fun h _ ↦ by rwa [← Finset.mem_Icc, h]
  · rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr; ext
    simpa only [Finset.mem_Icc, Finset.mem_filter, Set.mem_toFinset, Set.mem_setOf_eq,
      and_iff_right_iff_imp] using fun h ↦ by rwa [← Finset.mem_Icc, h]

open Filter Asymptotics

theorem card_isPrincipal_norm_le_div_atTop :
    (fun n ↦ (Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ≤ n} * torsionOrder K : ℝ) / n)
      ~[atTop] fun n ↦ (Nat.card {a : integralPoint K | intNorm a ≤ n} : ℝ) / n := by
  have : ∀ᶠ n in atTop, (Nat.card {a : integralPoint K | intNorm a ≤ n} : ℝ) / n ≠ 0 := sorry
  rw [isEquivalent_iff_tendsto_one this]
  simp_rw [Pi.div_def]
  have : ∀ n,
    (Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ≤ n} * torsionOrder K  : ℝ) =
      Nat.card {a : integralPoint K | intNorm a ≤ n} + (torsionOrder K - 1) := sorry
  simp_rw [this]
  simp_rw [div_div_div_cancel_right _ sorry, add_div, div_self sorry]
  sorry

#exit


  refine Asymptotics.IsLittleO.isEquivalent ?_
  simp_rw [Pi.sub_def, ← sub_div]
  have : ∀ n,
    (Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ≤ n} * torsionOrder K  : ℝ) -
      Nat.card {a : integralPoint K | intNorm a ≤ n} = torsionOrder K - 1 := sorry
  simp_rw [this]
  refine IsLittleO.trans ?_ (Asymptotics.isLittleO_zero (α := ℕ) (F' := ℝ) (E' := ℝ) _ atTop)
  rw?


#exit

  rw?
  rw [eventuallyEq_iff_sub, Pi.sub_def]
  simp_rw [← sub_div]
  have : ∀ n,
    (Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ≤ n} * torsionOrder K  : ℝ) -
      Nat.card {a : integralPoint K | intNorm a ≤ n} = torsionOrder K - 1 := sorry
  conv =>
    enter [2, i, 1]
    rw [this]
  refine Filter.eventuallyEq_of_left_inv_of_right_inv ?_ ?_ ?_

  have : (fun n ↦ (Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ≤ n} *
    torsionOrder K : ℝ) / n) =
    (fun n ↦ (Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ∈ Finset.Icc 1 n} *
      torsionOrder K  - 1 : ℝ) / n) := sorry
  rw [this]
  have : (fun n ↦ (Nat.card {a : integralPoint K | intNorm a ≤ n} : ℝ) / n) =
    (fun n ↦ (Nat.card {a : integralPoint K | intNorm a ∈ Finset.Icc 1 n} - 1 : ℝ) / n) := sorry
  rw [this]


  sorry


end fundamentalCone

end
