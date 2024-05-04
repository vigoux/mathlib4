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
between `fundamentalCone.integralPoint K / torsion K` and the principal ideals of `𝓞 K`.

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
  rw [unitSMul_smul, ← map_mul, Function.Injective.eq_iff, ← Submonoid.coe_mul, Subtype.mk_eq_mk]
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

open NumberField.Units NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

open Classical
/-- The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset fixed by multiplication by
a scalar, see `smul_mem_of_mem`--, that is also a fundamental domain for the action of `(𝓞 K)ˣ` up
to roots of unity, see `exists_unitSMul_mem` and `torsion_unitSMul_mem_of_mem`. -/
def fundamentalCone : Set (E K) :=
  logMap⁻¹' (Zspan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _)) \
      {x | mixedEmbedding.norm x = 0} ∪ {0}

namespace fundamentalCone

protected theorem zero_mem : 0 ∈ fundamentalCone K := Set.mem_union_right _ rfl

variable {K}

theorem smul_mem_of_mem {x : E K} (hx : x ∈ fundamentalCone K)
    (c : ℝ) : c • x ∈ fundamentalCone K := by
  by_cases hc : c = 0
  · rw [hc, zero_smul]
    exact fundamentalCone.zero_mem K
  · cases hx with
  | inl hx =>
      refine Set.mem_union_left _ ⟨?_, ?_⟩
      · rw [Set.mem_preimage, logMap_smul hx.2 hc]
        exact hx.1
      · rw [Set.mem_setOf_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
        exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩
  | inr hx =>
      rw [hx, smul_zero]
      exact fundamentalCone.zero_mem K

theorem exists_unitSMul_mem {x : E K} (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ fundamentalCone K := by
  classical
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : ∃ e : unitLattice K, e + logMap x ∈ Zspan.fundamentalDomain B
  · exact ⟨u,
      Set.mem_union_left _ ⟨by rwa [Set.mem_preimage, logMap_unitSMul u hx], by simp [hx]⟩⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Basis.ofZlatticeBasis_span ℝ (unitLattice K)]⟩, h₂⟩

theorem torsion_unitSMul_mem_of_mem {x : E K} (hx : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  by_cases hx' : x = 0
  · refine Set.mem_union_right _ ?_
    rw [hx', smul_zero, Set.mem_singleton_iff]
  · refine Set.mem_union_left _ ⟨?_, ?_⟩
    · rw [Set.mem_preimage, logMap_torsion_unitSMul _ hζ]
      exact (hx.resolve_right hx').1
    · simpa using (hx.resolve_right hx').2

theorem unitSMul_mem_iff_mem_torsion {x : E K} (hx : x ≠ 0) -- (hx : mixedEmbedding.norm x ≠ 0)
    (hx' : x ∈ fundamentalCone K) (u : (𝓞 K)ˣ) :
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
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, ← logMap_unitSMul _ (hx'.resolve_right hx).2]
      refine (h.resolve_right ?_).1
      rw [Set.mem_singleton_iff, unitSMul_eq_zero]
      exact hx
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
      exact (hx'.resolve_right hx).1
  · exact torsion_unitSMul_mem_of_mem hx' h

variable (K) in
/-- The set of images by `mixedEmbedding` of algebraic integers of `K` contained in the
fundamental cone. -/
def integralPoint : Set (E K) := (fundamentalCone K) ∩ (mixedEmbedding K '' (𝓞 K))

theorem exists_unique_preimage_of_integralPoint {x : E K} (hx : x ∈ integralPoint K) :
    ∃! a : (𝓞 K), mixedEmbedding K a = x := by
  refine ⟨⟨hx.2.choose, hx.2.choose_spec.1⟩, hx.2.choose_spec.2, fun x h ↦ ?_⟩
  rw [Subtype.ext_iff, ← (mixedEmbedding_injective K).eq_iff, h, hx.2.choose_spec.2]

/-- For `a : fundamentalCone K`, the unique algebraic integer which image by `mixedEmbedding` is
equal to `a`. -/
def preimageOfIntegralPoint (a : integralPoint K) : (𝓞 K) :=
  ⟨a.prop.2.choose, a.prop.2.choose_spec.1⟩

@[simp]
theorem image_preimageOfIntegralPoint (a : integralPoint K) :
    mixedEmbedding K (preimageOfIntegralPoint a) = a := a.prop.2.choose_spec.2

theorem preimageOfIntegralPoint_mixedEmbedding {x : 𝓞 K}
    (hx : mixedEmbedding K x ∈ integralPoint K) :
    preimageOfIntegralPoint (⟨mixedEmbedding K x, hx⟩) = x := by
  rw [Subtype.ext_iff, ← (mixedEmbedding_injective K).eq_iff, image_preimageOfIntegralPoint]

theorem exists_unitSMul_mem_integralPoint {x : E K} (hx : x ∈ mixedEmbedding K '' (𝓞 K)) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ integralPoint K := by
  by_cases hx' : x = 0
  · simp_rw [hx', smul_zero]
    exact ⟨1, fundamentalCone.zero_mem _, ⟨0, zero_mem _, map_zero _⟩⟩
  · replace hx' : mixedEmbedding.norm x ≠ 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx)).not.mpr hx'
    obtain ⟨u, hu⟩ := exists_unitSMul_mem hx'
    obtain ⟨x, ⟨hx₁, ⟨_, rfl⟩⟩⟩ := hx
    refine ⟨u, hu, ?_⟩
    rw [unitSMul_smul, ← map_mul]
    exact ⟨u * x,  mul_mem (SetLike.coe_mem (u : 𝓞 K)) hx₁, rfl⟩

theorem torsion_unitSMul_mem_integralPoint {x : E K} {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
    (hx : x ∈ integralPoint K) :
    ζ • x ∈ integralPoint K := by
  obtain ⟨a, ha, rfl⟩ := hx.2
  refine ⟨torsion_unitSMul_mem_of_mem hx.1 hζ, ⟨ζ * a, ?_, ?_⟩⟩
  · exact mul_mem (SetLike.coe_mem (ζ : (𝓞 K))) ha
  · rw [unitSMul_smul, map_mul]

variable (K) in
/-- The map that sends an element of `a : fundamentalCone K` to the associates class
of its preimage in `(𝓞 K)`. By quotienting by the kernel of the map, which is equal to the group of
roots of unity, we get the equivalence `integralPointQuotEquivAssociates`. -/
def integralPointToAssociates (a : integralPoint K) : Associates (𝓞 K) :=
  ⟦preimageOfIntegralPoint a⟧

@[simp]
theorem integralPointToAssociates_apply (a : integralPoint K) :
    integralPointToAssociates K a = ⟦preimageOfIntegralPoint a⟧ := rfl

variable (K) in
theorem integralPointToAssociates_surjective :
    Function.Surjective (integralPointToAssociates K) := by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, u • (mixedEmbedding K x) ∈ integralPoint K :=
      exists_unitSMul_mem_integralPoint ⟨x, SetLike.coe_mem x, rfl⟩
  refine ⟨⟨u • (mixedEmbedding K x), hu⟩, ?_⟩
  refine Quotient.sound ⟨u⁻¹, ?_⟩
  simp_rw [unitSMul_smul, ← map_mul, ← Submonoid.coe_mul]
  rw [preimageOfIntegralPoint_mixedEmbedding, mul_comm, Units.inv_mul_cancel_left]

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
  rw [integralPointToAssociates_apply, integralPointToAssociates_apply]
  rw [show ⟦preimageOfIntegralPoint a⟧ = ⟦preimageOfIntegralPoint b⟧ ↔
    ∃ u : (𝓞 K)ˣ, preimageOfIntegralPoint a * u = preimageOfIntegralPoint b by
    rw [Associates.mk_eq_mk_iff_associated, Associated]]
  simp_rw [mul_comm, ← unitSMul_eq_iff_mul_eq, image_preimageOfIntegralPoint, Subtype.ext_iff,
    integralPoint_torsionSMul_smul_coe]
  refine ⟨fun ⟨u, h⟩ ↦ ?_, fun ⟨⟨ζ, _⟩, h⟩ ↦ ⟨ζ, h⟩⟩
  by_cases ha : (a : E K) = 0
  · simp_rw [ha, smul_zero] at h ⊢
    exact ⟨1, h⟩
  · refine ⟨⟨u, (unitSMul_mem_iff_mem_torsion ha a.prop.1 u).mp ?_⟩, h⟩
    rw [h]
    exact b.prop.1

variable (K) in
/-- The equivalence between `fundamentalCone.integralPoint K / torsion K` and `Associates K`. By
composing with the equivalence between `Associates K` and the principal ideals of `𝓞 K`, we get the
equivalence `integralPointQuotEquivIsPrincipal`. -/
def integralPointQuotEquivAssociates :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) ≃ Associates (𝓞 K) := by
  refine Equiv.ofBijective (Quotient.lift (integralPointToAssociates K)
    fun _ _ h ↦ ((integralPointToAssociates_eq_iff _ _).mpr h).symm)
    ⟨?_, (Quot.surjective_lift _).mpr (integralPointToAssociates_surjective K)⟩
  convert Setoid.ker_lift_injective (integralPointToAssociates K)
  all_goals
  · ext a b
    rw [Setoid.ker_def, eq_comm, integralPointToAssociates_eq_iff b a,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

@[simp]
theorem integralPointQuotEquivAssociates_apply (a : integralPoint K) :
    integralPointQuotEquivAssociates K ⟦a⟧ = ⟦preimageOfIntegralPoint a⟧ := rfl

/-- the norm of `a : integralPoint K` as a natural integer. -/
def intNorm (a : integralPoint K) : ℕ := (Algebra.norm ℤ (preimageOfIntegralPoint a)).natAbs

@[simp]
theorem intNorm_coe (a : integralPoint K) :
    (intNorm a : ℝ) = mixedEmbedding.norm (a : E K) := by
  rw [intNorm, Int.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, Algebra.coe_norm_int,
    ← norm_eq_norm, image_preimageOfIntegralPoint]

/-- The norm `intNorm` defined on `fundamentalCone.integralPoint K` lifts to a function
on the classes of `fundamentalCone.integralPoint K` modulo `torsion K`. -/
def quotIntNorm :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) → ℕ := by
  refine Quotient.lift (fun x ↦ intNorm x) fun a b ⟨u, hu⟩ ↦ ?_
  rw [← Nat.cast_inj (R := ℝ), intNorm_coe, intNorm_coe, ← hu, integralPoint_torsionSMul_smul_coe,
    norm_unitSMul]

@[simp]
theorem quotIntNorm_apply (a : integralPoint K) : quotIntNorm ⟦a⟧ = intNorm a := rfl

theorem quotIntNorm_eq_zero_iff (q : Quotient (MulAction.orbitRel (torsion K) (integralPoint K))) :
    quotIntNorm q = 0 ↔ Quotient.out' q = (0 : E K) := by
  convert_to quotIntNorm ⟦Quotient.out' q⟧ = 0 ↔ Quotient.out' q = (0 : E K)
  · rw [← @Quotient.mk''_eq_mk, Quotient.out_eq']
  · rw [quotIntNorm_apply, intNorm, Int.natAbs_eq_zero, Algebra.norm_eq_zero_iff,
      ← image_preimageOfIntegralPoint, map_eq_zero, ZeroMemClass.coe_eq_zero]

-- Absorb this?
variable (K) in
/-- The equivalence between `fundamentalCone.integralPoint K / torsion K` and the principal
ideals of `𝓞 K`. -/
def integralPointQuotEquivIsPrincipal :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) ≃
      {I : Ideal (𝓞 K) // Submodule.IsPrincipal I} :=
  (integralPointQuotEquivAssociates K).trans (Ideal.associatesEquivIsPrincipal (𝓞 K))

theorem integralPointQuotEquivIsPrincipal_apply (a : integralPoint K) :
    integralPointQuotEquivIsPrincipal K ⟦a⟧ = Ideal.span {preimageOfIntegralPoint a} := by
  rw [integralPointQuotEquivIsPrincipal, Equiv.trans_apply,
    integralPointQuotEquivAssociates_apply, Ideal.associatesEquivIsPrincipal_apply]

theorem integralPoint_torsionSMul_stabilizer_eq_bot {a : integralPoint K} (ha : (a : E K) ≠ 0) :
    MulAction.stabilizer (torsion K) a = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ ↦ ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integralPoint_torsionSMul_smul_coe,
    unitSMul_smul, ← image_preimageOfIntegralPoint, ← map_mul, (mixedEmbedding_injective K).eq_iff,
    mul_eq_right₀, OneMemClass.coe_eq_one, Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  contrapose! ha
  rw [← image_preimageOfIntegralPoint, ha, map_zero]

theorem integralPoint_torsionSMul_stabilizer_eq_top {a : integralPoint K} (ha : (a : E K) = 0) :
    MulAction.stabilizer (torsion K) a = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro ζ
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integralPoint_torsionSMul_smul_coe, ha,
    smul_zero]

-- Change name
variable (K) in
def idealStab (I : Ideal (𝓞 K)) : Subgroup (torsion K) := if I = ⊥ then ⊥ else ⊤

variable (K) in
theorem toto1 : integralPoint K ≃
    (I : {I : Ideal (𝓞 K) // Submodule.IsPrincipal I}) × (idealStab K I) := by
  let e := MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integralPoint K)
  refine Equiv.trans e ?_
  refine Equiv.sigmaCongr (integralPointQuotEquivIsPrincipal K) ?_
  intro q
  by_cases hq : Quotient.out' q = (0 : E K)
  · rw [integralPoint_torsionSMul_stabilizer_eq_top hq]
    rw [show q = ⟦Quotient.out' q⟧ by sorry]
    rw [integralPointQuotEquivIsPrincipal_apply, idealStab, if_pos]
    have := QuotientGroup.subsingleton_quotient_top (G := torsion K)
    exact equivOfSubsingletonOfSubsingleton (fun _ ↦ 1) (fun _ ↦ 1)
    sorry
  · rw [integralPoint_torsionSMul_stabilizer_eq_bot hq]
    rw [show q = ⟦Quotient.out' q⟧ by sorry]
    rw [integralPointQuotEquivIsPrincipal_apply, idealStab, if_neg]
    exact QuotientGroup.quotientBot.toEquiv.trans Subgroup.topEquiv.toEquiv.symm
    sorry

@[simp]
theorem toto1_apply_fst (a : integralPoint K) :
    (toto1 K a).fst = Ideal.span {preimageOfIntegralPoint a} := by
  rw [← integralPointQuotEquivIsPrincipal_apply]
  unfold toto1
  rfl



open Submodule

variable (K) in
theorem toto2 {n : ℕ} (hn : 0 < n) :
    {a : integralPoint K // intNorm a = n} ≃
      {I : Ideal (𝓞 K) // IsPrincipal I ∧ Ideal.absNorm I = n} × (torsion K) := by
  -- refine Equiv.trans ?_ (Equiv.sigmaEquivProd _ _)
  let g := Equiv.subtypeEquiv (p := fun a ↦ intNorm a = n)
--    (q := fun σ ↦ ?_)
    (q := fun σ : (I : { I : Ideal (𝓞 K) // IsPrincipal I }) × (idealStab K I) ↦ Ideal.absNorm σ.1.val = n)
    (toto1 K) ?_
  · refine Equiv.trans g ?_
    let h := Equiv.subtypeSigmaEquiv
      (fun I : { I : Ideal (𝓞 K) // IsPrincipal I } ↦ (idealStab K I))
      (fun I ↦ Ideal.absNorm I.val = n)
    refine Equiv.trans h ?_
    refine Equiv.trans (Equiv.sigmaEquivProdOfEquiv (β := torsion K) ?_) ?_
    · rintro ⟨I, hI⟩
      rw [idealStab, if_neg]
      exact Subgroup.topEquiv.toEquiv
      rw [← Ideal.absNorm_eq_zero_iff, hI]
      linarith
    refine Equiv.prodCongrLeft fun _ ↦ ?_
    let h := Equiv.subtypeSubtypeEquivSubtypeInter (fun I : Ideal (𝓞 K) ↦ IsPrincipal I)
      (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I = n)
    exact h
  · intro a
    dsimp
    rw [toto1_apply_fst, Ideal.absNorm_span_singleton, intNorm]

theorem toto2_apply_fst {n : ℕ} (hn : 0 < n) (a : integralPoint K) (ha : intNorm a = n) :
    (toto2 K hn ⟨a, ha⟩).fst = Ideal.span {preimageOfIntegralPoint a} := by
  unfold toto2
  simp only [MulEquiv.toEquiv_eq_coe, eq_mpr_eq_cast, cast_eq, Equiv.trans_apply,
    Equiv.subtypeEquiv_apply]
  dsimp
  simp_rw [← toto1_apply_fst]
  rfl


#exit


  refine Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  refine Equiv.subtypeEquiv (integralPointQuotEquivIsPrincipal K) ?_
  sorry









-- variable (K) in
-- /-- The norm `mixedEmbedding.norm` defined on `fundamentalCone.integralPoint K` lifts to a function
-- on the classes of `fundamentalCone.integralPoint K` modulo `torsion K`. -/
-- def integralPointQuotNorm :
--     Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) → ℕ := by
--   refine Quotient.lift (fun x ↦ intNorm x) fun a b ⟨u, hu⟩ ↦ ?_
--   sorry
-- --  simp_rw [← hu, integralPoint_torsionSMul_smul_coe, norm_unitSMul]

-- theorem integralPointQuotNorm_apply (a : integralPoint K) :
--     integralPointQuotNorm K ⟦a⟧ = mixedEmbedding.norm (a : E K) := sorry --  rfl

-- theorem integralPointQuotNorm_eq_norm (a : integralPoint K) :
--     integralPointQuotNorm K ⟦a⟧ = |Algebra.norm ℤ (preimageOfIntegralPoint a)| := by
--   sorry
-- --  rw [integralPointQuotNorm_apply, ← image_preimageOfIntegralPoint, norm_eq_norm,
-- --    ← Algebra.coe_norm_int, Rat.cast_abs, Rat.cast_intCast, Int.cast_abs]

-- theorem integralPointQuotNorm_eq_zero_iff
--     (q : Quotient (MulAction.orbitRel (torsion K) (integralPoint K))) :
--     integralPointQuotNorm K q = 0 ↔ Quotient.out' q = (0 : E K) := by
--   sorry
--  convert_to integralPointQuotNorm K ⟦Quotient.out' q⟧ = 0 ↔ Quotient.out' q = (0 : E K)
--  · rw [← @Quotient.mk''_eq_mk, Quotient.out_eq']
--  · rw [integralPointQuotNorm_apply, norm_eq_zero_iff' (by
--      rw [← image_preimageOfIntegralPoint]
--      exact Set.mem_range_self _)]

open Ideal Submodule

variable (K)

/-- The equivalence between classes in `fundamentalCone.integralPoint K / torsion K` of norm `n`
and the principal ideals of `𝓞 K` of norm `n`. -/
def integralPointQuotNormEquivIsPrincipal (n : ℕ) :
    { x // integralPointQuotNorm K x = n } ≃
      { I : Ideal (𝓞 K) // IsPrincipal I ∧ absNorm I = n } := by
  refine Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  refine Equiv.subtypeEquiv (integralPointQuotEquivIsPrincipal K) ?_
  rintro ⟨a⟩
  sorry
--  rw [show Quot.mk _ a = ⟦a⟧ by rfl, integralPointQuotEquivIsPrincipal_apply,
--    integralPointQuotNorm_eq_norm, absNorm_span_singleton, Int.abs_eq_natAbs, Int.cast_natCast,
--    Nat.cast_inj]

/-- For `n` positive, the number of principal ideals in `𝓞 K` of norm `n` multiplied by the number
of roots of unity in `K` is equal to the number of `fundamentalCone.integralPoint K` of
norm `n`. -/
theorem card_isPrincipal_norm_eq {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I = n} * torsionOrder K =
        Nat.card ({a : integralPoint K | intNorm a = n}) := by
  rw [Set.coe_setOf, Set.coe_setOf, ← Nat.card_congr (integralPointQuotNormEquivIsPrincipal K n),
    torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  refine Nat.card_congr (Equiv.symm ?_)
  refine (Equiv.subtypeEquiv (q := fun s ↦ integralPointQuotNorm K s.fst = n)
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integralPoint K))
      fun _ ↦ ?_).trans  ?_
  · simp only [MulAction.selfEquivSigmaOrbitsQuotientStabilizer,
      MulAction.selfEquivSigmaOrbitsQuotientStabilizer', MulAction.selfEquivSigmaOrbits',
      Quotient.mk'_eq_mk, Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.trans_apply,
      Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_symm_apply_fst, Equiv.Set.ofEq_apply,
      integralPointQuotNorm_apply]
    sorry
  · refine (@Equiv.subtypeSigmaEquiv _ _ (fun q ↦ integralPointQuotNorm K q = n)).trans
      (Equiv.sigmaEquivProdOfEquiv fun ⟨_, h⟩ ↦ ?_)
    rw [integralPoint_torsionSMul_stabilizer]
    exact QuotientGroup.quotientBot.toEquiv
    sorry
    -- rw [ne_eq, ← integralPointQuotNorm_eq_zero_iff, h, Nat.cast_eq_zero, ← ne_eq]
    -- linarith

instance (n : ℕ) : Fintype {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I = n} := by
  refine Set.Finite.fintype ?_
  by_cases hn : n = 0
  · simp_rw [hn, Ideal.absNorm_eq_zero_iff]
    refine Set.Finite.subset (Set.finite_singleton ⊥) (by simp)
  · exact Set.Finite.subset (Ideal.finite_setOf_absNorm_eq (Nat.pos_of_ne_zero hn)) (by simp)

instance (n : ℕ) : Fintype {a : integralPoint K | intNorm a = n} := by
  refine Set.Finite.fintype ?_
  by_cases hn : n = 0
  · sorry
  ·
    sorry

theorem card_isPrincipal_norm_le {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ∈ Finset.Icc 1 n} * torsionOrder K =
        Nat.card ({a : integralPoint K | intNorm a ∈ Finset.Icc 1 n}) := by
  have : Fintype {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ∈ Finset.Icc 1 n} := sorry
  have : Fintype {a : integralPoint K | intNorm a ∈ Finset.Icc 1 n} := sorry

  have t₁ := @Finset.card_eq_sum_card_fiberwise (Ideal (𝓞 K)) ℕ _ (fun I ↦ absNorm I)
    {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I ∈ Finset.Icc 1 n}.toFinset
    (Finset.Icc 1 n) ?_

  rw [Nat.card_eq_fintype_card]
  rw [← Set.toFinset_card, t₁, Finset.sum_mul]

  have t₂ := @Finset.card_eq_sum_card_fiberwise (integralPoint K) ℕ _ (fun a ↦ intNorm a)
    {a : integralPoint K | intNorm a ∈ Finset.Icc 1 n}.toFinset (Finset.Icc 1 n) ?_

  · rw [Nat.card_eq_fintype_card]
    rw [← Set.toFinset_card, t₂]

    refine Finset.sum_congr rfl fun i hi ↦ ?_
    convert card_isPrincipal_norm_eq K (Finset.mem_Icc.mp hi).1
    · rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
      congr
      ext I
      rw [Finset.mem_filter, Set.mem_toFinset, Set.mem_toFinset, Set.mem_setOf_eq, Set.mem_setOf_eq,
        and_assoc, and_iff_right_of_imp (?_ : absNorm I = i → absNorm I ∈ Finset.Icc 1 n)]
      intro h
      rwa [← h] at hi
    · rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
      congr
      ext a
      rw [Finset.mem_filter, Set.mem_toFinset, Set.mem_toFinset, Set.mem_setOf_eq, Set.mem_setOf_eq,
        and_iff_right_of_imp]
      intro h
      rwa [← h] at hi
  · intro x hx
    convert (Set.mem_toFinset.mp hx)
  · intro x hx
    convert (Set.mem_toFinset.mp hx).2

#exit

  have t₁ := @Finset.card_eq_sum_card_fiberwise
    {I : Ideal (𝓞 K) // IsPrincipal I ∧ absNorm I ∈ Finset.Icc 1 n} ℕ
    _ (fun I ↦ absNorm I.1) Finset.univ (Finset.Icc 1 n) ?_
  have t₂ := @Finset.card_eq_sum_card_fiberwise
    {a : integralPoint K // intNorm a ∈ Finset.Icc 1 n} ℕ _ (fun a ↦ intNorm a.1) Finset.univ (Finset.Icc 1 n) ?_

  rw [t₁, t₂, Finset.sum_mul]

  refine Finset.sum_congr rfl fun n hn ↦ ?_
  · convert card_isPrincipal_norm_eq K (by sorry : 1 ≤ n)
    erw [← Finset.card_subtype, @Nat.card_eq_fintype_card _ (inst1 n), Fintype.card]






#exit

  rw [Set.coe_setOf, Set.coe_setOf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card, t₁, Fintype.card, t₂, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have := card_isPrincipal_norm_eq K (n := n) ?_
  convert this
  · rw [Set.coe_setOf, Nat.card_eq_fintype_card, ← Finset.card_subtype]




#exit

  have : ∀ n, Fintype { I : Ideal (𝓞 K) // IsPrincipal I ∧ absNorm I = n} := sorry
  have : ∀ n, Fintype { x : integralPoint K // mixedEmbedding.norm (x : E K) = n } := sorry
  have := Finset.sum_congr (α := Set.Icc 1 n) (s₁ := Finset.univ) rfl
    (fun n _ ↦ card_isPrincipal_norm_eq K n.prop.1)
  simp_rw [Set.coe_setOf, Nat.card_eq_fintype_card] at this
  rw? at this
#exit

  rw [show {I : Ideal (𝓞 K) | IsPrincipal I ∧ 1 ≤ absNorm I ∧ absNorm I ≤ n } =
    (⋃ i ∈ Set.Icc 1 n, {I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I = i}) by ext; simp]
  rw [show {a :integralPoint K | mixedEmbedding.norm (a : E K) ≤ n } =
    (⋃ i ∈ Set.Icc 1 n, {a : integralPoint K | mixedEmbedding.norm (a : E K) = i}) by sorry] --ext; simp]
  rw [torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]


#exit
  have h := card_isPrincipal_norm_eq K hn
  have : Fintype { I : Ideal (𝓞 K) // IsPrincipal I ∧ (1 ≤ absNorm I ∧ absNorm I ≤ n)} := sorry
  have : Fintype { x : integralPoint K // mixedEmbedding.norm (x : E K) ≤ n } := sorry
  rw [Set.coe_setOf, Set.coe_setOf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card, Fintype.card, Finset.univ.card_eq_sum_card_image
    (fun x : integralPoint K ↦ mixedEmbedding.norm (x : E K))]
  -- rw [torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  rw [show {I : Ideal (𝓞 K) | IsPrincipal I ∧ 1 ≤ absNorm I ∧ absNorm I ≤ n } =
    (⋃ i ∈ Set.Icc 1 n, { I : Ideal (𝓞 K) | IsPrincipal I ∧ absNorm I = i}) by ext; simp]


  -- exact Set.Finite.biUnion (Set.finite_Icc _ _) (fun n hn => Ideal.finite_setOf_absNorm_eq hn.1)
  sorry

end fundamentalCone

end
