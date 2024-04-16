import Mathlib.NumberTheory.NumberField.Units
import Mathlib.Covolume
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section Ideal

def Ideal.equivIsPrincipal (R : Type*) [CommRing R] [IsDomain R] :
    Quotient (MulAction.orbitRel Rˣ R) ≃ {I : Ideal R | Submodule.IsPrincipal I} := by
  have h_main : ∀ ⦃x : R⦄, ∀ ⦃y:R⦄,
      y ∈ MulAction.orbit Rˣ x ↔ Ideal.span {x} = Ideal.span {y} := fun x y ↦ by
    simp_rw [Ideal.span_singleton_eq_span_singleton, MulAction.orbit, Set.mem_range, Associated,
    mul_comm x _]
    rfl
  refine Equiv.ofBijective ?_ ⟨?_, fun ⟨I, hI⟩ ↦ ?_⟩
  · exact _root_.Quotient.lift (fun x ↦ ⟨Ideal.span {x}, ⟨x, rfl⟩⟩)
      fun _ _ h ↦ Subtype.mk_eq_mk.mpr (h_main.mp h).symm
  · rintro ⟨_⟩ ⟨_⟩ h
    exact Quotient.sound <| h_main.mpr ((Subtype.mk_eq_mk.mp h).symm)
  · obtain ⟨x, hx⟩ := hI
    exact ⟨⟦x⟧, Subtype.mk_eq_mk.mpr hx.symm⟩

theorem Ideal.equivIsPrincipal_apply (R : Type*) [CommRing R] [IsDomain R] (x : R) :
    Ideal.equivIsPrincipal R ⟦x⟧ = Ideal.span {x} := rfl

theorem Ideal.equivIsPrincipal_symm_apply (R : Type*) [CommRing R] [IsDomain R] {I : Ideal R}
    (hI : Submodule.IsPrincipal I) :
    (Ideal.equivIsPrincipal R).symm ⟨I, hI⟩ = ⟦hI.generator⟧ := by
  rw [Equiv.symm_apply_eq, Subtype.ext_iff, Ideal.equivIsPrincipal_apply, span_singleton_generator]

end Ideal

variable {K : Type*} [Field K] [NumberField K]

open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem FiniteDimensional

open scoped BigOperators Classical

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

section Embedding  -- Move this to `Embeddings`

theorem NumberField.InfinitePlace.norm_embedding_eq_of_isReal {K : Type*} [Field K]
    {w : NumberField.InfinitePlace K} (hw : NumberField.InfinitePlace.IsReal w) (x : K) :
    ‖embedding_of_isReal hw x‖ = w x := by
  rw [← norm_embedding_eq, ← embedding_of_isReal_apply hw, Complex.norm_real]

end Embedding

noncomputable section Basic -- Move this to `CanonicalEmbedding.Basic`

namespace NumberField

def mixedEmbedding.norm : (E K) →*₀ ℝ where
  toFun := fun x ↦ (∏ w, ‖x.1 w‖) * ∏ w, ‖x.2 w‖ ^ 2
  map_one' := by simp only [Prod.fst_one, Pi.one_apply, norm_one, Finset.prod_const_one,
    Prod.snd_one, one_pow, mul_one]
  map_zero' := by
    simp_rw [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, norm_zero, zero_pow (two_ne_zero),
      mul_eq_zero, Finset.prod_const, pow_eq_zero_iff', true_and, Finset.card_univ]
    by_contra!
    have : finrank ℚ K = 0 := by
      rw [← card_add_two_mul_card_eq_rank, NrRealPlaces, NrComplexPlaces, this.1, this.2]
    exact ne_of_gt finrank_pos this
  map_mul' _ _ := by simp only [Prod.fst_mul, Pi.mul_apply, norm_mul, Real.norm_eq_abs,
      Finset.prod_mul_distrib, Prod.snd_mul, Complex.norm_eq_abs, mul_pow]; ring

theorem mixedEmbedding.norm_ne_zero_iff {x : E K} :
    norm x ≠ 0 ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ w, x.2 w ≠ 0) := by
  simp_rw [norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_true_left, pow_ne_zero_iff two_ne_zero, _root_.norm_ne_zero_iff]

theorem mixedEmbedding.norm_const (c : ℝ) :
    norm ((fun _ ↦ c, fun _ ↦ c) : (E K)) = |c| ^ finrank ℚ K := by
  simp_rw [norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Real.norm_eq_abs, Complex.norm_eq_abs,
    Complex.abs_ofReal, Finset.prod_const, ← pow_mul, ← card_add_two_mul_card_eq_rank,
    Finset.card_univ, pow_add]

theorem mixedEmbedding.norm_smul (c : ℝ) (x : E K) :
    norm (c • x) = |c| ^ finrank ℚ K * (norm x) := by
  rw [show c • x = ((fun _ ↦ c, fun _ ↦ c) : (E K)) * x by rfl, map_mul, norm_const]

@[simp]
theorem mixedEmbedding.norm_eq_norm (x : K) :
    norm (mixedEmbedding K x) = |Algebra.norm ℚ x| := by
  simp_rw [← prod_eq_abs_norm, mixedEmbedding.norm, mixedEmbedding, RingHom.prod_apply,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Pi.ringHom_apply, norm_embedding_eq,
    norm_embedding_eq_of_isReal]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K ↦ IsReal w)]
  congr 1
  · exact Finset.prod_congr rfl (fun w _ ↦ by rw [mult, if_pos w.prop, pow_one])
  · refine (Fintype.prod_equiv (Equiv.subtypeEquivRight ?_) _ _ (fun w ↦ ?_)).symm
    · exact fun _ ↦ not_isReal_iff_isComplex
    · rw [Equiv.subtypeEquivRight_apply_coe, mult, if_neg w.prop]

theorem mixedEmbedding.norm_ne_zero {x : E K}
    (hx : x ∈ Set.range (mixedEmbedding K)) (hx' : x ≠ 0) : norm x ≠ 0 := by
  obtain ⟨a, rfl⟩ := hx
  rw [norm_eq_norm, Rat.cast_abs, ne_eq, abs_eq_zero, Rat.cast_eq_zero, Algebra.norm_eq_zero_iff]
  contrapose! hx'
  rw [hx', map_zero]

theorem mixedEmbedding.norm_unit (u : (𝓞 K)ˣ) :
    norm (mixedEmbedding K u) = 1 := by
  rw [norm_eq_norm, show |(Algebra.norm ℚ) (u : K)| = 1
      by exact NumberField.isUnit_iff_norm.mp (Units.isUnit u), Rat.cast_one]

end NumberField

end Basic

noncomputable section UnitSMul

@[simps]
instance NumberField.mixedEmbedding.unitSMul : SMul (𝓞 K)ˣ (E K) where
  smul := fun u x ↦ (mixedEmbedding K u) * x

instance : MulAction (𝓞 K)ˣ (E K) where
  one_smul := fun _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, Units.coe_mul, map_mul, mul_assoc]

instance : SMulZeroClass (𝓞 K)ˣ (E K) where
  smul_zero := fun _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, mul_zero]

instance : SMul (𝓞 K) (𝓞 K) := Algebra.toSMul

theorem NumberField.mixedEmbedding.unitSMul_iff_smul {x y : (𝓞 K)} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u • x = y := by
  rw [unitSMul_smul, ← map_mul, Units.smul_def, smul_eq_mul, Function.Injective.eq_iff,
    ←  Submonoid.coe_mul, Subtype.mk_eq_mk]
  exact mixedEmbedding_injective K

@[simp]
theorem  NumberField.mixedEmbedding.norm_unitSMul (u : (𝓞 K)ˣ) (x : E K) :
    norm (u • x) = norm x := by
  rw [unitSMul_smul, map_mul, norm_eq_norm, show |(Algebra.norm ℚ) (u : K)| = 1
      by exact NumberField.isUnit_iff_norm.mp (Units.isUnit u), Rat.cast_one, one_mul]

end UnitSMul

namespace NumberField.mixedEmbedding

noncomputable section logMap

open NumberField.Units

def logMap (x : E K) : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  fun w ↦
    if hw : IsReal w.val then
      Real.log ‖x.1 ⟨w.val, hw⟩‖ - Real.log (norm x) * (finrank ℚ K : ℝ)⁻¹
    else
      2 * (Real.log ‖x.2 ⟨w.val, not_isReal_iff_isComplex.mp hw⟩‖ -
        Real.log (norm x) * (finrank ℚ K : ℝ)⁻¹)

theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
    logMap (mixedEmbedding K u) = logEmbedding K u := by
  ext
  simp_rw [logMap, norm_unit, Real.log_one, zero_mul, sub_zero, logEmbedding, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, mult, Nat.cast_ite, ite_mul, Nat.cast_one, one_mul, Nat.cast_ofNat,
    mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply, norm_embedding_eq,
    norm_embedding_eq_of_isReal]
  rfl

theorem logMap_zero : logMap (0 : E K) = 0 := by
  ext
  simp_rw [logMap, Prod.fst_zero, Prod.snd_zero, map_zero, Pi.zero_apply, norm_zero, Real.log_zero,
    zero_mul, sub_zero, mul_zero, dite_eq_ite, ite_self]

theorem logMap_torsion_unitSMul_eq (x : E K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    logMap (ζ • x) = logMap x := by
  ext
  simp_rw [logMap, unitSMul_smul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, map_mul,
    norm_eq_norm, mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply,
    show |(Algebra.norm ℚ) (ζ : K)| = 1 by exact NumberField.isUnit_iff_norm.mp (Units.isUnit ζ),
    Rat.cast_one, one_mul, norm_embedding_eq, norm_embedding_eq_of_isReal, (mem_torsion K).mp hζ,
    one_mul]

theorem logMap_mul {x y : E K} (hx : norm x ≠ 0) (hy : norm y ≠ 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap]
  split_ifs with hw
  · rw [Prod.fst_mul, Pi.mul_apply, norm_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
    · ring
    · exact _root_.norm_ne_zero_iff.mpr <| (norm_ne_zero_iff.mp hx).1 ⟨_, hw⟩
    · exact _root_.norm_ne_zero_iff.mpr <| (norm_ne_zero_iff.mp hy).1 ⟨_, hw⟩
  · replace hw := not_isReal_iff_isComplex.mp hw
    rw [Prod.snd_mul, Pi.mul_apply, norm_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
    · ring
    · exact _root_.norm_ne_zero_iff.mpr <| (norm_ne_zero_iff.mp hx).2 ⟨_, hw⟩
    · exact _root_.norm_ne_zero_iff.mpr <| (norm_ne_zero_iff.mp hy).2 ⟨_, hw⟩

theorem logMap_unitSMul_eq (u : (𝓞 K)ˣ) {x : E K} (hx : norm x ≠ 0) :
    logMap (u • x) = logEmbedding K u + logMap x := by
  rw [unitSMul_smul, logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

theorem logMap_smul_eq {x : E K} {c : ℝ} (hx : norm x ≠ 0) (hc : c ≠ 0) :
    logMap (c • x) = logMap x := by
  rw [show c • x = ((fun _ ↦ c, fun _ ↦ c) : (E K)) * x by rfl, logMap_mul _ hx, add_left_eq_self]
  ext
  have hr : (finrank ℚ K : ℝ) ≠ 0 :=  Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
  simp_rw [logMap, Pi.zero_apply, norm_const, Real.log_pow, mul_comm, inv_mul_cancel_left₀ hr,
    Real.norm_eq_abs, Complex.norm_eq_abs,  Complex.abs_ofReal, sub_self, mul_zero, dite_eq_ite,
    ite_self]
  rw [norm_const]
  exact pow_ne_zero _ (abs_ne_zero.mpr hc)

end logMap

noncomputable section fundamentalCone

open NumberField.Units

variable (K)

def fundamentalCone : Set (E K) := by
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
  exact logMap⁻¹' (Zspan.fundamentalDomain B)

namespace fundamentalCone

protected theorem zero_mem : 0 ∈ fundamentalCone K := by
  simp_rw [fundamentalCone, Set.mem_preimage, Zspan.mem_fundamentalDomain, logMap_zero, map_zero,
    Finsupp.coe_zero, Pi.zero_apply, Set.left_mem_Ico, zero_lt_one, implies_true]

variable {K}

theorem smul_mem_of_mem {x : E K} (hx : norm x ≠ 0) (hx' : x ∈ fundamentalCone K)
    (c : ℝ) : c • x ∈ fundamentalCone K := by
  by_cases hc : c = 0
  · rw [hc, zero_smul]
    exact fundamentalCone.zero_mem K
  · rwa [fundamentalCone, Set.mem_preimage, logMap_smul_eq hx hc]

theorem exists_unitSMul_mem {x : E K} (hx : norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ fundamentalCone K := by
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : ∃ e : unitLattice K, e + logMap x ∈ Zspan.fundamentalDomain B
  · exact ⟨u, by rwa [fundamentalCone, Set.mem_preimage, logMap_unitSMul_eq u hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Basis.ofZlatticeBasis_span ℝ (unitLattice K)]⟩, h₂⟩

theorem torsion_unitSMul_mem_of_mem {x : E K}
    (hx' : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  rwa [fundamentalCone, Set.mem_preimage, logMap_torsion_unitSMul_eq _ hζ]

theorem unitSMul_mem_iff {x : E K} (hx : norm x ≠ 0) (hx' : x ∈ fundamentalCone K) (u : (𝓞 K)ˣ) :
    u • x ∈ fundamentalCone K ↔ u ∈ torsion K := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← logEmbedding_eq_zero_iff]
    let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
    refine (Subtype.mk_eq_mk (h := ?_) (h' := ?_)).mp <|
      ExistsUnique.unique (Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)) ?_ ?_
    · change logEmbedding K u ∈ (Submodule.span ℤ (Set.range B)).toAddSubgroup
      rw [Basis.ofZlatticeBasis_span ℝ (unitLattice K)]
      exact ⟨u, trivial, rfl⟩
    · exact Submodule.zero_mem _
    · rwa [fundamentalCone, Set.mem_preimage, logMap_unitSMul_eq _ hx] at h
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
      rwa [fundamentalCone, Set.mem_preimage] at hx'
  · exact torsion_unitSMul_mem_of_mem hx' h

variable (K) in
def integralPoints : Set (E K) := (fundamentalCone K) ∩ (mixedEmbedding K '' (𝓞 K))

theorem exists_unitSMul_mem_integralPoints {x : E K} (hx : x ∈ mixedEmbedding K '' (𝓞 K)) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ integralPoints K := by
  by_cases hx' : x = 0
  · simp_rw [hx', smul_zero]
    exact ⟨1, fundamentalCone.zero_mem _, ⟨0, zero_mem _, map_zero _⟩⟩
  · replace hx' : norm x ≠ 0 :=
      norm_ne_zero (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx) hx'
    obtain ⟨u, hu⟩ := exists_unitSMul_mem hx'
    obtain ⟨x, ⟨hx₁, ⟨_, rfl⟩⟩⟩ := hx
    refine ⟨u, hu, ?_⟩
    rw [unitSMul_smul, ← map_mul]
    exact ⟨u * x,  mul_mem (SetLike.coe_mem (u : 𝓞 K)) hx₁, rfl⟩

theorem exists_unique_preimage_of_integralPoint {x : E K} (hx : x ∈ integralPoints K) :
    ∃! a : (𝓞 K), mixedEmbedding K a = x := by
  refine ⟨⟨hx.2.choose, hx.2.choose_spec.1⟩, hx.2.choose_spec.2, fun x h ↦ ?_⟩
  rw [Subtype.ext_iff, ← (mixedEmbedding_injective K).eq_iff, h, hx.2.choose_spec.2]

def preimageOfIntegralPoints (a : integralPoints K) : (𝓞 K) :=
  ⟨a.prop.2.choose, a.prop.2.choose_spec.1⟩

theorem image_preimageOfIntegralPoints_eq (a : integralPoints K) :
    mixedEmbedding K (preimageOfIntegralPoints a) = a := a.prop.2.choose_spec.2

theorem torsion_unitSMul_mem_integralPoints {x : E K} {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
    (hx : x ∈ integralPoints K) :
    ζ • x ∈ integralPoints K := by
  obtain ⟨a, ha, rfl⟩ := hx.2
  refine ⟨torsion_unitSMul_mem_of_mem hx.1 hζ, ⟨ζ * a, ?_, ?_⟩⟩
  · exact mul_mem (SetLike.coe_mem (ζ : (𝓞 K))) ha
  · rw [unitSMul_smul, map_mul]

@[simps]
instance integralPoints_torsionSMul: SMul (torsion K) (integralPoints K) where
  smul := fun ⟨ζ, hζ⟩ ⟨x, hx⟩ ↦ ⟨ζ • x,  torsion_unitSMul_mem_integralPoints hζ hx⟩

instance : MulAction (torsion K) (integralPoints K) where
  one_smul := fun _ ↦ by
    rw [Subtype.mk_eq_mk, integralPoints_torsionSMul_smul_coe, OneMemClass.coe_one, one_smul]
  mul_smul := fun _ _ _ ↦ by
    rw [Subtype.mk_eq_mk]
    simp_rw [integralPoints_torsionSMul_smul_coe, Submonoid.coe_mul, mul_smul]

-- We need to remind Lean of this instance to avoid a timeout
instance : MulAction (𝓞 K) (𝓞 K) := MulActionWithZero.toMulAction

variable (K) in
def integralPointsToModUnits (a : integralPoints K) :
    Quotient (MulAction.orbitRel (𝓞 K)ˣ (𝓞 K)) := Quotient.mk _ (preimageOfIntegralPoints a)

theorem integralPointsToModUnits_apply (a : integralPoints K) :
  (integralPointsToModUnits K a) = ⟦preimageOfIntegralPoints a⟧ := rfl

variable (K) in
theorem integralPointsToModUnits_surjective :
    Function.Surjective (integralPointsToModUnits K) := by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, u • (mixedEmbedding K x) ∈ integralPoints K  :=
      exists_unitSMul_mem_integralPoints ⟨x, SetLike.coe_mem x, rfl⟩
  refine ⟨⟨u • (mixedEmbedding K x), hu⟩, Quotient.sound ⟨u, ?_⟩⟩
  rw [← unitSMul_iff_smul, image_preimageOfIntegralPoints_eq]

-- We need to remind Lean of this instance to avoid a timeout
instance : MulAction (𝓞 K) (𝓞 K) := MulActionWithZero.toMulAction

theorem integralPointsToModUnits_eq_iff (a b : integralPoints K) :
    integralPointsToModUnits K a = integralPointsToModUnits K b ↔
      ∃ ζ : torsion K, ζ • b = a := by
  rw [integralPointsToModUnits_apply, integralPointsToModUnits_apply]
  rw [show ⟦preimageOfIntegralPoints a⟧ = ⟦preimageOfIntegralPoints b⟧ ↔
    ∃ u : (𝓞 K)ˣ, u • preimageOfIntegralPoints b = preimageOfIntegralPoints a by
    rw [@Quotient.eq]; rfl]
  simp_rw [← unitSMul_iff_smul, image_preimageOfIntegralPoints_eq, Subtype.ext_iff,
    integralPoints_torsionSMul_smul_coe]
  refine ⟨fun ⟨u, h⟩ ↦ ?_, fun ⟨⟨ζ, _⟩, h⟩ ↦ ⟨ζ, h⟩⟩
  by_cases hb : (b : E K) = 0
  · rw [hb, smul_zero] at h
    exact ⟨1, by rw [hb, ← h, OneMemClass.coe_one, smul_zero]⟩
  · have hnz : norm (b : E K) ≠ 0 :=
      mixedEmbedding.norm_ne_zero ⟨b.prop.2.choose, b.prop.2.choose_spec.2⟩ hb
    refine ⟨⟨u, (unitSMul_mem_iff hnz b.prop.1 u).mp ?_⟩, h⟩
    rw [h]
    exact a.prop.1

variable (K) in
def integralPointsQuoEquivModUnits :
    Quotient (MulAction.orbitRel (torsion K) (integralPoints K)) ≃
      Quotient (MulAction.orbitRel (𝓞 K)ˣ (𝓞 K)) := by
  refine Equiv.ofBijective (Quotient.lift (integralPointsToModUnits K) ?_) ⟨?_, ?_⟩
  · exact fun a b ↦ (integralPointsToModUnits_eq_iff a b).mpr
  · convert Setoid.ker_lift_injective (integralPointsToModUnits K)
    all_goals
    · ext a b
      exact (integralPointsToModUnits_eq_iff a b).symm
  · rw [Quot.surjective_lift]
    exact integralPointsToModUnits_surjective K

variable (K) in
def integralPointsQuoEquivIsPrincipal :
    Quotient (MulAction.orbitRel (torsion K) (integralPoints K)) ≃
      {I : Ideal (𝓞 K) // Submodule.IsPrincipal I} :=
  (integralPointsQuoEquivModUnits K).trans (Ideal.equivIsPrincipal (𝓞 K))

theorem integralPointsQuoEquivIsPrincipal_apply (a : integralPoints K) :
    integralPointsQuoEquivIsPrincipal K ⟦a⟧ =
      Ideal.span {preimageOfIntegralPoints a} := by
  rw [integralPointsQuoEquivIsPrincipal, Equiv.trans_apply]
  erw [Ideal.equivIsPrincipal_apply]

def integralPointsQuoNorm :
    Quotient (MulAction.orbitRel (torsion K) (integralPoints K)) → ℝ := by
  refine Quotient.lift ?_ ?_
  · exact fun x ↦ norm (x : E K)
  · intro a b ⟨⟨u, _⟩, hu⟩
    rw [Subtype.ext_iff, integralPoints_torsionSMul_smul_coe] at hu
    rw [← hu]
    exact norm_unitSMul u b

theorem integralPointsQuoNorm_apply (a : integralPoints K) :
    integralPointsQuoNorm ⟦a⟧ = |Algebra.norm ℤ (preimageOfIntegralPoints a)| := by
  rw [integralPointsQuoNorm, @Quotient.lift_mk, ← image_preimageOfIntegralPoints_eq,
    norm_eq_norm, ← Algebra.coe_norm_int, Rat.cast_abs, Rat.cast_intCast, Int.cast_abs]

def integralPointsQuoOrbitEquiv {q : Quotient (MulAction.orbitRel (torsion K) (integralPoints K))}
    (hq : integralPointsQuoNorm q ≠ 0) :
    (MulAction.orbitRel.Quotient.orbit q) ≃ (torsion K) := by
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq', MulAction.orbit]
  refine (Equiv.ofInjective _ fun _ _ h ↦ ?_).symm
  suffices (preimageOfIntegralPoints (Quotient.out' q) : K) ≠ 0 by
    simp_rw [Subtype.ext_iff, integralPoints_torsionSMul_smul_coe, unitSMul_smul,
      ← image_preimageOfIntegralPoints_eq, ← map_mul, (mixedEmbedding_injective K).eq_iff] at h
    exact_mod_cast (mul_left_inj' this).mp h
  contrapose! hq
  rw [show q = ⟦Quotient.out' q⟧ from (Quotient.out_eq' q).symm, integralPointsQuoNorm_apply,
    Int.cast_abs, abs_eq_zero, Int.cast_eq_zero, Algebra.norm_eq_zero_iff]
  exact_mod_cast hq

variable (K) in
def integralPointsQuoNormEquivIsPrincipal (n : ℕ) :
    { x : Quotient (MulAction.orbitRel (torsion K) (integralPoints K)) //
      integralPointsQuoNorm x = n } ≃
      { I : Ideal (𝓞 K) // Submodule.IsPrincipal I ∧ Ideal.absNorm I = n } := by
  refine Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  refine Equiv.subtypeEquiv (integralPointsQuoEquivIsPrincipal K) ?_
  rintro ⟨_⟩
  erw [integralPointsQuoEquivIsPrincipal_apply, integralPointsQuoNorm_apply]
  rw [Ideal.absNorm_span_singleton, Int.abs_eq_natAbs, Int.cast_natCast, Nat.cast_inj]

variable (K) in
def integralPointsQuoNormProdEquiv {n : ℕ} (hn : 1 ≤ n) :
    { x // integralPointsQuoNorm (K := K) x = n } × (torsion K) ≃
        { a : integralPoints K // norm (a : E K) = n } := by
  let f : { a : integralPoints K // norm (a : E K) = n } →
      { x // integralPointsQuoNorm (K := K) x = n } := by
    rintro ⟨a, ha⟩
    refine ⟨⟦a⟧, by rw [← ha]; rfl⟩
  let e := Equiv.sigmaFiberEquiv (α := { a : integralPoints K // norm (a : E K) = n })
    (β := { x // integralPointsQuoNorm (K := K) x = n }) f
  refine Equiv.trans ?_ e
  refine (Equiv.sigmaEquivProdOfEquiv ?_).symm
  rintro ⟨q, hq⟩
  have hq' : integralPointsQuoNorm q ≠ 0 := by
    rw [hq]
    rw [Nat.cast_ne_zero]
    linarith
  refine Equiv.trans ?_ (integralPointsQuoOrbitEquiv hq')
  simp_rw [Subtype.ext_iff]
  refine Equiv.trans (Equiv.subtypeEquivRight fun _ ↦
    MulAction.orbitRel.Quotient.mem_orbit.symm) ?_
  refine Equiv.subtypeSubtypeEquivSubtype (q := fun x ↦ x ∈ MulAction.orbitRel.Quotient.orbit q) ?_
  rintro a ha
  rw [← hq, integralPointsQuoNorm]
  rw [MulAction.orbitRel.Quotient.mem_orbit] at ha
  rw [← ha]
  simp_rw [Quotient.mk''_eq_mk]
  simp_rw [Quotient.lift_mk]

theorem main {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {I : Ideal (𝓞 K) // Submodule.IsPrincipal I ∧ Ideal.absNorm I = n} *
      Fintype.card (torsion K) = Nat.card ({a : integralPoints K // norm (a : E K) = n}) := by
  rw [← Nat.card_congr (integralPointsQuoNormEquivIsPrincipal K n)]
  rw [← Nat.card_eq_fintype_card, ← Nat.card_prod]
  refine Nat.card_congr ?_
  exact integralPointsQuoNormProdEquiv K hn

end fundamentalCone

section InnerProductSpace

open scoped Classical

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K` as an Euclidean space. -/
local notation "E'" K =>
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsReal w})))

example : (E' K) ≃L[ℝ] (E K) := by
  refine ContinuousLinearEquiv.prod ?_ ?_
  exact EuclideanSpace.equiv _ ℝ
  

end InnerProductSpace

#exit

open Filter Topology MeasureTheory Submodule

example :
  Tendsto (fun s : ℝ ↦
      Nat.card {I : Ideal (𝓞 K) // Submodule.IsPrincipal I ∧ Ideal.absNorm I = s} / s)
      atTop (𝓝 ((volume {x ∈ fundamentalCone K | norm x ≤ 1}).toReal /
        Zlattice.covolume (span ℤ (Set.range (latticeBasis K))).toAddSubgroup)) := by
  letI : InnerProductSpace ℝ (E K) := by
    refine InnerProductSpace.ofNorm ℝ ?_
    sorry
  have : IsZlattice ℝ (toAddSubgroup (span ℤ (Set.range ⇑(latticeBasis K)))) := sorry
  have := cone₂ (span ℤ (Set.range (latticeBasis K))).toAddSubgroup
    (X := fundamentalCone K) (F := fun x ↦ norm x) ?_ ?_ ?_ ?_
  convert this using 3
  sorry
