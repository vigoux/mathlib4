import Mathlib --.Topology.ContinuousFunction.Ideals
import Mathlib.AANUCFC.QuasiSpectrum

section IdealInstances


instance (priority := 10000) Ideal.instMulMemClass {R : Type*} [Semiring R] :
    MulMemClass (Ideal R) R where
  mul_mem _ := Ideal.mul_mem_left _ _

--instance Ideal.instMul {R : Type*} [Semiring R] (I : Ideal R) :
    --Mul I where
  --mul x y := ⟨x * y, I.mul_mem_left x y.property⟩

instance Ideal.instNonUnitalSemiring {R : Type*} [Semiring R] (I : Ideal R) :
    NonUnitalSemiring I where
  left_distrib _ _ _ := Subtype.ext <| mul_add ..
  right_distrib _ _ _ := Subtype.ext <| add_mul ..
  zero_mul _ := Subtype.ext <| zero_mul _
  mul_zero _ := Subtype.ext <| mul_zero _
  mul_assoc _ _ _ := Subtype.ext <| mul_assoc ..

instance Ideal.instNonUnitalRing {R : Type*} [Ring R] (I : Ideal R) :
    NonUnitalRing I where
  left_distrib _ _ _ := Subtype.ext <| mul_add ..
  right_distrib _ _ _ := Subtype.ext <| add_mul ..
  zero_mul _ := Subtype.ext <| zero_mul _
  mul_zero _ := Subtype.ext <| mul_zero _
  mul_assoc _ _ _ := Subtype.ext <| mul_assoc ..

instance Ideal.instNonUnitalCommSemiring {R : Type*} [CommSemiring R] (I : Ideal R) :
    NonUnitalCommSemiring I where
  mul_comm x y := Subtype.ext <| mul_comm (x : R) (y : R)

instance Ideal.instNonUnitalCommRing {R : Type*} [CommRing R] (I : Ideal R) :
    NonUnitalCommRing I where
  mul_comm x y := Subtype.ext <| mul_comm (x : R) (y : R)

instance Ideal.instTopologicalSemiring {R : Type*} [Semiring R] [TopologicalSpace R]
    [TopologicalSemiring R] (I : Ideal R) : TopologicalSemiring I where
  continuous_mul := by -- `continuity` gets this, slowly, but `fun_prop` fails
    apply Continuous.subtype_mk
    exact continuous_induced_dom.comp' continuous_fst |>.mul <|
      continuous_induced_dom.comp' continuous_snd

instance Ideal.instTopologicalRing {R : Type*} [Ring R] [TopologicalSpace R]
    [TopologicalRing R] (I : Ideal R) : TopologicalRing I :=
  { }

end IdealInstances

structure ContinuousMapZero (X R : Type*) [Zero X] [Zero R] [TopologicalSpace X]
    [TopologicalSpace R] extends C(X, R) where
  map_zero' : toContinuousMap 0 = 0

namespace ContinuousMapZero

scoped notation "C(" X ", " R ")₀" => ContinuousMapZero X R

section Basic

variable {X Y R : Type*} [Zero X] [Zero Y] [Zero R]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]

instance instFunLike : FunLike C(X, R)₀ X R where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance instContinuousMapClass : ContinuousMapClass C(X, R)₀ X R where
  map_continuous f := f.continuous

instance instZeroHomClass : ZeroHomClass C(X, R)₀ X R where
  map_zero f := f.map_zero'

@[ext]
lemma ext {f g : C(X, R)₀} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[simp]
lemma coe_mk {f : C(X, R)} {h0 : f 0 = 0} : ⇑(mk f h0) = f := rfl

def comp (g : C(Y, R)₀) (f : C(X, Y)₀) : C(X, R)₀ where
  toContinuousMap := g.toContinuousMap.comp f.toContinuousMap
  map_zero' := show g (f 0) = 0 from map_zero f ▸ map_zero g

@[simp]
lemma comp_apply (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X) : g.comp f x = g (f x) := rfl

end Basic

section Semiring

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

instance instZero : Zero C(X, R)₀ where
  zero := ⟨0, rfl⟩

instance instAdd : Add C(X, R)₀ where
  add f g := ⟨f + g, by simp⟩

instance instMul : Mul C(X, R)₀ where
  mul f g := ⟨f * g, by simp⟩

instance instSMul {M : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R] :
    SMul M C(X, R)₀ where
  smul m f := ⟨m • f, by simp⟩

lemma toContinuousMap_injective :
    Function.Injective (toContinuousMap (X := X) (R := R)) :=
  fun f g h ↦ by refine congr(.mk $(h) ?_); exacts [f.map_zero', g.map_zero']

instance instNonUnitalCommSemiring : NonUnitalCommSemiring C(X, R)₀ :=
  (toContinuousMap_injective (X := X) (R := R)).nonUnitalCommSemiring
    _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instModule {M : Type*} [Semiring M] [Module M R] [ContinuousConstSMul M R] :
    Module M C(X, R)₀ :=
  (toContinuousMap_injective (X := X) (R := R)).module M
    { toFun := _, map_add' := fun _ _ ↦ rfl, map_zero' := rfl } (fun _ _ ↦ rfl)

instance instSMulCommClass {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMulCommClass M N R] :
    SMulCommClass M N C(X, R)₀ where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..

instance instIsScalarTower {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMul M N] [IsScalarTower M N R] :
    IsScalarTower M N C(X, R)₀ where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc ..

instance instStarRing [StarRing R] [ContinuousStar R] : StarRing C(X, R)₀ where
  star f := ⟨star f, by simp⟩
  star_involutive _ := ext fun _ ↦ star_star _
  star_mul _ _ := ext fun _ ↦ star_mul ..
  star_add _ _ := ext fun _ ↦ star_add ..

instance instTopologicalSpace : TopologicalSpace C(X, R)₀ :=
  TopologicalSpace.induced toContinuousMap inferInstance

end Semiring

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [CommRing R] [TopologicalSpace R] [TopologicalRing R]
section Ring

instance instSub : Sub C(X, R)₀ where
  sub f g := ⟨f - g, by simp⟩

instance instNeg : Neg C(X, R)₀ where
  neg f := ⟨-f, by simp⟩

instance instNonUnitalCommRing : NonUnitalCommRing C(X, R)₀ :=
  (toContinuousMap_injective (X := X) (R := R)).nonUnitalCommRing _ rfl
  (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Ring

end ContinuousMapZero

/-
section Notation

variable {X Y R : Type*} [Zero X] [TopologicalSpace X] [Zero Y] [TopologicalSpace Y]
variable [Semifield R] [TopologicalSpace R] [TopologicalSemiring R]

@[simps]
def ContinuousMap.evalRingHom {X : Type*} (R : Type*) [TopologicalSpace X] [TopologicalSpace R]
    [Semiring R] [TopologicalSemiring R] (x : X) : C(X, R) →+* R where
  toFun f := f x
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl


-- scoped[ContinuousMap] notation3 "C(" X ", " R ")₀" => idealOfSet R {(0 : X)}ᶜ
scoped[ContinuousMap] notation3 "C(" X ", " R ")₀" => RingHom.ker (ContinuousMap.evalRingHom R (0 : X))

set_option profiler true in
instance {X R : Type*} [TopologicalSpace X] [CommSemiring R] [TopologicalSpace R] [StarRing R]
    [ContinuousStar R] [TopologicalSemiring R] (x : X) :
    StarRing (RingHom.ker (ContinuousMap.evalRingHom R (x : X))) where
  star := sorry
  star_involutive f := sorry
  star_mul f g := sorry
  star_add f g := sorry
  --star f := ⟨star f.val, by rw [RingHom.mem_ker]; sorry⟩ --
    --Subtype.map (star (R := C(X, R))) fun y hy ↦ by
    --rw [RingHom.mem_ker (ContinuousMap.evalRingHom R (x : X))] at hy ⊢
    --simpa only [star_zero] using congr(star $(hy))

  #exit
  star_involutive f := Subtype.ext <| star_star (f : C(X, R))
  star_mul f g := Subtype.ext <| star_mul (f : C(X, R)) g
  star_add f g := Subtype.ext <| star_add (f : C(X, R)) g

#exit
open ContinuousMap

instance {X R : Type*} [TopologicalSpace X] [CommSemiring R] [TopologicalSpace R] [StarRing R]
    [ContinuousStar R] [TopologicalSemiring R] (s : Set X) : StarRing (idealOfSet R s) where
  star := Subtype.map (star (R := C(X, R))) <| by simp [mem_idealOfSet]
  star_involutive f := Subtype.ext <| star_star (f : C(X, R))
  star_mul f g := Subtype.ext <| star_mul (f : C(X, R)) g
  star_add f g := Subtype.ext <| star_add (f : C(X, R)) g

lemma ContinuousMap.mem_zeroAtZero_iff (f : C(X, R)) : f ∈ C(X, R)₀ ↔ f 0 = 0 := by simp

lemma ContinuousMap.zeroAtZero_map_zero (f : C(X, R)₀) : f.val 0 = 0 :=
  f.val.mem_zeroAtZero_iff.mp f.property

def ContinuousMap.comp_zeroAtZero (g : C(Y, R)₀) (f : C(X, Y)) (h0 : f 0 = 0) : C(X, R)₀ :=
  ⟨g.val.comp f, by simp [h0, ContinuousMap.zeroAtZero_map_zero g]⟩

end Notation
-/

local notation "σₙ" => quasiSpectrum

open scoped ContinuousMapZero

class NonUnitalContinuousFunctionalCalculus (R : Type*) {A : Type*} (p : outParam (A → Prop))
    [Semifield R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
    [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Prop where
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A,
    ClosedEmbedding φ ∧ φ ⟨(ContinuousMap.id R).restrict <| σₙ R a, rfl⟩ = a ∧
      (∀ f, σₙ R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

-- we really don't actually want a separate class for this, but for now we'll use this hack to
-- write the rest of the file.
class UniqueNonUnitalContinuousFunctionalCalculus (R A : Type*) [Semifield R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  eq_of_continuous_of_map_id (a : A) (φ ψ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ ⟨.restrict (σₙ R a) <| .id R, rfl⟩ = ψ ⟨.restrict (σₙ R a) <| .id R, rfl⟩) :
    φ = ψ

variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
variable [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R p]

lemma NonUnitalStarAlgHom.ext_continuousMap [UniqueNonUnitalContinuousFunctionalCalculus R A]
    (a : A) (φ ψ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ ⟨.restrict (σₙ R a) <| .id R, rfl⟩ = ψ ⟨.restrict (σₙ R a) <| .id R, rfl⟩) :
    φ = ψ :=
  UniqueNonUnitalContinuousFunctionalCalculus.eq_of_continuous_of_map_id a φ ψ hφ hψ h

section cfcₙHom

variable {a : A} (ha : p a)

noncomputable def cfcₙHom : C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

lemma cfcₙHom_closedEmbedding :
    ClosedEmbedding <| (cfcₙHom ha : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1

lemma cfcₙHom_id :
    cfcₙHom ha ⟨(ContinuousMap.id R).restrict <| σₙ R a, by simp⟩ = a :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1

/-- The **spectral mapping theorem** for the continuous functional calculus. -/
lemma cfcₙHom_map_quasiSpectrum (f : C(σₙ R a, R)₀) :
    σₙ R (cfcₙHom ha f) = Set.range f :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1 f

lemma cfcₙHom_predicate (f : C(σₙ R a, R)₀) :
    p (cfcₙHom ha f) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2 f

lemma cfcₙHom_eq_of_continuous_of_map_id [UniqueNonUnitalContinuousFunctionalCalculus R A]
    (φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) (hφ₁ : Continuous φ)
    (hφ₂ : φ ⟨.restrict (σₙ R a) <| .id R, by simp⟩ = a) : cfcₙHom ha = φ :=
  (cfcₙHom ha).ext_continuousMap a φ (cfcₙHom_closedEmbedding ha).continuous hφ₁ <| by
    rw [cfcₙHom_id ha, hφ₂]

theorem cfcₙHom_comp [UniqueNonUnitalContinuousFunctionalCalculus R A] (f : C(σₙ R a, R)₀)
    (f' : C(σₙ R a, σₙ R (cfcₙHom ha f))₀)
    (hff' : ∀ x, f x = f' x) (g : C(σₙ R (cfcₙHom ha f), R)₀) :
    cfcₙHom ha (g.comp f') = cfcₙHom (cfcₙHom_predicate ha f) g := by
  let ψ : C(σₙ R (cfcₙHom ha f), R)₀ →⋆ₙₐ[R] C(σₙ R a, R)₀ :=
    { toFun := (ContinuousMapZero.comp · f')
      map_smul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_star' := fun _ ↦ rfl }
  let φ : C(σₙ R (cfcₙHom ha f), R)₀ →⋆ₙₐ[R] A := (cfcₙHom ha).comp ψ
  suffices cfcₙHom (cfcₙHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcₙHom_eq_of_continuous_of_map_id (cfcₙHom_predicate ha f) φ ?_ ?_
  · refine (cfcₙHom_closedEmbedding ha).continuous.comp ?_ --f'.continuous_comp_left
    apply continuous_induced_rng.mpr
    exact f'.toContinuousMap.continuous_comp_left.comp continuous_induced_dom
  · simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk]
    congr
    ext x
    simp [hff']

end cfcₙHom


section CFCn

open Classical in
/-- This is the (non-unital) *continuous functional calculus* of an element `a : A` applied to bare
functions.  When either `a` does not satisfy the predicate `p` (i.e., `a` is not `IsStarNormal`,
`IsSelfAdjoint`, or `0 ≤ a` when `R` is `ℂ`, `ℝ`, or `ℝ≥0`, respectively), or when `f : R → R` is
not continuous on the σₙ of `a` or `f 0 ≠ 0`, then `cfc a f` returns the junk value `0`.

This is the primary declaration intended for widespread use of the (non-unital) continuous
functional calculus, and all the API applies to this declaration. For more information, see the
module documentation for `Topology.ContinuousFunction.FunctionalCalculus`. -/
noncomputable irreducible_def cfcₙ (a : A) (f : R → R) : A :=
  if h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
    then cfcₙHom h.1 ⟨⟨_, h.2.1.restrict⟩, h.2.2⟩
    else 0

variable (a : A)


/-- A tactic used to automatically discharge goals relating to the continuous functional calculus,
specifically concerning whether `f 0 = 0`. -/
syntax (name := cfcZeroTac) "cfc_zero_tac" : tactic
macro_rules
  | `(tactic| cfc_zero_tac) => `(tactic| try (first | aesop | assumption))

lemma cfcₙ_apply (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a f = cfcₙHom (a := a) ha ⟨⟨_, hf.restrict⟩, h0⟩ := by
  rw [cfcₙ_def, dif_pos ⟨ha, hf, h0⟩]

lemma cfcₙ_apply_of_not_and_and {f : R → R} (ha : ¬ (p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0)) :
    cfcₙ a f = 0 := by
  rw [cfcₙ_def, dif_neg ha]

lemma cfcₙ_apply_of_not_predicate {f : R → R} (ha : ¬ p a) :
    cfcₙ a f = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_left _ ha)]

lemma cfcₙ_apply_of_not_continuousOn {f : R → R} (hf : ¬ ContinuousOn f (σₙ R a)) :
    cfcₙ a f = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_left _ hf))]

lemma cfcₙ_apply_of_not_map_zero {f : R → R} (hf : ¬ f 0 = 0) :
    cfcₙ a f = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_right _ hf))]

variable (R) in
lemma cfcₙ_id (ha : p a := by cfc_tac) : cfcₙ a (id : R → R) = a :=
  cfcₙ_apply a (id : R → R) ▸ cfcₙHom_id (p := p) ha

variable (R) in
lemma cfcₙ_id' (ha : p a := by cfc_tac) : cfcₙ a (fun x : R ↦ x) = a :=
  cfcₙ_id R a

/-- The **spectral mapping theorem** for the continuous functional calculus. -/
lemma cfc_map_quasiSpectrum (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (h0 : f 0 = 0 := by cfc_zero_tac) :
    σₙ R (cfcₙ a f) = f '' σₙ R a := by
  simp [cfcₙ_apply a f, cfcₙHom_map_quasiSpectrum (p := p)]

lemma cfcₙ_predicate (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (h0 : f 0 = 0 := by cfc_zero_tac) :
    p (cfcₙ a f) :=
  cfcₙ_apply a f ▸ cfcₙHom_predicate (A := A) ha _

lemma cfcₙ_congr {f g : R → R} (hfg : (σₙ R a).EqOn f g) :
    cfcₙ a f = cfcₙ a g := by
  by_cases h : p a ∧ ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · rw [cfcₙ_apply a f h.1 (h.2.1.congr hfg) (hfg (quasiSpectrum.zero_mem R a) ▸ h.2.2),
      cfcₙ_apply a g h.1 h.2.1 h.2.2]
    congr
    exact Set.restrict_eq_iff.mpr hfg
  · simp only [not_and_or] at h
    obtain (ha | hg | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hg, cfcₙ_apply_of_not_continuousOn]
      exact fun hf ↦ hg (hf.congr hfg.symm)
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero]
      exact fun hf ↦ h0 (hfg (quasiSpectrum.zero_mem R a) ▸ hf)

lemma eqOn_of_cfcₙ_eq_cfcₙ {f g : R → R} (h : cfcₙ a f = cfcₙ a g) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    (σₙ R a).EqOn f g := by
  rw [cfcₙ_apply a f, cfcₙ_apply a g] at h
  have := (cfcₙHom_closedEmbedding (show p a from ha) (R := R)).inj h
  intro x hx
  congrm($(this) ⟨x, hx⟩)

lemma cfcₙ_eq_cfcₙ_iff_eqOn {f g : R → R} (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ a f = cfcₙ a g ↔ (σₙ R a).EqOn f g :=
  ⟨eqOn_of_cfcₙ_eq_cfcₙ a, cfcₙ_congr a⟩

variable (R)

@[simp]
lemma cfcₙ_zero : cfcₙ a (0 : R → R) = 0 := by
  by_cases ha : p a
  · exact cfcₙ_apply a (0 : R → R) ▸ map_zero (cfcₙHom ha)
  · rw [cfcₙ_apply_of_not_predicate a ha]

@[simp]
lemma cfcₙ_const_zero : cfcₙ a (fun _ : R ↦ 0) = 0 :=
  cfcₙ_zero R a

variable {R}

lemma cfcₙ_mul (f g : R → R)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (fun x ↦ f x * g x) = cfcₙ a f * cfcₙ a g := by
  by_cases ha : p a
  · rw [cfcₙ_apply a f, cfcₙ_apply a g, ← map_mul, cfcₙ_apply a _]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

-- :sad: no `ppow` yet
--lemma cfcₙ_pow (f : R → R) (n : ℕ) (ha : p a := by cfc_tac)
    --(hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (h0 : f 0 = 0 := by cfc_zero_tac) :
    --cfcₙ a (fun x ↦ (f x) ^ n) = cfcₙ a f ^ n := by
  --rw [cfcₙ_apply a f, ← map_pow, cfcₙ_apply a _]
  --congr

lemma cfcₙ_add (f g : R → R)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (fun x ↦ f x + g x) = cfcₙ a f + cfcₙ a g := by
  by_cases ha : p a
  · rw [cfcₙ_apply a f, cfcₙ_apply a g, cfcₙ_apply a _]
    simp_rw [← map_add]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (fun x ↦ s • f x) = s • cfcₙ a f := by
  by_cases ha : p a
  · rw [cfcₙ_apply a f, cfcₙ_apply a _]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_const_mul (r : R) (f : R → R) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (fun x ↦ r * f x) = r • cfcₙ a f :=
  cfcₙ_smul a r f

lemma cfcₙ_star (f : R → R) : cfcₙ a (fun x ↦ star (f x)) = star (cfcₙ a f) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply a f, ← map_star, cfcₙ_apply a _]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, star_zero]
      exact fun hf_star ↦ hf <| by simpa using hf_star.star
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, star_zero]
      exact fun hf0 ↦ h0 <| by simpa using congr(star $(hf0))

-- :sad: no `ppow`
--lemma cfcₙ_pow_id (n : ℕ) (ha : p a := by cfc_tac) : cfcₙ a (· ^ n : R → R) = a ^ n := by
  --rw [cfcₙ_pow a _, cfcₙ_id' R a]

lemma cfcₙ_smul_id {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (ha : p a := by cfc_tac) : cfcₙ a (s • · : R → R) = s • a := by
  rw [cfcₙ_smul a s _, cfcₙ_id' R a]

lemma cfcₙ_const_mul_id (r : R) (ha : p a := by cfc_tac) : cfcₙ a (r * ·) = r • a :=
  cfcₙ_smul_id a r

lemma cfcₙ_star_id (ha : p a := by cfc_tac) : cfcₙ a (star · : R → R) = star a := by
  rw [cfcₙ_star a _, cfcₙ_id' R a]
