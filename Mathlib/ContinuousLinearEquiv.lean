import Mathlib.Topology.Algebra.Module.Basic

namespace ContinuousLinearEquiv

variable (R : Type*) {S M M₂ : Type*} [Semiring R] [Semiring S]
    [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module R M₂] [Module S M] [Module S M₂] [LinearMap.CompatibleSMul M M₂ R S]

variable {R} in
protected theorem congr_arg {x x'} {f : M ≃L[S] M₂} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

variable {R} in
protected theorem congr_fun {f f' : M ≃L[S] M₂} (h : f = f') (x : M) : f x = f' x :=
  DFunLike.congr_fun h x

@[ext]
theorem ext'  {f f' : M ≃L[S] M₂} (h : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ h

/-- If `M` and `M₂` are both `R`-topological semimodules and `S`-semimodules and
`R`-semimodule structures are defined by an action of `R` on `S` (formally, we have two scalar
towers), then any continuous `S`-linear equivalence from `M` to `M₂` is also a continuous
`R`-linear equivalence.

See also `LinearEquiv.restrictScalars`. -/
@[simps!]
def restrictScalars (f : M ≃L[S] M₂) :
    M ≃L[R] M₂ :=
  { f.toLinearEquiv.restrictScalars R with
    continuous_toFun := f.continuous
    continuous_invFun := f.symm.continuous }

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M ≃L[S] M₂) → (M ≃L[R] M₂)) := fun _ _ h ↦
  ext' (ContinuousLinearEquiv.congr_fun h : _)

@[simp]
theorem restrictScalars_inj (f g : M ≃L[S] M₂) :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff
