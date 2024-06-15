/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Order.GroupWithZero.WithZero

#align_import ring_theory.dedekind_domain.finite_adele_ring from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# The finite adèle ring of a Dedekind domain
We define the ring of finite adèles of a Dedekind domain `R`.

## Main definitions
- `DedekindDomain.FiniteIntegralAdeles` : product of `adicCompletionIntegers`, where `v`
  runs over all maximal ideals of `R`.
- `DedekindDomain.ProdAdicCompletions` : the product of `adicCompletion`, where `v` runs over
  all maximal ideals of `R`.
- `DedekindDomain.finiteAdeleRing` : The finite adèle ring of `R`, defined as the
  restricted product `Π'_v K_v`. We give this ring a `K`-algebra structure.

## Implementation notes
We are only interested on Dedekind domains of Krull dimension 1 (i.e., not fields). If `R` is a
field, its finite adèle ring is just defined to be the trivial ring.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite adèle ring, dedekind domain
-/


noncomputable section

open Function Set IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace DedekindDomain

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The product of all `adicCompletionIntegers`, where `v` runs over the maximal ideals of `R`. -/
def FiniteIntegralAdeles : Type _ :=
  ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K
-- deriving CommRing, TopologicalSpace, Inhabited
#align dedekind_domain.finite_integral_adeles DedekindDomain.FiniteIntegralAdeles

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5020): added
section DerivedInstances

instance : CommRing (FiniteIntegralAdeles R K) :=
  inferInstanceAs (CommRing (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

instance : TopologicalSpace (FiniteIntegralAdeles R K) :=
  inferInstanceAs (TopologicalSpace (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

instance : TopologicalRing (FiniteIntegralAdeles R K) :=
  inferInstanceAs (TopologicalRing (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

instance : Inhabited (FiniteIntegralAdeles R K) :=
  inferInstanceAs (Inhabited (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

end DerivedInstances

local notation "R_hat" => FiniteIntegralAdeles

/-- The product of all `adicCompletion`, where `v` runs over the maximal ideals of `R`. -/
def ProdAdicCompletions :=
  ∀ v : HeightOneSpectrum R, v.adicCompletion K
-- deriving NonUnitalNonAssocRing, TopologicalSpace, TopologicalRing, CommRing, Inhabited
#align dedekind_domain.prod_adic_completions DedekindDomain.ProdAdicCompletions

section DerivedInstances

instance : NonUnitalNonAssocRing (ProdAdicCompletions R K) :=
  inferInstanceAs (NonUnitalNonAssocRing (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : TopologicalSpace (ProdAdicCompletions R K) :=
  inferInstanceAs (TopologicalSpace (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : TopologicalRing (ProdAdicCompletions R K) :=
  inferInstanceAs (TopologicalRing (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : CommRing (ProdAdicCompletions R K) :=
  inferInstanceAs (CommRing (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : Inhabited (ProdAdicCompletions R K) :=
  inferInstanceAs (Inhabited (∀ v : HeightOneSpectrum R, v.adicCompletion K))

end DerivedInstances

local notation "K_hat" => ProdAdicCompletions

namespace FiniteIntegralAdeles

noncomputable instance : Coe (R_hat R K) (K_hat R K) where coe x v := x v

theorem coe_apply (x : R_hat R K) (v : HeightOneSpectrum R) : (x : K_hat R K) v = ↑(x v) :=
  rfl
#align dedekind_domain.finite_integral_adeles.coe_apply DedekindDomain.FiniteIntegralAdeles.coe_apply

/-- The inclusion of `R_hat` in `K_hat` as a homomorphism of additive monoids. -/
@[simps]
def Coe.addMonoidHom : AddMonoidHom (R_hat R K) (K_hat R K) where
  toFun := (↑)
  map_zero' := rfl
  map_add' x y := by
    -- Porting note: was `ext v`
    refine funext fun v => ?_
    simp only [coe_apply, Pi.add_apply, Subring.coe_add]
    -- Porting note: added
    erw [Pi.add_apply, Pi.add_apply, Subring.coe_add]
#align dedekind_domain.finite_integral_adeles.coe.add_monoid_hom DedekindDomain.FiniteIntegralAdeles.Coe.addMonoidHom

/-- The inclusion of `R_hat` in `K_hat` as a ring homomorphism. -/
@[simps]
def Coe.ringHom : RingHom (R_hat R K) (K_hat R K) :=
  { Coe.addMonoidHom R K with
    toFun := (↑)
    map_one' := rfl
    map_mul' := fun x y => by
      -- Porting note: was `ext p`
      refine funext fun p => ?_
      simp only [Pi.mul_apply, Subring.coe_mul]
      -- Porting note: added
      erw [Pi.mul_apply, Pi.mul_apply, Subring.coe_mul] }
#align dedekind_domain.finite_integral_adeles.coe.ring_hom DedekindDomain.FiniteIntegralAdeles.Coe.ringHom

end FiniteIntegralAdeles

section AlgebraInstances

instance : Algebra K (K_hat R K) :=
  (by infer_instance : Algebra K <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)

@[simp]
lemma ProdAdicCompletions.algebraMap_apply' (k : K) :
    algebraMap K (K_hat R K) k v = (k : v.adicCompletion K) := rfl

instance ProdAdicCompletions.algebra' : Algebra R (K_hat R K) :=
  (by infer_instance : Algebra R <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)
#align dedekind_domain.prod_adic_completions.algebra' DedekindDomain.ProdAdicCompletions.algebra'

@[simp]
lemma ProdAdicCompletions.algebraMap_apply (r : R) :
    algebraMap R (K_hat R K) r v = (algebraMap R K r : v.adicCompletion K) := rfl

instance : IsScalarTower R K (K_hat R K) :=
  (by infer_instance : IsScalarTower R K <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)

instance : Algebra R (R_hat R K) :=
  (by infer_instance : Algebra R <| ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K)

instance ProdAdicCompletions.algebraCompletions : Algebra (R_hat R K) (K_hat R K) :=
  (FiniteIntegralAdeles.Coe.ringHom R K).toAlgebra
#align dedekind_domain.prod_adic_completions.algebra_completions DedekindDomain.ProdAdicCompletions.algebraCompletions

instance ProdAdicCompletions.isScalarTower_completions : IsScalarTower R (R_hat R K) (K_hat R K) :=
  (by infer_instance :
    IsScalarTower R (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) <|
      ∀ v : HeightOneSpectrum R, v.adicCompletion K)
#align dedekind_domain.prod_adic_completions.is_scalar_tower_completions DedekindDomain.ProdAdicCompletions.isScalarTower_completions

end AlgebraInstances

namespace FiniteIntegralAdeles

/-- The inclusion of `R_hat` in `K_hat` as an algebra homomorphism. -/
def Coe.algHom : AlgHom R (R_hat R K) (K_hat R K) :=
  { Coe.ringHom R K with
    toFun := (↑)
    commutes' := fun _ => rfl }
#align dedekind_domain.finite_integral_adeles.coe.alg_hom DedekindDomain.FiniteIntegralAdeles.Coe.algHom

theorem Coe.algHom_apply (x : R_hat R K) (v : HeightOneSpectrum R) : (Coe.algHom R K) x v = x v :=
  rfl
#align dedekind_domain.finite_integral_adeles.coe.alg_hom_apply DedekindDomain.FiniteIntegralAdeles.Coe.algHom_apply

end FiniteIntegralAdeles

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adicCompletion` with respect to `adicCompletionIntegers`. We prove that it is a commutative
ring. TODO: show that it is a topological ring with the restricted product topology. -/


namespace ProdAdicCompletions

variable {R K}

/-- An element `x : K_hat R K` is a finite adèle if for all but finitely many height one ideals
  `v`, the component `x v` is a `v`-adic integer. -/
def IsFiniteAdele (x : K_hat R K) :=
  ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, x v ∈ v.adicCompletionIntegers K
#align dedekind_domain.prod_adic_completions.is_finite_adele DedekindDomain.ProdAdicCompletions.IsFiniteAdele

@[simp]
lemma isFiniteAdele_iff (x : K_hat R K) :
    x.IsFiniteAdele ↔ {v | x v ∉ adicCompletionIntegers K v}.Finite := Iff.rfl

namespace IsFiniteAdele

/-- The sum of two finite adèles is a finite adèle. -/
theorem add {x y : K_hat R K} (hx : x.IsFiniteAdele) (hy : y.IsFiniteAdele) :
    (x + y).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite] at hx hy ⊢
  have h_subset :
    {v : HeightOneSpectrum R | ¬(x + y) v ∈ v.adicCompletionIntegers K} ⊆
      {v : HeightOneSpectrum R | ¬x v ∈ v.adicCompletionIntegers K} ∪
        {v : HeightOneSpectrum R | ¬y v ∈ v.adicCompletionIntegers K} := by
    intro v hv
    rw [mem_union, mem_setOf, mem_setOf]
    rw [mem_setOf] at hv
    contrapose! hv
    rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, ← max_le_iff] at hv
    rw [mem_adicCompletionIntegers, Pi.add_apply]
    exact le_trans (Valued.v.map_add_le_max' (x v) (y v)) hv
  exact (hx.union hy).subset h_subset
#align dedekind_domain.prod_adic_completions.is_finite_adele.add DedekindDomain.ProdAdicCompletions.IsFiniteAdele.add

/-- The tuple `(0)_v` is a finite adèle. -/
theorem zero : (0 : K_hat R K).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  have h_empty :
    {v : HeightOneSpectrum R | ¬(0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ := by
    ext v; rw [mem_empty_iff_false, iff_false_iff]; intro hv
    rw [mem_setOf] at hv; apply hv; rw [mem_adicCompletionIntegers]
    have h_zero : (Valued.v (0 : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = 0 :=
      Valued.v.map_zero'
    rw [h_zero]; exact zero_le_one' _
  -- Porting note: was `exact`, but `OfNat` got in the way.
  convert finite_empty
#align dedekind_domain.prod_adic_completions.is_finite_adele.zero DedekindDomain.ProdAdicCompletions.IsFiniteAdele.zero

/-- The negative of a finite adèle is a finite adèle. -/
theorem neg {x : K_hat R K} (hx : x.IsFiniteAdele) : (-x).IsFiniteAdele := by
  rw [IsFiniteAdele] at hx ⊢
  have h :
    ∀ v : HeightOneSpectrum R,
      -x v ∈ v.adicCompletionIntegers K ↔ x v ∈ v.adicCompletionIntegers K := by
    intro v
    rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, Valuation.map_neg]
  -- Porting note: was `simpa only [Pi.neg_apply, h] using hx` but `Pi.neg_apply` no longer works
  convert hx using 2 with v
  convert h v
#align dedekind_domain.prod_adic_completions.is_finite_adele.neg DedekindDomain.ProdAdicCompletions.IsFiniteAdele.neg

/-- The product of two finite adèles is a finite adèle. -/
theorem mul {x y : K_hat R K} (hx : x.IsFiniteAdele) (hy : y.IsFiniteAdele) :
    (x * y).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite] at hx hy ⊢
  have h_subset :
    {v : HeightOneSpectrum R | ¬(x * y) v ∈ v.adicCompletionIntegers K} ⊆
      {v : HeightOneSpectrum R | ¬x v ∈ v.adicCompletionIntegers K} ∪
        {v : HeightOneSpectrum R | ¬y v ∈ v.adicCompletionIntegers K} := by
    intro v hv
    rw [mem_union, mem_setOf, mem_setOf]
    rw [mem_setOf] at hv
    contrapose! hv
    rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers] at hv
    have h_mul : Valued.v (x v * y v) = Valued.v (x v) * Valued.v (y v) :=
      Valued.v.map_mul' (x v) (y v)
    rw [mem_adicCompletionIntegers, Pi.mul_apply, h_mul]
    exact mul_le_one' hv.left hv.right
  exact (hx.union hy).subset h_subset
#align dedekind_domain.prod_adic_completions.is_finite_adele.mul DedekindDomain.ProdAdicCompletions.IsFiniteAdele.mul

/-- The tuple `(1)_v` is a finite adèle. -/
theorem one : (1 : K_hat R K).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  have h_empty :
    {v : HeightOneSpectrum R | ¬(1 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ := by
    ext v; rw [mem_empty_iff_false, iff_false_iff]; intro hv
    rw [mem_setOf] at hv; apply hv; rw [mem_adicCompletionIntegers]
    exact le_of_eq Valued.v.map_one'
  -- Porting note: was `exact`, but `OfNat` got in the way.
  convert finite_empty
#align dedekind_domain.prod_adic_completions.is_finite_adele.one DedekindDomain.ProdAdicCompletions.IsFiniteAdele.one

open scoped DiscreteValuation

theorem algebraMap' (k : K) : (_root_.algebraMap K (K_hat R K) k).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  simp_rw [mem_adicCompletionIntegers, ProdAdicCompletions.algebraMap_apply',
    Valued.valuedCompletion_apply, not_le]
  change {v : HeightOneSpectrum R | 1 < v.valuation k}.Finite
  -- The goal currently: if k ∈ K = field of fractions of a Dedekind domain R,
  -- then v(k)>1 for only finitely many v.
  -- We now write k=n/d and go via R to solve this goal. Do we need to do this?
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
  have hd' : d ≠ 0 := nonZeroDivisors.ne_zero hd
  suffices {v : HeightOneSpectrum R | v.valuation (_root_.algebraMap R K d : K) < 1}.Finite by
    apply Finite.subset this
    intro v hv
    apply_fun v.valuation at hk
    simp only [Valuation.map_mul, valuation_of_algebraMap] at hk
    rw [mem_setOf_eq, valuation_of_algebraMap]
    have := int_valuation_le_one v n
    contrapose! this
    change 1 < v.intValuation n
    rw [← hk, mul_comm]
    exact lt_mul_of_le_of_one_lt' this hv (by simp) (by simp)
  simp_rw [valuation_of_algebraMap]
  change {v : HeightOneSpectrum R | v.intValuationDef d < 1}.Finite
  simp_rw [int_valuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]

end IsFiniteAdele

end ProdAdicCompletions

open ProdAdicCompletions.IsFiniteAdele

/-- The finite adèle ring of `R` is the restricted product over all maximal ideals `v` of `R`
of `adicCompletion`, with respect to `adicCompletionIntegers`. -/
def FiniteAdeleRing : Type _ := {x : K_hat R K // x.IsFiniteAdele}
#align dedekind_domain.finite_adele_ring DedekindDomain.FiniteAdeleRing

namespace FiniteAdeleRing

/-- The finite adèle ring of `R`, regarded as a `K`-subalgebra of the
product of the local completions of `K`. -/
def subalgebra : Subalgebra K (K_hat R K) where
  carrier := {x : K_hat R K | x.IsFiniteAdele}
  mul_mem' := mul
  one_mem' := one
  add_mem' := add
  zero_mem' := zero
  algebraMap_mem' := algebraMap'

instance : CommRing (FiniteAdeleRing R K) :=
  Subalgebra.toCommRing (subalgebra R K)

instance : Algebra K (FiniteAdeleRing R K) :=
  Subalgebra.algebra (subalgebra R K)

example (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) : Algebra A B := by
  exact φ.toAlgebra

example : R →+* K := algebraMap R K
example : K →+* (FiniteAdeleRing R K) := RingHom.smulOneHom

instance : Algebra R (FiniteAdeleRing R K) :=
  ((algebraMap K (FiniteAdeleRing R K)).comp (algebraMap R K)).toAlgebra

instance : Coe (FiniteAdeleRing R K) (K_hat R K) where
  coe := fun x ↦ x.1

@[ext]
lemma ext {a₁ a₂ : FiniteAdeleRing R K} (h : (a₁ : K_hat R K) = a₂) : a₁ = a₂ :=
  Subtype.ext h

/-- The finite adele ring is an algebra over the finite integral adeles. -/
instance : Algebra (R_hat R K) (FiniteAdeleRing R K) where
  smul rhat fadele := ⟨fun v ↦ rhat v * fadele.1 v, Finite.subset fadele.2 <| fun v hv ↦ by
    simp only [mem_adicCompletionIntegers, mem_compl_iff, mem_setOf_eq, map_mul] at hv ⊢
    exact mt (mul_le_one₀ (rhat v).2) hv
    ⟩
  toFun r := ⟨r, by simp_all⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' _ _ := mul_comm _ _
  smul_def' r x := rfl

instance : CoeFun (FiniteAdeleRing R K)
    (fun _ ↦ ∀ (v : HeightOneSpectrum R), adicCompletion K v) where
  coe a v := a.1 v

section Topology

open Classical

open nonZeroDivisors

open scoped algebraMap -- coercion from R to FiniteAdeleRing R K

lemma foo (a b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    ((a * b : FiniteAdeleRing R K) : K_hat R K) v = (a : K_hat R K) v * (b : K_hat R K) v := rfl

open scoped DiscreteValuation

open Multiplicative

variable {R K} in
lemma clear_local_denominator (v : HeightOneSpectrum R)
    (a : v.adicCompletion K) : ∃ b ∈ R⁰, a * b ∈ v.adicCompletionIntegers K := by
  by_cases ha : a ∈ v.adicCompletionIntegers K
  · use 1
    simp [ha, Submonoid.one_mem]
  · have xfoo : Valued.v a ≠ 0 := by
     intro h
     apply ha
     simp only [map_eq_zero] at h
     rw [h]
     exact ValuationSubring.zero_mem (adicCompletionIntegers K v)
    obtain ⟨n, hn⟩ : ∃ n : Multiplicative ℤ, Valued.v a = n := Option.ne_none_iff_exists'.mp xfoo
    -- n>1
    have foo : n > 1 := by
      by_contra! h2
      apply ha
      unfold adicCompletionIntegers
      simp only [Valuation.mem_valuationSubring_iff]
      rw [hn]
      exact_mod_cast h2
    let d : ℤ := Multiplicative.toAdd n
    have hd : 0 < d := by
      change 1 < n at foo
      rw [← Multiplicative.toAdd_lt] at foo
      exact foo
    have := v.ne_bot
    rw [Submodule.ne_bot_iff] at this
    obtain ⟨r, hrv, hr0⟩ := this
    have moo : v.asIdeal ∣ Ideal.span {r} := by
      simp only [Ideal.dvd_span_singleton, hrv]
    rw [← valuation_lt_one_iff_dvd (K := K) v r, valuation_of_algebraMap] at moo
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, v.intValuation r = m :=
      Option.ne_none_iff_exists'.mp <| int_valuation_ne_zero _ _ hr0
    let e : ℤ := Multiplicative.toAdd m
    have moo2 := hm ▸ moo
    norm_cast at moo2
    rw [← Multiplicative.toAdd_lt] at moo2
    simp at moo2
    refine ⟨r^d.natAbs, pow_mem (mem_nonZeroDivisors_of_ne_zero hr0) _, ?_⟩
    push_cast
    rw [mem_adicCompletionIntegers, map_mul, hn, map_pow]
    suffices (n : ℤₘ₀) * m ^ d.natAbs  ≤ 1 by
      convert this
      rw [← hm]
      simp
      convert Valued.valuedCompletion_apply (r : K)
      -- now purely global
      symm
      apply Valuation.extendToLocalization_apply_map_apply
      intro r hr hr2
      simp at hr2
      have := int_valuation_zero_le v ⟨r, hr⟩
      simp [← hr2] at this
    norm_cast

    rw [← toAdd_le, toAdd_mul, toAdd_pow, toAdd_one]--, ← Int.eq_natAbs_of_zero_le hd.le]
    change d + _ • e ≤ 0
    change e < 0 at moo2
    rw [show d.natAbs • e = (d.natAbs : ℤ) • e by simp only [nsmul_eq_mul,
      Int.natCast_natAbs, smul_eq_mul]]
    rw [← Int.eq_natAbs_of_zero_le hd.le, smul_eq_mul]
    suffices d * 1 + d * e ≤ 0 by simpa
    rw [← mul_add]
    have moo : 1 + e ≤ 0 := by omega
    exact Linarith.mul_nonpos moo foo

lemma exists_finiteIntegralAdele_iff (a : FiniteAdeleRing R K) : (∃ c : FiniteIntegralAdeles R K,
    a = c) ↔ ∀ (v : HeightOneSpectrum R), a v ∈ adicCompletionIntegers K v :=
  ⟨by rintro ⟨c, rfl⟩ v; exact (c v).2, fun h ↦ ⟨fun v ↦ ⟨a v, h v⟩, rfl⟩⟩

lemma Submonoid.finprod_mem {G : Type*} [CommMonoid G] {M : Submonoid G} {ι : Type*}
    {S : Set ι}
    {f : ι → G} (hf : ∀ i ∈ S, f i ∈ M) : (∏ᶠ i ∈ S, f i) ∈ M := by
  by_cases hS : (S ∩ mulSupport f).Finite
  · rw [finprod_mem_eq_prod _ hS]
    apply Submonoid.prod_mem M <| fun i hi ↦ hf _ ?_
    exact mem_of_mem_diff ((Finite.mem_toFinset hS).mp hi)
  · exact finprod_mem_eq_one_of_infinite hS ▸ M.one_mem

open scoped DiscreteValuation

lemma boundthing (r : R) :
    (r : adicCompletion K v) ∈ adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers]
  letI : Valued K ℤₘ₀ := adicValued v
  change Valued.v (r : v.adicCompletion K) ≤ 1
  suffices Valued.v (r : K) ≤ 1 by
    rw [← Valued.valuedCompletion_apply] at this
    convert this
  change v.valuation (r : K) ≤ 1
  suffices v.valuation (r : K) = v.intValuation r by
    rw [this]
    exact v.int_valuation_le_one r
  apply valuation_of_algebraMap

--  refine (Valuation.mem_valuationSubring_iff v.valuation (r : K)).mp ?_

    -- I'm sure I've seen this


--#check Valued.valuedCompletion_apply
variable {R K} in
lemma clear_denominator (a : FiniteAdeleRing R K) :
    ∃ (b : R⁰) (c : R_hat R K), a * ((b : R) : FiniteAdeleRing R K) = c := by
  let S := {v | a v ∉ adicCompletionIntegers K v}
  -- (a.2 : S.finite)
  choose b hb h using clear_local_denominator (R := R) (K := K)
  let p := ∏ᶠ v ∈ S, b v (a v)
  have hp : p ∈ R⁰ := Submonoid.finprod_mem <| fun v _ ↦ hb _ _
  use ⟨p, hp⟩
  rw [exists_finiteIntegralAdele_iff]
  intro v
  change a v * _ ∈ _
  dsimp
  by_cases hv : a v ∈ adicCompletionIntegers K v
  · apply mul_mem hv
    apply boundthing
  · have foo := h v (a v)
    simp at foo
    change a v * p ∈ _
    change v ∈ S at hv
    dsimp
    have pprod : p = b v (a v) * ∏ᶠ w ∈ S \ {v}, b w (a w) := by
      rw [show b v (a v) = ∏ᶠ w ∈ ({v} : Set (HeightOneSpectrum R)), b w (a w) by
        rw [finprod_mem_singleton]]
      rw [finprod_mem_mul_diff]
      · simp [hv]
      · exact a.2
    rw [pprod]
    push_cast
    rw [← mul_assoc]
    apply mul_mem foo
    apply boundthing

open scoped Pointwise

theorem submodulesRingBasis : SubmodulesRingBasis
    (fun (r : R⁰) ↦ Submodule.span (R_hat R K) {((r : R) : FiniteAdeleRing R K)}) where
  inter i j := ⟨i * j, by
    push_cast
    simp only [le_inf_iff, Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨((j : R) : R_hat R K), ?_⟩, ⟨((i : R) : R_hat R K), rfl⟩⟩
    rw [mul_comm]
    rfl
    ⟩
  leftMul a r := by
    rcases clear_denominator a with ⟨b, c, h⟩
    use r * b
    rintro x ⟨m, hm, rfl⟩
    simp only [Submonoid.coe_mul, SetLike.mem_coe] at hm
    rw [Submodule.mem_span_singleton] at hm ⊢
    rcases hm with ⟨n, rfl⟩
    simp only [LinearMapClass.map_smul, DistribMulAction.toLinearMap_apply, smul_eq_mul]
    use n * c
    push_cast
    rw [mul_left_comm, h, mul_comm _ (c : FiniteAdeleRing R K),
      Algebra.smul_def', Algebra.smul_def', ← mul_assoc]
    rfl
  mul r := ⟨r, by
    intro x hx
    rw [mem_mul] at hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_span_singleton] at ha hb ⊢
    rcases ha with ⟨m, rfl⟩
    rcases hb with ⟨n, rfl⟩
    use m * n * (r : R)
    simp only [Algebra.smul_def', map_mul]
    rw [mul_mul_mul_comm, mul_assoc]
    rfl
  ⟩

instance : Nonempty (R⁰) := ⟨1, Submonoid.one_mem R⁰⟩

instance : TopologicalSpace (FiniteAdeleRing R K) :=
  SubmodulesRingBasis.topology (submodulesRingBasis R K)

--#synth TopologicalRing (FiniteAdeleRing R K) -- works

end Topology

end FiniteAdeleRing

end DedekindDomain
