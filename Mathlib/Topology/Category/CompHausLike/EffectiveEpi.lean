/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# Effective epimorphisms in `CompHausLike`

In any category of compact Hausdorff spaces, continuous surjections are effective epimorphisms.
-/

universe u

open CategoryTheory Limits

attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

namespace CompHausLike

variable {P : TopCat.{u} → Prop}

/--
If `π` is a surjective morphism in `CompHausLike P`, then it is an effective epi.
-/
noncomputable
def struct {B X : CompHausLike P} (π : X ⟶ B) (hπ : Function.Surjective π) :
    EffectiveEpiStruct π where
  desc e h := (QuotientMap.of_surjective_continuous hπ π.continuous).lift e fun a b hab ↦
    DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a
  fac e h := ((QuotientMap.of_surjective_continuous hπ π.continuous).lift_comp e
    fun a b hab ↦ DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a)
  uniq e h g hm := by
    suffices g = (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv ⟨e,
      fun a b hab ↦ DFunLike.congr_fun
        (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩ (by ext; exact hab))
        a⟩ by assumption
    rw [← Equiv.symm_apply_eq (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv]
    ext
    simp only [QuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

/- This is not hard, but unnecessary for now because in all the relevant examples (`CompHaus`,
`Profinite`, `LightProfinite` and `Stonean`), `Epi` already implies surjective. -/
proof_wanted surjective_of_effectiveEpi {X Y : CompHausLike P} (f : X ⟶ Y) [EffectiveEpi f]
    (_ : P <| TopCat.of <| Set.range f) :
    Function.Surjective f

theorem preregular (hP : ∀ ⦃X Y B : CompHausLike P⦄ (f : X ⟶ B) (g : Y ⟶ B),
    P (TopCat.of { xy : X × Y | f xy.fst = g xy.snd }))
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f) :
    Preregular (CompHausLike P) where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π (hP _ _), pullback.fst f π (hP _ _), ?_, pullback.snd f π (hP _ _),
      (pullback.condition _ _ (hP _ _)).symm⟩
    refine ⟨⟨struct _ ?_⟩⟩
    intro y
    obtain ⟨z, hz⟩ := hs π hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

end CompHausLike
