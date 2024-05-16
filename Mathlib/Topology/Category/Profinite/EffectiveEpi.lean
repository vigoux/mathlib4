/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Boris Bolvig Kjær, Jon Eugster, Sina Hazratpour
-/
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.CompHausLike.EffectiveEpi

/-!
# Effective epimorphisms and finite effective epimorphic families in `Profinite`

This file proves that `Profinite` is `Preregular`. Together with the fact that it is
`FinitaryPreExtensive`, this implies that `Profinite` is `Precoherent`.

To do this, we need to characterise effective epimorphisms in `Profinite`. As a consequence, we also
get a characterisation of finite effective epimorphic families.

## Main results

* `Profinite.effectiveEpi_tfae`: For a morphism in `Profinite`, the conditions surjective,
  epimorphic, and effective epimorphic are all equivalent.

* `Profinite.effectiveEpiFamily_tfae`: For a finite family of morphisms in `Profinite` with fixed
  target in `Profinite`, the conditions jointly surjective, jointly epimorphic and effective
  epimorphic are all equivalent.

As a consequence, we obtain instances that `Profinite` is precoherent and preregular.

- TODO: Write API for reflecting effective epimorphisms and deduce the contents of this file by
  abstract nonsense from the corresponding results for `CompHaus`.

-/

universe u

open CategoryTheory Limits CompHausLike

namespace Profinite

open List in
theorem effectiveEpi_tfae
    {B X : Profinite.{u}} (π : X ⟶ B) :
    TFAE
    [ EffectiveEpi π
    , Epi π
    , Function.Surjective π
    ] := by
  tfae_have 1 → 2
  · intro; infer_instance
  tfae_have 2 ↔ 3
  · exact epi_iff_surjective π
  tfae_have 3 → 1
  · exact fun hπ ↦ ⟨⟨CompHausLike.struct π hπ⟩⟩
  tfae_finish

instance : Preregular Profinite := by
  apply preregular
  · intro X Y _ _ _
    exact show TotallyDisconnectedSpace {xy : X × Y | _} from inferInstance
  · intro _ _ _
    exact ((effectiveEpi_tfae _).out 0 2).mp

-- Was an `example`, but that made the linter complain about unused imports
instance : Precoherent Profinite.{u} := inferInstance

-- TODO: prove this for `Type*`
open List in
theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : Profinite.{u}}
    (X : α → Profinite.{u}) (π : (a : α) → (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 2 → 1
  · intro
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 → 2
  · intro; infer_instance
  tfae_have 3 → 2
  · intro e
    rw [epi_iff_surjective]
    intro b
    obtain ⟨t, x, h⟩ := e b
    refine ⟨Sigma.ι X t x, ?_⟩
    change (Sigma.ι X t ≫ Sigma.desc π) x = _
    simpa using h
  tfae_have 2 → 3
  · intro e; rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X (inferInstance : TotallyDisconnectedSpace (Σ (a : α), X a)) :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _ _)
    intro b
    obtain ⟨t, rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id]; rfl
    rw [this]
    show _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X _ π by
      rw [this]; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [i, Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext; rfl
  tfae_finish

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Finite α] {B : Profinite.{u}}
    (X : α → Profinite.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

end Profinite
