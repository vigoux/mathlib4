/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne
-/
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.CategoryTheory.FintypeCat

#align_import topology.category.Profinite.basic from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `TopCat`. The fully faithful functor
is called `Profinite.toTop`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

* Define procategories and prove that `Profinite` is equivalent to `Pro (FintypeCat)`.

## Tags

profinite

-/

set_option linter.uppercaseLean3 false

universe v u

open CategoryTheory

open Topology

/-- The type of profinite topological spaces. -/
abbrev Profinite := CompHausLike (fun X ↦ TotallyDisconnectedSpace X)
#align Profinite Profinite

namespace Profinite

/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] : Profinite :=
  CompHausLike.of _ X (inferInstance : TotallyDisconnectedSpace X)
#align Profinite.of Profinite.of

instance : Inhabited Profinite :=
  ⟨Profinite.of PEmpty⟩

instance hasForget₂ : HasForget₂ Profinite TopCat :=
  InducedCategory.hasForget₂ _
#align Profinite.has_forget₂ Profinite.hasForget₂

instance {X : Profinite} : TotallyDisconnectedSpace X :=
  X.prop

-- We check that we automatically infer that Profinite sets are compact and Hausdorff.
example {X : Profinite} : CompactSpace X :=
  inferInstance

example {X : Profinite} : T2Space X :=
  inferInstance

instance {X : Profinite} : TotallyDisconnectedSpace ((forget Profinite).obj X) := by
  change TotallyDisconnectedSpace X
  exact inferInstance

-- Porting note: removed, as it is a syntactic tautology.
-- @[simp]
-- theorem coe_toCompHaus {X : Profinite} : (X.toCompHaus : Type*) = (X : Type*) :=
--   rfl
-- #align Profinite.coe_to_CompHaus Profinite.coe_toCompHaus

end Profinite

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
abbrev profiniteToCompHaus : Profinite ⥤ CompHaus :=
  compHausLikeToCompHaus _
-- Porting note: deriving fails, adding manually.
-- deriving Full, Faithful
#align Profinite_to_CompHaus profiniteToCompHaus

instance : profiniteToCompHaus.Full :=
  show (inducedFunctor _).Full from inferInstance

instance : profiniteToCompHaus.Faithful :=
  show (inducedFunctor _).Faithful from inferInstance

-- Porting note: added, as it is not found otherwise.
instance {X : Profinite} : TotallyDisconnectedSpace (profiniteToCompHaus.obj X) :=
  X.prop

/-- The fully faithful embedding of `Profinite` in `TopCat`.
This is definitionally the same as the obvious composite. -/
abbrev Profinite.toTopCat : Profinite ⥤ TopCat :=
  CompHausLike.compHausLikeToTop _
-- Porting note: deriving fails, adding manually.
-- deriving Full, Faithful
#align Profinite.to_Top Profinite.toTopCat

instance : Profinite.toTopCat.Full :=
  show (inducedFunctor _).Full from inferInstance

instance : Profinite.toTopCat.Faithful :=
  show (inducedFunctor _).Faithful from inferInstance

-- @[simp]
-- theorem Profinite.to_compHausToTopCat :
--     profiniteToCompHaus ⋙ compHausToTop = Profinite.toTopCat :=
--   rfl
-- #align Profinite.to_CompHaus_to_Top Profinite.to_compHausToTopCat

section Profinite

-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
/--
(Implementation) The object part of the connected_components functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
def CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u} where
  toTop := TopCat.of (ConnectedComponents X)
  is_compact := Quotient.compactSpace
  is_hausdorff := ConnectedComponents.t2
  prop := ConnectedComponents.totallyDisconnectedSpace
#align CompHaus.to_Profinite_obj CompHaus.toProfiniteObj

/-- (Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
    (CompHaus.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y) where
  toFun f := f.comp ⟨Quotient.mk'', continuous_quotient_mk'⟩
  invFun g :=
    { toFun := Continuous.connectedComponentsLift g.2
      continuous_toFun := Continuous.connectedComponentsLift_continuous g.2 }
  left_inv _ := ContinuousMap.ext <| ConnectedComponents.surjective_coe.forall.2 fun _ => rfl
  right_inv _ := ContinuousMap.ext fun _ => rfl
#align Profinite.to_CompHaus_equivalence Profinite.toCompHausEquivalence

/-- The connected_components functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
def CompHaus.toProfinite : CompHaus ⥤ Profinite :=
  Adjunction.leftAdjointOfEquiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl
#align CompHaus.to_Profinite CompHaus.toProfinite

theorem CompHaus.toProfinite_obj' (X : CompHaus) :
    ↥(CompHaus.toProfinite.obj X) = ConnectedComponents X :=
  rfl
#align CompHaus.to_Profinite_obj' CompHaus.toProfinite_obj'

/-- Finite types are given the discrete topology. -/
def FintypeCat.botTopology (A : FintypeCat) : TopologicalSpace A := ⊥
#align Fintype.bot_topology FintypeCat.botTopology

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology

theorem FintypeCat.discreteTopology (A : FintypeCat) : DiscreteTopology A :=
  ⟨rfl⟩
#align Fintype.discrete_topology FintypeCat.discreteTopology

attribute [local instance] FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps!]
def FintypeCat.toProfinite : FintypeCat ⥤ Profinite where
  obj A := Profinite.of A
  map f := ⟨f, by continuity⟩
#align Fintype.to_Profinite FintypeCat.toProfinite

instance : FintypeCat.toProfinite.Faithful where
  map_injective h := funext fun _ ↦ (DFunLike.ext_iff.mp h) _

instance : FintypeCat.toProfinite.Full where
  map_surjective f := ⟨fun x ↦ f x, rfl⟩

end DiscreteTopology

end Profinite

namespace Profinite

/-- An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`CompHaus.limitCone`, which is defined in terms of `TopCat.limitCone`. -/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) : Limits.Cone F where
  pt :=
    { toTop := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).pt.toTop
      prop := by
        change TotallyDisconnectedSpace ({ u : ∀ j : J, F.obj j | _ } : Type _)
        exact Subtype.totallyDisconnectedSpace }
  π :=
  { app := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).π.app
    -- Porting note: was `by tidy`:
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }
#align Profinite.limit_cone Profinite.limitCone

/-- The limit cone `Profinite.limitCone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) :
    Limits.IsLimit (limitCone F) where
  lift S :=
    (CompHaus.limitConeIsLimit.{v, u} (F ⋙ profiniteToCompHaus)).lift
      (profiniteToCompHaus.mapCone S)
  uniq S m h := (CompHaus.limitConeIsLimit.{v, u} _).uniq (profiniteToCompHaus.mapCone S) _ h
#align Profinite.limit_cone_is_limit Profinite.limitConeIsLimit

/-- The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus -/
def toProfiniteAdjToCompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus :=
  Adjunction.adjunctionOfEquivLeft _ _
#align Profinite.to_Profinite_adj_to_CompHaus Profinite.toProfiniteAdjToCompHaus

/-- The category of profinite sets is reflective in the category of compact Hausdorff spaces -/
instance toCompHaus.reflective : Reflective profiniteToCompHaus where
  adj := Profinite.toProfiniteAdjToCompHaus
#align Profinite.to_CompHaus.reflective Profinite.toCompHaus.reflective

noncomputable instance toCompHaus.createsLimits : CreatesLimits profiniteToCompHaus :=
  monadicCreatesLimits _
#align Profinite.to_CompHaus.creates_limits Profinite.toCompHaus.createsLimits

noncomputable instance toTopCat.reflective : Reflective Profinite.toTopCat :=
  Reflective.comp profiniteToCompHaus compHausToTop
#align Profinite.to_Top.reflective Profinite.toTopCat.reflective

noncomputable instance toTopCat.createsLimits : CreatesLimits Profinite.toTopCat :=
  monadicCreatesLimits _
#align Profinite.to_Top.creates_limits Profinite.toTopCat.createsLimits

instance hasLimits : Limits.HasLimits Profinite :=
  hasLimits_of_hasLimits_createsLimits Profinite.toTopCat
#align Profinite.has_limits Profinite.hasLimits

instance hasColimits : Limits.HasColimits Profinite :=
  hasColimits_of_reflective profiniteToCompHaus
#align Profinite.has_colimits Profinite.hasColimits

noncomputable instance forgetPreservesLimits : Limits.PreservesLimits (forget Profinite) := by
  apply Limits.compPreservesLimits Profinite.toTopCat (forget TopCat)
#align Profinite.forget_preserves_limits Profinite.forgetPreservesLimits

theorem epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · -- Porting note: in mathlib3 `contrapose` saw through `Function.Surjective`.
    dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine' Set.mem_compl _
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ 𝓝 y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
    classical
      let Z := of (ULift.{u} <| Fin 2)
      let g : Y ⟶ Z := ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        apply ULift.ext
        dsimp [g, LocallyConstant.ofIsClopen]
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [comp_apply, ContinuousMap.coe_mk, comp_apply, ContinuousMap.coe_mk,
          Function.comp_apply, if_neg]
        refine' mt (fun α => hVU α) _
        simp only [U, C, Set.mem_range_self, not_true, not_false_iff, Set.mem_compl_iff]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget Profinite).epi_of_epi_map
#align Profinite.epi_iff_surjective Profinite.epi_iff_surjective

theorem mono_iff_injective {X Y : Profinite.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  CompHausLike.mono_iff_injective f (inferInstance : TotallyDisconnectedSpace PUnit.{u+1})
#align Profinite.mono_iff_injective Profinite.mono_iff_injective

end Profinite
