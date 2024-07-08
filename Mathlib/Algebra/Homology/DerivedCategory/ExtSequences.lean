/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.DerivedCategory.Ext
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Long exact sequences of `Ext`-groups

In this file, we obtain the covariant long exact sequence of `Ext`:
`Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ → Ext X S.X₃ n₁`
when `S` is a short exact short complex in an abelian category `C`
and `X : C`.

-/

universe w' w v u

namespace Function

namespace Exact

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [AddGroup X₁] [AddGroup X₂] [AddGroup X₃]
  [AddGroup Y₁] [AddGroup Y₂] [AddGroup Y₃]
  (f : X₁ →+ X₂) (g : X₂ →+ X₃) (f' : Y₁ →+ Y₂) (g' : Y₂ →+ Y₃)
  (e₁ : X₁ ≃+ Y₁) (e₂ : X₂ ≃+ Y₂) (e₃ : X₃ ≃+ Y₃)
  (comm₁₂ : f'.comp e₁.toAddMonoidHom = e₂.toAddMonoidHom.comp f)
  (comm₂₃ : g'.comp e₂.toAddMonoidHom = e₃.toAddMonoidHom.comp g)

lemma of_ladder_addEquiv (hfg : Exact f g) : Exact f' g' := by
  have h₁₂ := DFunLike.congr_fun comm₁₂
  have h₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at h₁₂ h₂₃
  apply of_comp_eq_zero_of_ker_in_range
  · ext y₁
    obtain ⟨x₁, rfl⟩ := e₁.surjective y₁
    dsimp
    rw [h₁₂, h₂₃, hfg.apply_apply_eq_zero, map_zero]
  · intro y₂ hx₂
    obtain ⟨x₂, rfl⟩ := e₂.surjective y₂
    obtain ⟨x₁, rfl⟩ := (hfg x₂).1 (e₃.injective (by rw [← h₂₃, hx₂, map_zero]))
    exact ⟨e₁ x₁, by rw [h₁₂]⟩

lemma of_ladder_addEquiv' (hfg' : Exact f' g') : Exact f g := by
  refine of_ladder_addEquiv f' g' f g e₁.symm e₂.symm e₃.symm ?_ ?_ hfg'
  · ext y₁
    obtain ⟨x₁, rfl⟩ := e₁.surjective y₁
    apply e₂.injective
    simpa using DFunLike.congr_fun comm₁₂.symm x₁
  · ext y₂
    obtain ⟨x₂, rfl⟩ := e₂.surjective y₂
    apply e₃.injective
    simpa using DFunLike.congr_fun comm₂₃.symm x₂

lemma iff_of_ladder_addEquiv : Exact f g ↔ Exact f' g' := by
  constructor
  · exact of_ladder_addEquiv f g f' g' e₁ e₂ e₃ comm₁₂ comm₂₃
  · exact of_ladder_addEquiv' f g f' g' e₁ e₂ e₃ comm₁₂ comm₂₃

end Exact

end Function

namespace CategoryTheory

namespace ShortComplex

lemma ab_exact_iff_function_exact (S : ShortComplex AddCommGrp.{u}) :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [S.ab_exact_iff]
  apply forall_congr'
  intro x₂
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨x₁, rfl⟩
    simp only [ab_zero_apply]
  · tauto

end ShortComplex

open Opposite DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Abelian

namespace Ext

section CovariantSequence

lemma hom_comp_singleFunctor_map_shift [HasDerivedCategory.{w'} C]
    {X Y Z : C} {n : ℕ} (x : Ext X Y n) (f : Y ⟶ Z) :
    x.hom ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦(n : ℤ)⟧' =
      (x.comp (mk₀ f) (add_zero n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.comp_mk₀]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

lemma preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply
    [HasDerivedCategory.{w'} C] {X : C} {n₀ : ℕ} (x : Ext X S.X₃ n₀)
    {n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequenceδ
      hS.singleTriangle n₀ n₁ (by omega) x.hom =
        (x.comp hS.extClass h).hom := by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply,
    comp_hom, hS.extClass_hom, ShiftedHom.comp]
  rfl

variable (X)

lemma covariant_sequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (AddCommGrp.ofHom ((mk₀ S.f).postcomp X (add_zero n)))
      (AddCommGrp.ofHom ((mk₀ S.g).postcomp X (add_zero n))) (by
        ext x
        dsimp [AddCommGrp.ofHom]
        simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, ShortComplex.zero, mk₀_zero,
          comp_zero]
        rfl)).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₂ _
    (hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv)
     (hfg' := this)
  all_goals ext x; apply hom_comp_singleFunctor_map_shift (C := C)

section

variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

lemma covariant_sequence_exact₃' :
    (ShortComplex.mk (AddCommGrp.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
      (AddCommGrp.ofHom (hS.extClass.postcomp X h)) (by
        ext x
        dsimp [AddCommGrp.ofHom]
        simp only [comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
          comp_zero]
        rfl)).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₃ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by omega)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (hfg' := this)
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h

lemma covariant_sequence_exact₁' :
    (ShortComplex.mk
      (AddCommGrp.ofHom (hS.extClass.postcomp X h))
      (AddCommGrp.ofHom ((mk₀ S.f).postcomp X (add_zero n₁))) (by
        ext x
        dsimp [AddCommGrp.ofHom]
        simp only [comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp, comp_zero]
        rfl)).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₁ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by omega)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (hfg' := this)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)

open ComposableArrows

/-- Given a short exact short complex `S` in an abelian category `C` and an object `X : C`,
this is the long exact sequence
`Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ → Ext X S.X₃ n₁`. -/
noncomputable def covariantSequence : ComposableArrows AddCommGrp.{w} 5 :=
  mk₅ (AddCommGrp.ofHom ((mk₀ S.f).postcomp X (add_zero n₀)))
    (AddCommGrp.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
    (AddCommGrp.ofHom (hS.extClass.postcomp X h))
    (AddCommGrp.ofHom ((mk₀ S.f).postcomp X (add_zero n₁)))
    (AddCommGrp.ofHom ((mk₀ S.g).postcomp X (add_zero n₁)))

lemma covariantSequence_exact :
    (covariantSequence X hS n₀ n₁ h).Exact :=
  exact_of_δ₀ (covariant_sequence_exact₂' X hS n₀).exact_toComposableArrows
    (exact_of_δ₀ (covariant_sequence_exact₃' X hS n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (covariant_sequence_exact₁' X hS n₀ n₁ h).exact_toComposableArrows
        (covariant_sequence_exact₂' X hS n₁).exact_toComposableArrows))

end

lemma covariant_sequence_exact₁ {n₁ : ℕ} (x₁ : Ext X S.X₁ n₁)
    (hx₁ : x₁.comp (mk₀ S.f) (add_zero n₁) = 0) {n₀ : ℕ} (hn₀ : n₀ + 1 = n₁) :
    ∃ (x₃ : Ext X S.X₃ n₀), x₃.comp hS.extClass hn₀ = x₁ := by
  have := covariant_sequence_exact₁' X hS n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

lemma covariant_sequence_exact₂ {n : ℕ} (x₂ : Ext X S.X₂ n)
    (hx₂ : x₂.comp (mk₀ S.g) (add_zero n) = 0) :
    ∃ (x₁ : Ext X S.X₁ n), x₁.comp (mk₀ S.f) (add_zero n) = x₂ := by
  have := covariant_sequence_exact₂' X hS n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

lemma covariant_sequence_exact₃ {n₀ : ℕ} (x₃ : Ext X S.X₃ n₀) {n₁ : ℕ} (hn₁ : n₀ + 1 = n₁)
    (hx₃ : x₃.comp hS.extClass hn₁ = 0) :
    ∃ (x₂ : Ext X S.X₂ n₀), x₂.comp (mk₀ S.g) (add_zero n₀) = x₃ := by
  have := covariant_sequence_exact₃' X hS n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

end CovariantSequence

end Ext

end Abelian

end CategoryTheory
