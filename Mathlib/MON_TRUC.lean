import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory


noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C]  [Small.{v, u} C]

variable (J : GrothendieckTopology C)

variable (X:C)

variable (F:Cᵒᵖ⥤ Ab)

variable (U:Presieve X)

local notation "R" => Sieve.generate U

--variable (W:C)
--variable (f:@U W)

def Y : Cᵒᵖ⥤Type v := ∐ (fun (Z : C) => ∐ (fun (f : @U Z) => yoneda.obj Z))


def tau_Z_f (Z:C) (f: @U Z): yoneda.obj Z ⟶ (Sieve.functor R ) where
  app W:= by
    apply Set.codRestrict (fun h => h ≫ f)
    intro x
    use Z, x, f
    constructor
    --exact (@U Z f)
    sorry


    sorry

  naturality := by
    intros V W h
    unfold yoneda
    simp
    rw [Set.val_codRestrict_apply]

    sorry

def τ:  (Y X U) ⟶ (Sieve.functor R ) := (Limits.Sigma.desc (fun (Z:C) => Limits.Sigma.desc fun (f : @U Z) => (tau_Z_f X U Z f)))


def machin2:  (Y X U) ⟶ (Sieve.functor R ):= (Limits.Sigma.desc (fun (Z:C) => Limits.Sigma.desc fun (f : @U Z) => (Set.codRestrict (yoneda.map (f : Z⟶ X)) _ _)))-/

lemma tau_epi: Epi (τ X U):= sorry

def Cech :SimplicialObject (Cᵒᵖ ⥤ Type v) := (Arrow.mk (τ X U)).cechNerve
