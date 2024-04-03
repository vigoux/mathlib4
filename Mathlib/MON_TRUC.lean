import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory

--open CategoryTheory.Limits

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C]  [Small.{v, u} C]

variable (J : GrothendieckTopology C)

variable (X:C)

variable (F:Cᵒᵖ⥤ Ab)

variable (U:Presieve X)

local notation "R" => Sieve.generate U


def Y : Cᵒᵖ⥤Type v := ∐ (fun (Z : C) => ∐ (fun (f : @U Z) => yoneda.obj Z))

def τ:  Y ⟶ (Sieve.functor R):= sorry

lemma tau_epi: Epi (τ X U):= sorry

def Cech :SimplicialObject (Cᵒᵖ ⥤ Type v) := (Arrow.mk (τ X U)).cechNerve
