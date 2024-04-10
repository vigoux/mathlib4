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

def Y : Cᵒᵖ⥤Type v := ∐ (fun (Z : C) => ∐ (fun (_ : @U Z) => yoneda.obj Z))


def tau_Z_f (Z:C) (f: @U Z): yoneda.obj Z ⟶ (Sieve.functor R ) where
  app W:= by
    intro a
    use (a ≫ f), Z, a, f
    constructor
    exact (f.2)
    simp
  naturality := by
    intros V W h
    simp only [yoneda_obj_obj, Sieve.functor_obj, Sieve.generate_apply]
    ext
    simp

def τ:  (Y X U) ⟶ (Sieve.functor R ) := (Limits.Sigma.desc (fun (Z:C) => Limits.Sigma.desc fun (f : @U Z) => (tau_Z_f X U Z f)))

lemma tau_epi: Epi (τ X U):= by
  constructor
  intros Z u v huv
  apply NatTrans.ext
  ext Z f
  rcases f with ⟨f,Y, g, h, hf1, hf2⟩



  simp
  rw [hf2]


def Cech :SimplicialObject (Cᵒᵖ ⥤ Type v) := (Arrow.mk (τ X U)).cechNerve
