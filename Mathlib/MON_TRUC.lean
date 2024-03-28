import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck

open CategoryTheory

--open CategoryTheory.Limits

--noncomputable section

universe v₁ v₂ u₁ u₂ w

variable {C : Type u₁} [Category.{v₁} C]

variable {A : Type u₂} [Category.{v₂} A]-- je n'ai pas trouvé les groupes abéliens

variable (J : GrothendieckTopology C)

variable (X:C)

variable (F:Cᵒᵖ⥤A)

variable (U:Presieve X)

def R: Sieve X:= Sieve.generate U
