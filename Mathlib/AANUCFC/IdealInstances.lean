import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.Ideal.Operations

section IdealInstances

instance Ideal.instMulMemClass {R : Type*} [Semiring R] :
    MulMemClass (Ideal R) R where
  mul_mem _ := Ideal.mul_mem_left _ _

instance Ideal.instNonUnitalSemiring {R : Type*} [Semiring R] (I : Ideal R) :
    NonUnitalSemiring I where
  left_distrib _ _ _ := Subtype.ext <| mul_add ..
  right_distrib _ _ _ := Subtype.ext <| add_mul ..
  zero_mul _ := Subtype.ext <| zero_mul _
  mul_zero _ := Subtype.ext <| mul_zero _
  mul_assoc _ _ _ := Subtype.ext <| mul_assoc ..

instance Ideal.instNonUnitalRing {R : Type*} [Ring R] (I : Ideal R) :
    NonUnitalRing I where
  left_distrib _ _ _ := Subtype.ext <| mul_add ..
  right_distrib _ _ _ := Subtype.ext <| add_mul ..
  zero_mul _ := Subtype.ext <| zero_mul _
  mul_zero _ := Subtype.ext <| mul_zero _
  mul_assoc _ _ _ := Subtype.ext <| mul_assoc ..

instance Ideal.instNonUnitalCommSemiring {R : Type*} [CommSemiring R] (I : Ideal R) :
    NonUnitalCommSemiring I where
  mul_comm x y := Subtype.ext <| mul_comm (x : R) (y : R)

instance Ideal.instNonUnitalCommRing {R : Type*} [CommRing R] (I : Ideal R) :
    NonUnitalCommRing I where
  mul_comm x y := Subtype.ext <| mul_comm (x : R) (y : R)

instance Ideal.instTopologicalSemiring {R : Type*} [Semiring R] [TopologicalSpace R]
    [TopologicalSemiring R] (I : Ideal R) : TopologicalSemiring I where
  continuous_mul := by -- `continuity` gets this, slowly, but `fun_prop` fails
    apply Continuous.subtype_mk
    exact continuous_induced_dom.comp' continuous_fst |>.mul <|
      continuous_induced_dom.comp' continuous_snd

end IdealInstances
