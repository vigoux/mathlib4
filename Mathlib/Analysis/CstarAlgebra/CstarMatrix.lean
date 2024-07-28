/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CstarAlgebra.HilbertCstarModule

/-!
# Matrices with entries in a C⋆-algebra

This file creates a type copy of `n → A` meant for vectors with entries in a C⋆-algebra `A`. It is
endowed with a Hilbert C⋆-module structure, which in particular comes with an `A`-valued
"inner product" `⟪w, v⟫ = ∑ i, star (w i) * v i` and a norm `‖v‖ = √‖⟪v, v⟫‖`.

## Main declarations

+ `CstarMatrix m n A`: the type copy
+ `instHilbertCstarModule`: the Hilbert C⋆-module instance

## Implementation notes

The norm on this type induces the product uniformity and bornology, but these are not defeq to
`Pi.uniformSpace` and `Pi.instBornology`. Hence, we prove the equality to the Pi instances and
replace the uniformity and bornology by the Pi ones when registering the
`NormedAddCommGroup (CstarVec n A)` instance. See the docstring of the `TopologyAux` section below
for more details.

-/

open scoped ComplexOrder Topology Uniformity Bornology

