/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Mathport.Rename

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

# Align statements for declarations from Batteries
-/

#align int.default_eq_zero Int.default_eq_zero
#align int.add_def Int.add_def
#align int.mul_def Int.mul_def
#align int.add_neg_one Int.add_neg_one
#align int.sign_neg Int.sign_neg
#align int.sign_mul Int.sign_mul
#align int.add_one_le_iff Int.add_one_le_iff
