/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Tactic.GCongr.Core

/-!
# Monotonicity of multiplication by positive elements

This file defines typeclasses to reason about monotonicity of the operations
* `b ↦ a * b`, "left multiplication"
* `a ↦ a * b`, "right multiplication"

We use eight typeclasses to encode the various properties we care about for those two operations.
These typeclasses are meant to be mostly internal to this file, to set up each lemma in the
appropriate generality.

Less granular typeclasses like `OrderedAddCommMonoid`, `LinearOrderedField` should be enough for
most purposes, and the system is set up so that they imply the correct granular typeclasses here.
If those are enough for you, you may stop reading here! Else, beware that what follows is a bit
technical.

## Definitions

In all that follows, `α` is an orders which has a `0` and a multiplication. Note however that we do
not use lawfulness of this action in most of the file. Hence `*` should be considered here as a
mostly arbitrary function `α → α → α`.

We use the following four typeclasses to reason about left multiplication (`b ↦ a * b`):
* `PosMulMono`: If `a ≥ 0`, then `b₁ ≤ b₂ → a * b₁ ≤ a * b₂`.
* `PosMulStrictMono`: If `a > 0`, then `b₁ < b₂ → a * b₁ < a * b₂`.
* `PosMulReflectLT`: If `a ≥ 0`, then `a * b₁ < a * b₂ → b₁ < b₂`.
* `PosMulReflectLE`: If `a > 0`, then `a * b₁ ≤ a * b₂ → b₁ ≤ b₂`.

We use the following four typeclasses to reason about right multiplication (`a ↦ a * b`):
* `MulPosMono`: If `b ≥ 0`, then `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b`.
* `MulPosStrictMono`: If `b > 0`, then `a₁ < a₂ → a₁ * b < a₂ * b`.
* `MulPosReflectLT`: If `b ≥ 0`, then `a₁ * b < a₂ * b → a₁ < a₂`.
* `MulPosReflectLE`: If `b > 0`, then `a₁ * b ≤ a₂ * b → a₁ ≤ a₂`.

## Implications

As `α` gets more and more structure, those typeclasses end up being equivalent. The commonly used
implications are:
*  When `α` is a partial order:
  * `PosMulStrictMono → PosMulMono`
  * `MulPosStrictMono → MulPosMono`
  * `PosMulReflectLE → PosMulReflectLT`
  * `MulPosReflectLE → MulPosReflectLT`
* When `α` is a linear order:
  * `PosMulStrictMono → PosMulReflectLE`
  * `MulPosStrictMono → MulPosReflectLE` .
* When the multiplication of `α` is commutative:
  * `PosMulMono → MulPosMono`
  * `PosMulStrictMono → MulPosStrictMono`
  * `PosMulReflectLE → MulPosReflectLE`
  * `PosMulReflectLT → MulPosReflectLT`

Further, the bundled non-granular typeclasses imply the granular ones like so:
* `OrderedSemiring → PosMulMono`
* `OrderedSemiring → MulPosMono`
* `StrictOrderedSemiring → PosMulStrictMono`
* `StrictOrderedSemiring → MulPosStrictMono`

All these are registered as instances, which means that in practice you should not worry about these
implications. However, if you encounter a case where you think a statement is true but not covered
by the current implications, please bring it up on Zulip!

## Notation

The following is local notation in this file:
* `α≥0`: `{x : α // 0 ≤ x}`
* `α>0`: `{x : α // 0 < x}`

See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
for a discussion about this notation, and whether to enable it globally (note that the notation is
currently global but broken, hence actually only works locally).
-/

variable (α : Type*)

set_option quotPrecheck false in
/-- Local notation for the nonnegative elements of a type `α`. TODO: actually make local. -/
notation "α≥0" => { x : α // 0 ≤ x }

set_option quotPrecheck false in
/-- Local notation for the positive elements of a type `α`. TODO: actually make local. -/
notation "α>0" => { x : α // 0 < x }

section Abbreviations

variable [Mul α] [Zero α] [Preorder α]

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the left,
namely `b₁ ≤ b₂ → a * b₁ ≤ a * b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSemiring`. -/
abbrev PosMulMono : Prop :=
  CovariantClass α≥0 α (fun x y => x * y) (· ≤ ·)

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the right,
namely `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSemiring`. -/
abbrev MulPosMono : Prop :=
  CovariantClass α≥0 α (fun x y => y * x) (· ≤ ·)

/-- Typeclass for strict monotonicity of multiplication by positive elements on the left,
namely `b₁ < b₂ → a * b₁ < a * b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`StrictOrderedSemiring`. -/
abbrev PosMulStrictMono : Prop :=
  CovariantClass α>0 α (fun x y => x * y) (· < ·)

/-- Typeclass for strict monotonicity of multiplication by positive elements on the right,
namely `a₁ < a₂ → a₁ * b < a₂ * b` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`StrictOrderedSemiring`. -/
abbrev MulPosStrictMono : Prop :=
  CovariantClass α>0 α (fun x y => y * x) (· < ·)

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the left, namely `a * b₁ < a * b₂ → b₁ < b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
abbrev PosMulReflectLT : Prop :=
  ContravariantClass α≥0 α (fun x y => x * y) (· < ·)

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the right, namely `a₁ * b < a₂ * b → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
abbrev MulPosReflectLT : Prop :=
  ContravariantClass α≥0 α (fun x y => y * x) (· < ·)

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the left,
namely `a * b₁ ≤ a * b₂ → b₁ ≤ b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
abbrev PosMulReflectLE : Prop :=
  ContravariantClass α>0 α (fun x y => x * y) (· ≤ ·)

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the right,
namely `a₁ * b ≤ a₂ * b → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
abbrev MulPosReflectLE : Prop :=
  ContravariantClass α>0 α (fun x y => y * x) (· ≤ ·)

end Abbreviations

variable {α} {a b c d : α}

section MulZero

variable [Mul α] [Zero α]

section Preorder

variable [Preorder α]

instance PosMulMono.to_covariantClass_pos_mul_le [PosMulMono α] :
    CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨fun a _ _ bc => @CovariantClass.elim α≥0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance MulPosMono.to_covariantClass_pos_mul_le [MulPosMono α] :
    CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨fun a _ _ bc => @CovariantClass.elim α≥0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance PosMulReflectLT.to_contravariantClass_pos_mul_lt [PosMulReflectLT α] :
    ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance MulPosReflectLT.to_contravariantClass_pos_mul_lt [MulPosReflectLT α] :
    ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

@[gcongr]
theorem mul_le_mul_of_nonneg_left [PosMulMono α] (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c :=
  @CovariantClass.elim α≥0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ h

@[gcongr]
theorem mul_le_mul_of_nonneg_right [MulPosMono α] (h : b ≤ c) (a0 : 0 ≤ a) : b * a ≤ c * a :=
  @CovariantClass.elim α≥0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ h

@[gcongr]
theorem mul_lt_mul_of_pos_left [PosMulStrictMono α] (bc : b < c) (a0 : 0 < a) : a * b < a * c :=
  @CovariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ bc

@[gcongr]
theorem mul_lt_mul_of_pos_right [MulPosStrictMono α] (bc : b < c) (a0 : 0 < a) : b * a < c * a :=
  @CovariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ bc

theorem lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ h

theorem lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ h

theorem le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

theorem le_of_mul_le_mul_right [MulPosReflectLE α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

alias lt_of_mul_lt_mul_of_nonneg_left := lt_of_mul_lt_mul_left

alias lt_of_mul_lt_mul_of_nonneg_right := lt_of_mul_lt_mul_right

alias le_of_mul_le_mul_of_pos_left := le_of_mul_le_mul_left

alias le_of_mul_le_mul_of_pos_right := le_of_mul_le_mul_right

@[simp]
theorem mul_lt_mul_left [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a * c ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· < ·) _ _ ⟨a, a0⟩ _ _

@[simp]
theorem mul_lt_mul_right [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    b * a < c * a ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· < ·) _ _ ⟨a, a0⟩ _ _

@[simp]
theorem mul_le_mul_left [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

@[simp]
theorem mul_le_mul_right [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

alias mul_le_mul_iff_of_pos_left := mul_le_mul_left
alias mul_le_mul_iff_of_pos_right := mul_le_mul_right
alias mul_lt_mul_iff_of_pos_left := mul_lt_mul_left
alias mul_lt_mul_iff_of_pos_right := mul_lt_mul_right

theorem mul_lt_mul_of_pos_of_nonneg [PosMulStrictMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c < d)
    (a0 : 0 < a) (d0 : 0 ≤ d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)

theorem mul_lt_mul_of_le_of_le' [PosMulStrictMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c < d)
    (b0 : 0 < b) (c0 : 0 ≤ c) : a * c < b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)

theorem mul_lt_mul_of_nonneg_of_pos [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c ≤ d)
    (a0 : 0 ≤ a) (d0 : 0 < d) : a * c < b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)

theorem mul_lt_mul_of_le_of_lt' [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c ≤ d)
    (b0 : 0 ≤ b) (c0 : 0 < c) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)

theorem mul_lt_mul_of_pos_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c < d)
    (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans (mul_lt_mul_of_pos_right h₁ d0)

theorem mul_lt_mul_of_lt_of_lt' [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c < d)
    (b0 : 0 < b) (c0 : 0 < c) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)

theorem mul_lt_of_mul_lt_of_nonneg_left [PosMulMono α] (h : a * b < c) (hdb : d ≤ b) (ha : 0 ≤ a) :
    a * d < c :=
  (mul_le_mul_of_nonneg_left hdb ha).trans_lt h

theorem lt_mul_of_lt_mul_of_nonneg_left [PosMulMono α] (h : a < b * c) (hcd : c ≤ d) (hb : 0 ≤ b) :
    a < b * d :=
  h.trans_le <| mul_le_mul_of_nonneg_left hcd hb

theorem mul_lt_of_mul_lt_of_nonneg_right [MulPosMono α] (h : a * b < c) (hda : d ≤ a) (hb : 0 ≤ b) :
    d * b < c :=
  (mul_le_mul_of_nonneg_right hda hb).trans_lt h

theorem lt_mul_of_lt_mul_of_nonneg_right [MulPosMono α] (h : a < b * c) (hbd : b ≤ d) (hc : 0 ≤ c) :
    a < d * c :=
  h.trans_le <| mul_le_mul_of_nonneg_right hbd hc

end Preorder

section LinearOrder

variable [LinearOrder α]

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulReflectLE [PosMulStrictMono α] :
    PosMulReflectLE α :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosReflectLE [MulPosStrictMono α] :
    MulPosReflectLE α :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim⟩

theorem PosMulReflectLE.toPosMulStrictMono [PosMulReflectLE α] : PosMulStrictMono α :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).2 ContravariantClass.elim⟩

theorem MulPosReflectLE.toMulPosStrictMono [MulPosReflectLE α] : MulPosStrictMono α :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).2 ContravariantClass.elim⟩

theorem posMulStrictMono_iff_posMulReflectLE : PosMulStrictMono α ↔ PosMulReflectLE α :=
  ⟨@PosMulStrictMono.toPosMulReflectLE _ _ _ _, @PosMulReflectLE.toPosMulStrictMono _ _ _ _⟩

theorem mulPosStrictMono_iff_mulPosReflectLE : MulPosStrictMono α ↔ MulPosReflectLE α :=
  ⟨@MulPosStrictMono.toMulPosReflectLE _ _ _ _, @MulPosReflectLE.toMulPosStrictMono _ _ _ _⟩

theorem PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).2 ContravariantClass.elim⟩

theorem MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).2 ContravariantClass.elim⟩

theorem PosMulMono.toPosMulReflectLT [PosMulMono α] : PosMulReflectLT α :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).1 CovariantClass.elim⟩

theorem MulPosMono.toMulPosReflectLT [MulPosMono α] : MulPosReflectLT α :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).1 CovariantClass.elim⟩

/- TODO: Currently, only one in four of the above are made instances; we could consider making
  both directions of `covariant_le_iff_contravariant_lt` and `covariant_lt_iff_contravariant_le`
  instances, then all of the above become redundant instances, but there are performance issues. -/

theorem posMulMono_iff_posMulReflectLT : PosMulMono α ↔ PosMulReflectLT α :=
  ⟨@PosMulMono.toPosMulReflectLT _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩

theorem mulPosMono_iff_mulPosReflectLT : MulPosMono α ↔ MulPosReflectLT α :=
  ⟨@MulPosMono.toMulPosReflectLT _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩

end LinearOrder

end MulZero

section MulZeroClass

variable [MulZeroClass α]

section Preorder

variable [Preorder α]

/-- Assumes left covariance. -/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos

theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp]
theorem mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a) :
    0 < a * b ↔ 0 < b := by simpa using mul_lt_mul_left (b := 0) h

/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp]
theorem mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b) :
    0 < a * b ↔ 0 < a := by simpa using mul_lt_mul_right (b := 0) h

/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias mul_nonneg := Left.mul_nonneg

theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

theorem mul_le_mul_of_le_of_le [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a)
    (d0 : 0 ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans <| mul_le_mul_of_nonneg_right h₁ d0

@[gcongr]
theorem mul_le_mul [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c)
    (b0 : 0 ≤ b) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans <| mul_le_mul_of_nonneg_left h₂ b0

theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  mul_le_mul hab hab ha <| ha.trans hab

theorem mul_le_of_mul_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hle : d ≤ b)
    (a0 : 0 ≤ a) : a * d ≤ c :=
  (mul_le_mul_of_nonneg_left hle a0).trans h

theorem le_mul_of_le_mul_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ d)
    (b0 : 0 ≤ b) : a ≤ b * d :=
  h.trans (mul_le_mul_of_nonneg_left hle b0)

theorem mul_le_of_mul_le_of_nonneg_right [MulPosMono α] (h : a * b ≤ c) (hle : d ≤ a)
    (b0 : 0 ≤ b) : d * b ≤ c :=
  (mul_le_mul_of_nonneg_right hle b0).trans h

theorem le_mul_of_le_mul_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ d)
    (c0 : 0 ≤ c) : a ≤ d * c :=
  h.trans (mul_le_mul_of_nonneg_right hle c0)

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨@PosMulMono.to_covariantClass_pos_mul_le _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      · simp [← ha]
      · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ h ⟩⟩

theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨@MulPosMono.to_covariantClass_pos_mul_le _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      · simp [← ha]
      · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ h ⟩⟩

theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      · simp [← ha] at h
      · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h ⟩⟩

theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      · simp [← ha] at h
      · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h ⟩⟩

-- Porting note: mathlib3 proofs would look like `StrictMono.monotone <| @CovariantClass.elim ..`
-- but implicit argument handling causes that to break
-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- Porting note: mathlib3 proofs would look like `StrictMono.monotone <| @CovariantClass.elim ..`
-- but implicit argument handling causes that to break
-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosMulReflectLT [PosMulReflectLE α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toMulPosReflectLT [MulPosReflectLE α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

theorem mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <|
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩

theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <|
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩

theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_le (mul_le_mul_of_nonneg_right hab d0.le)

theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le).trans_lt (mul_lt_mul_of_pos_left hcd b0)

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb


theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_le ha).2

theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_le ha).1

theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩

theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Left.mul_nonneg h1 h2).not_lt h

theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Right.mul_nonneg h1 h2).not_lt h

theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun h2 : a ≥ 0 => (Left.mul_nonneg h2 h1).not_lt h

theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun h2 : a ≥ 0 => (Right.mul_nonneg h2 h1).not_lt h

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α]

section Preorder

variable [Preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`,
which assume left covariance. -/


@[simp]
lemma le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)

@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)

@[simp]
lemma mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)

@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
which assume right covariance. -/


@[simp]
lemma le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right a0)

@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right a0)

@[simp]
lemma mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right b0)

@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right b0)

/-! Lemmas of the form `b ≤ 1 → a * b ≤ a`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `Mathlib/Algebra/Order/Ring/Defs`
(which imports this file) as they need additional results which are not yet available here. -/

theorem mul_le_of_le_one_right [PosMulMono α] (a0 : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h a0

theorem le_mul_of_one_le_right [PosMulMono α] (a0 : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h a0

theorem mul_le_of_le_one_left [MulPosMono α] (b0 : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h b0

theorem le_mul_of_one_le_left [MulPosMono α] (b0 : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h b0

theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (a0 : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h a0

theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (a0 : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h a0

theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (b0 : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h b0

theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (b0 : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h b0

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`. -/

@[deprecated (since := "2024-07-13")]
theorem mul_le_of_le_of_le_one_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a ≤ c :=
  (mul_le_of_le_one_right hb ha).trans h

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : a < 1) (b0 : 0 < b) :
    b * a < c :=
  (mul_lt_of_lt_one_right b0 ha).trans_le bc

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (h : b < c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a < c :=
  (mul_le_of_le_one_right hb ha).trans_lt h

@[deprecated (since := "2024-07-13")]
theorem mul_le_of_le_of_le_one' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : a ≤ 1) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : b * a ≤ c :=
  (mul_le_mul_of_nonneg_right bc a0).trans <| mul_le_of_le_one_right c0 ha

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_lt_of_le_one' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_le_of_lt_one' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : a < 1)
    (a0 : 0 ≤ a) (c0 : 0 < c) : b * a < c :=
  (mul_le_mul_of_nonneg_right bc a0).trans_lt <| mul_lt_of_lt_one_right c0 ha

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_lt_of_lt_one_of_pos [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`. -/


@[deprecated (since := "2024-07-13")]
theorem le_mul_of_le_of_one_le_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b ≤ c * a :=
  h.trans <| le_mul_of_one_le_right hc ha

@[deprecated (since := "2024-07-13")]
theorem lt_mul_of_le_of_one_lt_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : 1 < a) (c0 : 0 < c) :
    b < c * a :=
  bc.trans_lt <| lt_mul_of_one_lt_right c0 ha

@[deprecated (since := "2024-07-13")]
theorem lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (h : b < c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b < c * a :=
  h.trans_le <| le_mul_of_one_le_right hc ha

@[deprecated (since := "2024-07-13")]
theorem le_mul_of_le_of_one_le' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 ≤ a)
    (a0 : 0 ≤ a) (b0 : 0 ≤ b) : b ≤ c * a :=
  (le_mul_of_one_le_right b0 ha).trans <| mul_le_mul_of_nonneg_right bc a0

@[deprecated (since := "2024-07-13")]
theorem lt_mul_of_le_of_one_lt' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 < a)
    (a0 : 0 ≤ a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans_le <| mul_le_mul_of_nonneg_right bc a0

@[deprecated (since := "2024-07-13")]
theorem lt_mul_of_lt_of_one_le' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : 1 ≤ a)
    (a0 : 0 < a) (b0 : 0 ≤ b) : b < c * a :=
  (le_mul_of_one_le_right b0 ha).trans_lt <| mul_lt_mul_of_pos_right bc a0

@[deprecated (since := "2024-07-13")]
theorem lt_mul_of_lt_of_one_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (bc : b < c)
    (ha : 1 < a) (a0 : 0 < a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans <| mul_lt_mul_of_pos_right bc a0

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`. -/


@[deprecated (since := "2024-07-13")]
theorem mul_le_of_le_one_of_le_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b ≤ c) (hb : 0 ≤ b) :
    a * b ≤ c :=
  (mul_le_of_le_one_left hb ha).trans h

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_lt_one_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (h : b ≤ c) (hb : 0 < b) :
    a * b < c :=
  (mul_lt_of_lt_one_left hb ha).trans_le h

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_le_one_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b < c) (hb : 0 ≤ b) :
    a * b < c :=
  (mul_le_of_le_one_left hb ha).trans_lt h

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_lt_one_of_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (ha : a < 1)
    (bc : b < c) (a0 : 0 < a) (c0 : 0 < c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans <| mul_lt_of_lt_one_left c0 ha

@[deprecated (since := "2024-07-13")]
theorem mul_le_of_le_one_of_le' [PosMulMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b ≤ c) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : a * b ≤ c :=
  (mul_le_mul_of_nonneg_left bc a0).trans <| mul_le_of_le_one_left c0 ha

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_lt_one_of_le' [PosMulMono α] [MulPosStrictMono α] (ha : a < 1) (bc : b ≤ c)
    (a0 : 0 ≤ a) (c0 : 0 < c) : a * b < c :=
  (mul_le_mul_of_nonneg_left bc a0).trans_lt <| mul_lt_of_lt_one_left c0 ha

@[deprecated (since := "2024-07-13")]
theorem mul_lt_of_le_one_of_lt' [PosMulStrictMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b < c)
    (a0 : 0 < a) (c0 : 0 ≤ c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans_le <| mul_le_of_le_one_left c0 ha

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`. -/


@[deprecated (since := "2024-07-13")]
theorem lt_mul_of_one_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b ≤ c) (hc : 0 < c) :
    b < a * c :=
  h.trans_lt <| lt_mul_of_one_lt_left hc ha

@[deprecated (since := "2024-07-13")]
theorem lt_mul_of_one_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha

@[deprecated (since := "2024-07-13")]
theorem lt_mul_of_one_lt_of_lt_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b < c) (hc : 0 < c) :
    b < a * c :=
  h.trans <| lt_mul_of_one_lt_left hc ha

@[deprecated (since := "2024-07-13")]
theorem lt_mul_of_one_lt_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha

@[deprecated (since := "2024-07-13")]
theorem lt_of_mul_lt_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : 1 ≤ b)
    (ha : 0 ≤ a) : a < c :=
  (le_mul_of_one_le_right ha hle).trans_lt h

@[deprecated (since := "2024-07-13")]
theorem lt_of_lt_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a < b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a < b :=
  h.trans_le <| mul_le_of_le_one_right hb hc

@[deprecated (since := "2024-07-13")]
theorem lt_of_lt_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a < b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a < c :=
  h.trans_le <| mul_le_of_le_one_left hc hb

@[deprecated (since := "2024-07-13")]
theorem le_mul_of_one_le_of_le_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c) :
    b ≤ a * c :=
  bc.trans <| le_mul_of_one_le_left c0 ha

@[deprecated (since := "2024-07-13")]
theorem le_of_mul_le_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hb : 1 ≤ b)
    (ha : 0 ≤ a) : a ≤ c :=
  (le_mul_of_one_le_right ha hb).trans h

@[deprecated (since := "2024-07-13")]
theorem le_of_le_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a ≤ b :=
  h.trans <| mul_le_of_le_one_right hb hc

@[deprecated (since := "2024-07-13")]
theorem le_of_mul_le_of_one_le_nonneg_right [MulPosMono α] (h : a * b ≤ c) (ha : 1 ≤ a)
    (hb : 0 ≤ b) : b ≤ c :=
  (le_mul_of_one_le_left hb ha).trans h

@[deprecated (since := "2024-07-13")]
theorem le_of_le_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a ≤ c :=
  h.trans <| mul_le_of_le_one_left hc hb


/-! Lemmas of the form `a ≤ 1 → b ≤ 1 → a * b ≤ 1`. -/

/-- Assumes left covariance. -/
theorem mul_le_one_left [PosMulMono α]
    (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 ≤ a) : a * b ≤ 1 :=
  (mul_le_of_le_one_right a0 hb).trans ha

@[deprecated (since := "2024-07-13")]
alias Left.mul_le_one_of_le_of_le := mul_le_one_left

/-- Assumes left covariance. -/
theorem mul_lt_one_of_le_of_lt_left [PosMulStrictMono α]
    (ha : a ≤ 1) (hb : b < 1) (a0 : 0 < a) : a * b < 1 :=
  (mul_lt_of_lt_one_right a0 hb).trans_le ha

@[deprecated (since := "2024-07-13")]
alias Left.mul_lt_of_le_of_lt_one_of_pos := mul_lt_one_of_le_of_lt_left

/-- Assumes left covariance. -/
theorem mul_lt_one_of_lt_of_le_left [PosMulMono α]
    (ha : a < 1) (hb : b ≤ 1) (a0 : 0 ≤ a) : a * b < 1 :=
  (mul_le_of_le_one_right a0 hb).trans_lt ha

@[deprecated (since := "2024-07-13")]
alias Left.mul_lt_of_lt_of_le_one_of_nonneg := mul_lt_one_of_lt_of_le_left

/-- Assumes left covariance. -/
theorem mul_lt_one_left [PosMulStrictMono α]
    (ha : a < 1) (hb : b < 1) (a0 : 0 < a) : a * b < 1 :=
  (mul_lt_of_lt_one_right a0 hb).trans ha

/-- Assumes right covariance. -/
theorem mul_le_one_right [MulPosMono α]
    (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 ≤ b) : a * b ≤ 1 :=
  (mul_le_of_le_one_left b0 ha).trans hb

@[deprecated (since := "2024-07-13")]
alias Right.mul_le_one_of_le_of_le := mul_le_one_right

/-- Assumes right covariance. -/
theorem mul_lt_one_of_lt_of_le_right [MulPosStrictMono α]
    (ha : a < 1) (hb : b ≤ 1) (b0 : 0 < b) : a * b < 1 :=
  (mul_lt_of_lt_one_left b0 ha).trans_le hb

@[deprecated (since := "2024-07-13")]
alias Right.mul_lt_one_of_lt_of_le_of_pos := mul_lt_one_of_lt_of_le_right

/-- Assumes right covariance. -/
theorem mul_lt_one_of_le_of_lt_right [MulPosMono α]
    (ha : a ≤ 1) (hb : b < 1) (b0 : 0 ≤ b) : a * b < 1 :=
  (mul_le_of_le_one_left b0 ha).trans_lt hb

@[deprecated (since := "2024-07-13")]
alias Right.mul_lt_one_of_le_of_lt_of_nonneg := mul_lt_one_of_lt_of_le_right

/-- Assumes right covariance. -/
theorem mul_lt_one_right [MulPosStrictMono α]
    (ha : a < 1) (hb : b < 1) (b0 : 0 < b) : a * b < 1 :=
  (mul_lt_of_lt_one_left b0 ha).trans hb

theorem mul_le_one [MulPosMono α] (ha : a ≤ 1) (hb' : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  mul_le_one_right ha hb hb'

theorem mul_lt_one_of_nonneg_of_lt_one_left [PosMulMono α]
    (ha₀ : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
  mul_lt_one_of_lt_of_le_left ha hb ha₀

theorem mul_lt_one_of_nonneg_of_lt_one_right [MulPosMono α]
    (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) : a * b < 1 :=
  mul_lt_one_of_le_of_lt_right ha hb hb₀

/-! Lemmas of the form `1 ≤ a → 1 ≤ b → 1 ≤ a * b`. -/

/-- Assumes left covariance. -/
theorem Left.one_le_mul₀ [PosMulMono α] [ZeroLEOneClass α]
    (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  ha.trans (le_mul_of_one_le_right (zero_le_one.trans ha) hb)

-- See `Left.one_lt_mul_of_le_of_lt₀` for `1 ≤ a → 1 < b → 1 < a * b`
-- It's not here because we do not have `ZeroLTOneClass`. We need `PartialOrder` to show `0 < 1`.

/-- Assumes left covariance. -/
theorem Left.one_lt_mul_of_lt_of_le₀ [PosMulMono α] [ZeroLEOneClass α]
    (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
  ha.trans_le (le_mul_of_one_le_right (zero_le_one.trans ha.le) hb)

/-- Assumes left covariance. -/
theorem Left.one_lt_mul₀ [PosMulStrictMono α] [ZeroLEOneClass α]
    (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
  ha.trans (lt_mul_of_one_lt_right (zero_le_one.trans_lt ha) hb)

/-- Assumes right covariance. -/
theorem Right.one_le_mul₀ [MulPosMono α] [ZeroLEOneClass α]
    (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  hb.trans (le_mul_of_one_le_left (zero_le_one.trans hb) ha)

-- See `Right.one_lt_mul_of_lt_of_le₀` for `1 < a → 1 ≤ b → 1 < a * b`
-- It's not here because we do not have `ZeroLTOneClass`. We need `PartialOrder` to show `0 < 1`.

/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_le_of_lt₀ [MulPosMono α] [ZeroLEOneClass α]
    (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
  hb.trans_le (le_mul_of_one_le_left (zero_le_one.trans hb.le) ha)

/-- Assumes right covariance. -/
theorem Right.one_lt_mul₀ [MulPosStrictMono α] [ZeroLEOneClass α]
    (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
  hb.trans (lt_mul_of_one_lt_left (zero_le_one.trans_lt hb) ha)

alias one_le_mul_of_le_of_le := Left.one_le_mul₀
alias one_lt_mul_of_le_of_lt := Right.one_lt_mul_of_le_of_lt₀
alias one_lt_mul_of_lt_of_le := Left.one_lt_mul_of_lt_of_le₀
alias one_lt_mul_of_lt_of_lt := Left.one_lt_mul₀

alias one_le_mul_of_one_le_of_one_le := one_le_mul_of_le_of_le
alias one_lt_mul := one_lt_mul_of_le_of_lt

end Preorder

section PartialOrder

variable [PartialOrder α]

/-- Assumes left covariance. -/
theorem Left.one_lt_mul_of_le_of_lt₀ [PosMulStrictMono α] [ZeroLEOneClass α] [NeZero (1 : α)]
    (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
  ha.trans_lt (lt_mul_of_one_lt_right (zero_lt_one.trans_le ha) hb)

/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_lt_of_le₀ [MulPosStrictMono α] [ZeroLEOneClass α] [NeZero (1 : α)]
    (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
  hb.trans_lt (lt_mul_of_one_lt_left (zero_lt_one.trans_le hb) ha)

end PartialOrder

/-- Assumes left covariance. -/
@[deprecated Left.one_lt_mul_of_le_of_lt₀ (since := "2024-07-13")]
theorem Left.one_lt_mul_of_le_of_lt_of_pos [MulOneClass α] [Zero α] [Preorder α]
    [PosMulStrictMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (a0 : 0 < a) : 1 < a * b :=
  ha.trans_lt <| lt_mul_of_one_lt_right a0 hb

/-- Assumes left covariance. -/
@[deprecated Left.one_lt_mul_of_lt_of_le₀ (since := "2024-07-13")]
theorem Left.lt_mul_of_lt_of_one_le_of_nonneg [MulOneClass α] [Zero α] [Preorder α]
    [PosMulMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (a0 : 0 ≤ a) : 1 < a * b :=
  ha.trans_le <| le_mul_of_one_le_right a0 hb

/-- Assumes right covariance. -/
@[deprecated Right.one_lt_mul_of_lt_of_le₀ (since := "2024-07-13")]
theorem Right.one_lt_mul_of_lt_of_le_of_pos [MulOneClass α] [Zero α] [Preorder α]
    [MulPosStrictMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (b0 : 0 < b) : 1 < a * b :=
  hb.trans_lt <| lt_mul_of_one_lt_left b0 ha

/-- Assumes right covariance. -/
@[deprecated Right.one_lt_mul_of_le_of_lt₀ (since := "2024-07-13")]
theorem Right.one_lt_mul_of_le_of_lt_of_nonneg [MulOneClass α] [Zero α] [Preorder α]
    [MulPosMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (b0 : 0 ≤ b) : 1 < a * b :=
  hb.trans_le <| le_mul_of_one_le_left b0 ha

section LinearOrder

variable [LinearOrder α]

@[deprecated (since := "2024-07-13")]
theorem exists_square_le' [PosMulStrictMono α] (a0 : 0 < a) : ∃ b : α, b * b ≤ a := by
  obtain ha | ha := lt_or_le a 1
  · exact ⟨a, (mul_lt_of_lt_one_right a0 ha).le⟩
  · exact ⟨1, by rwa [mul_one]⟩

end LinearOrder

end MulOneClass

section MulZeroOneClass

variable [MulZeroOneClass α]

section Preorder

variable [Preorder α]

theorem Left.zero_lt_one_of_pos [PosMulReflectLT α]
    (a0 : 0 < a) : (0 : α) < 1 :=
  lt_of_mul_lt_mul_left ((mul_zero _).le.trans_lt (a0.trans_le (mul_one _).ge)) a0.le

theorem Right.zero_lt_one_of_pos [MulPosReflectLT α]
    (a0 : 0 < a) : (0 : α) < 1 :=
  lt_of_mul_lt_mul_right ((zero_mul _).le.trans_lt (a0.trans_le (one_mul _).ge)) a0.le

alias zero_lt_one_of_pos := Left.zero_lt_one_of_pos

end Preorder

end MulZeroOneClass

section CancelMonoidWithZero

variable [CancelMonoidWithZero α]

section PartialOrder

variable [PartialOrder α]

theorem PosMulMono.toPosMulStrictMono [PosMulMono α] : PosMulStrictMono α :=
  ⟨fun x _ _ h => (mul_le_mul_of_nonneg_left h.le x.2.le).lt_of_ne
    (h.ne ∘ mul_left_cancel₀ x.2.ne')⟩

theorem posMulMono_iff_posMulStrictMono : PosMulMono α ↔ PosMulStrictMono α :=
  ⟨@PosMulMono.toPosMulStrictMono α _ _, @PosMulStrictMono.toPosMulMono α _ _⟩

theorem MulPosMono.toMulPosStrictMono [MulPosMono α] : MulPosStrictMono α :=
  ⟨fun x _ _ h => (mul_le_mul_of_nonneg_right h.le x.2.le).lt_of_ne
    (h.ne ∘ mul_right_cancel₀ x.2.ne')⟩

theorem mulPosMono_iff_mulPosStrictMono : MulPosMono α ↔ MulPosStrictMono α :=
  ⟨@MulPosMono.toMulPosStrictMono α _ _, @MulPosStrictMono.toMulPosMono α _ _⟩

theorem PosMulReflectLT.toPosMulReflectLE [PosMulReflectLT α] : PosMulReflectLE α :=
  ⟨fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le⟩

theorem posMulReflectLE_iff_posMulReflectLT : PosMulReflectLE α ↔ PosMulReflectLT α :=
  ⟨@PosMulReflectLE.toPosMulReflectLT α _ _, @PosMulReflectLT.toPosMulReflectLE α _ _⟩

theorem MulPosReflectLT.toMulPosReflectLE [MulPosReflectLT α] : MulPosReflectLE α :=
  ⟨fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le⟩

theorem mulPosReflectLE_iff_mulPosReflectLT : MulPosReflectLE α ↔ MulPosReflectLT α :=
  ⟨@MulPosReflectLE.toMulPosReflectLT α _ _, @MulPosReflectLT.toMulPosReflectLE α _ _⟩

end PartialOrder

end CancelMonoidWithZero

section CommSemigroupHasZero

variable [Mul α] [IsSymmOp α α (· * ·)] [Zero α] [Preorder α]

theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp only [PosMulStrictMono, MulPosStrictMono, IsSymmOp.symm_op]

theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp only [PosMulReflectLT, MulPosReflectLT, IsSymmOp.symm_op]

theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by
  simp only [PosMulMono, MulPosMono, IsSymmOp.symm_op]

theorem posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE α := by
  simp only [PosMulReflectLE, MulPosReflectLE, IsSymmOp.symm_op]

end CommSemigroupHasZero
