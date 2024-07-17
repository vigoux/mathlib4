/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

#align_import algebra.order.ring.char_zero from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"
#align_import algebra.order.ring.defs from "leanprover-community/mathlib"@"44e29dbcff83ba7114a464d592b8c3743987c1e5"

/-!
# Ordered rings and semirings

This file develops the basics of ordered (semi)rings.

Each typeclass here comprises
* an algebraic class (`Semiring`, `CommSemiring`, `Ring`, `CommRing`)
* an order class (`PartialOrder`, `LinearOrder`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`+` respects `<`" means "strict monotonicity of addition"
* "`*` respects `≤`" means "monotonicity of multiplication by a nonnegative number".
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses

* `OrderedSemiring`: Semiring with a partial order such that `+` and `*` respect `≤`.
* `StrictOrderedSemiring`: Nontrivial semiring with a partial order such that `+` and `*` respects
  `<`.
* `OrderedCommSemiring`: Commutative semiring with a partial order such that `+` and `*` respect
  `≤`.
* `StrictOrderedCommSemiring`: Nontrivial commutative semiring with a partial order such that `+`
  and `*` respect `<`.
* `OrderedRing`: Ring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `OrderedCommRing`: Commutative ring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `LinearOrderedSemiring`: Nontrivial semiring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `LinearOrderedCommSemiring`: Nontrivial commutative semiring with a linear order such that `+`
  respects `≤` and `*` respects `<`.
* `LinearOrderedRing`: Nontrivial ring with a linear order such that `+` respects `≤` and `*`
  respects `<`.
* `LinearOrderedCommRing`: Nontrivial commutative ring with a linear order such that `+` respects
  `≤` and `*` respects `<`.
* `CanonicallyOrderedCommSemiring`: Commutative semiring with a partial order such that `+`
  respects `≤`, `*` respects `<`, and `a ≤ b ↔ ∃ c, b = a + c`.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `OrderedSemiring`
  - `OrderedAddCommMonoid` & multiplication & `*` respects `≤`
  - `Semiring` & partial order structure & `+` respects `≤` & `*` respects `≤`
* `StrictOrderedSemiring`
  - `OrderedCancelAddCommMonoid` & multiplication & `*` respects `<` & nontriviality
  - `OrderedSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedCommSemiring`
  - `OrderedSemiring` & commutativity of multiplication
  - `CommSemiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedCommSemiring`
  - `StrictOrderedSemiring` & commutativity of multiplication
  - `OrderedCommSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedRing`
  - `OrderedSemiring` & additive inverses
  - `OrderedAddCommGroup` & multiplication & `*` respects `<`
  - `Ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedRing`
  - `StrictOrderedSemiring` & additive inverses
  - `OrderedSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedCommRing`
  - `OrderedRing` & commutativity of multiplication
  - `OrderedCommSemiring` & additive inverses
  - `CommRing` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedCommRing`
  - `StrictOrderedCommSemiring` & additive inverses
  - `StrictOrderedRing` & commutativity of multiplication
  - `OrderedCommRing` & `+` respects `<` & `*` respects `<` & nontriviality
* `LinearOrderedSemiring`
  - `StrictOrderedSemiring` & totality of the order
  - `LinearOrderedAddCommMonoid` & multiplication & nontriviality & `*` respects `<`
* `LinearOrderedCommSemiring`
  - `StrictOrderedCommSemiring` & totality of the order
  - `LinearOrderedSemiring` & commutativity of multiplication
* `LinearOrderedRing`
  - `StrictOrderedRing` & totality of the order
  - `LinearOrderedSemiring` & additive inverses
  - `LinearOrderedAddCommGroup` & multiplication & `*` respects `<`
  - `Ring` & `IsDomain` & linear order structure
* `LinearOrderedCommRing`
  - `StrictOrderedCommRing` & totality of the order
  - `LinearOrderedRing` & commutativity of multiplication
  - `LinearOrderedCommSemiring` & additive inverses
  - `CommRing` & `IsDomain` & linear order structure
-/

open Function

universe u

variable {α : Type u} {β : Type*}

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/

/-- An `OrderedSemiring` is a semiring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
class OrderedSemiring (α : Type u) extends Semiring α, OrderedAddCommMonoid α where
  /-- `0 ≤ 1` in any ordered semiring. -/
  protected zero_le_one : (0 : α) ≤ 1
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the left
  by a non-negative element `0 ≤ c` to obtain `c * a ≤ c * b`. -/
  protected mul_le_mul_of_nonneg_left : ∀ a b c : α, a ≤ b → 0 ≤ c → c * a ≤ c * b
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the right
  by a non-negative element `0 ≤ c` to obtain `a * c ≤ b * c`. -/
  protected mul_le_mul_of_nonneg_right : ∀ a b c : α, a ≤ b → 0 ≤ c → a * c ≤ b * c
#align ordered_semiring OrderedSemiring

/-- An `OrderedCommSemiring` is a commutative semiring with a partial order such that addition is
monotone and multiplication by a nonnegative number is monotone. -/
class OrderedCommSemiring (α : Type u) extends OrderedSemiring α, CommSemiring α where
  mul_le_mul_of_nonneg_right a b c ha hc :=
    -- parentheses ensure this generates an `optParam` rather than an `autoParam`
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left a b c ha hc)
#align ordered_comm_semiring OrderedCommSemiring

/-- An `OrderedRing` is a ring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
class OrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α where
  /-- `0 ≤ 1` in any ordered ring. -/
  protected zero_le_one : 0 ≤ (1 : α)
  /-- The product of non-negative elements is non-negative. -/
  protected mul_nonneg : ∀ a b : α, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
#align ordered_ring OrderedRing

/-- An `OrderedCommRing` is a commutative ring with a partial order such that addition is monotone
and multiplication by a nonnegative number is monotone. -/
class OrderedCommRing (α : Type u) extends OrderedRing α, CommRing α
#align ordered_comm_ring OrderedCommRing

/-- A `StrictOrderedSemiring` is a nontrivial semiring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
class StrictOrderedSemiring (α : Type u) extends Semiring α, OrderedCancelAddCommMonoid α,
    Nontrivial α where
  /-- In a strict ordered semiring, `0 ≤ 1`. -/
  protected zero_le_one : (0 : α) ≤ 1
  /-- Left multiplication by a positive element is strictly monotone. -/
  protected mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b
  /-- Right multiplication by a positive element is strictly monotone. -/
  protected mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c
#align strict_ordered_semiring StrictOrderedSemiring

/-- A `StrictOrderedCommSemiring` is a commutative semiring with a partial order such that
addition is strictly monotone and multiplication by a positive number is strictly monotone. -/
class StrictOrderedCommSemiring (α : Type u) extends StrictOrderedSemiring α, CommSemiring α
#align strict_ordered_comm_semiring StrictOrderedCommSemiring

/-- A `StrictOrderedRing` is a ring with a partial order such that addition is strictly monotone
and multiplication by a positive number is strictly monotone. -/
class StrictOrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α, Nontrivial α where
  /-- In a strict ordered ring, `0 ≤ 1`. -/
  protected zero_le_one : 0 ≤ (1 : α)
  /-- The product of two positive elements is positive. -/
  protected mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b
#align strict_ordered_ring StrictOrderedRing

/-- A `StrictOrderedCommRing` is a commutative ring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
class StrictOrderedCommRing (α : Type*) extends StrictOrderedRing α, CommRing α
#align strict_ordered_comm_ring StrictOrderedCommRing

/- It's not entirely clear we should assume `Nontrivial` at this point; it would be reasonable to
explore changing this, but be warned that the instances involving `Domain` may cause typeclass
search loops. -/
/-- A `LinearOrderedSemiring` is a nontrivial semiring with a linear order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
class LinearOrderedSemiring (α : Type u) extends StrictOrderedSemiring α,
  LinearOrderedAddCommMonoid α
#align linear_ordered_semiring LinearOrderedSemiring

/-- A `LinearOrderedCommSemiring` is a nontrivial commutative semiring with a linear order such
that addition is monotone and multiplication by a positive number is strictly monotone. -/
class LinearOrderedCommSemiring (α : Type*) extends StrictOrderedCommSemiring α,
  LinearOrderedSemiring α
#align linear_ordered_comm_semiring LinearOrderedCommSemiring

/-- A `LinearOrderedRing` is a ring with a linear order such that addition is monotone and
multiplication by a positive number is strictly monotone. -/
class LinearOrderedRing (α : Type u) extends StrictOrderedRing α, LinearOrder α
#align linear_ordered_ring LinearOrderedRing

/-- A `LinearOrderedCommRing` is a commutative ring with a linear order such that addition is
monotone and multiplication by a positive number is strictly monotone. -/
class LinearOrderedCommRing (α : Type u) extends LinearOrderedRing α, CommMonoid α
#align linear_ordered_comm_ring LinearOrderedCommRing

section OrderedSemiring

variable [OrderedSemiring α] {a b c d : α}
-- see Note [lower instance priority]
instance (priority := 100) OrderedSemiring.zeroLEOneClass : ZeroLEOneClass α :=
  { ‹OrderedSemiring α› with }
#align ordered_semiring.zero_le_one_class OrderedSemiring.zeroLEOneClass

-- see Note [lower instance priority]
instance (priority := 200) OrderedSemiring.toPosMulMono : PosMulMono α :=
  ⟨fun x _ _ h => OrderedSemiring.mul_le_mul_of_nonneg_left _ _ _ h x.2⟩
#align ordered_semiring.to_pos_mul_mono OrderedSemiring.toPosMulMono

-- see Note [lower instance priority]
instance (priority := 200) OrderedSemiring.toMulPosMono : MulPosMono α :=
  ⟨fun x _ _ h => OrderedSemiring.mul_le_mul_of_nonneg_right _ _ _ h x.2⟩
#align ordered_semiring.to_mul_pos_mono OrderedSemiring.toMulPosMono

end OrderedSemiring

section OrderedRing

variable [OrderedRing α] {a b c d : α}

-- see Note [lower instance priority]
instance (priority := 100) OrderedRing.toOrderedSemiring : OrderedSemiring α :=
  { ‹OrderedRing α›, (Ring.toSemiring : Semiring α) with
    mul_le_mul_of_nonneg_left := fun a b c h hc => by
      simpa only [mul_sub, sub_nonneg] using OrderedRing.mul_nonneg _ _ hc (sub_nonneg.2 h),
    mul_le_mul_of_nonneg_right := fun a b c h hc => by
      simpa only [sub_mul, sub_nonneg] using OrderedRing.mul_nonneg _ _ (sub_nonneg.2 h) hc }
#align ordered_ring.to_ordered_semiring OrderedRing.toOrderedSemiring

end OrderedRing

section OrderedCommRing

variable [OrderedCommRing α]

-- See note [lower instance priority]
instance (priority := 100) OrderedCommRing.toOrderedCommSemiring : OrderedCommSemiring α :=
  { OrderedRing.toOrderedSemiring, ‹OrderedCommRing α› with }
#align ordered_comm_ring.to_ordered_comm_semiring OrderedCommRing.toOrderedCommSemiring

end OrderedCommRing

section StrictOrderedSemiring

variable [StrictOrderedSemiring α] {a b c d : α}

-- see Note [lower instance priority]
instance (priority := 200) StrictOrderedSemiring.toPosMulStrictMono : PosMulStrictMono α :=
  ⟨fun x _ _ h => StrictOrderedSemiring.mul_lt_mul_of_pos_left _ _ _ h x.prop⟩
#align strict_ordered_semiring.to_pos_mul_strict_mono StrictOrderedSemiring.toPosMulStrictMono

-- see Note [lower instance priority]
instance (priority := 200) StrictOrderedSemiring.toMulPosStrictMono : MulPosStrictMono α :=
  ⟨fun x _ _ h => StrictOrderedSemiring.mul_lt_mul_of_pos_right _ _ _ h x.prop⟩
#align strict_ordered_semiring.to_mul_pos_strict_mono StrictOrderedSemiring.toMulPosStrictMono

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedSemiring.toOrderedSemiring` to avoid using choice in
basic `Nat` lemmas. -/
abbrev StrictOrderedSemiring.toOrderedSemiring' [@DecidableRel α (· ≤ ·)] : OrderedSemiring α :=
  { ‹StrictOrderedSemiring α› with
    mul_le_mul_of_nonneg_left := fun a b c hab hc => by
      obtain rfl | hab := Decidable.eq_or_lt_of_le hab
      · rfl
      obtain rfl | hc := Decidable.eq_or_lt_of_le hc
      · simp
      · exact (mul_lt_mul_of_pos_left hab hc).le,
    mul_le_mul_of_nonneg_right := fun a b c hab hc => by
      obtain rfl | hab := Decidable.eq_or_lt_of_le hab
      · rfl
      obtain rfl | hc := Decidable.eq_or_lt_of_le hc
      · simp
      · exact (mul_lt_mul_of_pos_right hab hc).le }
#align strict_ordered_semiring.to_ordered_semiring' StrictOrderedSemiring.toOrderedSemiring'

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.toOrderedSemiring : OrderedSemiring α :=
  { ‹StrictOrderedSemiring α› with
    mul_le_mul_of_nonneg_left := fun _ _ _ =>
      letI := @StrictOrderedSemiring.toOrderedSemiring' α _ (Classical.decRel _)
      mul_le_mul_of_nonneg_left,
    mul_le_mul_of_nonneg_right := fun _ _ _ =>
      letI := @StrictOrderedSemiring.toOrderedSemiring' α _ (Classical.decRel _)
      mul_le_mul_of_nonneg_right }
#align strict_ordered_semiring.to_ordered_semiring StrictOrderedSemiring.toOrderedSemiring

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.toCharZero [StrictOrderedSemiring α] :
    CharZero α where
  cast_injective :=
    (strictMono_nat_of_lt_succ fun n ↦ by rw [Nat.cast_succ]; apply lt_add_one).injective
#align strict_ordered_semiring.to_char_zero StrictOrderedSemiring.toCharZero

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.toNoMaxOrder : NoMaxOrder α :=
  ⟨fun a => ⟨a + 1, lt_add_of_pos_right _ one_pos⟩⟩
#align strict_ordered_semiring.to_no_max_order StrictOrderedSemiring.toNoMaxOrder

end StrictOrderedSemiring

section StrictOrderedCommSemiring
variable [StrictOrderedCommSemiring α]

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedCommSemiring.toOrderedCommSemiring'` to avoid using
choice in basic `Nat` lemmas. -/
abbrev StrictOrderedCommSemiring.toOrderedCommSemiring' [@DecidableRel α (· ≤ ·)] :
    OrderedCommSemiring α :=
  { ‹StrictOrderedCommSemiring α›, StrictOrderedSemiring.toOrderedSemiring' with }
#align strict_ordered_comm_semiring.to_ordered_comm_semiring' StrictOrderedCommSemiring.toOrderedCommSemiring'

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedCommSemiring.toOrderedCommSemiring :
    OrderedCommSemiring α :=
  { ‹StrictOrderedCommSemiring α›, StrictOrderedSemiring.toOrderedSemiring with }
#align strict_ordered_comm_semiring.to_ordered_comm_semiring StrictOrderedCommSemiring.toOrderedCommSemiring

end StrictOrderedCommSemiring

section StrictOrderedRing
variable [StrictOrderedRing α] {a b c : α}

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedRing.toStrictOrderedSemiring : StrictOrderedSemiring α :=
  { ‹StrictOrderedRing α›, (Ring.toSemiring : Semiring α) with
    le_of_add_le_add_left := @le_of_add_le_add_left α _ _ _,
    mul_lt_mul_of_pos_left := fun a b c h hc => by
      simpa only [mul_sub, sub_pos] using StrictOrderedRing.mul_pos _ _ hc (sub_pos.2 h),
    mul_lt_mul_of_pos_right := fun a b c h hc => by
      simpa only [sub_mul, sub_pos] using StrictOrderedRing.mul_pos _ _ (sub_pos.2 h) hc }
#align strict_ordered_ring.to_strict_ordered_semiring StrictOrderedRing.toStrictOrderedSemiring

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedRing.toOrderedRing` to avoid using choice in basic
`Int` lemmas. -/
abbrev StrictOrderedRing.toOrderedRing' [@DecidableRel α (· ≤ ·)] : OrderedRing α :=
  { ‹StrictOrderedRing α›, (Ring.toSemiring : Semiring α) with
    mul_nonneg := fun a b ha hb => by
      obtain ha | ha := Decidable.eq_or_lt_of_le ha
      · rw [← ha, zero_mul]
      obtain hb | hb := Decidable.eq_or_lt_of_le hb
      · rw [← hb, mul_zero]
      · exact (StrictOrderedRing.mul_pos _ _ ha hb).le }
#align strict_ordered_ring.to_ordered_ring' StrictOrderedRing.toOrderedRing'

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedRing.toOrderedRing : OrderedRing α where
  __ := ‹StrictOrderedRing α›
  mul_nonneg := fun _ _ => mul_nonneg
#align strict_ordered_ring.to_ordered_ring StrictOrderedRing.toOrderedRing

end StrictOrderedRing

section StrictOrderedCommRing

variable [StrictOrderedCommRing α]

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedCommRing.toOrderedCommRing` to avoid using
choice in basic `Int` lemmas. -/
abbrev StrictOrderedCommRing.toOrderedCommRing' [@DecidableRel α (· ≤ ·)] : OrderedCommRing α :=
  { ‹StrictOrderedCommRing α›, StrictOrderedRing.toOrderedRing' with }
#align strict_ordered_comm_ring.to_ordered_comm_ring' StrictOrderedCommRing.toOrderedCommRing'

-- See note [lower instance priority]
instance (priority := 100) StrictOrderedCommRing.toStrictOrderedCommSemiring :
    StrictOrderedCommSemiring α :=
  { ‹StrictOrderedCommRing α›, StrictOrderedRing.toStrictOrderedSemiring with }
#align strict_ordered_comm_ring.to_strict_ordered_comm_semiring StrictOrderedCommRing.toStrictOrderedCommSemiring

-- See note [lower instance priority]
instance (priority := 100) StrictOrderedCommRing.toOrderedCommRing : OrderedCommRing α :=
  { ‹StrictOrderedCommRing α›, StrictOrderedRing.toOrderedRing with }
#align strict_ordered_comm_ring.to_ordered_comm_ring StrictOrderedCommRing.toOrderedCommRing

end StrictOrderedCommRing

section LinearOrderedSemiring

variable [LinearOrderedSemiring α] {a b c d : α}

-- see Note [lower instance priority]
instance (priority := 200) LinearOrderedSemiring.toPosMulReflectLT : PosMulReflectLT α :=
  ⟨fun a _ _ => (monotone_mul_left_of_nonneg a.2).reflect_lt⟩
#align linear_ordered_semiring.to_pos_mul_reflect_lt LinearOrderedSemiring.toPosMulReflectLT

-- see Note [lower instance priority]
instance (priority := 200) LinearOrderedSemiring.toMulPosReflectLT : MulPosReflectLT α :=
  ⟨fun a _ _ => (monotone_mul_right_of_nonneg a.2).reflect_lt⟩
#align linear_ordered_semiring.to_mul_pos_reflect_lt LinearOrderedSemiring.toMulPosReflectLT

attribute [local instance] LinearOrderedSemiring.decidableLE LinearOrderedSemiring.decidableLT

variable [ExistsAddOfLE α]

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedSemiring.noZeroDivisors : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    contrapose! hab
    obtain ha | ha := hab.1.lt_or_lt <;> obtain hb | hb := hab.2.lt_or_lt
    exacts [(mul_pos_of_neg_of_neg ha hb).ne', (mul_neg_of_neg_of_pos ha hb).ne,
      (mul_neg_of_pos_of_neg ha hb).ne, (mul_pos ha hb).ne']
#align linear_ordered_ring.no_zero_divisors LinearOrderedSemiring.noZeroDivisors

-- Note that we can't use `NoZeroDivisors.to_isDomain` since we are merely in a semiring.
-- See note [lower instance priority]
instance (priority := 100) LinearOrderedRing.isDomain : IsDomain α where
  mul_left_cancel_of_ne_zero {a b c} ha h := by
    obtain ha | ha := ha.lt_or_lt
    exacts [(strictAnti_mul_left ha).injective h, (strictMono_mul_left_of_pos ha).injective h]
  mul_right_cancel_of_ne_zero {b a c} ha h := by
    obtain ha | ha := ha.lt_or_lt
    exacts [(strictAnti_mul_right ha).injective h, (strictMono_mul_right_of_pos ha).injective h]
#align linear_ordered_ring.is_domain LinearOrderedRing.isDomain

end LinearOrderedSemiring

section LinearOrderedCommSemiring
variable [LinearOrderedCommSemiring α] {a b c d : α}

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommSemiring.toLinearOrderedCancelAddCommMonoid :
    LinearOrderedCancelAddCommMonoid α where __ := ‹LinearOrderedCommSemiring α›
#align linear_ordered_comm_semiring.to_linear_ordered_cancel_add_comm_monoid LinearOrderedCommSemiring.toLinearOrderedCancelAddCommMonoid

end LinearOrderedCommSemiring

section LinearOrderedRing
variable [LinearOrderedRing α] {a b c : α}

attribute [local instance] LinearOrderedRing.decidableLE LinearOrderedRing.decidableLT

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.toLinearOrderedSemiring : LinearOrderedSemiring α :=
  { ‹LinearOrderedRing α›, StrictOrderedRing.toStrictOrderedSemiring with }
#align linear_ordered_ring.to_linear_ordered_semiring LinearOrderedRing.toLinearOrderedSemiring

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.toLinearOrderedAddCommGroup :
    LinearOrderedAddCommGroup α where __ := ‹LinearOrderedRing α›
#align linear_ordered_ring.to_linear_ordered_add_comm_group LinearOrderedRing.toLinearOrderedAddCommGroup

end LinearOrderedRing

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedCommRing.toStrictOrderedCommRing
    [d : LinearOrderedCommRing α] : StrictOrderedCommRing α :=
  { d with }
#align linear_ordered_comm_ring.to_strict_ordered_comm_ring LinearOrderedCommRing.toStrictOrderedCommRing

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedCommRing.toLinearOrderedCommSemiring
    [d : LinearOrderedCommRing α] : LinearOrderedCommSemiring α :=
  { d, LinearOrderedRing.toLinearOrderedSemiring with }
#align linear_ordered_comm_ring.to_linear_ordered_comm_semiring LinearOrderedCommRing.toLinearOrderedCommSemiring

assert_not_exists MonoidHom
