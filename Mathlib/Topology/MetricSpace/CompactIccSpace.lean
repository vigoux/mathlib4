/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded

/-!
## Boundedness in (pseudo)-metric spaces with compact Icc
-/

open Set Bornology

variable {α : Type*} [PseudoMetricSpace α] [Preorder α] [CompactIccSpace α]

theorem totallyBounded_Icc (a b : α) : TotallyBounded (Icc a b) :=
  isCompact_Icc.totallyBounded
#align totally_bounded_Icc totallyBounded_Icc

theorem totallyBounded_Ico (a b : α) : TotallyBounded (Ico a b) :=
  totallyBounded_subset Ico_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ico totallyBounded_Ico

theorem totallyBounded_Ioc (a b : α) : TotallyBounded (Ioc a b) :=
  totallyBounded_subset Ioc_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ioc totallyBounded_Ioc

theorem totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a b) :=
  totallyBounded_subset Ioo_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ioo totallyBounded_Ioo

namespace Metric

theorem isBounded_Icc (a b : α) : IsBounded (Icc a b) :=
  (totallyBounded_Icc a b).isBounded
#align metric.bounded_Icc Metric.isBounded_Icc

theorem isBounded_Ico (a b : α) : IsBounded (Ico a b) :=
  (totallyBounded_Ico a b).isBounded
#align metric.bounded_Ico Metric.isBounded_Ico

theorem isBounded_Ioc (a b : α) : IsBounded (Ioc a b) :=
  (totallyBounded_Ioc a b).isBounded
#align metric.bounded_Ioc Metric.isBounded_Ioc

theorem isBounded_Ioo (a b : α) : IsBounded (Ioo a b) :=
  (totallyBounded_Ioo a b).isBounded
#align metric.bounded_Ioo Metric.isBounded_Ioo

/-- In a pseudo metric space with a conditionally complete linear order such that the order and the
    metric structure give the same topology, any order-bounded set is metric-bounded. -/
theorem isBounded_of_bddAbove_of_bddBelow {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s) :
    IsBounded s :=
  let ⟨u, hu⟩ := h₁
  let ⟨l, hl⟩ := h₂
  (isBounded_Icc l u).subset (fun _x hx => mem_Icc.mpr ⟨hl hx, hu hx⟩)
#align metric.bounded_of_bdd_above_of_bdd_below Metric.isBounded_of_bddAbove_of_bddBelow

end Metric
