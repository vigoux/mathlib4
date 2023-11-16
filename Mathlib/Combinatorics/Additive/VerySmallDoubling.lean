import Mathlib

open scoped Pointwise

open Finset

variable {G : Type*} [DecidableEq G] [Group G] {A : Finset G}

-- This came up a few times, it's useful to get size bounds on xA ∩ yA
lemma big_intersection {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    2 * A.card ≤ (({x} * A) ∩ ({y} * A)).card + (A * A).card := by
  have : (({x} * A) ∪ ({y} * A)).card ≤ (A * A).card := by
    refine card_le_of_subset ?_
    rw [←union_mul]
    refine mul_subset_mul_right ?_
    simp [union_subset_iff, hx, hy]
  refine (add_le_add_left this _).trans_eq' ?_
  rw [card_inter_add_card_union, card_singleton_mul, card_singleton_mul, two_mul]

lemma mul_comm_of_doubling_aux (h : (A * A).card < 2 * A.card) :
    A⁻¹ * A ⊆ A * A⁻¹ := by
  intro z
  simp only [mem_mul, forall_exists_index, exists_and_left, and_imp, mem_inv,
    exists_exists_and_eq_and]
  rintro x hx y hy rfl
  have ⟨t, ht⟩ : (({x} * A) ∩ ({y} * A)).Nonempty := by
    rw [←card_pos]
    linarith [big_intersection hx hy]
  simp only [mem_inter, mem_mul, mem_singleton, exists_and_left, exists_eq_left] at ht
  obtain ⟨⟨z, hz, hzxwy⟩, w, hw, rfl⟩ := ht
  refine ⟨z, hz, w, hw, ?_⟩
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, ←hzxwy, inv_mul_cancel_left]

-- TODO: is there a way to get wlog to make `mul_comm_of_doubling_aux` a goal?
-- ie wlog in the target rather than hypothesis
-- (BM: third time seeing this pattern)
lemma mul_comm_of_doubling (h : (A * A).card < 2 * A.card) :
    A * A⁻¹ = A⁻¹ * A := by
  refine Finset.Subset.antisymm ?_ (mul_comm_of_doubling_aux h)
  have : A⁻¹⁻¹ * A⁻¹ ⊆ A⁻¹ * A⁻¹⁻¹ := by
    refine mul_comm_of_doubling_aux ?_
    rw [←mul_inv_rev]
    simpa only [card_inv]
  rwa [inv_inv] at this

lemma coe_mul_comm_of_doubling (h : (A * A).card < 2 * A.card) :
    (A * A⁻¹ : Set G) = A⁻¹ * A := by
  rw [←Finset.coe_mul, mul_comm_of_doubling h, Finset.coe_mul]

lemma weaken_doubling (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    (A * A).card < 2 * A.card := by
  rw [←Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  linarith only [h]

lemma nonempty_of_doubling (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    A.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  simp at h

@[simps]
def symmetricSubgroup (A : Finset G) (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    Subgroup G where
  carrier := A⁻¹ * A
  one_mem' := by
    have ⟨x, hx⟩ : A.Nonempty := nonempty_of_doubling h
    rw [Set.mem_mul]
    exact ⟨x⁻¹, x, by simp [hx]⟩
  inv_mem' := by
    intro x
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, forall_exists_index, exists_and_left, mem_coe,
      and_imp]
    rintro a ha b hb rfl
    exact ⟨b⁻¹, by simpa using hb, a⁻¹, ha, by simp⟩
  mul_mem' := by
    have h₁ : ∀ x ∈ A, ∀ y ∈ A, (1 / 2 : ℚ) * A.card < (({x} * A) ∩ ({y} * A)).card := by
      intro x hx y hy
      have := big_intersection hx hy
      rw [←Nat.cast_le (α := ℚ), Nat.cast_mul, Nat.cast_add, Nat.cast_two] at this
      linarith
    intro a c ha hc
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, mem_coe, exists_and_left] at ha hc
    obtain ⟨a, ha, b, hb, rfl⟩ := ha
    obtain ⟨c, hc, d, hd, rfl⟩ := hc
    have h₂ : (1 / 2 : ℚ) * A.card < (A.filter (∃ z ∈ A, z * ·⁻¹ = a * b)).card := by
      refine (h₁ b hb _ ha).trans_le ?_
      rw [Nat.cast_le]
      refine card_le_card_of_inj_on (b⁻¹ * ·) ?_ ?_
      · simp only [mem_inter, not_exists, not_and, mem_filter, mul_inv_rev, inv_inv, and_imp,
          mem_mul, mem_singleton, exists_and_left, exists_eq_left, forall_exists_index,
          forall_apply_eq_imp_iff₂, inv_mul_cancel_left, inv_mul_cancel_right]
        intros u hu v hv h
        refine ⟨hu, v, hv, ?_⟩
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ←h, mul_inv_cancel_left]
      · simp
    have h₃ : (1 / 2 : ℚ) * A.card < (A.filter (∃ z ∈ A, · * z⁻¹ = c * d)).card := by
      refine (h₁ _ hc d hd).trans_le ?_
      rw [Nat.cast_le]
      refine card_le_card_of_inj_on (c * ·) ?_ ?_
      · simp only [mem_inter, not_exists, not_and, mem_filter, mul_inv_rev, inv_inv, and_imp,
          mem_mul, mem_singleton, exists_and_left, exists_eq_left, forall_exists_index,
          forall_apply_eq_imp_iff₂, mul_inv_cancel_left, inv_mul_cancel_right]
        intros u hu v hv h
        refine ⟨hu, v, hv, ?_⟩
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, h, mul_inv_cancel_left]
      · simp
    have ⟨t, ht⟩ :
        (A.filter (∃ z ∈ A, · * z⁻¹ = c * d) ∩ A.filter (∃ z ∈ A, z * ·⁻¹ = a * b)).Nonempty := by
      rw [←Finset.card_pos, ←Nat.cast_pos (α := ℚ)]
      have := card_inter_add_card_union
        (A.filter (∃ z ∈ A, · * z⁻¹ = c * d)) (A.filter (∃ z ∈ A, z * ·⁻¹ = a * b))
      rw [←Nat.cast_inj (R := ℚ), Nat.cast_add, Nat.cast_add] at this
      have : ((A.filter (∃ z ∈ A, · * z⁻¹ = c * d) ∪ A.filter (∃ z ∈ A, z * ·⁻¹ = a * b)).card : ℚ)
          ≤ A.card := by
        rw [←filter_or, Nat.cast_le]
        exact card_le_of_subset (filter_subset _ _)
      linarith
    simp only [not_exists, not_and, mem_inter, mem_filter] at ht
    have ⟨⟨_, u, hu, hu'⟩, _, v, hv, hv'⟩ := ht
    rw [←coe_mul_comm_of_doubling]
    swap
    · exact weaken_doubling h
    rw [←hu', ←hv', mul_assoc, inv_mul_cancel_left]
    exact Set.mul_mem_mul (by simp [hv]) (by simp [hu])

lemma two_two_two (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    ∃ H : Subgroup G, (H : Set G) = A⁻¹ * A :=
  ⟨symmetricSubgroup _ h, rfl⟩

-- This should 100% be in mathlib
lemma Subgroup.mul_self (H : Subgroup G) : (H : Set G) * H = H := by
  refine Set.Subset.antisymm ?_ (Set.subset_mul_left (H : Set G) (by simp [H.one_mem]))
  simp only [Set.subset_def, Set.mem_mul, SetLike.mem_coe, exists_and_left, forall_exists_index,
    and_imp]
  rintro _ a ha b hb rfl
  exact H.mul_mem ha hb

lemma weak_symmetricSubgroup_bound (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    (A⁻¹ * A).card < 2 * A.card := by
  have h₀ : A.Nonempty := nonempty_of_doubling h
  have h₁ : ∀ x ∈ A, ∀ y ∈ A, (1 / 2 : ℚ) * A.card < (({x} * A) ∩ ({y} * A)).card := by
    intro x hx y hy
    have := big_intersection hx hy
    rw [←Nat.cast_le (α := ℚ), Nat.cast_mul, Nat.cast_add, Nat.cast_two] at this
    linarith
  have h₂ : ∀ a ∈ A⁻¹ * A,
      (1 / 2 : ℚ) * A.card < ((A ×ˢ A).filter (fun ⟨x, y⟩ => x * y⁻¹ = a)).card := by
    simp only [mem_mul, mem_product, Prod.forall, and_imp, mem_inv, exists_exists_and_eq_and,
      forall_exists_index]
    rintro _ _ a b hb rfl ha rfl
    refine (h₁ a ha b hb).trans_le ?_
    rw [Nat.cast_le]
    refine card_le_card_of_inj_on (fun t => (b⁻¹ * t, a⁻¹ * t)) ?_ (by simp)
    simp only [mem_inter, mem_product, and_imp, Prod.forall, mem_filter, mul_inv_rev, inv_inv,
      mem_mul, mem_singleton, exists_and_left, exists_eq_left, forall_exists_index,
      forall_apply_eq_imp_iff₂, inv_mul_cancel_left, inv_mul_cancel_right]
    rintro c hc d hd h
    rw [mul_assoc, mul_inv_cancel_right, ←h, inv_mul_cancel_left]
    simp [hd, hc]
  have h₃ : ∀ x ∈ A ×ˢ A, (fun ⟨x, y⟩ => x * y⁻¹) x ∈ A⁻¹ * A := by
    rw [←mul_comm_of_doubling (weaken_doubling h)]
    simp only [mem_product, Prod.forall, mem_mul, and_imp, mem_inv]
    intro a b ha hb
    exact ⟨a, b⁻¹, ha, by simp [hb], rfl⟩
  have : ((1 / 2 : ℚ) * A.card) * (A⁻¹ * A).card < (A.card : ℚ) ^ 2 := by
    rw [←Nat.cast_pow, sq, ←card_product, card_eq_sum_card_fiberwise h₃, Nat.cast_sum]
    refine (Finset.sum_lt_sum_of_nonempty (by simp [h₀]) h₂).trans_eq' ?_
    simp only [sum_const, nsmul_eq_mul, mul_comm]
  have : (0 : ℚ) < A.card := by simpa [card_pos]
  rw [←Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  -- passing between ℕ- and ℚ-inequalities is annoying, here and above
  nlinarith

lemma subgroup_strong_bound_left (h : (A * A).card < (3 / 2 : ℚ) * A.card) (a : G) (ha : a ∈ A) :
    A * A ⊆ {a} * (A⁻¹ * A) * {a} := by
  rw [←Finset.coe_subset, coe_mul, coe_mul, coe_mul, coe_singleton, coe_mul]
  obtain ⟨H, hH⟩ := two_two_two h
  have hH' : (H : Set G) = A * A⁻¹ := by rw [hH, coe_mul_comm_of_doubling (weaken_doubling h)]
  have h₁ : (A : Set G) ⊆ {a} * H
  · rw [hH, ←mul_assoc]
    exact Set.subset_mul_right _ (by simp [ha])
  have h₂ : (A : Set G) ⊆ H * {a}
  · rw [hH', mul_assoc]
    exact Set.subset_mul_left _ (by simp [ha])
  refine (Set.mul_subset_mul h₁ h₂).trans ?_
  rw [←mul_assoc, mul_assoc {a} (H : Set G), H.mul_self, hH]

lemma subgroup_strong_bound_right (h : (A * A).card < (3 / 2 : ℚ) * A.card) (a : G) (ha : a ∈ A) :
    {a} * (A⁻¹ * A) * {a} ⊆ A * A := by
  intro z hz
  obtain ⟨H, hH⟩ := two_two_two h
  simp only [mem_mul, mem_singleton, exists_and_left, exists_eq_left, exists_exists_and_eq_and,
    mem_inv] at hz
  obtain ⟨_, ⟨b, hb, c, hc, rfl⟩, hz⟩ := hz
  let l : Finset G := A ∩ ({z * a⁻¹} * (A⁻¹ * A)) -- set of x ∈ A st ∃ y ∈ H a with x y = z
  let r : Finset G := ({a} * (A⁻¹ * A)) ∩ ({z} * A⁻¹)
  have : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [←Finset.coe_inj, coe_mul, coe_mul, ←hH, H.mul_self]
  have hl : l = A := by
    rw [inter_eq_left, ←hz, mul_inv_cancel_right, ←this, ←mul_assoc, ←mul_assoc]
    refine subset_mul_right _ ?_
    simp only [mem_mul, mem_singleton, exists_and_left, exists_eq_left, exists_exists_and_eq_and,
      mem_inv]
    exact ⟨(b⁻¹ * c)⁻¹, ⟨c, hc, b, hb, by simp⟩, a, ha,
      by simp only [mul_inv_cancel_right, mul_inv_self]⟩
  have hr : r = {z} * A⁻¹ := by
    rw [inter_eq_right, ←hz, ←this, mul_assoc _ A, ←mul_comm_of_doubling (weaken_doubling h)]
    simp only [←mul_assoc]
    -- everything from here in this goal feels like it should be automated...
    -- TODO: make gcongr handle this step
    refine mul_subset_mul_right ?_
    rw [singleton_subset_iff]
    exact mul_mem_mul (mul_mem_mul (mul_mem_mul (by simp) (inv_mem_inv hb)) hc) ha
  have lr : l ∪ r ⊆ {a} * (A⁻¹ * A) := by
    rw [union_subset_iff, hl, ←mul_assoc]
    refine ⟨subset_mul_right _ ?_, ?_⟩
    · simp only [mem_mul, mem_singleton, exists_and_left, exists_eq_left, mem_inv,
        exists_exists_and_eq_and]
      exact ⟨a, ha, by simp⟩
    rw [mul_assoc]
    exact inter_subset_left _ _
  have : l.card = A.card := by rw [hl]
  have : r.card = A.card := by rw [hr, card_singleton_mul, card_inv]
  have : (l ∪ r).card < 2 * A.card := by
    refine (card_le_of_subset lr).trans_lt ?_
    rw [card_singleton_mul]
    exact weak_symmetricSubgroup_bound h
  have ⟨t, ht⟩ : (l ∩ r).Nonempty := by
    rw [←card_pos]
    linarith [card_inter_add_card_union l r]
  simp only [hl, hr, mem_inter, mem_mul, mem_singleton, exists_and_left, exists_eq_left,
    mem_inv, exists_exists_and_eq_and, mul_inv_eq_iff_eq_mul] at ht
  obtain ⟨ht, u, hu, rfl⟩ := ht
  exact mul_mem_mul ht hu

lemma subgroup_strong_bound_equality (h : (A * A).card < (3 / 2 : ℚ) * A.card)
    (a : G) (ha : a ∈ A) :
    {a} * (A⁻¹ * A) * {a} = A * A :=
  (subgroup_strong_bound_right h a ha).antisymm (subgroup_strong_bound_left h a ha)

lemma subgroup_strong_bound (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    (A⁻¹ * A).card = (A * A).card := by
  obtain ⟨a, ha⟩ := nonempty_of_doubling h
  rw [←subgroup_strong_bound_equality h a ha, card_mul_singleton, card_singleton_mul]

lemma Nat.card_Subgroup {H : Subgroup G} : Nat.card H = Nat.card (H : Set G) := by
  simp only [SetLike.coe_sort_coe]

theorem very_small_doubling (A : Finset G) (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    ∃ (H : Subgroup G), ∃ a ∈ A,
      (H : Set G).ncard < (3 / 2 : ℚ) * A.card ∧
      (A : Set G) ⊆ {a} * H := by
  have ⟨a, ha⟩ := nonempty_of_doubling h
  refine ⟨symmetricSubgroup _ h, a, ha, ?_, ?_⟩
  · rwa [symmetricSubgroup_coe, ←coe_mul, Set.ncard_coe_Finset, subgroup_strong_bound h]
  · rw [symmetricSubgroup_coe, ←mul_assoc]
    exact Set.subset_mul_right _ (by simp [ha])
