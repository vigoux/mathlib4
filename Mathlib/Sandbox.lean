import Mathlib

noncomputable section Algebra

variable {E ι K : Type*} [NormedLinearOrderedField K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable (b : Basis ι K E)

open Submodule

open scoped Pointwise

example {c : K} (h : c ≠ 0) :
    Basis ι K E := b.isUnitSMul (fun _ ↦ Ne.isUnit h)

theorem Zspan.smul {c : K} (h : c ≠ 0) :
    c • span ℤ (Set.range b) = span ℤ (Set.range (b.isUnitSMul (fun _ ↦ Ne.isUnit h))) := by
  rw [smul_span, Set.smul_set_range]
  congr!
  rw [Basis.isUnitSMul_apply]

open Algebra

theorem Algebra.norm_smul {K : Type*} [Field K] {L : Type*} [Ring L] [Algebra K L] (x : L) (c : K) :
    Algebra.norm K (c • x) = c ^ FiniteDimensional.finrank K L * Algebra.norm K x := by
  classical
  rw [norm_apply, map_smul, LinearMap.det_smul, ← norm_apply]

end Algebra

open Filter BigOperators Asymptotics Topology

section RiemannZeta

theorem zap0 :
    Tendsto (fun s : ℂ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n:ℂ) ^ s)
      (𝓝[{s | 1 < s.re}] 1) (𝓝 1) := by
  have : Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝[{s | 1 < s.re}] 1) (𝓝 1) := by
    refine Filter.Tendsto.mono_left riemannZeta_residue_one ?_
    refine nhdsWithin_mono _ ?_
    aesop
  refine Tendsto.congr' ?_ this
  rw [eventuallyEq_nhdsWithin_iff]
  refine eventually_of_forall (fun s hs ↦ ?_)
  exact congr_arg ((s - 1) * ·) (zeta_eq_tsum_one_div_nat_cpow hs)

end RiemannZeta

section Eventually

theorem le_of_frequently_sub_le {α : Type*} [LinearOrderedField α] [TopologicalSpace α]
    [OrderTopology α] {a b : α} (h : ∃ᶠ ε in 𝓝[>] 0, b - ε ≤ a) : b ≤ a := by
  contrapose! h
  obtain ⟨c, hc⟩ := exists_add_lt_and_pos_of_lt h
  refine not_frequently.mpr <|
    eventually_iff_exists_mem.mpr ⟨Set.Ioc 0 c, Ioc_mem_nhdsWithin_Ioi' hc.2, fun _ hx ↦ ?_⟩
  exact not_le.mpr <| lt_of_lt_of_le (lt_tsub_of_add_lt_right hc.1) (sub_le_sub_left hx.2 b)

theorem le_of_frequently_le_add {α : Type*} [LinearOrderedField α] [TopologicalSpace α]
    [OrderTopology α] {a b : α} (h : ∃ᶠ ε in 𝓝[>] 0, b ≤ a + ε) : b ≤ a := by
  simp_rw [← sub_le_iff_le_add] at h
  exact le_of_frequently_sub_le h

end Eventually

section IsBounded

@[to_additive]
theorem IsBoundedUnder_le_mul_right {α β : Type*} [OrderedCommGroup α] {f : Filter β} {u : β → α}
    (a : α) (hu : IsBoundedUnder (· ≤ ·) f u) :
    IsBoundedUnder (· ≤ ·) f (fun x ↦ u x * a) :=
  (OrderIso.mulRight a).isBoundedUnder_le_comp.mpr hu

@[to_additive]
theorem IsBoundedUnder_le_mul_left {α β : Type*} [OrderedCommGroup α] {f : Filter β} {u : β → α}
    (a : α) (hu : IsBoundedUnder (· ≤ ·) f u) :
    IsBoundedUnder (· ≤ ·) f (fun x ↦ a * u x) :=
  (OrderIso.mulLeft a).isBoundedUnder_le_comp.mpr hu

@[to_additive]
theorem IsBoundedUnder_le_mul {α β : Type*} [OrderedCommGroup α] {f : Filter β} {u v : β → α}
    (hu : IsBoundedUnder (· ≤ ·) f u) (hv : IsBoundedUnder (· ≤ ·) f v) :
    IsBoundedUnder (· ≤ ·) f (u * v) := by
  obtain ⟨bu, hu⟩ := hu
  obtain ⟨bv, hv⟩ := hv
  refine ⟨bu * bv, ?_⟩
  rw [eventually_map] at hu hv ⊢
  filter_upwards [hu, hv] with _ h₁ h₂ using mul_le_mul' h₁ h₂

@[to_additive]
theorem IsBoundedUnder_ge_mul_right {α β : Type*} [OrderedCommGroup α] {f : Filter β} {u : β → α}
    (a : α) (hu : IsBoundedUnder (· ≥ ·) f u) :
    IsBoundedUnder (· ≥ ·) f (fun x ↦ u x * a) :=
  (OrderIso.mulRight a).isBoundedUnder_ge_comp.mpr hu

@[to_additive]
theorem IsBoundedUnder_ge_mul_left {α β : Type*} [OrderedCommGroup α] {f : Filter β} {u : β → α}
    (a : α) (hu : IsBoundedUnder (· ≥ ·) f u) :
    IsBoundedUnder (· ≥ ·) f (fun x ↦ a * u x) :=
  (OrderIso.mulLeft a).isBoundedUnder_ge_comp.mpr hu

@[to_additive]
theorem IsBoundedUnder_ge_mul {α β : Type*} [OrderedCommGroup α] {f : Filter β} {u v : β → α}
    (hu : IsBoundedUnder (· ≥ ·) f u) (hv : IsBoundedUnder (· ≥ ·) f v) :
    IsBoundedUnder (· ≥ ·) f (u * v) := by
  obtain ⟨bu, hu⟩ := hu
  obtain ⟨bv, hv⟩ := hv
  refine ⟨bu * bv, ?_⟩
  rw [eventually_map] at hu hv ⊢
  filter_upwards [hu, hv] with _ h₁ h₂ using mul_le_mul' h₁ h₂

-- Mathlib.Order.LiminfLimsup
-- #find_home IsBoundedUnder_ge_mul

theorem IsBoundedUnder_le_mul_right₀ {α β : Type*} [LinearOrderedSemifield α] {f : Filter β}
    {u : β → α} {a : α} (ha : 0 < a) (hu : IsBoundedUnder (· ≤ ·) f u) :
    IsBoundedUnder (· ≤ ·) f (fun x ↦ u x * a) :=
  (OrderIso.mulRight₀ a ha).isBoundedUnder_le_comp.mpr hu

theorem IsBoundedUnder_le_mul_left₀ {α β : Type*} [LinearOrderedSemifield α] {f : Filter β}
    {u : β → α} {a : α} (ha : 0 < a) (hu : IsBoundedUnder (· ≤ ·) f u) :
    IsBoundedUnder (· ≤ ·) f (fun x ↦ a * u x) :=
  (OrderIso.mulLeft₀ a ha).isBoundedUnder_le_comp.mpr hu

theorem IsBoundedUnder_ge_mul_right₀ {α β : Type*} [LinearOrderedSemifield α] {f : Filter β}
    {u : β → α} {a : α} (ha : 0 < a) (hu : IsBoundedUnder (· ≥ ·) f u) :
    IsBoundedUnder (· ≥ ·) f (fun x ↦ u x * a) :=
  (OrderIso.mulRight₀ a ha).isBoundedUnder_ge_comp.mpr hu

theorem IsBoundedUnder_ge_mul_left₀ {α β : Type*} [LinearOrderedSemifield α] {f : Filter β}
    {u : β → α} {a : α} (ha : 0 < a) (hu : IsBoundedUnder (· ≥ ·) f u) :
    IsBoundedUnder (· ≥ ·) f (fun x ↦ a * u x) :=
  (OrderIso.mulLeft₀ a ha).isBoundedUnder_ge_comp.mpr hu

-- Mathlib.Topology.Algebra.Order.LiminfLimsup
-- #find_home IsBoundedUnder_ge_mul_left₀

end IsBounded


section Analysis

-- Need to generalize to other limits than 1(?)
-- summability comes from easier facts
variable {u v : ℕ → ℝ} {a : ℝ} (ha : 0 < a) (h_main : Tendsto (u / v) atTop (𝓝 a))
  (h_sum : ∀ ⦃s⦄, (1:ℝ) < s → Summable (fun k ↦ v k ^ s))
  (h_res : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, v k ^ s) (𝓝[>] 1) (𝓝 1))

theorem tendsto_mul_tsum_of_tendsto_mul_tsum_aux (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 < v k) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ a) :
    ∃ t : Finset ℕ, ∀ ⦃s⦄, (1:ℝ) < s →
      (s - 1) * ∑ k in t, u k ^ s + (a - ε) ^ s * ((s - 1) * ∑' (k : {k // k ∉ t}), v k ^ s) ≤
      (s - 1) * ∑' k, u k ^ s ∧
      (s - 1) * ∑' k, u k ^ s ≤
      (s - 1) * ∑ k in t, u k ^ s + (a + ε) ^ s * ((s - 1) * ∑' (k : {k // k ∉ t}), v k ^ s) := by
  have h_sum' : ∀ ⦃s : ℝ⦄, 1 < s → Summable (fun k ↦ (u k) ^ s) := by
    sorry
  rsuffices ⟨k₀, hk₀⟩ : ∃ k₀, ∀ k ≥ k₀, ∀ ⦃s : ℝ⦄, 1 < s →
      (a - ε) ^ s * v k ^ s ≤ u k ^ s ∧ u k ^ s ≤ (a + ε) ^ s * v k ^ s := by
    obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.mp h_main ε hε
    refine ⟨k₀, fun k hk s hs ↦ ?_⟩
    -- We remind Lean of some facts so that positivity works later on
    have : 0 < v k := hv k
    have : 0 ≤ u k := hu k
    have : 0 ≤ a - ε := sub_nonneg_of_le hε'
    rw [← Real.mul_rpow, ← Real.mul_rpow, Real.rpow_le_rpow_iff, Real.rpow_le_rpow_iff, sub_mul,
      add_mul, ← sub_le_iff_le_add', sub_eq_add_neg, ← le_sub_iff_add_le', ← neg_mul,
      ← div_le_iff, ← le_div_iff, sub_div, mul_div_cancel_right₀, ← abs_le]
    exact le_of_lt (hk₀ k hk)
    any_goals positivity
  refine ⟨Finset.Iio k₀, fun s hs ↦ ⟨?_, ?_⟩⟩
  · rw [mul_left_comm, ← mul_add, mul_le_mul_left (sub_pos.mpr hs),
      ← sum_add_tsum_subtype_compl (h_sum' hs), add_le_add_iff_left, ← tsum_mul_left]
    refine tsum_mono ?_ ?_ (fun ⟨k, hk⟩ ↦ ?_)
    · exact Summable.mul_left _ (Summable.subtype (h_sum hs) _)
    · exact Summable.subtype (h_sum' hs) _
    · exact (hk₀ k (not_lt.mp (Finset.mem_Iio.not.mp hk)) hs).1
  · rw [mul_left_comm, ← mul_add, mul_le_mul_left (sub_pos.mpr hs),
      ← sum_add_tsum_subtype_compl (h_sum' hs), add_le_add_iff_left, ← tsum_mul_left]
    refine tsum_mono ?_ ?_ (fun ⟨k, hk⟩ ↦ ?_)
    · exact Summable.subtype (h_sum' hs) _
    · exact Summable.mul_left _ (Summable.subtype (h_sum hs) _)
    · exact (hk₀ k (not_lt.mp (Finset.mem_Iio.not.mp hk)) hs).2

theorem toto {a b : ℕ → ℝ} {l : ℝ}
    (ha : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, a k ^ s) (𝓝[>] 1) (𝓝 l))
    (has : ∀ ⦃s⦄, (1:ℝ) < s → Summable (fun k ↦ a k ^ s))
    (h : ∀ᶠ k in atTop, b k = a k) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, b k ^ s) (𝓝[>] 1) (𝓝 l) := by
  have hbs : ∀ ⦃s⦄, (1:ℝ) < s → Summable (fun k ↦ b k ^ s) := by
    intro s hs
    refine (IsEquivalent.summable_iff_nat ?_).mp (has hs)
    refine EventuallyEq.isEquivalent ?_
    filter_upwards [h] with _ h using by rw [h]
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp h
  have : ∀ᶠ (s:ℝ) in 𝓝[>] 1, (s - 1) * ∑ k in Finset.Iio k₀, (b k ^ s - a k ^ s) +
      (s - 1) * ∑' k, a k ^ s = (s - 1) * ∑' k, b k ^ s := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards
    intro s hs
    rw [← mul_add]
    rw [mul_right_inj']
    rw [ Finset.sum_sub_distrib]
    rw [← sum_add_tsum_subtype_compl (has hs) (Finset.Iio k₀)]
    rw [← add_assoc]
    rw [sub_add_cancel]
    rw [← sum_add_tsum_subtype_compl (hbs hs) (Finset.Iio k₀)]
    rw [add_right_inj]
    refine tsum_congr (fun ⟨k, hk⟩ ↦ ?_)
    have := not_lt.mp (Finset.mem_Iio.not.mp hk)
    have := hk₀ k (not_lt.mp (Finset.mem_Iio.not.mp hk))
    exact (congr_arg (· ^ s) (hk₀ k (not_lt.mp (Finset.mem_Iio.not.mp hk)))).symm
    rw [sub_ne_zero]
    refine ne_of_gt ?_
    exact hs
  refine Filter.Tendsto.congr' this ?_
  convert Tendsto.add (a := 0) ?_ ha
  · rw [zero_add]
  · have : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝 0) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine tendsto_sub_nhds_zero_iff.mpr ?_
      exact tendsto_id
    convert Tendsto.mul this (tendsto_finset_sum (a := fun k ↦ b k ^ (1:ℝ) - a k ^ (1:ℝ))
      (Finset.Iio k₀) fun k _ ↦ ?_)
    · rw [zero_mul]
    · refine Tendsto.sub ?_ ?_
      · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        exact Real.continuousAt_const_rpow' one_ne_zero
      · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        exact Real.continuousAt_const_rpow' one_ne_zero

theorem tendsto_mul_tsum_of_tendsto_mul_tsum' (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 < v k) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, u k ^ s) (𝓝[>] 1) (𝓝 a) := by
  -- We first need to prove some basic facts
  have h_lim_eq_self : ∀ x : ℝ, Tendsto (fun s : ℝ ↦ x ^ s) (𝓝[>] 1) (𝓝 x) := fun x ↦ by
    convert Tendsto.rpow tendsto_const_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)
      (Or.inr zero_lt_one)
    rw [Real.rpow_one]
  have h_tendsto_zero : ∀ (w : ℕ → ℝ) (t : Finset ℕ),
      Tendsto (fun s : ℝ ↦ (s - 1) * ∑ k in t, w k ^ s) (𝓝[>] 1) (𝓝 0) := fun w t ↦ by
    convert Tendsto.mul (a := 0) ?_ (tendsto_finset_sum t fun k _ ↦ h_lim_eq_self (w k))
    · rw [zero_mul]
    · exact (tendsto_sub_nhds_zero_iff.mpr tendsto_id).mono_left nhdsWithin_le_nhds
  have h_tendsto_one : ∀ (t : Finset ℕ),
      Tendsto (fun s : ℝ ↦ (s - 1) * ∑' (k : {k // k ∉ t}), v k ^ s) (𝓝[>] 1) (𝓝 1) := fun t ↦ by
    refine tendsto_nhdsWithin_congr (fun s hs ↦ ?_) <| (sub_zero (1:ℝ)) ▸
      Tendsto.sub h_res (h_tendsto_zero v t)
    rw [ ← sum_add_tsum_subtype_compl (h_sum hs) t, mul_add, add_sub_cancel_left]
  have h_bdu_le : ∀ (ε : ℝ) (t : Finset ℕ),
      IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s : ℝ ↦ (s - 1) * ∑ k in t, u k ^ s +
        (a + ε) ^ s * ((s - 1) * ∑' (k : { k // k ∉ t }), v k ^ s) := fun ε t ↦ by
    sorry
    -- refine IsBoundedUnder_le_add (h_tendsto_zero u t).isBoundedUnder_le ?_
    -- exact (Tendsto.mul (h_lim_eq_self (1 + ε)) (h_tendsto_one t)).isBoundedUnder_le
  have h_bdu_ge : ∀ (ε : ℝ) (t : Finset ℕ),
      IsBoundedUnder (· ≥ ·) (𝓝[>] 1) fun s : ℝ ↦ (s - 1) * ∑ k in t, u k ^ s +
        (a - ε) ^ s * ((s - 1) * ∑' (k : { k // k ∉ t }), v k ^ s) := fun ε t ↦ by
    sorry
    -- refine IsBoundedUnder_ge_add (h_tendsto_zero u t).isBoundedUnder_ge ?_
    -- exact (Tendsto.mul (h_lim_eq_self (1 - ε)) (h_tendsto_one t)).isBoundedUnder_ge
  have h_εbdd : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, 0 < ε ∧ ε ≤ a :=
    eventually_iff_exists_mem.mpr ⟨Set.Ioc 0 a, Ioc_mem_nhdsWithin_Ioi' ha, fun _ h ↦ h⟩
  -- We then prove bounds on liminf and limsup
  have h_bdd : ∀ ⦃ε : ℝ⦄, 0 < ε → ε ≤ a →
      a - ε ≤ liminf (fun s : ℝ ↦ (s - 1) * ∑' k, u k ^ s) (𝓝[>] 1) ∧
        limsup (fun s : ℝ ↦ (s - 1) * ∑' k, u k ^ s) (𝓝[>] 1) ≤ a + ε := fun ε hε hε' ↦ by
    obtain ⟨t, ht⟩ := tendsto_mul_tsum_of_tendsto_mul_tsum_aux ha h_main h_sum hu hv hε hε'
    have h₁ : ∀ᶠ (s : ℝ) in 𝓝[>] 1, _ := eventually_nhdsWithin_of_forall (fun s hs ↦ (ht hs).1)
    have h₂ : ∀ᶠ (s : ℝ) in 𝓝[>] 1, _ := eventually_nhdsWithin_of_forall (fun s hs ↦ (ht hs).2)
    refine ⟨?_, ?_⟩
    · convert liminf_le_liminf h₁ (h_bdu_ge ε t) ?_
      · refine (Tendsto.liminf_eq ?_).symm
        simp_rw [show 𝓝 (a - ε) = 𝓝 (0 + (a - ε) * 1) by ring_nf]
        exact (h_tendsto_zero u t).add  <| Tendsto.mul (h_lim_eq_self (a - ε)) (h_tendsto_one t)
      · exact IsBounded.isCobounded_ge <| IsBoundedUnder.mono_le (h_bdu_le ε t) h₂
    · convert limsup_le_limsup h₂ ?_ (h_bdu_le ε t)
      · refine (Tendsto.limsup_eq ?_).symm
        simp_rw [show 𝓝 (a + ε) = 𝓝 (0 + (a + ε) * 1) by ring_nf]
        exact (h_tendsto_zero u t).add  <| Tendsto.mul (h_lim_eq_self (a + ε)) (h_tendsto_one t)
      · exact IsBounded.isCobounded_le <| IsBoundedUnder.mono_ge (h_bdu_ge ε t) h₁
  -- Finally we get the result by proving that liminf and limsup are equal
  obtain ⟨t, ht⟩ := tendsto_mul_tsum_of_tendsto_mul_tsum_aux ha h_main h_sum hu hv ha le_rfl
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ ?_ ?_
  · refine le_of_frequently_sub_le (Eventually.frequently ?_)
    filter_upwards [h_εbdd] with ε ⟨hε, hε'⟩ using (h_bdd hε hε').1
  · refine le_of_frequently_le_add (Eventually.frequently ?_)
    filter_upwards [h_εbdd] with ε ⟨hε, hε'⟩ using (h_bdd hε hε').2
  · sorry
    -- exact (h_bdu_le 1 t).mono_le  (eventually_nhdsWithin_of_forall fun s hs ↦ (ht hs).2)
  · sorry
    -- exact (h_bdu_ge 1 t).mono_ge  (eventually_nhdsWithin_of_forall fun s hs ↦ (ht hs).1)

theorem tendsto_mul_tsum_of_tendsto_mul_tsum (hv : ∀ᶠ k in atTop, 0 < v k) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, u k ^ s) (𝓝[>] 1) (𝓝 a) := by
  have hu : ∀ᶠ k in atTop, 0 ≤ u k := by
    rw [Metric.tendsto_nhds] at h_main
    specialize h_main 1 zero_lt_one
    filter_upwards [h_main, hv] with k h₁ h₂
    rw [Pi.div_apply] at h₁
    rw [Real.dist_eq, abs_lt] at h₁
    rw [lt_tsub_iff_left] at h₁
    -- rw [add_neg_self] at h₁
    -- rw [div_pos_iff_of_pos_right h₂] at h₁
    -- exact le_of_lt h₁.1
    sorry
  obtain ⟨kv, hkv⟩ := eventually_atTop.mp hv
  obtain ⟨ku, hku⟩ := eventually_atTop.mp hu
  let v' : ℕ → ℝ := fun k ↦ if kv ≤ k then v k else 1
  let u' : ℕ → ℝ := fun k ↦ if ku ≤ k then u k else 1
  have hv' : ∀ k, 0 < v' k := by
    intro k
    dsimp only [v']
    split_ifs with h
    · exact hkv k h
    · norm_num
  have hu' : ∀ k, 0 ≤ u' k := by
    intro k
    dsimp only [u']
    split_ifs with h
    · exact hku k h
    · norm_num
  have hvv' : ∀ᶠ k in atTop, v' k = v k := by
    rw [eventually_atTop]
    refine ⟨kv, ?_⟩
    intro k h
    dsimp only [v']
    rw [if_pos h]
  have huu' : ∀ᶠ k in atTop, u k = u' k := by
    rw [eventually_atTop]
    refine ⟨ku, ?_⟩
    intro k h
    dsimp only [u']
    rw [if_pos h]
  have h_main' : Tendsto (u' / v') atTop (𝓝 a) := by
    refine Tendsto.congr' ?_ h_main
    filter_upwards [hvv', huu'] with _ h₁ h₂ using by simp_rw [Pi.div_apply, h₁, h₂]
  have h_sum' : ∀ ⦃s⦄, (1:ℝ) < s → Summable (fun k ↦ (v' k) ^ s) := by
    intro s hs
    refine (IsEquivalent.summable_iff_nat ?_).mp (h_sum hs)
    refine EventuallyEq.isEquivalent ?_
    filter_upwards [hvv'] with _ h using by rw [h]
  have h_res' : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, v' k ^ s) (𝓝[>] 1) (𝓝 1) := by
    exact toto h_res h_sum hvv'
  have := tendsto_mul_tsum_of_tendsto_mul_tsum' ha h_main' h_sum' h_res' hu' hv'

  refine toto this ?_ huu'
  intro s hs
  refine (IsEquivalent.summable_iff_nat ?_).mp (h_sum' hs)
  sorry -- too many similar proofs

end Analysis

/- section Analysis

-- Need to generalize to other limits than 1 / equivalent to a instead of 1?
-- summability comes from easier facts
variable {u v : ℕ → ℝ} (h_main : Tendsto (u / v) atTop (𝓝 1))
  (h_sum : ∀ ⦃s⦄, (1:ℝ) < s → Summable (fun k ↦ v k ^ s))
  (h_res : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, v k ^ s) (𝓝[>] 1) (𝓝 1))

theorem tendsto_mul_tsum_of_tendsto_mul_tsum_aux (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 < v k) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1) :
    ∃ t : Finset ℕ, ∀ ⦃s⦄, (1:ℝ) < s →
      (s - 1) * ∑ k in t, u k ^ s + (1 - ε) ^ s * ((s - 1) * ∑' (k : {k // k ∉ t}), v k ^ s) ≤
      (s - 1) * ∑' k, u k ^ s ∧
      (s - 1) * ∑' k, u k ^ s ≤
      (s - 1) * ∑ k in t, u k ^ s + (1 + ε) ^ s * ((s - 1) * ∑' (k : {k // k ∉ t}), v k ^ s) := by
  have h_sum' : ∀ ⦃s : ℝ⦄, 1 < s → Summable (fun k ↦ (u k) ^ s) := by
    refine fun s hs ↦ (IsEquivalent.summable_iff_nat ?_).mpr (h_sum hs)
    refine (isEquivalent_iff_tendsto_one (eventually_of_forall (fun _ ↦ ?_))).mpr ?_
    · refine (Real.rpow_eq_zero (le_of_lt (hv _)) (by linarith)).not.mpr <| ne_of_gt (hv _)
    · convert Tendsto.congr (fun _ ↦ ?_)
        (Tendsto.comp (Real.continuousAt_rpow_const 1 s (Or.inl one_ne_zero)) h_main)
      · simp_rw [Real.one_rpow]
      · rw [Function.comp_apply, Pi.div_apply, Pi.div_apply, Real.div_rpow (hu _) (le_of_lt (hv _))]
  rsuffices ⟨k₀, hk₀⟩ : ∃ k₀, ∀ k ≥ k₀, ∀ ⦃s : ℝ⦄, 1 < s →
      (1 - ε) ^ s * v k ^ s ≤ u k ^ s ∧ u k ^ s ≤ (1 + ε) ^ s * v k ^ s := by
    obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.mp h_main ε hε
    refine ⟨k₀, fun k hk s hs ↦ ?_⟩
    -- We remind Lean of some facts so that positivity works later on
    have : 0 < v k := hv k
    have : 0 ≤ u k := hu k
    have : 0 ≤ 1 - ε := sub_nonneg_of_le hε'
    rw [← Real.mul_rpow, ← Real.mul_rpow, Real.rpow_le_rpow_iff, Real.rpow_le_rpow_iff, sub_mul,
      add_mul, one_mul, ← sub_le_iff_le_add', sub_eq_add_neg, ← le_sub_iff_add_le', ← neg_mul,
      ← div_le_iff, ← le_div_iff, sub_div, div_self, ← abs_le]
    exact le_of_lt (hk₀ k hk)
    any_goals positivity
  refine ⟨Finset.Iio k₀, fun s hs ↦ ⟨?_, ?_⟩⟩
  · rw [mul_left_comm, ← mul_add, mul_le_mul_left (sub_pos.mpr hs),
      ← sum_add_tsum_subtype_compl (h_sum' hs), add_le_add_iff_left, ← tsum_mul_left]
    refine tsum_mono ?_ ?_ (fun ⟨k, hk⟩ ↦ ?_)
    · exact Summable.mul_left _ (Summable.subtype (h_sum hs) _)
    · exact Summable.subtype (h_sum' hs) _
    · exact (hk₀ k (not_lt.mp (Finset.mem_Iio.not.mp hk)) hs).1
  · rw [mul_left_comm, ← mul_add, mul_le_mul_left (sub_pos.mpr hs),
      ← sum_add_tsum_subtype_compl (h_sum' hs), add_le_add_iff_left, ← tsum_mul_left]
    refine tsum_mono ?_ ?_ (fun ⟨k, hk⟩ ↦ ?_)
    · exact Summable.subtype (h_sum' hs) _
    · exact Summable.mul_left _ (Summable.subtype (h_sum hs) _)
    · exact (hk₀ k (not_lt.mp (Finset.mem_Iio.not.mp hk)) hs).2

theorem toto {a b : ℕ → ℝ} (ha : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, a k ^ s) (𝓝[>] 1) (𝓝 1))
    (has : ∀ ⦃s⦄, (1:ℝ) < s → Summable (fun k ↦ a k ^ s))
    (h : ∀ᶠ k in atTop, b k = a k) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, b k ^ s) (𝓝[>] 1) (𝓝 1) := by
  have hbs : ∀ ⦃s⦄, (1:ℝ) < s → Summable (fun k ↦ b k ^ s) := by
    intro s hs
    refine (IsEquivalent.summable_iff_nat ?_).mp (has hs)
    refine EventuallyEq.isEquivalent ?_
    filter_upwards [h] with _ h using by rw [h]
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp h
  have : ∀ᶠ (s:ℝ) in 𝓝[>] 1, (s - 1) * ∑ k in Finset.Iio k₀, (b k ^ s - a k ^ s) +
      (s - 1) * ∑' k, a k ^ s = (s - 1) * ∑' k, b k ^ s := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards
    intro s hs
    rw [← mul_add]
    rw [mul_right_inj']
    rw [ Finset.sum_sub_distrib]
    rw [← sum_add_tsum_subtype_compl (has hs) (Finset.Iio k₀)]
    rw [← add_assoc]
    rw [sub_add_cancel]
    rw [← sum_add_tsum_subtype_compl (hbs hs) (Finset.Iio k₀)]
    rw [add_right_inj]
    refine tsum_congr (fun ⟨k, hk⟩ ↦ ?_)
    have := not_lt.mp (Finset.mem_Iio.not.mp hk)
    have := hk₀ k (not_lt.mp (Finset.mem_Iio.not.mp hk))
    exact (congr_arg (· ^ s) (hk₀ k (not_lt.mp (Finset.mem_Iio.not.mp hk)))).symm
    rw [sub_ne_zero]
    refine ne_of_gt ?_
    exact hs
  refine Filter.Tendsto.congr' this ?_
  convert Tendsto.add (a := 0) ?_ ha
  · rw [zero_add]
  · have : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝 0) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine tendsto_sub_nhds_zero_iff.mpr ?_
      exact tendsto_id
    convert Tendsto.mul this (tendsto_finset_sum (a := fun k ↦ b k ^ (1:ℝ) - a k ^ (1:ℝ))
      (Finset.Iio k₀) fun k _ ↦ ?_)
    · rw [zero_mul]
    · refine Tendsto.sub ?_ ?_
      · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        exact Real.continuousAt_const_rpow' one_ne_zero
      · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        exact Real.continuousAt_const_rpow' one_ne_zero

theorem tendsto_mul_tsum_of_tendsto_mul_tsum' (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 < v k) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, u k ^ s) (𝓝[>] 1) (𝓝 1) := by
  -- We first need to prove some basic facts
  have h_lim_eq_self : ∀ x : ℝ, Tendsto (fun s : ℝ ↦ x ^ s) (𝓝[>] 1) (𝓝 x) := fun x ↦ by
    convert Tendsto.rpow tendsto_const_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)
      (Or.inr zero_lt_one)
    rw [Real.rpow_one]
  have h_tendsto_zero : ∀ (w : ℕ → ℝ) (t : Finset ℕ),
      Tendsto (fun s : ℝ ↦ (s - 1) * ∑ k in t, w k ^ s) (𝓝[>] 1) (𝓝 0) := fun w t ↦ by
    convert Tendsto.mul (a := 0) ?_ (tendsto_finset_sum t fun k _ ↦ h_lim_eq_self (w k))
    · rw [zero_mul]
    · exact (tendsto_sub_nhds_zero_iff.mpr tendsto_id).mono_left nhdsWithin_le_nhds
  have h_tendsto_one : ∀ (t : Finset ℕ),
      Tendsto (fun s : ℝ ↦ (s - 1) * ∑' (k : {k // k ∉ t}), v k ^ s) (𝓝[>] 1) (𝓝 1) := fun t ↦ by
    refine tendsto_nhdsWithin_congr (fun s hs ↦ ?_) <| (sub_zero (1:ℝ)) ▸
      Tendsto.sub h_res (h_tendsto_zero v t)
    rw [ ← sum_add_tsum_subtype_compl (h_sum hs) t, mul_add, add_sub_cancel_left]
  have h_bdu_le : ∀ (ε : ℝ) (t : Finset ℕ),
      IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s : ℝ ↦ (s - 1) * ∑ k in t, u k ^ s +
        (1 + ε) ^ s * ((s - 1) * ∑' (k : { k // k ∉ t }), v k ^ s) := fun ε t ↦ by
    refine IsBoundedUnder_le_add (h_tendsto_zero u t).isBoundedUnder_le ?_
    exact (Tendsto.mul (h_lim_eq_self (1 + ε)) (h_tendsto_one t)).isBoundedUnder_le
  have h_bdu_ge : ∀ (ε : ℝ) (t : Finset ℕ),
      IsBoundedUnder (· ≥ ·) (𝓝[>] 1) fun s : ℝ ↦ (s - 1) * ∑ k in t, u k ^ s +
        (1 - ε) ^ s * ((s - 1) * ∑' (k : { k // k ∉ t }), v k ^ s) := fun ε t ↦ by
    refine IsBoundedUnder_ge_add (h_tendsto_zero u t).isBoundedUnder_ge ?_
    exact (Tendsto.mul (h_lim_eq_self (1 - ε)) (h_tendsto_one t)).isBoundedUnder_ge
  have h_εbdd : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 :=
    eventually_iff_exists_mem.mpr ⟨Set.Ioc 0 1, Ioc_mem_nhdsWithin_Ioi' zero_lt_one, fun _ h ↦ h⟩
  -- We then prove bounds on liminf and limsup
  have h_bdd : ∀ ⦃ε : ℝ⦄, 0 < ε → ε ≤ 1 →
      1 - ε ≤ liminf (fun s : ℝ ↦ (s - 1) * ∑' k, u k ^ s) (𝓝[>] 1) ∧
        limsup (fun s : ℝ ↦ (s - 1) * ∑' k, u k ^ s) (𝓝[>] 1) ≤ 1 + ε := fun ε hε hε' ↦ by
    obtain ⟨t, ht⟩ := tendsto_mul_tsum_of_tendsto_mul_tsum_aux h_main h_sum hu hv hε hε'
    have h₁ : ∀ᶠ (s : ℝ) in 𝓝[>] 1, _ := eventually_nhdsWithin_of_forall (fun s hs ↦ (ht hs).1)
    have h₂ : ∀ᶠ (s : ℝ) in 𝓝[>] 1, _ := eventually_nhdsWithin_of_forall (fun s hs ↦ (ht hs).2)
    refine ⟨?_, ?_⟩
    · convert liminf_le_liminf h₁ (h_bdu_ge ε t) ?_
      · refine (Tendsto.liminf_eq ?_).symm
        simp_rw [show 𝓝 (1 - ε) = 𝓝 (0 + (1 - ε) * 1) by ring_nf]
        exact (h_tendsto_zero u t).add  <| Tendsto.mul (h_lim_eq_self (1 - ε)) (h_tendsto_one t)
      · exact IsBounded.isCobounded_ge <| IsBoundedUnder.mono_le (h_bdu_le ε t) h₂
    · convert limsup_le_limsup h₂ ?_ (h_bdu_le ε t)
      · refine (Tendsto.limsup_eq ?_).symm
        simp_rw [show 𝓝 (1 + ε) = 𝓝 (0 + (1 + ε) * 1) by ring_nf]
        exact (h_tendsto_zero u t).add  <| Tendsto.mul (h_lim_eq_self (1 + ε)) (h_tendsto_one t)
      · exact IsBounded.isCobounded_le <| IsBoundedUnder.mono_ge (h_bdu_ge ε t) h₁
  -- Finally we get the result by proving that liminf and limsup are equal
  obtain ⟨t, ht⟩ := tendsto_mul_tsum_of_tendsto_mul_tsum_aux h_main h_sum hu hv zero_lt_one le_rfl
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ ?_ ?_
  · refine le_of_frequently_sub_le (Eventually.frequently ?_)
    filter_upwards [h_εbdd] with ε ⟨hε, hε'⟩ using (h_bdd hε hε').1
  · refine le_of_frequently_le_add (Eventually.frequently ?_)
    filter_upwards [h_εbdd] with ε ⟨hε, hε'⟩ using (h_bdd hε hε').2
  · exact (h_bdu_le 1 t).mono_le  (eventually_nhdsWithin_of_forall fun s hs ↦ (ht hs).2)
  · exact (h_bdu_ge 1 t).mono_ge  (eventually_nhdsWithin_of_forall fun s hs ↦ (ht hs).1)

theorem tendsto_mul_tsum_of_tendsto_mul_tsum (hv : ∀ᶠ k in atTop, 0 < v k) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, u k ^ s) (𝓝[>] 1) (𝓝 1) := by
  have hu : ∀ᶠ k in atTop, 0 ≤ u k := by
    rw [Metric.tendsto_nhds] at h_main
    specialize h_main 1 zero_lt_one
    filter_upwards [h_main, hv] with k h₁ h₂
    rw [Pi.div_apply] at h₁
    rw [Real.dist_eq, abs_lt] at h₁
    rw [lt_tsub_iff_left] at h₁
    rw [add_neg_self] at h₁
    rw [div_pos_iff_of_pos_right h₂] at h₁
    exact le_of_lt h₁.1
  obtain ⟨kv, hkv⟩ := eventually_atTop.mp hv
  obtain ⟨ku, hku⟩ := eventually_atTop.mp hu
  let v' : ℕ → ℝ := fun k ↦ if kv ≤ k then v k else 1
  let u' : ℕ → ℝ := fun k ↦ if ku ≤ k then u k else 1
  have hv' : ∀ k, 0 < v' k := by
    intro k
    dsimp only [v']
    split_ifs with h
    · exact hkv k h
    · norm_num
  have hu' : ∀ k, 0 ≤ u' k := by
    intro k
    dsimp only [u']
    split_ifs with h
    · exact hku k h
    · norm_num
  have hvv' : ∀ᶠ k in atTop, v' k = v k := by
    rw [eventually_atTop]
    refine ⟨kv, ?_⟩
    intro k h
    dsimp only [v']
    rw [if_pos h]
  have huu' : ∀ᶠ k in atTop, u k = u' k := by
    rw [eventually_atTop]
    refine ⟨ku, ?_⟩
    intro k h
    dsimp only [u']
    rw [if_pos h]
  have h_main' : Tendsto (u' / v') atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ h_main
    filter_upwards [hvv', huu'] with _ h₁ h₂ using by simp_rw [Pi.div_apply, h₁, h₂]
  have h_sum' : ∀ ⦃s⦄, (1:ℝ) < s → Summable (fun k ↦ (v' k) ^ s) := by
    intro s hs
    refine (IsEquivalent.summable_iff_nat ?_).mp (h_sum hs)
    refine EventuallyEq.isEquivalent ?_
    filter_upwards [hvv'] with _ h using by rw [h]
  have h_res' : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' k, v' k ^ s) (𝓝[>] 1) (𝓝 1) := by
    exact toto h_res h_sum hvv'
  have := tendsto_mul_tsum_of_tendsto_mul_tsum' h_main' h_sum' h_res' hu' hv'
  refine toto this ?_ huu'
  intro s hs
  refine (IsEquivalent.summable_iff_nat ?_).mp (h_sum' hs)
  sorry -- too many similar proofs

end Analysis -/

section Box

theorem BoxIntegral.Box.IsBounded_Icc {ι : Type*} [Fintype ι] (B : BoxIntegral.Box ι) :
    Bornology.IsBounded (BoxIntegral.Box.Icc B) := B.isCompact_Icc.isBounded

theorem BoxIntegral.Box.IsBounded {ι : Type*} [Fintype ι] (B : BoxIntegral.Box ι) :
    Bornology.IsBounded B.toSet :=
  Bornology.IsBounded.subset (BoxIntegral.Box.IsBounded_Icc B) coe_subset_Icc

end Box

noncomputable section

namespace BoxIntegral

open Bornology MeasureTheory Fintype Submodule

variable {ι : Type*} (n : ℕ+)

def UnitBoxPart (ν : ι → ℤ) : BoxIntegral.Box ι where
  lower := fun i ↦ ν i / n
  upper := fun i ↦ ν i / n + 1 / n
  lower_lt_upper := fun _ ↦ by norm_num

@[simp]
theorem UnitBoxPart_mem {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ UnitBoxPart n ν ↔ ∀ i, ν i / n < x i ∧ x i ≤ ν i / n + 1 / n := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBoxPart, Set.mem_Ioc]

def UnitBoxIndex (x : ι → ℝ) : ι → ℤ := fun i ↦ Int.ceil (n * x i) - 1

@[simp]
theorem UnitBoxIndex_apply {x : ι → ℝ} (i : ι) :
    UnitBoxIndex n x i = Int.ceil (n * (x : ι → ℝ) i) - 1 := rfl

variable {n} in
theorem UnitBoxPart_mem_iff_index_eq {x : ι → ℝ} {ν : ι → ℤ} :
    x ∈ UnitBoxPart n ν ↔ UnitBoxIndex n x = ν := by
  rw [UnitBoxPart_mem, Function.funext_iff]
  have h_npos : 0 < (n:ℝ) := Nat.cast_pos.mpr <| PNat.pos n
  simp_rw [UnitBoxIndex_apply n, sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
    add_sub_cancel_right, ← _root_.le_div_iff' h_npos, ← div_lt_iff' h_npos, add_div]

-- Upper right corner
def UnitBoxTag (ν : ι → ℤ) : ι → ℝ := fun i ↦ (ν i + 1) / n

theorem UnitBoxTag_injective : Function.Injective (fun ν : ι → ℤ ↦ UnitBoxTag n ν) := by
  intro _ _ h
  ext i
  have := congr_arg (fun x ↦ x i) h
  dsimp [UnitBoxTag] at this
  field_simp at this
  exact this

theorem UnitBoxTag_mem_unitBoxPart (ν : ι → ℤ) :
    UnitBoxTag n ν ∈ UnitBoxPart n ν := by
  simp_rw [Box.mem_def, UnitBoxTag, UnitBoxPart, Set.mem_Ioc]
  refine fun _ ↦ ⟨?_, by rw [← add_div]⟩
  rw [div_lt_div_right <| Nat.cast_pos.mpr (PNat.pos n)]
  linarith

@[simp]
theorem UnitBoxIndex_tag (ν : ι → ℤ) :
    UnitBoxIndex n (UnitBoxTag n ν) = ν := by
  rw [← UnitBoxPart_mem_iff_index_eq]
  exact UnitBoxTag_mem_unitBoxPart n ν

theorem UnitBoxPart_disjoint {ν ν' : ι → ℤ} :
    ν ≠ ν' ↔ Disjoint (UnitBoxPart n ν).toSet (UnitBoxPart n ν').toSet := by
  rw [not_iff_not.symm, ne_eq, not_not, Set.not_disjoint_iff]
  simp_rw [Box.mem_coe]
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, hx'⟩ ↦ ?_⟩
  · exact ⟨UnitBoxTag n ν, UnitBoxTag_mem_unitBoxPart n ν, h ▸ UnitBoxTag_mem_unitBoxPart n ν⟩
  · rw [← UnitBoxPart_mem_iff_index_eq.mp hx, ← UnitBoxPart_mem_iff_index_eq.mp hx']

theorem UnitBoxPart_injective : Function.Injective (fun ν : ι → ℤ ↦ UnitBoxPart n ν) := by
  intro _ _ h
  contrapose! h
  rw [UnitBoxPart_disjoint] at h
  exact Box.ne_of_disjoint_coe h

variable [Fintype ι]

theorem UnitBoxPart_diam (ν : ι → ℤ) :
    Metric.diam (BoxIntegral.Box.Icc (UnitBoxPart n ν)) ≤ 1 / n := by
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [BoxIntegral.Box.Icc_eq_pi]
  refine EMetric.diam_pi_le_of_le (fun i ↦ ?_)
  rw [Real.ediam_Icc, UnitBoxPart, add_sub_cancel_left, ENNReal.ofReal_div_of_pos,
    ENNReal.ofReal_one]
  exact Nat.cast_pos.mpr n.pos

@[simp]
theorem UnitBoxPart_volume (ν : ι → ℤ) :
    volume (UnitBoxPart n ν : Set (ι → ℝ)) = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc, UnitBoxPart,
    add_sub_cancel_left]
  rw [Finset.prod_const, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr n.pos), ENNReal.ofReal_one,
    ENNReal.ofReal_coe_nat, Finset.card_univ, one_div, one_div, ENNReal.inv_pow]

theorem UnitBoxIndex_setFinite_of_finite_measure {s : Set (ι → ℝ)} (hm : NullMeasurableSet s)
    (hs : volume s ≠ ⊤) :
    Set.Finite {ν : ι → ℤ | ↑(UnitBoxPart n ν) ⊆ s} := by
  have := Measure.finite_const_le_meas_of_disjoint_iUnion₀
    (volume : Measure (ι → ℝ)) (ε := 1 / n ^ card ι) (by norm_num)
    (As := fun ν : ι → ℤ ↦ (UnitBoxPart n ν) ∩ s) ?_ ?_ ?_
  · refine this.subset ?_
    intro ν hν
    rw [Set.mem_setOf, Set.inter_eq_self_of_subset_left hν, UnitBoxPart_volume]
  · intro ν
    refine NullMeasurableSet.inter ?_ hm
    exact (UnitBoxPart n ν).measurableSet_coe.nullMeasurableSet
  · intro ν ν' h
    have := (UnitBoxPart_disjoint n).mp h
    refine Disjoint.aedisjoint ?_
    rw [Set.disjoint_iff_inter_eq_empty]
    dsimp only
    rw [Set.inter_inter_inter_comm]
    rw [Set.disjoint_iff_inter_eq_empty] at this
    rw [this]
    rw [Set.empty_inter]
  · rw [← lt_top_iff_ne_top]
    refine measure_lt_top_of_subset ?_ hs
    aesop

def UnitBoxIndexAdmissible (B : Box ι) : Finset (ι → ℤ) := by
  let A := {ν : ι → ℤ | UnitBoxPart n ν ≤ B}
  refine Set.Finite.toFinset (s := A) ?_
  refine UnitBoxIndex_setFinite_of_finite_measure n ?_ ?_
  · exact B.measurableSet_coe.nullMeasurableSet
  · rw [← lt_top_iff_ne_top]
    refine IsBounded.measure_lt_top ?_
    exact Box.IsBounded B

variable {n} in
theorem UnitBoxIndexAdmissible_iff {B : Box ι} {ν : ι → ℤ} :
    ν ∈ UnitBoxIndexAdmissible n B ↔ UnitBoxPart n ν ≤ B := by
  rw [UnitBoxIndexAdmissible, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

open Classical in
def UnitBoxTaggedPrepartition (B : Box ι) : BoxIntegral.TaggedPrepartition B where
  boxes := Finset.image (fun ν ↦ UnitBoxPart n ν) (UnitBoxIndexAdmissible n B)
  le_of_mem' _ hB := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hB
    exact UnitBoxIndexAdmissible_iff.mp hν
  pairwiseDisjoint := by
    intro _ hB _ hB' h
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hB'
    exact (UnitBoxPart_disjoint n).mp fun h' ↦ h (congrArg (UnitBoxPart n) h')
  tag := by
    intro B'
    by_cases hB' : ∃ ν ∈ UnitBoxIndexAdmissible n B, B' = UnitBoxPart n ν
    · exact UnitBoxTag n hB'.choose
    · exact B.exists_mem.choose
  tag_mem_Icc := by
    intro B'
    split_ifs with hB'
    · have := hB'.choose_spec.1
      rw [UnitBoxIndexAdmissible_iff] at this
      refine Box.coe_subset_Icc ?_
      refine this ?_
      exact UnitBoxTag_mem_unitBoxPart n (Exists.choose hB')
    · exact Box.coe_subset_Icc (B.exists_mem.choose_spec)

variable {n} in
@[simp]
theorem UnitBoxTaggedPrepartition_mem_iff {B B' : Box ι} :
    B' ∈ UnitBoxTaggedPrepartition n B ↔
      ∃ ν ∈ UnitBoxIndexAdmissible n B, UnitBoxPart n ν = B' := by
  classical
  rw [UnitBoxTaggedPrepartition, TaggedPrepartition.mem_mk, Prepartition.mem_mk, Finset.mem_image]

theorem UnitBoxTaggedPrepartition_tag_eq {ν : ι → ℤ} (B : Box ι)
    (hν : ν ∈ UnitBoxIndexAdmissible n B) :
    (UnitBoxTaggedPrepartition n B).tag (UnitBoxPart n ν) = UnitBoxTag n ν := by
  dsimp only [UnitBoxTaggedPrepartition]
  have h : ∃ ν' ∈ UnitBoxIndexAdmissible n B, UnitBoxPart n ν = UnitBoxPart n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h, (UnitBoxTag_injective n).eq_iff, ← (UnitBoxPart_injective n).eq_iff]
  exact h.choose_spec.2.symm

theorem UnitBoxTaggedPrepartition_isHenstock (B : Box ι) :
    (UnitBoxTaggedPrepartition n B).IsHenstock := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := UnitBoxTaggedPrepartition_mem_iff.mp hB
  rw [UnitBoxTaggedPrepartition_tag_eq n B hν]
  exact BoxIntegral.Box.coe_subset_Icc (UnitBoxTag_mem_unitBoxPart n ν)

def HasIntegralVertices (B : Box ι) : Prop :=
  ∃ l u : ι → ℤ, (∀ i, B.lower i = l i) ∧ (∀ i, B.upper i = u i)

variable {n} in
theorem UnitBoxIndex_memAdmissible_iff' {x : ι → ℝ} {B : Box ι} :
  UnitBoxIndex n x ∈ UnitBoxIndexAdmissible n B ↔
    ∀ i, n * B.lower i + 1 ≤ Int.ceil (n * x i) ∧ Int.ceil (n * x i) ≤ n * B.upper i  := by
  simp_rw [UnitBoxIndexAdmissible_iff, Box.le_iff_bounds, UnitBoxPart, UnitBoxIndex, Pi.le_def,
    ← forall_and]
  have : (0:ℝ) < n := Nat.cast_pos.mpr n.pos
  simp_rw [Int.cast_sub, Int.cast_one, ← add_div, le_div_iff' this, div_le_iff' this,
    sub_add_cancel, le_sub_iff_add_le]

theorem UnixBoxIndexAdmissible_of_mem_box {B : Box ι} (hB : HasIntegralVertices B)
    {x : ι → ℝ} (hx : x ∈ B) :
    UnitBoxIndex n x ∈ UnitBoxIndexAdmissible n B := by
  obtain ⟨l, u, hl, hu⟩ := hB
  rw [UnitBoxIndex_memAdmissible_iff']
  intro i
  rw [hl i, hu i, show ((n : ℕ) : ℝ) = (n : ℤ) by rfl, ← Int.cast_mul, ← Int.cast_mul,
    ← Int.cast_one, ← Int.cast_add, Int.cast_le, Int.cast_le, Int.ceil_le]
  rw [Int.add_one_le_ceil_iff, Int.cast_mul, Int.cast_mul, mul_lt_mul_left, _root_.mul_le_mul_left]
  simp_rw [Box.mem_def, Set.mem_Ioc, hl, hu] at hx
  exact hx i
  exact Nat.cast_pos.mpr n.pos
  exact Nat.cast_pos.mpr n.pos

theorem UnitBoxPart_index_mem {B : Box ι} (hB : HasIntegralVertices B) {x : ι → ℝ} (hx : x ∈ B) :
    UnitBoxPart n (UnitBoxIndex n x) ∈ UnitBoxTaggedPrepartition n B := by
  rw [UnitBoxTaggedPrepartition_mem_iff]
  refine ⟨UnitBoxIndex n x, ?_, rfl⟩
  exact UnixBoxIndexAdmissible_of_mem_box n hB hx

theorem UnitBoxTaggedPrepartition_isPartition {B : Box ι} (hB : HasIntegralVertices B) :
    (UnitBoxTaggedPrepartition n B).IsPartition := by
  intro x hx
  use UnitBoxPart n (UnitBoxIndex n x)
  refine ⟨?_, ?_⟩
  · rw [BoxIntegral.TaggedPrepartition.mem_toPrepartition, UnitBoxTaggedPrepartition_mem_iff]
    refine ⟨UnitBoxIndex n x, ?_, rfl⟩
    exact UnixBoxIndexAdmissible_of_mem_box n hB hx
  · exact UnitBoxPart_mem_iff_index_eq.mpr rfl

theorem UnitBoxTaggedPrepartition_isSubordinate (B : Box ι) {r : ℝ} (hr : 0 < r) (hn : 1 / r ≤ n) :
    (UnitBoxTaggedPrepartition n B).IsSubordinate (fun _ ↦ ⟨r, hr⟩) := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := UnitBoxTaggedPrepartition_mem_iff.mp hB
  dsimp
  have t1 : Metric.diam (Box.Icc (UnitBoxPart n ν)) ≤ r := by
    refine le_trans (UnitBoxPart_diam n ν) ?_
    rw [div_le_iff]
    rwa [div_le_iff hr, mul_comm] at hn
    exact Nat.cast_pos.mpr n.pos
  intro x hx
  rw [Metric.mem_closedBall, UnitBoxTaggedPrepartition_tag_eq n B hν]
  have t2 : UnitBoxTag n ν ∈ (BoxIntegral.Box.Icc (UnitBoxPart n ν)) := by
    refine Box.coe_subset_Icc ?_
    exact UnitBoxTag_mem_unitBoxPart _ _
  have t3 := Metric.dist_le_diam_of_mem ?_ hx t2
  exact le_trans t3 t1
  refine IsCompact.isBounded ?_
  exact BoxIntegral.Box.isCompact_Icc (UnitBoxPart n ν)

theorem le_hasIntegralVertices_of_isBounded {ι : Type*} [Finite ι] {s : Set (ι → ℝ)}
    (h : IsBounded s) :
    ∃ B : BoxIntegral.Box ι, HasIntegralVertices B ∧ s ≤ B := by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := Bornology.IsBounded.subset_ball_lt h 0 0
  let C : ℕ+ := ⟨Nat.ceil R, Nat.ceil_pos.mpr hR₁⟩
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine BoxIntegral.Box.mk (fun _ ↦ - C) (fun _ ↦ C ) ?_
    intro _
    norm_num [hR₁]
  · exact fun _ ↦ - C
  · exact fun _ ↦ C
  · simp
  · intro x hx
    have t1 : Metric.ball (0 : ι → ℝ) R ⊆ Metric.ball 0 C := by
      refine Metric.ball_subset_ball ?h
      exact Nat.le_ceil R
    have := hR₂ hx
    have := t1 this
    rw [mem_ball_zero_iff] at this
    rw [pi_norm_lt_iff] at this
    · simp_rw [Real.norm_eq_abs, abs_lt] at this
      simp only [Box.mem_coe, Box.mem_mk, Set.mem_Ioc]
      refine fun i ↦ ⟨?_, ?_⟩
      · exact (this i).1
      · exact le_of_lt (this i).2
    · refine lt_of_lt_of_le hR₁ ?_
      exact Nat.le_ceil R

open scoped Pointwise

variable (c : ℝ) (s : Set (ι → ℝ))

-- abbrev IntegralPoints (c : ℝ) : Set (ι → ℝ) := c • s ∩ span ℤ (Set.range (Pi.basisFun ℝ ι))

-- -- Only keep this version and just prove the equiv with the other one if necessary
abbrev IntegralPoints : Set (ι → ℝ) := s ∩ c⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))

variable (F : (ι → ℝ) → ℝ) (hF : Continuous F)

open scoped BigOperators

-- This is really slow...
theorem Fintype_integralPoints (hs₀ : IsBounded s) : Fintype (IntegralPoints c s) := by
  rw [IntegralPoints, ← coe_pointwise_smul]
  by_cases hc : c = 0
  · rw [hc, inv_zero]
    rw [zero_smul]
    rw [zero_eq_bot, bot_coe]
    exact ofFinite _
  · rw [Zspan.smul _ (inv_ne_zero hc)]
    refine Set.Finite.fintype ?_
    refine Metric.finite_isBounded_inter_isClosed hs₀ ?_
    change IsClosed (span ℤ (Set.range (Basis.isUnitSMul (Pi.basisFun ℝ ι) _))).toAddSubgroup
    exact AddSubgroup.isClosed_of_discrete

def CountingFunction := Nat.card (IntegralPoints c s)

-- Probably inline that instead (and others too?)
abbrev SeriesFunction := ∑' x : IntegralPoints c s, F x

-- theorem IntegralPoints_mem_iff {x : ι → ℝ} :
--     x ∈ IntegralPoints s n ↔ (n:ℝ)⁻¹ • x ∈ IntegralPoints' ι s n := by
--   simp only [Set.mem_inter_iff, SetLike.mem_coe, ne_eq, Nat.cast_eq_zero, PNat.ne_zero,
--     not_false_eq_true, ← Set.mem_smul_set_iff_inv_smul_mem₀, smul_inv_smul₀]

-- def IntegralPointsEquiv : IntegralPoints ι s n ≃ IntegralPoints' ι s n := by
--   refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
--   · rintro ⟨x, hx⟩
--     exact ⟨(n:ℝ)⁻¹ • x, (IntegralPoints_mem_iff ι n s).mp hx⟩
--   · intro _ _ h
--     have := congr_arg ((n:ℝ) • ·) (Subtype.mk_eq_mk.mp h)
--     simpa [smul_inv_smul₀, SetCoe.ext_iff, this]
--   · rintro ⟨y, hy⟩
--     refine ⟨⟨((n:ℝ) • y), ?_⟩, ?_⟩
--     · simpa only [IntegralPoints_mem_iff, ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true,
--       inv_smul_smul₀]
--     · simp only [ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, inv_smul_smul₀]

-- theorem IntegralPointsEquiv_apply (x : IntegralPoints s n) :
--     (IntegralPointsEquiv ι n s x : ι → ℝ) = (n:ℝ)⁻¹ • x := rfl

-- theorem IntegralPointsEquiv_symm_apply (x : IntegralPoints' ι s n) :
--     ((IntegralPointsEquiv ι n s).symm x : ι → ℝ) = (n:ℝ) • x := by
--   have := IntegralPointsEquiv_apply ι n s ((IntegralPointsEquiv ι n s).symm x)
--   simp only [Equiv.apply_symm_apply] at this
--   rw [this]
--   simp

theorem UnitBoxTag_mem_smul_span (ν : ι → ℤ) :
    UnitBoxTag n ν ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
  simp_rw [← SetLike.mem_coe, coe_pointwise_smul, Set.mem_smul_set, SetLike.mem_coe,
    Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom,
    Set.mem_range]
  refine ⟨?_, ?_⟩
  · exact fun i ↦ ν i + 1
  · refine ⟨?_, ?_⟩
    · intro i
      use ν i + 1
      zify
    · ext i
      rw [Pi.smul_apply, smul_eq_mul, UnitBoxTag]
      ring

theorem UnitBoxTag_eq_of_mem_smul_span {x : ι → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) :
    UnitBoxTag n (UnitBoxIndex n x) = x := by
  simp_rw [← SetLike.mem_coe, coe_pointwise_smul, Set.mem_smul_set, SetLike.mem_coe,
    Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom,
    Set.mem_range] at hx
  obtain ⟨ν, hν, rfl⟩ := hx
  ext i
  obtain ⟨y, hy⟩ := hν i
  rw [UnitBoxTag, UnitBoxIndex, Pi.smul_apply, ← hy, smul_eq_mul, ← mul_assoc, mul_inv_cancel,
    one_mul, Int.cast_sub, Int.cast_one, sub_add_cancel]
  rw [Int.ceil_intCast]
  ring
  rw [Nat.cast_ne_zero]
  exact PNat.ne_zero n

theorem UnitBoxIndex_injective_of_mem {x y : ι → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))
    (hy : y ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))
    (h : UnitBoxIndex n x = UnitBoxIndex n y) : x = y := by
  have := congr_arg (UnitBoxTag n ·) h
  dsimp only at this
  rwa [UnitBoxTag_eq_of_mem_smul_span n hx, UnitBoxTag_eq_of_mem_smul_span n hy] at this

theorem UnitBoxTaggedPrepartition_tag_mem {x : ι → ℝ} {B : Box ι} (hB : HasIntegralVertices B)
    (hs₁ : s ≤ B) (hx : x ∈ IntegralPoints n s) :
    (UnitBoxTaggedPrepartition n B).tag (UnitBoxPart n (UnitBoxIndex n x)) ∈ s := by
  rw [UnitBoxTaggedPrepartition_tag_eq, UnitBoxTag_eq_of_mem_smul_span]
  · exact hx.1
  · exact hx.2
  · refine UnixBoxIndexAdmissible_of_mem_box n hB ?_
    exact hs₁ hx.1

theorem SeriesFunction_eq {B : Box ι} (hB : HasIntegralVertices B) (hs₀ : s ≤ B) :
    ∑' x : IntegralPoints n s, F x =
      Finset.sum (UnitBoxTaggedPrepartition n B).toPrepartition.boxes
        fun C ↦ (Set.indicator s F ((UnitBoxTaggedPrepartition n B).tag C)) := by
  classical
  -- have : Fintype (IntegralPoints s n) := by
  --   have : Fintype ((n:ℝ) • s ∩ span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)) := sorry
  --   refine @Fintype.ofEquiv _ _ this ?_
  --   rw [IntegralPoints]

  --   refine Set.Finite.fintype ?_

  --   let T := (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))
  --   have : DiscreteTopology ((n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)) := by

  --     sorry
  --   refine Metric.finite_isBounded_inter_isClosed ?_ ?_
  --   -- refine Bornology.IsBounded.smul₀ ?_ _
  --   -- have := UnitBox_isBounded ι A
  --   refine Bornology.IsBounded.subset ?_ hs₁
  --   exact Box.IsBounded B

  --   -- change IsClosed (span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup
  --   -- exact AddSubgroup.isClosed_of_discrete
  have : IsBounded s := by
    refine IsBounded.subset ?_ hs₀
    exact Box.IsBounded B
  have := Fintype_integralPoints n s this
  rw [tsum_fintype]
  rw [Finset.sum_indicator_eq_sum_filter]
  have : (n:ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact PNat.ne_zero n
  rw [Finset.sum_set_coe (IntegralPoints n s)]
  refine Finset.sum_nbij ?_ ?_ ?_ ?_ ?_
  · exact fun x ↦ UnitBoxPart n (UnitBoxIndex n x)
  · simp_rw [Set.mem_toFinset, Finset.mem_filter]
    intro x hx
    -- have t1 := UnixBoxIndexAdmissible_of_mem_box n hB (hs₁ hx.1)
    rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition]
    · refine ⟨?_, ?_⟩
      · refine UnitBoxPart_index_mem _ hB ?_
        exact hs₀ hx.1
      · rw [UnitBoxTaggedPrepartition_tag_eq]
        rw [UnitBoxTag_eq_of_mem_smul_span]
        exact hx.1
        exact hx.2
        exact UnixBoxIndexAdmissible_of_mem_box n hB (hs₀ hx.1)
  · simp_rw [Set.coe_toFinset]
    intro x hx y hy h
    rw [(UnitBoxPart_injective n).eq_iff] at h
    exact UnitBoxIndex_injective_of_mem n hx.2 hy.2 h
  · intro x hx
    rw [Finset.coe_filter, Set.mem_setOf_eq, BoxIntegral.Prepartition.mem_boxes,
      BoxIntegral.TaggedPrepartition.mem_toPrepartition, UnitBoxTaggedPrepartition_mem_iff] at hx
    obtain ⟨⟨ν, hν, rfl⟩, h⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · exact UnitBoxTag n ν
    · rw [Set.coe_toFinset, Set.mem_inter_iff]
      refine ⟨?_, ?_⟩
      · rwa [UnitBoxTaggedPrepartition_tag_eq] at h
        exact hν
      · rw [← coe_pointwise_smul]
        exact UnitBoxTag_mem_smul_span n ν
    · simp
  · intro x hx
    rw [Set.mem_toFinset] at hx
    rw [UnitBoxTaggedPrepartition_tag_eq, UnitBoxTag_eq_of_mem_smul_span]
    · exact hx.2
    · exact UnixBoxIndexAdmissible_of_mem_box n hB (hs₀ hx.1)

theorem UnitBoxTaggedPrepartition_integralSum' {B : Box ι} (hB : HasIntegralVertices B)
    (hs₀ : s ≤ B) :
    BoxIntegral.integralSum (Set.indicator s F)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
        (UnitBoxTaggedPrepartition n B) = (∑' x : IntegralPoints n s, F x) / n ^ card ι := by
  unfold BoxIntegral.integralSum
  rw [SeriesFunction_eq n s F hB hs₀, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  rintro _ hB
  rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition,
    UnitBoxTaggedPrepartition_mem_iff] at hB
  obtain ⟨_, _, rfl⟩ := hB
  rw [BoxIntegral.BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply, UnitBoxPart_volume,
    smul_eq_mul, mul_comm, ENNReal.toReal_div, ENNReal.one_toReal, ENNReal.toReal_pow,
    ENNReal.toReal_nat, mul_one_div]

theorem UnitBoxTaggedPrepartition_integralSum n {B : Box ι} (hB : HasIntegralVertices B)
    (hs₀ : s ≤ B) :
    BoxIntegral.integralSum (Set.indicator s fun x ↦ 1)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
      (UnitBoxTaggedPrepartition n B) = (CountingFunction n s : ℝ) / n ^ card ι := by
  convert UnitBoxTaggedPrepartition_integralSum' n s (fun _ ↦ (1:ℝ)) hB hs₀
  rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  rfl

variable (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s)

theorem main' :
    Tendsto (fun n : ℕ ↦ (∑' x : IntegralPoints n s, F x) / n ^ card ι)
      atTop (nhds (∫ x in s, F x)) := by
  obtain ⟨B, hB, hs₀⟩ := le_hasIntegralVertices_of_isBounded hs₁
  obtain ⟨R, hR₁, hR₂⟩ := Bornology.IsBounded.subset_ball_lt hs₁ 0 0
  have : ContinuousOn (Set.indicator s (fun x ↦ F x)) (BoxIntegral.Box.Icc B) := sorry
  have main := ContinuousOn.hasBoxIntegral (volume : Measure (ι → ℝ)) this
    BoxIntegral.IntegrationParams.Riemann
  rw [BoxIntegral.hasIntegral_iff] at main
  have : ∫ x in B, Set.indicator s F x = ∫ x in s, F x := by
    rw [MeasureTheory.integral_indicator hs₂]
    rw [Measure.restrict_restrict_of_subset hs₀]
  rw [this] at main

  rw [Metric.tendsto_atTop]
  intro eps h_eps
  specialize main (eps / 2) (half_pos h_eps)
  obtain ⟨r, hr₁, hr₂⟩ := main
  specialize hr₁ 0 rfl -- this say that ∀ x, r x = r 0
  specialize hr₂ 0
  let N : ℕ+ := by
    refine ⟨?_, ?_⟩
    exact Nat.ceil (1 / (r 0 0 : ℝ))
    rw [Nat.ceil_pos, one_div, inv_pos]
    exact (r 0 0).mem
  use N
  intro n hn
  have : ∀ n, N ≤ n →
      BoxIntegral.IntegrationParams.MemBaseSet BoxIntegral.IntegrationParams.Riemann
        B 0 (r 0) (UnitBoxTaggedPrepartition n B) := by
    intro n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : r 0 = fun _ ↦ r 0 0 := Function.funext_iff.mpr hr₁
      rw [this]
      refine UnitBoxTaggedPrepartition_isSubordinate _ _ _ ?_
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
      exact UnitBoxTaggedPrepartition_isHenstock _ _
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
  have hn₀ : 0 < n := lt_of_lt_of_le N.prop hn
  specialize hr₂ _ (this ⟨n, hn₀⟩ hn) (UnitBoxTaggedPrepartition_isPartition ⟨n, hn₀⟩ hB)
  rw [UnitBoxTaggedPrepartition_integralSum'] at hr₂
  refine lt_of_le_of_lt hr₂ ?_
  exact half_lt_self_iff.mpr h_eps
  exact hB
  exact hs₀

theorem main :
    Tendsto (fun n : ℕ ↦ (CountingFunction n s : ℝ) / n ^ card ι)
      atTop (nhds (volume s).toReal) := by
  convert main' s (fun _ ↦ 1) hs₁ hs₂
  · rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    rfl
  · rw [set_integral_const, smul_eq_mul, mul_one]

end BoxIntegral

section Counting

variable {x : ℕ → ℝ} (h₁ : Monotone x) (h₂ : Tendsto x atTop atTop) {l : ℝ}
    (h₃ : Tendsto (fun c : ℝ ↦ Nat.card {i | x i ≤ c} / c) atTop (𝓝 l))

theorem lemma1 (B : ℝ) : Set.Finite {i | x i ≤ B} := by
  simp_rw [show ∀ i, x i ≤ B ↔ ¬ x i > B by aesop]
  rw [← Filter.eventually_cofinite, Nat.cofinite_eq_atTop]
  exact Tendsto.eventually_gt_atTop h₂ B

theorem lemma2 :
    Tendsto (fun k ↦ Nat.card {i | x i ≤ x k - 1} / x k) atTop (𝓝 l) := by
  rw [tendsto_iff_seq_tendsto] at h₃
  specialize h₃ (fun k ↦ x k - 1) (tendsto_atTop_add_const_right atTop _ h₂)
  have : Tendsto (fun k ↦ 1 - (x k)⁻¹) atTop (𝓝 1) := by
    have t1 : Tendsto (fun k ↦ - (x k)⁻¹) atTop (𝓝 0) := by
      rw [show (0:ℝ) = - 0 from neg_zero.symm]
      exact h₂.inv_tendsto_atTop.neg
    convert Tendsto.const_add 1 t1 using 2
    rw [add_zero]
  refine Tendsto.congr' ?_ (mul_one l ▸ (Tendsto.mul h₃ this))
  have h₄ : ∀ᶠ k in atTop, x k - 1 ≠ 0 :=
    (tendsto_atTop_add_const_right atTop _ h₂).eventually_ne_atTop _
  have h₅ : ∀ᶠ k in atTop, x k ≠ 0 := h₂.eventually_ne_atTop _
  filter_upwards [h₄, h₅] with k hk hk'
  simp only [Set.coe_setOf, Function.comp_apply]
  rw [← one_div, one_sub_div hk', div_mul_div_cancel _ hk]

theorem lemma3 : Tendsto (fun k ↦ (k + 1) / x k) atTop (𝓝 l) := by
  have h₅ : ∀ᶠ k in atTop, 0 < x k := Tendsto.eventually_gt_atTop h₂ _
  have lim₁ := lemma2 h₂ h₃
  have lim₂ : Tendsto (fun k ↦ Nat.card {i | x i ≤ x k} / x k) atTop (𝓝 l) := by
    rw [tendsto_iff_seq_tendsto] at h₃
    specialize h₃ (fun k ↦ x k) h₂
    exact h₃
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lim₁ lim₂ ?_ ?_
  · filter_upwards [h₅] with k hk
    rw [div_le_div_right hk,  ← Nat.cast_add_one, Nat.cast_le,
      show k + 1 = Nat.card (Set.Icc 0 k) by simp]
    refine Nat.card_mono ?_ ?_
    · exact Set.finite_Icc 0 k
    · intro i hi
      simp only [Set.mem_Icc, zero_le, true_and]
      contrapose! hi
      have := h₁ (le_of_lt hi)
      simp
      refine lt_of_lt_of_le ?_ this
      norm_num
  · filter_upwards [h₅] with k hk
    rw [div_le_div_right hk, ← Nat.cast_add_one, Nat.cast_le,
      show k + 1 = Nat.card (Set.Icc 0 k) by simp]
    refine Nat.card_mono ?_ ?_
    · exact lemma1 h₂ (x k)
    · exact fun i hi ↦ by
        simp only [Set.mem_setOf_eq]
        exact h₁ hi.2

end Counting

noncomputable section general

open MeasureTheory MeasureTheory.Measure Submodule Filter Fintype BoxIntegral

open scoped Pointwise

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

variable (c : ℝ) (s : Set E)

-- We want to do it the other way around
abbrev LatticePoints  : Set E := c • s ∩ span ℤ (Set.range b)

-- abbrev LatticePoints' (c : ℝ) : Set E := s ∩ c⁻¹ • span ℤ (Set.range b)

def LatticeCountingFunction := Nat.card (LatticePoints b c s)

variable [Fintype ι]

variable {c} in
def EquivIntegralPoints (hc : c ≠ 0) :
    LatticePoints b c s ≃ IntegralPoints c (b.equivFun '' s) := by
  let e := b.equivFun.toEquiv
  let f : (ι → ℝ) ≃ (ι → ℝ) := MulAction.toPerm (Units.mk0 c⁻¹ (inv_ne_zero hc))
  let g := e.trans f
  refine g.subtypeEquiv ?_
  intro a
  simp [g, f, e, Set.mem_smul_set]
  refine ⟨fun ⟨⟨x, hxs, hxa⟩, h₂⟩ ↦ ⟨?_, ?_⟩, ?_⟩
  · refine ⟨x, hxs, ?_⟩
    rw [← hxa]
    rw [LinearEquiv.map_smul]
    rw [Finsupp.coe_smul]
    rw [inv_smul_smul₀ hc]
  · refine ⟨?_, ?_, ?_⟩
    · exact b.equivFun a
    · rw [Basis.mem_span_iff_repr_mem] at h₂
      simp_rw [Basis.mem_span_iff_repr_mem, Basis.equivFun_apply, Pi.basisFun_repr]
      exact h₂
    · simp
  · rintro ⟨⟨x, hxs, hxa⟩, ⟨y, hy, hya⟩⟩
    refine ⟨?_, ?_⟩
    · refine ⟨x, hxs, ?_⟩
      rw [eq_inv_smul_iff₀ hc] at hxa
      rw [← Finsupp.coe_smul, ← LinearEquiv.map_smul] at hxa
      have : Function.Injective b.equivFun := by exact LinearEquiv.injective _
      exact this hxa
    · rw [inv_smul_eq_iff₀ hc] at hya
      rw [smul_inv_smul₀ hc] at hya
      rw [Basis.mem_span_iff_repr_mem]
      simp_rw [Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, hya] at hy
      exact hy

theorem toto2 (hc : c ≠ 0) : LatticeCountingFunction b c s = CountingFunction c (b.equivFun '' s) := by
  refine Nat.card_congr ?_
  exact EquivIntegralPoints b s hc

variable [MeasurableSpace E] [BorelSpace E]

variable [DecidableEq ι] [DecidableEq (BoxIntegral.Box ι)]

theorem main2 (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s) :
    Tendsto (fun n : ℕ ↦ (LatticeCountingFunction b n s : ℝ) / n ^ card ι)
      atTop (𝓝 (volume (b.equivFun '' s)).toReal) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_fintype_basis b
  refine Tendsto.congr' ?_ (main (b.equivFun '' s) ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0]
    intro c hc
    congr
    have := toto2 b c s ?_
    exact this.symm
    refine ne_of_gt ?_
    exact Nat.cast_pos.mpr hc
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hs₁ ⊢
    have := Bornology.IsVonNBounded.image (E := E) (F := ι → ℝ) (σ := RingHom.id ℝ) hs₁
    erw [← LinearMap.coe_toContinuousLinearMap']
    exact this _
  · rw [LinearEquiv.image_eq_preimage]
    have : Continuous b.equivFun.symm := by
      exact LinearMap.continuous_of_finiteDimensional _
    have : Measurable b.equivFun.symm := by
      exact Continuous.measurable this
    exact this hs₂

-- All these theorems should limits on ℕ!!
-- theorem main2' :
--     Tendsto (fun n : ℕ ↦ (LatticeCountingFunction b n s : ℝ) / n ^ card ι)
--       atTop (𝓝 (volume (b.equivFun '' s)).toReal) := by sorry

variable (b₀ : Basis ι ℝ (ι → ℝ)) (s₀ : Set (ι → ℝ)) (hs₀₁ : Bornology.IsBounded s₀)
  (hs₀₂ : MeasurableSet s₀)

theorem main3 :
    Tendsto (fun n : ℕ ↦ (LatticeCountingFunction b₀ n s₀ : ℝ) / n ^ card ι)
      atTop (𝓝 (|(LinearEquiv.det b₀.equivFun : ℝ)| * (volume s₀).toReal)) := by
  convert main2 b₀ s₀ hs₀₁ hs₀₂ using 2
  rw [LinearEquiv.image_eq_preimage]
  rw [← MeasureTheory.Measure.map_apply₀]
  · erw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
    · rw [LinearEquiv.det_coe_symm, inv_inv]
      simp only [LinearEquiv.coe_det, smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply,
        smul_eq_mul, ENNReal.toReal_mul, abs_nonneg, ENNReal.toReal_ofReal]
    · refine IsUnit.ne_zero ?_
      exact LinearEquiv.isUnit_det' _
  · have : Continuous b₀.equivFun.symm := by
      exact LinearMap.continuous_of_finiteDimensional _
    exact Continuous.aemeasurable this
  · exact MeasurableSet.nullMeasurableSet hs₀₂

end general

#exit

section cone

variable {E ι : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

variable (X : Set E) (hX : ∀ (x : E) (r : ℝ), x ∈ X → 0 ≤ r → r • x ∈ X)

variable (F : E → ℝ) (hF₁ : ∀ (x : E) (r : ℝ), 0 ≤ r →  F (r • x) = r ^ card ι * (F x))
  (hF₂ : IsBounded {x | F x ≤ 1})

abbrev ConePoints : Set E := X ∩ span ℤ (Set.range b)

example : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' x : ConePoints b X, F x ^ (- s)) (𝓝[>] 1)
    (𝓝 (volume (b.equivFun '' {x | F x ≤ 1})).toReal) := by

  have : (fun s : ℝ ↦ (s - 1) * ∑' (n : ℕ),
    (n ^ card ι / LatticeCountingFunction b n {x | F x ≤ 1} : ℝ) ^ (- s))
      =ᶠ[𝓝[>] 1] fun s : ℝ ↦ (s - 1) * ∑' x : ConePoints b X, F x ^ (- s) := by sorry
  refine Tendsto.congr' this ?_
  simp_rw [Real.rpow_neg sorry, ← Real.inv_rpow sorry]
  refine tendsto_mul_tsum_of_tendsto_mul_tsum (v := fun k ↦ k) ?_ ?_ ?_ ?_ ?_
  ·
    sorry
  · have := main2' b {x | F x ≤ 1}
    sorry
  · intro s hs
    sorry
  · dsimp
    sorry
  · sorry

end cone

#exit -------------------------------

set_option autoImplicit false

noncomputable section pi

open MeasureTheory Submodule Filter Fintype

open scoped Pointwise NNReal ENNReal

variable (ι : Type*) (A : ℕ+)

def UnitBox : BoxIntegral.Box ι where
  lower := fun _ ↦ -(A:ℝ)
  upper := fun _ ↦ (A:ℝ)
  lower_lt_upper := fun _ ↦ by norm_num

theorem UnitBox_mem (x : ι → ℝ) : x ∈ UnitBox ι A ↔ ∀ i, - A < x i ∧ x i ≤ A := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBox, Set.mem_Ioc]

theorem UnitBox_ball_le [Fintype ι] :
    Metric.ball 0 A ⊆ (UnitBox ι A).toSet := by
  simp_rw [ball_pi _ (Nat.cast_pos.mpr A.pos), BoxIntegral.Box.coe_eq_pi,
    Set.univ_pi_subset_univ_pi_iff, Real.ball_eq_Ioo, UnitBox, Pi.zero_apply, zero_sub, zero_add,
    Set.Ioo_subset_Ioc_self, implies_true, true_or]

theorem UnitBox_le_closedBall [Fintype ι] :
    (UnitBox ι A).toSet ⊆ Metric.closedBall 0 A := by
  simp_rw [closedBall_pi _ (Nat.cast_nonneg A), BoxIntegral.Box.coe_eq_pi,
    Set.univ_pi_subset_univ_pi_iff, Real.closedBall_eq_Icc, UnitBox, Pi.zero_apply, zero_sub,
    zero_add, Set.Ioc_subset_Icc_self, implies_true, true_or]

theorem UnitBox_isBounded [Finite ι] :
    Bornology.IsBounded (UnitBox ι A).toSet :=
  have := Fintype.ofFinite ι
  (Metric.isBounded_iff_subset_closedBall _).mpr ⟨_, UnitBox_le_closedBall ι A⟩

variable (n : ℕ+)

def UnitBoxPart (ν : ι → ℤ) : BoxIntegral.Box ι where
  lower := fun i ↦ ν i / n
  upper := fun i ↦ ν i / n + 1 / n
  lower_lt_upper := fun _ ↦ by norm_num

theorem UnitBoxPart_mem {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ UnitBoxPart ι n ν ↔ ∀ i, ν i / n < x i ∧ x i ≤ ν i / n + 1 / n := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBoxPart, Set.mem_Ioc]

def UnitBoxIndex (x : ι → ℝ) : ι → ℤ := fun i ↦ Int.ceil (n * x i) - 1

theorem UnitBoxIndex_apply {x : ι → ℝ} (i : ι) :
    UnitBoxIndex ι n x i = Int.ceil (n * (x : ι → ℝ) i) - 1 := rfl

theorem UnitBoxPart_mem_iff_index_eq {x : ι → ℝ} {ν : ι → ℤ} :
    x ∈ UnitBoxPart ι n ν ↔ UnitBoxIndex ι n x = ν := by
  rw [UnitBoxPart_mem]
  rw [Function.funext_iff]
  have h_npos : 0 < (n:ℝ) := by
    rw [Nat.cast_pos]
    exact PNat.pos n
  simp_rw [UnitBoxIndex_apply ι n, sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
    add_sub_cancel, ← _root_.le_div_iff' h_npos, ← div_lt_iff' h_npos, add_div]

-- Upper right corner
def UnitBoxTag (ν : ι → ℤ) : ι → ℝ := fun i ↦ (ν i + 1) / n

theorem UnitBoxTag_mem_unitBoxPart (ν : ι → ℤ) :
    UnitBoxTag ι n ν ∈ UnitBoxPart ι n ν := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBoxTag, UnitBoxPart, Set.mem_Ioc]
  intro _
  refine ⟨?_, by rw [← add_div]⟩
  rw [div_lt_div_right <| Nat.cast_pos.mpr (PNat.pos n)]
  linarith

@[simp]
theorem UnitBoxIndex_tag (ν : ι → ℤ) :
    UnitBoxIndex ι n (UnitBoxTag ι n ν) = ν := by
  rw [← UnitBoxPart_mem_iff_index_eq]
  exact UnitBoxTag_mem_unitBoxPart _ _ _

theorem UnitBoxTag_injective : Function.Injective (UnitBoxTag ι n) := by
  intro _ _ h
  ext i
  have := congr_arg (fun x ↦ x i) h
  dsimp [UnitBoxTag] at this
  field_simp at this
  exact this

theorem UnitBoxPart_disjoint {ν ν' : ι → ℤ} :
    ν ≠ ν' ↔ Disjoint (UnitBoxPart ι n ν).toSet (UnitBoxPart ι n ν').toSet := by
  rw [not_iff_not.symm, ne_eq, not_not, Set.not_disjoint_iff]
  simp_rw [BoxIntegral.Box.mem_coe]
  refine ⟨?_, ?_⟩
  · intro h
    exact ⟨UnitBoxTag ι n ν, UnitBoxTag_mem_unitBoxPart ι n ν, h ▸ UnitBoxTag_mem_unitBoxPart ι n ν⟩
  · rintro ⟨x, hx, hx'⟩
    rw [UnitBoxPart_mem_iff_index_eq] at hx
    rw [UnitBoxPart_mem_iff_index_eq] at hx'
    rw [← hx, ← hx']

theorem UnitBoxPart_injective : Function.Injective (UnitBoxPart ι n) := by
  intro _ _ h
  contrapose! h
  rw [UnitBoxPart_disjoint] at h
  exact BoxIntegral.Box.ne_of_disjoint_coe h

variable [Fintype ι] [DecidableEq ι] -- Use Finite instead so Decidable should not be necessary

theorem UnitBoxPart_diam (ν : ι → ℤ) :
    Metric.diam (BoxIntegral.Box.Icc (UnitBoxPart ι n ν)) ≤ 1 / n := by
  rw [Metric.diam]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [BoxIntegral.Box.Icc_eq_pi]
  refine EMetric.diam_pi_le_of_le ?_
  intro i
  rw [Real.ediam_Icc, UnitBoxPart]
  rw [add_sub_cancel', ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one]
  exact Nat.cast_pos.mpr n.pos

@[simp]
theorem UnitBoxPart_volume (ν : ι → ℤ) :
    (volume (UnitBoxPart ι n ν : Set (ι → ℝ))).toReal = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc]
  simp_rw [UnitBoxPart, add_sub_cancel']
  rw [Finset.prod_const, ENNReal.ofReal_div_of_pos, ENNReal.toReal_pow, ENNReal.toReal_div,
    div_pow, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, one_pow, Fintype.card]
  any_goals positivity
  exact Nat.cast_pos.mpr n.pos

def AdmissibleIndex :
  Finset (ι → ℤ) := Fintype.piFinset (fun _ ↦ Finset.Ico (n * - (A:ℤ)) (n * A))

variable {ι A n} in
@[simp]
theorem UnitBoxIndex_admissible_iff {x : ι → ℝ} :
    UnitBoxIndex ι n x ∈ AdmissibleIndex ι A n ↔ x ∈ UnitBox ι A := by
  have h₁ : 0 < (n:ℝ) := Nat.cast_pos.mpr n.pos
  have h₂ : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  simp_rw [UnitBox_mem, AdmissibleIndex, mem_piFinset, Finset.mem_Ico, UnitBoxIndex_apply,
    Int.lt_iff_add_one_le, sub_add_cancel, le_sub_iff_add_le, ← Int.lt_iff_add_one_le, Int.lt_ceil,
    Int.ceil_le,  ← le_div_iff' h₁, ← div_lt_iff' h₁,  Int.cast_mul, mul_div_assoc,
    Int.cast_neg, Int.cast_ofNat, mul_div_cancel' _ h₂]

variable {ι A n} in
theorem UnitBoxPart_le_UnitBox {ν : ι → ℤ} :
    UnitBoxPart ι n ν ≤ UnitBox ι A ↔ ν ∈ AdmissibleIndex ι A n := by
  have h : 0 < (n:ℝ) := Nat.cast_pos.mpr n.pos
  simp_rw [BoxIntegral.Box.le_iff_bounds, UnitBox, UnitBoxPart, AdmissibleIndex, mem_piFinset,
    Finset.mem_Ico, Pi.le_def, ← forall_and, ← add_div, le_div_iff' h, div_le_iff' h,
    Int.lt_iff_add_one_le, ← Int.cast_le (α := ℝ), Int.cast_mul, Int.cast_add, Int.cast_one,
    Int.cast_neg, Int.cast_ofNat]

variable [DecidableEq (BoxIntegral.Box ι)]

def UnitBoxTaggedPrepartition : BoxIntegral.TaggedPrepartition (UnitBox ι A) where
  boxes := Finset.image (fun ν ↦ UnitBoxPart ι n ν) (AdmissibleIndex ι A n)
  le_of_mem' _ hB := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hB
    exact UnitBoxPart_le_UnitBox.mpr hν
  pairwiseDisjoint := by
    intro _ hB _ hB'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hB'
    rw [(UnitBoxPart_injective ι n).ne_iff]
    intro h
    exact (UnitBoxPart_disjoint ι n).mp h
  tag := by
    intro B
    by_cases hB : ∃ ν ∈ AdmissibleIndex ι A n, B = UnitBoxPart ι n ν
    · exact UnitBoxTag ι n hB.choose
    · exact 1
  tag_mem_Icc := by
    intro B
    split_ifs with h
    · refine BoxIntegral.Box.coe_subset_Icc ?_
      rw [BoxIntegral.Box.mem_coe]
      have t2 := UnitBoxPart_le_UnitBox.mpr h.choose_spec.1
      refine t2 ?_
      exact UnitBoxTag_mem_unitBoxPart ι n (Exists.choose h)
    · refine BoxIntegral.Box.coe_subset_Icc ?_
      rw [BoxIntegral.Box.mem_coe, UnitBox_mem]
      intro _
      simp
      refine ⟨?_, ?_⟩
      linarith
      exact A.pos

variable {ι A n} in
@[simp]
theorem mem_UnitBoxTaggedPrepartition_iff {B : BoxIntegral.Box ι} :
    B ∈ UnitBoxTaggedPrepartition ι A n ↔
      ∃ ν ∈ AdmissibleIndex ι A n, UnitBoxPart ι n ν = B := by simp [UnitBoxTaggedPrepartition]

theorem UnitBoxPart_index_mem {x : ι → ℝ} (hx : x ∈ UnitBox ι A) :
    UnitBoxPart ι n (UnitBoxIndex ι n x) ∈ UnitBoxTaggedPrepartition ι A n := by
  rw [mem_UnitBoxTaggedPrepartition_iff]
  refine ⟨UnitBoxIndex ι n x, ?_, rfl⟩
  rw [UnitBoxIndex_admissible_iff]
  exact hx

@[simp]
theorem UnitBoxTaggedPrepartition_tag_eq {ν : ι → ℤ} (hν : ν ∈ AdmissibleIndex ι A n) :
    (UnitBoxTaggedPrepartition ι A n).tag (UnitBoxPart ι n ν) = UnitBoxTag ι n ν := by
  dsimp only [UnitBoxTaggedPrepartition]
  have h : ∃ ν' ∈ AdmissibleIndex ι A n, UnitBoxPart ι n ν = UnitBoxPart ι n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h, (UnitBoxTag_injective ι n).eq_iff, ← (UnitBoxPart_injective ι n).eq_iff]
  exact h.choose_spec.2.symm

theorem UnitBoxTaggedPrepartition_isHenstock :
    (UnitBoxTaggedPrepartition ι A n).IsHenstock := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := mem_UnitBoxTaggedPrepartition_iff.mp hB
  rw [UnitBoxTaggedPrepartition_tag_eq ι A n hν]
  exact BoxIntegral.Box.coe_subset_Icc (UnitBoxTag_mem_unitBoxPart ι n ν)

theorem UnitBoxTaggedPrepartition_isPartition :
    (UnitBoxTaggedPrepartition ι A n).IsPartition := by
  intro x hx
  use UnitBoxPart ι n (UnitBoxIndex ι n x)
  refine ⟨?_, ?_⟩
  · rw [BoxIntegral.TaggedPrepartition.mem_toPrepartition, mem_UnitBoxTaggedPrepartition_iff]
    exact ⟨UnitBoxIndex ι n x, UnitBoxIndex_admissible_iff.mpr hx, rfl⟩
  · exact (UnitBoxPart_mem_iff_index_eq ι n).mpr rfl

theorem UnitBoxTaggedPrepartition_isSubordinate {r : ℝ} (hr : 0 < r) (hn : 1 / r ≤ n) :
    (UnitBoxTaggedPrepartition ι A n).IsSubordinate (fun _ ↦ ⟨r, hr⟩) := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := mem_UnitBoxTaggedPrepartition_iff.mp hB
  dsimp
  have t1 : Metric.diam (BoxIntegral.Box.Icc (UnitBoxPart ι n ν)) ≤ r := by
    refine le_trans (UnitBoxPart_diam ι n ν) ?_
    rw [div_le_iff]
    rwa [div_le_iff hr, mul_comm] at hn
    exact Nat.cast_pos.mpr n.pos
  intro x hx
  rw [Metric.mem_closedBall, UnitBoxTaggedPrepartition_tag_eq ι A n hν]
  have t2 : UnitBoxTag ι n ν ∈ (BoxIntegral.Box.Icc (UnitBoxPart ι n ν)) := by
    refine BoxIntegral.Box.coe_subset_Icc ?_
    exact UnitBoxTag_mem_unitBoxPart _ _ _
  have t3 := Metric.dist_le_diam_of_mem ?_ hx t2
  exact le_trans t3 t1
  refine IsCompact.isBounded ?_
  exact BoxIntegral.Box.isCompact_Icc (UnitBoxPart ι n ν)

variable (s : Set (ι → ℝ))

abbrev IntegralPoints (c : ℝ) : Set (ι → ℝ) := c • s ∩ span ℤ (Set.range (Pi.basisFun ℝ ι))

-- Only keep this version and just prove the equiv with the other one
abbrev IntegralPoints' (c : ℝ) : Set (ι → ℝ) := s ∩ c⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))

variable (F : (ι → ℝ) → ℝ) (hF : Continuous F)

open scoped BigOperators

-- Define c before so that arguments are always in the same order
def CountingFunction (c : ℝ) := Nat.card (IntegralPoints ι s c)

-- Probably inline that instead
abbrev SeriesFunction (c : ℝ) := ∑' x : IntegralPoints ι s c, F x

theorem IntegralPoints_mem_iff {x : ι → ℝ} :
    x ∈ IntegralPoints ι s n ↔ (n:ℝ)⁻¹ • x ∈ IntegralPoints' ι s n := by
  simp only [Set.mem_inter_iff, SetLike.mem_coe, ne_eq, Nat.cast_eq_zero, PNat.ne_zero,
    not_false_eq_true, ← Set.mem_smul_set_iff_inv_smul_mem₀, smul_inv_smul₀]

def IntegralPointsEquiv : IntegralPoints ι s n ≃ IntegralPoints' ι s n := by
  refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact ⟨(n:ℝ)⁻¹ • x, (IntegralPoints_mem_iff ι n s).mp hx⟩
  · intro _ _ h
    have := congr_arg ((n:ℝ) • ·) (Subtype.mk_eq_mk.mp h)
    simpa [smul_inv_smul₀, SetCoe.ext_iff, this]
  · rintro ⟨y, hy⟩
    refine ⟨⟨((n:ℝ) • y), ?_⟩, ?_⟩
    · simpa only [IntegralPoints_mem_iff, ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true,
      inv_smul_smul₀]
    · simp only [ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, inv_smul_smul₀]

theorem IntegralPointsEquiv_apply (x : IntegralPoints ι s n) :
    (IntegralPointsEquiv ι n s x : ι → ℝ) = (n:ℝ)⁻¹ • x := rfl

theorem IntegralPointsEquiv_symm_apply (x : IntegralPoints' ι s n) :
    ((IntegralPointsEquiv ι n s).symm x : ι → ℝ) = (n:ℝ) • x := by
  have := IntegralPointsEquiv_apply ι n s ((IntegralPointsEquiv ι n s).symm x)
  simp only [Equiv.apply_symm_apply] at this
  rw [this]
  simp

theorem UnitBoxTag_mem_smul_span (ν : ι → ℤ) :
    UnitBoxTag ι n ν ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
  simp_rw [← SetLike.mem_coe, coe_pointwise_smul, Set.mem_smul_set, SetLike.mem_coe,
    Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom,
    Set.mem_range]
  refine ⟨?_, ?_⟩
  · exact fun i ↦ ν i + 1
  · refine ⟨?_, ?_⟩
    · intro i
      use ν i + 1
      zify
    · ext i
      rw [Pi.smul_apply, smul_eq_mul, UnitBoxTag]
      ring

theorem UnitBoxTag_eq_of_mem_smul_span {x : ι → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) :
    UnitBoxTag ι n (UnitBoxIndex ι n x) = x := by
  simp_rw [← SetLike.mem_coe, coe_pointwise_smul, Set.mem_smul_set, SetLike.mem_coe,
    Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom,
    Set.mem_range] at hx
  obtain ⟨ν, hν, rfl⟩ := hx
  ext i
  obtain ⟨y, hy⟩ := hν i
  rw [UnitBoxTag, UnitBoxIndex, Pi.smul_apply, ← hy, smul_eq_mul, ← mul_assoc, mul_inv_cancel,
    one_mul, Int.cast_sub, Int.cast_one, sub_add_cancel]
  rw [Int.ceil_intCast]
  ring
  rw [Nat.cast_ne_zero]
  exact PNat.ne_zero n

theorem UnitBoxIndex_injective_of_mem {x y : ι → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))
    (hy : y ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))
    (h : UnitBoxIndex ι n x = UnitBoxIndex ι n y) : x = y := by
  have := congr_arg (UnitBoxTag ι n ·) h
  dsimp only at this
  rwa [UnitBoxTag_eq_of_mem_smul_span ι n hx, UnitBoxTag_eq_of_mem_smul_span ι n hy] at this

theorem UnitBoxTaggedPrepartition_tag_mem {x : ι → ℝ} (hs₁ : s ≤ UnitBox ι A)
    (hx : x ∈ IntegralPoints' ι s n) :
    (UnitBoxTaggedPrepartition ι A n).tag (UnitBoxPart ι n (UnitBoxIndex ι n x)) ∈ s := by
  rw [UnitBoxTaggedPrepartition_tag_eq, UnitBoxTag_eq_of_mem_smul_span]
  exact hx.1
  exact hx.2
  rw [UnitBoxIndex_admissible_iff]
  exact hs₁ hx.1

-- variable (hs₁ : s ≤ UnitBox ι H)

-- theorem Index_admissible_of_mem0 {x : ι → ℝ} (hx : x ∈ IntegralPoints' ι s n) :
--     UnitBoxIndex ι n x ∈ AdmissibleIndex ι lw up n := by
--   rw [← @UnitBox_mem_iff_index]
--   refine hs₁ (Set.mem_of_mem_inter_left hx)

theorem SeriesFunction_eq (hs₁ : s ≤ UnitBox ι A) :
    ∑' x : IntegralPoints ι s n, F ((n:ℝ)⁻¹ • x) =
      Finset.sum (UnitBoxTaggedPrepartition ι A n).toPrepartition.boxes
        fun B ↦ (Set.indicator s F ((UnitBoxTaggedPrepartition ι A n).tag B)) := by
  classical
  simp_rw [← Equiv.tsum_eq (IntegralPointsEquiv ι n s).symm, IntegralPointsEquiv_symm_apply]
  have : Fintype (IntegralPoints' ι s n) := by
    convert Fintype.ofEquiv (IntegralPoints ι s n) (IntegralPointsEquiv ι n s)
    rw [IntegralPoints]
    refine Set.Finite.fintype ?_
    refine Metric.finite_isBounded_inter_isClosed ?_ ?_
    refine Bornology.IsBounded.smul₀ ?_ _
    have := UnitBox_isBounded ι A
    exact Bornology.IsBounded.subset this hs₁
    change IsClosed (span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup
    exact AddSubgroup.isClosed_of_discrete
  rw [tsum_fintype]
  rw [Finset.sum_indicator_eq_sum_filter]
  have : (n:ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact PNat.ne_zero n
  simp_rw [inv_smul_smul₀ this]
  rw [Finset.sum_set_coe (IntegralPoints' ι s n)]
  refine Finset.sum_nbij ?_ ?_ ?_ ?_ ?_
  · exact fun x ↦ UnitBoxPart ι n (UnitBoxIndex ι n x)
  · simp_rw [Set.mem_toFinset, Finset.mem_filter]
    intro x hx
    rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition]
    · refine ⟨?_, ?_⟩
      · refine UnitBoxPart_index_mem ι A n ?_
        exact hs₁ hx.1
      · exact UnitBoxTaggedPrepartition_tag_mem ι A n s hs₁ hx
  · simp_rw [Set.coe_toFinset]
    intro x hx y hy h
    rw [(UnitBoxPart_injective ι n).eq_iff] at h
    exact UnitBoxIndex_injective_of_mem ι n hx.2 hy.2 h
  · intro x hx
    rw [Finset.coe_filter, Set.mem_setOf_eq, BoxIntegral.Prepartition.mem_boxes,
      BoxIntegral.TaggedPrepartition.mem_toPrepartition, mem_UnitBoxTaggedPrepartition_iff] at hx
    obtain ⟨⟨ν, hν, rfl⟩, h⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · exact UnitBoxTag ι n ν
    · rw [Set.coe_toFinset, Set.mem_inter_iff]
      refine ⟨?_, ?_⟩
      · rwa [UnitBoxTaggedPrepartition_tag_eq ι A n hν] at h
      · rw [← coe_pointwise_smul]
        exact UnitBoxTag_mem_smul_span ι n ν
    · simp
  · intro x hx
    rw [Set.mem_toFinset] at hx
    rw [UnitBoxTaggedPrepartition_tag_eq, UnitBoxTag_eq_of_mem_smul_span]
    · exact hx.2
    · rw [UnitBoxIndex_admissible_iff]
      exact hs₁ hx.1

theorem UnitBoxTaggedPrepartition_integralSum' (hs₁ : s ≤ UnitBox ι A) :
    BoxIntegral.integralSum (Set.indicator s F)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
        (UnitBoxTaggedPrepartition ι A n) = (
        ∑' x : IntegralPoints ι s n, F ((n:ℝ)⁻¹ • x)) / n ^ card ι := by
  unfold BoxIntegral.integralSum
  rw [SeriesFunction_eq ι A n s F hs₁, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  rintro _ hB
  rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition,
    mem_UnitBoxTaggedPrepartition_iff] at hB
  obtain ⟨_, _, rfl⟩ := hB
  rw [BoxIntegral.BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply, UnitBoxPart_volume,
    smul_eq_mul, mul_comm, mul_one_div]

theorem UnitBoxTaggedPrepartition_integralSum n (hs₁ : s ≤ UnitBox ι A) :
    BoxIntegral.integralSum (Set.indicator s fun x ↦ 1)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
      (UnitBoxTaggedPrepartition ι A n) = (CountingFunction ι s n : ℝ) / n ^ card ι := by
  convert UnitBoxTaggedPrepartition_integralSum' ι A n s (fun _ ↦ (1:ℝ)) hs₁
  rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  rfl

variable (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s)

theorem main' :
    Tendsto (fun n : ℕ+ ↦ (∑' x : IntegralPoints ι s n, F ((n:ℝ)⁻¹ • x)) / n ^ card ι)
      atTop (nhds (∫ x in s, F x)) := by
  obtain ⟨R, hR₁, hR₂⟩ := Bornology.IsBounded.subset_ball_lt hs₁ 0 0
  let C : ℕ+ := ⟨Nat.ceil R, Nat.ceil_pos.mpr hR₁⟩
  have hs : s ≤ UnitBox ι C := by
    have := UnitBox_ball_le ι C
    refine le_trans ?_ this
    refine le_trans hR₂ (Metric.ball_subset_ball ?_)
    exact Nat.le_ceil _
  have : ContinuousOn (Set.indicator s (fun x ↦ F x)) (BoxIntegral.Box.Icc (UnitBox ι C)) := sorry
  have main := ContinuousOn.hasBoxIntegral (volume : Measure (ι → ℝ)) this
    BoxIntegral.IntegrationParams.Riemann
  rw [BoxIntegral.hasIntegral_iff] at main
  have : ∫ x in (UnitBox ι C), Set.indicator s F x = ∫ x in s, F x := by
    rw [MeasureTheory.integral_indicator hs₂]
    rw [Measure.restrict_restrict_of_subset hs]
  rw [this] at main
  rw [Metric.tendsto_atTop]
  intro eps h_eps
  specialize main (eps / 2) (half_pos h_eps)
  obtain ⟨r, hr₁, hr₂⟩ := main
  specialize hr₁ 0 rfl -- this say that ∀ x, r x = r 0
  specialize hr₂ 0
  let N : ℕ+ := by
    refine ⟨?_, ?_⟩
    exact Nat.ceil (1 / (r 0 0 : ℝ))
    rw [Nat.ceil_pos, one_div, inv_pos]
    exact (r 0 0).mem
  use N
  intro n hn

  have : ∀ n, N ≤ n →
      BoxIntegral.IntegrationParams.MemBaseSet BoxIntegral.IntegrationParams.Riemann
        (UnitBox ι C) 0 (r 0) (UnitBoxTaggedPrepartition ι C n) := by
    intro n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : r 0 = fun _ ↦ r 0 0 := Function.funext_iff.mpr hr₁
      rw [this]
      refine UnitBoxTaggedPrepartition_isSubordinate ι _ _ _ ?_
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
      exact UnitBoxTaggedPrepartition_isHenstock ι _ _
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h

  specialize hr₂ _ (this n hn) (UnitBoxTaggedPrepartition_isPartition ι C n)
  rw [UnitBoxTaggedPrepartition_integralSum'] at hr₂
  refine lt_of_le_of_lt hr₂ ?_
  exact half_lt_self_iff.mpr h_eps
  exact hs

theorem main :
    Tendsto (fun n : ℕ+ ↦ (CountingFunction ι s n : ℝ) / n ^ card ι)
      atTop (nhds (volume s).toReal) := by
  convert main' ι s (fun _ ↦ 1) hs₁ hs₂
  · rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    rfl
  · rw [set_integral_const, smul_eq_mul, mul_one]

end pi

noncomputable section general

open MeasureTheory MeasureTheory.Measure Submodule Filter Fintype

open scoped Pointwise

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

variable (s : Set E)

abbrev LatticePoints (c : ℝ) : Set E := c • s ∩ span ℤ (Set.range b)

abbrev LatticePoints' (c : ℝ) : Set E := s ∩ c⁻¹ • span ℤ (Set.range b)

def LatticeCountingFunction (c : ℝ) := Nat.card (LatticePoints b s c)

variable [Fintype ι]

def EquivIntegralPoints {c : ℝ} (hc : c ≠ 0) : LatticePoints' b s c ≃ IntegralPoints' ι (b.equivFun '' s) c := by
  refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    refine ⟨b.equivFun x, ?_, ?_⟩
    · exact ⟨_, hx.1, rfl⟩
    · -- rw [← coe_pointwise_smul]
      refine ⟨c • b.equivFun x, ?_, ?_⟩
      · rw [SetLike.mem_coe]
        simp_rw [Basis.mem_span_iff_repr_mem, Basis.equivFun_apply,
          Pi.basisFun_repr, Set.mem_range, Pi.smul_apply, smul_eq_mul]
        intro i
        refine ⟨?_, ?_⟩

        sorry
      · simp [inv_smul_smul₀ hc]



theorem toto (c : ℝ) : LatticeCountingFunction b s c = CountingFunction ι (b.equivFun '' s) c := by
  refine Nat.card_congr ?_
  refine Set.BijOn.equiv b.equivFun ?_
  refine (Equiv.image_eq_iff_bijOn b.equivFun.toEquiv).mp ?_
  ext
  rw [LinearEquiv.coe_toEquiv, Set.InjOn.image_inter ((Basis.equivFun b).injective.injOn  _)
    (Set.subset_univ _) (Set.subset_univ _), Set.mem_inter_iff, Set.mem_inter_iff]
  erw [← Submodule.map_coe (b.equivFun.restrictScalars ℤ)]
  simp_rw [image_smul_set, Submodule.map_span, LinearEquiv.restrictScalars_apply, ← Set.range_comp]
  congr!
  ext
  rw [Function.comp_apply, Basis.equivFun_apply, Basis.repr_self]
  rfl

variable [MeasurableSpace E] [BorelSpace E]

variable [DecidableEq ι] [DecidableEq (BoxIntegral.Box ι)]

theorem main2 (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s) :
    Tendsto (fun n : ℕ+ ↦ (LatticeCountingFunction b s n : ℝ) / n ^ card ι)
      atTop (nhds (volume (b.equivFun '' s)).toReal) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_fintype_basis b
  simp_rw [toto]
  convert main ι _ ?_ ?_
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hs₁ ⊢
    have := Bornology.IsVonNBounded.image (E := E) (F := ι → ℝ) (σ := RingHom.id ℝ) hs₁
    erw [← LinearMap.coe_toContinuousLinearMap']
    exact this _
  · rw [LinearEquiv.image_eq_preimage]
    have : Continuous b.equivFun.symm := by
      exact LinearMap.continuous_of_finiteDimensional _
    have : Measurable b.equivFun.symm := by
      exact Continuous.measurable this
    exact this hs₂

variable (b₀ : Basis ι ℝ (ι → ℝ)) (s₀ : Set (ι → ℝ)) (hs₀₁ : Bornology.IsBounded s₀)
  (hs₀₂ : MeasurableSet s₀)

theorem main3 :
    Tendsto (fun n : ℕ+ ↦ (LatticeCountingFunction b₀ s₀ n : ℝ) / n ^ card ι)
      atTop (nhds (|(LinearEquiv.det b₀.equivFun : ℝ)| * (volume s₀).toReal)) := by
  convert main2 b₀ s₀ hs₀₁ hs₀₂ using 2
  rw [LinearEquiv.image_eq_preimage]
  rw [← MeasureTheory.Measure.map_apply₀]
  · erw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
    · rw [LinearEquiv.det_coe_symm, inv_inv]
      simp only [LinearEquiv.coe_det, smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply,
        smul_eq_mul, ENNReal.toReal_mul, abs_nonneg, ENNReal.toReal_ofReal]
    · refine IsUnit.ne_zero ?_
      exact LinearEquiv.isUnit_det' _
  · have : Continuous b₀.equivFun.symm := by
      exact LinearMap.continuous_of_finiteDimensional _
    exact Continuous.aemeasurable this
  · exact MeasurableSet.nullMeasurableSet hs₀₂

end general
