import Mathlib.Algebra.BigOperators.List.Basic
import Mathlib.Data.List.Join
import Mathlib.Data.List.Enum
import Mathlib.Data.List.EraseIdx
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Fin.Basic

namespace List

variable {α : Type*} {l : List α}

def offDiag (l : List α) : List (α × α) :=
  l.enum.bind fun nx ↦ map (Prod.mk nx.2) <| l.eraseIdx nx.1
    
@[simp]
theorem offDiag_nil : offDiag ([] : List α) = [] := rfl

@[simp]
theorem offDiag_singleton (a : α) : offDiag [a] = [] := rfl

theorem length_offDiag' (l : List α) : length l.offDiag = (length l - 1) * length l := by
  have : ∀ x ∈ enum l, length (eraseIdx l x.1) = length l - 1 := fun x hx ↦
    length_eraseIdx <| fst_lt_of_mem_enum hx
  simp [offDiag, (· ∘ ·), map_congr this, mul_comm]

@[simp]
theorem length_offDiag (l : List α) : length l.offDiag = length l ^ 2 - length l := by
  simp [length_offDiag', Nat.mul_sub_right_distrib, sq]

theorem mem_offDiag_iff_get {x : α × α} :
    x ∈ l.offDiag ↔ ∃ i j, i ≠ j ∧ l.get i = x.1 ∧ l.get j = x.2 := by
  rcases x with ⟨x, y⟩
  simp only [offDiag, exists_mem_enum, mem_eraseIdx_iff_get, mem_bind, mem_map]
  simp [@and_comm _ (_ = x), @and_left_comm _ (_ = x), @eq_comm (Fin _), Fin.val_inj]
  
@[simp]
theorem nodup_offDiag : l.offDiag.Nodup ↔ l.Nodup := by
  simp_rw [offDiag, nodup_bind, forall_mem_iff_get, get_enum]
  refine ⟨λ h ↦ ?_, fun h ↦ ⟨fun i ↦ (Pairwise.map _ ?_ (h.sublist <| eraseIdx_sublist ..)), ?_⟩⟩
  · replace h := h.2
    simp only [Nodup, pairwise_iff_get, get_enum] at h ⊢
    intro i j hlt heq
    specialize h (i.cast enum_length.symm) (j.cast enum_length.symm) hlt
    simp only [Fin.cast_trans, Fin.cast_eq_self, Fin.coe_cast, heq] at h
    exact h.of_map (mem_eraseIdx_iff_get.2 ⟨j, ne_of_gt hlt, rfl⟩)
      (mem_eraseIdx_iff_get.2 ⟨i, ne_of_lt hlt, heq⟩)
  · intro a b h
    simp [*]
  · simp_rw [pairwise_iff_get, Disjoint, mem_map, get_enum]
    rintro i j hlt _ ⟨a, -, rfl⟩ ⟨b, -, hab⟩
    simp [h.get_inj_iff, Fin.cast, Fin.val_inj, hlt.ne'] at hab

protected alias ⟨Nodup.of_offDiag, Nodup.offDiag⟩ := nodup_offDiag

theorem Nodup.mem_offDiag (h : l.Nodup) {x : α × α} :
    x ∈ l.offDiag ↔ x.1 ∈ l ∧ x.2 ∈ l ∧ x.1 ≠ x.2 := by
  rcases x with ⟨x, y⟩
  simp_rw [mem_offDiag_iff_get, mem_iff_get, Ne, ← h.get_inj_iff]
  constructor
  · rintro ⟨i, j, hne, rfl, rfl⟩
    exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, hne⟩
  · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩, hne⟩
    exact ⟨i, j, hne, rfl, rfl⟩

theorem Sublist.offDiag {l l' : List α} (h : l <+ l') : l.offDiag <+ l'.offDiag := by
  induction h with
  | slnil => simp
  | cons => _
  | cons₂ => _
  
