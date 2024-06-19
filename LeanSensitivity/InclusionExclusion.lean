import Mathlib.Tactic.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Card

open BigOperators symmDiff Nat Function Finset

lemma sup_union_singleton {α β : Type} {f : α → Finset β} {s : Finset α} {x : α} [DecidableEq α] [DecidableEq β] (h : x ∈ s):
  sup s f = (sup (s.erase x) f) ∪ f x := by
        ext a; constructor
        · intro h; rw [mem_sup] at h; rw [mem_union]
          obtain ⟨y, hy⟩ := h
          by_cases val_y : y = x
          exact Or.inr (val_y ▸ hy.2)
          apply Or.inl
          simp [mem_sup]
          use y
          exact ⟨⟨val_y, hy.1⟩, hy.2⟩
        · intro h; simp [mem_union, mem_sup] at h; simp [mem_sup]
          cases' h with h h
          obtain ⟨y, hy⟩ := h; use y;
          exact ⟨hy.1.2, hy.2⟩
          use x

lemma aux_sum {f : α → ℤ} : - Finset.sum s f = Finset.sum s ((-1) * f) := by
  simp

lemma aux_disj_union {a₁ a₂ b : Finset α} [DecidableEq α] (h₁ : Disjoint a₁ b) (h₂ : Disjoint a₂ b) : a₁ ∪ b = a₂ ∪ b → a₁ = a₂ := by
  intro h₃
  rw [@disjoint_left] at h₁ h₂
  rw [ext_iff] at h₃
  ext x
  constructor
  · intro h₄
    have := (h₃ x).mp (by simp [h₄])
    simp [(h₁ h₄)] at this
    exact this
  · intro h₄
    have := (h₃ x).mpr (by simp [h₄])
    simp [(h₂ h₄)] at this
    exact this

lemma aux_inf {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β] {a : Finset α} {f : α → Finset β} {x : α} {h : a ≠ ∅} : a.inf (λ y => f y ∩ f x) = (a ∪ {x}).inf f := by
          ext y
          constructor
          · intro h'
            simp [mem_inf]
            simp [mem_inf] at h'
            intro i hi
            cases' hi with hi hi
            exact (h' i hi).1
            obtain ⟨z, hz⟩ := nonempty_of_ne_empty h
            exact hi ▸ (h' z hz).2

          · intro h'
            simp [mem_inf]
            simp [mem_inf] at h'
            exact λ i hi => ⟨h' i (Or.inl hi), h' x (Or.inr rfl)⟩


lemma inclusion_exclusion' {α β : Type} (f : α → Finset β) (s : Finset α) [Fintype β] [DecidableEq α] [DecidableEq β]:
  (s.sup f).card = ∑ x in (Finset.powerset s \ {∅}), (-1 : ℤ)^(x.card + 1) * (Finset.inf x f).card := by
  set n := s.card with ncard
  clear_value n
  induction' n with n ih generalizing s f
  · simp [Finset.card_eq_zero.mp (id ncard.symm)]
  · obtain ⟨x, x_in_s⟩ : ∃ x : α, x ∈ s := Multiset.card_pos_iff_exists_mem.mp (Nat.lt_of_sub_eq_succ (id ncard.symm))
    let s' := s.erase x
    have s'_card : n = s'.card := (ncard.symm ▸ (Finset.card_erase_of_mem (x_in_s))).symm
    let g := λ y ↦ f y ∩ f x
    have hg : (sup s' f) ∩ f x = sup s' g := by
      ext _
      simp [mem_inter, mem_sup]
      exact ⟨λ h => Exists.elim h.1 (λ y hy => ⟨y, hy.1, hy.2, h.2⟩),
        λ h => Exists.elim h (λ y hy => ⟨⟨y, hy.1, hy.2.1⟩, hy.2.2⟩) ⟩

    calc ↑(sup s f).card
    _ = ↑((sup s' f) ∪ f x).card := by
      rw [← sup_union_singleton x_in_s]

    _ = ↑((sup s' f)).card  + ↑(f x).card - ↑((sup s' f) ∩ f x).card  := by
      rw [@eq_sub_iff_add_eq]
      repeat rw [Int.ofNat_add_out]
      rw [@card_union_add_card_inter]

    _ = ↑((sup s' f)).card  + ↑(f x).card - ↑((sup s' g)).card  := by
      rw [hg]

    _ = ∑ x in powerset s' \ {∅}, (-1) ^ (x.card + 1) * ↑(inf x f).card + ↑(f x).card - ∑ x in powerset s' \ {∅}, (-1) ^ (x.card + 1) * ↑(inf x g).card := by
      rw [ih f s' s'_card, ih g s' s'_card]

    _ = ∑ x in powerset s' \ {∅}, (-1) ^ (x.card + 1) * ↑(inf x f).card - ∑ x in powerset s' \ {∅}, (-1) ^ (x.card + 1) * ↑(inf x g).card + ↑(f x).card := by
      rw [@add_sub_right_comm]

    _ = ∑ x in powerset s' \ {∅}, (-1) ^ (x.card + 1) * ↑(inf x f).card + ∑ x in powerset s' \ {∅}, (-1) ^ (x.card + 1 + 1) * ↑(inf x g).card + ↑(f x).card := by
      simp [_root_.pow_succ (-1)]

    _ = ∑ x in (powerset s \ {∅, {x}}).filter (λ a => x ∉ a),  (-1) ^ (x.card + 1) * ↑(inf x f).card + ∑ x in powerset s' \ {∅}, (-1) ^ (x.card + 1 + 1) * ↑(inf x g).card + ↑(f x).card := by
      rw [add_right_cancel_iff, add_right_cancel_iff]
      apply Finset.sum_bij (λ a _ => a) _ (by simp) _ (λ a _ => rfl)
      · intro a h
        simp [subset_erase] at h
        simp [h]
        exact Ne.symm (ne_of_mem_of_not_mem' (by simp) h.1.2)

      · intro b h
        use b
        simp at h
        push_neg at h
        simp [subset_erase]
        exact ⟨⟨h.1.1, h.2⟩, h.1.2.1⟩


    _ = ∑ x in (powerset s \ {∅, {x}}).filter (λ a => x ∉ a),  (-1) ^ (x.card + 1) * ↑(inf x f).card + ∑ x in (powerset s \ {∅, {x}}).filter (λ a => x ∈ a), (-1) ^ (x.card + 1) * ↑(inf x f).card + ↑(f x).card := by
      rw [add_right_cancel_iff, add_left_cancel_iff]
      apply Finset.sum_bij (λ a _ => a ∪ {x})
      · intro a ha
        simp [subset_erase] at ha
        simp [union_eq_empty, union_subset_iff]
        exact ⟨⟨ha.1.1, x_in_s⟩, not_or.mpr ⟨ha.2, Ne.symm (ne_of_mem_of_not_mem' (by simp) ha.1.2)⟩⟩

      · intro a₁ h₁ a₂ h₂ eq_union
        simp [subset_erase] at h₁ h₂
        exact aux_disj_union (Finset.disjoint_singleton_right.mpr h₁.1.2) (Finset.disjoint_singleton_right.mpr h₂.1.2) eq_union

      · intro b h
        simp at h
        use (b.erase x)
        simp
        constructor
        · exact ⟨erase_subset_erase x h.1.1,
            by rw [Finset.erase_eq_empty_iff]; exact h.1.2⟩
        · have : b = b ∪ {x} := by simp [h.2]
          nth_rw 2 [this]
          exact Finset.erase_union_of_mem (by simp) b

      · intro a h
        have : a.card + 1 = (a ∪ {x}).card := by
          rw [Finset.card_disjoint_union]
          simp
          simp [subset_erase] at h
          exact disjoint_singleton_right.mpr h.1.2
        have aux : a ≠ ∅ := not_mem_singleton.mp (mem_sdiff.mp h).2
        simp [this, (@aux_inf _ _ _ _ _ _ _ _ aux)]


    _ = ∑ x in powerset s \ {∅, {x}}, (-1) ^ (x.card + 1) * ↑(inf x f).card +  ↑(f x).card := by
      rw [@add_right_cancel_iff]
      have h : Disjoint ((powerset s \ {∅, {x}}).filter (λ a => x ∉ a)) ((powerset s \ {∅, {x}}).filter (λ a => x ∈ a)) := by
        rw [@disjoint_filter]
        simp

      have : Finset.disjUnion ((powerset s \ {∅, {x}}).filter (λ a => x ∉ a)) ((powerset s \ {∅, {x}}).filter (λ a => x ∈ a)) h =
        (powerset s \ {∅, {x}}) := by
        ext a
        simp
        exact ⟨λ h' => (and_or_left.mpr h').1, λ h' => and_or_left.mp ⟨h', em' (x ∈ a)⟩⟩
      nth_rw 3 [this.symm]

      exact (Finset.sum_disjUnion h).symm

    _ = ∑ x in powerset s \ {∅}, (-1) ^ (x.card + 1) * ↑(inf x f).card := by
      have : insert {x} (powerset s \ {∅, {x}}) = (powerset s \ {∅}) := by
        ext a
        simp
        constructor
        · intro h'
          cases' h' with h' h'
          · simp [h', x_in_s]
          · exact ⟨h'.1, (not_or.mp h'.2).1 ⟩
        · intro h'
          by_cases val_a : a = {x}
          · exact Or.inl val_a
          · exact Or.inr ⟨h'.1, not_or.mpr ⟨h'.2, val_a⟩⟩

      rw [this.symm, Finset.sum_insert (by simp)]
      simp
      exact Int.add_comm _ _
