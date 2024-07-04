import Mathlib.Data.Real.sqrt
import LeanSensitivity.Basics

-- Definition neatPartition

noncomputable def n' (n : ℕ) := if (n : ℝ)/((Nat.sqrt n) : ℝ)> (((Nat.sqrt n) + 1) : ℝ) then (Nat.sqrt n) + 1 else Nat.sqrt n

def neatPartition {n : ℕ} (P : partition n) := (P.parts.card = Nat.sqrt n ∨ P.parts.card = Nat.sqrt n + 1) ∧
                                            ∀ p ∈ P.parts, (p.card = Nat.sqrt n ∨ p.card = Nat.sqrt n + 1)

set_option maxHeartbeats 0

lemma existance {n_not_zero : n > 0} : ∃ P : partition n, neatPartition P := by
  -- Defining n'
  have n_not_zero' : (n : ℝ) > 0 := by simp [n_not_zero]
  let n' :=         if (n : ℝ)/((Nat.sqrt n) : ℝ) > (((Nat.sqrt n) + 1) : ℝ) then (Nat.sqrt n) + 1 else Nat.sqrt n
  have n'_not_zero : n' > 0 := by
                    by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ)> (((Nat.sqrt n) + 1) : ℝ) <;> simp [h, Nat.sqrt_pos.mpr n_not_zero]
  have n'_le_n : n' ≤ n := by
                    by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ)> (((Nat.sqrt n) + 1) : ℝ) <;> simp [h]
                    · have : (n : ℝ) / (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by
                        simp [division_def, (mul_le_iff_le_one_right n_not_zero'), inv_le_one_iff ]
                        exact Or.inr (Nat.one_le_cast.mpr (Nat.le_sqrt.mpr n_not_zero))
                      have : (Nat.sqrt n : ℝ) + 1 < (n : ℝ) := gt_of_ge_of_gt this h
                      norm_cast at this
                      exact Nat.lt_succ.mp (Nat.le.step this)
                    · exact Nat.sqrt_le_self n

  -- Defining partition
  let part_i (i : Fin n') :=    Finset.filter (λ j : Fin n => j % n' = i) Finset.univ
  let parts_partition :=        Finset.image part_i Finset.univ
  let my_partition : partition n := {
                    parts :=    parts_partition
                    supIndep := by
                                  apply Finset.SupIndep.image
                                  rw [Finset.supIndep_iff_disjoint_erase]
                                  intro i _
                                  apply Finset.disjoint_left.mpr
                                  intro _ ha
                                  simp [Finset.mem_sup] at *
                                  exact (λ x hx => ha.symm ▸ ((propext (Fin.val_eq_val i x)).symm ▸ (ne_comm.mpr hx)))
                    supParts := by
                                  ext x
                                  simp [Finset.mem_sup]
                                  let k : Fin n' := {val:=x % n', isLt := Nat.mod_lt x.val n'_not_zero}
                                  use k
                    not_bot_mem := by
                                  simp
                                  intro x
                                  apply Finset.Nonempty.ne_empty
                                  simp [Finset.fiber_nonempty_iff_mem_image, Finset.mem_image]
                                  use {val:=x, isLt:=Fin.val_lt_of_le x n'_le_n}
                                  simp [Nat.mod_eq_of_lt (Fin.prop x)]

  }

  -- Number of parts
  have card_parts : parts_partition.card = n' := by
    have : parts_partition.card = (@Finset.univ (Fin n') _).card := by
            apply Finset.card_image_iff.mpr
            intro x₁ _ x₂ _ eq
            have := ((Finset.ext_iff.mp eq) {val := x₁, isLt:= Fin.val_lt_of_le x₁ n'_le_n}).mp (by simp [Nat.mod_eq_of_lt (Fin.prop x₁)])
            simp [Nat.mod_eq_of_lt (Fin.prop x₁)] at this
            exact Fin.ext this
    simp [this]

  -- Cardinality parts
  let val_i (i : Fin n') := if (n : ℝ)/((Nat.sqrt n) : ℝ)> (((Nat.sqrt n) + 1) : ℝ) then i < n' - (n'*n' - n) else i < n - n'*n'

  have (i : Fin n') : ((part_i i).card = Nat.sqrt n ∧ ¬ val_i i) ∨ ((part_i i).card = Nat.sqrt n + 1 ∧ val_i i) := by
    by_cases val_i : (val_i i)
    · have : (part_i i).card = (Finset.image (λ j : Fin (Nat.sqrt n + 1) => (i + j*n' : ℕ)) Finset.univ).card := by
        apply Finset.card_congr (λ a => λ _ => a.val) _ (λ _ _ _ _ eq => Fin.ext eq) _
        · intro a ha
          simp at ha; simp
          have aux : a.val % n' + n' * (a.val / n') = a.val:= Nat.mod_add_div (↑a) n'
          simp [ha] at aux

          have : a.val / n' < Nat.sqrt n + 1 := by
                            by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ)> (((Nat.sqrt n) + 1) : ℝ) <;> simp [h]
                            · have aux₁ : ((a.val / (Nat.sqrt n + 1) : ℕ) : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) →
                                                a.val / (Nat.sqrt n + 1) < Nat.sqrt n + 1 := λ h => Nat.cast_lt.mp h
                              apply aux₁

                              have aux₂ : (a.val / (Nat.sqrt n + 1) : ℝ) < (Nat.sqrt n + 1 : ℝ) →
                                                ((a.val / (Nat.sqrt n + 1) : ℕ) : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) :=
                                                λ h => gt_of_gt_of_ge ((@Nat.cast_add_one ℝ _ (Nat.sqrt n)).symm ▸ h)
                                                  ((@Nat.cast_add_one ℝ _ (Nat.sqrt n)).symm ▸ (((@Nat.cast_add_one ℝ _ (Nat.sqrt n)).symm ▸ Nat.cast_div_le)))
                              apply aux₂
                              have aux₃ : (a.val : ℝ) < ((Nat.sqrt n : ℝ) + 1)*((Nat.sqrt n : ℝ) + 1) := by
                                                norm_cast
                                                exact Nat.lt_trans (Fin.prop a) (Nat.lt_succ_sqrt n)
                              rw [propext (div_lt_iff (Nat.cast_add_one_pos (Nat.sqrt n)))]
                              exact aux₃
                            · simp at h
                              have aux₁ : ((a.val / Nat.sqrt n : ℕ) : ℝ) ≤ (a.val : ℝ) / (Nat.sqrt n : ℝ) := Nat.cast_div_le
                              have aux₂ : (a.val : ℝ) / (Nat.sqrt n : ℝ) < (n : ℝ) / (Nat.sqrt n : ℝ) := by
                                                have : (a.val : ℝ) < (n : ℝ) := by simp [Fin.prop a]
                                                rwa [propext (div_lt_div_right (by simp [Nat.sqrt_pos.mpr n_not_zero]))]
                              have aux₃ : ((a.val / Nat.sqrt n : ℕ) : ℝ) < (Nat.sqrt n + 1 : ℝ) → a.val / Nat.sqrt n < Nat.sqrt n + 1 := by
                                                intro h
                                                rwa [← Nat.cast_add_one, Nat.cast_lt] at h
                              exact aux₃ (gt_of_ge_of_gt h (gt_of_gt_of_ge aux₂ aux₁))

          use {val:=(a.val / n'), isLt:=this}
          symm; nth_rw 1 [aux.symm]; symm
          simp
          by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ)> (((Nat.sqrt n) + 1) : ℝ) <;> simp [h, Nat.mul_comm]

        · intro b hb
          simp at hb
          obtain ⟨a, ha⟩ := hb

          have : b < n := by
                          by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ) > (((Nat.sqrt n) + 1) : ℝ) <;> simp [h] at val_i ha
                          · rw [ha.symm]
                            have aux₁ : i.val + a.val * (Nat.sqrt n + 1) <
                                                Nat.sqrt n + 1 - ((Nat.sqrt n + 1)*(Nat.sqrt n + 1) - n) + a.val * (Nat.sqrt n + 1) := by
                                                simp [val_i]
                            have aux₂ : Nat.sqrt n + 1 - ((Nat.sqrt n + 1)*(Nat.sqrt n + 1) - n) + a.val * (Nat.sqrt n + 1) ≤
                                                Nat.sqrt n + 1 - ((Nat.sqrt n + 1)*(Nat.sqrt n + 1) - n) + (Nat.sqrt n) * (Nat.sqrt n + 1) := by
                                                simp [Fin.is_le a]
                            have aux₃ : Nat.sqrt n + 1 - ((Nat.sqrt n + 1)*(Nat.sqrt n + 1) - n) + (Nat.sqrt n) * (Nat.sqrt n + 1) = n := by
                                                have : Nat.sqrt n + 1 ≥ ((Nat.sqrt n + 1)*(Nat.sqrt n + 1) - n) := by
                                                    simp [add_mul_self_eq, (Nat.add_right_comm (Nat.sqrt n) 1 n)]
                                                    rw [← Nat.sub_le_iff_le_add', ← Nat.add_mul]
                                                    have : (Nat.sqrt n + 2) * Nat.sqrt n - Nat.sqrt n = (Nat.sqrt n + 2 - 1) * Nat.sqrt n := by
                                                      rw [Nat.mul_sub_right_distrib]
                                                      simp
                                                    simp [this]
                                                    have : (n : ℝ) > (Nat.sqrt n + 1 : ℝ) * (Nat.sqrt n : ℝ) := (lt_div_iff (Nat.cast_pos.mpr (Nat.sqrt_pos.mpr n_not_zero))).mp h
                                                    norm_cast at this
                                                    exact Nat.le_of_lt this
                                                rw [tsub_add_eq_add_tsub this]
                                                have : Nat.sqrt n + 1 + Nat.sqrt n * (Nat.sqrt n + 1) - ((Nat.sqrt n + 1)*(Nat.sqrt n + 1) - n) =
                                                    Nat.sqrt n + 1 + Nat.sqrt n * (Nat.sqrt n + 1) - (Nat.sqrt n + 1)*(Nat.sqrt n + 1) + n := by
                                                    rw [tsub_tsub_eq_add_tsub_of_le (Nat.le_of_lt (Nat.lt_succ_sqrt n)),
                                                      propext (Nat.sub_eq_iff_eq_add (by simp [← one_add_mul, Nat.one_add (Nat.sqrt n)]))]
                                                    symm; nth_rw 1 [Nat.add_right_comm]; symm
                                                    rw [Nat.add_right_cancel_iff, Nat.sub_add_cancel (by simp [← one_add_mul, Nat.one_add])]
                                                rw [this, (one_add_mul (Nat.sqrt n) (Nat.sqrt n + 1)).symm, add_comm 1 (Nat.sqrt n)]
                                                simp
                            rw [aux₃] at aux₂
                            exact Nat.lt_of_lt_of_le aux₁ aux₂
                          · simp at h
                            rw [ha.symm]
                            have aux₁ : i.val + a.val * Nat.sqrt n < n - Nat.sqrt n * Nat.sqrt n + a.val * Nat.sqrt n := by
                                                simp [val_i]
                            have aux₂ :  n - Nat.sqrt n * Nat.sqrt n + a.val * Nat.sqrt n ≤ n - Nat.sqrt n * Nat.sqrt n + Nat.sqrt n * Nat.sqrt n := by
                                                simp [Nat.sqrt_pos.mpr n_not_zero, Fin.is_le a]
                            have aux₃ : n - Nat.sqrt n * Nat.sqrt n + Nat.sqrt n * Nat.sqrt n  = n := tsub_add_cancel_iff_le.mpr (Nat.sqrt_le n)
                            rw [aux₃] at aux₂
                            exact Nat.lt_of_lt_of_le aux₁ aux₂

          use {val:=b, isLt:=this}
          simp [ha.symm]
          by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ) > (((Nat.sqrt n) + 1) : ℝ) <;> have := Fin.prop i <;> simp [h] at *
          · exact this
          · rw [Nat.mod_eq_of_lt this]

      rw [this]
      apply Or.inr
      constructor
      · have : # (@Finset.univ (Fin (Nat.sqrt n + 1)) _) = Nat.sqrt n + 1 := by simp
        symm; nth_rw 1 [this.symm]; symm
        apply Finset.card_image_iff.mpr
        intro x₁ _ x₂ _ eq
        simp only [gt_iff_lt, add_right_inj, propext (Nat.mul_right_cancel_iff n'_not_zero ↑x₁ ↑x₂)] at eq
        exact Fin.ext eq
      · exact val_i

    · have : (part_i i).card = (Finset.image (λ j : Fin (Nat.sqrt n) => (i + j*n' : ℕ)) Finset.univ).card := by
        apply Finset.card_congr (λ a => λ _ => a.val) _ (λ _ _ _ _ eq => Fin.ext eq) _
        · intro a ha
          simp at ha; simp
          have aux : a.val % n' + n' * (a.val / n') = a.val := Nat.mod_add_div (↑a) n'
          simp [ha] at aux

          have : a.val / n' < Nat.sqrt n := by
                                by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ) > (((Nat.sqrt n) + 1) : ℝ) <;> simp [h] at val_i aux ha <;> by_contra contra <;> simp [h] at contra
                                · have aux₁ : i.val + (Nat.sqrt n + 1) * (a.val / (Nat.sqrt n + 1)) ≥ i.val + (Nat.sqrt n + 1) * Nat.sqrt n := by
                                                    simp [contra]
                                  have aux₂ : i.val + (Nat.sqrt n + 1) * Nat.sqrt n ≥
                                                    Nat.sqrt n + 1 - ((Nat.sqrt n + 1) * (Nat.sqrt n + 1) - n) + (Nat.sqrt n + 1) * Nat.sqrt n := by
                                                    simp [val_i]
                                  have aux₃ : Nat.sqrt n + 1 - ((Nat.sqrt n + 1) * (Nat.sqrt n + 1) - n) + (Nat.sqrt n + 1) * Nat.sqrt n = n := by
                                                    rw [tsub_tsub_eq_add_tsub_of_le (Nat.le_of_lt (Nat.lt_succ_sqrt n)), ← Nat.add_one]
                                                    simp [add_mul_self_eq, add_one_mul]
                                                    have : Nat.sqrt n + 1 + n - (Nat.sqrt n * Nat.sqrt n + 2 * Nat.sqrt n + 1) =
                                                      n - (Nat.sqrt n * Nat.sqrt n + Nat.sqrt n) := by
                                                      nth_rw 1 [Nat.two_mul, add_comm, ← tsub_tsub_eq_add_tsub_of_le (by simp [le_add_left (Nat.le_add_left (Nat.sqrt n) (Nat.sqrt n))])]
                                                      simp [Nat.add_sub_assoc (Nat.le_add_left (Nat.sqrt n) (Nat.sqrt n)) (Nat.sqrt n * Nat.sqrt n), Nat.add_sub_cancel]

                                                    rw [this, tsub_add_cancel_iff_le]
                                                    have aux := (@lt_div_iff _ _  ((Nat.sqrt n : ℝ) + 1) (n : ℝ) _ (Nat.cast_pos.mpr (Nat.sqrt_pos.mpr n_not_zero))).mp h
                                                    norm_cast at aux
                                                    simp [Nat.add_mul] at aux
                                                    exact Nat.le_of_lt aux
                                  have : ¬ a.val ≥ n := by simp [Fin.prop a]
                                  exact this (Nat.le_trans (aux₃ ▸ aux₂) (aux ▸ aux₁))

                                · have aux₁ : i.val + (Nat.sqrt n) * (a.val / Nat.sqrt n) ≥ i.val + Nat.sqrt n * Nat.sqrt n := by
                                                    simp [contra, (Nat.sqrt_pos.mpr n_not_zero)]
                                  have aux₂ : i.val + Nat.sqrt n * Nat.sqrt n ≥ (n - Nat.sqrt n * Nat.sqrt n) + Nat.sqrt n * Nat.sqrt n := by
                                                    simp [val_i]
                                  have aux₃ : (n - Nat.sqrt n * Nat.sqrt n) + Nat.sqrt n * Nat.sqrt n = n := Nat.sub_add_cancel (Nat.sqrt_le n)
                                  have : ¬ a.val ≥ n := by simp [Fin.prop a]
                                  exact this (Nat.le_trans (aux₃ ▸ aux₂) (aux ▸ aux₁))

          use {val:=(a.val / n'),isLt:=this}
          symm; nth_rw 1 [aux.symm]; symm
          simp
          by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ)> (((Nat.sqrt n) + 1) : ℝ) <;> simp [h, Nat.mul_comm]

        · intro b hb
          simp at hb
          obtain ⟨a, ha⟩ := hb
          have sqrt_not_zero : Nat.sqrt n > 0 := Nat.sqrt_pos.mpr n_not_zero

          have : b < n := by
                              by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ) > (((Nat.sqrt n) + 1) : ℝ) <;> simp [h] at val_i ha <;> rw [ha.symm]
                              · have aux₁ := Fin.prop i
                                simp [h] at aux₁
                                have aux₂ : a ≤ Nat.sqrt n - 1 := (Nat.lt_iff_le_pred sqrt_not_zero).mp (Fin.prop a)
                                have aux₃ : i.val + a.val * (Nat.sqrt n + 1) < (Nat.sqrt n + 1) + a.val * (Nat.sqrt n + 1) := by
                                                simp [aux₁]
                                have aux₄ : (Nat.sqrt n + 1) + a.val * (Nat.sqrt n + 1) ≤ (Nat.sqrt n + 1) + (Nat.sqrt n - 1) * (Nat.sqrt n + 1) := by
                                                simp [aux₂]
                                have aux₅ : (Nat.sqrt n + 1) + (Nat.sqrt n - 1) * (Nat.sqrt n + 1) = (1 + (Nat.sqrt n - 1)) * (Nat.sqrt n + 1) := by
                                                nth_rw 1 [← (Nat.one_mul (Nat.sqrt n + 1)), Nat.add_mul]
                                rw [Nat.add_sub_of_le sqrt_not_zero] at aux₅
                                have aux₆ := (@lt_div_iff _ _  ((Nat.sqrt n : ℝ) + 1) (n : ℝ) _ (by simp [sqrt_not_zero])).mp h
                                norm_cast at aux₆
                                exact Nat.lt_trans (Nat.lt_of_lt_of_le aux₃ (aux₅ ▸ aux₄)) (Nat.mul_comm _ _ ▸ aux₆)

                              · have aux₁ := Fin.prop i
                                simp [h] at aux₁
                                have aux₂ : a.val ≤ Nat.sqrt n - 1 := (Nat.lt_iff_le_pred sqrt_not_zero).mp (Fin.prop a)
                                have aux₃ : i.val + a.val * Nat.sqrt n < Nat.sqrt n + a.val * Nat.sqrt n := by
                                                simp [aux₁]
                                have aux₄ : Nat.sqrt n + a.val * Nat.sqrt n ≤ Nat.sqrt n + (Nat.sqrt n - 1) * Nat.sqrt n := by
                                                simp [aux₂, sqrt_not_zero]
                                have aux₅ : Nat.sqrt n + (Nat.sqrt n - 1) * Nat.sqrt n = (1 + (Nat.sqrt n - 1)) * Nat.sqrt n := by
                                                nth_rw 1 [← (Nat.one_mul (Nat.sqrt n)), Nat.add_mul]
                                exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le aux₃ ((Nat.add_sub_of_le sqrt_not_zero ▸ aux₅) ▸ aux₄)) (Nat.sqrt_le n)

          use {val:=b, isLt:=this}
          simp [ha.symm]
          by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ)> (((Nat.sqrt n) + 1) : ℝ) <;> have := Fin.prop i <;> simp [h] <;> simp [h] at this
          · exact this
          · rw [Nat.mod_eq_of_lt this]

      rw [this]
      apply Or.inl
      constructor
      · have : # (@Finset.univ (Fin (Nat.sqrt n)) _) = Nat.sqrt n := by simp
        symm; nth_rw 1 [this.symm]; symm
        apply Finset.card_image_iff.mpr
        intro x₁ _ x₂ _ eq
        simp only [gt_iff_lt, add_right_inj, propext (Nat.mul_right_cancel_iff n'_not_zero ↑x₁ ↑x₂)] at eq
        exact Fin.ext eq
      · exact val_i

  -- Proof partition is neat
  use my_partition
  simp only [neatPartition]
  constructor

  · simp at card_parts
    rw [card_parts]
    by_cases h : (n : ℝ)/((Nat.sqrt n) : ℝ) > (((Nat.sqrt n) + 1) : ℝ) <;> simp [h]

  · intro p hp
    simp at hp
    obtain ⟨i, hp⟩ := hp
    rw [hp.symm]
    cases' (this i) with h h <;> simp at h <;> simp [h.1]
