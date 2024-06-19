import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Order.Partition.Finpartition

open scoped BigOperators symmDiff

-- notation for finsets
prefix:100 "#" => Finset.card

-- vertices
abbrev vertex (n : ℕ) := Finset (Fin n)
lemma nr_of_vertices (n : ℕ) : Fintype.card (vertex n) = 2^n                   := by simp [vertex]
lemma nr_of_vertices' (n : ℕ) : #(@Finset.univ (vertex n) _) = 2^n             := by simp [Finset.card_univ, nr_of_vertices]

-- vertex sets
abbrev vertex_set (n : ℕ) := (Finset (vertex n))
lemma nr_of_vertex_sets (n : ℕ) : Fintype.card (vertex_set n) = 2^(2^n)        := by simp [vertex_set, Finset.card_univ, nr_of_vertices]
lemma nr_of_vertex_sets' (n : ℕ) : #(@Finset.univ (vertex_set n) _) = 2^(2^n)  := by simp [Finset.card_univ, nr_of_vertex_sets]

abbrev partition (n : ℕ) := Finpartition (@Finset.univ ((Fin n)) _)

-- variables
variable {n : ℕ}
variable {v v₁ v₂ : vertex n}

-- adjacency
abbrev hammingDist (v₁ v₂ : vertex n) := (v₁ ∆ v₂).card
notation "d(" v₁ "," v₂ ")" => hammingDist v₁ v₂

lemma hammingDist_refl (v₁ : vertex n) : d(v₁, v₁) = 0 := by simp
lemma hammingDist_positiv (v₁ v₂ : vertex n) (diff : v₁ ≠ v₂) : d(v₁, v₂) > 0 := by simp [Finset.card_pos, diff]

lemma hammingDist_comm (v₁ v₂ : vertex n) : d(v₁,v₂) = d(v₂,v₁) := congrArg Finset.card (symmDiff_comm v₁ v₂)

lemma aux_symmDiff (v₁ v₂ v : vertex n) : v₁ ∆ v₂ ⊆ v₁ ∆ v ∪ v ∆ v₂ := by
  intro x hx
  simp [Finset.mem_union, Finset.mem_symmDiff] at *
  cases' hx with hx hx
  · exact by_cases (λ val_x : x ∈ v => Or.inr (Or.inl ⟨val_x, hx.2⟩))
      (λ val_x : x ∉ v => Or.inl (Or.inl ⟨hx.1, val_x⟩))
  · exact by_cases (λ val_x : x ∈ v => Or.inl (Or.inr ⟨val_x, hx.2⟩))
      (λ val_x : x ∉ v => Or.inr (Or.inr ⟨hx.1, val_x⟩))


lemma hammingDist_exact_triangle (h₁ : v ⊆ v₁ ∆ v₂) (h₂ : v' = v₁ ∆ v) : d(v₁,v₂) = d(v₁, v') + d(v', v₂) := by
  simp [hammingDist]

  have disjoint_finsets : Disjoint (v₁ ∆ v') (v' ∆ v₂) := by
                                                            simp [Finset.disjoint_left, h₂, Finset.mem_symmDiff]
                                                            intro a ha
                                                            push_neg
                                                            have aux := Finset.mem_symmDiff.mp (h₁ ha)
                                                            simp [ha]
                                                            constructor <;> intro h <;> simp [h] at aux <;> exact aux

  have : v₁ ∆ v₂ = Finset.disjUnion (v₁ ∆ v') (v' ∆ v₂) disjoint_finsets := by
                                                            simp [Finset.Subset.antisymm_iff, h₂]
                                                            constructor <;> intro x hx <;> simp [Finset.mem_symmDiff] at * <;> cases' hx with hx hx
                                                            · simp [hx.1, hx.2]
                                                              exact em (x ∈ v)
                                                            · simp [hx.1, hx.2]
                                                              exact em (x ∈ v)
                                                            · exact Finset.mem_symmDiff.mp (h₁ hx)
                                                            · cases' hx with hx hx <;> simp [hx.1, hx.2]
                                                              · cases' hx.1 with hx' hx'
                                                                · exact hx'.1
                                                                · have aux := h₁ hx'.1
                                                                  simp [Finset.mem_symmDiff, hx.2, hx'.2] at aux
                                                              · push_neg at hx
                                                                by_contra contra
                                                                have aux := h₁ (hx.2.1 contra)
                                                                simp [Finset.mem_symmDiff, contra, hx.1] at aux

  exact this ▸ Finset.card_disjUnion _ _ _


lemma hammingDist_triangle (v v₁ v₂ : vertex n) : d(v₁,v₂) ≤ d(v₁, v) + d(v, v₂) :=
  Nat.le_trans (Finset.card_le_card (aux_symmDiff v₁ v₂ v)) (Finset.card_union_le _ _)


abbrev adjacent (v₁ v₂ : vertex n) := d(v₁,v₂) = 1
infix:60 " ~ " => adjacent

lemma adjacent_comm (v₁ v₂ : vertex n) : v₁ ~ v₂ ↔ v₂ ~ v₁ := by rw [adjacent, hammingDist_comm]

lemma not_eq_of_odd_d (h : ¬Even (d(v₁,v₂))) : v₁ ≠ v₂ := λ c ↦ by simp [hammingDist, c] at h

abbrev degree (v : vertex n) (S : vertex_set n) := # (Finset.filter (λ u => v ~ u) S)
notation "deg(" v "," S ")" => degree v S
notation "deg(" v ")" => degree v Finset.univ

lemma degree_comm (v : vertex n) (S : vertex_set n) : deg(v,S) = # (Finset.filter (λ u => u ~ v) S) := by simp [adjacent_comm]

lemma complete_degree (v : vertex n) : deg(v) = n := by
  let F: Fin n → vertex n := λ i ↦ v ∆ {i}

  have : F.Injective := λ _ _ h ↦ by simp [F] at h; exact h

  calc deg(v)
   _ = #(Finset.image F Finset.univ)      := by
                                              apply congrArg Finset.card
                                              ext a; constructor <;> intro a_in <;> simp at *
                                              · rw [adjacent, hammingDist] at a_in
                                                have ⟨i, h⟩ := Finset.card_eq_one.mp a_in
                                                use i; simp [←h, F]
                                              · obtain ⟨i, v_as_u⟩ := a_in
                                                simp [←v_as_u, adjacent, hammingDist, F]
   _ = #Finset.univ                       := by rw [Finset.card_image_of_injective (Finset.univ) ‹F.Injective›]
   _ = n                                  := by rw [Finset.card_fin n]

lemma complete_degree_iff (v : vertex n) (S : vertex_set n) : deg(v,S) = n → ∀ u, v ~ u → u ∈ S := by
  intro h u hu
  have eq_filter : Finset.filter (λ u => v ~ u) S = Finset.filter (λ u => v ~ u) Finset.univ := by
    have : deg(v,S) = deg(v) := h.symm ▸ (complete_degree v).symm
    exact (Finset.eq_of_superset_of_card_ge (λ _ => by simp) (by simp [this])).symm
  have : u ∈ Finset.filter (λ u => v ~ u) Finset.univ := by simpa [adjacent_comm]
  exact (Finset.mem_filter.mp (eq_filter.symm ▸ this)).1

-- Determining the independence number of the Hypercube

abbrev max_degree (S : vertex_set n) : WithBot ℕ := Finset.max (Finset.image (degree . S) S)
notation "Δ(" S ")" => max_degree S
