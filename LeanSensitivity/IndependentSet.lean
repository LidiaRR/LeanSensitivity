import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Combinatorics.DoubleCounting
import LeanSensitivity.Basics

open scoped BigOperators symmDiff

-- variables
variable {n : ℕ}
variable {v v₁ v₂ : vertex n}

abbrev independent_set (S : vertex_set n) := ∀ v₁ ∈ S, ∀ v₂ ∈ S, ¬ v₁ ~ v₂

def independent_sets (n : ℕ) : Finset (vertex_set n) := Finset.filter (λ S => independent_set S) Finset.univ

lemma empty_set_independent (n : ℕ) : ∅ ∈ (independent_sets n) := by
  simp [independent_sets]
  exact λ v₁ h => ((List.mem_nil_iff v₁).mp h).elim

abbrev independence_number (n : ℕ) : ℕ := Finset.max' (Finset.image Finset.card (independent_sets n)) (Finset.Nonempty.image ⟨∅, empty_set_independent n⟩ (Finset.card))
notation "α(" n ")" => independence_number n

----Upper bound independence number

lemma double_counting_to_complement (_ : v ∈ S) (h : independent_set S) : deg(v,Sᶜ) = n := by
  have {v' : vertex n} (h' : v ~ v') : v' ∈ Sᶜ := by
    by_contra contra; exact (h v ‹v ∈ S›  v' (Finset.not_mem_compl.mp contra)) h'

  have : (Finset.filter (λ u => v ~ u ) Sᶜ) = (Finset.filter (λ u => v ~ u ) Finset.univ) := by
    ext b; constructor <;> intro b_el <;> simp [Finset.filter] at *
    · exact b_el.2
    · exact ⟨this b_el, b_el⟩

  calc # (Finset.filter (λ u => v ~ u ) Sᶜ)
   _ = # (Finset.filter (λ u => v ~ u ) Finset.univ) := by apply congrArg Finset.card; exact this
   _ = n                                             := complete_degree v

lemma double_counting_to_set (v : vertex n) (S : vertex_set n): deg(v,S) ≤ n  := by
  calc deg(v,S)
   _ ≤ # (Finset.filter (λ u => v ~ u ) Finset.univ)    := by apply Finset.card_le_card; intro x; simp
   _ = n                                                := complete_degree v

lemma independence_number_hypercube_ub (n : ℕ) : α(n+1) ≤ 2^n := by
  simp [independence_number, independent_sets]
  intro S Sind

  have double_counting := by
    calc #S * (n+1)
     _ = ∑ a in S, deg(a,Sᶜ)           := (Finset.sum_const_nat (λ _ x ↦ double_counting_to_complement x Sind)).symm
     _ = ∑ b in Sᶜ, # (Finset.filter (λ a => a ~ b) S) := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
     _ = ∑ b in Sᶜ, deg(b,S)           := by simp [←degree_comm]
     _ ≤ #Sᶜ * (n+1)                   := Sᶜ.sum_le_card_nsmul _ _ (λ v _ ↦ double_counting_to_set v S)
  simp at double_counting

  have : #S + #Sᶜ = 2^(n+1) := by simp
  have := (@Nat.pow_succ' 2 n) ▸ (Nat.two_mul S.card).symm ▸ Eq.trans_ge this (Nat.add_le_add_left double_counting S.card)
  simp at this
  exact this

-----Parity construction

def parity_structure {n : ℕ} (S : vertex_set n) := ∀ v₁ ∈ S, ∀ v₂ ∈ S, Even d(v₁,v₂)

def parity_set_is_independent {n : ℕ} (S : vertex_set n) (h : parity_structure S) : independent_set S := by
  intro v₁ v₁_in_S v₂ v₂_in_S
  have h := h v₁ v₁_in_S v₂ v₂_in_S
  by_contra contra
  simp [contra] at h

def even_construction (n : ℕ) := Finset.filter (λ v : vertex n => Even v.card) Finset.univ
def odd_construction (n : ℕ) := Finset.filter (λ v : vertex n => Odd v.card) Finset.univ

lemma even_complement (n : ℕ) : (even_construction n)ᶜ = odd_construction n := by simp [even_construction, odd_construction]

lemma eq_card_even_odd (n : ℕ) {h : n > 0} : #even_construction n = #odd_construction n := by
  let f : vertex n → vertex n := λ v => v ∆ {{val:=0,isLt:=h}}
  have eq_fun {a : vertex n} (ha : a ∈ even_construction n) : (λ v => λ _ => f v) a ha = f a := by simp

  have im_f_even {a : vertex n} (ha : a ∈ even_construction n) : f a ∈ odd_construction n := by
                                                    simp [even_construction] at ha
                                                    simp [odd_construction, symmDiff_def, Finset.card_disjoint_union, disjoint_sdiff_sdiff, Nat.even_add, ha]
                                                    by_cases zero_in_a : {val:=0, isLt:=h} ∈ a
                                                    · rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem zero_in_a]
                                                      simp [(Nat.even_sub ),Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero_of_mem zero_in_a), ha, Finset.sdiff_eq_inter_compl, zero_in_a, ha]
                                                    · have  : {{val:=0,isLt:=h}} \ a = {{val:=0,isLt:=h}} := by simp [zero_in_a]
                                                      simp [zero_in_a, ha, this]
  have im_f_odd {a : vertex n} (ha : a ∈ odd_construction n) : f a ∈ even_construction n := by
                                                    simp [even_construction, symmDiff_def, odd_construction] at *
                                                    by_cases zero_in_a : {val:=0, isLt:=h} ∈ a
                                                    · have sdiff_empty : {{val:=0, isLt:=h}} \ a = ∅ := by simp [zero_in_a]
                                                      simp [sdiff_empty, Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem zero_in_a, Nat.even_sub (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero_of_mem zero_in_a)), ha]
                                                    · simp [zero_in_a, Nat.even_add, ha]

  exact Finset.card_congr (λ v => λ _ => f v) (λ _ ha => (eq_fun ha) ▸ (im_f_even ha))
    (λ _ _ _ _ eq => (by simp at eq; exact eq)) (λ b hb => ⟨f b, by simp [im_f_odd hb]⟩)

lemma even_construction_card (n : ℕ) : #(even_construction (n+1)) = 2^n := by
  have sum_subsets : # (even_construction (n+1)) + # (odd_construction (n+1)) = 2 ^ (n+1) := by
    rw [← Finset.card_union_eq (by simp [← even_complement,disjoint_compl_right])]
    simp [← even_complement, nr_of_vertices']

  rw [(@eq_card_even_odd (n+1) (by simp)).symm, Nat.pow_succ', ← two_mul] at sum_subsets
  simp at sum_subsets
  exact sum_subsets

lemma even_construction_parity_structure : parity_structure (even_construction n) := by
  simp [parity_structure]

  intro v₁ hv₁ v₂ hv₂
  simp [hammingDist, symmDiff_eq]
  rw [Finset.card_disjoint_union (Finset.disjoint_iff_ne.mpr (λ _ ha _ hb => by simp at ha hb; by_contra contra; subst contra; exact hb.2 ha.1)),
        Nat.even_add]

  simp [even_construction] at hv₁ hv₂
  rw [← Finset.sdiff_eq_inter_compl, Nat.even_add.mp ((Finset.card_sdiff_add_card_inter v₁ v₂).symm ▸ hv₁),
    ← (Nat.even_add.mp (((Finset.inter_comm v₂ v₁) ▸ (Finset.card_sdiff_add_card_inter v₂ v₁).symm) ▸ hv₂)), ← Finset.sdiff_eq_inter_compl]


lemma independence_number_hypercube_lb (n : ℕ) : α(n+1) ≥ 2^n := by
  let S := even_construction (n+1)

  have Sind : S ∈ (independent_sets (n+1)) := by simpa [independent_sets, Finset.filter] using (parity_set_is_independent S (even_construction_parity_structure))

  have S_card : #S = 2^n := even_construction_card n
  have : 2^n ∈ (Finset.image Finset.card (independent_sets (n+1))) := S_card ▸ Finset.mem_image_of_mem Finset.card Sind

  exact Finset.le_max' _ (2 ^ n) this

------Exact independence number

lemma independence_number_hypercube (n : ℕ) : α(n+1) = 2^n := by
  exact le_antisymm (independence_number_hypercube_ub n) (independence_number_hypercube_lb n)

----Maximal independent set is parity_structur
lemma max_independent_sets_hypercube {n : ℕ} (S : vertex_set (n+1)) (Sind : independent_set S) (S_card : #S = 2^n) : parity_structure S := by
  by_contra contra
  simp [parity_structure] at contra

  have ⟨b₀, _, h⟩ : ∃ (b : vertex (n+1)) (h : b ∈ Sᶜ), deg(b,S) ≤ n := by

    -- Choose two vertices v₁ and v₂ in S such that d(v₁,v₂) is odd and minimal
    obtain ⟨v₁, _, v₂, _, _⟩ := contra
    let T := Finset.filter (λ x => Odd d(x.1,x.2)) S.offDiag
    have : T.Nonempty := by use ⟨v₁, v₂⟩; simp [T]; exact ⟨ ⟨‹v₁ ∈ S›, ‹v₂ ∈ S›, (not_eq_of_odd_d ‹¬Even d(v₁,v₂)›) ⟩, ‹¬Even (d(v₁,v₂))› ⟩
    obtain ⟨⟨v₁, v₂⟩, h₁, dist_min⟩ := T.exists_min_image (λ (v₁, v₂) ↦ d(v₁,v₂)) ‹T.Nonempty›
    simp [Finset.mem_product, T] at h₁ dist_min
    obtain ⟨⟨_, _, _⟩, not_even⟩ := h₁

    -- Define a vertex one step away from v₁ towards v₂
    have ⟨x, hx⟩ : (v₁ ∆ v₂).Nonempty := Finset.symmDiff_nonempty.mpr ‹v₁ ≠ v₂›
    let v' := v₁ ∆ {x}

    have : v₁ ~ v'    := by simp [v', adjacent, hammingDist]
    have : v' ∈ Sᶜ    := Finset.mem_compl.mpr (λ x ↦ Sind v' x v₁ ‹v₁ ∈ S› ((adjacent_comm v₁ v').mp ‹v₁ ~ v'›))

    -- This vertex has a degree at most n since otherwise we would have a pair of vertices at odd distance closer than v₁ and v₂
    have : deg(v',S) ≤ n := by
      by_contra contra
      have : deg(v',S) = n+1                 := (Nat.le_antisymm (Nat.gt_of_not_le contra) (double_counting_to_set v' S)).symm
      obtain ⟨x', hx'⟩ : (v' ∆ v₂).Nonempty    := Finset.symmDiff_nonempty.mpr (λ c ↦ (Sind v₁ ‹v₁ ∈ S› v₂ ‹v₂ ∈ S›) (c ▸ ‹v₁ ~ v'›))
      let v'' := v₁ ∆ {x, x'}

      have diff : x ≠ x' :=                      by
                                                  by_contra contra; subst contra
                                                  cases' (Finset.mem_symmDiff.mp hx) with hx hx <;> simp [Finset.mem_symmDiff, hx.1, hx.2] at hx'
      have : v'' ~ v' :=                        by
                                                  have : v'' ∆ v' = {x'} := by
                                                    simp [symmDiff_symmDiff_symmDiff_comm]
                                                    simp [symmDiff_eq, diff]
                                                  simp [adjacent, hammingDist, this]
      have :=                                     (complete_degree_iff v' S) (by assumption) v'' ((adjacent_comm  _ _).mp this)
      have pair_subset : {x, x'} ⊆ v₁ ∆ v₂ :=   by
                                                  simp [Finset.insert_subset_iff, hx]
                                                  simp [hx, Finset.mem_symmDiff, diff.symm] at hx'
                                                  simp [Finset.mem_symmDiff]
                                                  cases' hx' with hx' hx' <;> simp [hx'.1, hx'.2]
      have card_two : #{x, x'} = 2 :=           Finset.card_pair diff
      have h₂ : v'' = v₁ ∆ {x, x'} :=           rfl
      have hammingDist_triangle :=              hammingDist_exact_triangle pair_subset h₂
      have symmDiff_v₁_v'' : {x, x'} = v₁ ∆ v'' := by simp
      have : d(v₁,v₂) = d(v'',v₂) + 2        := by
                                                  have : #v₁ ∆ v'' = d(v₁,v'') := rfl
                                                  rwa [card_two.symm, symmDiff_v₁_v'', add_comm (d(v'',v₂)) _, this]
      have subset_aux : v'' ∆ v₂ ⊆ (v₁ ∆ v₂) \ {x, x'} := by
                                                  intro y hy
                                                  simp [Finset.mem_symmDiff] at *
                                                  cases' hy with hy hy <;> simp [hy.1, hy.2]
                                                  · cases' hy.1 with hy' hy'
                                                    · exact hy'
                                                    · have : y ∈ ({x, x'} : Finset (Fin (n+1))):= by simp [hy'.1]
                                                      have aux := pair_subset (this)
                                                      simp [Finset.mem_symmDiff, hy.2, hy'.2] at aux
                                                  · by_cases val_y : y = x ∨ y = x' <;> simp [val_y] at hy
                                                    · have : y ∈ ({x, x'} : Finset (Fin (n+1))):= by simp [val_y]
                                                      have aux := pair_subset (this)
                                                      simp [Finset.mem_symmDiff, hy.1, hy.2] at aux
                                                    · exact ⟨hy.2, val_y⟩
      have : d(v'',v₂) < d(v₁,v₂) :=            by
                                                  simp [hammingDist]
                                                  apply Finset.card_lt_card
                                                  have : (v₁ ∆ v₂) \ {x, x'} ⊂ (v₁ ∆ v₂) := by
                                                    apply Finset.ssubset_iff_exists_subset_erase.mpr
                                                    use x
                                                    constructor
                                                    · have : x ∈ ({x, x'} : Finset (Fin (n+1))) := by simp
                                                      exact pair_subset this
                                                    · rw [Finset.pair_comm, Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase]
                                                      exact Finset.erase_subset x' (Finset.erase (v₁ ∆ v₂) x)
                                                  exact Finset.ssubset_of_subset_of_ssubset subset_aux this
      have : ¬Even d(v'',v₂) :=                  by
                                                  have aux : d(v₁,v₂) ≥ d(v₁,v'') := by simp [hammingDist_triangle]
                                                  rw [((Nat.sub_eq_iff_eq_add' aux).mpr hammingDist_triangle).symm, (Nat.even_sub' aux)]
                                                  simp [not_even, hammingDist, card_two]


      have := dist_min _ _ ‹v'' ∈ S› ‹v₂ ∈ S› (not_eq_of_odd_d ‹¬Even (d(v'',v₂))›) ‹¬Even (d(v'',v₂))›
      exact Nat.not_le_of_lt ‹d(v'',v₂) < d(v₁,v₂)› ‹d(v₁,v₂) ≤ d(v'',v₂)›

    exact ⟨v', ‹v' ∈ Sᶜ›, this⟩

  -- Using this vertex, we can improve the double counting, deriving a contradictiong
  have double_counting := by
    calc #S * (n+1)
     _ = ∑ a in S, deg(a,Sᶜ)                     := (Finset.sum_const_nat (λ _ x ↦ double_counting_to_complement x Sind)).symm
     _ = ∑ b in Sᶜ, # Finset.filter (λ a => a ~ b) S := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
     _ = ∑ b in Sᶜ, deg(b,S)                     := by simp [degree_comm]
     _ = ∑ b in Sᶜ \ {b₀}, deg(b,S) + deg(b₀,S)  := Finset.sum_eq_sum_diff_singleton_add ‹b₀ ∈ Sᶜ› _
     _ ≤ #(Sᶜ \ {b₀}) * (n+1) + deg(b₀,S)        := Nat.add_le_add_right ((Sᶜ \ {b₀}).sum_le_card_nsmul _ _ (λ v _ ↦ double_counting_to_set v S)) deg(b₀,S)
     _ ≤ #(Sᶜ \ {b₀}) * (n+1) + n                := Nat.add_le_add_left h _
     _ < (#Sᶜ - 1) * (n+1) + (n+1)               := by simp [Finset.card_sdiff (Finset.singleton_subset_iff.mpr ‹b₀ ∈ Sᶜ›)]
     _ = #Sᶜ * (n+1)                             := by simp [Nat.mul_sub_right_distrib]; apply Nat.sub_add_cancel; simpa using Finset.card_pos.mpr ⟨b₀, ‹b₀ ∈ Sᶜ›⟩

  have : S.card + Sᶜ.card = 2^(n+1) := by simp

  have := by
    calc #S < #Sᶜ           := by simp at double_counting; exact double_counting
     _ = 2^(n+1) - #S       := (tsub_eq_of_eq_add_rev this.symm).symm
     _ = 2^(n+1) - 2^n      := by rw [‹#S = 2^n›]
     _ = 2^n                := by simp [Nat.pow_succ', Nat.two_mul]

  exact (Nat.ne_of_lt this) S_card
