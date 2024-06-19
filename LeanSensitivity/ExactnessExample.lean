import Mathlib.Data.Fin.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Real.sqrt
import LeanSensitivity.InclusionExclusion
import LeanSensitivity.ParityFamilies
import LeanSensitivity.NeatPartition

-- Auxiliar lemmas

lemma mem_filter_univ {p : α → Prop} [DecidablePred p] [Fintype α] {x : α}: x ∈ Finset.filter p Finset.univ ↔ p x := by
  exact ⟨λ h => (Finset.mem_filter.mp h).2 , λ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩  ⟩

lemma subs_sum {α : Type} (s : Finset α) (f g : α → ℤ): Finset.sum s f - Finset.sum s g = Finset.sum s (λ x => f x - g x) := by
    apply tsub_eq_of_eq_add_rev
    rw [← @Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (λ _ _ => eq_add_of_sub_eq' rfl)


-- Cardinality family

lemma card_family {P : partition n} {n_not_zero : n > 0} : (fam_from_partition P).card = (2^(n-1) + (-1)^(n + P.parts.card + 1) : ℤ) := by
  rw [fam_from_partition, Finset.card_union_eq even_odd_disjoint, Int.ofNat_add]

  have aux_ev := @card_sets n n_not_zero P true
  simp only [parity_set, ite_true] at aux_ev
  rw [aux_ev, odd_eq]

  have aux_odd := @card_sets n n_not_zero P false
  simp only [parity_set, ite_false] at aux_odd
  rw [Int.ofNat_sub (Finset.card_le_card odd_part'_subs), aux_odd, ← add_comm_sub, subs_sum]

  have : (fun x : Finset (Finset (Fin n) ) =>
    (-1 : ℤ) ^ (x.card + 1) * (if (Finset.sup x id).card = n then (ε' n true) else 2 ^ (n - (Finset.sup x id).card - 1)) -
    (-1 : ℤ) ^ (x.card + 1) * (if (Finset.sup x id).card = n then (ε' n false) else 2 ^ (n - (Finset.sup x id).card - 1)) ) =
    (λ x => (-1 : ℤ) ^ (x.card + 1) * (if (Finset.sup x id).card = n then ((ε' n true : ℤ) - (ε' n false : ℤ)) else 0)) := by
    ext x
    rw [← Int.mul_sub, Int.mul_eq_mul_left_iff (Int.neg_one_pow_ne_zero)]
    repeat rw [Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat]
    rw [(apply_ite₂ HSub.hSub ((x.sup id).card = n) (ε' n true : ℤ) (2 ^ (n - (Finset.sup x id).card - 1) : ℤ) (ε' n false : ℤ) (2 ^ (n - (Finset.sup x id).card - 1) : ℤ))]
    exact if_congr (by simp) (rfl) (by simp)
  simp [this, mul_ite, Finset.sum_ite]

  have : Finset.filter (λ x => (x.sup id).card = n) (Finset.powerset P.parts \ {∅}) = {P.parts} := by
    ext s
    constructor
    · intro h
      rw [Finset.mem_filter] at h
      exact Finset.mem_singleton.mpr (@total_set_part _ n_not_zero P _ h.1 h.2)
    · simp
      intro h
      simp [h]
      exact ⟨parts_not_empty n_not_zero, by simp [Finpartition.supParts]⟩
  simp [this]

  have := @card_par false n n_not_zero
  simp [par_fun] at this
  simp [this, add_comm, ε', ε]
  rw [add_comm, add_left_inj, ← Int.mul_sub]

  have : (((1 : ℕ) - n%2 : ℕ) - n%2 : ℤ) = (-1)^n := by
    simp [Int.ofNat_sub (Nat.lt_succ_iff.mp (Nat.mod_lt n (by simp)))]
    rw [Int.sub_sub, ← Int.two_mul]
    by_cases par_n : Even n
    · simp [par_n]
      norm_cast
      exact even_iff_two_dvd.mp par_n
    · simp [par_n]
      rw [@Nat.not_even_iff] at par_n
      have : (n : ℤ) % 2 = 1 := by norm_cast
      simp [this]

  rw [this, ← @pow_add]
  exact congrArg (HPow.hPow (-1)) (Nat.add_comm (P.parts.card + 1) n)

-- Max degree

lemma adj_vertices {n : ℕ} {u v : vertex n} (h : u ~ v) : ∃ a, (a ∈ v ∧ v.erase a = u) ∨ (a ∈ u ∧ u.erase a = v) := by
  simp [adjacent, hammingDist, symmDiff, Finset.card_eq_one] at h
  obtain ⟨a, ha⟩ := h
  use a
  simp [@Finset.eq_singleton_iff_unique_mem] at ha
  cases' ha.1 with ha' ha'
  · apply Or.inr
    simp [ha'.1]
    ext x; simp
    constructor
    · intro ⟨h1, h2⟩
      by_contra contra
      exact h1 (ha.2 x (by simp [h2, contra]))
    · intro h
      constructor
      · by_contra contra
        exact ha'.2 (contra ▸ h)
      · by_contra contra
        rw [(ha.2 x (by simp [h, contra]))] at h
        exact ha'.2 h
  · apply Or.inl
    simp [ha'.1]
    ext x; simp
    constructor
    · intro ⟨h1, h2⟩
      by_contra contra
      exact h1 (ha.2 x (by simp [h2, contra]))
    · intro h
      constructor
      · by_contra contra
        exact ha'.2 (contra ▸ h)
      · by_contra contra
        rw [(ha.2 x (by simp [h, contra]))] at h
        exact ha'.2 h

lemma parity_adjacent_even {n : ℕ} {u v : vertex n} (h : u ~ v) (h' : Even (#v)) : ¬ Even (#u) := by
  have ⟨a, ha⟩ := adj_vertices h
  cases' ha with ha ha
  · simp [← ha.2, Finset.card_erase_eq_ite, ha.1]
    apply Nat.even_add_one.mp
    rw [Nat.sub_add_cancel (Finset.card_pos.mpr ⟨a, ha.1⟩)]
    exact h'
  · have : insert a v = u := by
      ext x; simp
      have := ha.2
      simp [Finset.ext_iff] at this
      have := this x
      constructor
      · intro h
        cases' h with h h
        · exact (h.symm ▸ ha.1)
        · simp [h] at this
          exact this.2
      · intro h
        by_cases val_x : x = a
        · simp [val_x]
        · simp [h, val_x] at this
          simp [this]
    have a_not_v : a ∉ v := by simp [← ha.2]
    simp [this.symm, Finset.card_insert_eq_ite, a_not_v, Nat.even_add, h']

lemma parity_adjacent_odd {n : ℕ} {u v : vertex n} (h : u ~ v) (h' : ¬ Even (#v)) : Even (#u) := by
  have ⟨a, ha⟩ := adj_vertices h
  cases' ha with ha ha
  · simp [← ha.2, Finset.card_erase_eq_ite, ha.1]
    exact (Nat.even_sub (Finset.card_pos.mpr ⟨a, ha.1⟩)).mpr (by simp [h'])
  · have : insert a v = u := by
      ext x; simp
      have := ha.2
      simp [Finset.ext_iff] at this
      have := this x
      constructor
      · intro h
        cases' h with h h
        · exact (h.symm ▸ ha.1)
        · simp [h] at this
          exact this.2
      · intro h
        by_cases val_x : x = a
        · simp [val_x]
        · simp [h, val_x] at this
          simp [this]
    have a_not_v : a ∉ v := by simp [← ha.2]
    simp [← this, Finset.card_insert_eq_ite, a_not_v, Nat.even_add, h']

lemma degree_fam {P : partition n} {n_not_zero : n > 0} {neat_p: neatPartition P} : ∀ v ∈ (fam_from_partition P), deg(v, (fam_from_partition P)) ≤ Nat.sqrt n + 1 := by
  intro v hv
  simp [fam_from_partition, degree] at *
  cases' hv with hv hv
  · simp [even_part] at hv
    by_cases deg_v : deg(v,fam_from_partition P) = 0
    · simp [fam_from_partition] at deg_v
      simp [deg_v]
    · have aux₁ {u : vertex n} (h : v ~ u) (h' : u ∈ fam_from_partition P) : u ∈ odd_part P := by
        by_contra contra
        simp [fam_from_partition, contra, even_part] at h'
        exact (parity_adjacent_even ((adjacent_comm u v).mpr h) hv.1) h'.1

      have aux₂ {u : vertex n} (h : v ~ u) (h' : u ∈ fam_from_partition P) : u ⊆ v := by
        have ⟨a, aux⟩ := adj_vertices h
        have : v ⊆ u ∨ u ⊆ v := by
          cases' aux with aux aux
          · apply Or.inl
            rw [← aux.2]
            intro b
            simp
          · apply Or.inr
            rw [← aux.2]
            intro b
            simp
        have : u ⊆ v := by
          by_contra contra
          simp [contra] at this
          obtain ⟨p, hp⟩ := hv.2
          have aux := aux₁ h h'
          simp [odd_part] at aux
          exact (aux.2 p hp.1) (Finset.Subset.trans hp.2 this)
        exact this

      have aux₃ {u : vertex n} (h : v ~ u) (h' : u ∈ fam_from_partition P) : ∃ a ∈ v, v.erase a = u := by
        have ⟨a, ha⟩ := adj_vertices h
        use a
        by_contra contra
        simp [contra] at ha
        have : v ⊂ u := by
          simp [← ha.2, Finset.ssubset_iff]
          use a
          simp [ha.1]
        rw [Finset.ssubset_def] at this
        exact this.2 (aux₂ h h')

      have aux₄ : ∃ x ∈ odd_part P, v ~ x := by
        simp [Finset.filter_eq_empty_iff] at deg_v
        push_neg at deg_v
        obtain ⟨u, hu, adj⟩ := deg_v
        use u
        constructor
        · simp [fam_from_partition] at hu
          have : u ∉ even_part P := by
            have : ¬ Even (#u) := by
              have ⟨a, ha, a_eq⟩ := aux₃ adj (by simp [fam_from_partition, hu])
              simp [← a_eq, Finset.card_erase_eq_ite, ha]
              have : #v > 0 := by
                apply Finset.card_pos.mpr
                use a
              exact Nat.even_add_one.mp ((Nat.sub_add_cancel this).symm ▸ hv.1)
            simp [even_part, this]
          simp [this] at hu
          exact hu
        · exact adj

      have aux₅ : ∃! p, p ∈ P.parts ∧ p ⊆ v := by
        apply exists_unique_of_exists_of_unique hv.2
        intro y₁ y₂ hy₁ hy₂
        by_contra contra
        have ⟨u, hu, adj⟩ := aux₄
        have ⟨a, _, erase_eq⟩ := aux₃ adj (by simp [fam_from_partition, hu])
        simp [odd_part] at hu
        have hy₁' : a ∈ y₁ := by
          by_contra contra
          have : y₁ ⊆ u := by
            rw [← erase_eq]
            intro b hb; simp; constructor
            · by_contra contra'
              exact contra (contra' ▸ hb)
            · exact hy₁.2 hb
          exact (hu.2 y₁ hy₁.1) this
        have hy₂' : a ∈ y₂ := by
          by_contra contra
          have : y₂ ⊆ u := by
            rw [← erase_eq]
            intro b hb; simp; constructor
            · by_contra contra'
              exact contra (contra' ▸ hb)
            · exact hy₂.2 hb
          exact (hu.2 y₂ hy₂.1) this
        have disjoint := P.supIndep
        simp [Finset.SupIndep] at disjoint
        have : {y₂} ⊆ P.parts := by simp [hy₂.1]
        have := disjoint this hy₁.1 (by simp [contra])
        simp [Finset.sup_singleton, Disjoint] at this
        have := @this {a} (by simp [hy₁']) (by simp [hy₂'])
        simp at this

      obtain ⟨p, hp, p_unique⟩ := aux₅
      have aux₆ : Finset.filter (λ u => v ~ u) (odd_part P) = Finset.image (λ i => v.erase i) p := by
        ext u; simp; constructor
        · intro h
          have ⟨a, _, ha'⟩ := aux₃ h.2 (by simp [fam_from_partition, h.1])
          use a
          simp [ha']
          by_contra contra
          have : p ⊆ u := by
            rw [← ha']
            intro b hb; simp
            constructor
            · by_contra contra'
              exact contra (contra' ▸ hb)
            · exact hp.2 hb
          simp [odd_part] at h
          exact (h.1.2 p hp.1) this
        · intro ⟨a, ha, ha'⟩
          constructor
          · simp [odd_part]
            constructor
            · simp [← ha', Finset.card_erase_eq_ite, (hp.2 ha)]
              have : #v > 0 := by
                apply Finset.card_pos.mpr
                use a; exact hp.2 ha
              apply Nat.even_add_one.mp
              exact (Nat.sub_add_cancel this).symm ▸ hv.1
            · intro q hq
              by_contra contra
              by_cases val_q : q = p
              · subst val_q
                have aux : a ∉ u := by simp [← ha']
                exact aux (contra ha)
              · simp at p_unique
                have : u ⊆ v := by simp [← ha', Finset.erase_eq]
                exact val_q (p_unique q hq (Finset.Subset.trans contra this))
          · simp [← ha', adjacent, hammingDist, symmDiff, Finset.card_eq_one]
            use a
            have : Finset.erase v a \ v = ∅ := by ext x; simp
            simp [this, Finset.eq_singleton_iff_unique_mem, (hp.2 ha)]
            intro x hx hx'
            by_contra contra
            exact (hx' contra) hx

      have aux₇ : Finset.filter (λ u => v ~ u) (even_part P ∪ odd_part P) = Finset.filter (λ u => v ~ u) (odd_part P) := by
        ext x; simp
        exact λ adj h => (aux₁ adj (by simp [fam_from_partition, h]))

      rw [aux₇, aux₆]
      have aux₈ : # p ≤ Nat.sqrt n + 1 := by
        simp [neatPartition] at neat_p
        cases' (neat_p.2 p hp.1) with aux aux <;> simp [aux]
      exact Nat.le_trans (Finset.card_image_le) aux₈
  · simp [odd_part] at hv
    by_cases deg_v : deg(v, fam_from_partition P) = 0
    · simp [fam_from_partition] at deg_v
      simp [deg_v]
    · have aux₁ {u : vertex n} (h : v ~ u) (h' : u ∈ fam_from_partition P) : u ∈ even_part P := by
        by_contra contra
        simp [fam_from_partition, contra, odd_part] at h'
        exact h'.1 (parity_adjacent_odd ((adjacent_comm u v).mpr h) hv.1)

      have aux₂ {u : vertex n} (h : v ~ u) (h' : u ∈ fam_from_partition P) : ∃ a ∈ u, u.erase a = v := by
        have ⟨a, ha⟩ := adj_vertices h
        cases' ha with ha ha
        · use a
        · have := aux₁ h h'
          simp [even_part] at this
          obtain ⟨p, hp⟩ := this.2
          have contra1 := (hv.2 p hp.1)
          have contra2 := (Finset.Subset.trans (ha.2.symm ▸ hp.2) (Finset.erase_subset a v))
          contradiction

      have aux₃ : Finset.filter (λ u => v ~ u) (even_part P ∪ odd_part P) = Finset.filter (λ u => v ~ u) (even_part P) := by
        ext x; simp
        intro adj odd_x
        simp [odd_part] at odd_x
        have := odd_x.1
        have :=  (parity_adjacent_odd ((adjacent_comm v x).mp adj) hv.1)
        contradiction

      have aux₄ {u : vertex n} (h : u ∈ Finset.filter (fun u => v ~ u) (even_part P)) :  ∃ p ∈ P.parts, p ⊆ u := by
        simp [even_part] at h
        exact h.1.2

      have aux₅ : #Finset.filter (λ u => v ~ u) (even_part P) = #Finset.filter (λ p => ∃ a ∈ p, p.erase a ⊆ v) P.parts := by
        let f := λ u : vertex n => λ h₁ : u ∈ Finset.filter (fun u => v ~ u) (even_part P) => (Classical.choose (aux₄ h₁))
        apply Finset.card_congr f
        · intro u hu
          simp
          constructor
          · simp [((Classical.choose_spec (aux₄ hu))).1]
          · have hu' := hu
            simp at hu'
            have ⟨a, ha⟩ := aux₂ hu'.2 (by simp [fam_from_partition, hu'.1])
            use a
            constructor
            · by_contra contra
              have : (Classical.choose (aux₄ hu)) ⊆ v := by
                intro x hx
                simp [← ha.2]
                constructor
                · by_contra contra'
                  exact contra (contra' ▸ hx)
                · exact (Classical.choose_spec (aux₄ hu)).2 hx
              exact (hv.2 (Classical.choose (aux₄ hu)) (Classical.choose_spec (aux₄ hu)).1) this
            · simp [← ha.2]
              intro x hx
              simp
              simp at hx
              exact ⟨hx.1, (Classical.choose_spec (aux₄ hu)).2 hx.2⟩
        · intro x y hx hy eq_f
          have hx' := hx; have hy' := hy
          simp at hx' hy' eq_f
          have ⟨a, ha⟩ := aux₂ hx'.2 (by simp [fam_from_partition, hx'.1])
          have ⟨b, hb⟩ := aux₂ hy'.2 (by simp [fam_from_partition, hy'.1])
          have hb' : b ∈ Classical.choose (aux₄ hx) := by
            rw [eq_f]
            by_contra contra
            have : (Classical.choose (aux₄ hy)) ⊆ v := by
              intro c hc
              simp [← hb.2]
              constructor
              · by_contra contra'
                exact contra (contra' ▸ hc)
              · exact (Classical.choose_spec (aux₄ hy)).2 hc
            exact (hv.2 (Classical.choose (aux₄ hy)) (Classical.choose_spec (aux₄ hy)).1) this
          have b_in_x : b ∈ x := ((Classical.choose_spec (aux₄ hx)).2 hb')
          have : b ∉ x.erase a := by simp [ha.2, ← hb.2]
          simp [b_in_x] at this
          rw [this] at hb
          have : Finset.erase x a = Finset.erase y a := by simp [ha.2, hb.2]
          simp [Finset.ext_iff, ha.1, hb.1] at this
          ext c
          by_cases val_c : c = a
          · simp [val_c, ha.1, hb.1]
          · exact (this c val_c)
        · intro b hb
          simp at hb
          have ⟨a, ha⟩ := hb.2
          use (insert a v)
          have : insert a v ∈ even_part P := by
            simp [even_part]
            constructor
            · have : a ∉ v := by
                by_contra contra
                have : b ⊆ v := by
                  intro x hx
                  by_cases val_x : x = a
                  · rwa [val_x]
                  · exact (ha.2 (by simp [val_x, hx]))
                exact (hv.2 b hb.1) this
              simp [Finset.card_insert_eq_ite, this, Nat.even_add, hv.1]
            · use b
              constructor
              exact hb.1
              intro x hx
              by_cases val_x : x = a <;> simp [val_x]
              exact (ha.2 (by simp [hx, val_x]))
          simp [this]
          have : v ~ insert a v := by
            have : v \ ({a} ∪ v) = ∅ := by
              ext x; simp
              exact λ h => Or.inr h
            simp [adjacent, hammingDist, symmDiff, Finset.insert_eq, this]
            have : ({a} ∪ v) \ v = {a} := by
              ext x; simp
              have : a ∉ v := by
                by_contra contra
                have : b ⊆ v := by
                  intro x hx
                  by_cases val_x : x = a
                  · rwa [val_x]
                  · exact (ha.2 (by simp [val_x, hx]))
                exact (hv.2 b hb.1) this
              by_cases val_x : x = a <;> simp [val_x, this]
            simp [this]
          use this
          by_contra contra
          have disjoint := P.supIndep
          simp [Finset.SupIndep] at disjoint
          have exist : ∃ p ∈ P.parts, p ⊆ insert a v := by
            use b; simp [hb.1]
            intro x hx
            by_cases val_x : x = a <;> simp [val_x]
            · exact ha.2 (by simp [val_x, hx])
          have diff : ¬ Classical.choose exist = b := by
            by_contra contra'
            simp [← contra'] at contra

          have aux : {Classical.choose exist} ⊆ P.parts := by simp [(Classical.choose_spec exist).1]
          have := disjoint (aux) hb.1 (by simp [diff]; exact ne_comm.mpr contra)
          simp [Finset.disjoint_left] at this
          have := this ha.1
          have : Classical.choose exist ⊆ v := by
            intro x hx
            have aux := (Classical.choose_spec exist).2 hx
            have val_x : x ≠ a := by
              by_contra contra
              simp [contra] at hx
              exact this hx
            simp [val_x] at aux
            exact aux
          exact (hv.2 (Classical.choose exist) (Classical.choose_spec exist).1) this

      have aux₆ : # P.parts ≤ Nat.sqrt n + 1 := by
        simp [neatPartition] at neat_p
        cases' neat_p.1 with h h <;> simp [h]

      rw [aux₃, aux₅]
      exact Nat.le_trans (Finset.card_filter_le P.parts _) aux₆
