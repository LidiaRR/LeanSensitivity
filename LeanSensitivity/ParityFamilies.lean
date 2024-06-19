import Mathlib.Data.Fin.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Real.sqrt
import LeanSensitivity.InclusionExclusion
import LeanSensitivity.IndependentSet

open BigOperators

lemma total_set_part {n : ℕ} {hn : n > 0} (P : partition n) {s : vertex_set n} (hs : s ∈ Finset.powerset P.parts \ {∅}) (s_card: (s.sup id).card = n) :
  s = P.parts := by
  have : s ⊆ P.parts := by simp at hs; exact hs.1
  simp [@Finset.Subset.antisymm_iff, this]

  intro a a_part
  have card_lt : ((P.parts.sup id) \ a ).card < n := by
    simp [Finpartition.supParts, Finset.card_univ_diff, tsub_lt_self_iff, hn, Finset.card_pos]
    exact Finpartition.nonempty_of_mem_parts P a_part

  by_contra contra
  have sup_subs : s.sup id ⊆ (P.parts.sup id) \ a := by
    intro x hx
    simp [Finset.mem_sup] at *
    obtain ⟨v, hv⟩ := hx
    constructor
    · use v
      exact ⟨hs.1 hv.1, hv.2⟩
    · by_contra x_in_a
      exact (ne_of_mem_of_not_mem hv.1 contra) (Finpartition.eq_of_mem_parts P (this hv.1) a_part hv.2 x_in_a)

  exact LT.lt.false (s_card ▸ (Nat.lt_of_le_of_lt (Finset.card_le_card sup_subs) card_lt))

lemma parts_not_empty {n : ℕ} {P : partition n} (h : n > 0) : P.parts ≠ ∅ := by
  simp [ne_eq, Finpartition.parts_eq_empty_iff]
  by_contra contra
  let zero : Fin n := {val:=0, isLt:=h}
  exact (Finset.eq_empty_iff_forall_not_mem.mp contra) zero (Finset.mem_univ zero)

-- Family construction and basic properties

def even_part {n : ℕ} (P : partition n) : vertex_set n := Finset.filter (λ v => Even (v.card) ∧ ∃ p ∈ P.parts, p ⊆ v) Finset.univ
def odd_part {n : ℕ} (P : partition n) : vertex_set n := Finset.filter (λ v => Odd (v.card) ∧ ∀ p ∈ P.parts, ¬(p ⊆ v)) Finset.univ
def odd_part' {n : ℕ} (P : partition n) : vertex_set n := Finset.filter (λ v => Odd (v.card) ∧ ∃ p ∈ P.parts, p ⊆ v) Finset.univ
def fam_from_partition {n : ℕ} (P : partition n) := (even_part P) ∪ (odd_part P)

lemma odd_part'_subs {n : ℕ} {P : partition n} : odd_part' P ⊆ Finset.filter (λ v => Odd (v.card)) Finset.univ := by
  intro x hx
  simp [odd_part'] at *
  exact hx.1

lemma odd_eq  {n : ℕ} {P : partition n}: (odd_part P).card = (Finset.filter (λ v : Finset (Fin n) => Odd (v.card)) Finset.univ).card - (odd_part' P).card := by
  have : odd_part P = (Finset.filter (λ v : Finset (Fin n) => Odd (v.card)) Finset.univ) \ (odd_part' P) := by
    ext x
    simp [odd_part, odd_part']
    intro hx
    exact ⟨λ h _ => h, λ h => h hx⟩

  rw [this]
  exact Finset.card_sdiff odd_part'_subs

lemma even_odd_disjoint {n : ℕ} {P : partition n} : Disjoint (even_part P) (odd_part P) := by
  apply Finset.disjoint_iff_ne.mpr
  intro _ h1 _ h2
  apply ne_of_apply_ne (fun a => Even a.card)
  simp [even_part, odd_part] at h1 h2
  exact (Mathlib.Meta.NormNum.ne_of_true_of_false h1.1 h2.1)

def parity_set {n : ℕ} (P : partition n) (parity : Bool) : vertex_set n := if parity then even_part P else odd_part' P
def par_fun (par : Bool) : ℕ → Prop := if par then Even else Odd

noncomputable instance {par : Bool} {k : ℕ} : Decidable (par_fun par k) := Classical.dec (par_fun par k)

lemma parity_set_eq {n : ℕ} {P : partition n} (par : Bool) : parity_set P par =
  (P.parts).sup (λ i => Finset.filter (λ v => (par_fun par v.card) ∧ i ⊆ v) Finset.univ) := by
  ext x
  simp [Finset.mem_sup, parity_set, par_fun, even_part, odd_part']
  by_cases val_par : par <;> simp [val_par]
  · constructor
    · intro ⟨h₁, ⟨p, hp, h₂⟩⟩
      use p
    · intro ⟨p, hp, h₁, h₂⟩
      exact ⟨h₁, by use p⟩
  · constructor
    · intro ⟨h₁, ⟨p, hp, h₂⟩⟩
      use p
    · intro ⟨p, hp, h₁, h₂⟩
      exact ⟨h₁, by use p⟩

lemma add_par_fun : par_fun par (a + b) ↔ (par_fun par a ↔ Even b) := by
  simp [par_fun]
  by_cases val_par : par
  · simp [val_par, Nat.even_add]
  · simp only [val_par, ite_false, Nat.odd_add]

-- Cardinality result - Auxiliar lemmas

def ε (n : ℕ) := n % 2
def ε' (n : ℕ) (parity : Bool) := if parity then 1 - (ε n) else ε n

lemma h₁ {n : ℕ} {x : vertex_set n} {h : (x.sup id).card < n} {par : Bool} : (Finset.filter (λ v => par_fun par (v ∪ Finset.sup x id).card) (Finset.powerset (Finset.univ \ Finset.sup x id))).card =
    (Finset.filter (λ v => par_fun par (v.card + (Finset.sup x id).card)) (Finset.powerset (@Finset.univ (Fin (n - (Finset.sup x id).card)) _))).card := by
    let compl_x := Finset.univ \ (x.sup id)

    have length_eq : List.length (Finset.sort (fun j k => j ≤ k) compl_x) = n - (x.sup id).card := by
      simp [Finset.length_sort, Finset.card_univ_diff]

    have aux₁ (i : Fin _) (h : i ∈ compl_x) : List.indexOf i (Finset.sort (fun x x_1 => x ≤ x_1) compl_x) < n - (Finset.sup x id).card := by
      simp
      have : i ∈ (Finset.sort (fun x x_1 => x ≤ x_1) compl_x) := by simp only [Finset.mem_sort, h]
      exact length_eq ▸ (List.indexOf_lt_length.mpr this)

    let g := λ i : Fin n => (dite (i ∈ compl_x) (λ h => {val:=(compl_x.sort (· ≤ ·)).indexOf i, isLt:= aux₁ i h}) (λ _ => {val:=0, isLt:=by simp [h]}) : Fin (n - (Finset.sup x id).card))
    let f := (λ s : vertex n => (λ _ : (s ∈ Finset.filter (λ v => par_fun par (v ∪ Finset.sup x id).card) (Finset.powerset compl_x)) =>
      (s.image g)))

    let g' := λ i : Fin (n - (x.sup id).card) => ((compl_x.sort (λ j k => j ≤ k)).get {val := i, isLt := by rw [length_eq]; exact Fin.prop i} : Fin n)
    let f' := (λ s : vertex (n - (x.sup id).card) => (s.image g' : Finset (Fin n)))

    have aux₂ (a : vertex n) (ha : a ⊆ compl_x): (a.image g).card = a.card := by
      apply Finset.card_image_iff.mpr
      simp [Set.InjOn]
      intro _ hx₁ _ hx₂
      have h₁' := ha hx₁
      have h₂' := ha hx₂
      simp at h₁' h₂'
      simp [h₁', h₂']
      intro h
      rw [List.indexOf_inj (by simp [Finset.mem_sort, h₁']) (by simp [Finset.mem_sort, h₂'])] at h
      exact h

    have aux₃ {a b : vertex n} {ha : _} {hb : _} : f a ha = f b hb → a = b := by
      intro eq
      ext x
      have impl (c d : vertex n) (hc : _) (hd : _) (y : Fin n) (eq' : f c hc = f d hd) (h : y ∈ c)  : y ∈ d := by
        rw [Finset.Subset.antisymm_iff] at eq'
        have : (g y) ∈ (f c hc) := by simp; use y
        have := eq'.1 this
        simp at this
        obtain ⟨y', hy1', hy2'⟩ := this
        have hy : y ∈ compl_x := by
          simp at hc
          have := hc.1 h
          simp; simp at this
          exact this
        have hy' : y' ∈ compl_x := by
          simp at hd
          have := hd.1 hy1'
          simp; simp at this
          exact this
        simp at hy hy'
        simp [hy, hy'] at hy2'
        rw [List.indexOf_inj (by simp [Finset.mem_sort, hy']) (by simp [Finset.mem_sort, hy])] at hy2'
        exact (hy2' ▸ hy1')

      exact ⟨λ h => impl a b ha hb x eq h, λ h => impl b a hb ha x eq.symm h⟩

    have aux₄ {b : vertex (n - (x.sup id).card)} (hb : b ∈ Finset.filter (fun v => par_fun par (v.card + (Finset.sup x id).card)) (Finset.powerset Finset.univ)) :
      f' b ∈ Finset.filter (λ v => par_fun par (v ∪ Finset.sup x id).card) (Finset.powerset compl_x) := by
      simp
      simp at hb
      constructor
      · intro y hy
        simp
        simp at hy
        obtain ⟨z, _, hz2⟩ := hy
        have : y ∈ compl_x.sort (· ≤ ·) := by
          rw [List.mem_iff_get]
          use {val:=z, isLt:=by rw [length_eq]; simp}
        simp at this
        exact this
      · have : (b.image g' ∪ (x.sup id)).card = (b.image g').card + (x.sup id).card := by
          apply Finset.card_disjoint_union
          rw [Finset.disjoint_left]
          intro y hy
          simp at hy
          obtain ⟨z, _, hz2⟩ := hy
          have : y ∈ compl_x.sort (· ≤ ·) := by
            rw [List.mem_iff_get]
            use {val:=z, isLt:=by rw [length_eq]; simp}

          simp at this
          exact this
        rw [this]
        have : (b.image g').card = b.card := by
          rw [Finset.card_image_iff]
          intro y _ y' _ eq
          simp [ List.Nodup.get_inj_iff ] at eq
          exact Fin.ext_iff.mpr eq
        exact (this ▸ hb)

    have aux₅ {b : vertex (n - (x.sup id).card)} (hb : b ∈ Finset.filter (fun v => par_fun par (v.card + (Finset.sup x id).card)) (Finset.powerset Finset.univ)) :
      f (f' b) (aux₄ hb) = b := by
      ext y
      simp
      have {k : _} : List.get (compl_x.sort (· ≤ ·)) k ∈ (compl_x.sort (· ≤ ·)) := List.get?_mem (List.get_eq_iff.mp rfl)
      constructor
      · intro h
        obtain ⟨y', hy1', hy2'⟩ := h
        simp [Finset.mem_sort] at this
        simp [this] at hy2'
        simp [hy2'.symm, List.get_indexOf, hy1']

      · intro h
        use y
        simp [Finset.mem_sort] at this
        simp [h, this, List.get_indexOf]


    apply Finset.card_congr f _ (λ _ _ ha hb eq => @aux₃ _ _ ha hb eq) (λ b hb => ⟨f' b, (aux₄ hb),  aux₅ hb⟩)
    · intro a ha
      simp [add_par_fun]
      simp at ha
      have := aux₂ a ha.1
      simp at this
      rw [this]
      rw [(Finset.card_disjoint_union (le_compl_iff_disjoint_right.mp ha.1)), add_par_fun] at ha
      exact ha.2

lemma aux' {n : ℕ} {s : vertex_set n} {P : partition n} (hs : s ∈ Finset.powerset P.parts \ {∅}) :
  Finset.inf s (λ i => Finset.filter (λ v => (par_fun par v.card) ∧ i ⊆ v) Finset.univ) =
  Finset.filter (λ v => (par_fun par v.card) ∧ (Finset.sup s id) ⊆ v) Finset.univ := by
  ext a
  simp [Finset.mem_inf]
  constructor
  · intro h
    have aux : ∃ i, i ∈ s := by
      rw [← nonempty_subtype, Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty]
      simp at hs
      exact hs.2

    obtain ⟨i, hi⟩ := aux
    constructor
    exact (h i hi).1
    intro x hx
    simp [Finset.mem_sup] at hx
    obtain ⟨v, hv⟩ := hx
    exact (h v hv.1).2 hv.2

  · intro h i hi
    constructor
    exact h.1
    have aux : i ⊆ s.sup id := by
      intro x hx
      simp [Finset.mem_sup]
      use i
    exact Finset.Subset.trans aux h.2


--- Need to put in a separate file with the even/odd partition from the other example
lemma par_fun_eq (par : Bool) (n : ℕ) : Finset.filter (λ v => par_fun par v.card) (@Finset.univ (vertex n) _) = even_construction n ∨
  Finset.filter (λ v => par_fun par v.card) (@Finset.univ (vertex n) _) = odd_construction n := by
  simp [even_construction, odd_construction, par_fun]
  by_cases val_par : par <;> simp [val_par]

lemma card_par {par : Bool} {n : ℕ} {h : n > 0}: (Finset.filter (λ v => par_fun par v.card) (@Finset.univ (vertex (n)) _)).card = 2^(n-1) := by
  have := @par_fun_eq par n
  cases' this with h' h'
  · simp [h']
    have := even_construction_card (n-1)
    rw [Nat.sub_add_cancel h] at this
    exact this
  · simp [h']
    rw [← @eq_card_even_odd _ h]
    have := even_construction_card (n-1)
    rw [Nat.sub_add_cancel h] at this
    exact this

---

lemma card_sets {n : ℕ} {hn : n > 0} {P : partition n} (par : Bool) : (parity_set P par).card =
  ∑ x in (Finset.powerset P.parts \ {∅}), (-1 : ℤ)^(x.card + 1) *
  if (x.sup id).card = n then (ε' n par) else 2 ^ (n - (x.sup id).card - 1) := by
  rw [parity_set_eq, inclusion_exclusion']

  apply Finset.sum_congr rfl
  intro s hs
  rw [(Int.mul_eq_mul_left_iff (Int.neg_one_pow_ne_zero))]

  by_cases card_s : (s.sup id).card = n
  · ----- s = P.parts
    simp [card_s, ε', (@total_set_part n hn P s hs card_s)]
    have : P.parts ∈ Finset.powerset P.parts \ {∅} := by simp [Finset.mem_powerset, (parts_not_empty hn)]
    rw [aux' this, P.supParts]
    have {v : Finset (Fin n)}: Finset.univ ⊆ v ↔ Finset.univ = v := ⟨λ h => by simp [Finset.Subset.antisymm_iff, h], λ h => by simp [h]⟩
    simp [this]

    have : Finset.filter (λ v => (par_fun par v.card) ∧ Finset.univ = v) Finset.univ =
      if par then (if Even (@Finset.univ (Fin n) _).card then {Finset.univ} else ∅ : Finset (Finset (Fin n)))
        else (if ¬ Even (@Finset.univ (Fin n) _).card then {Finset.univ} else ∅ : Finset (Finset (Fin n))) := by
      ext x
      simp [par_fun]
      by_cases val_par : par
      · simp [val_par]
        constructor
        · intro h
          have : x.card = n := by simp [h.2.symm]
          have : Even n := by simp [this.symm, h.1]
          simp [this, h.2]
        · intro h
          by_cases even_n : Even n
          · simp [even_n] at h
            have : x.card = n := by simp [h, even_n]
            exact (this.symm ▸ ⟨even_n, h.symm⟩)
          · simp [even_n] at h
      · simp [val_par]
        constructor
        · intro h
          have : x.card = n := by simp [h.2.symm]
          rw [this] at h
          simp [h.1, h.2]
        · intro h
          by_cases even_n : Even n
          · simp [even_n] at h
          · simp [even_n] at h
            have : x.card = n := by simp [h]
            exact (this.symm ▸ ⟨even_n, h.symm⟩)
    rw [this]

    by_cases val_par : par
    · simp [val_par, ε]
      by_cases par_n : Even n
      · simp [par_n, Nat.even_iff.mp par_n]
      · simp [par_n, Nat.not_even_iff.mp par_n]

    · simp [val_par, ε]
      by_cases par_n : Even n
      · norm_cast
        simp [par_n, Nat.even_iff.mp par_n]
      · norm_cast
        simp [par_n, Nat.not_even_iff.mp par_n]

  · ---- s ⊂ P.parts
    simp [card_s, aux' hs]
    have : (Finset.filter (λ v => (par_fun par v.card) ∧ Finset.sup s id ⊆ v) Finset.univ).card =
      (Finset.filter (λ v => par_fun par (v ∪ Finset.sup s id).card) (Finset.powerset ((@Finset.univ (Fin n) _) \ (Finset.sup s id)))).card := by
      apply Finset.card_congr (λ v : Finset (Fin n) => λ _ => v \ (Finset.sup s id))
      · intro a ha
        simp
        constructor
        · intro b hb
          simp at *
          exact hb.2
        · simp at ha
          rw [(Finset.union_eq_left.mpr ha.2)]
          exact ha.1
      · intro a b ha hb h
        simp at ha hb
        ext y
        by_cases val_y : y ∈ s.sup id
        · exact iff_of_true (ha.2 val_y) (hb.2 val_y)
        · have ha' : y ∈ a ↔ y ∈ a \ s.sup id := by simp [val_y]
          have hb' : y ∈ b ↔ y ∈ b \ s.sup id := by simp [val_y]
          rw [ha', hb']
          simp [h]
      · intro b hb
        let a := b ∪ s.sup id
        use a
        simp at *
        constructor
        · exact ⟨hb.2, Finset.subset_union_right b (s.sup id)⟩
        · ext y
          simp
          constructor
          · intro ⟨h, h'⟩
            cases' h with h h
            exact h
            exact (h' h).elim
          · exact (λ h => ⟨Or.inl h, Finset.mem_compl.mp (hb.1 h)⟩)

    rw [this, @h₁ _ _ (Nat.lt_iff_le_and_ne.mpr ⟨card_finset_fin_le (Finset.sup s id), card_s⟩)]

    let par' := if Even (s.sup id).card then par else !par
    rw [Finset.powerset_univ]
    have {v : Finset (Fin (n - (s.sup id).card))} : par_fun par (v.card + (s.sup id).card) =
      par_fun par' v.card := by
      rw [add_par_fun]
      simp
      by_cases val_sup : Even (s.sup id).card
      · simp [val_sup]
      · simp [val_sup, par_fun]
        by_cases val_par : par
        simp [val_par]
        simp [val_par]

    simp only [this]
    have := @card_par par' (n - (s.sup id).card) (by simp [(Nat.lt_of_le_of_ne (card_finset_fin_le (s.sup id)) card_s)])
    simp at this
    simp [this]
