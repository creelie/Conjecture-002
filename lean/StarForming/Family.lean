import StarForming.Basic

/-!
# A bipartite family with `β_k < SF_k` for every `k ≥ 3`

For `m ≥ 1` the graph `G m` has `3m + 6` vertices:

* hubs `h_1, …, h_m`;
* two blocks `X₁ = {x₁(1), …, x₁(m)}` and `X₂ = {x₂(1), …, x₂(m)}`;
* six further vertices `x₀, p, c₁, c₂, q₁, q₂` (indices `0, …, 5` of `Fin 6`).

Every hub is adjacent to `x₀` and to every vertex of `X₁ ∪ X₂`; `x₀p`, `c₁q₁`, `c₂q₂` are edges,
`c₁` is adjacent to all of `X₁` and `c₂` to all of `X₂`.  With `k = m + 1` the set
`S = V ∖ {p, q₁, q₂}` is a minimal `k`-star-forming set of size `3m + 3 = 3k`, while every
`k`-independent set has at most `2m + 4 = 2k + 2` vertices.
-/

open Finset

namespace StarForming

/-- The vertex type of `G m`. -/
abbrev W (m : ℕ) := Fin m ⊕ Fin m ⊕ Fin m ⊕ Fin 6

variable {m : ℕ}

/-- The hubs. -/
def hub (i : Fin m) : W m := Sum.inl i
/-- The block `X₁`. -/
def x1 (j : Fin m) : W m := Sum.inr (Sum.inl j)
/-- The block `X₂`. -/
def x2 (j : Fin m) : W m := Sum.inr (Sum.inr (Sum.inl j))
/-- The six special vertices `x₀ = sp 0`, `p = sp 1`, `c₁ = sp 2`, `c₂ = sp 3`, `q₁ = sp 4`,
`q₂ = sp 5`. -/
def sp (s : Fin 6) : W m := Sum.inr (Sum.inr (Sum.inr s))

/-- One direction of each edge. -/
def E : W m → W m → Bool
  | Sum.inl _, Sum.inr (Sum.inl _) => true
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inl _)) => true
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inr s)) => s == 0
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr (Sum.inr s)) => s == 2
  | Sum.inr (Sum.inr (Sum.inl _)), Sum.inr (Sum.inr (Sum.inr s)) => s == 3
  | Sum.inr (Sum.inr (Sum.inr s)), Sum.inr (Sum.inr (Sum.inr t)) =>
      (s == 0 && t == 1) || (s == 2 && t == 4) || (s == 3 && t == 5)
  | _, _ => false

/-- The graph `G m`. -/
def G (m : ℕ) : SimpleGraph (W m) where
  Adj u v := E u v = true ∨ E v u = true
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => by
    rcases u with i | j | j | s
    · simp [E] at h
    · simp [E] at h
    · simp [E] at h
    · fin_cases s <;> simp [E] at h⟩

instance : DecidableRel (G m).Adj := fun u v =>
  inferInstanceAs (Decidable (E u v = true ∨ E v u = true))

section adjacency

variable (i i' : Fin m) (j j' : Fin m) (s : Fin 6)

@[simp] lemma adj_hub_hub : ¬ (G m).Adj (hub i) (hub i') := by simp [G, E, hub]
@[simp] lemma adj_hub_x1 : (G m).Adj (hub i) (x1 j) := by simp [G, E, hub, x1]
@[simp] lemma adj_hub_x2 : (G m).Adj (hub i) (x2 j) := by simp [G, E, hub, x2]
@[simp] lemma adj_hub_sp : (G m).Adj (hub i) (sp s) ↔ s = 0 := by simp [G, E, hub, sp]
@[simp] lemma adj_x1_hub : (G m).Adj (x1 j) (hub i) := by simp [G, E, hub, x1]
@[simp] lemma adj_x1_x1 : ¬ (G m).Adj (x1 j) (x1 j') := by simp [G, E, x1]
@[simp] lemma adj_x1_x2 : ¬ (G m).Adj (x1 j) (x2 j') := by simp [G, E, x1, x2]
@[simp] lemma adj_x1_sp : (G m).Adj (x1 j) (sp s) ↔ s = 2 := by simp [G, E, x1, sp]
@[simp] lemma adj_x2_hub : (G m).Adj (x2 j) (hub i) := by simp [G, E, hub, x2]
@[simp] lemma adj_x2_x1 : ¬ (G m).Adj (x2 j) (x1 j') := by simp [G, E, x1, x2]
@[simp] lemma adj_x2_x2 : ¬ (G m).Adj (x2 j) (x2 j') := by simp [G, E, x2]
@[simp] lemma adj_x2_sp : (G m).Adj (x2 j) (sp s) ↔ s = 3 := by simp [G, E, x2, sp]
@[simp] lemma adj_sp_hub : (G m).Adj (sp s) (hub i) ↔ s = 0 := by
  simp [G, E, hub, sp]
@[simp] lemma adj_sp_x1 : (G m).Adj (sp s) (x1 j) ↔ s = 2 := by simp [G, E, x1, sp]
@[simp] lemma adj_sp_x2 : (G m).Adj (sp s) (x2 j) ↔ s = 3 := by simp [G, E, x2, sp]

lemma adj_sp_sp (s t : Fin 6) : (G m).Adj (sp s) (sp t) ↔
    (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) ∨ (s = 2 ∧ t = 4) ∨ (s = 4 ∧ t = 2) ∨
      (s = 3 ∧ t = 5) ∨ (s = 5 ∧ t = 3) := by
  fin_cases s <;> fin_cases t <;> simp [G, E, sp]

end adjacency

/-- `G m` is bipartite. -/
def side : W m → Bool
  | Sum.inl _ => false
  | Sum.inr (Sum.inl _) => true
  | Sum.inr (Sum.inr (Sum.inl _)) => true
  | Sum.inr (Sum.inr (Sum.inr s)) => s == 0 || s == 4 || s == 5

theorem side_ne_of_adj {u v : W m} (h : (G m).Adj u v) : side u ≠ side v := by
  rcases u with i | j | j | s <;> rcases v with i' | j' | j' | t <;> (try fin_cases s) <;>
    (try fin_cases t) <;> simp [G, E, side] at h ⊢

theorem colorable_two : (G m).Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (fun v => (if side v then 1 else 0 : Fin 2)) (fun {u v} h => by
    have := side_ne_of_adj h
    cases hu : side u <;> cases hv : side v <;> simp_all)⟩

lemma sp_injective : Function.Injective (sp : Fin 6 → W m) := by
  intro s t h; simpa [sp] using h

@[simp] lemma sp_inj {s t : Fin 6} : (sp s : W m) = sp t ↔ s = t := sp_injective.eq_iff
@[simp] lemma hub_ne_sp (i : Fin m) (s : Fin 6) : hub i ≠ sp s := by simp [hub, sp]
@[simp] lemma x1_ne_sp (j : Fin m) (s : Fin 6) : x1 j ≠ sp s := by simp [x1, sp]
@[simp] lemma x2_ne_sp (j : Fin m) (s : Fin 6) : x2 j ≠ sp s := by simp [x2, sp]
@[simp] lemma sp_ne_hub (i : Fin m) (s : Fin 6) : sp s ≠ hub i := (hub_ne_sp i s).symm
@[simp] lemma sp_ne_x1 (j : Fin m) (s : Fin 6) : sp s ≠ x1 j := (x1_ne_sp j s).symm
@[simp] lemma sp_ne_x2 (j : Fin m) (s : Fin 6) : sp s ≠ x2 j := (x2_ne_sp j s).symm
@[simp] lemma hub_inj {i i' : Fin m} : hub i = hub i' ↔ i = i' := by simp [hub]
@[simp] lemma x1_inj {j j' : Fin m} : x1 j = x1 j' ↔ j = j' := by simp [x1]
@[simp] lemma x2_inj {j j' : Fin m} : x2 j = x2 j' ↔ j = j' := by simp [x2]
@[simp] lemma hub_ne_x1 (i j : Fin m) : hub i ≠ x1 j := by simp [hub, x1]
@[simp] lemma hub_ne_x2 (i j : Fin m) : hub i ≠ x2 j := by simp [hub, x2]
@[simp] lemma x1_ne_x2 (i j : Fin m) : x1 i ≠ x2 j := by simp [x1, x2]
@[simp] lemma x1_ne_hub (i j : Fin m) : x1 j ≠ hub i := (hub_ne_x1 i j).symm
@[simp] lemma x2_ne_hub (i j : Fin m) : x2 j ≠ hub i := (hub_ne_x2 i j).symm
@[simp] lemma x2_ne_x1 (i j : Fin m) : x2 j ≠ x1 i := (x1_ne_x2 i j).symm

lemma W_cases (v : W m) :
    (∃ i, v = hub i) ∨ (∃ j, v = x1 j) ∨ (∃ j, v = x2 j) ∨ ∃ s, v = sp s := by
  rcases v with i | j | j | s <;> simp [hub, x1, x2, sp]

/-! ## Counting inside a set -/

section counting

variable (I : Finset (W m))

/-- Number of hubs in `I`. -/
def nH : ℕ := #(univ.filter fun i : Fin m => hub i ∈ I)
/-- Number of vertices of `X₁` in `I`. -/
def nA : ℕ := #(univ.filter fun j : Fin m => x1 j ∈ I)
/-- Number of vertices of `X₂` in `I`. -/
def nB : ℕ := #(univ.filter fun j : Fin m => x2 j ∈ I)
/-- Indicator of the special vertex `sp s` in `I`. -/
def ind (s : Fin 6) : ℕ := if sp s ∈ I then 1 else 0

theorem card_filter_split (P : W m → Prop) [DecidablePred P] :
    #(I.filter P) = #(univ.filter fun i => hub i ∈ I ∧ P (hub i))
      + #(univ.filter fun j => x1 j ∈ I ∧ P (x1 j))
      + #(univ.filter fun j => x2 j ∈ I ∧ P (x2 j))
      + ∑ s : Fin 6, if sp s ∈ I ∧ P (sp s) then 1 else 0 := by
  have h : I.filter P = univ.filter (fun v => v ∈ I ∧ P v) := by ext v; simp
  rw [h, card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type,
    card_filter, card_filter, card_filter]
  simp only [add_assoc]
  rfl

theorem card_eq : #I = nH I + nA I + nB I +
    (ind I 0 + ind I 1 + ind I 2 + ind I 3 + ind I 4 + ind I 5) := by
  have := card_filter_split I (fun _ => True)
  rw [filter_true_of_mem (fun _ _ => trivial)] at this
  rw [this, Fin.sum_univ_six]
  simp [nH, nA, nB, ind]

theorem deg_hub (i : Fin m) : #(I.filter ((G m).Adj (hub i))) = nA I + nB I + ind I 0 := by
  rw [card_filter_split, Fin.sum_univ_six]
  simp [nA, nB, ind]

theorem deg_x1 (j : Fin m) : #(I.filter ((G m).Adj (x1 j))) = nH I + ind I 2 := by
  rw [card_filter_split, Fin.sum_univ_six]
  simp [nH, ind]

theorem deg_x2 (j : Fin m) : #(I.filter ((G m).Adj (x2 j))) = nH I + ind I 3 := by
  rw [card_filter_split, Fin.sum_univ_six]
  simp [nH, ind]

theorem deg_sp0 : #(I.filter ((G m).Adj (sp 0))) = nH I + ind I 1 := by
  rw [card_filter_split, Fin.sum_univ_six]
  simp [nH, ind, adj_sp_sp]

theorem deg_sp1 : #(I.filter ((G m).Adj (sp 1))) = ind I 0 := by
  rw [card_filter_split, Fin.sum_univ_six]
  simp [ind, adj_sp_sp]

theorem deg_sp2 : #(I.filter ((G m).Adj (sp 2))) = nA I + ind I 4 := by
  rw [card_filter_split, Fin.sum_univ_six]
  simp [nA, ind, adj_sp_sp]

theorem deg_sp3 : #(I.filter ((G m).Adj (sp 3))) = nB I + ind I 5 := by
  rw [card_filter_split, Fin.sum_univ_six]
  simp [nB, ind, adj_sp_sp]

theorem deg_sp4 : #(I.filter ((G m).Adj (sp 4))) = ind I 2 := by
  rw [card_filter_split, Fin.sum_univ_six]
  simp [ind, adj_sp_sp]

theorem deg_sp5 : #(I.filter ((G m).Adj (sp 5))) = ind I 3 := by
  rw [card_filter_split, Fin.sum_univ_six]
  simp [ind, adj_sp_sp]

theorem nH_le : nH I ≤ m := (card_filter_le _ _).trans (by simp)
theorem nA_le : nA I ≤ m := (card_filter_le _ _).trans (by simp)
theorem nB_le : nB I ≤ m := (card_filter_le _ _).trans (by simp)
theorem ind_le (s : Fin 6) : ind I s ≤ 1 := by unfold ind; split_ifs <;> simp

theorem ind_eq_one {s : Fin 6} : ind I s = 1 ↔ sp s ∈ I := by
  unfold ind; split_ifs with h <;> simp [h]

theorem exists_hub (h : 1 ≤ nH I) : ∃ i, hub i ∈ I := by
  obtain ⟨i, hi⟩ := card_pos.1 h
  exact ⟨i, (mem_filter.1 hi).2⟩

theorem exists_x1 (h : 1 ≤ nA I) : ∃ j, x1 j ∈ I := by
  obtain ⟨j, hj⟩ := card_pos.1 h
  exact ⟨j, (mem_filter.1 hj).2⟩

theorem exists_x2 (h : 1 ≤ nB I) : ∃ j, x2 j ∈ I := by
  obtain ⟨j, hj⟩ := card_pos.1 h
  exact ⟨j, (mem_filter.1 hj).2⟩

end counting

/-! ## The upper bound `β_{m+1}(G m) ≤ 2m + 4` -/

theorem kIndep_card_le (I : Finset (W m)) (hI : KIndep (G m) (m + 1) I) :
    #I ≤ 2 * m + 4 := by
  have hH := nH_le I
  have hA := nA_le I
  have hB := nB_le I
  have e0 := ind_le I 0
  have e1 := ind_le I 1
  have e2 := ind_le I 2
  have e3 := ind_le I 3
  have e4 := ind_le I 4
  have e5 := ind_le I 5
  -- a hub in `I` sees `x₀` and all of `I ∩ (X₁ ∪ X₂)`
  have cH : 1 ≤ nH I → nA I + nB I + ind I 0 ≤ m := by
    intro h
    obtain ⟨i, hi⟩ := exists_hub I h
    have := hI _ hi
    rw [deg_hub] at this
    omega
  -- `x₀` sees every hub and `p`
  have c0 : ind I 0 = 1 → nH I + ind I 1 ≤ m := by
    intro h
    have := hI _ ((ind_eq_one I).1 h)
    rw [deg_sp0] at this
    omega
  -- a vertex of `X₁` sees every hub and `c₁`
  have cA : 1 ≤ nA I → nH I + ind I 2 ≤ m := by
    intro h
    obtain ⟨j, hj⟩ := exists_x1 I h
    have := hI _ hj
    rw [deg_x1] at this
    omega
  have cB : 1 ≤ nB I → nH I + ind I 3 ≤ m := by
    intro h
    obtain ⟨j, hj⟩ := exists_x2 I h
    have := hI _ hj
    rw [deg_x2] at this
    omega
  -- `c₁` sees `X₁` and `q₁`
  have c2 : ind I 2 = 1 → nA I + ind I 4 ≤ m := by
    intro h
    have := hI _ ((ind_eq_one I).1 h)
    rw [deg_sp2] at this
    omega
  have c3 : ind I 3 = 1 → nB I + ind I 5 ≤ m := by
    intro h
    have := hI _ ((ind_eq_one I).1 h)
    rw [deg_sp3] at this
    omega
  rw [card_eq]
  omega

/-- A `k`-independent set of size `2m + 4`: `X₁ ∪ X₂ ∪ {x₀, p, q₁, q₂}`. -/
def I0 (m : ℕ) : Finset (W m) :=
  univ.filter fun v => (∃ j, v = x1 j) ∨ (∃ j, v = x2 j) ∨ v = sp 0 ∨ v = sp 1 ∨ v = sp 4 ∨
    v = sp 5

@[simp] lemma hub_mem_I0 (i : Fin m) : hub i ∉ I0 m := by
  simp only [I0, mem_filter, mem_univ, true_and]; simp
@[simp] lemma x1_mem_I0 (j : Fin m) : x1 j ∈ I0 m := by
  simp only [I0, mem_filter, mem_univ, true_and]; simp
@[simp] lemma x2_mem_I0 (j : Fin m) : x2 j ∈ I0 m := by
  simp only [I0, mem_filter, mem_univ, true_and]; simp
@[simp] lemma sp_mem_I0 (s : Fin 6) : sp s ∈ I0 m ↔ s = 0 ∨ s = 1 ∨ s = 4 ∨ s = 5 := by
  simp only [I0, mem_filter, mem_univ, true_and]; simp

theorem kIndep_I0 (hm : 1 ≤ m) : KIndep (G m) (m + 1) (I0 m) := by
  intro v hv
  obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨s, rfl⟩ := W_cases v
  · exact absurd hv (hub_mem_I0 i)
  · rw [deg_x1]; simp [nH, ind]
  · rw [deg_x2]; simp [nH, ind]
  · rw [sp_mem_I0] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [deg_sp0]; simp [nH, ind]; omega
    · rw [deg_sp1]; simp [ind]; omega
    · rw [deg_sp4]; simp [ind]
    · rw [deg_sp5]; simp [ind]

theorem card_I0 : #(I0 m) = 2 * m + 4 := by
  rw [card_eq]
  simp [nH, nA, nB, ind]
  omega

/-! ## The minimal star-forming set `S = V ∖ {p, q₁, q₂}` -/

/-- The set `S` of size `3m + 3`. -/
def S0 (m : ℕ) : Finset (W m) := univ.filter fun v => v ≠ sp 1 ∧ v ≠ sp 4 ∧ v ≠ sp 5

@[simp] lemma hub_mem_S0 (i : Fin m) : hub i ∈ S0 m := by
  simp only [S0, mem_filter, mem_univ, true_and]; simp
@[simp] lemma x1_mem_S0 (j : Fin m) : x1 j ∈ S0 m := by
  simp only [S0, mem_filter, mem_univ, true_and]; simp
@[simp] lemma x2_mem_S0 (j : Fin m) : x2 j ∈ S0 m := by
  simp only [S0, mem_filter, mem_univ, true_and]; simp
@[simp] lemma sp_mem_S0 (s : Fin 6) : sp s ∈ S0 m ↔ s = 0 ∨ s = 2 ∨ s = 3 := by
  simp only [S0, mem_filter, mem_univ, true_and]
  fin_cases s <;> simp

theorem card_S0 : #(S0 m) = 3 * m + 3 := by
  rw [card_eq]
  simp [nH, nA, nB, ind]
  omega

/-- The only neighbour of `p`, `q₁`, `q₂` is `x₀`, `c₁`, `c₂` respectively. -/
lemma eq_of_adj_sp1 {c : W m} (h : (G m).Adj c (sp 1)) : c = sp 0 := by
  obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨s, rfl⟩ := W_cases c
  · simp at h
  · simp at h
  · simp at h
  · rw [adj_sp_sp] at h
    have : s = 0 := by omega
    simp [this]

lemma eq_of_adj_sp4 {c : W m} (h : (G m).Adj c (sp 4)) : c = sp 2 := by
  obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨s, rfl⟩ := W_cases c
  · simp at h
  · simp at h
  · simp at h
  · rw [adj_sp_sp] at h
    have : s = 2 := by omega
    simp [this]

lemma eq_of_adj_sp5 {c : W m} (h : (G m).Adj c (sp 5)) : c = sp 3 := by
  obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨s, rfl⟩ := W_cases c
  · simp at h
  · simp at h
  · simp at h
  · rw [adj_sp_sp] at h
    have : s = 3 := by omega
    simp [this]

theorem isStarForming_S0 : IsStarForming (G m) (m + 1) (S0 m) := by
  intro v hv
  obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨s, rfl⟩ := W_cases v
  · exact absurd (hub_mem_S0 i) hv
  · exact absurd (x1_mem_S0 j) hv
  · exact absurd (x2_mem_S0 j) hv
  · rw [sp_mem_S0] at hv
    have hs : s = 1 ∨ s = 4 ∨ s = 5 := by omega
    rcases hs with rfl | rfl | rfl
    · -- `p` is a leaf of the star at `x₀` whose other leaves are the hubs
      refine ⟨sp 0, by simp, _, subset_refl _, ?_, Or.inr ?_⟩
      · rw [deg_sp0]; simp [nH, ind]
      · simp [adj_sp_sp]
    · refine ⟨sp 2, by simp, _, subset_refl _, ?_, Or.inr ?_⟩
      · rw [deg_sp2]; simp [nA, ind]
      · simp [adj_sp_sp]
    · refine ⟨sp 3, by simp, _, subset_refl _, ?_, Or.inr ?_⟩
      · rw [deg_sp3]; simp [nB, ind]
      · simp [adj_sp_sp]

theorem not_isStarForming_erase (hm : 1 ≤ m) (s : W m) (hs : s ∈ S0 m) :
    ¬ IsStarForming (G m) (m + 1) ((S0 m).erase s) := by
  intro hsf
  obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨t, rfl⟩ := W_cases s
  · -- deleting a hub: `p` loses its star
    have hw : sp 1 ∉ (S0 m).erase (hub i) := by simp
    obtain ⟨c, hc⟩ := hsf _ hw
    obtain ⟨hcT, hcv, hk⟩ := hc.card_le
    rcases hcv with rfl | hadj
    · rw [deg_sp1] at hk; simp [ind] at hk; omega
    · obtain rfl := eq_of_adj_sp1 hadj
      rw [deg_sp0] at hk
      have : nH (insert (sp 1) ((S0 m).erase (hub i))) = m - 1 := by
        simp only [nH, mem_insert, mem_erase, ne_eq, hub_inj, hub_ne_sp, false_or,
          hub_mem_S0, and_true]
        rw [filter_ne' univ i, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
      rw [this] at hk; simp [ind] at hk; omega
  · -- deleting a vertex of `X₁`: `q₁` loses its star
    have hw : sp 4 ∉ (S0 m).erase (x1 j) := by simp
    obtain ⟨c, hc⟩ := hsf _ hw
    obtain ⟨hcT, hcv, hk⟩ := hc.card_le
    rcases hcv with rfl | hadj
    · rw [deg_sp4] at hk; simp [ind] at hk; omega
    · obtain rfl := eq_of_adj_sp4 hadj
      rw [deg_sp2] at hk
      have : nA (insert (sp 4) ((S0 m).erase (x1 j))) = m - 1 := by
        simp only [nA, mem_insert, mem_erase, ne_eq, x1_inj, x1_ne_sp, false_or,
          x1_mem_S0, and_true]
        rw [filter_ne' univ j, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
      rw [this] at hk; simp [ind] at hk; omega
  · -- deleting a vertex of `X₂`: `q₂` loses its star
    have hw : sp 5 ∉ (S0 m).erase (x2 j) := by simp
    obtain ⟨c, hc⟩ := hsf _ hw
    obtain ⟨hcT, hcv, hk⟩ := hc.card_le
    rcases hcv with rfl | hadj
    · rw [deg_sp5] at hk; simp [ind] at hk; omega
    · obtain rfl := eq_of_adj_sp5 hadj
      rw [deg_sp3] at hk
      have : nB (insert (sp 5) ((S0 m).erase (x2 j))) = m - 1 := by
        simp only [nB, mem_insert, mem_erase, ne_eq, x2_inj, x2_ne_sp, false_or,
          x2_mem_S0, and_true]
        rw [filter_ne' univ j, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
      rw [this] at hk; simp [ind] at hk; omega
  · rw [sp_mem_S0] at hs
    rcases hs with rfl | rfl | rfl
    · -- deleting `x₀`: `p` has no neighbour left
      have hw : sp 1 ∉ (S0 m).erase (sp 0) := by simp
      obtain ⟨c, hc⟩ := hsf _ hw
      obtain ⟨hcT, hcv, hk⟩ := hc.card_le
      rcases hcv with rfl | hadj
      · rw [deg_sp1] at hk; simp [ind] at hk
      · obtain rfl := eq_of_adj_sp1 hadj
        simp at hcT
    · -- deleting `c₁`: `q₁` has no neighbour left
      have hw : sp 4 ∉ (S0 m).erase (sp 2) := by simp
      obtain ⟨c, hc⟩ := hsf _ hw
      obtain ⟨hcT, hcv, hk⟩ := hc.card_le
      rcases hcv with rfl | hadj
      · rw [deg_sp4] at hk; simp [ind] at hk
      · obtain rfl := eq_of_adj_sp4 hadj
        simp at hcT
    · -- deleting `c₂`: `q₂` has no neighbour left
      have hw : sp 5 ∉ (S0 m).erase (sp 3) := by simp
      obtain ⟨c, hc⟩ := hsf _ hw
      obtain ⟨hcT, hcv, hk⟩ := hc.card_le
      rcases hcv with rfl | hadj
      · rw [deg_sp5] at hk; simp [ind] at hk
      · obtain rfl := eq_of_adj_sp5 hadj
        simp at hcT

theorem isMinimalStarForming_S0 (hm : 1 ≤ m) : IsMinimalStarForming (G m) (m + 1) (S0 m) :=
  isMinimalStarForming_of_erase _ _ isStarForming_S0 (not_isStarForming_erase hm)

/-! ## Main theorem -/

/-- For `m ≥ 1` and `k = m + 1`: `G m` is bipartite, has a minimal `k`-star-forming set of size
`3k`, and its largest `k`-independent sets have exactly `2k + 2` vertices. -/
theorem main (hm : 1 ≤ m) :
    (G m).Colorable 2 ∧
    IsMinimalStarForming (G m) (m + 1) (S0 m) ∧ #(S0 m) = 3 * (m + 1) ∧
    (∀ I, KIndep (G m) (m + 1) I → #I ≤ 2 * (m + 1) + 2) ∧
    KIndep (G m) (m + 1) (I0 m) ∧ #(I0 m) = 2 * (m + 1) + 2 :=
  ⟨colorable_two, isMinimalStarForming_S0 hm, by rw [card_S0]; ring,
    fun I hI => by have := kIndep_card_le I hI; omega, kIndep_I0 hm,
    by rw [card_I0]; ring⟩

/-- **Answer to Sahbi's Problem 7.3, and to the bipartite case of Conjecture 4.1 for every
`k ≥ 3`.**  For every `k ≥ 3` there is a bipartite graph (namely `G (k - 1)`, on `3k + 3`
vertices) with a minimal `k`-star-forming set larger than every `k`-independent set; in fact
`SF_k - β_k ≥ k - 2`. -/
theorem sf_gt_beta (k : ℕ) (hk : 3 ≤ k) :
    (G (k - 1)).Colorable 2 ∧
    ∃ S : Finset (W (k - 1)), IsMinimalStarForming (G (k - 1)) k S ∧
      ∀ I, KIndep (G (k - 1)) k I → #I + (k - 2) ≤ #S := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  show (G m).Colorable 2 ∧ ∃ S : Finset (W m), IsMinimalStarForming (G m) (m + 1) S ∧
      ∀ I, KIndep (G m) (m + 1) I → #I + (m + 1 - 2) ≤ #S
  obtain ⟨hc, hS, hcard, hI, -, -⟩ := main hm
  refine ⟨hc, S0 m, hS, fun I h => ?_⟩
  have := hI I h
  omega

/-- The vertex count of `G m`. -/
theorem card_W : Fintype.card (W m) = 3 * m + 6 := by
  simp [Fintype.card_sum]; ring

end StarForming
