import StarForming.Basic

/-!
# The local form of the definition, and the numbers `β_k` and `SF_k`

* `deg G T v` is the number of neighbours of `v` in `T`.
* `Covered G k T v` is the local condition of Lemma 2.2 of Sahbi: `v` has `k` neighbours in `T`, or
  a neighbour `u ∈ T` with `k - 1` neighbours in `T`. For `v ∉ T` and `k ≥ 1` it says exactly
  that `G[T ∪ {v}]` contains a copy of `K_{1,k}` through `v` (`starAt_iff_covered`).
* `betaK G k` and `sfK G k` are `β_k(G)` and `SF_k(G)`, and `betaK_le_sfK` is the inequality
  `β_k ≤ SF_k` of Chellali and Favaron.
* `exists_kIndep_of_unique_high`: a minimal `k`-star-forming set with at most one vertex of degree
  at least `k` inside it can be traded for a `k`-independent set of the same size.
-/

open Finset

set_option linter.unusedSectionVars false

namespace StarForming

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-- The number of neighbours of `v` in `T`. -/
def deg (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : V) : ℕ :=
  #(T.filter (G.Adj v))

theorem deg_mono_nbhd (T : Finset V) {u v : V} (h : ∀ w, G.Adj u w → G.Adj v w) :
    deg G T u ≤ deg G T v :=
  card_le_card (by intro w; simp only [mem_filter]; exact fun hw => ⟨hw.1, h w hw.2⟩)

theorem deg_erase_of_not_adj {T : Finset V} {v s : V} (h : ¬ G.Adj v s) :
    deg G (T.erase s) v = deg G T v := by
  unfold deg
  rw [filter_erase, erase_eq_of_notMem (by simp [h])]

theorem deg_erase_self (T : Finset V) (v : V) : deg G (T.erase v) v = deg G T v :=
  deg_erase_of_not_adj (G.irrefl)

theorem deg_erase_le (T : Finset V) (v s : V) : deg G (T.erase s) v ≤ deg G T v :=
  card_le_card (filter_subset_filter _ (erase_subset _ _))

theorem deg_le_deg_erase_add_one (T : Finset V) (v s : V) :
    deg G T v ≤ deg G (T.erase s) v + 1 := by
  unfold deg
  rw [filter_erase]
  have := pred_card_le_card_erase (s := T.filter (G.Adj v)) (a := s)
  omega

theorem deg_erase_of_adj {T : Finset V} {v s : V} (h : G.Adj v s) (hs : s ∈ T) :
    deg G (T.erase s) v + 1 = deg G T v := by
  unfold deg
  have hmem : s ∈ T.filter (G.Adj v) := mem_filter.2 ⟨hs, h⟩
  rw [filter_erase, card_erase_of_mem hmem]
  have := card_pos.2 ⟨s, hmem⟩
  omega

theorem deg_insert_self (T : Finset V) (v : V) : deg G (insert v T) v = deg G T v := by
  unfold deg
  rw [filter_insert]
  simp

theorem deg_insert_of_not_adj {T : Finset V} {v z : V} (h : ¬ G.Adj v z) :
    deg G (insert z T) v = deg G T v := by
  unfold deg
  rw [filter_insert]
  simp [h]

theorem deg_insert_of_adj {T : Finset V} {v z : V} (h : G.Adj v z) (hz : z ∉ T) :
    deg G (insert z T) v = deg G T v + 1 := by
  unfold deg
  simp only [filter_insert, h, ↓reduceIte]
  rw [card_insert_of_notMem (by simp [hz])]

/-- The local condition of Lemma 2.2 of Sahbi for a vertex `v` and a set `T`. -/
def Covered (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (T : Finset V) (v : V) : Prop :=
  k ≤ deg G T v ∨ ∃ u ∈ T, G.Adj u v ∧ k ≤ deg G T u + 1

/-- Lemma 2.2 of Sahbi: for `v ∉ T` and `k ≥ 1`, `G[T ∪ {v}]` contains a copy of `K_{1,k}`
through `v` if and only if `v` has `k` neighbours in `T` or a neighbour in `T` with `k - 1`
neighbours in `T`. -/
theorem starAt_iff_covered (hk : 1 ≤ k) {T : Finset V} {v : V} (hv : v ∉ T) :
    (∃ c, StarAt G k (insert v T) v c) ↔ Covered G k T v := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨hcT, hcv, hcard⟩ := hc.card_le
    change k ≤ deg G (insert v T) c at hcard
    by_cases hcv' : c = v
    · rw [hcv', deg_insert_self] at hcard
      exact Or.inl hcard
    · have hadj : G.Adj c v := hcv.resolve_left hcv'
      rw [deg_insert_of_adj hadj hv] at hcard
      exact Or.inr ⟨c, (mem_insert.1 hcT).resolve_left hcv', hadj, hcard⟩
  · rintro (h | ⟨u, huT, hadj, h⟩)
    · obtain ⟨L, hL, hcard⟩ := exists_subset_card_eq (s := T.filter (G.Adj v)) h
      exact ⟨v, mem_insert_self _ _, L, hL.trans (filter_subset_filter _ (subset_insert _ _)),
        hcard, Or.inl rfl⟩
    · obtain ⟨L, hL, hcard⟩ :=
        exists_subset_card_eq (s := T.filter (G.Adj u)) (n := k - 1) (by unfold deg at h; omega)
      have hvL : v ∉ L := fun h' => hv (mem_filter.1 (hL h')).1
      refine ⟨u, mem_insert_of_mem huT, insert v L, ?_, ?_, Or.inr (mem_insert_self _ _)⟩
      · intro w hw
        rcases mem_insert.1 hw with rfl | hw
        · exact mem_filter.2 ⟨mem_insert_self _ _, hadj⟩
        · exact filter_subset_filter _ (subset_insert _ _) (hL hw)
      · rw [card_insert_of_notMem hvL, hcard]
        omega

theorem IsStarForming.covered (hk : 1 ≤ k) {S : Finset V} (hS : IsStarForming G k S) {v : V}
    (hv : v ∉ S) : Covered G k S v :=
  (starAt_iff_covered hk hv).1 (hS v hv)

theorem isStarForming_of_covered (hk : 1 ≤ k) {S : Finset V}
    (h : ∀ v, v ∉ S → Covered G k S v) : IsStarForming G k S :=
  fun v hv => (starAt_iff_covered hk hv).2 (h v hv)

/-- Minimality: deleting a vertex `s` of a minimal `k`-star-forming set leaves some vertex `w`
uncovered. -/
theorem IsMinimalStarForming.witness (hk : 1 ≤ k) {S : Finset V}
    (hS : IsMinimalStarForming G k S) {s : V} (hs : s ∈ S) :
    ∃ w, w ∉ S.erase s ∧ ¬ Covered G k (S.erase s) w := by
  by_contra hcon
  push Not at hcon
  exact hS.2 _ (erase_ssubset hs) (isStarForming_of_covered hk hcon)

/-- A minimal `k`-star-forming set with at most one vertex of degree at least `k` inside it can be
traded for a `k`-independent set of the same size: if there is such a vertex `h`, replace it by a
vertex left uncovered by `S ∖ {h}`. -/
theorem exists_kIndep_of_unique_high (hk : 1 ≤ k) {S : Finset V}
    (hS : IsMinimalStarForming G k S)
    (huniq : ∀ h ∈ S, ∀ t ∈ S, k ≤ deg G S h → k ≤ deg G S t → h = t) :
    ∃ I, KIndep G k I ∧ #I = #S := by
  by_cases hD : ∃ h ∈ S, k ≤ deg G S h
  · obtain ⟨h, hh, hdh⟩ := hD
    obtain ⟨z, hzT, hzc⟩ := hS.witness hk hh
    have hzh : z ≠ h := by
      rintro rfl
      exact hzc (Or.inl (by rw [deg_erase_self]; exact hdh))
    refine ⟨insert z (S.erase h), ?_, ?_⟩
    · intro v hv
      change deg G (insert z (S.erase h)) v < k
      rcases mem_insert.1 hv with rfl | hvT
      · rw [deg_insert_self]
        by_contra hc
        exact hzc (Or.inl (by omega))
      · have hvh : v ≠ h := (mem_erase.1 hvT).1
        have hvS : v ∈ S := (mem_erase.1 hvT).2
        have hlow : deg G S v < k := by
          by_contra hc
          exact hvh (huniq v hvS h hh (by omega) hdh)
        by_cases hvz : G.Adj v z
        · rw [deg_insert_of_adj hvz hzT]
          by_contra hc
          exact hzc (Or.inr ⟨v, hvT, hvz, by omega⟩)
        · rw [deg_insert_of_not_adj hvz]
          have := deg_erase_le (G := G) S v h
          omega
    · rw [card_insert_of_notMem hzT, card_erase_of_mem hh]
      have := card_pos.2 ⟨h, hh⟩
      omega
  · push Not at hD
    exact ⟨S, fun v hv => hD v hv, rfl⟩

/-- Chellali and Favaron: a `k`-independent set that is maximal with respect to inclusion is a
minimal `k`-star-forming set. -/
theorem isMinimalStarForming_of_maximal (hk : 1 ≤ k) {J : Finset V} (hJ : KIndep G k J)
    (hmax : ∀ v, v ∉ J → ¬ KIndep G k (insert v J)) : IsMinimalStarForming G k J := by
  refine isMinimalStarForming_of_erase G k (isStarForming_of_covered hk fun v hv => ?_) ?_
  · have hnot := hmax v hv
    unfold KIndep at hnot
    push Not at hnot
    obtain ⟨u, hu, hku⟩ := hnot
    change k ≤ deg G (insert v J) u at hku
    rcases mem_insert.1 hu with rfl | huJ
    · rw [deg_insert_self] at hku
      exact Or.inl hku
    · have hlow : deg G J u < k := hJ u huJ
      by_cases huv : G.Adj u v
      · rw [deg_insert_of_adj huv hv] at hku
        exact Or.inr ⟨u, huJ, huv, hku⟩
      · rw [deg_insert_of_not_adj huv] at hku
        omega
  · intro s hs hsf
    have hc := hsf.covered hk (notMem_erase s J)
    rcases hc with hc | ⟨u, huT, hus, hc⟩
    · rw [deg_erase_self] at hc
      have := hJ s hs
      change deg G J s < k at this
      omega
    · have := deg_erase_of_adj hus hs
      have := hJ u (mem_of_mem_erase huT)
      change deg G J u < k at this
      omega

/-- Every `k`-independent set lies in a minimal `k`-star-forming set at least as large. -/
theorem exists_minimalStarForming_ge [Fintype V] (hk : 1 ≤ k) {I : Finset V} (hI : KIndep G k I) :
    ∃ S, IsMinimalStarForming G k S ∧ #I ≤ #S := by
  classical
  let F := (univ : Finset (Finset V)).filter fun J => I ⊆ J ∧ KIndep G k J
  obtain ⟨J, hJF, hJmax⟩ := exists_max_image F card ⟨I, mem_filter.2 ⟨mem_univ _, subset_rfl, hI⟩⟩
  obtain ⟨-, hIJ, hJ⟩ := mem_filter.1 hJF
  refine ⟨J, isMinimalStarForming_of_maximal hk hJ fun v hv hvJ => ?_, card_le_card hIJ⟩
  have := hJmax (insert v J) (mem_filter.2 ⟨mem_univ _, hIJ.trans (subset_insert _ _), hvJ⟩)
  rw [card_insert_of_notMem hv] at this
  omega

section numbers

variable [Fintype V]

open Classical in
/-- `β_k(G)`: the largest size of a `k`-independent set. -/
noncomputable def betaK (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  ((univ : Finset (Finset V)).filter (KIndep G k)).sup card

open Classical in
/-- `SF_k(G)`: the largest size of a minimal `k`-star-forming set. -/
noncomputable def sfK (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  ((univ : Finset (Finset V)).filter (IsMinimalStarForming G k)).sup card

theorem card_le_betaK {I : Finset V} (h : KIndep G k I) : #I ≤ betaK G k := by
  unfold betaK
  exact le_sup (f := card) (by simpa using h)

theorem card_le_sfK {S : Finset V} (h : IsMinimalStarForming G k S) : #S ≤ sfK G k := by
  unfold sfK
  exact le_sup (f := card) (by simpa using h)

theorem betaK_le_iff {n : ℕ} : betaK G k ≤ n ↔ ∀ I, KIndep G k I → #I ≤ n := by
  classical
  unfold betaK
  rw [Finset.sup_le_iff]
  simp

theorem sfK_le_iff {n : ℕ} : sfK G k ≤ n ↔ ∀ S, IsMinimalStarForming G k S → #S ≤ n := by
  classical
  unfold sfK
  rw [Finset.sup_le_iff]
  simp

/-- Chellali and Favaron: `β_k(G) ≤ SF_k(G)` for `k ≥ 1`. -/
theorem betaK_le_sfK (hk : 1 ≤ k) : betaK G k ≤ sfK G k :=
  betaK_le_iff.2 fun _ hI =>
    let ⟨_, hS, hle⟩ := exists_minimalStarForming_ge hk hI
    hle.trans (card_le_sfK hS)

end numbers

end StarForming
