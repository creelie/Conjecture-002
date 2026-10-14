import Mathlib

/-!
# k-independence and k-star-forming sets

Definitions from R. Sahbi, *Upper k-star-forming sets, k-independence, and upper domination*,
arXiv:2610.03785, following Chellali and Favaron.

* `KIndep G k I`: the induced subgraph `G[I]` has maximum degree less than `k`;
  `β_k(G)` is the largest size of such a set.
* `IsStarForming G k S`: for every vertex `v ∉ S`, the induced subgraph `G[S ∪ {v}]` contains a
  copy of `K_{1,k}` that contains `v` (Definition 2.1 of the paper).
* `IsMinimalStarForming G k S`: `S` is k-star-forming and no proper subset of `S` is;
  `SF_k(G)` is the largest size of such a set.
-/

open Finset

namespace StarForming

variable {V : Type*} [DecidableEq V]

/-- `I` is `k`-independent: every vertex of `I` has fewer than `k` neighbours in `I`. -/
def KIndep (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (I : Finset V) : Prop :=
  ∀ v ∈ I, #(I.filter (G.Adj v)) < k

/-- `T` contains a star `K_{1,k}` with centre `c` (and `k` leaves in `T`) that contains `v`. -/
def StarAt (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (T : Finset V) (v c : V) : Prop :=
  c ∈ T ∧ ∃ L ⊆ T.filter (G.Adj c), #L = k ∧ (c = v ∨ v ∈ L)

/-- `S` is `k`-star-forming: every vertex `v` outside `S` lies in a copy of `K_{1,k}`
inside `G[S ∪ {v}]`. -/
def IsStarForming (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (S : Finset V) : Prop :=
  ∀ v, v ∉ S → ∃ c, StarAt G k (insert v S) v c

/-- `S` is a minimal `k`-star-forming set. -/
def IsMinimalStarForming (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (S : Finset V) :
    Prop :=
  IsStarForming G k S ∧ ∀ T, T ⊂ S → ¬ IsStarForming G k T

variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)

/-- Supersets of star-forming sets are star-forming. -/
theorem isStarForming_mono {S S' : Finset V} (h : IsStarForming G k S) (hSS' : S ⊆ S') :
    IsStarForming G k S' := by
  intro v hv
  obtain ⟨c, hc, L, hL, hcard, hvL⟩ := h v (fun h' => hv (hSS' h'))
  refine ⟨c, insert_subset_insert v hSS' hc, L, ?_, hcard, hvL⟩
  exact hL.trans (filter_subset_filter _ (insert_subset_insert v hSS'))

/-- Minimality only has to be tested on one-point deletions. -/
theorem isMinimalStarForming_of_erase {S : Finset V} (h : IsStarForming G k S)
    (herase : ∀ s ∈ S, ¬ IsStarForming G k (S.erase s)) : IsMinimalStarForming G k S := by
  refine ⟨h, fun T hT hTsf => ?_⟩
  obtain ⟨s, hsS, hsT⟩ := exists_of_ssubset hT
  exact herase s hsS (isStarForming_mono G k hTsf (subset_erase.2 ⟨hT.subset, hsT⟩))

omit [DecidableEq V] in
/-- A star at `c` containing `v` forces `c = v` or `c` adjacent to `v`, and at least `k`
neighbours of `c` in `T`. -/
theorem StarAt.card_le {T : Finset V} {v c : V} (h : StarAt G k T v c) :
    c ∈ T ∧ (c = v ∨ G.Adj c v) ∧ k ≤ #(T.filter (G.Adj c)) := by
  obtain ⟨hc, L, hL, hcard, hvL⟩ := h
  refine ⟨hc, ?_, hcard ▸ card_le_card hL⟩
  rcases hvL with h | h
  · exact Or.inl h
  · exact Or.inr (mem_filter.1 (hL h)).2

end StarForming
