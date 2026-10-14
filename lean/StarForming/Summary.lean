import StarForming.Family
import StarForming.Chain

/-!
# The two answers, stated with `β_k` and `SF_k`

* `betaK_family`: for every `k ≥ 3` the bipartite graph `G (k - 1)` has `β_k = 2k + 2` and
  `SF_k ≥ 3k`, so `β_k < SF_k` (`betaK_lt_sfK`). This refutes Sahbi's Conjecture 4.1 for every
  `k ≥ 3` and answers his Problem 7.3 in the negative.
* `sfK_eq_betaK_of_isChain` (in `StarForming.Chain`): `SF_k = β_k` on chain graphs for every
  `k ≥ 2`, which proves Sahbi's Conjecture 6.4.
-/

open Finset

namespace StarForming

/-- For `k ≥ 3`, `G (k - 1)` is bipartite with `β_k = 2k + 2` and `SF_k ≥ 3k`. -/
theorem betaK_family (k : ℕ) (hk : 3 ≤ k) :
    (G (k - 1)).Colorable 2 ∧ betaK (G (k - 1)) k = 2 * k + 2 ∧ 3 * k ≤ sfK (G (k - 1)) k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  show (G m).Colorable 2 ∧ betaK (G m) (m + 1) = 2 * (m + 1) + 2 ∧
    3 * (m + 1) ≤ sfK (G m) (m + 1)
  obtain ⟨hc, hS, hcard, hI, hI0, hcardI0⟩ := main hm
  refine ⟨hc, le_antisymm (betaK_le_iff.2 hI) ?_, ?_⟩
  · rw [← hcardI0]
    exact card_le_betaK hI0
  · rw [← hcard]
    exact card_le_sfK hS

/-- **Sahbi's Conjecture 4.1 fails for every `k ≥ 3`**: the bipartite graph `G (k - 1)` has
`β_k < SF_k`. -/
theorem betaK_lt_sfK (k : ℕ) (hk : 3 ≤ k) :
    (G (k - 1)).Colorable 2 ∧ betaK (G (k - 1)) k < sfK (G (k - 1)) k := by
  obtain ⟨hc, hb, hs⟩ := betaK_family k hk
  exact ⟨hc, by omega⟩

end StarForming
