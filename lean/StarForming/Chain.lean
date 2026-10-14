import StarForming.Local

/-!
# Chain graphs: `β_k = SF_k` for every `k ≥ 2`

Sahbi (arXiv:2610.03785, Conjecture 6.4) conjectured that `β_k(G) = SF_k(G)` for every chain graph
`G` and every `k ≥ 3`; he proved the case `k = 2`. A chain graph is a bipartite graph in which the
neighbourhoods of the vertices of one side are nested. We prove the conjecture for every `k ≥ 2`.

The proof: in a minimal `k`-star-forming set `S` of a chain graph, a vertex `h` with at least `k`
neighbours in `S` forces every vertex of `S` on the other side to have at most `k - 2` neighbours
in `S` (`deg_add_two_le`), and so `h` is the only such vertex (`eq_of_high`). Then
`exists_kIndep_of_unique_high` trades `S` for a `k`-independent set of the same size.
-/

open Finset

namespace StarForming

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-- `N(u) ⊆ N(v)`. -/
def NbhdLE (G : SimpleGraph V) (u v : V) : Prop :=
  ∀ w, G.Adj u w → G.Adj v w

/-- `G` is a chain graph with sides `side`: every edge joins the two sides, and the neighbourhoods
of the vertices on the side `false` are nested (Sahbi, Section 6). -/
def IsChain (G : SimpleGraph V) (side : V → Bool) : Prop :=
  (∀ u v, G.Adj u v → side u ≠ side v) ∧
    ∀ u v, side u = false → side v = false → NbhdLE G u v ∨ NbhdLE G v u

theorem bool_eq_of_ne_of_ne {a b c : Bool} (h1 : a ≠ b) (h2 : c ≠ b) : a = c := by
  revert h1 h2
  cases a <;> cases b <;> cases c <;> decide

variable {side : V → Bool}

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- In a chain graph the neighbourhoods of the vertices on either side are nested. -/
theorem IsChain.nested (hG : IsChain G side) {u v : V} (h : side u = side v) :
    NbhdLE G u v ∨ NbhdLE G v u := by
  cases hu : side u
  · exact hG.2 u v hu (h.symm.trans hu)
  · by_contra hcon
    push Not at hcon
    obtain ⟨huv, hvu⟩ := hcon
    simp only [NbhdLE, not_forall] at huv hvu
    obtain ⟨a, hua, hva⟩ := huv
    obtain ⟨b, hvb, hub⟩ := hvu
    have hv : side v = true := h.symm.trans hu
    have ha : side a = false :=
      Bool.eq_false_iff.2 fun e => hG.1 u a hua (hu.trans e.symm)
    have hb : side b = false :=
      Bool.eq_false_iff.2 fun e => hG.1 v b hvb (hv.trans e.symm)
    rcases hG.2 a b ha hb with hab | hba
    · exact hub (hab u hua.symm).symm
    · exact hva (hba v hvb.symm).symm

variable {S : Finset V}

/-- If `h ∈ S` has at least `k` neighbours in `S` and `y` is one of them, then deleting `y` from
`S` leaves uncovered a vertex `w ∉ S` adjacent to `y` all of whose other neighbours in `S` have
at most `k - 2` neighbours in `S`. -/
theorem exists_witness_of_adj_high (hG : IsChain G side) (hk : 2 ≤ k)
    (hS : IsMinimalStarForming G k S) {h y : V} (hh : h ∈ S) (hdh : k ≤ deg G S h)
    (hy : y ∈ S) (hhy : G.Adj h y) :
    ∃ w, w ∉ S ∧ G.Adj w y ∧ ∀ u ∈ S, u ≠ y → G.Adj w u → deg G S u + 2 ≤ k := by
  obtain ⟨w, hwT, hwc⟩ := hS.witness (by omega) hy
  have hhT : h ∈ S.erase y := mem_erase.2 ⟨G.ne_of_adj hhy, hh⟩
  have hdh' := deg_le_deg_erase_add_one (G := G) S h y
  have hshy : side h ≠ side y := hG.1 h y hhy
  by_cases hwy : w = y
  · rw [hwy] at hwc
    exact absurd (Or.inr ⟨h, hhT, hhy, by omega⟩) hwc
  have hwS : w ∉ S := fun h' => hwT (mem_erase.2 ⟨hwy, h'⟩)
  by_cases hsw : side w = side y
  · -- `w` is on the side of `y`: its neighbours keep their degrees, and its certificate in `S`
    -- would survive.
    exfalso
    have hdw : deg G (S.erase y) w = deg G S w :=
      deg_erase_of_not_adj fun hadj => hG.1 w y hadj hsw
    rcases hS.1.covered (by omega) hwS with hc | ⟨u, huS, hu, hcu⟩
    · exact hwc (Or.inl (by rw [hdw]; exact hc))
    · have hsuw : side u ≠ side w := hG.1 u w hu
      have hsu : side u = side h :=
        bool_eq_of_ne_of_ne (fun e => hsuw (e.trans hsw.symm)) hshy
      have huy : u ≠ y := fun e => hsuw (by rw [e, hsw])
      have hdu' := deg_le_deg_erase_add_one (G := G) S u y
      rcases hG.nested hsu with hle | hle
      · exact hwc (Or.inr ⟨h, hhT, hle w hu, by omega⟩)
      · have := deg_mono_nbhd (G := G) S hle
        exact hwc (Or.inr ⟨u, mem_erase.2 ⟨huy, huS⟩, hu, by omega⟩)
  · -- `w` is on the side of `h`; its neighbours are on the side of `y`.
    have hnb : ∀ u, G.Adj u w → ¬ G.Adj u y := fun u hu huy =>
      hG.1 u y huy (bool_eq_of_ne_of_ne (hG.1 u w hu) (Ne.symm hsw))
    by_cases hadj : G.Adj w y
    · refine ⟨w, hwS, hadj, fun u huS huy hwu => ?_⟩
      have hdu : deg G (S.erase y) u = deg G S u := deg_erase_of_not_adj (hnb u hwu.symm)
      by_contra hcon
      exact hwc (Or.inr ⟨u, mem_erase.2 ⟨huy, huS⟩, hwu.symm, by omega⟩)
    · exfalso
      have hdw : deg G (S.erase y) w = deg G S w := deg_erase_of_not_adj hadj
      rcases hS.1.covered (by omega) hwS with hc | ⟨u, huS, hu, hcu⟩
      · exact hwc (Or.inl (by rw [hdw]; exact hc))
      · have huy : u ≠ y := fun e => hadj (by rw [← e]; exact hu.symm)
        have hdu : deg G (S.erase y) u = deg G S u := deg_erase_of_not_adj (hnb u hu)
        exact hwc (Or.inr ⟨u, mem_erase.2 ⟨huy, huS⟩, hu, by rw [hdu]; exact hcu⟩)

/-- In a minimal `k`-star-forming set `S` of a chain graph (`k ≥ 2`), if some vertex `h ∈ S` has
at least `k` neighbours in `S`, then every vertex of `S` on the other side has at most `k - 2`. -/
theorem deg_add_two_le (hG : IsChain G side) (hk : 2 ≤ k) (hS : IsMinimalStarForming G k S)
    {h y : V} (hh : h ∈ S) (hdh : k ≤ deg G S h) (hy : y ∈ S) (hs : side y ≠ side h) :
    deg G S y + 2 ≤ k := by
  -- two neighbours `a`, `b` of `h` in `S` with `N(a) ⊆ N(b)` already force the bound
  have key : ∀ a b, a ∈ S → G.Adj h a → b ∈ S → a ≠ b → NbhdLE G a b → side b = side y →
      deg G S y + 2 ≤ k := by
    intro a b ha hha hb hab hle hsb
    obtain ⟨w, -, hwa, hw⟩ := exists_witness_of_adj_high hG hk hS hh hdh ha hha
    have hwb : G.Adj w b := (hle w hwa.symm).symm
    have hb2 : deg G S b + 2 ≤ k := hw b hb (Ne.symm hab) hwb
    rcases hG.nested hsb.symm with hyb | hby
    · have := deg_mono_nbhd (G := G) S hyb
      omega
    · by_cases hya : y = a
      · subst hya
        have := deg_mono_nbhd (G := G) S hle
        omega
      · exact hw y hy hya (hby w hwb.symm).symm
  have h2 : 1 < #(S.filter (G.Adj h)) := by
    change 1 < deg G S h
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 h2
  obtain ⟨haS, hha⟩ := mem_filter.1 ha
  obtain ⟨hbS, hhb⟩ := mem_filter.1 hb
  have hsa : side a = side y := bool_eq_of_ne_of_ne (Ne.symm (hG.1 h a hha)) hs
  have hsb : side b = side y := bool_eq_of_ne_of_ne (Ne.symm (hG.1 h b hhb)) hs
  rcases hG.nested (hsa.trans hsb.symm) with hle | hle
  · exact key a b haS hha hbS hab hle hsb
  · exact key b a hbS hhb haS (Ne.symm hab) hle hsa

/-- In a minimal `k`-star-forming set of a chain graph (`k ≥ 2`) at most one vertex has at least
`k` neighbours inside the set. -/
theorem eq_of_high (hG : IsChain G side) (hk : 2 ≤ k) (hS : IsMinimalStarForming G k S)
    {h t : V} (hh : h ∈ S) (hdh : k ≤ deg G S h) (ht : t ∈ S) (hdt : k ≤ deg G S t) :
    h = t := by
  by_contra hne
  by_cases hs : side t = side h
  swap
  · have := deg_add_two_le hG hk hS hh hdh ht hs
    omega
  -- `a`, `b` on the same side with `N(b) ⊆ N(a)`: deleting `b` leaves every vertex covered
  have key : ∀ a b, a ∈ S → k ≤ deg G S a → b ∈ S → k ≤ deg G S b → a ≠ b →
      side a = side b → NbhdLE G b a → False := by
    intro a b ha hda hb hdb hab hsab hle
    obtain ⟨z, hzT, hzc⟩ := hS.witness (by omega) hb
    by_cases hzb : z = b
    · rw [hzb] at hzc
      exact hzc (Or.inl (by rw [deg_erase_self]; exact hdb))
    have hzS : z ∉ S := fun h' => hzT (mem_erase.2 ⟨hzb, h'⟩)
    have haT : a ∈ S.erase b := mem_erase.2 ⟨hab, ha⟩
    have hda' : deg G (S.erase b) a = deg G S a :=
      deg_erase_of_not_adj fun hadj => hG.1 a b hadj hsab
    by_cases hsz : side z = side b
    · have hdz : deg G (S.erase b) z = deg G S z :=
        deg_erase_of_not_adj fun hadj => hG.1 z b hadj hsz
      rcases hS.1.covered (by omega) hzS with hc | ⟨u, huS, hu, hcu⟩
      · exact hzc (Or.inl (by rw [hdz]; exact hc))
      · have hsu : side u ≠ side a := fun e => hG.1 u z hu (e.trans (hsab.trans hsz.symm))
        have := deg_add_two_le hG hk hS ha hda huS hsu
        omega
    · have hza : ¬ G.Adj a z := fun hadj => hzc (Or.inr ⟨a, haT, hadj, by omega⟩)
      have hbz : ¬ G.Adj b z := fun hadj => hza (hle z hadj)
      have hdz : deg G (S.erase b) z = deg G S z :=
        deg_erase_of_not_adj fun hadj => hbz hadj.symm
      rcases hS.1.covered (by omega) hzS with hc | ⟨u, huS, hu, hcu⟩
      · exact hzc (Or.inl (by rw [hdz]; exact hc))
      · have hub : u ≠ b := fun e => hbz (by rw [← e]; exact hu)
        have hsu : side u = side b := bool_eq_of_ne_of_ne (hG.1 u z hu) (Ne.symm hsz)
        have hdu : deg G (S.erase b) u = deg G S u :=
          deg_erase_of_not_adj fun hadj => hG.1 u b hadj hsu
        exact hzc (Or.inr ⟨u, mem_erase.2 ⟨hub, huS⟩, hu, by rw [hdu]; exact hcu⟩)
  rcases hG.nested hs with hle | hle
  · exact key h t hh hdh ht hdt hne hs.symm hle
  · exact key t h ht hdt hh hdh (Ne.symm hne) hs hle

/-- Every minimal `k`-star-forming set of a chain graph (`k ≥ 2`) has the size of a
`k`-independent set. -/
theorem exists_kIndep_card_eq (hG : IsChain G side) (hk : 2 ≤ k)
    (hS : IsMinimalStarForming G k S) : ∃ I, KIndep G k I ∧ #I = #S :=
  exists_kIndep_of_unique_high (by omega) hS fun _ hh _ ht hdh hdt =>
    eq_of_high hG hk hS hh hdh ht hdt

/-- **Sahbi's Conjecture 6.4, for every `k ≥ 2`.** For every chain graph `G`,
`SF_k(G) = β_k(G)`. -/
theorem sfK_eq_betaK_of_isChain [Fintype V] (hG : IsChain G side) (hk : 2 ≤ k) :
    sfK G k = betaK G k :=
  le_antisymm
    (sfK_le_iff.2 fun _ hS =>
      let ⟨_, hI, hcard⟩ := exists_kIndep_card_eq hG hk hS
      by rw [← hcard]; exact card_le_betaK hI)
    (betaK_le_sfK (by omega))

end StarForming
