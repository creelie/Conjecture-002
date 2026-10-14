import StarForming.Local

/-!
# Computing `SF_2` is NP-hard on bipartite graphs

For a graph `H` let `gadget H` be the graph obtained by replacing every edge `uv` of `H` by a path
`u - a - b - c - v` with three new inner vertices and attaching a new pendant vertex to every
vertex of `H`. It is bipartite, and

  `SF₂(gadget H) = β₂(gadget H) = |V(H)| + 2 |E(H)| + α(H)`

(`sfK_gadget`, the identity of Theorem 1.4 of the paper). Since the gadget is built in polynomial time and computing the independence number
`α(H)` is NP-hard, computing `SF₂` is NP-hard on bipartite graphs; this answers Problem 9.3 of
Sahbi's paper.

The vertices of `H` carry a linear order, so that every edge is listed once as a pair `(u, v)` with
`u < v` (`Edge H`); the inner vertex at position `a` is next to `u` and the one at `c` next to `v`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace StarForming

variable {W : Type*} [LinearOrder W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The edges of `H`, each listed once as a pair `(u, v)` with `u < v`. -/
abbrev Edge := {p : W × W // p.1 < p.2 ∧ H.Adj p.1 p.2}

/-- The three inner vertices of a subdivided edge `(u, v)`: `a` next to `u`, `b` in the middle and
`c` next to `v`. -/
inductive Pos
  | a | b | c
  deriving DecidableEq

instance : Fintype Pos := ⟨{.a, .b, .c}, fun x => by cases x <;> simp⟩

/-- The vertices of the gadget: `inl v` is the vertex `v` of `H`, `inr (inl v)` the pendant vertex
at `v`, and `inr (inr (e, p))` the inner vertex of the edge `e` at position `p`. -/
abbrev Pt := W ⊕ W ⊕ (Edge H × Pos)

instance : DecidableEq (Pt H) :=
  @instDecidableEqSum W (W ⊕ (Edge H × Pos)) (fun a b => LinearOrder.toDecidableEq a b)
    (@instDecidableEqSum W (Edge H × Pos) (fun a b => LinearOrder.toDecidableEq a b) inferInstance)

variable {H}

/-- The vertex `v` of `H`. -/
abbrev orig (v : W) : Pt H := .inl v
/-- The pendant vertex at `v`. -/
abbrev pend (v : W) : Pt H := .inr (.inl v)
/-- The inner vertex of the edge `e` at position `p`. -/
abbrev inn (e : Edge H) (p : Pos) : Pt H := .inr (.inr (e, p))

variable (H)

/-- One direction of the adjacency of the gadget. -/
def Link : Pt H → Pt H → Prop
  | .inl v, .inr (.inl w) => v = w
  | .inl v, .inr (.inr (e, .a)) => v = e.1.1
  | .inl v, .inr (.inr (e, .c)) => v = e.1.2
  | .inr (.inr (e, .a)), .inr (.inr (f, .b)) => e = f
  | .inr (.inr (e, .b)), .inr (.inr (f, .c)) => e = f
  | _, _ => False

instance (x y : Pt H) : Decidable (Link H x y) := by
  rcases x with v | v | ⟨e, p⟩ <;> rcases y with w | w | ⟨f, q⟩ <;>
    (try cases p) <;> (try cases q) <;> unfold Link <;> infer_instance

/-- The gadget: triple subdivision of `H` with a pendant vertex at every vertex of `H`. -/
def gadget : SimpleGraph (Pt H) where
  Adj x y := Link H x y ∨ Link H y x
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun x h => by
    rcases x with v | v | ⟨e, p⟩ <;> (try cases p) <;> simp [Link] at h⟩

instance : DecidableRel (gadget H).Adj := fun x y =>
  inferInstanceAs (Decidable (Link H x y ∨ Link H y x))

variable {H}

/-! ### Neighbourhoods -/

theorem adj_pend_iff {x : Pt H} {v : W} : (gadget H).Adj x (pend v) ↔ x = orig v := by
  rcases x with w | w | ⟨f, q⟩ <;> (try cases q) <;> simp [gadget, Link]

theorem adj_innA_iff {x : Pt H} {e : Edge H} :
    (gadget H).Adj x (inn e .a) ↔ x = orig e.1.1 ∨ x = inn e .b := by
  rcases x with w | w | ⟨f, q⟩ <;> (try cases q) <;> simp [gadget, Link]; aesop

theorem adj_innB_iff {x : Pt H} {e : Edge H} :
    (gadget H).Adj x (inn e .b) ↔ x = inn e .a ∨ x = inn e .c := by
  rcases x with w | w | ⟨f, q⟩ <;> (try cases q) <;> simp [gadget, Link] <;> aesop

theorem adj_innC_iff {x : Pt H} {e : Edge H} :
    (gadget H).Adj x (inn e .c) ↔ x = orig e.1.2 ∨ x = inn e .b := by
  rcases x with w | w | ⟨f, q⟩ <;> (try cases q) <;> simp [gadget, Link] <;> aesop

theorem adj_orig_iff {x : Pt H} {v : W} :
    (gadget H).Adj x (orig v) ↔
      x = pend v ∨ (∃ e : Edge H, e.1.1 = v ∧ x = inn e .a) ∨
        (∃ e : Edge H, e.1.2 = v ∧ x = inn e .c) := by
  rcases x with w | w | ⟨f, q⟩ <;> (try cases q) <;> simp [gadget, Link] <;> aesop

theorem adj_orig_innA (e : Edge H) : (gadget H).Adj (orig e.1.1) (inn e .a) :=
  adj_innA_iff.2 (Or.inl rfl)

theorem adj_orig_innC (e : Edge H) : (gadget H).Adj (orig e.1.2) (inn e .c) :=
  adj_innC_iff.2 (Or.inl rfl)

theorem adj_innAB (e : Edge H) : (gadget H).Adj (inn e .a) (inn e .b) :=
  adj_innB_iff.2 (Or.inl rfl)

theorem adj_innCB (e : Edge H) : (gadget H).Adj (inn e .c) (inn e .b) :=
  adj_innB_iff.2 (Or.inr rfl)

theorem adj_orig_pend (v : W) : (gadget H).Adj (orig v) (pend v) :=
  adj_pend_iff.2 rfl

/-- The colour classes: `H`'s vertices and middle inner vertices, against the rest. -/
def gadgetSide : Pt H → Fin 2
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (_, .b)) => 0
  | .inr (.inr (_, _)) => 1

/-- The gadget is bipartite. -/
theorem gadget_colorable : (gadget H).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk gadgetSide fun {x y} h => ?_⟩
  rcases x with v | v | ⟨e, p⟩ <;> rcases y with w | w | ⟨f, q⟩ <;>
    (try cases p) <;> (try cases q) <;> simp [gadget, Link, gadgetSide] at h ⊢

/-! ### Covering lemmas for `k = 2` -/

section covering

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem covered_of_two {T : Finset V} {v a b : V} (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b)
    (haT : a ∈ T) (hbT : b ∈ T) : Covered G 2 T v := by
  left
  have hsub : ({a, b} : Finset V) ⊆ T.filter (G.Adj v) := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_filter.2 ⟨haT, ha⟩
    · rw [mem_singleton.1 hx]; exact mem_filter.2 ⟨hbT, hb⟩
  have := card_le_card hsub
  rw [card_pair hab] at this
  exact this

theorem covered_of_path {T : Finset V} {v u z : V} (huv : G.Adj u v) (huT : u ∈ T)
    (huz : G.Adj u z) (hzT : z ∈ T) : Covered G 2 T v := by
  right
  refine ⟨u, huT, huv, ?_⟩
  have : 1 ≤ deg G T u := card_pos.2 ⟨z, mem_filter.2 ⟨hzT, huz⟩⟩
  omega

/-- Deleting a vertex `s` at distance at least three from `w` does not change whether `w` is
covered. -/
theorem covered_erase_of_far {k : ℕ} {S : Finset V} {w s : V} (h1 : ¬ G.Adj w s)
    (h2 : ∀ u, G.Adj w u → ¬ G.Adj u s) (hc : Covered G k S w) : Covered G k (S.erase s) w := by
  rcases hc with hc | ⟨u, huS, huw, hc⟩
  · left
    rwa [deg_erase_of_not_adj h1]
  · right
    have hus : u ≠ s := by
      rintro rfl
      exact h1 huw.symm
    refine ⟨u, mem_erase.2 ⟨hus, huS⟩, huw, ?_⟩
    rwa [deg_erase_of_not_adj (h2 u huw.symm)]

end covering

/-! ### Minimal 2-star-forming sets of the gadget -/

variable {S : Finset (Pt H)}

/-- A pendant vertex outside `S` forces its neighbour into `S`. -/
theorem orig_mem_of_pend_notMem (hS : IsStarForming (gadget H) 2 S) {v : W} (hv : pend v ∉ S) :
    orig v ∈ S := by
  rcases hS.covered (by norm_num) hv with hc | ⟨u, huS, hu, -⟩
  · exfalso
    have hsub : S.filter ((gadget H).Adj (pend v)) ⊆ {orig v} := by
      intro x hx
      have := (mem_filter.1 hx).2
      exact mem_singleton.2 (adj_pend_iff.1 this.symm)
    have := (card_le_card hsub).trans (card_singleton _).le
    change 2 ≤ #(S.filter ((gadget H).Adj (pend v))) at hc
    omega
  · rwa [adj_pend_iff.1 hu] at huS

/-- The general shape of the argument: if every vertex outside `S ∖ {s}` is covered by `S ∖ {s}`,
then `S` is not minimal. -/
theorem not_minimal_of_covered {s : Pt H} (hS : IsMinimalStarForming (gadget H) 2 S) (hs : s ∈ S)
    (h : ∀ w, w ∉ S.erase s → Covered (gadget H) 2 (S.erase s) w) : False :=
  hS.2 _ (erase_ssubset hs) (isStarForming_of_covered (by norm_num) h)

/-- In a minimal 2-star-forming set no edge has all three inner vertices in `S`. -/
theorem not_all_inner (hS : IsMinimalStarForming (gadget H) 2 S) (e : Edge H)
    (h0 : inn e .a ∈ S) (h1 : inn e .b ∈ S) (h2 : inn e .c ∈ S) : False := by
  have hne02 : inn e .a ≠ (inn e .c : Pt H) := by simp
  have hne01 : inn e .a ≠ (inn e .b : Pt H) := by simp
  have hne21 : inn e .c ≠ (inn e .b : Pt H) := by simp
  refine not_minimal_of_covered hS h1 fun w hw => ?_
  by_cases hws : w = inn e .b
  · subst hws
    exact covered_of_two (adj_innAB e).symm (adj_innCB e).symm hne02
      (mem_erase.2 ⟨hne01, h0⟩) (mem_erase.2 ⟨hne21, h2⟩)
  have hwS : w ∉ S := fun h => hw (mem_erase.2 ⟨hws, h⟩)
  by_cases ha : (gadget H).Adj w (inn e .b)
  · rcases adj_innB_iff.1 ha with rfl | rfl <;> contradiction
  by_cases hb : ∃ u, (gadget H).Adj w u ∧ (gadget H).Adj u (inn e .b)
  · obtain ⟨u, hwu, hu⟩ := hb
    rcases adj_innB_iff.1 hu with rfl | rfl
    · rcases adj_innA_iff.1 hwu with rfl | rfl
      · have hp := orig_mem_of_pend_notMem hS.1 (v := e.1.1)
        have hpS : pend e.1.1 ∈ S := by
          by_contra hp'
          exact hwS (hp hp')
        exact covered_of_two (adj_orig_pend _) (adj_orig_innA e) (by simp)
          (mem_erase.2 ⟨by simp, hpS⟩) (mem_erase.2 ⟨hne01, h0⟩)
      · exact absurd rfl hws
    · rcases adj_innC_iff.1 hwu with rfl | rfl
      · have hp := orig_mem_of_pend_notMem hS.1 (v := e.1.2)
        have hpS : pend e.1.2 ∈ S := by
          by_contra hp'
          exact hwS (hp hp')
        exact covered_of_two (adj_orig_pend _) (adj_orig_innC e) (by simp)
          (mem_erase.2 ⟨by simp, hpS⟩) (mem_erase.2 ⟨hne21, h2⟩)
      · exact absurd rfl hws
  push Not at hb
  exact covered_erase_of_far ha hb (hS.1.covered (by norm_num) hwS)


/-- If both ends of `e` lie in `S` together with their pendant vertices, then `S` contains at most
one inner vertex of `e`: positions `a` and `b`. -/
theorem not_inner_ab (hS : IsMinimalStarForming (gadget H) 2 S) (e : Edge H)
    (hu : orig e.1.1 ∈ S) (hv : orig e.1.2 ∈ S) (hpv : pend e.1.2 ∈ S)
    (ha : inn e .a ∈ S) (hb : inn e .b ∈ S) : False := by
  by_cases hc : inn e .c ∈ S
  · exact not_all_inner hS e ha hb hc
  refine not_minimal_of_covered hS hb fun w hw => ?_
  by_cases hws : w = inn e .b
  · subst hws
    exact covered_of_path (adj_innAB e) (mem_erase.2 ⟨by simp, ha⟩) (adj_orig_innA e).symm
      (mem_erase.2 ⟨by simp, hu⟩)
  have hwS : w ∉ S := fun h => hw (mem_erase.2 ⟨hws, h⟩)
  by_cases h1 : (gadget H).Adj w (inn e .b)
  · rcases adj_innB_iff.1 h1 with rfl | rfl
    · exact absurd ha hwS
    · exact covered_of_path (adj_orig_innC e) (mem_erase.2 ⟨by simp, hv⟩) (adj_orig_pend _)
        (mem_erase.2 ⟨by simp, hpv⟩)
  by_cases h2 : ∃ u, (gadget H).Adj w u ∧ (gadget H).Adj u (inn e .b)
  · obtain ⟨u, hwu, hu'⟩ := h2
    rcases adj_innB_iff.1 hu' with rfl | rfl
    · rcases adj_innA_iff.1 hwu with rfl | rfl
      · exact absurd hu hwS
      · exact absurd rfl hws
    · rcases adj_innC_iff.1 hwu with rfl | rfl
      · exact absurd hv hwS
      · exact absurd rfl hws
  push Not at h2
  exact covered_erase_of_far h1 h2 (hS.1.covered (by norm_num) hwS)

/-- Positions `b` and `c`. -/
theorem not_inner_bc (hS : IsMinimalStarForming (gadget H) 2 S) (e : Edge H)
    (hu : orig e.1.1 ∈ S) (hpu : pend e.1.1 ∈ S) (hv : orig e.1.2 ∈ S)
    (hb : inn e .b ∈ S) (hc : inn e .c ∈ S) : False := by
  by_cases ha : inn e .a ∈ S
  · exact not_all_inner hS e ha hb hc
  refine not_minimal_of_covered hS hb fun w hw => ?_
  by_cases hws : w = inn e .b
  · subst hws
    exact covered_of_path (adj_innCB e) (mem_erase.2 ⟨by simp, hc⟩) (adj_orig_innC e).symm
      (mem_erase.2 ⟨by simp, hv⟩)
  have hwS : w ∉ S := fun h => hw (mem_erase.2 ⟨hws, h⟩)
  by_cases h1 : (gadget H).Adj w (inn e .b)
  · rcases adj_innB_iff.1 h1 with rfl | rfl
    · exact covered_of_path (adj_orig_innA e) (mem_erase.2 ⟨by simp, hu⟩) (adj_orig_pend _)
        (mem_erase.2 ⟨by simp, hpu⟩)
    · exact absurd hc hwS
  by_cases h2 : ∃ u, (gadget H).Adj w u ∧ (gadget H).Adj u (inn e .b)
  · obtain ⟨u, hwu, hu'⟩ := h2
    rcases adj_innB_iff.1 hu' with rfl | rfl
    · rcases adj_innA_iff.1 hwu with rfl | rfl
      · exact absurd hu hwS
      · exact absurd rfl hws
    · rcases adj_innC_iff.1 hwu with rfl | rfl
      · exact absurd hv hwS
      · exact absurd rfl hws
  push Not at h2
  exact covered_erase_of_far h1 h2 (hS.1.covered (by norm_num) hwS)

/-- Positions `a` and `c`. -/
theorem not_inner_ac (hS : IsMinimalStarForming (gadget H) 2 S) (e : Edge H)
    (hu : orig e.1.1 ∈ S) (hpu : pend e.1.1 ∈ S) (hv : orig e.1.2 ∈ S)
    (ha : inn e .a ∈ S) (hc : inn e .c ∈ S) : False := by
  by_cases hb : inn e .b ∈ S
  · exact not_all_inner hS e ha hb hc
  refine not_minimal_of_covered hS ha fun w hw => ?_
  by_cases hws : w = inn e .a
  · subst hws
    exact covered_of_path (adj_orig_innA e) (mem_erase.2 ⟨by simp, hu⟩) (adj_orig_pend _)
      (mem_erase.2 ⟨by simp, hpu⟩)
  have hwS : w ∉ S := fun h => hw (mem_erase.2 ⟨hws, h⟩)
  by_cases h1 : (gadget H).Adj w (inn e .a)
  · rcases adj_innA_iff.1 h1 with rfl | rfl
    · exact absurd hu hwS
    · exact covered_of_path (adj_innCB e) (mem_erase.2 ⟨by simp, hc⟩) (adj_orig_innC e).symm
        (mem_erase.2 ⟨by simp, hv⟩)
  by_cases h2 : ∃ u, (gadget H).Adj w u ∧ (gadget H).Adj u (inn e .a)
  · obtain ⟨u, hwu, hu'⟩ := h2
    rcases adj_innA_iff.1 hu' with rfl | rfl
    · exact covered_of_path hwu.symm (mem_erase.2 ⟨by simp, hu⟩) (adj_orig_pend _)
        (mem_erase.2 ⟨by simp, hpu⟩)
    · rcases adj_innB_iff.1 hwu with rfl | rfl
      · exact absurd rfl hws
      · exact absurd hc hwS
  push Not at h2
  exact covered_erase_of_far h1 h2 (hS.1.covered (by norm_num) hwS)

/-! ### Counting -/

theorem ite_three_le_two (A B C : Prop) [Decidable A] [Decidable B] [Decidable C]
    (h : ¬ (A ∧ B ∧ C)) :
    (if A then 1 else 0) + (if B then 1 else 0) + (if C then 1 else 0) ≤ 2 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp_all

theorem ite_three_le_one (A B C : Prop) [Decidable A] [Decidable B] [Decidable C]
    (h1 : ¬ (A ∧ B)) (h2 : ¬ (B ∧ C)) (h3 : ¬ (A ∧ C)) :
    (if A then 1 else 0) + (if B then 1 else 0) + (if C then 1 else 0) ≤ 1 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp_all

theorem sum_pos (f : Pos → ℕ) : ∑ p, f p = f .a + f .b + f .c := by
  change ∑ p ∈ ({.a, .b, .c} : Finset Pos), f p = _
  rw [sum_insert (by simp), sum_insert (by simp), sum_singleton]
  ring

variable [Fintype W]

/-- Counting a set of vertices of the gadget vertex by vertex and edge by edge. -/
theorem card_pt (T : Finset (Pt H)) :
    #T = ∑ v : W, ((if orig v ∈ T then 1 else 0) + (if pend v ∈ T then 1 else 0)) +
      ∑ e : Edge H, ((if inn e .a ∈ T then 1 else 0) + (if inn e .b ∈ T then 1 else 0) +
        (if inn e .c ∈ T then 1 else 0)) := by
  have h : #T = ∑ x : Pt H, if x ∈ T then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext x
    simp
  rw [h, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, sum_add_distrib]
  simp only [sum_pos]
  ring

/-- The vertices `v` of `H` with `v` and its pendant vertex both in `S`. -/
def Y2 (S : Finset (Pt H)) : Finset W := univ.filter fun v => orig v ∈ S ∧ pend v ∈ S

/-- The edges of `H` with both ends in `Y`. -/
def inside (Y : Finset W) : Finset (Edge H) := univ.filter fun e => e.1.1 ∈ Y ∧ e.1.2 ∈ Y

theorem mem_Y2 {v : W} : v ∈ Y2 S ↔ orig v ∈ S ∧ pend v ∈ S := by simp [Y2]

theorem mem_inside {Y : Finset W} {e : Edge H} : e ∈ inside Y ↔ e.1.1 ∈ Y ∧ e.1.2 ∈ Y := by
  simp [inside]

/-- The counting step: every vertex of `H` contributes at most `1 + [v ∈ Y₂]`, every edge at most
`2`, and at most `1` when both ends are in `Y₂`. -/
theorem card_add_card_inside_le (hS : IsMinimalStarForming (gadget H) 2 S) :
    #S + #(inside (H := H) (Y2 S)) ≤ Fintype.card W + #(Y2 S) + 2 * Fintype.card (Edge H) := by
  have hY : #(Y2 S) = ∑ v : W, if orig v ∈ S ∧ pend v ∈ S then 1 else 0 := by
    rw [Y2, card_filter]
  have hI : #(inside (H := H) (Y2 S)) = ∑ e : Edge H, if e ∈ inside (Y2 S) then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext e
    simp
  rw [card_pt S, hY, hI]
  have hv : ∑ v : W, ((if orig v ∈ S then 1 else 0) + (if pend v ∈ S then 1 else 0)) ≤
      Fintype.card W + ∑ v : W, (if orig v ∈ S ∧ pend v ∈ S then 1 else 0) := by
    calc _ ≤ ∑ v : W, (1 + if orig v ∈ S ∧ pend v ∈ S then 1 else 0) := by
          refine sum_le_sum fun v _ => ?_
          by_cases ho : orig v ∈ S <;> by_cases hp : pend v ∈ S <;> simp [ho, hp]
      _ = _ := by rw [sum_add_distrib]; simp
  have he : ∑ e : Edge H, ((if inn e .a ∈ S then 1 else 0) + (if inn e .b ∈ S then 1 else 0) +
        (if inn e .c ∈ S then 1 else 0)) + ∑ e : Edge H, (if e ∈ inside (Y2 S) then 1 else 0) ≤
      2 * Fintype.card (Edge H) := by
    rw [← sum_add_distrib]
    calc _ ≤ ∑ _e : Edge H, 2 := by
          refine sum_le_sum fun e _ => ?_
          by_cases hin : e ∈ inside (Y2 S)
          · simp only [hin, ↓reduceIte]
            obtain ⟨h1, h2⟩ := mem_inside.1 hin
            obtain ⟨hu, hpu⟩ := mem_Y2.1 h1
            obtain ⟨hv, hpv⟩ := mem_Y2.1 h2
            have := ite_three_le_one (inn e .a ∈ S) (inn e .b ∈ S) (inn e .c ∈ S)
              (fun h => not_inner_ab hS e hu hv hpv h.1 h.2)
              (fun h => not_inner_bc hS e hu hpu hv h.1 h.2)
              (fun h => not_inner_ac hS e hu hpu hv h.1 h.2)
            omega
          · simp only [hin, ↓reduceIte]
            have := ite_three_le_two (inn e .a ∈ S) (inn e .b ∈ S) (inn e .c ∈ S)
              (fun h => not_all_inner hS e h.1 h.2.1 h.2.2)
            omega
      _ = _ := by simp [mul_comm]
  omega

/-- An edge of `H` through two given adjacent vertices. -/
def edgeOf {a b : W} (h : H.Adj a b) : Edge H :=
  if hab : a < b then ⟨(a, b), hab, h⟩
  else ⟨(b, a), lt_of_le_of_ne (not_lt.1 hab) h.ne.symm, h.symm⟩

theorem edgeOf_ends {a b : W} (h : H.Adj a b) :
    ((edgeOf h).1.1 = a ∧ (edgeOf h).1.2 = b) ∨ ((edgeOf h).1.1 = b ∧ (edgeOf h).1.2 = a) := by
  unfold edgeOf
  split_ifs <;> simp

/-- Deleting one end of every edge inside `Y` leaves an independent set:
`|Y| ≤ |E(H[Y])| + α(H)`. -/
theorem card_le_inside_add_betaK (Y : Finset W) :
    #Y ≤ #(inside (H := H) Y) + betaK H 1 := by
  induction Y using Finset.strongInduction with
  | H Y ih =>
    by_cases hE : ∃ a ∈ Y, ∃ b ∈ Y, H.Adj a b
    · obtain ⟨a, ha, b, hb, hab⟩ := hE
      have hrec := ih (Y.erase a) (erase_ssubset ha)
      have hnot : edgeOf hab ∉ inside (H := H) (Y.erase a) := by
        intro hm
        obtain ⟨h1, h2⟩ := mem_inside.1 hm
        rcases edgeOf_ends hab with ⟨e1, -⟩ | ⟨-, e2⟩
        · rw [e1] at h1; simp at h1
        · rw [e2] at h2; simp at h2
      have hsub : insert (edgeOf hab) (inside (H := H) (Y.erase a)) ⊆ inside Y := by
        intro e he
        rcases mem_insert.1 he with rfl | he
        · rcases edgeOf_ends hab with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
            exact mem_inside.2 (by rw [e1, e2]; tauto)
        · obtain ⟨h1, h2⟩ := mem_inside.1 he
          exact mem_inside.2 ⟨mem_of_mem_erase h1, mem_of_mem_erase h2⟩
      have hc := card_le_card hsub
      rw [card_insert_of_notMem hnot] at hc
      have := card_erase_of_mem ha
      have : 0 < #Y := card_pos.2 ⟨a, ha⟩
      omega
    · push Not at hE
      have hK : KIndep H 1 Y := by
        intro v hv
        have : Y.filter (H.Adj v) = ∅ := by
          ext w
          simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
          exact hE v hv w
        rw [this]
        simp
      have := card_le_betaK hK
      omega

/-- The upper bound: every minimal 2-star-forming set of the gadget has at most
`|V(H)| + 2 |E(H)| + α(H)` vertices. -/
theorem card_le_of_minimal (hS : IsMinimalStarForming (gadget H) 2 S) :
    #S ≤ Fintype.card W + 2 * Fintype.card (Edge H) + betaK H 1 := by
  have h1 := card_add_card_inside_le hS
  have h2 := card_le_inside_add_betaK (H := H) (Y2 S)
  omega

/-! ### The lower bound -/

/-- The 2-independent set of the gadget built from an independent set `I` of `H`: all pendant
vertices, the vertices of `I`, the middle of every edge, and next to the middle the inner vertex
on the side away from `I`. -/
def inJ (I : Finset W) : Pt H → Bool
  | .inl v => decide (v ∈ I)
  | .inr (.inl _) => true
  | .inr (.inr (e, .a)) => decide (e.1.1 ∉ I)
  | .inr (.inr (_, .b)) => true
  | .inr (.inr (e, .c)) => decide (e.1.1 ∈ I)

/-- The set `J(I)`. -/
def J (I : Finset W) : Finset (Pt H) := univ.filter fun x => inJ I x = true

theorem kIndep_J {I : Finset W} (hI : KIndep H 1 I) : KIndep (gadget H) 2 (J I) := by
  have hI' : ∀ u ∈ I, ∀ w ∈ I, ¬ H.Adj u w := by
    intro u hu w hw huw
    have := hI u hu
    have : w ∈ I.filter (H.Adj u) := mem_filter.2 ⟨hw, huw⟩
    have := card_pos.2 ⟨w, this⟩
    omega
  have key : ∀ x y : Pt H, (∀ w, w ∈ J I → (gadget H).Adj x w → w = y) →
      #((J I).filter ((gadget H).Adj x)) < 2 := by
    intro x y h
    have : (J I).filter ((gadget H).Adj x) ⊆ {y} := by
      intro w hw
      obtain ⟨hwJ, hxw⟩ := mem_filter.1 hw
      exact mem_singleton.2 (h w hwJ hxw)
    have := (card_le_card this).trans (card_singleton y).le
    omega
  intro x hx
  have hxJ : inJ I x = true := (mem_filter.1 hx).2
  rcases x with v | v | ⟨e, p⟩
  · -- a vertex of `I`: its only neighbour in `J` is its pendant vertex
    have hvI : v ∈ I := by simpa [inJ] using hxJ
    refine key _ (pend v) fun w hwJ hxw => ?_
    have hw : inJ I w = true := (mem_filter.1 hwJ).2
    rcases adj_orig_iff.1 hxw.symm with h | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
    · exact h
    · simp [inJ, hf, hvI] at hw
    · exfalso
      have h1 : f.1.1 ∈ I := by simpa [inJ] using hw
      exact hI' _ h1 v hvI (hf ▸ f.2.2)
  · refine key _ (orig v) fun w _ hxw => adj_pend_iff.1 hxw.symm
  · cases p with
    | a =>
      have h1 : e.1.1 ∉ I := by simpa [inJ] using hxJ
      refine key _ (inn e .b) fun w hwJ hxw => ?_
      have hw : inJ I w = true := (mem_filter.1 hwJ).2
      rcases adj_innA_iff.1 hxw.symm with rfl | h
      · simp [inJ, h1] at hw
      · exact h
    | b =>
      by_cases h1 : e.1.1 ∈ I
      · refine key _ (inn e .c) fun w hwJ hxw => ?_
        have hw : inJ I w = true := (mem_filter.1 hwJ).2
        rcases adj_innB_iff.1 hxw.symm with rfl | h
        · simp [inJ, h1] at hw
        · exact h
      · refine key _ (inn e .a) fun w hwJ hxw => ?_
        have hw : inJ I w = true := (mem_filter.1 hwJ).2
        rcases adj_innB_iff.1 hxw.symm with h | rfl
        · exact h
        · simp [inJ, h1] at hw
    | c =>
      have h1 : e.1.1 ∈ I := by simpa [inJ] using hxJ
      refine key _ (inn e .b) fun w hwJ hxw => ?_
      have hw : inJ I w = true := (mem_filter.1 hwJ).2
      rcases adj_innC_iff.1 hxw.symm with rfl | h
      · exfalso
        have h2 : e.1.2 ∈ I := by simpa [inJ] using hw
        exact hI' _ h1 _ h2 e.2.2
      · exact h

theorem card_J (I : Finset W) :
    #(J (H := H) I) = Fintype.card W + 2 * Fintype.card (Edge H) + #I := by
  rw [card_pt]
  have hI : #I = ∑ v : W, if v ∈ I then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext v
    simp
  have hv : ∀ v : W, ((if orig v ∈ J (H := H) I then 1 else 0) +
      (if pend v ∈ J (H := H) I then 1 else 0)) = (if v ∈ I then 1 else 0) + 1 := by
    intro v
    by_cases h : v ∈ I <;> simp [J, inJ, h]
  have he : ∀ e : Edge H, (if inn e .a ∈ J I then 1 else 0) + (if inn e .b ∈ J I then 1 else 0) +
      (if inn e .c ∈ J I then 1 else 0) = 2 := by
    intro e
    by_cases h : e.1.1 ∈ I <;> simp [J, inJ, h]
  rw [sum_congr rfl fun v _ => hv v, sum_congr rfl fun e _ => he e, sum_add_distrib, ← hI]
  simp only [sum_const, card_univ, smul_eq_mul, mul_one]
  ring

/-! ### The theorem -/

/-- `β₁` is the independence number. -/
theorem betaK_one_eq_indepNum : betaK H 1 = H.indepNum := by
  apply le_antisymm
  · refine betaK_le_iff.2 fun I hI => ?_
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    intro u hu w hw _ huw
    have := hI u hu
    have : w ∈ I.filter (H.Adj u) := mem_filter.2 ⟨hw, huw⟩
    have := card_pos.2 ⟨w, this⟩
    omega
  · obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
    rw [← hs.card_eq]
    apply card_le_betaK
    intro v hv
    have : s.filter (H.Adj v) = ∅ := by
      ext w
      simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hw hvw
      exact hs.isIndepSet hv hw hvw.ne hvw
    change #(s.filter (H.Adj v)) < 1
    rw [this]
    simp

/-- The pairs `u < v` with `u ~ v` are exactly the edges of `H`. -/
theorem card_edge : Fintype.card (Edge H) = #H.edgeFinset := by
  rw [← card_univ]
  refine card_bij (fun p _ => s(p.1.1, p.1.2)) (fun p _ => by simpa using p.2.2) ?_ ?_
  · intro p _ q _ hpq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subtype.ext (Prod.ext h1 h2)
    · exfalso
      have hp := p.2.1
      have hq := q.2.1
      rw [h1, h2] at hp
      exact lt_asymm hq hp
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : H.Adj a b := by simpa using he
      rcases lt_or_gt_of_ne hab.ne with h | h
      · exact ⟨⟨(a, b), h, hab⟩, mem_univ _, rfl⟩
      · exact ⟨⟨(b, a), h, hab.symm⟩, mem_univ _, Sym2.eq_swap⟩

/-- **Main theorem.** For every graph `H` the gadget is bipartite and
`SF₂(gadget H) = β₂(gadget H) = |V(H)| + 2 |E(H)| + α(H)`. -/
theorem sfK_gadget :
    (gadget H).Colorable 2 ∧
      sfK (gadget H) 2 = Fintype.card W + 2 * #H.edgeFinset + H.indepNum ∧
      betaK (gadget H) 2 = Fintype.card W + 2 * #H.edgeFinset + H.indepNum := by
  rw [← card_edge, ← betaK_one_eq_indepNum]
  have hup : sfK (gadget H) 2 ≤ Fintype.card W + 2 * Fintype.card (Edge H) + betaK H 1 :=
    sfK_le_iff.2 fun S hS => card_le_of_minimal hS
  have hlow : Fintype.card W + 2 * Fintype.card (Edge H) + betaK H 1 ≤ betaK (gadget H) 2 := by
    have : betaK H 1 ≤ betaK (gadget H) 2 - (Fintype.card W + 2 * Fintype.card (Edge H)) := by
      refine betaK_le_iff.2 fun I hI => ?_
      have := card_le_betaK (kIndep_J hI)
      rw [card_J] at this
      omega
    have h0 : Fintype.card W + 2 * Fintype.card (Edge H) ≤ betaK (gadget H) 2 := by
      have := card_le_betaK (kIndep_J (H := H) (I := ∅) (by intro v hv; simp at hv))
      rw [card_J] at this
      omega
    omega
  have hmid := betaK_le_sfK (G := gadget H) (k := 2) (by norm_num)
  exact ⟨gadget_colorable, by omega, by omega⟩

end StarForming
