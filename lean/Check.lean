import StarForming

/-! Prints the axioms of the main theorems; `scripts/audit_axioms.py` checks that only `propext`,
`Classical.choice` and `Quot.sound` occur. -/

-- the counterexamples to Conjecture 4.1 (every k ≥ 3)
#print axioms StarForming.betaK_lt_sfK
#print axioms StarForming.betaK_family
#print axioms StarForming.sf_gt_beta
#print axioms StarForming.main
#print axioms StarForming.kIndep_card_le
#print axioms StarForming.isMinimalStarForming_S0
#print axioms StarForming.colorable_two
#print axioms StarForming.card_W
-- chain graphs (Conjecture 6.4, every k ≥ 2)
#print axioms StarForming.sfK_eq_betaK_of_isChain
#print axioms StarForming.exists_kIndep_card_eq
#print axioms StarForming.eq_of_high
#print axioms StarForming.deg_add_two_le
#print axioms StarForming.IsChain.nested
-- general facts
#print axioms StarForming.betaK_le_sfK
#print axioms StarForming.isMinimalStarForming_of_maximal
#print axioms StarForming.exists_kIndep_of_unique_high
#print axioms StarForming.starAt_iff_covered
#print axioms StarForming.isMinimalStarForming_of_erase
