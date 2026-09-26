# Lane H log: Perelman II 4.3 neck improvement

- 2026-09-25: statement sent to lead; revised to minimizing-arms hypothesis (angle θ₀, lengths √R·ell ∈ [D,2D], D after ρ Phi); lead accepted.
- Route: contradiction; `exists_windowed_tolerances_for_original_arm_cylinder_limit` (cylinder limit) + `StrongNeck.eventually_transport_of_windowed_models`; windowed witnesses from a copy of the proof of `exists_uniform_canonical_threshold_of_parabolically_noncollapsed` exporting `OrientedWitness`.
- File: `Surgery/Topology/HornNeckImprovement.lean`. First compile blocked: `WindowedCanonicalBoundsLimit.olean` missing (lead build); retrying after 5 min.
- Compiled clean (`lake env lean`, no diagnostics). Axioms of both new theorems and of the two tree lemmas used: propext, Classical.choice, Quot.sound. Names unique. Missing factory-side lemma: necks within D/√R ⇒ two minimizing arms of lengths in [D,2D]/√R at comparison angle ≥ θ₀ (see report). Not linted (lead).
