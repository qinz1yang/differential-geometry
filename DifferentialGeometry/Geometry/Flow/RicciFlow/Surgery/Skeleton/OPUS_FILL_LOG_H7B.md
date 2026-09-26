# Lane H7b log: history reduced Jacobian monotone (DESIGN_22 §4, row H7b)

- 2026-09-26 start. Target `Surgery/Topology/HistoryLGeometry/JacobianMonotone.lean` (+ more files in
  `HistoryLGeometry/` if needed). Read: AGENTS.md, DESIGN_22 §0–§5/§7, H6 and H7a logs,
  `Jacobian.lean`, `JacobianUnconditional.lean`, `Index.lean` (chain API),
  `Jacobian/GramIndexBound.lean`, `Jacobian/Basic.lean:855` (`lExpLog_deriv_le`),
  `Jacobian/Monotonicity.lean` (`redLength_ray_K`), `Hamilton/Basic.lean` (`lK`, `lK_ray_energy`),
  `Index/Trace.lean:216`, `Hamilton/TraceIntegral.lean:678`.
- Compile route: reuse scratch `scratchpad\h3a` (modules `H3aPre.*`). Added `H3aPre.IndexChain` and
  `H3aPre.JacobianUnconditional` from the repo files (only imports renamed): 41 s and 32 s, clean.
- Plan (after reading the suppliers). The derivative inequality needs history Jacobi fields and
  Perelman's adapted frames on ONE chain whose last window carries the H7a family at `v`. H6's
  `exists_lWindowChain` chains carry no families, so its windows cannot host the Jacobi fields.
  New structure `LFamilyChain` = `LWindowChain` along `historyLCurve Z₀` + per-piece H3b'
  families (`V k`, `K k`, `β k`) with the representation of `historyLCurve Z` for `Z ∈ V k`, and
  the base piece given by `lRegularizedCurve` (for non-conjugacy near 0). Fields on it: Jacobi
  fields `J i k s = ρ_k(s) • ∂_Z β_k(Z₀, s) e_i` (bump ρ_k for global smoothness), adapted frames
  by downward induction (generalized `exists_lAdaptedField` to `Icc a' b`). Trace identity is
  proved piecewise with `D(s) = s·Lag/4 − s³R` telescoping across nodes (no history `K` needed):
  `Σ_l I(Y_l,Y_l) = (D(v) − A/4)/v² + 3/(2v)`, which with G5 gives `(log ℓJ)' ≤ 0`.
- Progress 1 (~1 h): scratch modules `H3aPre.JMChain` (structure), `H3aPre.JMAlong` (smooth
  sections along curves: add/smul/zero), `H3aPre.JMAdapted` (`exists_lAdaptedField_Icc`),
  `H3aPre.JMFields` (bumps, Jacobi fields: global smoothness, Jacobi property, `J 0 0 = 0`) compile.
  Scratch-only substitution: `DifferentialGeometry.Bundle.PartialMfderiv.Regularity` is not in the
  E: build, so it is compiled as `H3aPre.PMRegularity` (identical copy); the repo files import
  the real module.
- Progress 2 (~2 h): `JMFields` complete — Jacobi fields glued in value and covariant derivative
  (G2 naturality `mfderiv_covDerivAlong_of_isLocalDiffeomorph` + H7a `historyLJacobiField_eq_mfderiv`),
  adapted frames on the whole chain by downward induction, bumped to global C^∞ (`exists_adaptedFrame`).
  `JMTrace`: orthonormality along the chain, pointwise trace identity, `hasDerivAt_energy`
  (`lTrace_deriv` + `lLagMul_deriv`), per-piece integral identity and the telescoped
  `sum_historyLIndex`: `Σ_l I(Y_l,Y_l) = (E(v) − A/4)/v² + 3v/(2v²)`, `E = s·Lag/4 − s³R`. All compile.
- Progress 3 (~3 h): `JMGram` compiles: `half_trace_le` — for any `LFamilyChain` on `[0, v]` with an
  adapted frame, given linear independence of the chain Jacobi fields at `v` and index
  nonnegativity on glued C⁸ fields vanishing at both ends,
  `½ tr(G⁻¹G')(v²) ≤ Lag(v)/(4v²) − A/(4v³) + 3/(2v²)` for the last window's family Gram matrix
  (exactly the bound making `(log ℓJ)' ≤ 0`). Lesson: rewriting `map_smul` inside `g.inner` with big
  arguments times out (TangentSpace smul diamond); proved a small generic `lGramDeriv_eq_of_eq`
  instead. Next: chain existence with families, non-conjugacy, minimizer transfer, assembly.
- Progress 4 (~4.5 h): `JMClosure` (`historyLCurve_eq_of_family`: a family representation on open
  stage pieces extends to the closed pieces, via the curve's own windows) and `JMExists`
  (`exists_base_family`: base-window family `lRegularizedCurve (L Z)` representing
  `historyLCurve Z` near `s = 0` by H3a uniqueness; `famPiece_of_window`: interior pieces) compile.
  Design change: the action `A(v')` near `v` is handled by H6/Window's split-at-parameter +
  window piece identity (no chain surgery); chains are needed only for the Gram bound and for
  non-conjugacy. Remaining: base cover, chain assembly, non-conjugacy, minimizer transfer,
  local derivative, seam/endpoint limits, real-analysis lemma, headline.
- Progress 5 (~5 h): `JMChainExists.exists_lFamilyChain` compiles: for `Z₀` in H3b's open domain at
  `w`, any non-seam interior `v < w` and prescribed non-seam breakpoint `w' < v`, there is an
  `LFamilyChain` on `[0, v]` with `w'` a breakpoint (base cover + interior family pieces +
  Lebesgue partition, following H6's `exists_lWindowChain`).
- Progress 6 (~6 h): `JMConj` compiles — non-conjugacy at interior breakpoints
  (`linearIndependent_historyLJacobiField`: H6 `eqOn_zero_of_conjugate_of_minimizer` + base-piece
  contradiction via `covDerivAlong_lRegularizedJacobiField_ne_zero`). `JMAction.historyLAction_split`
  compiles: `A(v') = A(v) + lRegularizedAction W.S T γ v v'` for any family window covering `[v, v']`
  (H4 action identity + H5 truncation + Window split/`regularizedExtendedAction_eq_coe`).
  09:29: a `lake build` in pc3 (not mine) is rewriting E: oleans; scratch compiles blocked until it
  finishes (CompactVolumeEquivalence.olean missing).
- Progress 7 (~7 h): E: build repaired by the lead's acceptance build (09:40); scratch compiles resumed.
  `JMLocal`: `historyStage`, `historyReducedJacobianAlong` (the v ↦ ℓJ function with the active
  stage), minimizer facts for `historyLCurve`, `exists_family_chain_linearIndependent` (chain at `v`
  + non-conjugacy transferred from a longer chain with `v` as breakpoint). `JMDeriv`: derivative
  set-up (H7a `hasDerivAt_historyLJacobianDensity` on the chain's last window, `hpos` from linear
  independence, FTC for the action) compiles; the final algebra is next.
- Progress 8 (~8 h): `JMDeriv.exists_hasDerivAt_historyReducedJacobianAlong` PROVED (non-seam
  interior `v`: `HasDerivAt ℓJ d v` with `d ≤ 0`). `JMSeam.exists_tendsto_seam_historyReducedJacobianAlong`
  PROVED (seam `v`: equal one-sided limits, via H3b' seam family + H7a seam limits + action split).
  `JMReal.le_of_hasDerivAt_nonpos_off_finite` PROVED (real analysis). Remaining: left continuity at
  the endpoint `v₂` (end family) and the headline.
- Progress 9 (~9 h): `JMEnd.continuousWithinAt_historyReducedJacobianAlong` PROVED (left continuity at
  the endpoint `v₂` via H3b's private end family `hasPrefixFamily_end`, G2
  `paramDensity_comp_of_inner_eq`, action split). All 16 scratch modules sorry-free. Next: headline.
  Note: the shared E: build is being rewritten by acceptance builds; scratch compiles retried
  (`h3a/jmtry.sh`).

## Progress 10 (2026-09-26)

- Scratch `JMMono` compiles: `historyReducedJacobianAlong_le`, `historyReducedJacobian_antitoneOn`
  (AntitoneOn on `{v | 0 < v ∧ v ≤ v₂ ∧ T - v ^ 2 ∉ range H.time}`), and the pairwise
  `historyReducedJacobian_le_of_le_of_mem_Ioo` (both parameters interior to their stages).
  Renamed from `historyReducedJacobian_le_of_le` to avoid clashing with the H7b+ statement in
  DESIGN_C2_ASSEMBLY §3 (seam values, closed-start `v₂`, seam base), which this lane does not cover.
- Cleanup pass: file-local helpers made private, abbreviations renamed (`FamilyPiece`,
  `familyDeriv`), lines reflowed to ≤ 100, unused binders removed; full chain recompiling.

## Progress 11 (finish, 2026-09-26, finishing worker)

- Previous worker killed mid-cleanup; 17 untracked files in `Surgery/Topology/HistoryLGeometry/`.
  Compile route: scratch modules `H7f.*` (imports of the 17 files and of the unbuilt committed
  `Bundle/PartialMfderiv/Regularity` renamed; everything else from the shared E: build), scratchpad
  `h7f/`, script `h7f/sc.sh`, full Mathlib standard linter set.
- Import order: AntitoneOffFinite (Mathlib only); FamilyChain → FamilyChainSections →
  AdaptedFieldIcc → FamilyChainJacobi → FamilyChainTrace → FamilyChainGram → FamilyChainClosure →
  FamilyChainCover → FamilyChainExists → FamilyChainConjugate → ActionSplit → JacobianAlong →
  JacobianDerivative → JacobianSeam (+ AntitoneOffFinite) → JacobianEndpoint → JacobianMonotone.
- Static checks: no `sorry`/`axiom`/`nolint`/`set_option` other than the tree-wide
  `autoImplicit false`, no comments or docstrings; only import lines exceed 100 characters (as in
  the committed siblings, which also carry no copyright header).
- Compile (scratch modules, `-Dweak.linter.mathlibStandardSet=true`, linter activity confirmed
  by a probe): all 17 files plus the scratch copy of `PartialMfderiv/Regularity` compile with
  zero errors, zero warnings, zero info. No edits were needed; the in-tree files are unchanged
  from the killed worker's cleanup pass. Lines: AntitoneOffFinite 90, FamilyChain 47,
  FamilyChainSections 82, AdaptedFieldIcc 239, FamilyChainJacobi 461, FamilyChainTrace 371,
  FamilyChainGram 354, FamilyChainClosure 93, FamilyChainCover 348, FamilyChainExists 165,
  FamilyChainConjugate 267, ActionSplit 156, JacobianAlong 213, JacobianDerivative 238,
  JacobianSeam 200, JacobianEndpoint 223, JacobianMonotone 96 (total 3643).
- Axioms (scratch probe, removed): `historyReducedJacobian_antitoneOn`,
  `historyReducedJacobian_le_of_le_of_mem_Ioo`, `historyReducedJacobianAlong_le` all
  `[propext, Classical.choice, Quot.sound]`.
- Statement vs DESIGN_22 §4 (`AntitoneOn … (Ioc 0 v₂)` with `first v` the active stage):
  the function is `historyReducedJacobianAlong Z₂` (ℓJ with the active stage `historyStage T v`,
  equal to `historyReducedJacobian` at non-seam `v` by `historyReducedJacobianAlong_eq`); the set
  is `{v | 0 < v ∧ v ≤ v₂ ∧ T - v ^ 2 ∉ range H.time}` (seam parameters excluded) and `v₂` is
  interior to stage `first` (`hv₂k`). No `hT` hypothesis on the base time is needed. Seam values,
  closed-start `v₂` and seam base are H7b+ (DESIGN_C2_ASSEMBLY §2(d), §6), not this lane; the
  pairwise form is named `historyReducedJacobian_le_of_le_of_mem_Ioo` (both parameters interior
  to their stages) so that `historyReducedJacobian_le_of_le` stays free for H7b+.
- Short-name clashes (66 public names checked library-wide): `energy`
  (`ObservedHistory.LFamilyChain.energy` vs CurveShortening `energy`, different namespaces) and
  `regular_of_mem_piece` (`LFamilyChain.regular_of_mem_piece`, statement ∃ open `Ioo`
  neighbourhood, vs `LWindowChain.regular_of_mem_piece` in `Index.lean`, statement on `uIcc`;
  full names distinct, dot notation on an `LFamilyChain` picks the former). No full-name clash.
- Deferred merges: `inner_congr_point'` (FamilyChainTrace) is a public copy of the private
  `inner_congr_point` in `Index.lean`; the files reach committed private lemmas through
  `open private … from` (IndexChain, ExponentialSmooth, Truncation,
  `Perelman/LGeometry/AdaptedField/Existence`); `exists_lAdaptedField_Icc`
  generalizes the committed `exists_lAdaptedField` to `Icc a' b` and could replace it.
