# OPUS fill log XP4 — brick X4a of DESIGN_CROSSING_ASSEMBLY.md (2026-09-26)

Worktree `D:\differential-geometry-pc3`, base e68bf6466. Read-only compiles only; scratch under
`scratchpad\xp4`. Binding corrections: H14 (b) (anchors only at fixed `(A*, D*)`; the distance lemma
needs the whole `[a, 0]` bound first), DESIGN_X4D G5/G8.

## Start
- Read: DCA §2.7 (X4a statement, route steps 1–5), DESIGN_X4D G5/G8/§2, H14, H15, XP2 log.
- Template found in tree: `exists_uniform_backward_scalar_bound_on_finite_horizon`
  (`Perelman/CanonicalNeighborhood/BackwardScalarBound.lean:22`) is the TerminalLimit/BackwardExtension
  analogue of X4a (compact case: scalar minimum principle + diameter; noncompact case: far field
  `exists_uniform_scalar_bound_outside_terminal_ball` + one escape anchor + bounded curvature at
  bounded distance). X4a = this proof on an abstract flow on `openClosed (-T*) 0`, plus a derivative
  bootstrap because the abstract flow has no `compact_time_bound` field.
- Plan: file `Perelman/CanonicalNeighborhood/WindowScalarBound.lean` (new), namespace
  `…Surgery.Topology` (as DCA §2 and the Σ block's unqualified `windowFarAccuracy`).

## Statement check (sorry probe, in-tree file, 45 s)
- DCA §2.7 X4a statement elaborated verbatim, plus the one added binder below; far-field lemma and
  the generalized derivative-step lemma elaborated with `sorry`. Only `declaration uses sorry`.

## DEVIATION: one added hypothesis (κ at time 0)
- Added, after the `Rm ≥ 0` binder: `(∃ κ : ℝ, 0 < κ ∧ MetricNoncollapsed P κ (Ioc 0 1))`.
- Reason: the far field (DCA step 3) is the port of `exists_uniform_scalar_bound_outside_terminal_ball`
  (`BackwardScalarExterior.lean:89`). Its contradiction is: a far neck's central sphere `S` at time `s`
  has tiny `d_s`-, hence `d_0`-diameter, so `S ⊆ B_0(v, r)`, and `B_0(v, r)ᶜ` is path connected, so
  `p` and the far point `z` (from `exists_far_spatialNeck_unbounded_separated_component_of_nonnegative`)
  lie in one component of `Sᶜ`. The uniform path-connected ball complement is
  `exists_uniform_pathConnected_ball_complement_of_metricNoncollapsed` (`Geometry/Neck/BallComplement.lean:27`),
  which needs `MetricNoncollapsed P κ (Ioc 0 1)` and a curvature bound at time 0; the original takes it
  from `TerminalLimit.noncollapse`. X4a as written has no κ, so the port has no substitute. Without κ the
  step would need a tiny far separating 2-sphere to be excluded by 3-manifold topology
  (irreducibility of collapsed `T²`-fibred ends / Cheeger–Gromoll), which the tree does not have.
  No counterexample to κ-free X4a was found; the added binder is the nearest provable statement.
- It is used only in the noncompact case. Compact `P.M` needs no κ and no far field.
- X4 supply: `MetricNoncollapsed P κ (Ioc 0 1)` for the time-0 limit `P` (all scales ≤ 1 in the rescaled
  picture, since the approximants are κ-noncollapsed below `ρ√Rₙ → ∞`); cf. `noncollapse_passes_to_limit`
  (`BlowupConvergence.lean:132`) or W1's windowed κ clause at `σ = 0`. This is a NEW input for X4 (DESIGN_X4D
  §1 said no consumer in X4's chain reads a limit κ; X4a now does, at time 0 only).

## Far-field port: witness route, not the comparison-angle route
- The original's neck selection `exists_far_spatialNeck_of_backwardExtension` (compactness of normalized
  sequences, comparison angle) is NOT ported. With the witness hypothesis the neck is read off directly:
  at `y` with `R_s(y)` large, alternative `neck` gives the neck at `y`; `cap` gives, by
  `capTubeHasNeckChart ε`, a neck at a tube point `v` with `R_s(v) ≥ R_s(y)/C2` and
  `d_s(y, v) < 2·radius ≤ 2C1/√R_s(y) ≤ 1`; `positive`/`round` are whole components, excluded by
  noncompactness. The rest is the original's separation argument at `v`.
- Public lemma `exists_scalar_bound_far_of_spatialCanonicalWitness` (single metric `g` compared with
  `P.metric`: `d_0 ≤ d_g ≤ d_0 + A`), ~150 lines instead of the budgeted 700–1200.

## Proof of X4a (H14 (b), G5, G8 respected)
- `Q₀`: B6d per-slice (`AncientPointedFlowLimitBoundedCurvature.lean:110`) at `τ = 0`; `Q = max Q₀ 0`.
- Distance: `ricciFlow_additive_distance_bound_of_terminal_scalar` (`Estimates/Distance/TerminalScalar.lean:173`,
  finite-left-endpoint Harnack inside, G5) on `[s, 0]`, called only under a hypothesis that `[s, 0]`
  already carries a scalar bound (turned into `|Rm|² ≤ 100²K²` by `Rm ≥ 0`); constant
  `c₀ = (20/3)√(2T*Q)√T*`.
- Anchor stage (`Cs`, fixed before any window endpoint; hRP called ONLY at these fixed pairs, G8):
  - compact: diameter `2R` at time 0, anchor = the time-`s` minimum point (`exists_scalar_le_at_earlier_time_of_compact`,
    `R_s(z) ≤ R_0(p) ≤ Q`), hRP at `(Q, 2R + c₀ + 1)`;
  - noncompact: far field at `A = c₀` gives `(Rf, Cf)`; ONE escape point `z` with `Rf < d_0(p, z)` chosen at
    time 0; hRP at `(Cf, d_0(z, p) + Rf + c₀ + 1)`; points with `d_0(p, x) > Rf` by the far field.
  - `Cs = max Q …`; statement: for `s ∈ Ioc`, a bound on `[s, 0]` implies `R_s ≤ Cs`.
- Bootstrap: `B = max Cs (max q 1)`, `δ = 1/(2(Ctime+1)B)`; induction on `n`: `R ≤ Cs` on
  `[max s₀ (−nδ), 0]`. Step: derivative lemma on `[a', a]` gives `2B`, so `[a', 0]` carries a bound, then
  the anchor stage gives `Cs`. Conclusion `C = Cs`.
- The derivative lemma needed the right endpoint `0 ∉ Ioo`: new
  `le_two_mul_of_abs_deriv_le_mul_sq_of_continuousOn_of_right_le` (continuity on `Icc`, differentiability
  and the bound on `Ioo`). DEFERRED MERGE: it generalizes `le_two_mul_of_abs_deriv_le_mul_sq_of_right_le`
  (`AncientPointedFlowLimitBoundedCurvature.lean:19`, committed; not modified); the old one becomes a corollary.
- `windowFarAccuracy.{u} : ℝ := (X4a).choose` and `windowFarAccuracy_pos` at the end of the file. The def
  carries the universe `u` of the flows (the existential is universe-polymorphic); the Σ block should write
  `hεfar : 2 * ε ≤ windowFarAccuracy.{u}`.

## Result
- File `Perelman/CanonicalNeighborhood/WindowScalarBound.lean` (new), 516 lines. Imports committed modules only
  (`AncientPointedFlowLimitBoundedCurvature`, `BackwardScalarExterior`, `Estimates/Distance/TerminalScalar`,
  `Preservation/ScalarMinimum`).
- Compile (`lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`, 52 s): exit 0, no output.
- Axioms (scratch copy with `#print axioms`, deleted): X4a, far field, derivative lemma all
  `[propext, Classical.choice, Quot.sound]`.
- Not registered in `DifferentialGeometry.lean` (lead's job). No committed file touched.

## Hypothesis list X4 must discharge (for the glued limit flow `G` on `openClosed (−T*) 0`, `P` its time-0 slice)
1. `[ConnectedSpace P.M]`; `0 < T*`.
2. `IsSolutionOn ({ base.metric := G } : SolutionOn … (RealTimeInterval.openClosed (-Tstar) 0 0 ⟨by linarith, le_rfl⟩))`
   (same interval term as `OpenClosedGluing.lean:36` up to the proof of membership).
3. `G 0 = P.metric`.
4. `∀ τ ∈ Ioc (-T*) 0, RiemannianMetricComplete (G τ)`.
5. `∀ τ ∈ Ioc (-T*) 0, ∀ x, metricAlgebraicCurvatureTensorAt (G τ) x ∈ algebraicCurvatureOperatorNonnegativeCone`.
6. NEW: `∃ κ, 0 < κ ∧ MetricNoncollapsed P κ (Ioc 0 1)`.
7. `ε ≤ windowFarAccuracy.{u}`.
8. Witnesses: `∀ τ ∈ Ioc (-T*) 0, ∀ x, q < R_τ(x) → ∃ W : SpatialCanonicalWitness (G τ) ε C1 C2 x, W.capTubeHasNeckChart ε`
   (time 0 included).
9. Derivative: `∀ τ ∈ Ioo (-T*) 0, ∀ x, q < R_τ(x) → |derivWithin (fun v => R_v(x)) (Iic τ) τ| ≤ Ctime·R_τ(x)²`.
10. hRP: `∀ A Dd, ∃ C, ∀ τ ∈ Ioo (-T*) 0, ∀ z x, R_τ(z) ≤ A → riemannianEDistOf (G τ) z x < ofReal Dd → R_τ(x) ≤ C`.
Conclusion: `∃ C, ∀ τ ∈ Ioc (-T*) 0, ∀ x, R_τ(x) ≤ C`.
