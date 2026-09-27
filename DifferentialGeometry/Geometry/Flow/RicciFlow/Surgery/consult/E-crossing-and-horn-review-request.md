# Fifth review request (E): the crossing leaf, the deep-horn neck improvement, and the strong interface

Target: `liao9yuan/differential-geometry-dev`, branch `codex/pc-target-c-psf` @ 1dfbc801f. Read:
`…/Surgery/Topology/CanonicalNeighborhoodContinuationLeaves.lean` (`CapWindowPoint` with the margin
`‖x‖ < Dcap + 1`, `CapWindowContinuation`, `CrossingContinuation`, the assembly),
`…/Surgery/Topology/CrossingRoom.lean` (room lemmas; `OPUS_FILL_LOG_X1.md` for the missing step),
`…/Surgery/Topology/HornNeckImprovement.lean` (`exists_strongNeck_threshold_of_minimizing_arms`,
`exists_uniform_orientedWitness_of_parabolically_noncollapsed`),
`…/Surgery/Topology/NeckRegionAxialArms.lean`, `…/Surgery/Topology/NeckChainAxialArms.lean`
(necklace hypotheses, `metricDistance_ge_of_separating_slices`, accuracy `1/3000`),
`…/Surgery/Topology/ProspectiveNeckSurvivalVariableThreshold.lean` (`exists_threshold_uniform_selected_neck_append_backward`),
`…/Perelman/CanonicalNeighborhood/SpatialCanonicalWitness.lean` (+ `…Projection.lean`),
`…/Surgery/Topology/SpatialCanonicalContinuation.lean`,
`…/Surgery/Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean` (strong C, strong S, assemblies),
`…/Surgery/Topology/CapWindowStandardComparison.lean` (bridge to the collaborator's comparison),
`…/Surgery/Topology/DeepContinuation.lean` (proved leaf), `…/Surgery/consult/C-debit-step-review-digest.md`.

## Questions (Chinese, ~1500 characters, verdict table, counterexamples clause by clause)

1. Deep-horn neck improvement: the theorem takes two minimizing arms from `x` of normalized
   length in `[D, 2D]` at comparison angle `≥ θ₀ > 0` (any positive angle; `D` chosen after
   `θ₀, κ, ρ, Phi`), plus pinching and parabolic κ-noncollapsing on the window `[t − θ/R, t]`, and
   concludes a strong `δ`-neck at `x`. Is the angle hypothesis with arbitrary `θ₀` sound (the tree's
   cylinder-limit lemma takes it; the Bryant-tip objection fails because comparison angles at
   arm length `≫ 1` decay unless the solution splits a line): confirm or refute. Is the necklace
   formulation of "deep in a horn" (`NeckChainAxialArms.lean`: consecutive necks at fixed accuracy
   `1/3000`, steps along the axis, central spheres separating, scalar comparability
   `R(c i₀) ≤ 4R(c k)`) something the debit-step factory's ε-horn can supply, and is the fixed
   accuracy `1/3000` compatible with the factory's coarse accuracy `ε̄`? What is the correct
   Perelman II 4.3 / KL 71 hypothesis in our vocabulary?
2. Crossing room lemma: from `¬ CapWindowPoint` (with margin) and the derivative and gradient
   clauses, the worker proved that `y` itself has a backward trace and that a ball whose points all
   have traces is parabolically controlled at radius `c/√R`; the missing step is "a point of
   `B(y, c/√R)` without a trace at event `j` puts `y` in the cap window of `j`" (needs metric
   distortion along traces across events and a ball sandwich for the cap window). Is the intended
   dichotomy (unscathed at radius `c/√R` ∨ in a cap window at cap-age `≤ θcap`) correct with
   `Dcap ≥ transitionEnd + C₁c`, `θcap ≥ C₂c²`? Also: the cap scalar lower bound
   `exists_presented_cap_scalar_lower_bound_of_canonical_window` needs accuracy `≤ ε₀(D)` with
   `D = p.modelRadius`, but `εcap` in `CrossingContinuation` is chosen before `p₀.modelRadius`
   (only bounded below by `Dcap`): is that a genuine quantifier defect, and how should the class be
   constrained (fix `modelRadius` as a function of `Dcap`, or make the cap scalar bound uniform in `D`)?
3. Crossing blow-up plan: from the room lemma, iterate to windows of depth `θ/R` and radius `A/√R`
   for every `A` by the same dichotomy (each failure puts the base in a cap window), build the
   pointed limit on the survivor flow (the collaborator's radius-`R/4` local limits and the
   cone-exclusion without necks), exhaust radii and depths, and transport a witness back. What is
   the minimal set of lemmas (statements) for a complete ancient κ-solution limit on incomplete
   sources through events; where exactly do young points (age `< τmin`, no strong neck) enter, and
   does the induction predicate need spatial neck structure there (cf. review 3, F6)?
4. Strong interface (`CanonicalNeighborhoodsThroughSurgeryStrong`, `UniformDebitSurgeryStepStrong`):
   order `∀ B, ∃ Λ, ∀ Ctime, ∃ ε, …` for S; the spatial age-free clause with `SpatialCanonicalWitness`;
   `κ` via `TerminalNoncollapsedBefore` on `G`; `a₀` from `exists_pos_fixedHamiltonIveyRegion_for_identified_histories`;
   the old C only as a projection restricted to `recenterConstant ≤ Λ`. Sound? Any circularity in the
   assembly (`hstep B → Λ; hcn B (1/22) Λ → Ctime; hstep Ctime → ε; hcn B ε Λ → rest`)? Is the fourth
   leaf `SpatialCanonicalContinuation` (inputs C3's constants and `qcan`, outputs `C1s C2s qs ≥ qcan`)
   provable at young points on round/positive components and fresh cap tips (producers:
   `LocalInitialSpatialCap`, `RoundCanonicalWitness`)?
5. Cap-window bridge: the class gaps kept explicit (`qcan ≤ Cbirth · scale`, `1 ≤ a₀ · scale`,
   `Gk.DerivativeBoundBefore C qcan t` up to the current time) — which belong in the class
   (`InCutoffClass`/records), and is the nested continuation inside the cap window (derivative
   bound at the standard solution's constant `≤ Ctime₀`) the right way to break the circularity?
6. Variable-threshold neck survival: `∃ ηstar mstar Λ, ∀ q₀, …, Λ · max q₀ 1 ≤ O.scale → …` — the
   proof takes a threshold sequence with `q₀ₙ/scaleₙ → 0`; is that the correct decoupling (review 3,
   F3), and is anything lost for the factory (the `Contract/PreparedHistoryCutoff` wrapper still
   uses the old order)?
7. Anything false or vacuous in the files above, with a configuration.
