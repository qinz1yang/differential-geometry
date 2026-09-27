# OPUS fill log XP3 — Crossing bricks W1′ (depth-schedule local limits) and the `openClosed (−T*) 0` gluing (2026-09-26)

Worktree `D:\differential-geometry-pc3`, base e68bf6466. Read-only compiles only (`lean` with the lake
LEAN_PATH, `LEAN_NUM_THREADS=2`, `-DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`);
uncommitted imports built to scratch oleans under `scratchpad\xp3\olean` (script `xp3/cc.sh`: the
dependency is compiled in place with `-R` the worktree root and `-o` into the scratch olean tree, which is
prepended to LEAN_PATH, so no module renaming). Read at start: `OPUS_FILL_LOG_XP2.md`, `DESIGN_X4D.md`
§1–§2, `DESIGN_CROSSING_ASSEMBLY.md` §2.6 (W1) and §2.7 (X4 steps 1–2), H14/H15 digests.

## Brick G — gluing on `openClosed (−T) 0`

- File `Geometry/Flow/RicciFlow/Solution/OpenClosedGluing.lean` (new), namespace
  `DifferentialGeometry.PDE.RicciFlow`, same variable block as `AncientGluing.lean`.
- Statement (general schedule, recorded before the proof):
  ```lean
  theorem exists_openClosed_solution_of_compatible_open_cover {T : ℝ} (hT : 0 < T)
      (U : ℕ → Opens M) (hU : Monotone U) (hcover : ∀ x : M, ∃ n, x ∈ U n)
      (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcmono : Monotone c) (hcT : ∀ s < T, ∃ n, s < c n)
      (g : ∀ n, ℝ → SmoothRiemannianMetric I (U n))
      (hg : ∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := I) (M := U n)
        (RealTimeInterval.closed (-c n) 0 (neg_nonpos.mpr (hc n)))))
      (hcompat : ∀ n m, ∀ t ∈ Icc (-c n) 0, t ∈ Icc (-c m) 0 →
        (g n t).restrictOpenOfSubset (inf_le_left : U n ⊓ U m ≤ U n) =
          (g m t).restrictOpenOfSubset (inf_le_right : U n ⊓ U m ≤ U m)) :
      ∃ G : ℝ → SmoothRiemannianMetric I M,
        IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := M)
          (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) ∧
        ∀ n t, t ∈ Icc (-c n) 0 → (G t).restrictOpen (U n) = g n t
  ```
  Corollary `exists_openClosed_solution_of_compatible_open_cover_of_depth_schedule`: the same with
  `c n` spelled `((n+1:ℕ):ℝ)/((n+2:ℕ):ℝ) * (T * ((n+1:ℕ):ℝ) / ((n+2:ℕ):ℝ))` (W1′'s inner window at
  `τ n = T(n+1)/(n+2)`, i.e. `T((n+1)/(n+2))² ↑ T`), monotonicity and exhaustion proved inside.
- Differences from `AncientGluing.lean:17`: windows `[-c n, 0]` instead of `[-(n+1), 0]`; the metric family
  is glued over the time set `⋃ n, Icc (-c n) 0` (so the restriction identity holds on every whole window
  even if some `c n ≥ T`); solution property by `isSolutionOn_of_local_time_restrictions` with, at each
  `t ∈ (-T, 0]`, the neighbourhood `Ioi (-c n)` (`-c n < t`) and the open cover `U (n + k)`.
- Proof: done. Compile: exit 0, no output. Axioms (both): `[propext, Classical.choice, Quot.sound]`.
  115 lines.

## Brick W1′ — depth-schedule local limits (in progress)

Plan (two new files):
1. `Geometry/Flow/RicciFlow/Compactness/Limits/LocalPointedFlowLimit.lean` (generic, no Surgery): the
   depth-schedule analogue of `AncientPointedFlowLimit.lean:59/292` WITHOUT gluing — outer windows
   `[-τ k, 0]`, inner windows `[-c k, 0]` (`0 < c k < τ k`), per-`k` local limit flows `Gloc k` on
   `V k = B_P((k+1)/2)`, `Gloc k 0 = P.metric|V k`, solution on `closed (-c k) 0`, compatibility on common
   times, convergence of the pulled-back approximants on `Icc (-c k) 0` (all `p`, compact `K`).
   Theorems `exists_local_flow_limits_of_pointed_convergence_of_local_solutions` and
   `exists_pointed_local_flow_limits_of_local_solutions`. Uses the two private codomain-restriction
   lemmas of `AncientPointedFlowLimit` by `open private` (no copy). STATUS: proved, compile exit 0, no
   output.
2. `Surgery/Topology/TracedRegionLocalLimitDepthSchedule.lean`: W1′ itself (statement below).

### W1′ statement (elaborated with `sorry`, 12:xx; recorded before the proof)
`ObservedHistory.exists_local_pointed_flow_limits_with_time_lipschitz_survivor_maps_of_depth_schedule`
in `Surgery/Topology/TracedRegionLocalLimitDepthSchedule.lean`. It is TimeControl:781's statement with
DCA §2.6's substitutions, writing `β k := ((k+1:ℕ):ℝ)/((k+2:ℕ):ℝ)`:
- new binders `(τ : ℕ → ℝ) (hτ : ∀ k, 0 < τ k)`; `htraced` is per depth:
  `∀ k, ∃ K, 0 ≤ K ∧ ∀ᶠ n, (H n).isTracedRegion (t n) (y n) (((k+3:ℕ):ℝ)/√(R n)) (τ k / R n) (K * R n)`.
  DEVIATION from DCA:404 (radius `k+4`): radius `k+3` suffices (the survivor domain `W k n` IS the
  rescaled traced ball of radius `k+3`, as in TimeControl) — a weaker hypothesis.
- `hsliver`, `hnc` (`v < t₀ n`), `hPhi`, `hpinch`, `κ, ρ` exactly as :781.
- per-`k` block: solution window `closed (-τ k) 0`; current-slab identity and survivor identities on
  `Icc (-τ k) 0`; survivor start `a = t n − τ k / R n`; approximant κ-test for `σ ∈ Icc (-(β k * τ k)) 0`,
  `t n + σ/R n < t₀ n`, with `Icc (σ − r²) σ ⊆ Icc (-τ k) 0`.
- Lipschitz and `e²` clauses on `Icc (-(β k * τ k)) 0`; scalar bound on `Icc (-τ k) 0`; radii `k+3`,
  `k+2`, `(k+1)/2` unchanged.
- limit: per-`k` `Gloc k : ℝ → SmoothRiemannianMetric ThreeModel (V k)`, `Gloc k 0 = P.metric|V k`,
  solution on `closed (-(β k * τ k)) 0`, convergence on `Icc (-(β k * τ k)) 0` (DCA:423–435 verbatim with
  `t ↦ s`). ADDITION: the compatibility clause
  `∀ k l, ∀ s ∈ Icc (-(β k*τ k)) 0, s ∈ Icc (-(β l*τ l)) 0 → (Gloc k s)|V k ⊓ V l = (Gloc l s)|V k ⊓ V l`
  (free from the construction; it is exactly brick G's `hcompat`, so X4 need not re-derive it from
  `hφF`).
- NO κ clause on the limit (DESIGN_X4D §1.7 / H14 (d)); the windowed per-`k` limit clause is NOT
  included (no consumer; not cheap — TimeControl's limit κ goes through the ancient-limit lemma
  `parabolicallyKappaNoncollapsedBelowScale_of_local_pinching_flow_limit_of_time_lt`, which is stated
  for `infiniteClosed`).

Proof route (planned):
- generic limit part: `exists_pointed_local_flow_limits_of_local_solutions` with `c k := β k * τ k`.
- Shi margin (H14 (d)): TimeControl's jets come from Shi on the terminal ball (`[-θ/2, 0]` only); at
  `β k > 1/2` this is not enough. New private lemma: Shi (`shi_curvDerivNorm_on_terminal_ball`) with the
  terminal time moved to the slice `s ∈ [-β τ, 0]` and window `[s − (1−β)τ, s]` (fixed length, so one
  constant), compactness of the time-`s` ball from the `e²` metric comparison (distance at `s` ≥ e⁻¹ ×
  distance at 0, `riemannianEDistOf_le_of_metric_lower_on_ball`). The same jets feed the Lipschitz lemma
  `exists_metricDerivNorm_terminal_reference_time_lipschitz_of_curvature_jets` (T = βτ, T₂ = τ).
- `e²` clause: Ricci lower bound from pinching with `δ = 1/(2βτ)` (TimeControl:689 with `k+1 ↦ βτ`).
- volume at time 0 (Cheeger–Gromov non-collapsing input): TimeControl's private
  `volume_ball_ge_of_isScaledSurvivorData_at_zero` is hard-wired to depth `2(k+2) ≥ 1`; copied as
  `volume_ball_ge_of_isScaledSurvivorData_at_depth` with a general depth `θ` and hypothesis `a² ≤ θ`
  (DEFERRED MERGE: TimeControl's lemma is the instance `θ = 2(k+2)`); radius `a` also shrunk below `√τ`.

### W1′ proof: DONE (compile exit 0, no output, before the κ delta)
- Private lemmas in the W1′ file: `volume_ball_ge_of_isScaledSurvivorData_at_depth` (copy of TimeControl's
  `…_at_zero`, depth `θ` general with `a² ≤ θ`; DEFERRED MERGE into TimeControl, whose lemma is the case
  `θ = 2(k+2)`), `exists_curvDerivNorm_bound_of_inner_window` (Shi at the slice `s` with window
  `[s − (θ − c), s]`, compactness of the time-`s` ball of radius `r₀e⁻¹` from the `e²` comparison).
  TimeControl/Data/TracedRegionAncientLimit privates used by `open private` (no copy).

### Lead delta (mid-lane): a κ clause at time 0 for X4a
Lead: X4a (`WindowScalarBound.lean`, XP4) needs `∃ κ, 0 < κ ∧ MetricNoncollapsed P κ (Ioc 0 1)`; W1′
must export a κ clause at time 0 ("B6c-κ form restricted to σ = 0 / windowed per-k at σ = 0"); no κ at
negative times required.
- FINDING (to the lead): `MetricNoncollapsed P κ (Ioc 0 1)` is STATIC (curvature bound only on the
  time-0 ball), while everything the tree transfers to limits (TimeControl:950, NC0, B6c-κ) is
  PARABOLIC (curvature bound on `[t − r², t] × B_t`). Static does not follow from parabolic without
  backward curvature control. The conversion needs, on the glued limit, `Rm ≥ 0` (X4 step 2: then
  `g(s) ≥ g(0)` for `s < 0`, so `B_s(x, r) ⊆ B_0(x, r)`, and `|Rm| ≤ R`) and the derivative clause
  (X4 step 5: `|∂_s R| ≤ Ctime R²`, so `R(y, s) ≤ 2R(y, 0)` for `|s| ≤ 1/(2 Ctime R(y,0))`): a time-0
  ball with `|Rm| ≤ r⁻²` has a parabolic sub-ball of radius `r' = r / C(Ctime)` that is Rm-controlled,
  hence `vol B_0(x, r) ≥ vol B_0(x, r') ≥ (κ/250) r'³ = κ' r³`. That step belongs to X4 (it owns steps
  2 and 5), not to W1′ (whose hypotheses carry no derivative clause). W1′ supplies the parabolic input.
- W1′ delivery for this delta: a parabolic κ theorem for the GLUED limit on `openClosed (−T) 0`
  (the B6c-κ form of TimeControl:950 with the window `(−T, 0]`): every parabolically Rm-controlled
  ball, time 0 included, of radius `≤ ρ` is `κ/250`-noncollapsed. Local copy of
  `isKappaNoncollapsed_of_local_flow_limit_of_time_lt` (`AncientPointedFlowLimitTerminalNoncollapsing.lean:31`,
  ancient → `openClosed`, windows `[-c k, 0] ⊂ [-τ k, 0]`, comparison on `closed a 0` with
  `a = −(c k + min (τ k) T)/2`), time 0 through NC0 `parabolicallyKappaNoncollapsedBelowScale_of_forall_time_lt`.
  Hypotheses: completeness of every slice `G t`, `t ∈ Ioc (−T) 0` (X4 step 3 supplies it), `c k < T`.
- κ file `Surgery/Topology/LocalPointedFlowLimitNoncollapsing.lean` (new, 267 lines, namespace
  `…Perelman.CanonicalNeighborhood.FiniteHorn`): `isKappaNoncollapsed_of_local_flow_limit_on_openClosed_of_time_lt`
  and `parabolicallyKappaNoncollapsedBelowScale_of_local_flow_limit_on_openClosed` (conclusion
  `ParabolicallyKappaNoncollapsedBelowScale (G on openClosed (−T) 0) (κ/250) ρ`, every `ρ > 0`).
  Privates of `AncientLimitCanonicalWitness` by `open private` (no copy). Compile exit 0, no output.
- W1′ ADDITIONS for X4 (cheap, already proved inside): the pinching clause in `h`-form on `Icc (-τ k) 0`
  (input of the window version of `AncientPointedFlowLimitCurvature.lean:26`, X4 step 2) and the
  limit-ready κ-test `∀ k, ∀ σ ∈ Icc (-(β k τ k)) 0, σ < 0 → ∀ᶠ n, …` with `radii n = ρ√(R n)` (the
  `hnc` input of the κ file; `hsliver` already consumed).

## Final state
| Brick | File (new) | Lines | Compile (std linter set) | Axioms |
|---|---|---|---|---|
| G gluing | `Solution/OpenClosedGluing.lean` | 115 | exit 0, no output | propext, Classical.choice, Quot.sound |
| W1′ generic limit | `Compactness/Limits/LocalPointedFlowLimit.lean` | 310 | exit 0, no output | same |
| W1′ | `Surgery/Topology/TracedRegionLocalLimitDepthSchedule.lean` | 742 | exit 0, no output (scratch chain) | same |
| κ on `(−T, 0]` | `Surgery/Topology/LocalPointedFlowLimitNoncollapsing.lean` | 267 | exit 0, no output | same |
Axioms printed from a scratch module importing all four (7 public theorems), then deleted. No committed
file touched; not registered in `DifferentialGeometry.lean`. Import order for the acceptance build:
OpenClosedGluing, LocalPointedFlowLimit → TracedRegionLocalLimitDepthSchedule; LocalPointedFlowLimitNoncollapsing
(independent). Deferred merge: `volume_ball_ge_of_isScaledSurvivorData_at_depth` (W1′ file, private)
generalizes TimeControl's private `…_at_zero`.

## Interface for X4 (steps 1, κ) — `τ k := Tstar * ((k+1:ℕ):ℝ) / ((k+2:ℕ):ℝ)`, `c k := β k * τ k`
1. W1′ on the subsequence history `H ∘ σ` with this `τ` (`hτ k` by positivity; `htraced k` from
   `DepthExtendable … (τ k)` at `A = k+3`, `τ k < Tstar`). Obtain `W, h, hblock, hlip, hscal, hlow,
   hpinchW, hncW, f, hf, P, F, hCd, hPc, hconn, hballF, V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, hG,
   hGcompat, ψ, hψ, hconv`.
2. `V` monotone and covering from `hV` (+ `hconn`), 10 lines as in
   `AncientPointedFlowLimitTerminalNoncollapsing.lean:218–235`.
3. Glue: `exists_openClosed_solution_of_compatible_open_cover_of_depth_schedule hT V hVmono hVcover Gloc hG
   hGcompat` (window spelling matches W1′'s after β-reduction) gives `G` on `openClosed (−Tstar) 0` with
   `(G s).restrictOpen (V k) = Gloc k s` on `Icc (-c k) 0`; `G 0 = P.metric` from `hG0` + cover
   (`SmoothRiemannianMetric.ext_inner`, as `AncientPointedFlowLimit.lean:269`); rewrite `hconv` into the
   `G`-form with the restriction identity.
4. κ at time 0 (and all times) after completeness (step 3 of DCA X4):
   `parabolicallyKappaNoncollapsedBelowScale_of_local_flow_limit_on_openClosed hT τ c hc hcτ hcT hcmono
   hcex hsol hκ (radii := fun n => ρ * √(R n)) hradii hncW hf F hVmono hVcover hVF φ hφ hφF hG hcomplete
   hψ hconvG ρ' hρ'` (`hsol` = first conjunct pair of `hblock`; `hcT`, `hcmono`, `hcex` are the
   depth-schedule facts proved inside the gluing corollary — restate them or copy its 20 lines).
5. X4a's `MetricNoncollapsed P κ' (Ioc 0 1)` from 4 + `Rm ≥ 0` + the derivative clause (see the finding
   above); this step is X4's.
