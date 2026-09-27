# OPUS fill log XP2 — bricks P1, X4d-Σ, X4 of DESIGN_X4D.md (2026-09-26)

Worktree `D:\differential-geometry-pc3`, base e68bf6466. Read-only compiles only; scratch under
`scratchpad\xp2`. Binding corrections: `consult/H15-crossing-x4d-sigma-review-digest.md`.
Suppliers already delivered by XP1 (log read at start): P3 `StandardCloseComparison.lean`, P2
`CapWindowBallCapture.lean`, P1s `CrossingPersistenceInputs.lean`, X4-ev `SurvivorTraceScalar.lean`.

## P1
- Start: statement drafted per §1.4 + H15 (b): full `:20` binder list, per history, `Θ = θcap = 1/2`
  local, `C` = the caller's derivative constant (Ctime), threshold `qcan`, radius `D₂`, `N := 2`,
  `ε = η := ε'`.
- File: `Surgery/Topology/CapWindowSliceComparison.lean` (new), theorem
  `RetainedCoreHistory.exists_capWindow_embedding_standard_close (C : ℝ≥0)`.
- DEVIATION from §1.4 (H15 (b) form): stated per history with :20's FULL binder list instead of
  inside Σ (`∀ᶠ n`): `IsCanonicalCutoffRecordFamily`, `δbound ≤ δ₀`, `R ≤ modelRadius`,
  `m₀ ≤ modelOrder`, `modelAccuracy ≤ ζ₀`, `0 < qcan`, Hamilton–Ivey + `-3/a₀` floor at
  `initialMetric 0`, birth-scale bounds `∀ i b, qcan ≤ Cbirth·λ ∧ 1 ≤ a₀·λ`, arbitrary stage `k`
  with slab `Gk`, initial-metric match, `EventSlabsDerivative C qcan k`, `time k < t < s`,
  `Gk.DerivativeBoundBefore C qcan t`, then the FULL `CapWindowPoint records k w t Dw (1/2)`
  (its `BackwardPointTrace` + birth-point equation + age + radius are the existential's fields).
  Conclusion: `Ξ : standardCapWindow D₂ → (H.stage k).Carrier` (= `(·).val.val ∘ Ξ₂₀`, the
  composite with the incoming map), local diffeo, injective, `Ξ z₀ = w`, `‖z₀‖ < Dw+1`, and
  `∃ i b Q τw, τw ∈ [0,1/2] ∧ ∀ u, ∀ m ≤ 2, metricDerivNorm m (pull (λ_{i b}·g_t) Ξ) (Q τw) cap u < ε`
  with `λ = ((records i).static b).neck.scale` itself (the Σ form's `(n+1)qcan ≤ lam` is then `hscale`).
  Reasons: stated inside Σ it would trip `unusedSectionVars` (XP1's finding); per-`k` form covers
  terminal AND event slabs in one statement (no `prefixAt` detour needed for P1 itself).
  Σ-form supply: P1s gives every binder eventually (`R ≤ D n ≤ modelRadius` etc.).
- Proof: `:20` at `Θ = θcap = 1/2`, `D := D₂`, `ε = η := ε`, `N := 2`; `capWindow_flow_metric_eq`
  (`CapWindowContinuationAssembly.lean`) at `T = λ(t − time j.succ)`; composite local diffeo and
  injectivity from `CapWindowFlowPushforward.lean:72, 83`.
- Compile: exit 0, no output (64 s). Axioms: `[propext, Classical.choice, Quot.sound]`. 87 lines.

## X4d-Σ (in progress)
- Compile method: scratch modules `XP2S.*` (uncommitted imports copied to `scratchpad\xp2\src`, imports
  rewritten, `lean -R src -o olean/...`, LEAN_PATH = scratch oleans + `lake env`), script `xp2/cc.sh`.
- File `Surgery/Topology/BoundedCurvatureAtDistanceAnchor.lean` (new).
- Private generic core `scalar_le_of_rebase_capWindow_dichotomy` (any compact 3-manifold slice, any
  predicate `CWP`): rebase point `w` with `R(w) = max(Rₙ, R(z))` from
  `exists_minimizing_segment_to_level_of_isCompact_sublevel` (NOT the chain lemma: only the point is
  needed), `d(w,x) < 2D/√Rₙ`; case split on the full predicate; ¬CWP ⇒ B3e at ball radius
  `A_B ≥ 2D√A'`; CWP ⇒ P1 data + P3 (`λ ≤ 2L ≤ 2A'Rₙ`, `cap ≤ Lc² g̃`, `R_g̃ ≤ Cup`) + P2 with
  `r > 2·D·Lc·√(2A')` (Lc fixed first), `D₂ = D₁ + 1 + r`. Conclusion `R(x) ≤ A'(Q_B + 2Cup + 1)Rₙ`.
  Compiled clean.
- Private `eventually_slab_scalar_le_at_normalized_distance` (Σ hypotheses explicit): `∀ A ≥ 1, D > 0,
  ∃ C Λ, ∀ᶠ n`, terminal slices `time last < τ < t₀ n` and event-slab slices
  `time j.castSucc < τ < time j.succ`, both with `Λ ≤ Rₙ·τ`. B3e terminal constants used for BOTH slabs
  (event slab through `prefixAt`, replicating B3e-event's 10-line proof, so ONE `Dcap = D₁`); threshold
  `q = qs n` for B3e (`qs ≤ Cs·qcan ≤ Cs·Rₙ ≤ Cs·R(w)`), `qcan` for P1; P1s (XP1's revised signature)
  for all P1 gates; `n₀` depends on `(A, D)` only. Compiled clean.
- Private `scalar_le_of_right_shift` (any `IncomingSlab`, slice `v ∈ Ico a b`): BS1
  `exists_forall_Icc_scalar_riemannNorm_metric_close` at `t₀ := v` (Ico, so the slab START is allowed)
  with `ζ = min 1 (1/D)`; one interior slice `τ = v + min(δ,e)/2` at FIXED `n`; `R_τ(z) ≤ R_v(z) + ζ`,
  `d_τ ≤ √(1+ζ)·d_v ≤ (D+1)/√Rₙ`, bound at `τ` with margins `(A'+1, D+1)`, back by `+ζ ≤ Rₙ`. This is
  H15's event-time step (right neighbourhood at fixed n, margins, no σ′-quantifier swap); it is used for
  EVERY slice (event time or not), so no case split on event times is needed.
- Headline `eventually_scalar_le_at_normalized_distance_of_anchor`: conclusion VERBATIM §1.5 (the `let K`,
  `∀ A Dd, 0 < A → 0 < Dd → ∃ C, 1 ≤ C ∧ ∀ σ < 0, ∀ᶠ n, ∀ v, v = t n + σ/Rₙ → ∀ z x …`).
  DEVIATION (binders only, as XP1's P1s): the Σ hypotheses are explicit binders, the 15 used ones
  verbatim (`hε hεcone hκ hphi hH hG hrec hq hpar hscale hpinch hslabs hbefore hsliver hbad`); unused Σ
  fields `hεfar hθ hCs hCt hθcap` dropped (inside the Σ `include` block they trip `unusedSectionVars`).
  Probe (deleted): the verbatim §1.5 statement inside the verbatim Σ block (`DCA:258–307`,
  `windowFarAccuracy` → variable `εfar`) closes by
  `eventually_scalar_le_at_normalized_distance_of_anchor hε hεcone hκ hphi hH hG hrec hq hpar hscale
  hpinch hslabs hbefore hsliver hbad` (only the expected unusedSectionVars note of the probe itself).
- Constants: `A' = max A 1 + 1`, `D' = Dd + 1`; slab lemma at `(A', D')` gives `C₁`; `C = max 1 (C₁+1)`.
  Per σ: F3 (`tendsto_scalar_mul_time_atTop_of_inCutoffClass`, `InitialWindowScalarBound.lean`) gives
  `Λ ≤ Rₙ·v`; `hsliver` gives `Rₙ(tₙ − t₀ₙ) ≤ 1/(n+1) < −σ`, so `v < t₀ n`. Stage identification:
  `stageMetric_extendHorizon_last` (last) and `stageMetric_castSucc_apply` (events), `activeStage_mem`.
- Compile (scratch chain, standard linter set): exit 0, no output. Axioms `[propext, Classical.choice,
  Quot.sound]`.
- File: 498 lines (core 130, slab lemma 190, right shift 50, headline 130). Imports (uncommitted, for the
  acceptance order): P1 `CapWindowSliceComparison` (XP2), P1s `CrossingPersistenceInputs`, P2
  `CapWindowBallCapture`, P3 `StandardCloseComparison` (XP1), X1k `RetainedCoreHistoryExtendAt` (XA2),
  X0/F3 `InitialWindowScalarBound` (XA1). No committed file touched; no private lemma copied; no
  deferred merge.

## X4 — NOT started (blocked; reported to lead)
- X4 (DCA §2.7 steps 1–8 with DESIGN_X4D §2 step-6/8 deltas) needs, besides X4d-Σ (done) and X4-ev (XP1):
  W1 (600–1000 lines, depth-schedule copy of TimeControl:345/781, unassigned; XA4's X3a needs the same
  theorem), the `openClosed (−T*) 0` gluing generalization of `AncientGluing.lean:17`, and X4a
  (`exists_uniform_scalar_bound_on_openClosed_window_of_spatialCanonicalWitness` + far-field port,
  1.2–2.1k lines, unassigned, no file anywhere in the tree). X4's step 7 IS X4a; without it X4 would be a
  conditional delivery. Stopped here for a dispatch decision rather than open a 3–5k-line private lane.

## Summary
| Brick | File | Lines | Status | Axioms |
|---|---|---|---|---|
| P1 | `Surgery/Topology/CapWindowSliceComparison.lean` | 87 | clean (in-tree `lake env lean`) | propext, Classical.choice, Quot.sound |
| X4d-Σ | `Surgery/Topology/BoundedCurvatureAtDistanceAnchor.lean` | 498 | clean (scratch chain) | propext, Classical.choice, Quot.sound |
| X4 | — | — | blocked on X4a + W1 (+ gluing) | — |
Not registered in `DifferentialGeometry.lean` (lead's job). Shared-olean caveat: only a fresh build certifies.

## X4 (resumed on lead instruction, 2026-09-26) — BLOCKED by an X4a interface gap (reported)
Read XP3 (W1′, gluing, κ on `(−T,0]`) and XP4 (X4a) logs and the supplier statements.
- FINDING: X4a (`WindowScalarBound.lean:260`) takes, on EVERY limit slice `τ ∈ Ioc (−T*) 0`,
  `∃ W : SpatialCanonicalWitness (G τ) ε C1 C2 x, W.capTubeHasNeckChart ε` above `q`. Nothing in the tree
  produces `SpatialCanonicalWitness` on a LIMIT slice:
  - B6 (`TracedRegionAncientLimitNeckAlternatives.lean:21`) and B9 (`AncientPointedFlowLimitShiftedTransfer.lean:354`)
    transfer only the three NECK ALTERNATIVES (neck at x / neck at nearby w / `∀ y, R(y) ≤ C·R(x)`); DCA §2.7
    step 4 cites exactly these for X4a's witness input, so DCA step 4 does not type-check against X4a.
  - The only witness-level transport, `SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance`
    (`SpatialCanonicalWitnessUniformTransport.lean:757`), needs `W.HasMargins m` on the source witness; no
    history/Σ witness carries margins (`HasMargins` is produced only for standard-solution witnesses), and it
    also needs a gradient bound for the LIMIT metric at the image point.
- Why the neck-alternative form cannot simply replace the witnesses in XP4's proof: slice-0 `Q₀` is fine
  (`exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives`, Transfer:440), but XP4's far
  field (noncompact case) excludes the `positive/round` witness alternatives by `W.domain.compact` +
  noncompactness. The transferred third alternative `∀ y, R_s(y) ≤ C·R_s(x)` has lost that compactness, and a
  noncompact complete `Rm ≥ 0` slice (e.g. a cylinder) satisfies it, so the far point is not controlled
  (the escape-point anchor is circular in that case).
- Fix options for the lead (none is a local change inside X4):
  (F1) window-B9 variant whose third alternative is `CompactSpace P.M` (from the stage witness's
      `inside_ball`: whole component ⊆ ball(x, 2C1/√R)); needs a lower distance comparison between the limit
      slice and the stage slice through `f j ∘ φ` (paths leaving the survivor image) — not in the tree;
      then an X4a′ with neck-alternative hypotheses (XP4's proof with Transfer:440 for `Q₀`).
  (F2) canonical class with margins (`HasMargins`) in Σ/the leaf, so the uniform witness transport applies
      at shifted times (plus a limit gradient transfer).
  (F3) port the original comparison-angle far field (`FarSpatialNeck.lean:23`), so X4a needs neck
      alternatives only at time 0.
- Everything else X4 needs is available (W1′ + gluing + κ on `(−T*,0]`, Rm ≥ 0 by a window copy of
  `AncientPointedFlowLimitCurvature.lean:26`, completeness, Part A derivative, X4d-Σ → hRP via survivor maps,
  X4-ev for step 8); the static κ for X4a is derivable from XP3's parabolic κ + `Rm ≥ 0` + the derivative
  clause as XP3 describes. No X4 code written (would be a conditional delivery on the witness clause).

## F1 statements (lead decision F1; both elaborated with `sorry`, only `declaration uses sorry`)
### B9w — `Surgery/Topology/AncientPointedFlowLimitWindowNeckAlternatives.lean`
`FiniteHorn.neck_alternatives_of_local_flow_limit_on_window` = B9 (`ShiftedTransfer:354`) with:
- window schedule: `{T} {c : ℕ → ℝ} (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)`;
  `hconvσ` for `s ∈ Ioc (-T) 0`, `-c k < s`, shifted times in `Icc (-c k) 0`; `hcomplete`, `hσE` on `Ioc (-T) 0`;
  `hW` on `s ∈ Icc (-c k) 0`;
- NEW binder `hWF : ∀ k, ∀ᶠ j in atTop, (W k (f j) : Set _) ⊆ F.target j` (W1′: `W k n` = ball `k+3`, target ⊇ balls);
- approximant third alternative CHANGED to `IsCompact (connectedComponent z)` (component taken in `W k n`);
- conclusion, for `s ∈ Ioc (-T) 0`, `4·max q 1 < R_s(x)`:
  `Nonempty (SpatialNeck (G s) (2α) x) ∨ (∃ w, Nonempty (SpatialNeck (G s) (2α) w) ∧
   R_s(x) ≤ 4·max C2 1·R_s(w) ∧ d_{G s}(x,w) < ofReal (4·max C2 1/√R_s(x))) ∨ CompactSpace P.M`
  (the distance in alternative 2 is NEW; X4a′'s far field needs the neck point near the far point).
- Route for the third alternative: a compact component `Z ⊆ W k (f j) ⊆ F.target j` is open (manifold) ⇒
  `F.source ∩ F.map⁻¹ Z` is open and equals `F.symm '' Z`, compact hence closed, nonempty (∋ x) ⇒ all of the
  connected `P.M` ⇒ compact. No distance comparison needed.
### X4a′ — `Perelman/CanonicalNeighborhood/WindowScalarBoundNeckAlternatives.lean`
`exists_uniform_scalar_bound_on_openClosed_window_of_neck_alternatives`: X4a verbatim except the witness
clause is replaced by, on every `τ ∈ Ioc (-T*) 0`, `q < R_τ(x) →
Nonempty (SpatialNeck (G τ) ε x) ∨ (∃ w, Nonempty (SpatialNeck (G τ) ε w) ∧ R_τ(x) ≤ C·R_τ(w) ∧
d_{G τ}(x,w) < ofReal (C/√R_τ(x))) ∨ CompactSpace P.M`, with `{ε C q}` (one comparison constant).
Proof plan: XP4's proof; `Q₀` = max on compact `P.M`, else Transfer:440 (only alternatives 1–2); far field
copied with the witness replaced by alternatives 1–2 (`d(y,w) < C/√R_y ≤ 1` once `R_y ≥ C²`).
### SUPPLY GAP found while stating (reported before proving)
B9w's approximant third alternative `IsCompact (connectedComponent z)` in `W` holds iff the stage witness's
whole component `K` (compact, ⊆ ball(f z, 2C1/√R)) lies in the survivor image `f j (W)`.
- terminal-stage slices (`f = id`): provable (first exit: a stage-minimizing path from `z` inside `K` has
  `h(s)`-length ≤ 2C1/√R_h, so `h(0)`-length ≤ e·that by W1′'s `e²` clause, so it never reaches `∂W`);
- pre-event slices (arise only when `Rₙ(tₙ − time last)` stays bounded, e.g. Case II): needs "a component
  of stage `j` meeting the survivor image lies in it" — NOT in the tree (surgery could cut `K`).

## F1 deltas after lead decision (c) and review H19 (recorded before proving)
- X4a′ PROVED (file above, 432 lines incl. `windowNeckAccuracy.{u}` + `_pos`): XP4's proof copied (far field
  and main; XP4's public `le_two_mul_…_of_right_le` imported, not copied; no private lemma copied). DEVIATION:
  alternative 2's distance is `d_{G τ}(x,w) < 2` (bounded) instead of `< C/√R_τ(x)` — weaker hypothesis,
  stronger theorem; the far field only needs a bounded neck distance (`Rf := max D0 r + 3`). `Q₀`: max on
  compact `P.M`, else Transfer:440. H19 (c): X4 must take `2α ≤ windowNeckAccuracy` (the neck tolerance fed is
  `2α`). Compile: clean.
- B9w: statement unchanged (H19 (1) cleared). Distance clause (H19 (2)): proved for the SAME neck centre by a
  local copy of the core transfer whose alternative-2 branch adds, via `ball_subset_image_of_metric_lower_on_opens`
  (`OpenEmbeddingBallCapture:52`, `L = √2` from `g ≤ 2φ*h`), `φ w' = v` with `d_g(x, w') ≤ √2·C/√r_z`,
  `r_z > 7a/8`, and injectivity of `φ` identifies `w' = w`: `d_s(x,w) ≤ √(16/7)·C/√a < 4·max C 1/√a`.
  Compactness step via `F.partialDiffeomorph`'s open source + continuous inverse (H19 (1), (d)).
- Supply of B9w's third alternative (H19 (3), lead): BUFFERED capture, same lemma for terminal and pre-event
  slices: `ball_subset_image_of_metric_lower_on_opens` with `U = W`, `f = f_j`, source metric `g₀ = h(0)`,
  `L = e` (W1′: `h(0) ≤ e²·h(s)`, `h(s) = f_j*ḡ` scaled), `R = 19/10`: for `z ∈ closedBall(p, k+1)` the closed
  `g₀`-ball `(z, 19/10) ⊆ W = B(p, k+3)` is compact, so `B_ḡ(f z, 19/(10e)) ⊆ f(closedBall_{g₀}(z, 19/10))`;
  the stage witness's positive/round domain `K = component ⊆ B_ḡ(f z, 2C1/√R_h(z))` and threshold
  `q ≥ (20·e·C1/19)²` give `K ⊆ f(W)`, hence the `W`-component of `z` is `f⁻¹ K`, compact. Threshold is fixed
  (no "large k"), per H19's quantifier note.
- B9w PROVED: `Surgery/Topology/AncientPointedFlowLimitWindowNeckAlternatives.lean` (statement as in "F1 statements").
  Private `exists_neck_alternatives_transfer_constants_near` = copy of Transfer:1057 (alternatives 1–2 only)
  with the SAME-centre distance: capture `ball_hm(φx, rr/√2) ⊆ φ(closedBall_g(x, rr))`, `rr = √2·C/√z`,
  `z > 7a/8`; `w' = w` by injectivity; `d ≤ rr ≤ 2√2·C/√a < 4·max C 1/√a`. Private
  `compactSpace_of_isCompact_isOpen_subset_target` (open source + continuous inverse of the partial
  homeomorphism, H19 (1)). DEFERRED MERGE: the core copy generalizes Transfer:1057 (adds the distance).
  Compile clean (scratch chain).
- X4 supplier inventory (uncommitted, consumed via scratch): W1′ (XP3), gluing (XP3), κ on `(−T,0]` (XP3),
  X4a′ (mine), B9w (mine), X4d-Σ (mine), X4-ev (XP1), XA4's `RetainedCoreHistoryExtendAtBefore` (hnc,
  witnesses, pinching on `extendAt`), B12 (`abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt`),
  `abs_derivWithin_scalar_le_of_survivor_maps_of_lt`. Window copies still needed: shifted convergence
  (ShiftedTransfer:205), Part A (ShiftedTransfer:48), Rm ≥ 0 (Curvature:26), static κ at time 0.

## Resumed (XP2′), 2026-09-26 ~14:10 PDT
- Found on disk from the killed worker (uncommitted, not logged before): `Surgery/Topology/NeckAlternativesLocalPullCompact.lean`
  (buffered capture, local-pull form, compact third alternative), `Surgery/Topology/LocalFlowLimitWindowTransfer.lean`
  (window copies: Part A derivative, shifted convergence, `Rm ≥ 0`), `Surgery/Topology/CrossingMaximalWindow.lean`
  (static κ from parabolic κ + `Rm ≥ 0` + derivative clause; hRP transfer to the limit). Continuing from these.
- Scratch: `scratchpad\xp2b` (script `cc.sh`, modules renamed `XP2B.*`).
- Verified: `CrossingMaximalWindow.lean` (as left) compiles clean (scratch chain, std linter set; deps
  `WindowScalarBound`, X4a′, `LocalFlowLimitWindowTransfer` rebuilt as scratch oleans).
- BUFFERED CAPTURE, local form: `FiniteHorn.exists_neckAlternatives_or_isCompact_localPull_of_spatialCanonicalWitness`
  (`Surgery/Topology/NeckAlternativesLocalPullCompact.lean`, 150 lines): for an injective local diffeo `f : N → M`, a
  source metric `h0` with compact `closedBall_{h0}(z, r)` and `h0 ≤ L²·f*g` there, a witness at `f z` and the fixed
  buffer `L·(C + (D + 2/ε)√C) < r√R(f z)` (`C = max(2|C1|, C2)`): the pulled neck alternatives, or
  `IsCompact (connectedComponent z)` (component ⊆ `f⁻¹(B_g(f z, 2·radius)) ⊆ closedBall_{h0}(z, r)`, via
  `ball_subset_image_of_metric_lower_crossModel` + injectivity). Compile clean (std linter set).
- BUFFERED CAPTURE on survivor maps (terminal AND pre-event slices uniformly, any stage `activeStage v`):
  `ObservedHistory.exists_neckAlternatives_or_isCompact_of_survivor_maps`
  (`Surgery/Topology/TracedRegionNeckAlternativesCompact.lean`, new, 85 lines) = B6's statement with the third
  alternative `IsCompact (connectedComponent z)`; radius `r = 1`, `L = e` from W1′'s `e²` clause; threshold
  `qW ≥ (e·(C + (D+2/ε)√C))²` is fixed (no large-`k` clause). Compile clean.
- GENERIC WINDOW ASSEMBLY (X4 steps 2–7 on abstract W1′-shaped data), in `CrossingMaximalWindow.lean`:
  `exists_uniform_scalar_bound_of_local_flow_limit_on_window` (window analogue of the ancient B13 assembly
  `ShiftedTransfer:560`): `Rm ≥ 0` (window Curvature:26), completeness on `(−T, 0]`
  (`complete_at_earlier_time_of_ricci_nonnegative` from `G 0 = P.metric`), Part A window derivative,
  static κ (parabolic κ given as `completeness → ParabolicallyKappaNoncollapsedBelowScale … κ 1`, discharged by
  XP3 in X4), B9w with shifted times avoiding `E n` (window shifted convergence), hRP transfer
  (`scalar_le_at_distance_of_local_flow_limit_on_window`, happrox now in window form
  `∀ k, ∀ τ ∈ Icc (-c k) 0, τ < 0 → ∀ᶠ n`), then X4a′ at `ε := 2α ≤ windowNeckAccuracy` (H19 (c)),
  `q := max(4·max qW 1, 4·max qD 1, (2·max C2 1)²)` (the last makes B9w's `d < 4C'/√R` a `d < 2`).
  New def `crossingWindowNeckAccuracy := neckModelTolerance (min (windowNeckAccuracy/2) (1/44))` (+ `_pos`):
  the approximant neck accuracy must be `≤` it. Compile clean (std linter set).
- X4 (Σ form) drafted in NEW file `Surgery/Topology/CrossingWindowAnchorBound.lean`:
  `RetainedCoreHistory.exists_subseq_windowAnchorBound_of_depthExtendable` — DCA §2.7 statement verbatim
  (conclusion = X4ext's anchor hypothesis along `σ ∘ ψ`), Σ binders as explicit variables (only the used ones
  included), plus `hεX : ε ≤ crossingWindowNeckAccuracy` (replaces the design's `hεfar`, same role as XA4's
  `crossingNeckAccuracy`). Route: W1′ at `τ_k = T*(k+1)/(k+2)` on `K ∘ σ` (htraced from `DepthExtendable`), gluing
  corollary → `Gl` on `openClosed (−T*) 0`, `Gl 0 = P.metric`; generic window assembly with: hW from the buffered
  capture on survivor maps (`E'` = `[t₀,·)` ∪ event times, as X3), hderiv from B12 + survivor lemma (constants
  `(2Ctime, qD = 2)`, `t₀ := tₙ`), hpar from XP3's κ (κ/250, ρ = 1, radii `ε√Rₙ`), happrox from X4d-Σ via the
  survivor identity at `j = activeStage v` + `d_stage(f z, f x) ≤ d_{f*g}(z,x)`. Step 8: `ψ = f ∘ ψ₁`,
  `M = max C₀ 0 + 1`; `x = F.map p`, `p ∈ B̄_P(2A) ⊆ V k`, `x = φ p` (hφF), X4-ev gives `R(Bt.point) = Rₙ·R(h(−T'))(φ p)`,
  C² convergence at the fixed slice `−T' ∈ [−c_k, 0]` gives `R(h(−T'))(φ p) ≤ C₀ + 1`.
- X4 first single-declaration draft hit the per-declaration heartbeat limit (no budget override allowed): split
  into four generic `ObservedHistory` lemmas (same file), stated on arbitrary survivor-block data
  (the W1′ block shape with `X.obj n` written out), then a thin Σ assembly:
  * `exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks` (hW for the generic assembly; buffered capture),
  * `eventually_abs_derivWithin_scalar_le_of_survivor_blocks` (hderiv),
  * `survivor_blocks_scalar_le_at_distance` (happrox from an X4d-Σ-shaped stage bound),
  * `eventually_scalar_backwardPointTrace_le_of_window_limit` (step 8 via X4-ev).
  `E'` now uses `(K (σ m)).toHistory.time` (no reliance on the extendAt/H time defeq).
- `LocalFlowLimitWindowTransfer.lean`: `open private … from` module path moved to column 0 (longLine linter).

## Final state (XP2′)
| Brick | File | Lines | Compile (std linter set, scratch chain) | Axioms |
|---|---|---|---|---|
| buffered capture, local | `Surgery/Topology/NeckAlternativesLocalPullCompact.lean` | 173 | clean | propext, Classical.choice, Quot.sound |
| buffered capture, survivor maps | `Surgery/Topology/TracedRegionNeckAlternativesCompact.lean` | 92 | clean | same |
| B9w | `Surgery/Topology/AncientPointedFlowLimitWindowNeckAlternatives.lean` | 393 | clean | same |
| X4a′ | `Perelman/CanonicalNeighborhood/WindowScalarBoundNeckAlternatives.lean` | 423 | clean | same |
| window copies (Part A, shifted conv., Rm ≥ 0) | `Surgery/Topology/LocalFlowLimitWindowTransfer.lean` | 401 | clean | same |
| static κ, hRP transfer, generic window assembly, `crossingWindowNeckAccuracy` | `Surgery/Topology/CrossingMaximalWindow.lean` | 514 | clean | same |
| X4 + 4 generic lemmas | `Surgery/Topology/CrossingWindowAnchorBound.lean` | 789 | clean | same |
Axioms printed for all 17 public headlines from a scratch probe (deleted). No committed file touched; nothing
registered in `DifferentialGeometry.lean`. No private lemma copied except `closedBall_one_subset_of_ball_eq_window`
(7-line copy of XA4's private `closedBall_one_subset_of_ball_eq` in uncommitted `CrossingTimeZeroBound.lean`;
DEFERRED MERGE). Import order for acceptance: WindowScalarBound → X4a′; LocalFlowLimitWindowTransfer; B9w;
CrossingMaximalWindow; NeckAlternativesLocalPullCompact → TracedRegionNeckAlternativesCompact;
CrossingWindowAnchorBound (also needs W1′, gluing, XP3 κ, X4d-Σ + P-bricks, X4-ev, XA4's CrossingBaseSliceBound /
CrossingTracedRegion / RetainedCoreHistoryExtendAtBefore, X2 TracedRegionMaximalDepth).
Deviations: (1) X4 carries `hεX : ε ≤ crossingWindowNeckAccuracy` instead of the design's `hεfar : 2ε ≤ windowFarAccuracy`;
(2) X4a′ alternative-2 distance `< 2` (weaker hypothesis); (3) hRP transfer's approximant hypothesis is in window form.
X7 must supply: `ε ≤ crossingWindowNeckAccuracy` (add to εbar's `min`, alongside XA4's `crossingNeckAccuracy`), the Σ
fields used (`hε hεcone hκ hphi hCs hH hG hrec hq hpar hscale hpinch hslabs hbefore hsliver hbad`), `StrictMono σ`,
`0 < T*`, the ŷ/HEq pair, and `DepthExtendable … σ T` for all `T < T*` (X2/X3 + X4ext iteration).
