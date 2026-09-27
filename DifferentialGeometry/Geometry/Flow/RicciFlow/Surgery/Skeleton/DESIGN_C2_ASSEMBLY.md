# DESIGN C2 assembly: `historyReducedVolumeMonotone` (H8) and `historyReducedVolumeLocalUpperBound` (H9)

2026-09-26. Read-only design worker, worktree `D:\differential-geometry-pc3` (branch
`codex/pc-target-c-psf` @ bf07a1e58 plus uncommitted lanes). No Lean edits, no git writes, no builds.
Paths are relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/` unless they start with
`DifferentialGeometry/`.

**Probe result.** Every statement below was checked in one scratch file outside the repo:
`<session scratchpad>\c2a\P6.lean`, compiled with `LEAN_NUM_THREADS=2 lake env lean` against pc3's
`.lake` oleans (`HistoryLGeometry/JacobianUnconditional`, `Parametric/AreaInequality`,
`Parametric/Integration` and `HistoryParabolicBall` are all current). Result: **0 errors**. 24
declarations have `sorry` bodies; these are the bricks listed in §6. The two leaves themselves are
**proved in the probe with no `sorry` of their own**, and so is the whole H8 change-of-variables
chain (`lintegral_image_historyMinDomain_le_of_lt`, with the pointwise Jacobian step written out).
That proof exercised the instance plumbing end to end: G7's private `borel` instances, `modelHaar`
on `ThreeSpace`, the stage `borel` instance of `reducedVolume`, and the `extendHorizon`
definitional equalities. The probe also checked that
`(H.extendHorizon T' hT' G hG).toHistory.activeStage ⟨t, _, _⟩ = H.toHistory.activeStage t` and the
matching `stageAt` carrier equality both hold by `rfl`.

The leaf predicates take `P₀` only. The brief wrote `HistoryReducedVolumeMonotone P₀ g₀`, but on disk
it is `HistoryReducedVolumeMonotone (P₀ : OrientedThreeStage)`
(`Surgery/Topology/NoncollapsingThroughSurgeryLeaves.lean:208,214`). No `g₀` and no cutoff class are
involved.

## 1. Failures first

F1. **H8 cannot skip `MeasurableSet K` (`K := historyMinDomain … v₂`).** The pointwise step
`∫_K ℓJ(v₂) ≤ ∫_K ℓJ(v₁)` is false for a non-measurable `K` when the integrands are not measurable.
Configuration: Lebesgue measure on `[0,1]`, `K` a Bernstein set (every measurable subset of `K` and
of `Kᶜ` is null), `A = 1`, `B = 1_K`. Then `A ≤ B` on `K`, yet `∫⁻_K A = μ*(K) = 1` and
`∫⁻_K B = 0`. The measurable-hull trick (`restrict_toMeasurable_of_sFinite`) does rescue the area
inequality at `v₂`, but it does not rescue this step or the injective step at `v₁`. So `K` must be
shown measurable. Brick **M** (§3) does this.

F2. **The existing injective change of variables is unusable at `v₁`.**
`lintegral_image_eq_lintegral_paramDensity_mul` (`DifferentialGeometry/Analysis/Integration/Measure/Parametric/Integration.lean:53`)
needs `AEMeasurable φ` for `φ = regularizedDensity`, and nobody has proved that density measurable.
Queue entry 26's route through `hclosed` is still open. The fix is generic brick **G7′**: the `≥`
direction for any `φ`. Its proof uses three existing pieces:
- `ContinuousOn.measurableEmbedding` (Mathlib `MeasureTheory/Constructions/Polish/Basic.lean:864`);
- `MeasurableEmbedding.lintegral_map`;
- `lintegral_withDensity_eq_lintegral_mul_non_measurable` (Mathlib `Measure/WithDensity.lean:477`).

With G7′, **entry 26 is not a prerequisite.** Neither measurability of `regularMinimizerEndpoints`
nor of the density is needed anywhere. The first step is H4's equality, which needs no measurability.

F3. **`lSourceGaussian_uniform_tail` cannot give `R(η)`.** There are two reasons:
- its `M` needs `[PseudoMetricSpace M]`, which stage carriers do not have
  (`OrientedThreeStage`, `EventData.lean:161`);
- its `R` is chosen after the section variable `M` is fixed, so `R` may depend on the type.

H9 needs one `R` for all histories. Brick **TailG** restates the tail at the metric level, uniform over
all `X : Type u`, straight from `gaussianPosDef_uniform_tail`
(`DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/PositiveDefinite/GaussianTail.lean:197`).
It should be homed in `Perelman/LGeometry/Jacobian/SourceGaussianTail.lean`, with the flow version
recast as a corollary.

F4. **The single-flow I 7.3 theorem is unusable** (as DESIGN_22 F3 already says).
`exists_pos_redVolume_le_on_flowMetricBall` needs a global `[CompactSpace M] [ConnectedSpace M]` and a
`FlowMetricBall` of the same flow. H9 is assembled from G6 and G8 on the common flow instead.

F5. **The closed-start endpoint case is on the consumer's critical path.** It cannot be avoided.
`noncollapsedAboveBefore_of_reducedVolume_bounds` calls the leaf with `v₂ = √t`, so
`T − v₂² = 0 = time 0`, the closed start of stage 0. That time is never in `D.regular` of stage 0's
slab. Two things are therefore required:
- H3b's open package (which needs `hend : T − v² ∈ Ioo (time first) (stageEndTime first)`) must be
  extended to closed starts;
- H7b's comparison must hold with `v₂` at a closed start.

A limiting argument `v₂' ↑ v₂` is not available. No continuity of `reducedVolume` in `v` exists in
the tree, and proving `Ṽ(v₂) ≤ liminf Ṽ(v₂')` needs the area inequality at `v₂` itself, which is the
same missing piece. The route is extension, using G1b/G1c plus one new single-flow lemma **E2a**
(velocity limit at a closed start on a compact stage, by Gronwall). G1c's flat punctured
counterexample needs non-compactness, and the stages are compact.

F6. **H4, H5 and H7c exclude the base times the consumer uses.**
- H4's surjectivity and H5's injectivity need `T ∈ Ioo (time last) (stageEndTime last)`.
- H7c needs `time last < T` and `first = last`.
- The consumer calls both leaves at every `t ∈ Icc 0 horizon`. That includes event times
  `t = time k` (seam base), and it includes `t = horizon`. For cutoff-class histories
  (`hH.2.1 : time last = horizon`) these two coincide.

So the leaves are **not** provable from H4/H5/H7c as delivered. The fixes are:
- seam base: bricks SB1, SB2 and SB3;
- `t = horizon`: horizon extension X. **No interface change is needed**; see §2(b).

F7. **H7b is not delivered.** `OPUS_FILL_LOG_H7B.md` stops at "Progress 3": `half_trace_le` on an
`LFamilyChain`, with no file in the repo. Its chain breakpoints and H6's non-conjugacy work only at
non-seam parameters, so even a finished H7b yields antitonicity at non-seam `v` with an interior base.
H8 needs the pairwise statement `historyReducedJacobian_le_of_le` (§3), which also covers:
- `v₁` or `v₂` at a seam parameter;
- `v₂` at a closed start;
- a seam base.

That extra coverage is brick **H7b+**.

No leaf statement is false. I found no configuration that refutes `HistoryReducedVolumeMonotone` or
`HistoryReducedVolumeLocalUpperBound`.

## 2. H8: answers to (a)–(e)

Chain, for `0 < v₁ < v₂`, `v₂² ≤ T`, base `T ∈ Ico (time k) (stageEndTime k)` (after X). Let
`K := historyMinDomain hle T B₀ v₂ p ⊆ ThreeSpace`, with `U₂, f₂` and `U₁, f₁` the open packages
(brick E) at `v₂` and `v₁`. Then:

```
Ṽ(v₂) = ∫_{historyLExp(v₂) '' K} dens₂                  -- H4 corollary on Ico (SB1)
      = ∫_{f₂ '' K} dens₂                                -- agreement clause of E
      ≤ ∫_K ofReal(paramDensity g₂ f₂) · dens₂∘f₂        -- G7 (needs U₂ open, K ⊆ U₂, C¹, MeasurableSet K)
      = ∫_K ofReal(src) · ofReal(ℓJ(v₂))                 -- paramDensity_eq_historyLJacobianDensity_of_eventuallyEq
                                                        --   (U₂ ⊆ historyLExpDomain) + ofReal_historyReducedJacobian_eq
      ≤ ∫_K ofReal(src) · ofReal(ℓJ(v₁))                 -- setLIntegral_mono' (MeasurableSet K) + H7b+
      = ∫_K ofReal(paramDensity g₁ f₁) · dens₁∘f₁        -- same identities at v₁ (K ⊆ historyMinDomain(v₁), H5 nesting)
      ≤ ∫_{f₁ '' K} dens₁                                -- G7′ (InjOn f₁ K from SB2), no measurability of dens₁
      ≤ ∫_{regularMinimizerEndpoints(v₁)} dens₁ = Ṽ(v₁)  -- image_historyMinDomain_subset_of_le (H5), lintegral_mono_set,
                                                        --   exists_reducedVolume_eq_lintegral (H0)
```

The probe compiles this chain verbatim (§5).

(a) **`MeasurableSet K` is needed (F1).** `K` is not closed: a limit of minimizers can cross an event
at a boundary point of `old`, which is not a regular crossing. It is not the preimage of a
continuous map either, since the cost is not continuous. What works is to show that `K` is
**relatively closed in the open package `U`**:

`K = U ∩ {Z | ↑(L Z) ≤ regularizedCost(f Z)}`.

The ingredients are:
- `L`: the history action, continuous on `U` (E's last clause);
- `f`: C¹ on `U`;
- **upper semicontinuity of `regularizedCost` in the endpoint** (brick M1). Perturb a near-optimal
  competitor on its stage-`first` piece, which has positive length, inside one chart. Crossings are
  untouched, and bounded energy gives uniform control. This works at closed starts too.

On `U` the geodesic of `Z` is a competitor, so `cost(f Z) ≤ L Z`. The containment `⊇` therefore needs:
- the pieces of `historyLCurve` to be AC (brick M3a);
- the regularized action to equal `historyLAction` under the floor (brick M3b).

`{L ≤ cost∘f}` is the relative superlevel set of an upper semicontinuous function. Hence `K` is open
∩ closed, so Borel. That is brick **M**, `measurableSet_historyMinDomain`, stated for `borel ThreeSpace`
(the instance G7 uses). The cheaper routes all fail:
- closedness of `K`: false;
- the preimage of a continuous map: the cost is not continuous;
- the measurable hull: F1;
- entry 26's lower semicontinuity: not refuted, but not needed.

(b) **Base time.** `hT : T ∈ stageDomain k` admits two boundary cases:
- `T = time k` for `k ≥ 1` (`T = time 0 = 0` is excluded by `0 < v₁ ≤ v₂`, `v₂² ≤ T`);
- `k = last` with `T = horizon`.

The consumer uses both. **No interface change is needed.**
- `T = horizon`: replace `H` by `H.extendHorizon T' _ G hG` with `T' > horizon`.
  - When `time last < horizon`, `G` extends `finalSlab` by G1's
    `exists_isSolutionOn_extension_past_right_endpoint`. The stage is compact.
  - When `time last = horizon`, `G` is `exists_closedSlab_of_metric (stage last) (initialMetric last)`.
  - Brick X2 shows that `reducedVolume` is unchanged at every `T ≤ horizon` (X1, X2).
  - Then `T ∈ Ico (time k) (stageEndTime' k)`. The probed leaf proof always extends, so there is no
    case split.
- `T = time k` (seam base): H4, H5 and H7c must accept a multi-stage base window with `W.a = 0` (the
  glued seam flow). `HasHistoryLInitialVector` already allows it. The work is:
  - SB1: the initial vector exists at a seam base;
  - SB2: injectivity at a seam base, reading `Z` off the base window instead of the stage-`last`
    piece `Icc 0 η`, which is `{0}` there;
  - SB3: H7c's limit on the glued base window.

  All bricks E, M, H7b+ and SB1/SB2 are stated with `hT : T ∈ Ico (time last) (stageEndTime last)`.

(c) **Endpoint time `T − v₂²` an event time or time 0**, the post-surgery closed start of stage
`first`. It is needed (F5). Brick E covers it:
1. Run H3b′'s prefix family up to a non-event `c < v`.
2. Transfer into stage `first`'s slab flow (`exists_incomingSlab_stageMetric`).
3. Close the last step with G1b's `exists_lPhaseFlow_of_start` / G1c's
   `exists_lRegularizedFamily_of_start`. Its hypothesis `hlim` comes from **E2a** (Gronwall:
   `d/ds|γ'|² ≤ C(1+|γ'|²)` from bounded `Ric` and `∇R` on the compact stage up to the closed start).

This is H3b's open item (4) plus E2a. The event-time case at `v₁` (seam parameter, `first₁` the new
stage at its closed start) is the same closed-start case, so it goes through E too.

(d) **Pointwise inequality:** `historyReducedJacobian_le_of_le` (H7b+), fed by:
- `ofReal_historyReducedJacobian_eq` (H7a): `ofReal ℓJ = ofReal(J/src) · dens(historyLExp Z)` on
  `historyMinDomain`;
- `paramDensity_eq_historyLJacobianDensity_of_eventuallyEq` (H7a), which is why E returns
  `U ⊆ historyLExpDomain`;
- `mem_historyLExpDomain_of_le` (H3b′) for the `v₁` subtype;
- `historyMinDomain_subset_of_le` (H5) for `K ⊆ historyMinDomain(v₁)`.

H7b as planned delivers `(log ℓJ)' ≤ 0` on windows at non-seam parameters (F7). H7b+ adds:
- the value at seam parameters: left-continuity of `v ↦ ℓJ(first v, v)` at `w`, where
  `v ≤ w` is the post-surgery stage-`k` side (H7a open item (b));
- the closed-start end `v₂`, using the E2a family for the Jacobi fields at `v₂`;
- the seam base.

(e) **Equality at `v₁`** is used only as `≥`, via G7′ with `InjOn f₁ K`. That comes from
`injOn_historyLExp_of_lt` (H5; SB2 at a seam base) and the agreement `f₁ = historyLExp` on
`K ⊆ U₁ ⊆ historyLExpDomain(v₁)`.

## 3. H9: split at `|Z| = R(η)`

Quantifier order. Take `C₀ := (4π)^{-3/2} e^{36}` first. For each `η`:
- `R := R(η)` from **TailG** with `eps = ofReal η`, a dimension-only choice;
- `σ := σ(R)` from **C9**, which is G6's `σ = min(1/2, 1/(16(√(AQ)+1)))` with `Q = Q(R)`.

Hence `σ = σ(η)` is independent of `H`, `t`, `p` and `r`. It is fixed before `∀ H`, as the leaf
requires. The constant `36 = 9 + 27` has two sources:
- `r⁴|Rm|² ≤ 1` gives `Ric ≥ −9/r²` (G6's `K = n²`), so `R ≥ −27/r²`. The action then satisfies
  `A ≥ −18v³/r²`, so `−A/(2v) ≤ 9σ² ≤ 9`;
- G8's volume-form distortion is `e^{n³} = e^{27}`.

Assembly (probed, §5):
1. Extend (X1). Transfer the ball (X3: `isParabolicallyRmControlledBall_extendHorizon`), the volume
   (`stageMetric_extendHorizon`) and `Ṽ` (X2). Now `t < stageEndTime' (activeStage t)`
   (`lt_stageEndTime_extendHorizon`).
2. `Ṽ = ∫_{historyLExp '' K} dens` (SB1 corollary, Ico base; `v = σr > 0`, `v² ≤ r² ≤ t`).
3. `historyLExp '' K ⊆ historyLExp '' (K ∩ {√g(Z,Z) ≤ R}) ∪ historyLExp '' (K ∩ {R < √g(Z,Z)})`, then
   `lintegral_mono_set` and `lintegral_union_le`.
4. Core ≤ `ofReal(C₀/(σr)³) · vol_t(B(p,r))` (**C9**). Inside C9:
   - **CF** (route (B)) gives the common flow on `closed a t₁` with `t < t₁`, so `t ∈ D.regular`.
   - An `LWindow` with `a = 0` built from it identifies `historyLCurve Z = f ∘ lRegularizedCurve S t pU Z`
     for `g(Z,Z) ≤ R²`. This uses G6 (confinement within `r/4`, domain `σr`) and
     `IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector` (H3a).
   - Hence `historyLAction Z = lRegularizedAction S …` and `dens ≤ (4π)^{-3/2} e^{9}/(σr)³`. The
     scalar bound comes from `r⁴|Rm|² ≤ 1` on `U`. This works because `Z ∈ historyMinDomain`, so
     `Z`'s own geodesic realizes the cost. A competitor leaving `U` is irrelevant.
   - Volume: the image lies in `f_first '' A` with `A := {γ_S(Z, v)}` inside the compact half-ball.
     Three steps bound it:
     - `riemannianVolumeMeasure_map_restrict_of_injective_local_isometry`
       (`DifferentialGeometry/Geometry/Measure/LocalIsometry.lean:88`), using the metric clause at
       `t − v² ∈ stageDomain first`;
     - G8 `riemannianVolumeMeasure_le_exp_cube_mul_of_parabolic_rmNormSq_le` on `[t − r², t]`, which
       gives `e^{27}`;
     - `riemannianVolumeMeasure_restrictOpen_apply` with `hterminal` and `U = B(p,r)`.
   - G6's compactness hypothesis holds because `{d_U(pU,·) ≤ r/2}` is closed in `U` and lies inside the
     preimage of the compact stage ball of radius `r/2 < r`.
5. Tail ≤ `∫_{R<√g(Z,Z)} ofReal(π^{-3/2} src e^{−g(Z,Z)}) dλ ≤ ofReal η` (**T9**, then **TailG** at
   `X := stage`, `g := stageMetric k t`, `x := p`). T9 is G7 on `K ∩ {R < √g}`, which is measurable
   by M and a closed condition. It uses the pointwise `historyReducedJacobian_le_gaussian` (Gauss =
   H7b+ with H7c; SB3 at a seam base).

## 4. Degenerate cases

| Case | What happens |
|---|---|
| Empty endpoint set / `K = ∅` | Image is `∅`, `Ṽ = 0`. The probe's H8 proof has this branch explicitly; for H9 it is `bot_le`. |
| `v = 0` | Excluded: `0 < v₁`; in H9 `v = σr > 0` since `hball.1 : 0 < r`. |
| `first > k` (zero branch of `reducedVolume`) | Never reached: `v² ≤ T` gives `first ≤ k` (`first_le_of_mem_stageDomain`, probed). |
| `t = horizon` / `T = horizon` | Horizon extension X1–X3. Stated for every `RetainedCoreHistory`, including `time last = horizon`. |
| `T = time k`, `k ≥ 1` (seam base; includes `T = horizon = time last` after X) | SB1, SB2, SB3. E, M and H7b+ take `hT : T ∈ Ico …`. If `p` is not a regular output image, no curve crosses at `s = 0`, so `Ṽ ≡ 0` and the claim holds trivially. The bricks cover it anyway. |
| `T − v²` an event time, or `0` (closed start) | E through E2a, G1b and G1c; M through E; H7b+ at the endpoint. The consumer always hits this with `v₂ = √t`. |
| Cost `⊤` | Density 0 off the image (`setLIntegral_regularMinimizerEndpoints_eq`, H4). `historyMinDomain` requires finite action. |
| `T − v² < 0` in a generic brick | `IsHistoryLGeodesicOn` needs `T − v² ∈ stageDomain first ⊆ [0, horizon]`, so `K = ∅`. |
| `v₁ = v₂` | `le_rfl` (probed). |

## 5. Probed statements (all elaborate; bodies `sorry` except the assembly proofs)

Namespaces as in the probe: `DifferentialGeometry.Integral.Measure` for G7′,
`DifferentialGeometry.PDE.RicciFlow.Perelman` for E2a,
`DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory` or `.RetainedCoreHistory` for
history bricks (variables `{H : ObservedHistory.{u}} {first last k} {T B v v₁ v₂ : ℝ}
{p : (H.stage last).Carrier}`). The probe opens `ContDiff` (for `∞`), `Tensor0SBundle` (for
`normSq0S`) and `Geometry.Curvature`. Measure instances: G7′ uses G7's private `borel` instances;
history integrals use the file-local `borel P.Carrier` instance.

### 5.1 Generic and single-flow

```lean
theorem lintegral_paramDensity_mul_le_lintegral_image
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : InjOn f K) (φ : M → ℝ≥0∞) :
    ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x) * φ (f x) ∂(modelHaar (E := E)) ≤
      ∫⁻ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g := sorry
```

```lean
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_tendsto_lVelocity_of_isLRegularizedGeodesicOn_of_closedStart [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) {a c : ℝ} (hac : a < c)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a c ×ˢ (univ : Set M)))
    {T s₁ v : ℝ} (hs₁ : 0 < s₁) (hs₁v : s₁ < v) (hstart : T - v ^ 2 = a)
    (hreg : ∀ s ∈ Ioo s₁ v, T - s ^ 2 ∈ D.regular) {γ : ℝ → M}
    (hγ : IsLRegularizedGeodesicOn S T γ (Ioo s₁ v)) :
    ∃ ξ : TangentBundle I M,
      Tendsto (fun s => (TotalSpace.mk' E (γ s) (lVelocity (I := I) γ s) : TangentBundle I M))
        (𝓝[<] v) (𝓝 ξ) := sorry
```

```lean
theorem exists_uniform_tail_gaussian_metric (eps : ℝ≥0∞) (heps : 0 < eps) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
      [IsManifold ThreeModel ∞ X] (g : SmoothRiemannianMetric ThreeModel X) (x : X),
      ∫⁻ Z : ThreeSpace in {Z | R < Real.sqrt (g.inner x Z Z)},
        ENNReal.ofReal ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
          Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
            g.inner x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis ThreeSpace i)
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis ThreeSpace k)).det *
          Real.exp (-g.inner x Z Z)) ∂(modelHaar (E := ThreeSpace)) ≤ eps := sorry
```

### 5.2 History L-geometry (E, M, H7b+, Gauss, SB1, SB2, T9)

```lean
theorem exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain
    {hle : first ≤ last} (hv : 0 < v) (hT : T ∈ Ico (H.time last) (H.stageEndTime last))
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) (q : (H.stage first).Carrier) :
    ∃ U : Set ThreeSpace, IsOpen U ∧ H.historyMinDomain hle T B v p ⊆ U ∧
      U ⊆ H.historyLExpDomain hle T v p ∧
      (∃ f : ThreeSpace → (H.stage first).Carrier,
        ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel 1 f U ∧
        ∀ Z (hZ : Z ∈ H.historyLExpDomain hle T v p), f Z = H.historyLExp hle T v p ⟨Z, hZ⟩) ∧
      ∃ L : ThreeSpace → ℝ, ContinuousOn L U ∧
        ∀ Z (hZ : Z ∈ H.historyLExpDomain hle T v p), L Z = H.historyLAction hle T v p ⟨Z, hZ⟩ :=
  sorry
```

```lean
theorem upperSemicontinuous_regularizedCost {hle : first ≤ last} (hv : 0 < v) (hT : T ∈ H.stageDomain last)
    (hend : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) :
    UpperSemicontinuous (H.regularizedCost first last hle T B 0 v p) := sorry
```

```lean
theorem absolutelyContinuousOnInterval_historyLCurve {hle : first ≤ last} (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (j : H.StageInterval first last) :
    Manifold.absolutelyContinuousOnInterval ThreeModel (H.historyLCurve hle T v p Z j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) := sorry
```

```lean
theorem regularizedExtendedAction_historyLCurve_eq_historyLAction_of_mem {hle : first ≤ last}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) :
    H.regularizedExtendedAction first last T B 0 v (H.historyLCurve hle T v p Z) =
      (H.historyLAction hle T v p Z : WithTop ℝ) := sorry
```

```lean
theorem measurableSet_historyMinDomain {hle : first ≤ last} (hv : 0 < v)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last))
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) :
    @MeasurableSet ThreeSpace (borel ThreeSpace) (H.historyMinDomain hle T B v p) := sorry
```

```lean
theorem historyReducedJacobian_le_of_le {hle : first ≤ last}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) (hfk : first ≤ k) (hkl : k ≤ last)
    (hv₁ : 0 < v₁)
    (h12 : v₁ ≤ v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k) (Z : H.historyLExpDomain hle T v₂ p)
    (hZ : Z.1 ∈ H.historyMinDomain hle T B v₂ p) :
    H.historyReducedJacobian hle T v₂ p Z ≤
      H.historyReducedJacobian hkl T v₁ p ⟨Z.1, mem_historyLExpDomain_of_le hfk hkl hv₁ h12 hk Z.2⟩ :=
  sorry
```

```lean
theorem historyReducedJacobian_le_gaussian {hle : first ≤ last}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (hZ : Z.1 ∈ H.historyMinDomain hle T B v p) :
    H.historyReducedJacobian hle T v p Z ≤
      (Real.pi ^ ((3 : ℝ) / 2))⁻¹ * Real.exp (-(H.stageMetric last T).inner p Z.1 Z.1) :=
  sorry
```

```lean
theorem exists_historyLExp_eq_of_mem_regularMinimizerEndpoints_of_mem_Ico {hle : first ≤ last}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) (hv : 0 < v)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) {q : (H.stage first).Carrier}
    (hq : q ∈ H.regularMinimizerEndpoints first last hle T B v p)
    (hfin : H.regularizedCost first last hle T B 0 v p q ≠ ⊤) :
    ∃ Z : H.historyLExpDomain hle T v p,
      Z.1 ∈ H.historyMinDomain hle T B v p ∧ H.historyLExp hle T v p Z = q := sorry
```

```lean
theorem injOn_historyLExp_of_lt_of_mem_Ico {hle : first ≤ last} (hkl : k ≤ last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) (hv₁ : 0 < v₁) (h12 : v₁ < v₂)
    (hk : T - v₁ ^ 2 ∈ H.stageDomain k) :
    InjOn (H.historyLExp hkl T v₁ p) (Subtype.val ⁻¹' H.historyMinDomain hle T B v₂ p) := sorry
```

```lean
theorem lintegral_image_historyMinDomain_tail_le {hle : first ≤ last}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) (hv : 0 < v) (R : ℝ) :
    ∫⁻ q in H.historyLExp hle T v p '' (Subtype.val ⁻¹' (H.historyMinDomain hle T B v p ∩
        {Z | R < Real.sqrt ((H.stageMetric last T).inner p Z Z)})),
        H.regularizedDensity first last hle T B v p q
        ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
          (H.stageMetric first (T - v ^ 2)) ≤
      ∫⁻ Z : ThreeSpace in {Z | R < Real.sqrt ((H.stageMetric last T).inner p Z Z)},
        ENNReal.ofReal ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ * H.historyLSourceDensity T p *
          Real.exp (-(H.stageMetric last T).inner p Z Z)) ∂(modelHaar (E := ThreeSpace)) :=
  sorry
```

### 5.3 Common flow past `t` (CF) and core (C9)

```lean
open _root_.Manifold TopologicalSpace in
theorem exists_common_flow_past_time_of_parabolicallyRmControlledBall
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (r : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r)
    (ht : (t : ℝ) < H.stageEndTime (H.activeStage t)) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - r ^ 2 ∧
      ∃ (t₁ : ℝ) (htt₁ : t.val < t₁),
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set (H.stageAt t).Carrier) = riemannianBallOf (H.stageMetric (H.activeStage t) t) p r ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ H.activeStage t), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U)
                (RealTimeInterval.closed a.val t₁ ((show (a : ℝ) ≤ t from hat).trans htt₁.le)),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                ∀ v ∈ Icc a.val t₁, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                r ^ 4 * normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ 1) ∧
              S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U ∧
              ∃ (pU : U) (K : Set U), pU.val = p ∧
                Subtype.val '' K =
                  riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2) ∧
                IsCompact K ∧ pU ∈ interior K ∧
                ∀ x ∈ frontier K,
                  ENNReal.ofReal (r / 2) ≤ riemannianEDistOf (S.base.metric t) pU x := sorry
```

```lean
theorem exists_lintegral_image_historyMinDomain_core_le (R : ℝ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
      (p : (H.stageAt t).Carrier) (r B : ℝ), H.isParabolicallyRmControlledBall t p r →
      (t : ℝ) < H.stageEndTime (H.activeStage t) →
      (∀ j, ∀ τ ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j τ) x) →
      ∀ (hle : H.activeStage (projIcc 0 H.horizon H.horizon_nonneg (t - (σ * r) ^ 2)) ≤
        H.activeStage t),
      ∫⁻ q in H.historyLExp hle t (σ * r) p '' (Subtype.val ⁻¹'
          (H.historyMinDomain hle t B (σ * r) p ∩
            {Z | Real.sqrt ((H.stageMetric (H.activeStage t) t).inner p Z Z) ≤ R})),
          H.regularizedDensity _ _ hle t B (σ * r) p q
          ∂riemannianVolumeMeasure ThreeModel
            (H.stage (H.activeStage (projIcc 0 H.horizon H.horizon_nonneg
              (t - (σ * r) ^ 2)))).Carrier (H.stageMetric _ (t - (σ * r) ^ 2)) ≤
        ENNReal.ofReal ((4 * Real.pi) ^ (-(3 : ℝ) / 2) * Real.exp 36 / (σ * r) ^ 3) *
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) := sorry
```

### 5.4 `RetainedCoreHistory`: SB1 corollary and horizon extension (X)

```lean
theorem exists_reducedVolume_eq_lintegral_image_historyMinDomain_of_mem_Ico :
    ∃ b : ℝ, ∀ B₀ : ℝ, b ≤ B₀ → ∀ (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier)
      (T v : ℝ)
      (hle : H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)) ≤ k),
      0 < v → T ∈ Ico (H.toHistory.time k) (H.toHistory.stageEndTime k) →
      H.reducedVolume k p T v =
        ∫⁻ q in H.toHistory.historyLExp hle T v p ''
            (Subtype.val ⁻¹' H.toHistory.historyMinDomain hle T B₀ v p),
          H.toHistory.regularizedDensity _ k hle T B₀ v p q
          ∂riemannianVolumeMeasure ThreeModel
            (H.stage (H.toHistory.activeStage
              (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)))).Carrier
            (H.toHistory.stageMetric _ (T - v ^ 2)) := sorry
```

```lean
theorem exists_extendHorizon_gt :
    ∃ (T' : ℝ) (hT' : H.horizon < T')
      (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
      (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
      ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
        G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ := sorry
```

```lean
theorem reducedVolume_extendHorizon {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier) {T v : ℝ} (hT : T ≤ H.horizon) :
    (H.extendHorizon T' hT' G hG).reducedVolume k p T v = H.reducedVolume k p T v := sorry
```

```lean
theorem stageMetric_extendHorizon {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (j : Fin (H.eventCount + 1)) {τ : ℝ} (hτ : τ ∈ H.toHistory.stageDomain j) :
    (H.extendHorizon T' hT' G hG).toHistory.stageMetric j τ = H.toHistory.stageMetric j τ :=
  sorry
```

```lean
theorem isParabolicallyRmControlledBall_extendHorizon {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (t : Icc (0 : ℝ) H.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ)
    (hball : H.toHistory.isParabolicallyRmControlledBall t p r) :
    (H.extendHorizon T' hT' G hG).toHistory.isParabolicallyRmControlledBall
      ⟨t.1, t.2.1, t.2.2.trans hT'⟩ p r := sorry
```

```lean
theorem lt_stageEndTime_extendHorizon {T' : ℝ} (hT' : H.horizon < T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (t : Icc (0 : ℝ) H.horizon) :
    (t : ℝ) < (H.extendHorizon T' hT'.le G hG).toHistory.stageEndTime
      (H.toHistory.activeStage t) := sorry
```

```lean
theorem mem_Icc_of_mem_stageDomain' {k : Fin (H.eventCount + 1)} {T : ℝ}
    (hT : T ∈ H.toHistory.stageDomain k) : T ∈ Icc 0 H.horizon := sorry
```

```lean
theorem stageDomain_extendHorizon {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (k : Fin (H.eventCount + 1)) :
    H.toHistory.stageDomain k ⊆ (H.extendHorizon T' hT' G hG).toHistory.stageDomain k := sorry
```

```lean
theorem mem_Ico_extendHorizon_of_mem_stageDomain {T' : ℝ} (hT' : H.horizon < T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {k : Fin (H.eventCount + 1)} {T : ℝ}
    (hT : T ∈ H.toHistory.stageDomain k) :
    T ∈ Ico ((H.extendHorizon T' hT'.le G hG).toHistory.time k)
      ((H.extendHorizon T' hT'.le G hG).toHistory.stageEndTime k) := sorry
```

### 5.5 Assembly proofs (compile in the probe, no own `sorry`)

H8 core chain:

```lean
theorem lintegral_image_historyMinDomain_le_of_lt {hle : first ≤ last} (hkl : k ≤ last)
    (hfk : first ≤ k)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) (hv₁ : 0 < v₁) (h12 : v₁ < v₂)
    (hk : T - v₁ ^ 2 ∈ H.stageDomain k) :
    ∫⁻ q in H.historyLExp hle T v₂ p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v₂ p),
        H.regularizedDensity first last hle T B v₂ p q
        ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
          (H.stageMetric first (T - v₂ ^ 2)) ≤
      ∫⁻ q in H.regularMinimizerEndpoints k last hkl T B v₁ p,
        H.regularizedDensity k last hkl T B v₁ p q
        ∂riemannianVolumeMeasure ThreeModel (H.stage k).Carrier (H.stageMetric k (T - v₁ ^ 2)) := by
  classical
  have hv₂ : 0 < v₂ := hv₁.trans h12
  set K : Set ThreeSpace := H.historyMinDomain hle T B v₂ p with hKdef
  rcases K.eq_empty_or_nonempty with hK0 | ⟨Z₀, hZ₀⟩
  · have : Subtype.val ⁻¹' H.historyMinDomain hle T B v₂ p =
        (∅ : Set (H.historyLExpDomain hle T v₂ p)) := by
      ext Z
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hZ
      exact (hK0 ▸ hZ : Z.1 ∈ (∅ : Set ThreeSpace))
    rw [this, image_empty, Measure.restrict_empty, lintegral_zero_measure]
    exact bot_le
  have hZ₀d : Z₀ ∈ H.historyLExpDomain hle T v₂ p :=
    historyMinDomain_subset_historyLExpDomain hZ₀
  have hZ₀₁ : Z₀ ∈ H.historyLExpDomain hkl T v₁ p :=
    mem_historyLExpDomain_of_le hfk hkl hv₁ h12.le hk hZ₀d
  obtain ⟨U₂, hU₂, hKU₂, hU₂d, ⟨f₂, hf₂, hf₂eq⟩, -⟩ :=
    exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain (hle := hle) (p := p)
      hv₂ hT hfloor (H.historyLExp hle T v₂ p ⟨Z₀, hZ₀d⟩)
  obtain ⟨U₁, hU₁, hKU₁, hU₁d, ⟨f₁, hf₁, hf₁eq⟩, -⟩ :=
    exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain (hle := hkl) (p := p)
      hv₁ hT hfloor (H.historyLExp hkl T v₁ p ⟨Z₀, hZ₀₁⟩)
  have hKK₁ : K ⊆ H.historyMinDomain hkl T B v₁ p :=
    historyMinDomain_subset_of_le hfloor hkl hv₁ h12.le hk
  have hKm : @MeasurableSet ThreeSpace (borel ThreeSpace) K :=
    measurableSet_historyMinDomain hv₂ hT hfloor
  have himg₂ : H.historyLExp hle T v₂ p '' (Subtype.val ⁻¹' K) = f₂ '' K := by
    ext q
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      exact ⟨Z.1, hZ, hf₂eq Z.1 Z.2⟩
    · rintro ⟨Z, hZ, rfl⟩
      exact ⟨⟨Z, historyMinDomain_subset_historyLExpDomain hZ⟩, hZ,
        (hf₂eq Z (historyMinDomain_subset_historyLExpDomain hZ)).symm⟩
  have himg₁ : f₁ '' K ⊆ H.regularMinimizerEndpoints k last hkl T B v₁ p := by
    rintro _ ⟨Z, hZ, rfl⟩
    have hZd := hU₁d (hKU₁ (hKK₁ hZ))
    rw [hf₁eq Z hZd]
    exact (image_historyMinDomain_subset_of_le hfloor hkl hv₁ h12.le hk
      ⟨⟨Z, hZd⟩, hZ, rfl⟩).1
  have hinj : InjOn f₁ K := by
    intro Z hZ Z' hZ' hEq
    have hZd := hU₁d (hKU₁ (hKK₁ hZ))
    have hZd' := hU₁d (hKU₁ (hKK₁ hZ'))
    rw [hf₁eq Z hZd, hf₁eq Z' hZd'] at hEq
    exact congrArg Subtype.val
      (injOn_historyLExp_of_lt_of_mem_Ico hkl hfloor hT hv₁ h12 hk hZ hZ' hEq)
  have hpt : ∀ Z ∈ K,
      ENNReal.ofReal (paramDensity (H.stageMetric first (T - v₂ ^ 2)) f₂ Z) *
          H.regularizedDensity first last hle T B v₂ p (f₂ Z) ≤
        ENNReal.ofReal (paramDensity (H.stageMetric k (T - v₁ ^ 2)) f₁ Z) *
          H.regularizedDensity k last hkl T B v₁ p (f₁ Z) := by
    intro Z hZ
    have hZd₂ : Z ∈ H.historyLExpDomain hle T v₂ p := hU₂d (hKU₂ hZ)
    have hZ₁m : Z ∈ H.historyMinDomain hkl T B v₁ p := hKK₁ hZ
    have hZd₁ : Z ∈ H.historyLExpDomain hkl T v₁ p :=
      mem_historyLExpDomain_of_le hfk hkl hv₁ h12.le hk hZd₂
    have hJ₂ : paramDensity (H.stageMetric first (T - v₂ ^ 2)) f₂ Z =
        H.historyLJacobianDensity hle T v₂ p ⟨Z, hZd₂⟩ ⟨first, le_rfl, hle⟩ v₂ := by
      refine paramDensity_eq_historyLJacobianDensity_of_eventuallyEq (Z₀ := ⟨Z, hZd₂⟩)
        ⟨first, le_rfl, hle⟩ v₂ ?_
      filter_upwards [hU₂.mem_nhds (hKU₂ hZ)] with W hW
      rw [hf₂eq W (hU₂d hW), historyLCurveMap_of_mem _ _ (hU₂d hW)]
      rfl
    have hJ₁ : paramDensity (H.stageMetric k (T - v₁ ^ 2)) f₁ Z =
        H.historyLJacobianDensity hkl T v₁ p ⟨Z, hZd₁⟩ ⟨k, le_rfl, hkl⟩ v₁ := by
      refine paramDensity_eq_historyLJacobianDensity_of_eventuallyEq (Z₀ := ⟨Z, hZd₁⟩)
        ⟨k, le_rfl, hkl⟩ v₁ ?_
      filter_upwards [hU₁.mem_nhds (hKU₁ hZ₁m)] with W hW
      rw [hf₁eq W (hU₁d hW), historyLCurveMap_of_mem _ _ (hU₁d hW)]
      rfl
    have hsrc := H.historyLSourceDensity_pos (T := T) (p := p)
    have e₂ := ofReal_historyReducedJacobian_eq hfloor hv₂ (Z₀ := ⟨Z, hZd₂⟩) hZ
    have e₁ := ofReal_historyReducedJacobian_eq hfloor hv₁ (Z₀ := ⟨Z, hZd₁⟩) hZ₁m
    have hmono := historyReducedJacobian_le_of_le hfloor hT hfk hkl hv₁ h12.le hk
      ⟨Z, hZd₂⟩ hZ
    have key (J s : ℝ) (hs : 0 < s) (d : ℝ≥0∞) :
        ENNReal.ofReal J * d = ENNReal.ofReal s * (ENNReal.ofReal (J / s) * d) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hs.le, mul_div_cancel₀ _ hs.ne']
    rw [hJ₂, hJ₁, hf₂eq Z hZd₂, hf₁eq Z hZd₁,
      key (H.historyLJacobianDensity hle T v₂ p ⟨Z, hZd₂⟩ ⟨first, le_rfl, hle⟩ v₂) _ hsrc,
      key (H.historyLJacobianDensity hkl T v₁ p ⟨Z, hZd₁⟩ ⟨k, le_rfl, hkl⟩ v₁) _ hsrc, ← e₂, ← e₁]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hmono)
  rw [himg₂]
  calc _ ≤ ∫⁻ Z in K, ENNReal.ofReal (paramDensity (H.stageMetric first (T - v₂ ^ 2)) f₂ Z) *
          H.regularizedDensity first last hle T B v₂ p (f₂ Z) ∂(modelHaar (E := ThreeSpace)) :=
        lintegral_image_le_lintegral_paramDensity_mul _ hU₂ hKm hKU₂ hf₂ _
    _ ≤ ∫⁻ Z in K, ENNReal.ofReal (paramDensity (H.stageMetric k (T - v₁ ^ 2)) f₁ Z) *
          H.regularizedDensity k last hkl T B v₁ p (f₁ Z) ∂(modelHaar (E := ThreeSpace)) :=
        setLIntegral_mono' hKm hpt
    _ ≤ ∫⁻ q in f₁ '' K, H.regularizedDensity k last hkl T B v₁ p q
          ∂riemannianVolumeMeasure ThreeModel (H.stage k).Carrier
            (H.stageMetric k (T - v₁ ^ 2)) :=
        lintegral_paramDensity_mul_le_lintegral_image _ hU₁ hKm
          (fun Z hZ => hKU₁ (hKK₁ hZ)) hf₁ hinj _
    _ ≤ _ := lintegral_mono_set himg₁
```

```lean
theorem reducedVolume_le_of_lt_of_mem_Ico (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier)
    {T v₁ v₂ : ℝ} (hT : T ∈ Ico (H.toHistory.time k) (H.toHistory.stageEndTime k))
    (hTk : T ∈ H.toHistory.stageDomain k) (hv₁ : 0 < v₁) (h12 : v₁ < v₂) (hv₂T : v₂ ^ 2 ≤ T) :
    H.reducedVolume k p T v₂ ≤ H.reducedVolume k p T v₁ := by
  obtain ⟨b, hb⟩ := H.exists_reducedVolume_eq_lintegral_image_historyMinDomain_of_mem_Ico
  obtain ⟨b', -, hfl⟩ := H.exists_stageMetric_scalar_lower_bound
  obtain ⟨b'', hb''⟩ := H.exists_reducedVolume_eq_lintegral
  set B₀ := max b (max b' b'')
  have hfloor : ∀ j, ∀ t ∈ H.toHistory.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.toHistory.stageMetric j t) x := fun j t ht x =>
    (neg_le_neg (le_max_of_le_right (le_max_left _ _))).trans (hfl j t ht x)
  have hTI := H.mem_Icc_of_mem_stageDomain' hTk
  have hv₂ : 0 < v₂ := hv₁.trans h12
  have hmem (v : ℝ) (hv : 0 ≤ v) (hvT : v ^ 2 ≤ T) :
      T - v ^ 2 ∈ H.toHistory.stageDomain
        (H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2))) := by
    have h := H.toHistory.activeStage_mem (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2))
    have hv' : ((projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2) : ℝ)) = T - v ^ 2 := by
      rw [projIcc_of_mem _ ⟨by linarith, by linarith [hTI.2, sq_nonneg v]⟩]
    rwa [hv'] at h
  have hv₁T : v₁ ^ 2 ≤ T := (pow_le_pow_left₀ hv₁.le h12.le 2).trans hv₂T
  have hT0 : T - (0 : ℝ) ^ 2 ∈ H.toHistory.stageDomain k := by simpa using hTk
  have hle₂ := ObservedHistory.first_le_of_mem_stageDomain le_rfl hv₂.le
    (hmem v₂ hv₂.le hv₂T) hT0
  have hle₁ := ObservedHistory.first_le_of_mem_stageDomain le_rfl hv₁.le
    (hmem v₁ hv₁.le hv₁T) hT0
  have hfk := ObservedHistory.first_le_of_mem_stageDomain hv₁.le h12.le
    (hmem v₂ hv₂.le hv₂T) (hmem v₁ hv₁.le hv₁T)
  rw [hb B₀ (le_max_left _ _) k p T v₂ hle₂ hv₂ hT,
    hb'' B₀ ((le_max_right _ _).trans (le_max_right _ _)) k p T v₁ hle₁]
  exact ObservedHistory.lintegral_image_historyMinDomain_le_of_lt hle₁ hfk hfloor hT hv₁ h12
    (hmem v₁ hv₁.le hv₁T)
```

```lean
theorem historyReducedVolumeMonotone (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeMonotone P₀ := by
  intro H k p T v₁ v₂ hT hv₁ h12 hv₂T
  rcases h12.eq_or_lt with rfl | h12
  · exact le_rfl
  obtain ⟨T', hT', G, hG, hagree⟩ := H.exists_extendHorizon_gt
  have hTle : T ≤ H.horizon := (H.mem_Icc_of_mem_stageDomain' hT).2
  rw [← H.reducedVolume_extendHorizon hT'.le G hG hagree k p hTle,
    ← H.reducedVolume_extendHorizon hT'.le G hG hagree k p hTle]
  exact (H.extendHorizon T' hT'.le G hG).reducedVolume_le_of_lt_of_mem_Ico k p
    (H.mem_Ico_extendHorizon_of_mem_stageDomain hT' G hG hT)
    (H.stageDomain_extendHorizon hT'.le G hG k hT) hv₁ h12 hv₂T
```

```lean
open DifferentialGeometry.Geometry.Curvature in
theorem historyReducedVolumeLocalUpperBound (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeLocalUpperBound P₀ := by
  refine ⟨(4 * Real.pi) ^ (-(3 : ℝ) / 2) * Real.exp 36, by positivity, fun η hη => ?_⟩
  obtain ⟨R, -, htail⟩ := exists_uniform_tail_gaussian_metric.{u} (ENNReal.ofReal η)
    (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨σ, hσ, hσ1, hcore⟩ :=
    ObservedHistory.exists_lintegral_image_historyMinDomain_core_le.{u} R
  refine ⟨σ, hσ, hσ1, fun H t p r hball => ?_⟩
  obtain ⟨T', hT', G, hG, hagree⟩ := H.exists_extendHorizon_gt
  have hball' := H.isParabolicallyRmControlledBall_extendHorizon hT'.le G hG hagree t p r hball
  have hr : 0 < r := hball.1
  have hv : 0 < σ * r := mul_pos hσ hr
  have htmem : (t : ℝ) ∈ H.toHistory.stageDomain (H.toHistory.activeStage t) :=
    H.toHistory.activeStage_mem t
  have hmet := H.stageMetric_extendHorizon hT'.le G hG hagree _ htmem
  have hVeq : H.reducedVolume (H.toHistory.activeStage t) p t (σ * r) =
      (H.extendHorizon T' hT'.le G hG).reducedVolume (H.toHistory.activeStage t) p t (σ * r) :=
    (H.reducedVolume_extendHorizon hT'.le G hG hagree _ p t.2.2).symm
  rw [hVeq, ← hmet]
  obtain ⟨b, hb⟩ :=
    (H.extendHorizon T' hT'.le G hG).exists_reducedVolume_eq_lintegral_image_historyMinDomain_of_mem_Ico
  obtain ⟨b', -, hfl⟩ := (H.extendHorizon T' hT'.le G hG).exists_stageMetric_scalar_lower_bound
  set H' := H.extendHorizon T' hT'.le G hG with hH'
  set k := H.toHistory.activeStage t with hk
  set B₀ := max b b' with hB₀
  have hfloor : ∀ j, ∀ τ ∈ H'.toHistory.stageDomain j, ∀ x : (H'.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H'.toHistory.stageMetric j τ) x := fun j τ hτ x =>
    (neg_le_neg (le_max_right _ _)).trans (hfl j τ hτ x)
  have hTIco : (t : ℝ) ∈ Ico (H'.toHistory.time k) (H'.toHistory.stageEndTime k) :=
    ⟨H.toHistory.activeStage_time_le t, H.lt_stageEndTime_extendHorizon hT' G hG t⟩
  have htk' : (t : ℝ) ∈ H'.toHistory.stageDomain k :=
    H'.toHistory.activeStage_mem ⟨t.1, t.2.1, t.2.2.trans hT'.le⟩
  have hvt : (σ * r) ^ 2 ≤ t :=
    (pow_le_pow_left₀ hv.le (mul_le_of_le_one_left hr.le hσ1) 2).trans
      hball.radius_sq_le_time
  have hlow : (t : ℝ) - (σ * r) ^ 2 ∈ H'.toHistory.stageDomain
      (H'.toHistory.activeStage (projIcc 0 H'.horizon H'.horizon_nonneg (t - (σ * r) ^ 2))) := by
    have h := H'.toHistory.activeStage_mem
      (projIcc 0 H'.horizon H'.horizon_nonneg (t - (σ * r) ^ 2))
    have hv' : ((projIcc 0 H'.horizon H'.horizon_nonneg (t - (σ * r) ^ 2) : ℝ)) =
        t - (σ * r) ^ 2 := by
      rw [projIcc_of_mem _ ⟨by linarith, by
        have h1 : H'.horizon = T' := rfl
        have h2 := t.2.2
        nlinarith [sq_nonneg (σ * r), hT'.le]⟩]
    rwa [hv'] at h
  have ht0 : (t : ℝ) - (0 : ℝ) ^ 2 ∈ H'.toHistory.stageDomain k := by simpa using htk'
  have hle := ObservedHistory.first_le_of_mem_stageDomain le_rfl hv.le hlow ht0
  rw [hb B₀ (le_max_left _ _) k p t (σ * r) hle hv hTIco]
  set K := H'.toHistory.historyMinDomain hle t B₀ (σ * r) p with hK
  set g := H'.toHistory.stageMetric k t with hg
  have hsplit : H'.toHistory.historyLExp hle t (σ * r) p '' (Subtype.val ⁻¹' K) ⊆
      H'.toHistory.historyLExp hle t (σ * r) p '' (Subtype.val ⁻¹'
          (K ∩ {Z | Real.sqrt (g.inner p Z Z) ≤ R})) ∪
        H'.toHistory.historyLExp hle t (σ * r) p '' (Subtype.val ⁻¹'
          (K ∩ {Z | R < Real.sqrt (g.inner p Z Z)})) := by
    rintro _ ⟨Z, hZ, rfl⟩
    rcases le_or_gt (Real.sqrt (g.inner p Z.1 Z.1)) R with h | h
    · exact Or.inl ⟨Z, ⟨hZ, h⟩, rfl⟩
    · exact Or.inr ⟨Z, ⟨hZ, h⟩, rfl⟩
  refine (lintegral_mono_set hsplit).trans ((lintegral_union_le _ _ _).trans (add_le_add ?_ ?_))
  · exact hcore H'.toHistory ⟨t.1, t.2.1, t.2.2.trans hT'.le⟩ p r B₀ hball'
      (H.lt_stageEndTime_extendHorizon hT' G hG t) hfloor hle
  · refine (ObservedHistory.lintegral_image_historyMinDomain_tail_le hfloor hTIco hv R).trans ?_
    exact htail g p
```

## 6. Dependency-ordered bricks (each unconditional; line estimates)

| # | Brick | Home | Needs | Lines |
|---|---|---|---|---|
| G7′ | `lintegral_paramDensity_mul_le_lintegral_image` (injective `≥`, no measurability of `φ`) | `DifferentialGeometry/Analysis/Integration/Measure/Parametric/AreaInequality.lean` (sibling of G7) | Mathlib (F2) | 100 |
| TailG | `exists_uniform_tail_gaussian_metric` (metric-level, uniform in `X`); recast `lSourceGaussian_uniform_tail` as a corollary | `Perelman/LGeometry/Jacobian/SourceGaussianTail.lean` | `gaussianPosDef_uniform_tail` | 100 |
| E2a | `exists_tendsto_lVelocity_of_isLRegularizedGeodesicOn_of_closedStart` (Gronwall on a compact `M`) | `Perelman/LGeometry/Geodesic/ClosedStartCurve.lean` | G1b `ChartCurvatureRegularity` | 350 |
| X1–X3 | `exists_extendHorizon_gt`, `stageMetric_extendHorizon`, `reducedVolume_extendHorizon`, `isParabolicallyRmControlledBall_extendHorizon`, the small `lt_stageEndTime_`/`stageDomain_`/`mem_Ico_…` lemmas | `Surgery/Topology/HistoryHorizonExtension.lean` (new) | G1 `exists_isSolutionOn_extension_past_right_endpoint`, `exists_closedSlab_of_metric`; `extendHorizon` fields are `rfl` | 150 + 350 + 150 |
| M1 | `upperSemicontinuous_regularizedCost` (endpoint perturbation in the stage-`first` piece) | `Surgery/Topology/HistoryAction/…` (new file beside `AbsoluteContinuity`) | H1 splice/AC joins, H0 floor | 350 |
| M3 | `absolutelyContinuousOnInterval_historyLCurve`, `regularizedExtendedAction_historyLCurve_eq_historyLAction_of_mem` | `HistoryLGeometry/MinDomain.lean` sibling | `absolutelyContinuousOnInterval_of_contMDiffOn`/`_piecewise_Iic`, windows; E2a-type velocity bound at `v` | 250 |
| CF | `exists_common_flow_past_time_of_parabolicallyRmControlledBall` (route (B)) | `Surgery/Topology/HistoryParabolicBall.lean` sibling | existing `:737/:860` construction, stage slab past `t` (`t < stageEndTime`), seam flow when `t = time k` | 350 |
| SB1 | `exists_historyLExp_eq_of_mem_regularMinimizerEndpoints_of_mem_Ico` and the `RetainedCoreHistory` corollary `…_of_mem_Ico` | `HistoryLGeometry/MinDomain.lean` sibling | H2b seam window with `u = w = 0` (H3a's 80-line note) | 200 |
| SB2 | `injOn_historyLExp_of_lt_of_mem_Ico` | `HistoryLGeometry/Truncation.lean` sibling | SB1's base window, `mfderiv` of the seam map | 150 |
| E | `exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain` (open `U ⊆ domain`, C¹ `f`, continuous action `L`; interior, closed-start and seam-base cases) | `HistoryLGeometry/ExponentialSmooth.lean` sibling | H3b, H3b′ families, G1b `exists_lPhaseFlow_of_start`, G1c, E2a (H3b item 4) | 800 |
| M | `measurableSet_historyMinDomain` | with E | E, M1, M3 | 120 |
| H7b | window derivative `(log ℓJ)' ≤ 0` (running lane) | `HistoryLGeometry/JacobianMonotone` | H6, H7a, G5 | (lane) |
| H7b+ | `historyReducedJacobian_le_of_le` (seam values, closed-start end, seam base) | same | H7b, E, H7a | 400 |
| SB3 / Gauss | H7c on the glued seam base window; `historyReducedJacobian_le_gaussian` | `HistoryLGeometry/JacobianLimit` sibling | H7c, H7b+ | 250 |
| T9 | `lintegral_image_historyMinDomain_tail_le` | `HistoryLGeometry/ReducedVolumeUpperBound` | E, M, Gauss, G7 | 150 |
| C9 | `exists_lintegral_image_historyMinDomain_core_le` | same | CF, G6, G8, H3a uniqueness, `LocalIsometry`, `restrictOpen` volume | 600 |
| H8 | `lintegral_image_historyMinDomain_le_of_lt`, `reducedVolume_le_of_lt_of_mem_Ico`, `historyReducedVolumeMonotone` (proofs in §5.5) | `HistoryLGeometry/ReducedVolumeMonotone` | G7, G7′, E, M, H7b+, SB1, SB2, H5, X1, X2 | 150 |
| H9 | `historyReducedVolumeLocalUpperBound` (proof in §5.5) | `HistoryLGeometry/ReducedVolumeUpperBound` | C9, T9, TailG, SB1, X1–X3 | 100 |

Parallel wave 1 (no dependencies among them): G7′, TailG, E2a, X1–X3, M1, M3, CF, SB1, SB2. Wave 2: E (needs
E2a), then M. Wave 3: H7b+ (after the H7b lane and E), SB3/Gauss. Wave 4: T9, C9. Wave 5: H8, H9.
Total new ≈ 5,300 lines (excluding the running H7b lane).

The leaf names `historyReducedVolumeMonotone` / `historyReducedVolumeLocalUpperBound` (same
namespace) are the skeleton's `sorry` stubs at `Surgery/Skeleton/PoincareEndgame.lean:22,26`: the H8/H9
files define them and the stubs are deleted in the same commit. Every other new public name above was chosen by conclusion. Before landing, grep each one
library-wide; the probe compiled them next to the full `JacobianUnconditional` closure with no clash.
