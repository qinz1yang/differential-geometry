# SelectedCountersequenceAdapter.lean — note (book25 Chapter 25, decision D4, worker W-O)

Claude's initial source is committed in fd5979f97. Current review follow-up is
verified: focused91 EMPTY (28.02s), named lint build91 (35.81s), fresh external
audit91 (19.14s), all16 public declarations standard-only. The leaf is registered.
The source hash is b6c8b67d403175d788e95eacdb764c3dca001d74593f9b5baa9b642efc17767b.
Receipts: E:/lean-tools/chapter25-terminal-local-20260909/claude-review-completion.json.

The adapter now imports Chapter25Convergence and ClosedBadPointSelection directly.
The unchanged ClosedModelHypotheses, closed_bad_point_selection,
ModelRadiusWorksClosed and SelectedCountersequence declarations have moved here,
so Chapter25Theorems can import this adapter without an import cycle. Their
public names are unchanged. The specialized original theorem is wired directly
to the adapter and freshly audits standard-only.

Target: decision D4 of `CANONICAL_NEIGHBORHOOD_PLAN.md` §2, i.e. the adapter
`Chapter25Theorems.selected_countersequence_of_radius_failure`
(`lem:scn-bad-point-selection` + `eq:scn-selected-normalization` on closed source
windows). The endpoint here is `selected_countersequence_of_radius_failure'`.

## 0. Status in one line

The OrientedWitnessRestriction input is removed. WindowedWitnessRestriction's
orientedWitness_mono_closed proves the required closed-source specialization,
using interior metric coefficient smoothness and interval germs at the terminal
endpoint. No new terminal regularity hypothesis is needed. ConnectedSpace
was added to ModelRadiusWorksClosed by Claude, so the duplicate connected
predicate and ConnectedSourceReduction have been removed. Positivity of kappa
and sigma and admissibility of Phi were used only by the removed reduction;
they are not needed by normalization and were removed from both normalization
entry points, with the actual caller updated. They remain hypotheses of the
abstract model theorem, which consumes them in the later geometric argument.

The verification and two-interface discussion below are the original worker
record; BOTH additional interfaces are superseded by this review. The new
receipts above certify the current source. The generic arbitrary-D stability
card remains open and is no longer a normalization dependency.

## 1. Verification

The only command run, from `E:/differential-geometry-dev` (no `lake build`, `lake-locked`,
`clean` or `update` at any point):

```
LEAN_NUM_THREADS=1 lake env lean \
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/SelectedCountersequenceAdapter.lean
```

Result: exit 0, **no output — zero errors, zero warnings**, 39 s wall time. The only
`set_option` in the file is `autoImplicit false`; no `sorry`, no `nolint`, no
`maxHeartbeats`/`maxRecDepth`/`linter…`, no `show` tactic, no `letI`. A temporary
`#print axioms` block (since removed) reported, for
`selected_countersequence_of_radius_failure'`, `orientedWitness_paraSolution_iff`,
`orientedWitness_timeRestrict`, `orientedWitness_of_timeRestrict`,
`spatiallyKappaNoncollapsed_timeRestrict` and `nonempty_closedModelCounterexample`, each

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. no `sorryAx`: nothing in this file goes through the `sorry`s of
`Chapter25Theorems.lean` (in particular `oriented_witness_mono` is *not* used; it is
replaced by the hypothesis `OrientedWitnessRestriction`, §4.1).

Note on the shared checkout: two runs failed with transient
`failed to read file '…\*.olean.private'`, and one with
`object file '…ModelWitness.olean' … does not exist`, while another session was running a
`lake` build that was rewriting oleans under `.lake/build`. These are workspace collisions,
not proof failures; the checks above were rerun to completion after that build finished.

## 2. Declarations

### Upstream candidates (section `Upstream`)

These are the real content of the brick. All are stated for a general source flow on a
general `RealTimeInterval`; none mentions the countersequence.

| Declaration | Content |
|---|---|
| `scalar_timeRestrict` | `(S.timeRestrict D').scalar = S.scalar` (`rfl`) |
| `WindowedModelWitness.timeRestrict` | a windowed witness survives shrinking the flow interval, given `t ∈ D'.carrier` and the model window `[t − (εR)⁻¹, t] ⊆ D'.carrier` |
| `WindowedModelWitness.ofTimeRestrict` | the converse, given `D'.carrier ⊆ D.carrier` |
| `WindowedModelWitness.parabolic` / `.ofParabolic` | the windowed witness under `paraSolution`, both directions |
| `orientedWitness_paraSolution_iff` | **the invariance lemma**, see §3 |
| `orientedWitness_timeRestrict`, `orientedWitness_of_timeRestrict` | the interval half, for `OrientedWitness` |
| `spatiallyKappaNoncollapsed_timeRestrict` | `SpatiallyKappaNoncollapsedBelowScale` restricts to a smaller flow interval |

Suggested homes: the four `WindowedModelWitness` transports and the three
`orientedWitness_*` lemmas belong next to `WindowedModelWitness` / `OrientedWitness` in
`Chapter25Geometry.lean` (they are the Chapter-25 windowed analogue of
`WitnessParabolicTransport.lean`, which does exactly this for `KappaModelWitness` /
`ModelComparison`); `spatiallyKappaNoncollapsed_timeRestrict` belongs in
`Perelman/Noncollapsing/Predicates.lean` next to `para_spatial_noncollapse`;
`scalar_timeRestrict` belongs in `Solution/Restriction.lean`.

### Interfaces, bundle and endpoint

| Declaration | Content |
|---|---|
| `OrientedWitnessRestriction` | interface, = `Chapter25Theorems.oriented_witness_mono` |
| `ModelRadiusWorksClosedConnected` | `ModelRadiusWorksClosed` with `[ConnectedSpace M]` added |
| `ConnectedSourceReduction` | interface: a radius counterexample can be taken connected |
| `ClosedModelCounterexample` | the negation of `ModelRadiusWorksClosedConnected` at one radius, bundled with the manifold and its six instances |
| `nonempty_closedModelCounterexample` | proved: failure ⟺ a bundle exists |
| `adapterDepth`, `adapterRadius` (+ 6 private lemmas) | the chosen half depths `H_n = max(modelDepth small, n)` and radii `r_n = min(√ε, 1/(8H_n+1))` |
| `selected_countersequence_of_radius_failure'` | the endpoint |

## 3. The invariance lemma

This is what the brick is about, and it is the only place where the windowed model witness
of Chapter 25 is really used. Exact statement:

```lean
theorem orientedWitness_paraSolution_iff (S : SolutionOn (I := I3) (M := M) D)
    (o : TangentOrientationSection M) {tau A : ℝ} (hA : 0 < A) (htau : tau ∈ D.carrier)
    (s : ℝ) (x : M) (eps kappa : ℝ) :
    OrientedWitness (paraSolution S tau A hA htau) o eps kappa x s ↔
      OrientedWitness S o eps kappa x (paraTime tau A s)
```

with `M` a three-manifold (`[TopologicalSpace M] [ChartedSpace ThreeSpace M]
[IsManifold I3 ∞ M]`; `T2Space`/`SigmaCompactSpace` are `omit`ted, they are not needed).

Proof, in both directions: the ancient model `W.model`, its embedding `W.embedding`, the
buffered ball, `base_map` and the entire `MetricComparisonOn` are **kept unchanged**, so the
orientation clause of `OrientedWitness` transports verbatim — the transported witness has
`.model` and `.embedding` definitionally equal to the old ones. The two things that do move:

* the normalization scale, `R̂(x,s) = A⁻¹ R(x, τ + s/A)` (`paraSolution_scalar`), so that
  `rescaledMetric (paraSolution S τ A) s (R̂ x s) = rescaledMetric S (paraTime τ A s) (R x t)`
  as families of metrics — this is the existing `rescaledMetric_paraSolution` of
  `WitnessParabolicTransport.lean` ("a rescaling of a rescaling is a rescaling"), the same
  identity that `KappaModelWitness.parabolic` uses;
* the admissibility window `time_mem` / `window_mem`, which is carried across by the
  affine maps `paraTime`/`paraBack` (`paraTime_window_start`, a private copy of the
  identically named private lemma of `WitnessParabolicTransport.lean`). For
  `paraSolution` alone this is painless because
  `(paraInterval D τ A hτ).carrier = {s | paraTime τ A s ∈ D.carrier}` holds by `rfl`.

The genuinely new half compared to `WitnessParabolicTransport.lean` is the **flow-interval
restriction**, `orientedWitness_timeRestrict` / `orientedWitness_of_timeRestrict`: the
normalized source lives on `RealTimeInterval.closed (−2H) 0`, which is strictly smaller than
the full rescaled interval `paraInterval`. Restricting is *not* symmetric — it strengthens
`window_mem` — so the two directions have different hypotheses:

* going **down** to the smaller interval needs `t ∈ D'.carrier` and
  `Icc (t − (ε R)⁻¹) t ⊆ D'.carrier`;
* going **up** needs only `D'.carrier ⊆ D.carrier`.

That asymmetry is exactly what the past buffer of `NormalizedSequence` pays for; see §5.

## 4. The two interfaces, and why they are needed

### 4.1 `OrientedWitnessRestriction` (`lem:scn-model-witness-stability`, restriction half)

```lean
def OrientedWitnessRestriction : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] [SigmaCompactSpace M] (D : RealTimeInterval)
    (S : SolutionOn (I := I3) (M := M) D), IsSolutionOn S →
      ∀ (o : TangentOrientationSection M) (delta eps kappa : ℝ),
        0 < delta → delta ≤ eps → eps < 1 → ∀ (x : M) (t : ℝ),
          OrientedWitness S o delta kappa x t → OrientedWitness S o eps kappa x t
```

Wiring, once `oriented_witness_mono` is proved (one line, no change to my statement):

```lean
fun M _ _ _ _ _ D S hS o delta eps kappa hd hde he x t hw =>
  oriented_witness_mono S hS o hd hde he hw
```

**Why it is unavoidable.** The hypothesis of the endpoint is the failure of
`ModelRadiusWorksClosed` at tolerance `eps`, and the conclusion is a countersequence at
tolerance `small ≤ eps`. `SelectedCountersequence small` needs `bad` *and* `higher_good` at
`small`, so the closed selection has to be run at `small` (this is what the book does), and
its seed must be a `small`-bad point. The only bridge between the two tolerances in the
whole statement is `small`-goodness ⟹ `eps`-goodness, i.e. exactly
`oriented_witness_mono`. There is no route around it.

**Why the tree does not have it.** `oriented_witness_mono` is `sorry` in
`Chapter25Theorems.lean` (plan §5, row 14, "Open adapter"). It is a real obstruction, not an
oversight: `MetricComparisonOn.jet_succ` pins the time jets by
`derivWithin _ times s` with `times = Icc (−modelDepth eps) 0`, and this set *shrinks* with
`eps`. For `s` in the interior of the old window the two `derivWithin`s agree, but at the
new left endpoint `s = −modelDepth eps ∈ Ioo (−modelDepth delta) 0` the old identity gives a
two-sided `derivWithin` while the new one asks for a one-sided one; without differentiability
of `s ↦ jet b s y v` at that point the two are unrelated (`derivWithin` is `0` for a
non-differentiable function). This is precisely the trap recorded in plan §4:
"`RealTimeInterval` does not identify its regular subset with the carrier interior; window
inclusion alone does not justify derivative restriction at new endpoints."
`KappaModelWitness.mono` (proved, `ModelWitness.lean`) is *not* affected because
`ModelComparison.jet_succ` differentiates over the **fixed** set `Set.Iic 0`. Closing
`oriented_witness_mono` therefore needs time regularity of the jets, i.e. all-order
smoothness in time of both flows — that is its own brick, not part of this adapter.

### 4.2 `ConnectedSourceReduction` (a statement repair, recommended)

`NormalizedSequence.connected : ∀ i, ConnectedSpace (term i).M` is a field of the target,
but neither `ModelRadiusWorksClosed` nor `ClosedModelHypotheses` assumes the source manifold
is connected, so the counterexample produced by `failure` need not be connected and the
field cannot be filled. This file therefore defines

```lean
def ModelRadiusWorksClosedConnected (eps kappa sigma : ℝ) (Phi : ℝ → ℝ) (r : ℝ) : Prop
```

— literally `ModelRadiusWorksClosed` with `[ConnectedSpace M]` inserted — and the interface

```lean
def ConnectedSourceReduction : Prop :=
  ∀ (eps kappa sigma : ℝ) (Phi : ℝ → ℝ), 0 < eps → eps < 1 → 0 < kappa → 0 < sigma →
    AdmissiblePinchingFunction Phi → ∀ r : ℝ, 0 < r →
      ¬ ModelRadiusWorksClosed.{u} eps kappa sigma Phi r →
        ¬ ModelRadiusWorksClosedConnected.{u} eps kappa sigma Phi r
```

Mathematically this is "pass to the connected component of the bad point": the component of
a point in a manifold is open and closed, hence again a complete, `Φ`-almost nonnegative,
`κ`-noncollapsed 3-dimensional Ricci flow with the same compact-slab curvature bounds, and
`OrientedWitness` transports because the model window and the source capture ball of a
witness stay inside one component. The tree has **no restriction of a `SolutionOn` to an open
submanifold** (`Solution/Components.lean` is about Ricci-evolution components in a frame, not
about connected components), so building this would be a separate file.

**Recommended repair, which removes this interface entirely**: add `[ConnectedSpace M]` to
`ModelRadiusWorksClosed` in `Chapter25Theorems.lean` — my
`ModelRadiusWorksClosedConnected` then *is* the tree's definition, `ConnectedSourceReduction`
becomes `fun _ _ _ _ _ _ _ _ _ _ _ h => h` and can be dropped. This is in the spirit of
D4, which already asks for `ModelRadiusWorksClosed` to be restated. It weakens
`abstract_model_theorem`'s conclusion to connected sources, which is what its downstream
consumers (all of which run on a fixed connected flow) need.

The standing hypotheses `0 < eps`, `eps < 1`, `0 < kappa`, `0 < sigma`,
`AdmissiblePinchingFunction Phi` are carried *inside* the two interfaces (as
`SelectedSequenceEventuallyGood` does in `ModelTheorem.lean`), so that every hypothesis of
the endpoint statement is consumed and the file has no unused-variable warnings.

## 5. How each field of `SelectedCountersequence` is discharged

Notation: `H_n = adapterDepth small n = max (modelDepth small) n`,
`r_n = adapterRadius eps small n = min (√ε, 1/(8H_n+1))`,
`C_n` the counterexample bundle at radius `r_n`, `(x_n, t_n)` the selected bad point,
`Q_n = R(x_n, t_n)`, and `term n` the parabolic rescaling
`(paraSolution C_n.S t_n Q_n).timeRestrict (RealTimeInterval.closed (−2H_n) 0)`.

Numerics. `r_n ≤ 1/(8H_n+1)` and `8H_n+1 ≥ 1` give `8H_n + 1 ≤ r_n⁻²`
(`adapterDepth_le_threshold`), hence `8H_n + 1 ≤ Q̂_n ≤ Q_n`. So no index shift is needed
anywhere: for **every** `n` the selection is admissible (`2H_n ≤ Q̂_n/4`), `Q̂_n > 0`, and
`Q_n ≥ 8H_n + 1 ≥ 8n + 1`, which is `scale_tendsto`. `H_n ≥ n` gives `depth_tendsto`, and
`H_n ≥ modelDepth small` is `depth_buffer` by construction.

| Field | Source |
|---|---|
| `interval`, `carrier_eq`, `regular_eq` | `RealTimeInterval.closed (−2H_n) 0`; both `rfl` |
| `term`, `isSolution` | `paraSol` + `isSoln_timeRestrict`; the carrier/regular inclusions are the images of the selection's `window_subset` under `paraTime` (`hcarSub`/`hregSub`), the regular one using `0 ≤ t_n − 2H_n/Q_n` and `t_n ≤ T_n` |
| `depth`, `scale`, `depth_pos`, `scale_pos`, `depth_buffer`, `depth_tendsto`, `scale_tendsto` | `adapterDepth` / `Q`, numerics above |
| `connected`, `orientation` | fields of the bundle |
| `complete` | `ClosedModelHypotheses.complete` + `RiemannianMetricComplete.of_lower` with `c = Q_n` (`scaleMetric_inner` makes the required inequality an equality, so `le_rfl`); `MetricComplete (F.atTime t)` is then definitionally `RiemannianMetricComplete.complete`, as in `Estimates/Shi/CompactSlab.lean` |
| `source_bound` | `ClosedModelHypotheses.curvature` on `[0, T_n]` + `paraRmNormSq` (`|Rm|̂² = Q⁻² |Rm|²`); the eigenvalue bridge `RmNormFromEigenvalues` is **not** needed, the closed hypotheses already give a tensor bound |
| `base_one` | `scalar_timeRestrict`, `paraSolution_scalar`, `paraTime_zero`, `inv_mul_cancel₀` |
| `noncollapse` | `para_spatial_noncollapse` (scale `√Q_n · σ`) + `spatiallyKappaNoncollapsed_timeRestrict` |
| `pinching` | `phiAlmostNonnegative_paraSolution` with `rescalePinchingFunction Q_n Phi`, restricted along `hcarSub` |
| `higher_good` | see below |
| `bad` | `orientedWitness_of_timeRestrict` + `orientedWitness_paraSolution_iff` + `paraTime_zero`, against the selection's `bad` at tolerance `small` |

The **scalar bound** that `closed_bad_point_selection` needs (`∀ y s ∈ [0,T], R ≤ K`) is not
a field of `ClosedModelHypotheses`; it is derived from the tensor bound
`ClosedModelHypotheses.curvature` through `Geometry.Curvature.scalar_abs_le_rm`
(`|R| ≤ n² |Rm|`), with `K = (finrank ℝ ThreeSpace)² √C`.

`higher_good` is where the past buffer is spent. A point of the rescaled flow at
`s ∈ [−H_n, 0]` with `R̂ ≥ 2` has `R ≥ 2Q_n` at `paraTime t_n Q_n s ∈ [t_n − H_n/Q_n, t_n]`,
so the selection's `higher_curvature_good` (which holds on the doubled window
`[t_n − 2H_n/Q_n, t_n]`) applies; transporting the witness *down* to
`RealTimeInterval.closed (−2H_n) 0` then needs its model window inside `[−2H_n, 0]`, and
that window has length `(small · R̂)⁻¹ ≤ (2·small)⁻¹ ≤ modelDepth small ≤ H_n`, so
`s − (small R̂)⁻¹ ≥ −H_n − H_n = −2H_n`. This is exactly the invariant recorded in plan §4
("a normalized source lives on `[-2*depth,0]`; higher-curvature goodness is on
`[-depth,0]`, with `modelDepth eps <= depth`. Preserve the past buffer") and it is the
reason the closed selection is run with input depth `2H_n`, not `H_n`.

## 6. What the reviewer has to do

1. Register the import in `DifferentialGeometry.lean` and refresh the module (needs an
   exclusive window; the file was only focus-checked).
2. Decide on the `ConnectedSpace` repair of `ModelRadiusWorksClosed` (§4.2). If taken, drop
   the `reduction` binder and `ModelRadiusWorksClosedConnected` from this file.
3. Once `oriented_witness_mono` is proved, drop the `restriction` binder with the one-line
   wiring of §4.1; `selected_countersequence_of_radius_failure` in `Chapter25Theorems.lean`
   is then `selected_countersequence_of_radius_failure'` verbatim.
4. Move the `Upstream` section down as suggested in §2.
