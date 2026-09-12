# BackgroundJetTransfer — discharging `hback` of the neck transport

Lane `CanonicalNeighborhood/`, book `ch:scn` (`master05b.tex`), namespace
`DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.Chapter25`.
Consumer: `ComparisonComposition.lean` (`TransportedErrorTower`, `MetricComparisonOn.trans`,
`StrongNeck.transport`).  Nothing in `ComparisonComposition.lean` was edited.

## What the module establishes

`ComparisonComposition.lean` isolates one analytic input of the composition
`cyl ≈ model ≈ source`, the hypothesis `hback` of `TransportedErrorTower.ofPullbackCross`:
the spatial covariant jets of a two-tensor measured in the cylinder background `h s` are bounded
by `K` times the same jets measured in the pulled-back model background `Phi^* (k s)`.

The estimate is the native `iterated_covariant_derivative_norm_comparison_bound`
(`Geometry/Compactness/CheegerGromov/Estimates/CovariantDerivativeNormComparison.lean`, L48),
used twice:

1. `g := g₁`, `gRef := h`, `T := metricTensorField g₁ - metricTensorField h`, `eps := 2α`.
   Its `hgK` asks for `h`-jets of `g₁`, which are the `h`-jets of the difference field
   (`iterCov h 2 (metricTensorField h) (j+1) = 0`, `iterCov_metric_zero`).  Output: the
   `g₁`-jets of the difference, hence (up to a sign, `normSq0S_neg`) the `g₁`-jets of `h`,
   with the inflated tolerance `ε₂ := backgroundJetBudget E' order * α`.
2. `g := h`, `gRef := g₁`, `T := T`, `eps := ε₂`.  Its `hgK` is exactly the output of step 1.

Bridge between the two towers: `tensor02CovDerivNormWith a A g g y`
(`ApproximateIsometry/MetricApproximationDefs.lean` L76, via `metricCovDerivStep`) equals
`√(normSq0S g y (2+a) (iterCov g 2 A a y))` — this is the existing
`HCGCompactness.t02Norm_eq_iterCov` (`ApproximateIsometry/PullbackTowerBounds.lean` L142), fed
with an orthonormal basis from `exists_gOrthonormalBasis` + `metricInverseInBasis_of_orthonormal`.
No new induction on `a` was needed.

## Two facts that shape the public statements

**(1) The estimate is not jet-by-jet.**  The comparison lemma's conclusion carries the full
lower-order sum `∑_{k < r}` on the right; it cannot be absorbed at the same single order.  The
delivered bound is therefore

```
‖∇^a_h T‖_h ≤ backgroundJetConstant E' order * ∑_{k ≤ a} ‖∇^k_{g₁} T‖_{g₁}.
```

Consequently `TransportedErrorTower.ofPullbackCross` is **not** usable (its `hback` argument
compares order `a` with order `a`).  Instead `TransportedErrorTower.ofPullbackCross_of_close`
builds the same structure directly: `tower`, `zero_eq`, `succ_eq` and `differentiableWithinAt` are
the same proofs as in `ofPullbackCross` (pullback of the model-to-source error jets, its
evaluation identity and the time recursion), and `close` is proved from the change of background
plus `tensor02CovDerivNormWith_pullbackTensor02FieldCross` and `c.close j b` for every `j ≤ a`.
Since all model jets of order `≤ order` are bounded by the same `eps`, the sum costs only the
factor `order + 1`, and the tower's constant is
`backgroundJetConstant E' order * (order + 1)`.  No modified structure and no
`MetricComparisonOn.trans'` were needed: the `close` field of the existing `TransportedErrorTower`
already has the shape `≤ K * eps`.

**(2) `α ≤ 1/4` is not enough.**  The comparison constant
`metricCovariantDerivativeComparisonConstant (E := E') 2 order` grows with `order`, and step 1
inflates `α` by roughly `√((3/2)^(2+order)) * (1 + Cc * order)`.  Step 2 requires its own
`eps ≤ 1`, so the tolerance of the `cyl ≈ model` comparison must be small *relative to the
order*.  The threshold is made explicit as

```
backgroundJetBudget   E' order = √((3/2)^(2+order)) * (1 + Cc * order) + 2
backgroundJetSmallness E' order = min (1/4) (backgroundJetBudget E' order)⁻¹
backgroundJetConstant  E' order = √(2^(2+order)) * (1 + Cc)
```

with `Cc = metricCovariantDerivativeComparisonConstant (E := E') 2 order`.  The `+ 2` in the
budget guarantees `ε₂ ≥ 2α`, which is what makes the `(1-α)/(1+α)`-form equivalence of
`MetricComparisonOn` imply the `(1+eps)⁻¹`-form equivalence required by the comparison lemma in
both directions (note `(1+α)⁻¹ ≥ 1-α`, so the naive `eps := α` does **not** work; `eps := 2α` is
the smallest convenient choice for `α ≤ 1/4`).

## Locality

`MetricComparisonOn.pullback_eq` holds only on the comparison set `U`, so `c₁.jet 0 s` agrees with
`metricTensorField (Phi^* (k s)) - metricTensorField (h s)` only on `U`.  Covariant jets are
local, and the lane already has the exact lemma:
`Chapter25.tensor02CovDerivNormWith_eq_on_closure` (`WitnessClosedBallJets.lean` L96) with
`U ⊆ closure U`.  This is why `ofPullbackCross_of_close` takes `hU : IsOpen U`.
`jet_zero_eq_metric_difference` records the pointwise identity on `U`.

## Inherited restrictions (not introduced here)

* The cylinder-to-model chart must agree with a **global** diffeomorphism
  `Phi : N ≃ₘ⟮J, I3⟯ P` (`hG : ∀ y, G y = Phi y`).  This is exactly the restriction of
  `TransportedErrorTower.ofPullbackCross`; `pullbackTensor02FieldCross` and
  `Diffeomorph.pullbackMetricCross` are defined for global diffeomorphisms only.
* The time-differentiability input `hdiff` of `ofPullbackCross` is kept verbatim.
* `StrongNeck.transport_of_comparisons` inherits `hjet` (time differentiability of the model
  neck's own comparison jets) from `StrongNeck.transport`, and fixes the model-to-source
  comparison's time set to `Set.Icc (-1) 0`, since `TransportedErrorTower` shares its time set
  with the comparison it transports.

## Verification

```
LEAN_NUM_THREADS=2 lake env lean \
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/BackgroundJetTransfer.lean
```

run from the repository root.  Final run on the complete file: **empty output, 62 s** (single
`lean.exe`, two threads; two earlier runs of intermediate states: 38.3 s and 55.4 s).  No `sorry`,
no `nolint`, no `maxHeartbeats`/`maxRecDepth`/`skipKernelTC`, no `set_option backward.*`, no
`show`.  Only the four `import` lines exceed 100 characters (module paths).

**Axiom audit.**  Run without an artifact refresh, by elaborating a scratch copy of the file with
`#print axioms` appended for each of the 18 public declarations
(`…/scratchpad/BackgroundJetTransferAudit.lean`, 42 s).  All 18 report exactly

```
[propext, Classical.choice, Quot.sound]
```

so the whole module is **standard-axioms-only**: no `sorryAx` is inherited from
`ComparisonComposition`, `WitnessClosedBallJets`, `MetricApproximationHigherDerivatives`,
`PullbackTowerBounds` or `CovariantDerivativeNormComparison`.  Reproduce by copying the file,
inserting `#print axioms <fully qualified name>` lines before the closing `end <namespace>`, and
running `lake env lean` on the copy; no `.olean` for this module is needed.

The file is not imported by `DifferentialGeometry.lean` and no artifact was refreshed, so the
module has no `.olean` yet; a named refresh is still required before any downstream file can
import it.

**Host note (diagnosed, worth keeping).**  `lake env lean` intermittently aborts at import time
with `failed to read file '….olean.private'` (a toolchain or Mathlib olean, varying file).  The
cause is *commit charge*, not physical RAM: while another worker's `lean.exe` holds ~7.4 GB of
commit, `Win32_OperatingSystem.FreeVirtualMemory` drops to ~0.2 GB of a 51 GB commit limit and
the olean memory maps fail.  Physical free RAM at the same moment was ~4.7 GB of 31.5 GB, so the
usual RAM check does not detect it.  Diagnostic:

```powershell
Get-CimInstance Win32_OperatingSystem |
  Select-Object @{n='CommitFreeGB';e={[math]::Round($_.FreeVirtualMemory/1MB,2)}}
Get-Process | Sort-Object PagedMemorySize64 -Descending | Select-Object -First 5 Name,Id,
  @{n='CommitGB';e={[math]::Round($_.PagedMemorySize64/1GB,2)}}
```

Wait until `CommitFreeGB` is a few GB and rerun; the check then succeeds unchanged.

## Public declarations

Constants and their elementary properties: `backgroundJetBudget`, `backgroundJetSmallness`,
`backgroundJetConstant`, `two_le_backgroundJetBudget`, `backgroundJetBudget_pos`,
`backgroundJetSmallness_le_quarter`, `backgroundJetSmallness_le_inv`,
`backgroundJetSmallness_pos`, `two_le_backgroundJetConstant`, `backgroundJetConstant_pos`.

Jet algebra: `tensor02CovDerivNormWith_eq_sqrt_normSq0S_iterCov`,
`iterCov_metricTensorField_succ_eq_diff`, `iterCov_metricTensorField_succ_eq_neg_diff`.

Main results: `tensor02CovDerivNormWith_le_of_metric_close`, `jet_zero_eq_metric_difference`,
`TransportedErrorTower.ofPullbackCross_of_close`, `StrongNeck.transport_of_comparisons`,
`SpatialNeck.transport_of_comparisons`.

`SpatialNeck.transport_of_comparisons` is the sharpest endpoint of the module: the comparison time
set is `{0}`, so `hdiff` collapses to `DifferentiableWithinAt.singleton` and the statement carries
no differentiability hypothesis at all — only the two explicit smallness conditions, the
`hcore`/`hVsource`/`hbase` bookkeeping of `SpatialNeck.transport`, and the global-diffeomorphism
agreement `hPhi`.

## Open next steps for this slot

* The `order`-dependence of `backgroundJetSmallness` is real: for the buffered neck,
  `order = ⌈(2α)⁻¹⌉₊` grows as `α → 0`, so `α ≤ backgroundJetSmallness _ ⌈(2α)⁻¹⌉₊` is a genuine
  constraint on the pair, not an automatic consequence of `α` being small.  If a consumer needs
  it for arbitrary small `α`, the comparison constant's growth in `p` (through
  `iteratedRecurrenceConstant` / `inverseContractionRecurrenceConstant`) has to be examined; the
  estimate as delivered does not settle that.
* Removing the global-diffeomorphism restriction requires a partial-diffeomorphism version of
  `pullbackTensor02FieldCross` / `Diffeomorph.pullbackMetricCross`, which is upstream work in
  `KappaSolutions/CrossModelTensorPullback.lean` and `Geometry/Metric/PullbackCross.lean`.
