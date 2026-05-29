import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSDiffWkpNormEnergyBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedRegularityHigherQuant

/-!
# Sharp `eLpNorm` bound for the differentiated chart right-hand side, in
chart-component data

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P₀`, a level `m`, and a direction multi-index
`l : Fin m → Fin n`, the level-`m` differentiated chart right-hand side
`eigenvectorChartRHSDiff g r s h_atlas i α P₀ m l` has, by the energy-bound
chain `eigenvectorChartRHSDiff_wkpNorm_le_uniform` at `K = 0` paired with
`diffRHSAggregate_le_energy_perK`, a sharp `eLpNorm` bound

```
eLpNorm (eigenvectorChartRHSDiff … m l) 2 (volume.restrict (chartTargetEuclid α))
  ≤ ENNReal.ofReal (C · μ⁻¹^e) · ENNReal.ofReal ‖tensorResolventEigenbasisVec …‖
```

driven by uniform `wkpNorm`-graded chart-component energy hypotheses on each of
the seven primitive source atoms — the eigenvector chart component itself, and
the six per-limit resolvent / partial / component / cross-right / cutoff data.

The iterated-weak-partial bound that `diffRHSAggregate_le_energy_perK` requires
is derived from the chart-component per-K-family hypothesis via the polymorphic
bridge `eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp`, combined with
`wkpNorm`-monotonicity in the order: for any direction count `j ≤ m + 1`, the
`j`-fold mixed weak partial at order `2 + K'` is bounded by the chart component
at order `(K' + m + 3)` (the maximum order needed in the recursion).

The constant `C` is geometric (it depends on `g r s h_atlas α P₀ m l` and on
the constants supplied by the input hypotheses); the exponent `e : ℕ` is
likewise geometric. The eigenvalue factor `μ⁻¹^e` is the only `i`-dependent
piece, and the abstract `L²` norm `‖tensorResolventEigenbasisVec …‖` is
likewise the only abstract right-hand side factor.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Iterated-partial per-K-family from chart-component per-K-family

The energy aggregate bound `diffRHSAggregate_le_energy_perK` consumes a
`j ≤ m + 1`-restricted per-K-family hypothesis on the iterated weak partials of
the eigenvector chart component:

```
∀ i j (hj : j ≤ m + 1) idx K',
  wkpNorm (2 + K') 2 (eigenvectorChartIteratedPartial … j idx)
      (chartTargetEuclid α)
    ≤ ENNReal.ofReal (Citer K' · μ⁻¹^eIter K') · ofReal ‖vec_i‖.
```

For any `j ≤ m + 1` and any `K'`, the polymorphic bridge gives:

* `wkpNorm (2 + K') 2 (partial j idx) ≤ wkpNorm ((2 + K') + j) 2 (chart cpt)`
  via `eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp`;
* `wkpNorm ((2 + K') + j) 2 (chart cpt) ≤ wkpNorm (K' + m + 3) 2 (chart cpt)`
  via `wkpNorm_mono_order` (since `j ≤ m + 1` implies `2 + K' + j ≤ K' + m + 3`);
* `wkpNorm (K' + m + 3) 2 (chart cpt) ≤ ENNReal.ofReal (Ceig (K' + m + 3) ·
    μ⁻¹^(eEig (K' + m + 3))) · ofReal ‖vec_i‖` by the chart-component per-K-family
  hypothesis at order `K' + m + 3`.

Setting `Citer K' := Ceig (K' + m + 3)` and `eIter K' := eEig (K' + m + 3)`
yields the desired bound. -/

omit [CompleteSpace E] in
/-- **Iterated-partial per-K-family bound from chart-component per-K-family
bound.** For a fixed differentiation level `m`, every `j ≤ m + 1`-fold mixed
weak partial of the eigenvector chart component has, at every order `2 + K'`,
a `wkpNorm`-bound

```
wkpNorm (2 + K') 2 (eigenvectorChartIteratedPartial … j idx) (chartTargetEuclid α)
  ≤ ENNReal.ofReal (Ceig (K' + m + 3) · μ⁻¹^(eEig (K' + m + 3))) · ofReal ‖vec_i‖,
```

derived from the chart-component per-K-family bound `hCeig_bd` at order
`K' + m + 3` via the polymorphic bridge
`eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp` and `wkpNorm`-order
monotonicity. -/
private lemma iteratedPartial_wkpNorm_le_of_chart_perK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ)
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
      j ≤ m + 1 →
      ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Ceig (K' + m + 3) *
              (i.fst.val)⁻¹ ^ (eEig (K' + m + 3))) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  intro i j hj idx K'
  -- Step 1: chart-component `wkpNorm` at order `K' + m + 3` via `hCeig_bd`.
  have h_chart_cpt :
      wkpNorm (d := Module.finrank ℝ E) (K' + m + 3) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig (K' + m + 3) *
            (i.fst.val)⁻¹ ^ (eEig (K' + m + 3))) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
    hCeig_bd i (K' + m + 3)
  -- Step 2: chart cpt `MemWkp` at order `(2 + K') + j`, free for all orders.
  have h_chart_cpt_memWkp :
      MemWkp (d := Module.finrank ℝ E) ((2 + K') + j) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
      g r s h_atlas i ((2 + K') + j) α P₀
  -- Step 3: bridge to the `j`-fold iterated weak partial.
  obtain ⟨_, h_partial⟩ :=
    eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
      (I := I) (M := M) g r s h_atlas i α P₀ j (2 + K') h_chart_cpt_memWkp idx
  -- Step 4: `wkpNorm`-monotonicity: `wkpNorm (2 + K' + j) ≤ wkpNorm (K' + m + 3)`.
  have h_order_le : (2 + K') + j ≤ K' + m + 3 := by omega
  have h_mono :
      wkpNorm (d := Module.finrank ℝ E) ((2 + K') + j) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ wkpNorm (d := Module.finrank ℝ E) (K' + m + 3) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_mono_order (d := Module.finrank ℝ E) h_order_le _ _
  -- Chain: `wkpNorm (2 + K') (partial j idx) ≤ wkpNorm (2 + K' + j) (chart cpt)
  --                                          ≤ wkpNorm (K' + m + 3) (chart cpt)
  --                                          ≤ ofReal (...) · ofReal ‖vec‖`.
  exact h_partial.trans (h_mono.trans h_chart_cpt)

/-! ## The headline sharp `eLpNorm` bound

For a closed Riemannian manifold, ranks, chart center, component multi-index,
differentiation level `m`, and direction multi-index, given uniform
`wkpNorm`-graded chart-component energy hypotheses on each of the seven
primitive source atoms — phrased as per-K-families, with `K`-dependent constants
and exponents — plus a partition-of-unity regularity hypothesis (`MemWkp` at
order `m + 1`), there is a single geometric constant `C` and exponent `e`
controlling the order-`0` `wkpNorm` (= `eLpNorm`) of the level-`m` differentiated
chart right-hand side.

The proof composes the existing energy-bound chain at `K = 0`:

* `eigenvectorChartRHSDiff_eLpNorm_le_uniform` produces an `eLpNorm` bound
  against `diffRHSAggregate … m 0 l`, with constant `μ⁻¹ · Cwk`;
* `diffRHSAggregate_le_energy_perK` collapses the aggregate, at order `0`, to
  `ENNReal.ofReal (Caggr · μ⁻¹^e) · ofReal ‖vec_i‖`, using the seven per-K-family
  hypotheses and the iterated-partial `j ≤ m + 1`-restricted family derived
  from the chart-component per-K-family via
  `iteratedPartial_wkpNorm_le_of_chart_perK`. -/

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- **Sharp `eLpNorm` bound on the level-`m` differentiated chart right-hand
side, in chart-component data.**

For a closed Riemannian manifold, ranks `(r, s)`, a chart center `α : M`, a
component multi-index `P₀`, a level `m`, a direction multi-index
`l : Fin m → Fin n`, an order-`(m + 1)` partition-of-unity regularity hypothesis
`h_pou` on the resolvent chart components, and seven uniform `wkpNorm`-graded
chart-component energy hypotheses phrased as per-K-families with constants
`Ceig : ℕ → ℝ`, `CresH : ℕ → ℝ`, etc., there is a single geometric constant
`C : ℝ` and exponent `e : ℕ` such that, for *every* eigenbasis index `i` with
resolvent eigenvalue `μ := i.fst.val`,

```
eLpNorm (eigenvectorChartRHSDiff … m l) 2 (volume.restrict (chartTargetEuclid α))
  ≤ ENNReal.ofReal (C · μ⁻¹^e) · ENNReal.ofReal ‖tensorResolventEigenbasisVec …‖.
```

The constant `C` is geometric — it depends on `g r s h_atlas α P₀ m l` and on
the constants supplied by the seven per-K-family input hypotheses and the
partition-of-unity hypothesis; in particular it is independent of the
eigenbasis index `i`. The exponent `e` is likewise geometric. The eigenvalue
factor `μ⁻¹^e` is the only `i`-dependent piece. -/
theorem eigenvectorChartRHSDiff_eLpNorm_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m l) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- Step 1: bound `eLpNorm` of the level-`m` differentiated right-hand side by
  -- `μ⁻¹ · C * diffRHSAggregate m 0 l` via the existing weighted-`eLpNorm`
  -- chain.
  obtain ⟨Cwk, hCwk_nn, hCwk_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le_uniform (I := I) (M := M)
      g r s h_atlas α P₀ m l h_pou
  -- Step 2: bound `diffRHSAggregate m 0 l` by `ofReal (Caggr * μ⁻¹^e) * ‖vec‖`
  -- via the energy-aggregate chain. The iterated-partial per-K-family is
  -- derived from the chart-component per-K-family via the polymorphic bridge
  -- combined with `wkpNorm`-monotonicity in the order.
  set Citer : ℕ → ℝ := fun K' => Ceig (K' + m + 3) with hCiter_def
  set eIter : ℕ → ℕ := fun K' => eEig (K' + m + 3) with heIter_def
  have hCiter_nn : ∀ K', 0 ≤ Citer K' := fun K' => hCeig_nn (K' + m + 3)
  have hCiter_bd :
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
        j ≤ m + 1 →
        ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
          wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
    iteratedPartial_wkpNorm_le_of_chart_perK (I := I) (M := M)
      g r s h_atlas α P₀ m Ceig eEig hCeig_bd
  obtain ⟨Caggr, eAggr, hCaggr_nn, hCaggr_bd⟩ :=
    diffRHSAggregate_le_energy_perK (I := I) (M := M)
      g r s h_atlas α P₀ m 0 l
      Ceig eEig hCeig_nn hCeig_bd
      CresH eResH hCresH_nn hCresH_bd
      CresL eResL hCresL_nn hCresL_bd
      Cpar ePar hCpar_nn hCpar_bd
      Ccom eCom hCcom_nn hCcom_bd
      CcR eCcR hCcR_nn hCcR_bd
      Ccut eCcut hCcut_nn hCcut_bd
      Citer eIter hCiter_nn hCiter_bd
  -- Step 3: compose the two bounds to get the headline.
  -- The eigenvalue is in `(0, 1]`, so `μ⁻¹ ≥ 1` and `μ⁻¹ ≤ μ⁻¹ · μ⁻¹^e ≤ μ⁻¹^(e + 1)`.
  refine ⟨Cwk * Caggr, eAggr + 1, mul_nonneg hCwk_nn hCaggr_nn, fun i => ?_⟩
  -- Per-`i` setup: eigenvalue facts.
  -- The resolvent eigenvalue lies in `(0, 1]`.
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 := by
    have h_norm :
        ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
      (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
        (g := g) (r := r) (s := s) h_atlas).norm_eq_one i
    exact tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ with hRhs_def
  -- Chain: `eLpNorm ≤ ofReal (μ⁻¹ · Cwk) · diffRHSAggregate m 0 l`
  --                ≤ ofReal (μ⁻¹ · Cwk) · (ofReal (Caggr · μ⁻¹^eAggr) · ‖vec‖)
  --                = ofReal ((Cwk · Caggr) · μ⁻¹^(eAggr + 1)) · ‖vec‖.
  calc eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ m l) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          diffRHSAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m 0 l := hCwk_bd i
    _ ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          (ENNReal.ofReal (Caggr * (i.fst.val)⁻¹ ^ eAggr) * Rhs) :=
        mul_le_mul' (le_refl _) (hCaggr_bd i)
    _ = ENNReal.ofReal ((Cwk * Caggr) * (i.fst.val)⁻¹ ^ (eAggr + 1)) * Rhs := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [pow_succ, mul_comm ((i.fst.val)⁻¹ ^ eAggr) (i.fst.val)⁻¹]
        ring

/-! ## The order-`1` sharp `wkpNorm` bound, simultaneous companion

The order-`1` `wkpNorm`-graded companion of the sharp `eLpNorm` bound: the same
chart-component per-K-family hypotheses, but with the partition-of-unity
hypothesis bumped to order `m + 2` (since the order-`1` `wkpNorm` of the
level-`m` differentiated right-hand side draws on its order-`(K + 1)` resolvent
data at `K = 1`, requiring partition-of-unity regularity at order `m + 2`).

The proof composes `eigenvectorChartRHSDiff_wkpNorm_le_uniform` at `K = 1`
with `diffRHSAggregate_le_energy_perK` at `K = 1`. -/

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- **Order-`1` sharp `wkpNorm` bound on the level-`m` differentiated chart
right-hand side, in chart-component data.**

The order-`1` `wkpNorm`-graded companion of `eigenvectorChartRHSDiff_eLpNorm_le_chartcpt`:
the same chart-component per-K-family hypotheses, but the partition-of-unity
hypothesis is at order `m + 2`. -/
theorem eigenvectorChartRHSDiff_wkpNormOne_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- Step 1: bound `wkpNorm 1` of the level-`m` differentiated right-hand side
  -- by `μ⁻¹ · C * diffRHSAggregate m 1 l` via the existing `wkpNorm`-graded
  -- chain at `K = 1`.
  obtain ⟨Cwk, hCwk_nn, hCwk_bd⟩ :=
    eigenvectorChartRHSDiff_wkpNorm_le_uniform (I := I) (M := M)
      g r s h_atlas α P₀ m 1 l h_pou
  -- Step 2: bound `diffRHSAggregate m 1 l` by `ofReal (Caggr * μ⁻¹^e) * ‖vec‖`
  -- via the energy-aggregate chain at `K = 1`.
  set Citer : ℕ → ℝ := fun K' => Ceig (K' + m + 3) with hCiter_def
  set eIter : ℕ → ℕ := fun K' => eEig (K' + m + 3) with heIter_def
  have hCiter_nn : ∀ K', 0 ≤ Citer K' := fun K' => hCeig_nn (K' + m + 3)
  have hCiter_bd :
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
        j ≤ m + 1 →
        ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
          wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
    iteratedPartial_wkpNorm_le_of_chart_perK (I := I) (M := M)
      g r s h_atlas α P₀ m Ceig eEig hCeig_bd
  obtain ⟨Caggr, eAggr, hCaggr_nn, hCaggr_bd⟩ :=
    diffRHSAggregate_le_energy_perK (I := I) (M := M)
      g r s h_atlas α P₀ m 1 l
      Ceig eEig hCeig_nn hCeig_bd
      CresH eResH hCresH_nn hCresH_bd
      CresL eResL hCresL_nn hCresL_bd
      Cpar ePar hCpar_nn hCpar_bd
      Ccom eCom hCcom_nn hCcom_bd
      CcR eCcR hCcR_nn hCcR_bd
      Ccut eCcut hCcut_nn hCcut_bd
      Citer eIter hCiter_nn hCiter_bd
  refine ⟨Cwk * Caggr, eAggr + 1, mul_nonneg hCwk_nn hCaggr_nn, fun i => ?_⟩
  -- Per-`i` setup: eigenvalue facts.
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 := by
    have h_norm :
        ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
      (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
        (g := g) (r := r) (s := s) h_atlas).norm_eq_one i
    exact tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ with hRhs_def
  calc wkpNorm (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m l)
          (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          diffRHSAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m 1 l := hCwk_bd i
    _ ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          (ENNReal.ofReal (Caggr * (i.fst.val)⁻¹ ^ eAggr) * Rhs) :=
        mul_le_mul' (le_refl _) (hCaggr_bd i)
    _ = ENNReal.ofReal ((Cwk * Caggr) * (i.fst.val)⁻¹ ^ (eAggr + 1)) * Rhs := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [pow_succ, mul_comm ((i.fst.val)⁻¹ ^ eAggr) (i.fst.val)⁻¹]
        ring

/-! ## Chart-locality-free twins

The chart-locality-free companions of the declarations above, re-keyed onto the
intrinsic compact-operator eigenbasis `tensorResolventEigenbasisVec_ofCompact`
of `tensorResolventL2_isCompactOperator_intrinsic g r s`, dropping the
`HasLocallyConstantChartAt` hypothesis throughout. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

/-- Chart-locality-free twin of `iteratedPartial_wkpNorm_le_of_chart_perK`. -/
private lemma iteratedPartial_wkpNorm_le_of_chart_perK_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ)
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖) :
    ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
      j ≤ m + 1 →
      ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Ceig (K' + m + 3) *
              (i.fst.val)⁻¹ ^ (eEig (K' + m + 3))) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro i j hj idx K'
  -- Step 1: chart-component `wkpNorm` at order `K' + m + 3` via `hCeig_bd`.
  have h_chart_cpt :
      wkpNorm (d := Module.finrank ℝ E) (K' + m + 3) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig (K' + m + 3) *
            (i.fst.val)⁻¹ ^ (eEig (K' + m + 3))) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ :=
    hCeig_bd i (K' + m + 3)
  -- Step 2: chart cpt `MemWkp` at order `(2 + K') + j`, free for all orders.
  have h_chart_cpt_memWkp :
      MemWkp (d := Module.finrank ℝ E) ((2 + K') + j) 2
          (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary_unconditional (I := I) (M := M)
      g r s i ((2 + K') + j) α P₀
  -- Step 3: bridge to the `j`-fold iterated weak partial.
  obtain ⟨_, h_partial⟩ :=
    eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp_unconditional
      (I := I) (M := M) g r s i α P₀ j (2 + K') h_chart_cpt_memWkp idx
  -- Step 4: `wkpNorm`-monotonicity: `wkpNorm (2 + K' + j) ≤ wkpNorm (K' + m + 3)`.
  have h_order_le : (2 + K') + j ≤ K' + m + 3 := by omega
  have h_mono :
      wkpNorm (d := Module.finrank ℝ E) ((2 + K') + j) 2
          (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ wkpNorm (d := Module.finrank ℝ E) (K' + m + 3) 2
            (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_mono_order (d := Module.finrank ℝ E) h_order_le _ _
  -- Chain: `wkpNorm (2 + K') (partial j idx) ≤ wkpNorm (2 + K' + j) (chart cpt)
  --                                          ≤ wkpNorm (K' + m + 3) (chart cpt)
  --                                          ≤ ofReal (...) · ofReal ‖vec‖`.
  exact h_partial.trans (h_mono.trans h_chart_cpt)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Chart-locality-free twin of `eigenvectorChartRHSDiff_eLpNorm_le_chartcpt`. -/
theorem eigenvectorChartRHSDiff_eLpNorm_le_chartcpt_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m l) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  -- Step 1: bound `eLpNorm` of the level-`m` differentiated right-hand side by
  -- `μ⁻¹ · C * diffRHSAggregate m 0 l` via the existing weighted-`eLpNorm`
  -- chain.
  obtain ⟨Cwk, hCwk_nn, hCwk_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le_uniform_unconditional (I := I) (M := M)
      g r s α P₀ m l h_pou
  -- Step 2: bound `diffRHSAggregate m 0 l` by `ofReal (Caggr * μ⁻¹^e) * ‖vec‖`
  -- via the energy-aggregate chain. The iterated-partial per-K-family is
  -- derived from the chart-component per-K-family via the polymorphic bridge
  -- combined with `wkpNorm`-monotonicity in the order.
  set Citer : ℕ → ℝ := fun K' => Ceig (K' + m + 3) with hCiter_def
  set eIter : ℕ → ℕ := fun K' => eEig (K' + m + 3) with heIter_def
  have hCiter_nn : ∀ K', 0 ≤ Citer K' := fun K' => hCeig_nn (K' + m + 3)
  have hCiter_bd :
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
        j ≤ m + 1 →
        ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
          wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖ :=
    iteratedPartial_wkpNorm_le_of_chart_perK_unconditional (I := I) (M := M)
      g r s α P₀ m Ceig eEig hCeig_bd
  obtain ⟨Caggr, eAggr, hCaggr_nn, hCaggr_bd⟩ :=
    diffRHSAggregate_le_energy_perK_unconditional (I := I) (M := M)
      g r s α P₀ m 0 l
      Ceig eEig hCeig_nn hCeig_bd
      CresH eResH hCresH_nn hCresH_bd
      CresL eResL hCresL_nn hCresL_bd
      Cpar ePar hCpar_nn hCpar_bd
      Ccom eCom hCcom_nn hCcom_bd
      CcR eCcR hCcR_nn hCcR_bd
      Ccut eCcut hCcut_nn hCcut_bd
      Citer eIter hCiter_nn hCiter_bd
  -- Step 3: compose the two bounds to get the headline.
  -- The eigenvalue is in `(0, 1]`, so `μ⁻¹ ≥ 1` and `μ⁻¹ ≤ μ⁻¹ · μ⁻¹^e ≤ μ⁻¹^(e + 1)`.
  refine ⟨Cwk * Caggr, eAggr + 1, mul_nonneg hCwk_nn hCaggr_nn, fun i => ?_⟩
  -- Per-`i` setup: eigenvalue facts.
  -- The resolvent eigenvalue lies in `(0, 1]`.
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 := by
    have h_norm :
        ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i‖ = 1 :=
      (tensorResolventEigenbasisVec_ofCompact_orthonormal (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s)).norm_eq_one i
    exact tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ with hRhs_def
  -- Chain: `eLpNorm ≤ ofReal (μ⁻¹ · Cwk) · diffRHSAggregate m 0 l`
  --                ≤ ofReal (μ⁻¹ · Cwk) · (ofReal (Caggr · μ⁻¹^eAggr) · ‖vec‖)
  --                = ofReal ((Cwk · Caggr) · μ⁻¹^(eAggr + 1)) · ‖vec‖.
  calc eLpNorm (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ m l) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          diffRHSAggregate_unconditional (I := I) (M := M)
            g r s i α P₀ m 0 l := hCwk_bd i
    _ ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          (ENNReal.ofReal (Caggr * (i.fst.val)⁻¹ ^ eAggr) * Rhs) :=
        mul_le_mul' (le_refl _) (hCaggr_bd i)
    _ = ENNReal.ofReal ((Cwk * Caggr) * (i.fst.val)⁻¹ ^ (eAggr + 1)) * Rhs := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [pow_succ, mul_comm ((i.fst.val)⁻¹ ^ eAggr) (i.fst.val)⁻¹]
        ring

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Chart-locality-free twin of `eigenvectorChartRHSDiff_wkpNormOne_le_chartcpt`. -/
theorem eigenvectorChartRHSDiff_wkpNormOne_le_chartcpt_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  -- Step 1: bound `wkpNorm 1` of the level-`m` differentiated right-hand side
  -- by `μ⁻¹ · C * diffRHSAggregate m 1 l` via the existing `wkpNorm`-graded
  -- chain at `K = 1`.
  obtain ⟨Cwk, hCwk_nn, hCwk_bd⟩ :=
    eigenvectorChartRHSDiff_wkpNorm_le_uniform_unconditional (I := I) (M := M)
      g r s α P₀ m 1 l h_pou
  -- Step 2: bound `diffRHSAggregate m 1 l` by `ofReal (Caggr * μ⁻¹^e) * ‖vec‖`
  -- via the energy-aggregate chain at `K = 1`.
  set Citer : ℕ → ℝ := fun K' => Ceig (K' + m + 3) with hCiter_def
  set eIter : ℕ → ℕ := fun K' => eEig (K' + m + 3) with heIter_def
  have hCiter_nn : ∀ K', 0 ≤ Citer K' := fun K' => hCeig_nn (K' + m + 3)
  have hCiter_bd :
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
        j ≤ m + 1 →
        ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
          wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖ :=
    iteratedPartial_wkpNorm_le_of_chart_perK_unconditional (I := I) (M := M)
      g r s α P₀ m Ceig eEig hCeig_bd
  obtain ⟨Caggr, eAggr, hCaggr_nn, hCaggr_bd⟩ :=
    diffRHSAggregate_le_energy_perK_unconditional (I := I) (M := M)
      g r s α P₀ m 1 l
      Ceig eEig hCeig_nn hCeig_bd
      CresH eResH hCresH_nn hCresH_bd
      CresL eResL hCresL_nn hCresL_bd
      Cpar ePar hCpar_nn hCpar_bd
      Ccom eCom hCcom_nn hCcom_bd
      CcR eCcR hCcR_nn hCcR_bd
      Ccut eCcut hCcut_nn hCcut_bd
      Citer eIter hCiter_nn hCiter_bd
  refine ⟨Cwk * Caggr, eAggr + 1, mul_nonneg hCwk_nn hCaggr_nn, fun i => ?_⟩
  -- Per-`i` setup: eigenvalue facts.
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 := by
    have h_norm :
        ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i‖ = 1 :=
      (tensorResolventEigenbasisVec_ofCompact_orthonormal (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s)).norm_eq_one i
    exact tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ with hRhs_def
  calc wkpNorm (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m l)
          (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          diffRHSAggregate_unconditional (I := I) (M := M)
            g r s i α P₀ m 1 l := hCwk_bd i
    _ ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          (ENNReal.ofReal (Caggr * (i.fst.val)⁻¹ ^ eAggr) * Rhs) :=
        mul_le_mul' (le_refl _) (hCaggr_bd i)
    _ = ENNReal.ofReal ((Cwk * Caggr) * (i.fst.val)⁻¹ ^ (eAggr + 1)) * Rhs := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [pow_succ, mul_comm ((i.fst.val)⁻¹ ^ eAggr) (i.fst.val)⁻¹]
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
