import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70SubBindersV3_O53
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HtraceU_O56

/-!
# CH12-O56, group 2: hKL v4 — the v3 (cone-end) composition at the union cap predicate

`[FROZEN] CH12-O56 G1/G2`.  `hNoEscPos_of_ABC_v4_O56` is `hNoEscPos_of_ABC_v3_O53` (same proof) with
* `capPt := capPtU_O56 Hp hKcap` (lead ruling O56-1 (a)),
* the LIMP output of hA2 and the `a2` premise of `hE` in `[FROZEN v2] CH12-O55 LIMP` text (PHI clause,
  radial C⁰ clause, pair clause only on `B_L(x₀, R̄/3)`, LIMP v3 of lead ruling O59), `R̄ = ρ - (Real.sqrt 2)⁻¹ / 4`.
`hKL70_U_O56` is the U-form of the A13/A09 `hKL70` binder (no `∃ Dcap hD`).  v4 supersedes
`hNoEscPos_of_ABC_v2_O51` / `_v3_O53` as the combinator for `hKL70`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **hKL v3** (cone-end route): hA1, hA2 and the escape-limit slot `hE`; pure composition with
`hC2_O53`. -/
theorem hNoEscPos_of_ABC_v4_O56 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hKcap :
      ∀ A : ℝ, 0 < A → ∃ Q _T θ : ℝ, 1 ≤ Q ∧ 0 < θ ∧ ∀ Dcap : ℝ, StandardCap.transitionEnd < Dcap →
        ∃ T' : ℝ, ∀ s : RegularSlice F.observation, T' ≤ s.time → ∀ T₀ : ℝ, T' ≤ T₀ → T₀ ≤ s.time →
        ∀ (p : CutoffParameters)
          (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
            T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
            GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i p),
          (p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
            p.fixed = Hp.parameters.fixed ∧ p.recenterConstant = Hp.parameters.recenterConstant ∧
            32 * (Dcap + 1 + 4 * A) + 2 ≤ p.modelRadius ∧
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b))) →
          ∀ y : s.stage.Carrier,
          (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
              (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
              (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
              (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
                (Fin.last (sliceHistoryR_O3 F s).eventCount) hl y)
              (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
              (x : standardCapWindow p.modelRadius),
              B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
                s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                  θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
            metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y)
    (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (heps : 13000 * (13000 * Hp.epsilon) ≤
      min (neckModelTolerance ((1 / 4000000 : ℝ) / 26000)) (((1 / 4000000 : ℝ) / 26000) / 64))
    (hA1 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      0 ≤ ρ → ρ ≤ A →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      (∀ r : ℝ, 0 < r → r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∃ v : ℝ, 0 < v ∧
        ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ min 1 (ρ - (Real.sqrt 2)⁻¹ / 4 - r) → ∀ᶠ n in atTop,
          ∀ p ∈ riemannianBallOf (s n).metric (y n) (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
            ENNReal.ofReal (v * (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))) ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (s n).stage.Carrier (s n).metric
                (riemannianBallOf (s n).metric p (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))))))
    (hA2 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      0 ≤ ρ → ρ ≤ A →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      1 / 4 ≤ ρ →
      (∀ r : ℝ, 0 < r → r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∃ v : ℝ, 0 < v ∧
        ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ min 1 (ρ - (Real.sqrt 2)⁻¹ / 4 - r) → ∀ᶠ n in atTop,
          ∀ p ∈ riemannianBallOf (s n).metric (y n) (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
            ENNReal.ofReal (v * (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))) ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (s n).stage.Carrier (s n).metric
                (riemannianBallOf (s n).metric p (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))))) →
      (∃ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f ∧
        ∃ φ : ∀ k, LM → (s (f k)).stage.Carrier,
          (∃ src : ℕ → Set LM, (∀ k, IsOpen (src k)) ∧ (∀ K : Set LM, IsCompact K → ∀ᶠ k in atTop, K ⊆ src k) ∧
            (∀ k, x₀ ∈ src k) ∧ (∀ k, ContMDiffOn ThreeModel ThreeModel ∞ (φ k) (src k))) ∧
          (∀ k, φ k x₀ = y (f k)) ∧
          (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal (ρ - (Real.sqrt 2)⁻¹ / 4)) ∧
          (∀ r : ℝ, r < ρ - (Real.sqrt 2)⁻¹ / 4 → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
          (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
            |metricScalarAt (s (f k)).metric (φ k x) / metricScalarAt (s (f k)).metric (y (f k)) - metricScalarAt gL x| < ε ∧
            |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                (riemannianEDistOf (s (f k)).metric (y (f k)) (φ k x)).toReal -
              (riemannianEDistOf gL x₀ x).toReal| < ε) ∧
          (∀ K : Set LM, IsCompact K →
            (∀ x ∈ K, riemannianEDistOf gL x₀ x < ENNReal.ofReal ((ρ - (Real.sqrt 2)⁻¹ / 4) / 3)) →
            ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K, ∀ x' ∈ K,
              |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                  (riemannianEDistOf (s (f k)).metric (φ k x) (φ k x')).toReal -
                (riemannianEDistOf gL x x').toReal| < ε) ∧
          (∀ x : LM, SectionalBoundedBelowAt gL x 0) ∧
          (∀ r : ℝ, r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∃ C : ℝ, ∀ x : LM,
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)))
    (hE : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPtU_O56 Hp hKcap A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      (∀ r : ℝ, 0 < r → r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∃ v : ℝ, 0 < v ∧
        ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ min 1 (ρ - (Real.sqrt 2)⁻¹ / 4 - r) → ∀ᶠ n in atTop,
          ∀ p ∈ riemannianBallOf (s n).metric (y n) (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
            ENNReal.ofReal (v * (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))) ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (s n).stage.Carrier (s n).metric
                (riemannianBallOf (s n).metric p (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))))) →
      (∃ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f ∧
        ∃ φ : ∀ k, LM → (s (f k)).stage.Carrier,
          (∃ src : ℕ → Set LM, (∀ k, IsOpen (src k)) ∧ (∀ K : Set LM, IsCompact K → ∀ᶠ k in atTop, K ⊆ src k) ∧
            (∀ k, x₀ ∈ src k) ∧ (∀ k, ContMDiffOn ThreeModel ThreeModel ∞ (φ k) (src k))) ∧
          (∀ k, φ k x₀ = y (f k)) ∧
          (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal (ρ - (Real.sqrt 2)⁻¹ / 4)) ∧
          (∀ r : ℝ, r < ρ - (Real.sqrt 2)⁻¹ / 4 → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
          (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
            |metricScalarAt (s (f k)).metric (φ k x) / metricScalarAt (s (f k)).metric (y (f k)) - metricScalarAt gL x| < ε ∧
            |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                (riemannianEDistOf (s (f k)).metric (y (f k)) (φ k x)).toReal -
              (riemannianEDistOf gL x₀ x).toReal| < ε) ∧
          (∀ K : Set LM, IsCompact K →
            (∀ x ∈ K, riemannianEDistOf gL x₀ x < ENNReal.ofReal ((ρ - (Real.sqrt 2)⁻¹ / 4) / 3)) →
            ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K, ∀ x' ∈ K,
              |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                  (riemannianEDistOf (s (f k)).metric (φ k x) (φ k x')).toReal -
                (riemannianEDistOf gL x x').toReal| < ε) ∧
          (∀ x : LM, SectionalBoundedBelowAt gL x 0) ∧
          (∀ r : ℝ, r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∃ C : ℝ, ∀ x : LM,
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) →
      (∃ (x : ∀ i, ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
            (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen)
          (hQ : ∀ i, 1 ≤ (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (x i).val),
        (∀ i, (Hp.parameters.neckRadius (s i).time ^ 2)⁻¹ ≤
          (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (x i).val) ∧
        Tendsto (fun i => (Hp.parameters.neckRadius (s i).time ^ 2)⁻¹ /
          (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (x i).val) atTop (𝓝 0) ∧
        ∃ (rho : ℝ) (_ : 0 < rho) (f : ℕ → ℕ) (_ : StrictMono f) (r : ℕ → ℝ) (_ : ∀ n, 0 < r n)
          (_ : Tendsto r atTop (𝓝 rho)) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (Fc : PointedRiemannianConvergenceMaps
            ({ obj := fun i =>
                { M := ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
                    (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen
                  basepoint := x i
                  metric := scaleMetric ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (x i).val)
                    (zero_lt_one.trans_le (hQ i))
                    ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
                      ((sliceHistoryR_O3 F (s i)).stage
                        (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric } } :
              PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
          (Mc : MetricConvergenceData Fc),
          (∀ n, Mc.domain n = CanonicalMetricCompactness.canonicalSourceData Fc n) ∧
          (∀ z : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho) ∧
          (∀ R : ℝ, 0 ≤ R → R < rho →
            IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
          (∀ n, riemannianClosedBallOf
            (scaleMetric ((sliceSlabR_O3 F (s (f n))).flow.scalar (s (f n)).time (x (f n)).val)
              (zero_lt_one.trans_le (hQ (f n))) ((sliceSlabR_O3 F (s (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 F (s (f n))).stage (Fin.last (sliceHistoryR_O3 F (s (f n))).eventCount))).metric)
            (x (f n)) (r n) ⊆ Fc.target n) ∧
          (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y ∈ Fc.source n, ∀ v : TangentSpace ThreeModel y,
            (1 - ε) * Pl.metric.inner y v v ≤
              (scaleMetric ((sliceSlabR_O3 F (s (f n))).flow.scalar (s (f n)).time (x (f n)).val)
                (zero_lt_one.trans_le (hQ (f n)))
                ((sliceSlabR_O3 F (s (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 F (s (f n))).stage (Fin.last (sliceHistoryR_O3 F (s (f n))).eventCount))).metric).inner (Fc.map n y)
                (mfderiv ThreeModel ThreeModel (Fc.map n) y v)
                (mfderiv ThreeModel ThreeModel (Fc.map n) y v)) ∧
          ∃ zz : ∀ n, ((sliceSlabR_O3 F (s (f n))).restrictIncoming le_rfl (sliceSlabR_O3 F (s (f n))).lt le_rfl).terminalRegularOpen,
          (∀ n, riemannianEDistOf
            (scaleMetric ((sliceSlabR_O3 F (s (f n))).flow.scalar (s (f n)).time (x (f n)).val)
              (zero_lt_one.trans_le (hQ (f n))) ((sliceSlabR_O3 F (s (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 F (s (f n))).stage (Fin.last (sliceHistoryR_O3 F (s (f n))).eventCount))).metric)
            (x (f n)) (zz n) ≠ ⊤) ∧
          (Tendsto (fun n => (riemannianEDistOf
            (scaleMetric ((sliceSlabR_O3 F (s (f n))).flow.scalar (s (f n)).time (x (f n)).val)
              (zero_lt_one.trans_le (hQ (f n))) ((sliceSlabR_O3 F (s (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 F (s (f n))).stage (Fin.last (sliceHistoryR_O3 F (s (f n))).eventCount))).metric)
            (x (f n)) (zz n)).toReal) atTop (𝓝 rho)) ∧
          (Tendsto (fun n => metricScalarAt
            ((sliceSlabR_O3 F (s (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 F (s (f n))).stage (Fin.last (sliceHistoryR_O3 F (s (f n))).eventCount))).metric (zz n) /
              (sliceSlabR_O3 F (s (f n))).flow.scalar (s (f n)).time (x (f n)).val) atTop atTop) ∧
          (Tendsto (fun n => (sliceSlabR_O3 F (s (f n))).flow.scalar (s (f n)).time (x (f n)).val) atTop atTop) ∧
          ∃ (κ : ℝ) (σ : ℕ → ℝ), (0 < κ) ∧
          (Tendsto (fun i => σ i *
            Real.sqrt ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (x i).val)) atTop atTop) ∧
          (∀ i (w : ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
              (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen),
            riemannianEDistOf ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
              ((sliceHistoryR_O3 F (s i)).stage
                (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric (x i) w <
              ENNReal.ofReal (σ i) →
            ∀ b : ℝ, 0 < b → b ≤ σ i →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel
                  ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
                    (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen
                  ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
                    ((sliceHistoryR_O3 F (s i)).stage
                      (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric
                  (riemannianBallOf ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
                    ((sliceHistoryR_O3 F (s i)).stage
                      (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric w b)) ∧
          (∀ xW : ℕ → Pl.M, Tendsto (fun n => metricScalarAt Pl.metric (xW n)) atTop atTop →
            ∃ θ₂ : ℝ, 0 < θ₂ ∧ ∀ m, ∀ᶠ n in atTop,
              ∃ first : Fin ((sliceHistoryR_O3 F (s (f n))).eventCount + 1),
                (sliceHistoryR_O3 F (s (f n))).time first ≤ (s (f n)).time - θ₂ /
                  (sliceSlabR_O3 F (s (f n))).flow.scalar (s (f n)).time (Fc.map n (xW m)).val ∧
                ∀ w ∈ riemannianBallOf ((sliceSlabR_O3 F (s (f n))).flow.base.metric (s (f n)).time)
                  (Fc.map n (xW m)).val
                  (Real.sqrt ((sliceSlabR_O3 F (s (f n))).flow.scalar (s (f n)).time
                    (Fc.map n (xW m)).val))⁻¹,
                  Nonempty (BackwardPointTrace (sliceHistoryR_O3 F (s (f n))).toHistory first
                    (Fin.last (sliceHistoryR_O3 F (s (f n))).eventCount) (Fin.le_last first) w)))) :
    ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPtU_O56 Hp hKcap A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      False := by
  intro A hA s y z ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have a1 := hA1 A hA s y z ρ h1 h2 h3 h5 h6 h8 h9 h10 h11
  have a2 := hA2 A hA s y ρ h1 h2 h3 h5 h6 h9 h11 a1
  obtain ⟨x, hQ, hqQ, hqlim, rho, hrho, f, hf, r, hr, hrlim, Pl, Fc, Mc, hcan, hradial, hcompact,
    hcapture, hlower, zz, hfinite, hdist, hhigh, hQlim, κ, σ, hκ, hσlim, hloc, htrace⟩ :=
    hE A hA s y z ρ h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 a1 a2
  exact hC2_O53 Hp Ctime hP2 s x hQ hqQ hqlim (alpha := 1 / 4000000) (by norm_num) (by norm_num)
    heps hrho f hf r hr hrlim Pl Fc Mc hcan hradial hcompact hcapture hlower zz hfinite hdist hhigh
    hQlim σ hκ hσlim hloc htrace

/-- **hKL70 in U-form** (the A13/A09 `hKL70` binder without `∃ Dcap hD`, cap premise `¬ capPtU_O56`):
the extra canonical-witness premise of `hKL70` is dropped.  Use with
`hKL70_U_O56 Hp hKcap (hNoEscPos_of_ABC_v4_O56 Hp hKcap Ctime hP2 heps hA1 hA2 hE)`. -/
theorem hKL70_U_O56 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hKcap :
      ∀ A : ℝ, 0 < A → ∃ Q _T θ : ℝ, 1 ≤ Q ∧ 0 < θ ∧ ∀ Dcap : ℝ, StandardCap.transitionEnd < Dcap →
        ∃ T' : ℝ, ∀ s : RegularSlice F.observation, T' ≤ s.time → ∀ T₀ : ℝ, T' ≤ T₀ → T₀ ≤ s.time →
        ∀ (p : CutoffParameters)
          (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
            T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
            GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i p),
          (p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
            p.fixed = Hp.parameters.fixed ∧ p.recenterConstant = Hp.parameters.recenterConstant ∧
            32 * (Dcap + 1 + 4 * A) + 2 ≤ p.modelRadius ∧
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b))) →
          ∀ y : s.stage.Carrier,
          (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
              (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
              (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
              (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
                (Fin.last (sliceHistoryR_O3 F s).eventCount) hl y)
              (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
              (x : standardCapWindow p.modelRadius),
              B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
                s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                  θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
            metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y)
    (hKL :
    ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPtU_O56 Hp hKcap A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      False) :
      ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPtU_O56 Hp hKcap A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      (∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℝ, 1 < lam → ∀ r : ℝ, ρ < r → ∀ᶠ n in atTop,
          ∃ w : (s n).stage.Carrier,
            w ∈ riemannianBallOf (s n).metric (y n)
              (r / Real.sqrt (metricScalarAt (s n).metric (y n))) ∧
            metricScalarAt (s n).metric w = lam * metricScalarAt (s n).metric (y n) ∧
            ∃ hR : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ < metricScalarAt (s n).metric w,
            ∃ W : SpatialCanonicalWitness (s n).metric Hp.epsilon Hp.C1 Hp.C2 w,
              W.capTubeHasNeckChart Hp.epsilon ∧
              (W.alternative.requiresVolume → ∀ b : ℝ, 0 < b → b ≤ (Real.sqrt Hp.C2)⁻¹ →
                ENNReal.ofReal (κ * b ^ 3) ≤
                  riemannianVolumeMeasure ThreeModel (s n).stage.Carrier
                    (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric)
                    (riemannianBallOf
                      (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric) w b)) ∧
              ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
                ∃ (U : TopologicalSpace.Opens (s n).stage.Carrier) (hxU : w ∈ U)
                  (S : SolutionOn (I := ThreeModel) (M := U)
                    (RealTimeInterval.closed
                      ((s n).time - (metricScalarAt (s n).metric w)⁻¹) (s n).time
                      (sub_le_self _ (inv_nonneg.mpr
                        (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
                  IsSolutionOn S ∧ S.base.metric (s n).time = (s n).metric.restrictOpen U ∧
                  Nonempty (StrongNeck S Hp.epsilon ⟨w, hxU⟩ (s n).time)) →
      False := by
  intro A hA s y z ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 _
  exact hKL A hA s y z ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

end GC.LongTime.Ch12
