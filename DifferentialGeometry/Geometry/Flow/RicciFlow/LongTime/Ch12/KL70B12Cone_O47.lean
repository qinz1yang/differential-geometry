import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70B1Ray_O47
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70B2Sec_O47
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70SubBinders_O38

/-!
# CH12-O47, group 3: B1 + B2 on the escape limit in the cone-end input form; B1 v2 → O38 hB1

`[FROZEN] CH12-O47` G3.
* `b12_of_escape_limit_O47`: from the tree escape-limit data (binders of
  `exists_isometric_ray_with_spatialNecks_of_scalar_escape` + the pinching binders of
  `metricRm04StandardAt_nonneg_of_normalized_terminal_pinching`), a typed limit
  `(LM, MetricSpace LM, …, gL, x₀)` with `edist = riemannianEDistOf gL`, `Rm ≥ 0` in O38's form,
  the unit-speed ray `γ` from `x₀` on `[0, rho)` with `R → ∞` along `𝓝[<] rho`, and spatial necks
  on a tail `Ico t₀ rho` — exactly the inputs of `cone_end_of_ray_necks_O39` (check file).
* `hB1_of_v2_O47`: `[FROZEN v2] CH12-O39 B1` (MetricSpace in the output, necks with the tree constant
  `1 / 4000000`) implies O38's hB1 binder (forgetful).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **B1 v2 → O38's hB1** (forgetful: the topology and `T2Space` come from the metric). -/
theorem hB1_of_v2_O47 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hB1v2 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
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
                (riemannianBallOf (s n).metric p (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))))) →
      (∃ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f ∧
        ∃ φ : ∀ k, LM → (s (f k)).stage.Carrier,
          (∀ k, ContMDiff ThreeModel ThreeModel ∞ (φ k)) ∧ (∀ k, φ k x₀ = y (f k)) ∧
          (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal (ρ - (Real.sqrt 2)⁻¹ / 4)) ∧
          (∀ r : ℝ, r < ρ - (Real.sqrt 2)⁻¹ / 4 → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
          (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
            |metricScalarAt (s (f k)).metric (φ k x) / metricScalarAt (s (f k)).metric (y (f k)) - metricScalarAt gL x| < ε ∧
            ∀ x' ∈ K, |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                (riemannianEDistOf (s (f k)).metric (φ k x) (φ k x')).toReal -
              (riemannianEDistOf gL x x').toReal| < ε) ∧
          (∀ x : LM, SectionalBoundedBelowAt gL x 0) ∧
          (∀ r : ℝ, r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∃ C : ℝ, ∀ x : LM,
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) →
      (∃ (LM : Type u) (_ : MetricSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f ∧
        (∀ a b : LM, edist a b = riemannianEDistOf gL a b) ∧
        ∃ φ : ∀ k, LM → (s (f k)).stage.Carrier,
          ((∀ k, ContMDiff ThreeModel ThreeModel ∞ (φ k)) ∧ (∀ k, φ k x₀ = y (f k)) ∧
          (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal (ρ)) ∧
          (∀ r : ℝ, r < ρ → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
          (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
            |metricScalarAt (s (f k)).metric (φ k x) / metricScalarAt (s (f k)).metric (y (f k)) - metricScalarAt gL x| < ε ∧
            ∀ x' ∈ K, |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                (riemannianEDistOf (s (f k)).metric (φ k x) (φ k x')).toReal -
              (riemannianEDistOf gL x x').toReal| < ε) ∧
          (∀ x : LM, SectionalBoundedBelowAt gL x 0) ∧
          (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ x : LM,
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) ∧
        ∃ γ : ℝ → LM, γ 0 = x₀ ∧
          (∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
            riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
          Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] ρ) atTop ∧
          ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < ρ ∧
            ∀ t ∈ Ico t₀ ρ, Nonempty (SpatialNeck gL (1 / 4000000) (γ t)))) :
    ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
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
                (riemannianBallOf (s n).metric p (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))))) →
      (∃ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f ∧
        ∃ φ : ∀ k, LM → (s (f k)).stage.Carrier,
          (∀ k, ContMDiff ThreeModel ThreeModel ∞ (φ k)) ∧ (∀ k, φ k x₀ = y (f k)) ∧
          (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal (ρ - (Real.sqrt 2)⁻¹ / 4)) ∧
          (∀ r : ℝ, r < ρ - (Real.sqrt 2)⁻¹ / 4 → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
          (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
            |metricScalarAt (s (f k)).metric (φ k x) / metricScalarAt (s (f k)).metric (y (f k)) - metricScalarAt gL x| < ε ∧
            ∀ x' ∈ K, |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                (riemannianEDistOf (s (f k)).metric (φ k x) (φ k x')).toReal -
              (riemannianEDistOf gL x x').toReal| < ε) ∧
          (∀ x : LM, SectionalBoundedBelowAt gL x 0) ∧
          (∀ r : ℝ, r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∃ C : ℝ, ∀ x : LM,
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) →
      (∃ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f ∧
        ∃ φ : ∀ k, LM → (s (f k)).stage.Carrier,
          ((∀ k, ContMDiff ThreeModel ThreeModel ∞ (φ k)) ∧ (∀ k, φ k x₀ = y (f k)) ∧
          (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal (ρ)) ∧
          (∀ r : ℝ, r < ρ → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
          (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
            |metricScalarAt (s (f k)).metric (φ k x) / metricScalarAt (s (f k)).metric (y (f k)) - metricScalarAt gL x| < ε ∧
            ∀ x' ∈ K, |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                (riemannianEDistOf (s (f k)).metric (φ k x) (φ k x')).toReal -
              (riemannianEDistOf gL x x').toReal| < ε) ∧
          (∀ x : LM, SectionalBoundedBelowAt gL x 0) ∧
          (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ x : LM,
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) ∧
        ∃ γ : ℝ → LM, γ 0 = x₀ ∧
          (∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
            riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
          Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] ρ) atTop) := by
  intro A hA s y z ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  obtain ⟨LM, mLM, cLM, iLM, sLM, gL, x₀, f, hf, -, φ, hφ, γ, hγ0, hiso, hblow, -⟩ :=
    hB1v2 A hA s y z ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact ⟨LM, inferInstance, cLM, iLM, inferInstance, sLM, gL, x₀, f, hf, φ, hφ, γ, hγ0, hiso,
    hblow⟩

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **B1 + B2 on the escape limit**, in the input form of `cone_end_of_ray_necks_O39`. -/
theorem b12_of_escape_limit_O47
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ) (A : ∀ i, (P i).ClosedSlab (a i) (s i))
    (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ)
    (htime : ∀ i y, ∀ t ∈ Ioo (a i) (s i), q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (hgradient : ∀ i y, ∀ t ∈ Ioo (a i) (s i), q i < (A i).flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (s i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (s i) (x i).val)
    (hqlim : Tendsto (fun i => q i / (A i).flow.scalar (s i) (x i).val) atTop (𝓝 0))
    {eps C1 C2 alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1 / 11)
    (heps : 13000 * (13000 * eps) ≤
      min (neckModelTolerance (alpha / 26000)) ((alpha / 26000) / 64))
    (hW : ∀ i y, q i < (A i).flow.scalar (s i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (s i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {rho : ℝ} (hrho : 0 < rho) (f : ℕ → ℕ) (hf : StrictMono f)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 rho))
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (s i) (x i).val)
              (zero_lt_one.trans_le (hQ i)) ((A i).endpointTerminalLimitMetric (P i)).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hradial : ∀ z : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R))
    (hcapture : ∀ n, riemannianClosedBallOf
      (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric)
      (x (f n)) (r n) ⊆ F.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y ∈ F.source n, ∀ v : TangentSpace ThreeModel y,
      (1 - ε) * Pl.metric.inner y v v ≤
        (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
          (zero_lt_one.trans_le (hQ (f n)))
          ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric).inner (F.map n y)
          (mfderiv ThreeModel ThreeModel (F.map n) y v)
          (mfderiv ThreeModel ThreeModel (F.map n) y v))
    (z : ∀ n, ((A (f n)).restrictIncoming le_rfl (A (f n)).lt le_rfl).terminalRegularOpen)
    (hfinite : ∀ n, riemannianEDistOf
      (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric)
      (x (f n)) (z n) ≠ ⊤)
    (hdist : Tendsto (fun n => (riemannianEDistOf
      (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric)
      (x (f n)) (z n)).toReal) atTop (𝓝 rho))
    (hhigh : Tendsto (fun n => metricScalarAt
      ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric (z n) /
        (A (f n)).flow.scalar (s (f n)) (x (f n)).val) atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow (Ico (a i) (s i)) Phi)
    (hQlim : Tendsto (fun n => (A (f n)).flow.scalar (s (f n)) (x (f n)).val) atTop atTop) :
    ∃ (LM : Type u) (_ : MetricSpace LM) (_ : ChartedSpace ThreeSpace LM)
      (_ : IsManifold ThreeModel ∞ LM) (_ : SigmaCompactSpace LM)
      (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM),
      (∀ a b : LM, edist a b = riemannianEDistOf gL a b) ∧
      (∀ z : LM, SectionalBoundedBelowAt gL z 0) ∧
      ∃ γ : ℝ → LM, γ 0 = x₀ ∧
        (∀ t₁ ∈ Ico (0 : ℝ) rho, ∀ t₂ ∈ Ico (0 : ℝ) rho,
          riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
        Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] rho) atTop ∧
        ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < rho ∧ ∀ t ∈ Ico t₀ rho, Nonempty (SpatialNeck gL alpha (γ t)) := by
  have h1 := escape_ray_necks_O47 P a s A Ctime Cgrad q htime hgradient x hQ hqQ hqlim halpha
    halpha1 heps hW hrho f hf r hr hrlim Pl F M hcanonical hradial hcompact hcapture hlower z
    hfinite hdist hhigh
  dsimp only at h1
  obtain ⟨hfin, γ, hγ0, hiso, hblow, t₀, ht₀, ht₀ρ, hnk⟩ := h1
  have hsec := escape_sec_nonneg_O47 P a s A x hQ hPhi hpinch Pl F M hcanonical hQlim
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  exact ⟨Pl.M, EMetricSpace.toMetricSpace hfin, Pl.charted, Pl.smooth, Pl.sigmaCompact, Pl.metric,
    Pl.basepoint, fun _ _ => rfl, hsec, γ, hγ0, hiso, hblow, t₀, ht₀, ht₀ρ, hnk⟩

end GC.LongTime.Ch12
