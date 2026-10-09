import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70B12Cone_O47

/-!
# CH12-O51, group 3: hKL v2 from six KL70.2 slots — the hB2 slot removed (lead ruling D5)

`[FROZEN] CH12-O51 G3`.  `hNoEscPos_of_ABC_v2_O51` is `hNoEscPos_of_ABC_O38` with
* the B1 slot in v3 form: `[FROZEN v2] CH12-O39 B1` (MetricSpace + necks in the output, = the
  `hB1v2` binder of `hB1_of_v2_O47`) plus the premise `∀ n, ¬ capPt A (s n) (y n)` (finding O51-1:
  with hB2 gone this is the only slot that can use it, and the escape limit at radius `ρ` needs it
  for backward traces);
* the hB2 slot deleted;
* the B3 slot in v2 form: it receives the B1 v3 data (MetricSpace, `edist = riemannianEDistOf gL`,
  necks on a tail of the ray) instead of hB2's output (finding O51-2: O38's B3 slot consumes b2);
* hA1, hA2, hC1, hC2 verbatim (KL70SubBinders_O38).
Pure composition.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **hKL v2 from six KL70.2 slots** (hB2 removed; B1 v3, B3 v2; pure composition). -/
theorem hNoEscPos_of_ABC_v2_O51 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (capPt : ℝ → ∀ s : RegularSlice F.observation, s.stage.Carrier → Prop)
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
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)))
    (hB1 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPt A (s n) (y n)) →
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
            ∀ t ∈ Ico t₀ ρ, Nonempty (SpatialNeck gL (1 / 4000000) (γ t))))
    (hB3 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      0 ≤ ρ → ρ ≤ A →
      1 / 4 ≤ ρ →
      ∀ (LM : Type u) (_ : MetricSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f →
      (∀ a b : LM, edist a b = riemannianEDistOf gL a b) →
      ∀ φ : ∀ k, LM → (s (f k)).stage.Carrier,
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
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) →
      ∀ γ : ℝ → LM, (γ 0 = x₀ ∧
          (∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
            riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
          Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] ρ) atTop) →
      (∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < ρ ∧
        ∀ t ∈ Ico t₀ ρ, Nonempty (SpatialNeck gL (1 / 4000000) (γ t))) →
      (∃ (CM : Type u) (_ : TopologicalSpace CM) (_ : ChartedSpace ThreeSpace CM)
          (_ : IsManifold ThreeModel ∞ CM) (gC : SmoothRiemannianMetric ThreeModel CM) (c₀ : CM) (ψ : ℕ → CM → LM),
        (∀ x : CM, SectionalBoundedBelowAt gC x 0) ∧ 0 < metricScalarAt gC c₀ ∧
        (∀ j, ψ j c₀ = γ (ρ - (2 : ℝ)⁻¹ ^ j)) ∧ (∀ lam : ℝ, 0 < lam → ∃ D : CM → CM, ∀ x x' : CM,
          (riemannianEDistOf gC (D x) (D x')).toReal = lam * (riemannianEDistOf gC x x').toReal ∧
          metricScalarAt gC (D x) = (lam ^ 2)⁻¹ * metricScalarAt gC x) ∧
        ∀ K : Set CM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x ∈ K,
          |((2 : ℝ)⁻¹ ^ j) ^ 2 * metricScalarAt gL (ψ j x) - metricScalarAt gC x| < ε ∧
          ∀ x' ∈ K, |(2 : ℝ) ^ j * (riemannianEDistOf gL (ψ j x) (ψ j x')).toReal -
            (riemannianEDistOf gC x x').toReal| < ε))
    (hC1 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
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
      ∀ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f →
      ∀ φ : ∀ k, LM → (s (f k)).stage.Carrier,
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
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) →
      ∀ γ : ℝ → LM, (γ 0 = x₀ ∧
          (∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
            riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
          Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] ρ) atTop) →
      ∀ (CM : Type u) (_ : TopologicalSpace CM) (_ : ChartedSpace ThreeSpace CM)
          (_ : IsManifold ThreeModel ∞ CM) (gC : SmoothRiemannianMetric ThreeModel CM) (c₀ : CM) (ψ : ℕ → CM → LM),
        (∀ x : CM, SectionalBoundedBelowAt gC x 0) → 0 < metricScalarAt gC c₀ →
        (∀ j, ψ j c₀ = γ (ρ - (2 : ℝ)⁻¹ ^ j)) →
      (∃ (f₂ : ℕ → ℕ), StrictMono f₂ ∧ ∃ (p : ∀ k, (s (f (f₂ k))).stage.Carrier) (η : ℕ → ℝ),
        Tendsto η atTop (𝓝 0) ∧
        (∃ Rinf : ℝ, 0 < Rinf ∧ Tendsto (fun k => metricScalarAt (s (f (f₂ k))).metric (p k) /
          metricScalarAt (s (f (f₂ k))).metric (y (f (f₂ k)))) atTop (𝓝 Rinf)) ∧
        ∀ k, ∃ hRp : 0 < metricScalarAt (s (f (f₂ k))).metric (p k),
          ∃ (U : TopologicalSpace.Opens (s (f (f₂ k))).stage.Carrier) (_ : p k ∈ U)
            (S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed ((s (f (f₂ k))).time -
                (metricScalarAt (s (f (f₂ k))).metric (p k))⁻¹) (s (f (f₂ k))).time
                (sub_le_self _ (inv_nonneg.mpr hRp.le)))),
            IsSolutionOn S ∧ S.base.metric (s (f (f₂ k))).time = (s (f (f₂ k))).metric.restrictOpen U ∧
            ∀ v ∈ Icc ((s (f (f₂ k))).time - (metricScalarAt (s (f (f₂ k))).metric (p k))⁻¹)
                (s (f (f₂ k))).time, ∀ q : U,
              SectionalBoundedBelowAt (S.base.metric v) q
                (-(η k * metricScalarAt (s (f (f₂ k))).metric (p k)))))
    (hC2 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      0 ≤ ρ → ρ ≤ A →
      1 / 4 ≤ ρ →
      ∀ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f →
      ∀ φ : ∀ k, LM → (s (f k)).stage.Carrier,
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
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) →
      ∀ γ : ℝ → LM, (γ 0 = x₀ ∧
          (∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
            riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
          Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] ρ) atTop) →
      ∀ (CM : Type u) (_ : TopologicalSpace CM) (_ : ChartedSpace ThreeSpace CM)
          (_ : IsManifold ThreeModel ∞ CM) (gC : SmoothRiemannianMetric ThreeModel CM) (c₀ : CM) (ψ : ℕ → CM → LM),
        (∀ x : CM, SectionalBoundedBelowAt gC x 0) → 0 < metricScalarAt gC c₀ →
        (∀ j, ψ j c₀ = γ (ρ - (2 : ℝ)⁻¹ ^ j)) →
      (∀ lam : ℝ, 0 < lam → ∃ D : CM → CM, ∀ x x' : CM,
          (riemannianEDistOf gC (D x) (D x')).toReal = lam * (riemannianEDistOf gC x x').toReal ∧
          metricScalarAt gC (D x) = (lam ^ 2)⁻¹ * metricScalarAt gC x) →
      (∃ (f₂ : ℕ → ℕ), StrictMono f₂ ∧ ∃ (p : ∀ k, (s (f (f₂ k))).stage.Carrier) (η : ℕ → ℝ),
        Tendsto η atTop (𝓝 0) ∧
        (∃ Rinf : ℝ, 0 < Rinf ∧ Tendsto (fun k => metricScalarAt (s (f (f₂ k))).metric (p k) /
          metricScalarAt (s (f (f₂ k))).metric (y (f (f₂ k)))) atTop (𝓝 Rinf)) ∧
        ∀ k, ∃ hRp : 0 < metricScalarAt (s (f (f₂ k))).metric (p k),
          ∃ (U : TopologicalSpace.Opens (s (f (f₂ k))).stage.Carrier) (_ : p k ∈ U)
            (S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed ((s (f (f₂ k))).time -
                (metricScalarAt (s (f (f₂ k))).metric (p k))⁻¹) (s (f (f₂ k))).time
                (sub_le_self _ (inv_nonneg.mpr hRp.le)))),
            IsSolutionOn S ∧ S.base.metric (s (f (f₂ k))).time = (s (f (f₂ k))).metric.restrictOpen U ∧
            ∀ v ∈ Icc ((s (f (f₂ k))).time - (metricScalarAt (s (f (f₂ k))).metric (p k))⁻¹)
                (s (f (f₂ k))).time, ∀ q : U,
              SectionalBoundedBelowAt (S.base.metric v) q
                (-(η k * metricScalarAt (s (f (f₂ k))).metric (p k)))) →
      False) :
    ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPt A (s n) (y n)) →
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
  obtain ⟨LM, mLM, cLM, iLM, sLM, gL, x₀, f, hf, hmetric, φ, hL, γ, hγ0, hiso, hblow, hnk⟩ :=
    hB1 A hA s y z ρ h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 a1 a2
  obtain ⟨CM, j1, j2, j3, gC, c₀, ψ, hC0, hCpos, hψ0, hdil, -⟩ :=
    hB3 A hA s y ρ h5 h6 h11 LM mLM cLM iLM sLM gL x₀ f hf hmetric φ hL γ ⟨hγ0, hiso, hblow⟩ hnk
  exact hC2 A hA s y ρ h5 h6 h11 LM inferInstance cLM iLM inferInstance sLM gL x₀ f hf φ hL γ
    ⟨hγ0, hiso, hblow⟩ CM j1 j2 j3 gC c₀ ψ hC0 hCpos hψ0 hdil
    (hC1 A hA s y ρ h1 h2 h3 h5 h6 h9 h11 LM inferInstance cLM iLM inferInstance sLM gL x₀ f hf φ
      hL γ ⟨hγ0, hiso, hblow⟩ CM j1 j2 j3 gC c₀ ψ hC0 hCpos hψ0)

end GC.LongTime.Ch12
