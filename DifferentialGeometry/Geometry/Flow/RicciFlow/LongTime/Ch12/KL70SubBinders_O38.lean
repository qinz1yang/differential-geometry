import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreAssembly_O31
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StrongNeckV2_O31
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# CH12-O38, group 1: hKL v2 and the seven KL70.2 sub-binders (`[FROZEN v2] CH12-O31 G2`)

* hKL v2 = the `hNoEscPos` binder of `hNoEsc_of_pos_O29` verbatim (no re-centred-witness
  premise: the hKL producer takes hStrong v2 as its own binder and gets the buffered centre
  from `exists_buffered_rcw_O31` with NK := v2 neck clause).  `hKL_v1_of_v2_O38` feeds the
  delivered v1 consumers (`hNoEscPos_O31`, `hcore_O31`, S78's `hKL70`).
* `hNoEscPos_of_ABC_O38`: hKL v2 from the seven sub-binders of `[FROZEN] CH12-O31` KL70.2
  sub-statements (A1 A2 B1 B2 B3 C1 C2), pure composition.  Every sub-binder carries the full
  premise list Σ of hKL; normalized balls are written unscaled (`B'_n(p, r) = B(p, r/√R(y n))`),
  `r_* = ρ − (√2)⁻¹/4`; limits are pointed smooth 3-manifolds `(LM, gL, x₀)` (instances as explicit
  binders) with explicit approximating maps `φ k : LM → (s (f k)).stage.Carrier`.
* `hcore_of_ABC_O38`: the K-core binder `hcore` of `hKcan_v2_of_branchesA_O23` from hStrong v2
  and the seven sub-binders.
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

/-- **hKL v2 from the seven KL70.2 sub-binders** (pure composition). -/
theorem hNoEscPos_of_ABC_O38 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
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
          Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] ρ) atTop))
    (hB2 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPt A (s n) (y n)) →
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
      (∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < ρ ∧ ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ t ∈ Ico t₀ ρ,
        c₁ * (ρ - t) ≤ (Real.sqrt (metricScalarAt gL (γ t)))⁻¹ ∧
        (Real.sqrt (metricScalarAt gL (γ t)))⁻¹ ≤ c₂ * (ρ - t) ∧
        (∃ W : SpatialCanonicalWitness gL Hp.epsilon Hp.C1 Hp.C2 (γ t),
          ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) ∧
        ∀ t' ∈ Ioo t ρ, ∀ c : ℝ → LM, ContinuousOn c (Icc 0 1) → c 0 = x₀ → c 1 = γ t' →
          ∃ u ∈ Icc (0 : ℝ) 1, riemannianEDistOf gL (c u) (γ t) <
            ENNReal.ofReal (3 * c₂ * (ρ - t))))
    (hB3 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
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
      (∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < ρ ∧ ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ t ∈ Ico t₀ ρ,
        c₁ * (ρ - t) ≤ (Real.sqrt (metricScalarAt gL (γ t)))⁻¹ ∧
        (Real.sqrt (metricScalarAt gL (γ t)))⁻¹ ≤ c₂ * (ρ - t) ∧
        (∃ W : SpatialCanonicalWitness gL Hp.epsilon Hp.C1 Hp.C2 (γ t),
          ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) ∧
        ∀ t' ∈ Ioo t ρ, ∀ c : ℝ → LM, ContinuousOn c (Icc 0 1) → c 0 = x₀ → c 1 = γ t' →
          ∃ u ∈ Icc (0 : ℝ) 1, riemannianEDistOf gL (c u) (γ t) <
            ENNReal.ofReal (3 * c₂ * (ρ - t))) →
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
  obtain ⟨LM, i1, i2, i3, i4, i5, gL, x₀, f, hf, φ, hL, γ, hγ⟩ := hB1 A hA s y z ρ h1 h2 h3 h5 h6 h8 h9 h10 h11 a1 a2
  have b2 := hB2 A hA s y ρ h1 h2 h3 h4 h5 h6 h9 h11 LM i1 i2 i3 i4 i5 gL x₀ f hf φ hL γ hγ
  obtain ⟨CM, j1, j2, j3, gC, c₀, ψ, hC0, hCpos, hψ0, hdil, -⟩ :=
    hB3 A hA s y ρ h5 h6 h11 LM i1 i2 i3 i4 i5 gL x₀ f hf φ hL γ hγ b2
  exact hC2 A hA s y ρ h5 h6 h11 LM i1 i2 i3 i4 i5 gL x₀ f hf φ hL γ hγ CM j1 j2 j3 gC c₀ ψ hC0 hCpos hψ0 hdil
    (hC1 A hA s y ρ h1 h2 h3 h5 h6 h9 h11 LM i1 i2 i3 i4 i5 gL x₀ f hf φ hL γ hγ CM j1 j2 j3 gC c₀ ψ hC0 hCpos hψ0)

end GC.LongTime.Ch12
