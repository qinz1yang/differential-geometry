import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceLocalCGv3_O59
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreA2Inputs_O45
import DifferentialGeometry.Geometry.Measure.BallComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalAllOrdersScaled
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

/-!
# CH12-O59, group 2: hA2 (LIMP v3) from the slice Shi bounds (`[FROZEN] CH12-O59 G1`, plan G2)

`hA2_of_sliceShi_O59`: the hA2 binder of `hNoEscPos_of_ABC_v4_O56` (= O38 hA2 premises verbatim,
conclusion `[FROZEN v3] CH12-O59 LIMP` with `R̄ = ρ - (√2)⁻¹/4`), from ONE inline slot `hShi`
(the slice Shi derivative bounds on the rescaled balls = `sliceLocalCG_O55`'s own `hjets` read on
slices, shape frozen in `[FROZEN] CH12-O59 G1`).  Everything else is proved here:
* `hcompact`: stage carriers are compact;
* `hvol`: rescaling of the A1-type inner volume premise (`riemannianVolumeMeasure_ball_ge_scaleMetric_iff`);
* `hsec`: `sectional_almost_nonneg_on_ball_O45` + `metricRm04StandardAt_scaleMetric`;
* distance conversions `d_{R g} = √R d_g` (`edistOf_scale`).
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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- `(√2)⁻¹ / 4 < 1 / 4`. -/
theorem inv_sqrt_two_div_four_lt_O59 : (Real.sqrt 2)⁻¹ / 4 < 1 / 4 := by
  have h1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  linarith

/-- Sectional lower bound under rescaling: `sec_g ≥ -ε Q` gives `sec_{Q g} ≥ -ε`. -/
theorem sectional_scaleMetric_O59 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (gM : SmoothRiemannianMetric ThreeModel M) (Q : ℝ) (hQ : 0 < Q) (w : M) {ε : ℝ}
    (h : SectionalBoundedBelowAt gM w (-(ε * Q))) :
    SectionalBoundedBelowAt (scaleMetric Q hQ gM) w (-ε) := by
  intro v u
  have hvu := h v u
  rw [metricRm04StandardAt_scaleMetric]
  simp only [scaleMetric_inner]
  have key := mul_le_mul_of_nonneg_left hvu hQ.le
  have e : ∀ a b c : ℝ, -ε * (Q * a * (Q * b) - (Q * c) ^ 2) =
      Q * (-(ε * Q) * (a * b - c ^ 2)) := by intros; ring
  rw [e]
  exact key

/-- **hA2 (LIMP v3) from the slice Shi bounds** (`[FROZEN] CH12-O59 G1`, plan G2). -/
theorem hA2_of_sliceShi_O59 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hShi : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
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
      ∀ hpos : ∀ n, 0 < metricScalarAt (s n).metric (y n),
      ∀ R : ℝ, 0 < R → R < ρ - (Real.sqrt 2)⁻¹ / 4 → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ w : (s n).stage.Carrier,
          riemannianEDistOf (scaleMetric (metricScalarAt (s n).metric (y n)) (hpos n) (s n).metric)
              (y n) w ≤ ENNReal.ofReal R →
            curvDerivNorm p (scaleMetric (metricScalarAt (s n).metric (y n)) (hpos n) (s n).metric) w ≤
              C) :
    ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
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
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) := by
  intro A hA s y ρ h1 h2 h3 h5 h6 h9 h11 a1
  have hpos : ∀ n, 0 < metricScalarAt (s n).metric (y n) := fun n =>
    lt_of_lt_of_le (inv_pos.mpr (pow_pos
      (Hp.parameters.neckRadius_pos _ (s n).positive.le) 2)) (h2 n)
  have hRb : 0 < ρ - (Real.sqrt 2)⁻¹ / 4 := by linarith [inv_sqrt_two_div_four_lt_O59]
  have hs2 : 0 < (Real.sqrt 2)⁻¹ / 4 := by positivity
  have hcompact : ∀ R : ℝ, 0 < R → R < ρ - (Real.sqrt 2)⁻¹ / 4 → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf
        (scaleMetric (metricScalarAt (s n).metric (y n)) (hpos n) (s n).metric) (y n) R) :=
    fun _ _ _ => Filter.Eventually.of_forall fun _ =>
      (DifferentialGeometry.Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact
  have hvol : ∀ r R : ℝ, 0 < r → r < R → R < ρ - (Real.sqrt 2)⁻¹ / 4 → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf
          (scaleMetric (metricScalarAt (s n).metric (y n)) (hpos n) (s n).metric) (y n) r,
        ENNReal.ofReal (κ * a ^ 3) ≤
          riemannianVolumeMeasure ThreeModel (s n).stage.Carrier
            (scaleMetric (metricScalarAt (s n).metric (y n)) (hpos n) (s n).metric)
            (riemannianBallOf (scaleMetric (metricScalarAt (s n).metric (y n)) (hpos n)
              (s n).metric) x a) := by
    intro r R hr hrR hRRb C hC
    obtain ⟨v, hv, hvℓ⟩ := a1 ((r + R) / 2) (by linarith) (by linarith)
    set a := min (min 1 ((R - r) / 2)) (1 / (C + 1)) with ha_def
    have ha1 : a ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
    have ha2 : a ≤ (R - r) / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have ha3 : a ≤ 1 / (C + 1) := min_le_right _ _
    have hapos : 0 < a := lt_min (lt_min one_pos (by linarith)) (by positivity)
    refine ⟨a, v, hapos, hv, by linarith, ?_, ?_⟩
    · have haC : a * C ≤ 1 := by
        rw [le_div_iff₀ (by linarith)] at ha3
        nlinarith
      have hac0 : 0 ≤ a * C := mul_nonneg hapos.le hC
      have h4 : a ^ 4 * C ^ 2 = a ^ 2 * (a * C) ^ 2 := by ring
      rw [h4]
      have hA : a ^ 2 ≤ 1 := by nlinarith
      have hB : (a * C) ^ 2 ≤ 1 := by nlinarith
      calc a ^ 2 * (a * C) ^ 2 ≤ 1 * 1 :=
            mul_le_mul hA hB (sq_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · filter_upwards [hvℓ a hapos (le_min ha1 (by linarith))] with n hn x hx
      set Q := metricScalarAt (s n).metric (y n) with hQ_def
      have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr (hpos n)
      have e1 : Real.sqrt Q * ((r + R) / 2 / Real.sqrt Q) = (r + R) / 2 := by field_simp
      have e2 : Real.sqrt Q * (a / Real.sqrt Q) = a := by field_simp
      have hx' : x ∈ riemannianBallOf (s n).metric (y n) ((r + R) / 2 / Real.sqrt Q) := by
        rw [← riemannianBallOf_scaleMetric Q (hpos n) (s n).metric (y n), e1]
        change riemannianEDistOf _ (y n) x < _
        exact lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
      have h := hn x hx'
      have h' : ENNReal.ofReal v * ENNReal.ofReal (a / Real.sqrt Q) ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (s n).stage.Carrier (s n).metric
            (riemannianBallOf (s n).metric x (a / Real.sqrt Q)) := by
        rw [← ENNReal.ofReal_pow (div_pos hapos hsQ).le, ← ENNReal.ofReal_mul hv.le]
        exact h
      have hiff := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
        (s n).metric Q (hpos n) x (a / Real.sqrt Q) (ENNReal.ofReal v)
      simp only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin, e2] at hiff
      rw [ENNReal.ofReal_mul hv.le, ENNReal.ofReal_pow hapos.le]
      exact hiff.mpr h'
  have hsec : ∀ r : ℝ, r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ w : (s n).stage.Carrier,
        riemannianEDistOf (scaleMetric (metricScalarAt (s n).metric (y n)) (hpos n) (s n).metric)
            (y n) w < ENNReal.ofReal r →
          SectionalBoundedBelowAt
            (scaleMetric (metricScalarAt (s n).metric (y n)) (hpos n) (s n).metric) w (-ε) := by
    intro r hr ε hε
    filter_upwards [sectional_almost_nonneg_on_ball_O45 Hp s y ρ h3 h9 r (by linarith) ε hε]
      with n hn w hw
    have hsQ : 0 < Real.sqrt (metricScalarAt (s n).metric (y n)) := Real.sqrt_pos.mpr (hpos n)
    have e1 : Real.sqrt (metricScalarAt (s n).metric (y n)) *
        (r / Real.sqrt (metricScalarAt (s n).metric (y n))) = r := by field_simp
    have hw' : w ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n))) := by
      rw [← riemannianBallOf_scaleMetric _ (hpos n) (s n).metric (y n), e1]
      exact hw
    exact sectional_scaleMetric_O59 _ _ (hpos n) w (hn w hw')
  obtain ⟨LM, i1, i2, i3, i4, i5, gL, x₀, f, hf, φ, src, hPHI, hbase, hrad0, hcl, -, -, hscal,
      hradial, hpair, hsecL, hscb⟩ :=
    sliceLocalCGv3_O59 (fun n => (s n).stage.Carrier) (fun n => (s n).metric) y
      (fun n => metricScalarAt (s n).metric (y n)) hpos hRb hcompact
      (hShi A hA s y ρ h1 h2 h3 h5 h6 h9 h11 a1 hpos) hvol hsec
  have hconv : ∀ k (a b : (s (f k)).stage.Carrier),
      (riemannianEDistOf (scaleMetric (metricScalarAt (s (f k)).metric (y (f k))) (hpos (f k))
          (s (f k)).metric) a b).toReal =
        Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
          (riemannianEDistOf (s (f k)).metric a b).toReal := by
    intro k a b
    rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  refine ⟨LM, i1, i2, i3, i4, i5, gL, x₀, f, hf, φ, ⟨src, hPHI⟩, hbase, hrad0, hcl, ?_, ?_,
    hsecL, hscb⟩
  · intro K hK ε hε
    filter_upwards [hscal K hK ε hε, hradial K hK ε hε] with k hk1 hk2 x hx
    refine ⟨hk1 x hx, ?_⟩
    rw [← hconv]
    exact hk2 x hx
  · intro K hK hK3 ε hε
    filter_upwards [hpair K hK hK3 ε hε] with k hk x hx x' hx'
    rw [← hconv]
    exact hk x hx x' hx'

end GC.LongTime.Ch12

end
