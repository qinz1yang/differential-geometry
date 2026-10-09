import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.FiniteTime

/-!
# Ball volumes and entropy for the U1 curvature bound

Chapter 7, packet P8, surface lemma U1, route (a), lane a3.

* `surfaceFlow_exists_ball_volume_lower`: Perelman's no-local-collapsing theorem
  (`no_local_collapsing`) for a Ricci flow on `[0, T)` on a compact connected surface: for a fixed
  scale `ρ` there is `κ > 0` such that a `g(t)`-ball of radius `r ≤ ρ` has area at least `κ r²` as
  soon as `r² ≤ t` and `r⁴ |Rm|² ≤ 1` on the backward window `[t - r², t]`.
* `surfaceEntropy_ge_of_ball`: if `R > 0` and `R ≥ c` on a measurable set `B` with `c · Area ≥ 1`,
  then Hamilton's entropy `∫ R log (R Area)` is at least `c log (c Area) μ(B) - 1`, from
  `R log (R A) ≥ (R A - 1) / A` off `B`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.Measure
open MeasureTheory Filter Topology Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  {T : ℝ} {hT : 0 < T}

private local instance volumeMeasurable : MeasurableSpace M := borel M
private local instance volumeBorel : BorelSpace M := ⟨rfl⟩

theorem surfaceFlow_exists_ball_volume_lower (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t ∈ Ioo 0 T, ∀ (x : M) (r : ℝ), 0 < r → r ≤ ρ → r ^ 2 ≤ t →
      (∀ u ∈ Icc (t - r ^ 2) t, ∀ y,
        r ^ 4 * normSq0S (S.family.metric u) y 4 (metricRm04At (S.family.metric u) y) ≤ 1) →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 2 ≤
        riemannianVolumeMeasure I M (S.family.metric t)
          {y | riemannianEDistOf (S.family.metric t) x y < ENNReal.ofReal r} := by
  obtain ⟨κ, hκ, -, hcol⟩ := no_local_collapsing hT S hS hρ
  refine ⟨κ, hκ, fun t ht x r hr hrρ hrt hcurv => ?_⟩
  let tt : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen 0 T hT) :=
    ⟨t, (⟨ht.1.le, ht.2⟩ : t ∈ Ico 0 T)⟩
  let B : FlowMetricBall S tt := ⟨x, r, hr⟩
  have hctrl : B.IsRmControlled := by
    refine ⟨fun u hu => (⟨by linarith [hu.1], lt_of_le_of_lt hu.2 ht.2⟩ : u ∈ Ico 0 T),
      fun u hu y _ => ?_⟩
    exact hcurv u hu y
  have h := (hcol tt B hrρ hctrl).2
  rw [hdim] at h
  exact h

omit [I.Boundaryless] in
theorem surfaceEntropy_ge_of_ball (g : SmoothRiemannianMetric I M)
    (hpos : ∀ x, 0 < metricScalarAt g x) {B : Set M} (hB : MeasurableSet B) {c : ℝ} (hc : 0 < c)
    (hcB : ∀ y ∈ B, c ≤ metricScalarAt g y) (hcA : 1 ≤ c * surfaceArea g) :
    c * Real.log (c * surfaceArea g) * (riemannianVolumeMeasure I M g B).toReal - 1 ≤
      surfaceEntropy g := by
  let μ := riemannianVolumeMeasure I M g
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set A := surfaceArea g with hAdef
  have hA : 0 < A := surfaceArea_pos (I := I) (M := M) g
  have hlogc : 0 ≤ Real.log (c * A) := Real.log_nonneg hcA
  let φ : M → ℝ := fun x => B.indicator (fun _ => c * Real.log (c * A)) x + -(1 / A)
  have hφint : Integrable φ μ :=
    ((integrable_const _).indicator hB).add (integrable_const _)
  have hRcont : Continuous (metricScalarAt g) := (metricScalar_smooth g).continuous
  have hfcont : Continuous (fun x => metricScalarAt g x * Real.log (metricScalarAt g x * A)) :=
    hRcont.mul ((hRcont.mul continuous_const).log fun x => (mul_pos (hpos x) hA).ne')
  have hfint : Integrable (fun x => metricScalarAt g x * Real.log (metricScalarAt g x * A)) μ :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ x, φ x ≤ metricScalarAt g x * Real.log (metricScalarAt g x * A) := by
    intro x
    by_cases hx : x ∈ B
    · simp only [φ, Set.indicator_of_mem hx]
      have hRx := hcB x hx
      have hle : Real.log (c * A) ≤ Real.log (metricScalarAt g x * A) :=
        Real.log_le_log (mul_pos hc hA) (mul_le_mul_of_nonneg_right hRx hA.le)
      have h1 : c * Real.log (c * A) ≤ metricScalarAt g x * Real.log (metricScalarAt g x * A) :=
        mul_le_mul hRx hle hlogc (hpos x).le
      have h2 : 0 ≤ 1 / A := by positivity
      linarith
    · simp only [φ, Set.indicator_of_notMem hx, zero_add]
      have hml := Real.self_sub_one_le_mul_log (mul_pos (hpos x) hA).le
      have heq : metricScalarAt g x * Real.log (metricScalarAt g x * A) =
          (metricScalarAt g x * A * Real.log (metricScalarAt g x * A)) / A := by
        field_simp
      rw [heq, le_div_iff₀ hA]
      have : -(1 / A) * A = -1 := by field_simp
      rw [this]
      nlinarith [(hpos x).le, hA.le]
  have hmono := integral_mono hφint hfint hpt
  have hφval : ∫ x, φ x ∂μ = c * Real.log (c * A) * (μ B).toReal - 1 := by
    simp only [φ]
    rw [integral_add ((integrable_const _).indicator hB) (integrable_const _),
      integral_indicator hB, setIntegral_const, integral_const]
    simp only [smul_eq_mul, measureReal_def]
    have hAμ : (μ Set.univ).toReal = A := by
      simp only [hAdef, surfaceArea, μ, measureReal_def]
    rw [hAμ]
    field_simp
    ring
  unfold surfaceEntropy
  rw [← hφval]
  exact hmono

end GC.Geometry
