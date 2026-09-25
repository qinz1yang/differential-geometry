import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SmoothSmallBallBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SmoothBallVolumeContinuity
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff ENNReal _root_.Topology

private theorem tendsto_one_of_eventual_real_bounds
    {α : Type*} {l : Filter α} {f : α → ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ a in l,
      ENNReal.ofReal (1 - ε) ≤ f a ∧ f a ≤ ENNReal.ofReal (1 + ε)) :
    Tendsto f l (𝓝 1) := by
  have hfinite : ∀ᶠ a in l, f a ≠ ⊤ := by
    filter_upwards [h (1 / 2) (by norm_num) (by norm_num)] with a ha
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha.2
  have hreal : Tendsto (fun a => (f a).toReal) l (𝓝 (1 : ℝ)) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    let δ : ℝ := min (ε / 2) (1 / 2)
    have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
    have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    filter_upwards [h δ hδ hδ1, hfinite] with a ha hfin
    have hlo := ENNReal.toReal_mono hfin ha.1
    have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top ha.2
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1.le)] at hlo
    rw [ENNReal.toReal_ofReal (by linarith only [hδ] : 0 ≤ 1 + δ)] at hhi
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith only [hlo, hδε], by linarith only [hhi, hδε]⟩
  have hback : (fun a => ENNReal.ofReal (f a).toReal) =ᶠ[l] f := by
    filter_upwards [hfinite] with a ha
    exact ENNReal.ofReal_toReal ha
  simpa only [ENNReal.ofReal_one] using (ENNReal.tendsto_ofReal hreal).congr' hback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [ConnectedSpace M]

private local instance smallBallModelMeasurable : MeasurableSpace E := borel E
private local instance smallBallModelBorel : BorelSpace E := ⟨rfl⟩
private local instance smallBallMeasurable : MeasurableSpace M := borel M
private local instance smallBallBorel : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem tendsto_normalizedBallVolumeRatio_nhdsGT_zero
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M) :
    Tendsto (normalizedBallVolumeRatio g p) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  apply tendsto_one_of_eventual_real_bounds
  intro ε hε hε1
  obtain ⟨ρ, hρ, hbounds⟩ := riemannianBallOf_volume_small_radius_bounds
    g hcomplete p hε hε1
  filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
  have hden0 : euclideanUnitBallVolume (Module.finrank ℝ E) *
      ENNReal.ofReal (r ^ Module.finrank ℝ E) ≠ 0 :=
    mul_ne_zero (euclideanUnitBallVolume_pos _).ne'
      (ENNReal.ofReal_pos.mpr (pow_pos hr.1 _)).ne'
  have hdent : euclideanUnitBallVolume (Module.finrank ℝ E) *
      ENNReal.ofReal (r ^ Module.finrank ℝ E) ≠ ⊤ :=
    ENNReal.mul_ne_top (euclideanUnitBallVolume_ne_top _) ENNReal.ofReal_ne_top
  obtain ⟨hlo, hhi⟩ := hbounds r hr.1 hr.2
  constructor
  · exact (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)).mpr hlo
  · exact (ENNReal.div_le_iff hden0 hdent).mpr hhi

theorem tendsto_riemannianBallOf_volume_div_pow_nhdsGT_zero
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M) :
    Tendsto (fun r : ℝ =>
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) /
        ENNReal.ofReal (r ^ Module.finrank ℝ E))
      (𝓝[>] (0 : ℝ)) (𝓝 (euclideanUnitBallVolume (Module.finrank ℝ E))) := by
  have hlim := ENNReal.Tendsto.const_mul
    (a := euclideanUnitBallVolume (Module.finrank ℝ E))
    (tendsto_normalizedBallVolumeRatio_nhdsGT_zero g hcomplete p) (Or.inl one_ne_zero)
  rw [mul_one] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro r
  unfold normalizedBallVolumeRatio
  simpa only [mul_div_assoc] using
    (ENNReal.mul_div_mul_left
      (riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r))
      (ENNReal.ofReal (r ^ Module.finrank ℝ E))
      (euclideanUnitBallVolume_pos _).ne' (euclideanUnitBallVolume_ne_top _))

theorem tendsto_riemannianBallOf_realVolume_div_pow_nhdsGT_zero
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M) :
    Tendsto (fun r : ℝ =>
      (riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r)).toReal /
        r ^ Module.finrank ℝ E)
      (𝓝[>] (0 : ℝ)) (𝓝 (euclideanUnitBallVolume (Module.finrank ℝ E)).toReal) := by
  have hlim := (ENNReal.tendsto_toReal (euclideanUnitBallVolume_ne_top _)).comp
    (tendsto_riemannianBallOf_volume_div_pow_nhdsGT_zero g hcomplete p)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  simp only [Function.comp_apply, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (pow_nonneg hrpos.le _)]

private theorem riemannianBallOf_volume_continuity_data
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) :
    ContinuousAt (fun r : ℝ =>
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r)) R ∧
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p R) ≠ ⊤ := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  exact ⟨smooth_segBall_vol_cont (I := I) g hEnorm p hR,
    (segmentBall_vol_fin (I := I) g hEnorm p (R := R)).ne⟩

theorem continuousAt_riemannianBallOf_volume
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) :
    ContinuousAt (fun r : ℝ =>
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r)) R :=
  (riemannianBallOf_volume_continuity_data g hcomplete p hR).1

theorem continuousAt_riemannianBallOf_realVolume_div_pow
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) :
    ContinuousAt (fun r : ℝ =>
      (riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r)).toReal /
        r ^ Module.finrank ℝ E) R := by
  obtain ⟨hvol, hfinite⟩ := riemannianBallOf_volume_continuity_data g hcomplete p hR
  exact ((ENNReal.continuousAt_toReal hfinite).comp
    (f := fun r : ℝ =>
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r)) hvol).div
    (continuousAt_id.pow _) (pow_ne_zero _ hR.ne')

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
