import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorCurveLength
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric
import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength

/-!
Actual unit native rays bound original subsegment and pole distances by physical elapsed time.
The original pole point limit closes the positive-time bound without placing that pole inside.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem positiveRayDistance_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

omit ambientFinite manifoldT2 in
private theorem unitArcLength_of_Ioo (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {a b : ℝ} (hab : a ≤ b)
    (hunit : ∀ t ∈ Ioo a b, g.inner (γ t)
      (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)) = 1) :
    arcLength g γ a b = b - a := by
  unfold arcLength
  calc
    _ = ∫ _t in a..b, (1 : ℝ) :=
      intervalIntegral.integral_congr_Ioo_of_le hab (fun t ht => by
        rw [hunit t ht, Real.sqrt_one])
    _ = b - a := by simp

theorem boundaryInterior_positive_ray_distance (g : SmoothRiemannianMetric I M) (p : M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      positiveRayDistance_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (γ : ℝ → U) (T : ℝ),
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Ioc 0 T) →
      (∀ t ∈ Ioo 0 T, k.inner (γ t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)) = 1) →
      Tendsto (fun t : ℝ => (γ t : M)) (𝓝[>] (0 : ℝ)) (𝓝 p) →
      (∀ s ∈ Ioc 0 T, ∀ t ∈ Ioc 0 T, s ≤ t →
        DifferentialGeometry.riemannianEDistOf g (γ s : M) (γ t : M) ≤
          ENNReal.ofReal (t - s)) ∧
      ∀ t ∈ Ioc 0 T, DifferentialGeometry.riemannianEDistOf g p (γ t : M) ≤
        ENNReal.ofReal t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    positiveRayDistance_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro γ T hγ hunit hpole
  have hpair (s : ℝ) (hs : s ∈ Ioc 0 T) (t : ℝ) (ht : t ∈ Ioc 0 T) (hst : s ≤ t) :
      DifferentialGeometry.riemannianEDistOf g (γ s : M) (γ t : M) ≤
        ENNReal.ofReal (t - s) := by
    have hC : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Icc s t) := hγ.mono
      (fun r hr => ⟨lt_of_lt_of_le hs.1 hr.1, hr.2.trans ht.2⟩)
    have hl := unitArcLength_of_Ioo k γ hst (fun r hr => hunit r
      ⟨lt_of_lt_of_le hs.1 hr.1.le, lt_of_lt_of_le hr.2 ht.2⟩)
    exact (boundaryInterior_curve_length g γ s t hst hC).2.trans_eq
      (congrArg ENNReal.ofReal hl)
  refine ⟨hpair, ?_⟩
  intro t ht
  have hcont : Continuous (fun q : M => DifferentialGeometry.riemannianEDistOf g q (γ t : M)) :=
    (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g (γ t : M)).congr
      (fun q => DifferentialGeometry.riemannianEDistOf_comm g (γ t : M) q)
  have hleft := hcont.continuousAt.tendsto.comp hpole
  have hright : Tendsto (fun ε : ℝ => ENNReal.ofReal (t - ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal t)) := by
    have hsub : Continuous (fun ε : ℝ => t - ε) := continuous_const.sub continuous_id
    have hh : Tendsto (fun ε : ℝ => ENNReal.ofReal (t - ε))
        (𝓝 (0 : ℝ)) (𝓝 (ENNReal.ofReal (t - 0))) :=
      (ENNReal.continuous_ofReal.comp hsub).continuousAt.tendsto
    simpa only [sub_zero] using hh.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds] with ε hε hεt
    exact ⟨hε, hεt⟩
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hnear] with ε hε
  exact hpair ε ⟨hε.1, hε.2.le.trans ht.2⟩ t ht hε.2.le

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
