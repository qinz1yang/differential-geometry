import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPositiveRayDistance
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMinimum
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric
import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength

/-!
A true original endpoint minimum forces positive native prefixes and subsegments to minimize.
Unit-speed distance bounds and finite metric cancellation derive every native competitor minimum.
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

private theorem alivePrefixMinimum_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInterior_alive_prefix_minimum (g : SmoothRiemannianMetric I M) (p : M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      alivePrefixMinimum_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (γ : ℝ → U) (T : ℝ), 0 < T →
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Ioc 0 T) →
      (∀ t ∈ Ioo 0 T, k.inner (γ t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)) = 1) →
      Tendsto (fun t : ℝ => (γ t : M)) (𝓝[>] (0 : ℝ)) (𝓝 p) →
      DifferentialGeometry.riemannianEDistOf g p (γ T : M) = ENNReal.ofReal T →
      (∀ t ∈ Ioc 0 T, DifferentialGeometry.riemannianEDistOf g p (γ t : M) =
        ENNReal.ofReal t) ∧
      (∀ s ∈ Ioc 0 T, ∀ t ∈ Ioc 0 T, s ≤ t →
        DifferentialGeometry.riemannianEDistOf g (γ s : M) (γ t : M) =
          ENNReal.ofReal (t - s)) ∧
      ∀ s ∈ Ioc 0 T, ∀ t ∈ Ioc 0 T, s ≤ t →
        ∀ η : ℝ → U, ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 η (Icc s t) →
          η s = γ s → η t = γ t → arcLength k γ s t ≤ arcLength k η s t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    alivePrefixMinimum_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro γ T hT hγ hunit hpole hminimum
  obtain ⟨hupperPair, hupperPole⟩ :=
    boundaryInterior_positive_ray_distance g p γ T hγ hunit hpole
  have hsum (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      ENNReal.ofReal t = ENNReal.ofReal s + ENNReal.ofReal (t - s) :=
    (congrArg ENNReal.ofReal (by ring : t = s + (t - s))).trans
      (ENNReal.ofReal_add hs (sub_nonneg.mpr hst))
  have hprefix (s : ℝ) (hs : s ∈ Ioc 0 T) :
      DifferentialGeometry.riemannianEDistOf g p (γ s : M) = ENNReal.ofReal s := by
    have htri := (DifferentialGeometry.riemannianEDistOf_triangle g p (γ s : M) (γ T : M)).trans
      (add_le_add le_rfl (hupperPair s hs T ⟨hT, le_rfl⟩ hs.2))
    rw [hminimum, hsum s T hs.1.le hs.2] at htri
    have hlower := (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp htri
    exact le_antisymm (hupperPole s hs) hlower
  have hpair (s : ℝ) (hs : s ∈ Ioc 0 T) (t : ℝ) (ht : t ∈ Ioc 0 T) (hst : s ≤ t) :
      DifferentialGeometry.riemannianEDistOf g (γ s : M) (γ t : M) =
        ENNReal.ofReal (t - s) := by
    have htri := DifferentialGeometry.riemannianEDistOf_triangle g p (γ s : M) (γ t : M)
    rw [hprefix t ht, hprefix s hs, hsum s t hs.1.le hst] at htri
    have hlower := (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp htri
    exact le_antisymm (hupperPair s hs t ht hst) hlower
  refine ⟨hprefix, hpair, ?_⟩
  intro s hs t ht hst
  exact boundaryInterior_curve_minimizing g γ s t hst (fun r hr => hunit r
    ⟨lt_of_lt_of_le hs.1 hr.1.le, lt_of_lt_of_le hr.2 ht.2⟩) (hpair s hs t ht hst)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
