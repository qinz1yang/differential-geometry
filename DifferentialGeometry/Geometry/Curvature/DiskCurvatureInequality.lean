import DifferentialGeometry.Geometry.Curvature.RegularizedGaussBonnet
import DifferentialGeometry.Geometry.Curvature.RegularizedIntegralComparison
import DifferentialGeometry.Geometry.Curvature.DiskBoundaryLimit
import DifferentialGeometry.Geometry.Curvature.DiskCurvatureDensity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCoefficientExtension









noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]





theorem SmoothDiskExtension.curvature_inequality
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ Metric.ball 0 1, diskMapTension g U q = 0)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ) :
    2 * Real.pi ≤
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapSectionalDensity g U z) +
      (∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity g U γ φ θ) := by
  obtain ⟨a, ha, _, han, haeq⟩ := hu.exists_nonneg_coefficient_extension g
  obtain ⟨κ, f, _, _, hκsupp, _, _, hf, _, hfΔ, hfν⟩ :=
    hu.exists_curvature_regularizer g
      (fun q hq => hconf q (Metric.ball_subset_closedBall hq)) hnon
  obtain ⟨_, s, hs, hDs, hU⟩ := hu
  let D := Metric.closedBall (0 : ℂ) 1
  have hD : IsCompact D := isCompact_closedBall _ _
  have hae (z : ℂ) (hz : z ∈ D) : a z = diskMapConformalCoefficient g U z :=
    (haeq z hz).eq_of_nhds
  have hB : IntegrableOn (diskMapSectionalDensity g U) D :=
    integrableOn_diskMapSectionalDensity g hs hU hD hDs hconf
  have hL : IntegrableOn (fun z => -Laplacian.laplacian f z) D :=
    (continuous_laplacian (hf.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).neg.continuousOn.integrableOn_compact hD
  have hBzero : ∀ᵐ z ∂volume.restrict D, a z = 0 → diskMapSectionalDensity g U z = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz hza
    simp only [diskMapSectionalDensity, ← hae z hz, hza, mul_zero]
  have hLzero : ∀ᵐ z ∂volume.restrict D, a z = 0 → -Laplacian.laplacian f z = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz hza
    rw [hfΔ z hz]
    by_contra hκz
    have hp := (hκsupp (subset_tsupport κ (Function.mem_support.mpr hκz))).2
    change 0 < diskMapConformalCoefficient g U z at hp
    rw [← hae z hz, hza] at hp
    exact (lt_irrefl 0) hp
  have hBl := tendsto_integral_regularizedConformalWeight_comp_of_zero
    (c := id) measurable_id ha.continuous.measurable hf.continuous.measurable
    (Eventually.of_forall han) hB hBzero
  have hLl := tendsto_integral_one_sub_regularizedConformalWeight_comp
    (c := id) measurable_id ha.continuous.measurable hf.continuous.measurable
    (Eventually.of_forall han) hL hLzero
  have hCl := tendsto_intervalIntegral_diskMapTraceBoundaryDensity g hs hU hDs hconf
    hγ hi hφ htrace ha.continuous.measurable hf.continuous.measurable han hae (-Real.pi) Real.pi
  have hlim := ((hBl.add hLl).add hCl).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [add_zero] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  have hε : ε ≠ 0 := ne_of_gt hεpos
  have hgb := gaussBonnet_regularizedDisk_trace g hs hU hDs hconf hγ hi hφ hm htrace
    ha hf han haeq hfν hε
  have hle := integral_regularizedDisk_curvatureDensity_le g hs hU hDs hconf hharm
    ha hf han haeq hε
  exact hgb.ge.trans (add_le_add hle le_rfl)

end DifferentialGeometry.Geometry
