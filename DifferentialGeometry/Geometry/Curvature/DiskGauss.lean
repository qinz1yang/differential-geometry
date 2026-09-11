import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskBochner
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalSecondPartial
import DifferentialGeometry.Geometry.Metric.OrthogonalPlaneNormal
import DifferentialGeometry.Geometry.Curvature.SectionalContraction



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def diskMapNormalPartial (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z v w : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  orthogonalPlaneNormal g (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I)
    (diskMapCovariantPartial g U z v w)





theorem diskMap_gauss_identity [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {z : ℂ} (hz : z ∈ s) (ha : 0 < diskMapConformalCoefficient g U z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (diskMapConformalCoefficient g U q)) z =
      g.inner (U z) (riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
          (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) (diskMapPartial U z 1) /
        diskMapConformalCoefficient g U z -
      (g.inner (U z) (diskMapNormalPartial g U z 1 1) (diskMapNormalPartial g U z 1 1) +
        g.inner (U z) (diskMapNormalPartial g U z Complex.I 1)
          (diskMapNormalPartial g U z Complex.I 1)) / diskMapConformalCoefficient g U z := by
  have hc := hconf z hz
  have hq : g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I) ≠ 0 := by
    rw [← hc.2]
    exact ha.ne'
  have hreg : ContDiffAt ℝ 2 (diskMapConformalCoefficient g U) z :=
    ((contDiffOn_diskMapConformalCoefficient g hs hU z hz).contDiffAt
      (hs.mem_nhds hz)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have ht := diskMapCovariantPartial_tangent_components g hs hU hconf hz
  rw [DifferentialGeometry.Analysis.laplacian_log hreg ha.ne',
    laplacian_diskMapConformalCoefficient_of_harmonic g hs hU hharm hz]
  unfold diskMapNormalPartial
  rw [orthogonalPlaneNormal_inner_self g (U z) _ _ _ hc.1 ha.ne' hq,
    orthogonalPlaneNormal_inner_self g (U z) _ _ _ hc.1 ha.ne' hq]
  rw [← hc.2, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]
  change -(1 / 2 : ℝ) * (_ / diskMapConformalCoefficient g U z -
    _ / (diskMapConformalCoefficient g U z) ^ 2) = _
  change -(1 / 2 : ℝ) * (_ / diskMapConformalCoefficient g U z -
    _ / (diskMapConformalCoefficient g U z) ^ 2) =
    _ / diskMapConformalCoefficient g U z -
      ((_ - _ / diskMapConformalCoefficient g U z - _ / diskMapConformalCoefficient g U z) +
       (_ - _ / diskMapConformalCoefficient g U z - _ / diskMapConformalCoefficient g U z)) /
        diskMapConformalCoefficient g U z
  field_simp
  ring



theorem diskMap_curvature_density_le [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {z : ℂ} (hz : z ∈ s) (ha : 0 < diskMapConformalCoefficient g U z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (diskMapConformalCoefficient g U q)) z ≤
      g.inner (U z) (riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
          (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) (diskMapPartial U z 1) /
        diskMapConformalCoefficient g U z := by
  rw [diskMap_gauss_identity g hs hU hconf hharm hz ha]
  have hnonneg (v w : ℂ) : 0 ≤
      g.inner (U z) (diskMapNormalPartial g U z v w) (diskMapNormalPartial g U z v w) :=
    (g.toRiemannianMetric.toCore (U z)).re_inner_nonneg (diskMapNormalPartial g U z v w)
  exact sub_le_self _ (div_nonneg (add_nonneg (hnonneg 1 1) (hnonneg Complex.I 1)) ha.le)



theorem DiskMapConformalAt.sectional_mul_coefficient [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) :
    sectionalCurvature g (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) *
        diskMapConformalCoefficient g U z =
      g.inner (U z) (riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
          (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) (diskMapPartial U z 1) /
        diskMapConformalCoefficient g U z := by
  by_cases ha : diskMapConformalCoefficient g U z = 0
  · simp only [ha, mul_zero, div_zero]
  · rw [sectionalCurvature_eq_riemann, hc.1, ← hc.2,
      g.symm (U z) (diskMapPartial U z 1)]
    change _ / (diskMapConformalCoefficient g U z * diskMapConformalCoefficient g U z - 0 ^ 2) *
      diskMapConformalCoefficient g U z = _ / diskMapConformalCoefficient g U z
    field_simp
    ring



theorem diskMap_curvature_density_le_sectional [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {z : ℂ} (hz : z ∈ s) (ha : 0 < diskMapConformalCoefficient g U z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (diskMapConformalCoefficient g U q)) z ≤
      sectionalCurvature g (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) *
        diskMapConformalCoefficient g U z := by
  rw [(hconf z hz).sectional_mul_coefficient]
  exact diskMap_curvature_density_le g hs hU hconf hharm hz ha

end DifferentialGeometry.Geometry
