import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalChartFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalChartParallelAlign

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem x124_ray_parallel_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

omit [CompleteSpace E] in
/-- A target-parallel field in a genuine pole-chart extension pulls back to the original
interior metric of the corner manifold. The source chart and its metric identity are built from
the original boundary chart and the restricted metric. -/
theorem originalCorner_extension_parallel_pullback
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ v w : E,
      G.inner y v w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y v w)
    {t : ℝ} (δ : ℝ → E) (W : ∀ s, TangentSpace 𝓘(ℝ, E) (δ s))
    (hδ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ t)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent 2
      (fun s => (⟨δ s, W s⟩ : TangentBundle (𝓘(ℝ, E)) E)) t)
    (hparallel : covDerivAlong G δ W t = 0)
    (x : DifferentialGeometry.Manifold.intrinsicInterior I ∞
      x124_ray_parallel_infty_ne_zero (M := M))
    (hxchart : (x : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source)
    (hxcoord : extChartAt I p (x : M) = δ t)
    (hxO : extChartAt I p (x : M) ∈ O) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      x124_ray_parallel_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    let F := fun z : U => extChartAt I p (z : M)
    let S := {z : U | (z : M) ∈
        (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧ F z ∈ O}
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U E ∞,
      Φ.source = S ∧ (∀ z ∈ S, Φ z = F z) ∧
      (∀ z ∈ S, ∀ v w : TangentSpace 𝓘(ℝ, E) z,
        k.inner z v w = G.inner (Φ z)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z w)) ∧
      Φ.symm (δ t) = x ∧
      covDerivAlong k (fun s => Φ.symm (δ s))
        (fun s => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W s)) t = 0 := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    x124_ray_parallel_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  let F := fun z : U => extChartAt I p (z : M)
  let S := {z : U | (z : M) ∈
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧ F z ∈ O}
  dsimp only
  have hxS : x ∈ S := ⟨hxchart, hxO⟩
  obtain ⟨Φ, hsource, hmap, hmetric⟩ :=
    boundaryOriginal_chart_partial_isometry g p G O hG ⟨x, hxS⟩
  have hxΦ : x ∈ Φ.source := hsource.symm ▸ hxS
  have hxmap : Φ x = δ t := (hmap x hxS).trans hxcoord
  have htarget : δ t ∈ Φ.target := by
    exact hxmap ▸ Φ.map_source hxΦ
  have hinv : Φ.symm (δ t) = x :=
    (congrArg Φ.symm hxmap.symm).trans (Φ.left_inv' hxΦ)
  have hmetric' : ∀ z ∈ Φ.source, ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      G.inner (Φ z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z w) = k.inner z v w := by
    intro z hz v w
    rw [hsource] at hz
    exact (hmetric z hz v w).symm
  have hpull := partialIsometry_pullback_parallel_on_target k G Φ hmetric'
    δ W htarget hδ hW hparallel
  exact ⟨Φ, hsource, hmap, hmetric, hinv, hpull⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
