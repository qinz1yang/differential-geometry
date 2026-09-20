import DifferentialGeometry.Geometry.HarmonicMap.ConformalSource
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Analysis.Elliptic.MetricExtension

noncomputable section
open Set Filter Bundle Manifold InnerProductSpace
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem toEuclidean_chartCoord (v : E) (k : Fin (Module.finrank ℝ E)) :
    toEuclidean v k = chartCoord k v := by
  unfold chartCoord chartModelBasis
  rw [Module.Basis.map_repr]
  change toEuclidean v k = (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).repr
    (toEuclidean v) k
  exact (EuclideanSpace.basisFun_repr _ _ _ k).symm


private theorem toEuclidean_christoffelContraction
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) (v w y : E)
    (k : Fin (Module.finrank ℝ E)) :
    toEuclidean (chartChristoffelContraction g p v w y) k =
      ∑ a, ∑ b, chartChristoffel g p a b k y * toEuclidean v a * toEuclidean w b := by
  rw [toEuclidean_chartCoord]
  simp only [chartChristoffelContraction, chartCoord, Module.Basis.repr_sum_self]
  simp only [toEuclidean_chartCoord, chartCoord]


theorem diskMapTension_eq_zero_of_chart_laplacian
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 U z) {p : M}
    (hsrc : U z ∈ (chartAt E p).source)
    (heq : let X : ℂ → H := fun x => toEuclidean (extChartAt 𝓘(ℝ, E) p (U x))
      ∀ k, Laplacian.laplacian (fun x => X x k) z =
        -(∑ j : Fin 2, ∑ a, ∑ b,
          chartChristoffel g p a b k ((toEuclidean (E := E)).symm (X z)) *
            (fderiv ℝ X z (Complex.orthonormalBasisOneI j)) a *
            (fderiv ℝ X z (Complex.orthonormalBasisOneI j)) b)) :
    diskMapTension g U z = 0 := by
  let Y : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  let X : ℂ → H := fun x => toEuclidean (Y x)
  have hY : ContDiffAt ℝ 2 Y z :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 2) hsrc).comp z hU).contDiffAt
  have hd (v : ℂ) : fderiv ℝ X z v = toEuclidean (fderiv ℝ Y z v) := by
    rw [show X = (toEuclidean (E := E)) ∘ Y from rfl]
    have hh := (toEuclidean (E := E)).hasFDerivAt.comp z
      (hY.differentiableAt (by norm_num)).hasFDerivAt
    rw [hh.fderiv]
    rfl
  have hΔ (k : Fin (Module.finrank ℝ E)) :
      Laplacian.laplacian (fun x => X x k) z =
        toEuclidean (Laplacian.laplacian Y z) k := by
    let L : E →L[ℝ] ℝ := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (Module.finrank ℝ E) => ℝ) k).comp
      (toEuclidean (E := E)).toContinuousLinearMap
    exact hY.laplacian_CLM_comp_left (l := L)
  have hzero : Laplacian.laplacian Y z +
      chartChristoffelContraction g p (fderiv ℝ Y z 1) (fderiv ℝ Y z 1) (Y z) +
      chartChristoffelContraction g p (fderiv ℝ Y z Complex.I)
        (fderiv ℝ Y z Complex.I) (Y z) = 0 := by
    apply (toEuclidean (E := E)).injective
    ext k
    simp only [map_add, map_zero, PiLp.add_apply, PiLp.zero_apply]
    rw [← hΔ k, toEuclidean_christoffelContraction, toEuclidean_christoffelContraction]
    have hh := heq k
    change Laplacian.laplacian (fun x => X x k) z =
      -(∑ j : Fin 2, ∑ a, ∑ b,
        chartChristoffel g p a b k ((toEuclidean (E := E)).symm (X z)) *
          (fderiv ℝ X z (Complex.orthonormalBasisOneI j)) a *
          (fderiv ℝ X z (Complex.orthonormalBasisOneI j)) b) at hh
    have hXz : (toEuclidean (E := E)).symm (X z) = Y z :=
      ContinuousLinearEquiv.symm_apply_apply _ _
    rw [hXz] at hh
    simp only [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI,
      Matrix.cons_val_zero, Matrix.cons_val_one, hd] at hh
    change Laplacian.laplacian (fun x => X x k) z + _ + _ = 0
    linarith
  have hchart := chart_planarTension g hU hsrc
  have hb : U z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
  let τ := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  apply (τ.continuousLinearEquivAt ℝ (U z) hb).injective
  simp only [Trivialization.coe_continuousLinearEquivAt_eq τ hb, map_zero]
  change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (U z)
    (planarTension g U z) = 0
  exact hchart.trans hzero

end DifferentialGeometry.Geometry

end
