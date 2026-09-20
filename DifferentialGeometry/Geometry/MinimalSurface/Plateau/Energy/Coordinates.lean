import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskReflectionDifferential
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section

open Manifold MeasureTheory Set
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

private theorem mfderiv_comp_linearEquiv
    {V W E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (U : W → M) (L : V ≃L[ℝ] W) (z : V) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (U ∘ L) z =
      (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) U (L z)).comp L.toContinuousLinearMap := by
  have hL : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) L z := L.differentiableAt.mdifferentiableAt
  by_cases hU : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, E) U (L z)
  · rw [mfderiv_comp z hU hL, mfderiv_eq_fderiv, L.hasFDerivAt.fderiv]
    rfl
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) (U ∘ L) z := by
      intro h
      have hi : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, V) L.symm (L z) :=
        L.symm.differentiableAt.mdifferentiableAt
      have h' : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) (U ∘ L) (L.symm (L z)) :=
        (L.symm_apply_apply z).symm ▸ h
      have heq : ((U ∘ L) ∘ L.symm) = U := by
        funext w
        simp only [Function.comp_apply, L.apply_symm_apply]
      exact hU (heq ▸ h'.comp (L z) hi)
    rw [mfderiv_zero_of_not_mdifferentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hU]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem sum_metric_mfderiv_plane_isometry
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∑ j : Fin 2, g.inner (U (Complex.orthonormalBasisOneI.repr.symm x))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
        (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
        (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))) =
      2 * diskMapEnergyDensity g U (Complex.orthonormalBasisOneI.repr.symm x) := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hd := mfderiv_comp_linearEquiv (E := E) U e.toContinuousLinearEquiv x
  have hde (j : Fin 2) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E) (U ∘ e) x
        (EuclideanSpace.single j 1) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e x) (e (EuclideanSpace.single j 1)) := by
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] E =>
      L (EuclideanSpace.single j 1)) hd
  have h0 : e (EuclideanSpace.single 0 (1 : ℝ)) = (1 : ℂ) := by simp [e]
  have h1 : e (EuclideanSpace.single 1 (1 : ℝ)) = Complex.I := by simp [e]
  change (∑ j : Fin 2, g.inner (U (e x))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E) (U ∘ e) x
        (EuclideanSpace.single j 1))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E) (U ∘ e) x
        (EuclideanSpace.single j 1))) = 2 * diskMapEnergyDensity g U (e x)
  simp only [Fin.sum_univ_two, hde, h0, h1, diskMapEnergyDensity, diskMapPartial]
  ring

theorem sum_integral_metric_mfderiv_plane_isometry
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hi : ∀ j : Fin 2, IntegrableOn (fun x : EuclideanSpace ℝ (Fin 2) =>
      g.inner (U (Complex.orthonormalBasisOneI.repr.symm x))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
          (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
          (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1)))
        (Metric.ball 0 1)) :
    (∑ j : Fin 2, ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      g.inner (U (Complex.orthonormalBasisOneI.repr.symm x))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
          (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
          (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))) =
      2 * ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g U z := by
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  simp_rw [sum_metric_mfderiv_plane_isometry]
  rw [integral_const_mul]
  congr 1
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hset : e ⁻¹' Metric.ball (0 : ℂ) 1 = Metric.ball 0 1 := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, e.norm_map]
  have hchange := e.measurePreserving.setIntegral_preimage_emb
    e.toMeasurableEquiv.measurableEmbedding (diskMapEnergyDensity g U) (Metric.ball (0 : ℂ) 1)
  rw [hset] at hchange
  apply hchange.trans
  apply setIntegral_congr_set
  have hball := (ae_restrict_iff' measurableSet_closedBall).mp ae_disk_interior
  filter_upwards [hball] with z hz
  exact propext ⟨fun h => Metric.ball_subset_closedBall h, hz⟩

end DifferentialGeometry.Geometry
