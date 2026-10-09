import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskArea
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskBoundaryMetric
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set Manifold MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem isExteriorSpanningDisk.isSmoothEmbeddedLoop
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u) :
    IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ := by
  obtain ⟨htrace, _, hemb, _, _, U, hU, himm⟩ := hu
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞
      (fun t : ℝ => γ (t : loopCircle)) := by
    simpa only [htrace] using hU.smoothUpToBoundary.trace
  have hboundary : _root_.Topology.IsEmbedding diskBoundary := by
    apply _root_.Topology.IsEmbedding.of_comp diskBoundary.continuous continuous_subtype_val
    change _root_.Topology.IsEmbedding (fun θ : loopCircle => (AddCircle.toCircle θ : ℂ))
    have heq :
        (fun θ : loopCircle => (AddCircle.toCircle θ : ℂ)) =
          (Subtype.val : Circle → ℂ) ∘
            (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) := by
      funext θ
      exact congrArg Subtype.val
        (AddCircle.homeomorphCircle_apply one_ne_zero θ).symm
    rw [heq]
    exact _root_.Topology.IsEmbedding.subtypeVal.comp
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).isEmbedding
  refine ⟨hsmooth, ?_, ?_⟩
  · rw [← htrace]
    exact hemb.comp hboundary
  · intro t
    let b : ℝ → ℂ := fun s => circleMap 0 1 (2 * Real.pi * s)
    have hb (s : ℝ) : b s = (diskBoundary (s : loopCircle) : ℂ) := by
      simp [b, circleMap, diskBoundary_coe]
    have hbmem (s : ℝ) : b s ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [hb]
      exact (diskBoundary (s : loopCircle)).property
    have htrace' : U ∘ b = fun s : ℝ => γ (s : loopCircle) := by
      funext s
      rw [Function.comp_apply, hb, hU.1]
      exact congrArg (fun η : freeLoop M => η (s : loopCircle)) htrace
    have hbder : HasDerivAt b
        ((2 * Real.pi) • (circleMap 0 1 (2 * Real.pi * t) * Complex.I)) t := by
      have hscale : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) t := by
        simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
      exact (hasDerivAt_circleMap 0 1 (2 * Real.pi * t)).scomp t hscale
    obtain ⟨_, N, hN, hDN, hUs⟩ := hU
    have hUt : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 3) U (b t) :=
      (hUs.contMDiffAt (hN.mem_nhds (hDN (hbmem t)))).mdifferentiableAt (by simp)
    have hv := congrArg
      (fun p : TangentBundle (𝓡 3) M => (p.2 : EuclideanSpace ℝ (Fin 3)))
      (tangent_velocity_comp hUt hbder.differentiableAt)
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (U ∘ b) t (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U (b t) (deriv b t) at hv
    erw [htrace', hbder.deriv] at hv
    intro hzero
    have hvec : (2 * Real.pi) •
        (circleMap 0 1 (2 * Real.pi * t) * Complex.I) = (0 : ℂ) :=
      (himm _ (hbmem t)) (hv.symm.trans (hzero.trans (map_zero _).symm))
    have hcircle : circleMap 0 1 (2 * Real.pi * t) ≠ (0 : ℂ) :=
      circleMap_ne_center one_ne_zero
    exact (smul_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (mul_ne_zero hcircle Complex.I_ne_zero)) hvec

end DifferentialGeometry.Geometry.MinimalSurface
