import DifferentialGeometry.Topology.Manifold.SphereRadialChart
import DifferentialGeometry.Topology.Manifold.SphereRadialDiffeomorph
import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianCoordinates
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module

noncomputable section
open Set Metric Filter Topology Manifold Module
open scoped ContDiff

namespace Poincare.Topology.Manifold

theorem det_radial_pos_iff_det_chart_pos
    (e : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ℂ)
    (htarget : e.target = univ)
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ e.symm e.target)
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hv : v ∈ e.source) (hfv : f v ∈ e.source) :
    0 < (fderiv ℝ (sphereRadialExtension f) (v : EuclideanSpace ℝ (Fin 3))).toLinearMap.det ↔
      0 < (fderiv ℝ (fun z ↦ e (f (e.symm z))) (e v)).toLinearMap.det := by
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  obtain ⟨c, hcs, hcfor, _, _⟩ := exists_smooth_radial_chart e htarget he hei
  let L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ℝ × ℂ :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let a : ℝ × ℂ := (1, e v)
  let F := sphereRadialExtension f
  let g : ℂ → ℂ := fun z ↦ e (f (e.symm z))
  let G : ℝ × ℂ → ℝ × ℂ := fun q ↦ (q.1, g q.2)
  let U : Set ℂ := (fun z ↦ f (e.symm z)) ⁻¹' e.source
  have hi : ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞ e.symm := contMDiffOn_univ.mp (htarget ▸ hei)
  have hU : IsOpen U := e.open_source.preimage (f.continuous.comp hi.continuous)
  have hevU : e v ∈ U := by
    change f (e.symm (e v)) ∈ e.source
    rw [e.left_inv hv]
    exact hfv
  have hg : ContDiffOn ℝ ∞ g U :=
    (he.comp (f.contMDiff.comp hi).contMDiffOn (fun _ hz ↦ hz)).contDiffOn
  have hga : HasFDerivAt g (fderiv ℝ g (e v)) (e v) :=
    ((hg.contDiffAt (hU.mem_nhds hevU)).differentiableAt (by simp)).hasFDerivAt
  have hgsnd : HasFDerivAt (fun q : ℝ × ℂ ↦ g q.2)
      ((fderiv ℝ g (e v)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)) a := by
    dsimp only [a]
    convert hga.comp (1, e v) (show HasFDerivAt (Prod.snd : ℝ × ℂ → ℂ)
      (ContinuousLinearMap.snd ℝ ℝ ℂ) (1, e v) from hasFDerivAt_snd) using 1 <;> rfl
  have hG : HasFDerivAt G ((ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ g (e v))) a :=
    hasFDerivAt_fst.prodMk hgsnd
  have hca : c a = (v : EuclideanSpace ℝ (Fin 3)) := by
    rw [hcfor]
    change (1 : ℝ) • (e.symm (e v) : EuclideanSpace ℝ (Fin 3)) = _
    rw [e.left_inv hv, one_smul]
  have hF : DifferentiableAt ℝ F (c a) := by
    rw [hca]
    exact ((contDiffOn_sphereRadialExtension f f.contMDiff).contDiffAt
      (isOpen_compl_singleton.mem_nhds (ne_zero_of_mem_unit_sphere v))).differentiableAt (by simp)
  have hcomm : F ∘ c =ᶠ[𝓝 a] c ∘ G := by
    have haU : a ∈ Ioi (0 : ℝ) ×ˢ U := ⟨show (0 : ℝ) < 1 from zero_lt_one, hevU⟩
    filter_upwards [(isOpen_Ioi.prod hU).mem_nhds haU] with q hq
    change F (c q) = c (G q)
    rw [hcfor, hcfor]
    change sphereRadialExtension f (q.1 • (e.symm q.2 : EuclideanSpace ℝ (Fin 3))) =
      q.1 • (e.symm (e (f (e.symm q.2))) : EuclideanSpace ℝ (Fin 3))
    rw [sphereRadialExtension_pos_smul _ _ hq.1, e.left_inv hq.2]
  have hconn : IsPreconnected c.source := by
    rw [hcs]
    exact (convex_Ioi (0 : ℝ)).isPreconnected.prod convex_univ.isPreconnected
  have ha : a ∈ c.source := hcs ▸ ⟨show (0 : ℝ) < 1 from zero_lt_one, mem_univ _⟩
  have hGa : G a ∈ c.source := hcs ▸ ⟨show (0 : ℝ) < 1 from zero_lt_one, mem_univ _⟩
  have hsign := Poincare.Analysis.det_fderiv_pos_iff_of_equivalent_coordinates
    L c hconn F G ha hGa hF hG.differentiableAt hcomm
  rw [hca, hG.fderiv] at hsign
  change 0 < (fderiv ℝ F (v : EuclideanSpace ℝ (Fin 3))).toLinearMap.det ↔
    0 < (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fderiv ℝ g (e v)).toLinearMap).det at hsign
  simpa only [LinearMap.det_prodMap, LinearMap.det_id, one_mul] using hsign

end Poincare.Topology.Manifold
