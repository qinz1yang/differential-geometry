import DifferentialGeometry.Topology.Manifold.SphereRadialExtension
import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Set Metric Manifold Module
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

def sphereRadialDiffeomorph
    (f : Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toFun := sphereRadialExtension f
  invFun := sphereRadialExtension f.symm
  source := {0}ᶜ
  target := {0}ᶜ
  map_source' := by
    intro x hx
    change sphereRadialExtension f x ≠ 0
    intro h
    have hn := norm_sphereRadialExtension f x
    rw [h, norm_zero] at hn
    exact hx (norm_eq_zero.mp hn.symm)
  map_target' := by
    intro x hx
    change sphereRadialExtension f.symm x ≠ 0
    intro h
    have hn := norm_sphereRadialExtension f.symm x
    rw [h, norm_zero] at hn
    exact hx (norm_eq_zero.mp hn.symm)
  left_inv' := by
    intro x _
    have heq : f.symm ∘ f = id := funext f.symm_apply_apply
    have h := sphereRadialExtension_comp (f : _ → _) (f.symm : _ → _)
    rw [heq, sphereRadialExtension_id] at h
    exact (congrFun h x).symm
  right_inv' := by
    intro x _
    have heq : f ∘ f.symm = id := funext f.apply_symm_apply
    have h := sphereRadialExtension_comp (f.symm : _ → _) (f : _ → _)
    rw [heq, sphereRadialExtension_id] at h
    exact (congrFun h x).symm
  open_source := isOpen_compl_singleton
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun := (contDiffOn_sphereRadialExtension f f.contMDiff).contMDiffOn
  contMDiffOn_invFun := (contDiffOn_sphereRadialExtension f.symm f.symm.contMDiff).contMDiffOn

theorem det_fderiv_sphereRadialExtension_ne_zero
    (f : Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞)
    {x : E} (hx : x ≠ 0) :
    (fderiv ℝ (sphereRadialExtension f) x).toLinearMap.det ≠ 0 :=
  Poincare.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph (sphereRadialDiffeomorph f) hx

theorem det_fderiv_sphereRadialExtension_pos_iff
    (hrank : 1 < Module.rank ℝ E)
    (f : Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    0 < (fderiv ℝ (sphereRadialExtension f) x).toLinearMap.det ↔
      0 < (fderiv ℝ (sphereRadialExtension f) y).toLinearMap.det :=
  Poincare.Analysis.det_fderiv_pos_iff_of_preconnected (sphereRadialDiffeomorph f)
    (isConnected_compl_singleton_of_one_lt_rank hrank 0).isPreconnected hx hy

end Poincare.Topology.Manifold
