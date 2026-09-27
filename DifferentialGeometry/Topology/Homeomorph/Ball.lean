import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

open Set Metric

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mapsTo_ball_of_image_sphere_eq {F : Type*} [PseudoMetricSpace F]
    (D : E ≃ₜ F) {c : E} {d : F} {r s : ℝ}
    (hr : 0 < r) (hsphere : D '' sphere c r = sphere d s)
    (hc : D c ∈ ball d s) : MapsTo D (ball c r) (ball d s) := by
  intro x hx
  by_contra hn
  have hnx : s ≤ dist (D x) d := le_of_not_gt hn
  obtain ⟨y, hy, hyD⟩ := (convex_ball c r).isPreconnected.intermediate_value
    (mem_ball_self hr) hx (D.continuous.dist continuous_const).continuousOn
    (show s ∈ Icc (dist (D c) d) (dist (D x) d) from ⟨hc.le, hnx⟩)
  have hyS : D y ∈ sphere d s := hyD
  obtain ⟨z, hz, hzy⟩ := hsphere.symm.subset hyS
  have hzy' := D.injective hzy
  subst z
  exact (mem_ball.mp hy).ne (mem_sphere.mp hz)

theorem image_closedBall_of_image_sphere_eq_of_map_center
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (D : E ≃ₜ F)
    {c : E} {d : F} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hsphere : D '' sphere c r = sphere d s) (hc : D c = d) :
    D '' closedBall c r = closedBall d s := by
  have hball : D '' ball c r = ball d s := by
    apply Subset.antisymm
    · exact (D.mapsTo_ball_of_image_sphere_eq hr hsphere
        (by rw [hc]; exact mem_ball_self hs)).image_subset
    · intro y hy
      have hiS : D.symm '' sphere d s = sphere c r := by
        rw [← hsphere, image_image]
        simp only [D.symm_apply_apply, image_id']
      have hc' : D.symm d = c := by rw [← hc, D.symm_apply_apply]
      exact ⟨D.symm y,
        D.symm.mapsTo_ball_of_image_sphere_eq hs hiS (by rw [hc']; exact mem_ball_self hr) hy,
        D.apply_symm_apply y⟩
  rw [← closure_ball c hr.ne', D.image_closure, hball, closure_ball d hs.ne']

end Homeomorph
