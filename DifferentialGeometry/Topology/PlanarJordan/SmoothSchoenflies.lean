import DifferentialGeometry.Topology.Planar.PolygonDisk
import DifferentialGeometry.Topology.Planar.CanonicalRounding
import DifferentialGeometry.Topology.PlanarJordan.InnermostDisk

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

theorem smooth_schoenflies
    {f : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ f) :
    ∃ Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane,
      Φ '' sphere (0 : Schoenflies.Plane) 1 = range f ∧
      Φ '' ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (range f) ∧
      Φ '' closedBall (0 : Schoenflies.Plane) 1 = closure (Schoenflies.inside (range f)) := by
  obtain ⟨m, P, e, U, r, d, s, R, ε, φ, _, hnorm, hc, hdisj, hKU, hε, hR,
      _, hφ, _⟩ := Planar.exists_diffeomorph_finite_vertex_rounding hf
  obtain ⟨Ψ, hΨ⟩ := P.exists_diffeomorph_vertex_rounding e U r d s (fun _ => ε) R hnorm
    (fun i => (hc i).1) (fun i => (hc i).2.2.1) (fun i => (hc i).2.2.2.1)
    (fun _ => hε) hR hKU hdisj (fun i => (hc i).2.2.2.2)
  have hboundary : Ψ '' sphere (0 : Schoenflies.Plane) 1 = φ '' range f := by
    rw [← frontier_closedBall (0 : Schoenflies.Plane) (by norm_num : (1 : ℝ) ≠ 0)]
    change Ψ.toHomeomorph '' frontier (closedBall (0 : Schoenflies.Plane) 1) = _
    rw [Ψ.toHomeomorph.image_frontier, Diffeomorph.coe_toHomeomorph, hΨ, hφ]
  let Φ := Ψ.trans φ.symm
  have hΦ : Φ '' sphere (0 : Schoenflies.Plane) 1 = range f := by
    change (fun x => φ.symm (Ψ x)) '' sphere (0 : Schoenflies.Plane) 1 = range f
    rw [← image_image, hboundary]
    exact φ.symm_image_image (range f)
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · have h := image_ball_eq_inside_image_sphere Φ.toHomeomorph 0 zero_lt_one
    simpa only [Diffeomorph.coe_toHomeomorph, hΦ] using h
  · have h := image_closedBall_eq_closure_inside_image_sphere Φ.toHomeomorph 0 zero_lt_one
    simpa only [Diffeomorph.coe_toHomeomorph, hΦ] using h

end DifferentialGeometry.Topology.PlanarJordan
