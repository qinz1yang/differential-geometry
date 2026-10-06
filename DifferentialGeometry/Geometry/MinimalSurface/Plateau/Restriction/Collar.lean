import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.BoundaryCollar
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundaryTraceInjectivity

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace IMS03Embeddedness

/-- Boundary rank and the original boundary-avoidance statement give arbitrarily
large proper round restrictions of the very same Morrey disk. All original
collisions lie strictly inside each selected circle; the literal restricted
boundary is smoothly embedded and the original metric is retained. -/
theorem morrey_exists_concentric_restrictions_surrounding_collisions
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hrank : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ∀ θ : loopCircle, q z ≠ γ θ) :
    ∃ r₀ : ℝ, 0 ≤ r₀ ∧ r₀ < 1 ∧
      (∀ z : closedDisk, r₀ < ‖(z : ℂ)‖ →
        (∀ w, q w = q z → w = z) ∧
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) ∧
      (∀ x y : closedDisk, q x = q y → x ≠ y →
        ‖(x : ℂ)‖ ≤ r₀ ∧ ‖(y : ℂ)‖ ≤ r₀) ∧
      ∀ r : ℝ, r₀ < r → r < 1 →
        IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r)) ∧
        IsMorreyDisk g (diskTrace (affineSubdisk q 0 r)) (affineSubdisk q 0 r) ∧
        (∀ (θ : loopCircle) (w : closedDisk),
          q w = diskTrace (affineSubdisk q 0 r) θ →
            (w : ℂ) = r • (diskBoundary θ : ℂ)) ∧
        (∀ w : closedDisk, ‖(w : ℂ)‖ < r → ∀ θ : loopCircle,
          q w ≠ diskTrace (affineSubdisk q 0 r) θ) := by
  obtain ⟨σ, hσ, htrace⟩ := hq.trace
  have hboundary := hQ.boundary_fiber_eq hγ hσ htrace hrank hseparate
  have hsingle (z : closedDisk) (hz : ‖(z : ℂ)‖ = 1)
      (w : closedDisk) (hw : q w = q z) : w = z := by
    let c : Circle := ⟨(z : ℂ), mem_sphere_zero_iff_norm.mpr hz⟩
    obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
    have hb : diskBoundary θ = z := by
      apply Subtype.ext
      have hc := congrArg (fun v : Circle => (v : ℂ)) hθ
      simpa only [AddCircle.homeomorphCircle_apply] using! hc
    exact (hboundary θ w (hw.trans (congrArg q hb).symm)).trans hb
  obtain ⟨r₀, hr₀, hr₀1, hcollar, hrestr⟩ :=
    hq.exists_regular_concentric_restrictions hQ hsingle hrank
  refine ⟨r₀, hr₀, hr₀1, hcollar, ?_, ?_⟩
  · intro x y hxy hne
    constructor
    · apply le_of_not_gt
      intro hx
      exact hne ((hcollar x hx).1 y hxy.symm).symm
    · apply le_of_not_gt
      intro hy
      exact hne ((hcollar y hy).1 x hxy)
  · intro r hr hr1
    obtain ⟨hloop, hmorrey, hfiber⟩ := hrestr r hr hr1
    refine ⟨hloop, hmorrey, hfiber, ?_⟩
    intro w hw θ heq
    have hcoord := hfiber θ w heq
    have hnorm : ‖(w : ℂ)‖ = r := by
      rw [hcoord, norm_smul, Real.norm_eq_abs, abs_of_pos (hr₀.trans_lt hr),
        (show ‖(diskBoundary θ : ℂ)‖ = 1 from Circle.norm_coe _), mul_one]
    exact (ne_of_lt hw) hnorm

end IMS03Embeddedness
