import DifferentialGeometry.Topology.Manifold.BoundaryIntegralCurve
import DifferentialGeometry.Topology.Manifold.IntegralCurveHeight

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

theorem injOn_integralCurveFamily_of_height
    {u : M → ℝ} {v : (x : M) → TangentSpace I x} {Φ : M × ℝ → M}
    {S : Set M} {ε a κ : ℝ} (hε : 0 < ε) (hκ : κ ≠ 0)
    (hu : MDifferentiable I 𝓘(ℝ) u)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hunit : ∀ x, mfderiv I 𝓘(ℝ) u x (v x) = κ)
    (hlevel : ∀ x ∈ S, u x = a)
    (hzero : ∀ x ∈ S, Φ (x, 0) = x)
    (hcurve : ∀ x ∈ S, IsMIntegralCurveOn (fun t ↦ Φ (x, t)) v (Ico 0 ε)) :
    InjOn Φ (S ×ˢ Ico 0 ε) := by
  have hheight : ∀ x ∈ S, ∀ t ∈ Ico 0 ε, u (Φ (x, t)) = a + κ * t := by
    intro x hx t ht
    simpa only [hzero x hx, hlevel x hx] using
      height_eq_add_mul_time hε hu hunit (hcurve x hx) t ht
  rintro ⟨x, t⟩ hx ⟨y, s⟩ hy heq
  have ht : t = s := by
    have hh := congrArg u heq
    rw [hheight x hx.1 t hx.2, hheight y hy.1 s hy.2] at hh
    exact mul_left_cancel₀ hκ (add_left_cancel hh)
  subst s
  have hcurves := isMIntegralCurveOn_Ico_eqOn hx.2 hv (hcurve x hx.1) (hcurve y hy.1) heq
  have hxy := hcurves (show (0 : ℝ) ∈ Ico 0 ε from ⟨le_rfl, hε⟩)
  dsimp only at hxy
  rw [hzero x hx.1, hzero y hy.1] at hxy
  exact Prod.ext hxy rfl

end Poincare.Topology.Manifold
