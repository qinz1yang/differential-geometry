import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- The existing fixed-model ellipticity constant transfers to the same actual
presented window and output metric. It is chosen before all finite events. -/
theorem exists_uniform_presented_window_ellipticity (R : ℝ) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
        {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
        (S : E.PresentedStaticCap fixed D m ε b),
        S.hasCanonicalWindow → ε ≤ 1 / 2 → R < D →
        ∀ x : standardCapWindow D, ‖x.val‖ ≤ R → ∀ v : TangentSpace ThreeModel x,
          Λ⁻¹ * ‖v‖ ^ 2 ≤ S.neck.scale * E.outputMetric.inner (S.window x)
            (mfderiv ThreeModel ThreeModel S.window x v)
            (mfderiv ThreeModel ThreeModel S.window x v) ∧
          S.neck.scale * E.outputMetric.inner (S.window x)
            (mfderiv ThreeModel ThreeModel S.window x v)
            (mfderiv ThreeModel ThreeModel S.window x v) ≤ Λ * ‖v‖ ^ 2 := by
  obtain ⟨Λ, hΛ, hbound⟩ := StandardCap.exists_uniform_window_ellipticity R
  refine ⟨Λ, hΛ, ?_⟩
  intro P Q a s E fixed D ε m b S hcanonical hε hRD x hx v
  obtain ⟨x₀, δ, k, d, w, _, hmetric, _⟩ := hcanonical
  have h := hbound w hε hRD x hx v
  rw [← w.window_inner x v v, hmetric x v v] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
