import DifferentialGeometry.Geometry.Comparison.LineSplitting
import DifferentialGeometry.Topology.MetricSpace.GeodesicLine
import DifferentialGeometry.Topology.MetricSpace.LpProductEnds
import Mathlib.Topology.Connected.PathConnected

set_option autoImplicit false

open Set Metric MeasureTheory

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

theorem exists_isometryEquiv_real_prod_compact_of_unbounded_components
    {X : Type u} [MetricSpace X] [ProperSpace X]
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {K : Set X} (hK : IsCompact K) {a b : X}
    (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b))
    (hab : connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) :
    ∃ (Y : Type u) (m : MetricSpace Y), letI := m
      ∃ (p : Y) (e : X ≃ᵢ WithLp 2 (ℝ × Y)),
        CompactSpace Y ∧ fourPointComparison 0 (univ : Set Y) ∧
        e.symm (WithLp.toLp 2 (0, p)) ∈ K ∧
        (∀ x y : Y, ∃ f : Icc (0 : ℝ) 1 → Y,
          Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
        dimH (univ : Set Y) ≤ dimH (univ : Set X) := by
  obtain ⟨γ, hγ, hγK⟩ := exists_isometric_line_of_unbounded_components hsegments hK ha hb hab
  obtain ⟨Y, mY, p, e, he, hproper, _, hYcomp, hYseg, hdim⟩ :=
    exists_isometryEquiv_real_prod hcomp hγ hsegments
  let := mY
  let := hproper
  let : PathConnectedSpace Y := {
    nonempty := ⟨p⟩
    joined := fun x y => by
      obtain ⟨f, hf, hf0, hf1, _⟩ := hYseg x y
      exact ⟨⟨⟨f, hf⟩, hf0, hf1⟩⟩ }
  have hbnd := e.isBounded_factor_of_unbounded_components hK.isBounded ha hb hab
  have hcompact : CompactSpace Y := ⟨isCompact_of_isClosed_isBounded isClosed_univ hbnd⟩
  refine ⟨Y, mY, p, e, hcompact, hYcomp, ?_, hYseg, hdim⟩
  rw [← he 0, e.symm_apply_apply]
  exact hγK

end DifferentialGeometry.Geometry.Comparison.Toponogov
