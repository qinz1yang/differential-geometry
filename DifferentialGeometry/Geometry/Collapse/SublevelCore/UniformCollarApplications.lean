import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformCollar

/-!
# Consumer of LC49

On a complete connected manifold with nonnegative sectional curvature, the PC point-distance
outward field at infinity (`exists_smooth_outward_field_at_infinity`) has, on the compact annulus
`R₁ ≤ d(p, ·) ≤ R₁ + 1`, an LC49 uniform collar: one open neighbourhood with compact closure away
from `p` on which the field is bounded and pairs with every inward unit minimizing direction with a
fixed negative margin.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Consumer of LC49.** The PC outward field at infinity has a uniform LC49 collar around every
compact annulus beyond its threshold. -/
theorem outwardField_uniform_collar_on_annulus
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯, ∃ α B : ℝ, 0 < α ∧ 0 < B ∧
      ∃ U : Set M, IsOpen U ∧ {q | R₁ ≤ dist p q ∧ dist p q ≤ R₁ + 1} ⊆ U ∧
        IsCompact (closure U) ∧ closure U ⊆ ball p (R₁ + 2) \ {p} ∧
        ∀ q ∈ closure U, g.inner q (X q) (X q) ≤ B ^ 2 ∧
          ∀ v ∈ inwardMinimizingDirections (I := I) g hEnorm p q, g.inner q (X q) v ≤ -(2 * α) := by
  obtain ⟨R₀, R₁, hR₀, hR₀₁, X, -, -, hX⟩ :=
    exists_smooth_outward_field_at_infinity (I := I) g hEnorm hsec p
  have hR₁ : 0 < R₁ := hR₀.trans hR₀₁
  set C₀ : Set M := {q | R₁ ≤ dist p q ∧ dist p q ≤ R₁ + 1} with hC₀def
  have hC₀closed : IsClosed C₀ :=
    (isClosed_le continuous_const (continuous_const.dist continuous_id)).inter
      (isClosed_le (continuous_const.dist continuous_id) continuous_const)
  have hC₀ : IsCompact C₀ :=
    (soul_isCompact_closedBall (I := I) g hEnorm p (R₁ + 1)).of_isClosed_subset hC₀closed
      (fun q hq => by rw [mem_closedBall, dist_comm]; exact hq.2)
  have hC₀n : C₀ ⊆ ball p (R₁ + 2) \ {p} := by
    intro q hq
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_comm]; linarith [hq.2]
    · intro hqp
      rw [mem_singleton_iff] at hqp
      subst hqp
      have := hq.1
      rw [dist_self] at this
      linarith
  obtain ⟨α, B, hα, hB, U, hU, hC₀U, hUc, hUsub, hbounds⟩ :=
    exists_uniform_collar_of_strict_point_directions_of_radius (I := I) g hEnorm p hC₀ hC₀n
      isOpen_univ (subset_univ _) (fun y => X y) X.contMDiff.continuous.continuousOn
      (fun q hq v hv => (hX q hq.1 v hv.1 hv.2).trans_lt (by norm_num))
  exact ⟨R₁, hR₁, X, α, B, hα, hB, U, hU, hC₀U, hUc, fun q hq => (hUsub hq).1, hbounds⟩

end DifferentialGeometry.Geometry.Collapse
