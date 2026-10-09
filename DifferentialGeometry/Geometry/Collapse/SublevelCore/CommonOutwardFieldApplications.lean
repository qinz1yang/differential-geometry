import DifferentialGeometry.Geometry.Collapse.SublevelCore.CommonOutwardField

/-!
# Consumer of LC52–LC53 (with LC49)

On a complete connected manifold with `sec ≥ 0`, take the compact target `S = B̄(p, 1)`. The LC53
field `X` vanishes on `S`, is outward for both distances beyond `A₁`, and on the compact annulus
`A₁ ≤ d(p, ·) ≤ A₁ + 1` it has an LC49 uniform collar for the point directions.
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

/-- **Consumer of LC52–LC53 and LC49.** The two-target field for `S = B̄(p, 1)` vanishes on `S`,
pairs at most `-1/4` with every direction realizing the distance to `S` beyond `A₁`, and has a
uniform LC49 collar for the point directions around the far annulus. -/
theorem twoTarget_field_ball_collar
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) :
    ∃ A₁ : ℝ, 0 < A₁ ∧ ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ q ∈ closedBall p 1, X q = 0) ∧
      (∀ q, A₁ ≤ dist p q → ∀ v ∈ minimizingDirectionsTo (I := I) g hEnorm (closedBall p 1) q,
        g.inner q (X q) v ≤ -(1 / 4)) ∧
      ∃ α B : ℝ, 0 < α ∧ 0 < B ∧ ∃ U : Set M, IsOpen U ∧
        {q | A₁ ≤ dist p q ∧ dist p q ≤ A₁ + 1} ⊆ U ∧ IsCompact (closure U) ∧
        ∀ q ∈ closure U, g.inner q (X q) (X q) ≤ B ^ 2 ∧
          ∀ v ∈ inwardMinimizingDirections (I := I) g hEnorm p q, g.inner q (X q) v ≤ -(2 * α) := by
  obtain ⟨A₀, A₁, hA₀, hA₀₁, hSball, X, -, hX0, hX⟩ :=
    exists_smooth_outward_field_two_targets (I := I) g hEnorm hsec p
      (soul_isCompact_closedBall (I := I) g hEnorm p 1)
  have hA₁ : 0 < A₁ := hA₀.trans hA₀₁
  set C₀ : Set M := {q | A₁ ≤ dist p q ∧ dist p q ≤ A₁ + 1} with hC₀def
  have hC₀closed : IsClosed C₀ :=
    (isClosed_le continuous_const (continuous_const.dist continuous_id)).inter
      (isClosed_le (continuous_const.dist continuous_id) continuous_const)
  have hC₀ : IsCompact C₀ :=
    (soul_isCompact_closedBall (I := I) g hEnorm p (A₁ + 1)).of_isClosed_subset hC₀closed
      (fun q hq => by rw [mem_closedBall, dist_comm]; exact hq.2)
  have hC₀n : C₀ ⊆ ball p (A₁ + 2) \ {p} := by
    intro q hq
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_comm]; linarith [hq.2]
    · intro hqp
      rw [mem_singleton_iff] at hqp
      subst hqp
      have := hq.1
      rw [dist_self] at this
      linarith
  obtain ⟨α, B, hα, hB, U, hU, hC₀U, hUc, -, hbounds⟩ :=
    exists_uniform_collar_of_strict_point_directions_of_radius (I := I) g hEnorm p hC₀ hC₀n
      isOpen_univ (subset_univ _) (fun y => X y) X.contMDiff.continuous.continuousOn
      (fun q hq v hv => (hX q hq.1 v (Or.inl hv)).trans_lt (by norm_num))
  refine ⟨A₁, hA₁, X, fun q hq => hX0 q ?_, fun q hq v hv => hX q hq v (Or.inr hv),
    α, B, hα, hB, U, hU, hC₀U, hUc, hbounds⟩
  have := hSball hq
  rw [mem_ball] at this
  rw [dist_comm]
  exact this.le

end DifferentialGeometry.Geometry.Collapse
