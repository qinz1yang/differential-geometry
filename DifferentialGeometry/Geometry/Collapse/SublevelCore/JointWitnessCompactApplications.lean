import DifferentialGeometry.Geometry.Collapse.SublevelCore.JointWitnessCompact
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity

/-!
# Consumer of the compact branch of LC57/LC61

For a compact connected Riemannian manifold `(N, g, n)` and the constant sequence `M i = N` with the
identity maps, the compact branch gives one scale `R > T` at which the exact normalized distance
`d(n, ·)/R` has all its sublevels `{· ≤ ρ}`, `ρ ≥ 1/5`, and all open balls `B(n, ρ R)` equal to `N`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]

/-- **Consumer of `exists_scale_eventually_compact_joint_type`.** On a compact connected model with
the identity maps, one scale `R > T` makes every open ball `B(n, ρ R)`, `ρ ≥ 1/5`, all of `N`, and
every sublevel of `d(n, ·)/R` at level `ρ ≥ 1/5` all of `N`. -/
theorem compact_model_identity_joint_type [CompactSpace N] [Nonempty N] [ConnectedSpace N]
    (g : SmoothRiemannianMetric I N) (hNorm : IsMetricNorm g) (n : N) (T : ℝ) :
    ∃ R : ℝ, T < R ∧ 0 < R ∧ (∀ ρ : ℝ, 1 / 5 ≤ ρ → {y | dist n y / R ≤ ρ} = univ) ∧
      ∀ ρ : ℝ, 1 / 5 ≤ ρ → Metric.ball n (ρ * R) = univ := by
  let j := (Diffeomorph.refl I N ∞).toPartialDiffeomorph
  have hj : j.source = univ := rfl
  have hjn : ∀ x, j x = x := fun _ => rfl
  obtain ⟨R, hTR, hR0, hall⟩ := exists_scale_eventually_compact_joint_type (M := fun _i : ℕ => N)
    (e := 1 / 10) (T := T) g hNorm n (fun _i => g) (fun _i => g) (fun _i => hNorm)
    (fun _i => j) (fun _i => hj)
    (fun _i x v w => by
      change g.inner x v w = g.inner x (mfderiv I I (id : N → N) x v)
        (mfderiv I I (id : N → N) x w)
      rw [mfderiv_id]
      rfl)
    (fun epsilon hepsilon => ⟨0, fun _i _hi => by
      rw [metricDerivNormSupOn_self]; exact hepsilon⟩) (by norm_num)
  have h := (hall (fun _i y => dist n y / R) (Eventually.of_forall fun _i y => by
    rw [hjn, sub_self, abs_zero]; norm_num)).exists
  obtain ⟨_i, hsub, hball, -⟩ := h
  exact ⟨R, hTR, hR0, hsub, fun ρ hρ => by simpa only [hjn] using hball ρ hρ⟩

end DifferentialGeometry.Geometry.Collapse
