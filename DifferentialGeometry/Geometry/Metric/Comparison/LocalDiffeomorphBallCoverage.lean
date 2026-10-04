import DifferentialGeometry.Geometry.Metric.Comparison.BallImageLower
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

set_option autoImplicit false

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry

theorem IsLocalDiffeomorphOn.exists_partialDiffeomorph_ball_coverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun y : M => TangentSpace I y)] [IsRiemannianManifold I M]
    {N : Type*} [PseudoMetricSpace N] [ChartedSpace G N] [T2Space N]
    [RiemannianBundle (fun y : N => TangentSpace J y)] [IsRiemannianManifold J N]
    {k : ℕ} (hk : 1 ≤ k) {f : M → N} {U : Set M}
    {O x : M} {r R A : ℝ} {C : NNReal}
    (hU : IsOpen U) (hR : 0 ≤ R)
    (hcompact : IsCompact (Metric.closedBall O R))
    (hsub : Metric.closedBall O R ⊆ U)
    (hf : IsLocalDiffeomorphOn I J (k : WithTop ℕ∞) f U)
    (hinj : Set.InjOn f U)
    (hlower : ∀ y ∈ Metric.closedBall O R, ∀ v : TangentSpace I y,
      ‖v‖ₑ ≤ ENNReal.ofReal (C : ℝ) * ‖mfderiv I J f y v‖ₑ)
    (hx : x ∈ Metric.ball O r) (hmargin : (C : ℝ) * A + r < R) :
    ∃ Φ : PartialDiffeomorph I J M N (k : WithTop ℕ∞),
      Φ.source = U ∧ Φ.target = f '' U ∧ (Φ : M → N) = f ∧
        Metric.ball (f x) A ⊆ f '' Metric.closedBall O R := by
  have hUne : U.Nonempty := ⟨O, hsub (Metric.mem_closedBall_self hR)⟩
  obtain ⟨Φ, hsrc, htgt, hfun⟩ :=
    IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hf hU hUne hinj
  have hΦ : (Φ : M → N) = f := hfun
  refine ⟨Φ, hsrc, htgt, hΦ, ?_⟩
  have hk1 : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by
    exact_mod_cast hk
  let Ψ : PartialDiffeomorph I J M N 1 := PartialDiffeomorph.ofLE Φ hk1
  have hΨ : (Ψ : M → N) = f := hΦ
  have hΨsub : Metric.closedBall O R ⊆ Ψ.source := by
    change Metric.closedBall O R ⊆ Φ.toPartialEquiv.source
    rw [hsrc]
    exact hsub
  have hΨlower : ∀ y ∈ Metric.closedBall O R, ∀ v : TangentSpace I y,
      ‖v‖ₑ ≤ ENNReal.ofReal (C : ℝ) * ‖mfderiv I J (Ψ : M → N) y v‖ₑ := by
    exact Eq.mpr (congrArg
      (fun g : M → N => ∀ y ∈ Metric.closedBall O R, ∀ v : TangentSpace I y,
        ‖v‖ₑ ≤ ENNReal.ofReal (C : ℝ) * ‖mfderiv I J g y v‖ₑ)
      hΨ) hlower
  simpa only [hΨ] using
    (PartialDiffeomorph.ball_subset_image_closedBall_of_enorm_mfderiv_lower
      Ψ hcompact hΨsub hΨlower hx hmargin)

end DifferentialGeometry
