import DifferentialGeometry.Geometry.Metric.DirectLimit.Distance

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace SmoothSeqSystem

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem isCompact_limit_closedBall (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal),
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      ∃ k, ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ Set.range (S.toSeqSystem.incl k))
    (hcpt : ∀ (k : ℕ) (a : A k) (r : ENNReal),
      letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
        ⟨(g k).toRiemannianMetric⟩
      IsCompact {b : A k | Manifold.riemannianEDist I a b ≤ r})
    (z : S.toSeqSystem.Lim) (r : ENNReal) (hr : r ≠ ⊤) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    IsCompact {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r} := by
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  obtain ⟨k, hk⟩ := hexh z (r + 1)
  let : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  have hz : z ∈ Set.range (S.toSeqSystem.incl k) :=
    hk z (by rw [Manifold.riemannianEDist_self]; exact zero_le)
  have himg : IsCompact (S.toSeqSystem.incl k ''
      {b : A k | Manifold.riemannianEDist I (Function.invFun (S.toSeqSystem.incl k) z) b
        ≤ r + 1}) :=
    (hcpt k _ (r + 1)).image (S.toSeqSystem.continuous_incl k)
  refine IsCompact.of_isClosed_subset himg ?_ ?_
  · let : IsManifold I 1 S.toSeqSystem.Lim :=
      IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    let : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
      Manifold.metrizableSpace I S.toSeqSystem.Lim
    let : T3Space S.toSeqSystem.Lim := inferInstance
    let : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
        by intro x v w; rfl⟩⟩
    let : EMetricSpace S.toSeqSystem.Lim :=
      EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
    have hcont : Continuous fun w : S.toSeqSystem.Lim => edist z w :=
      continuous_const.edist continuous_id
    have hset : {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r}
        = (fun w : S.toSeqSystem.Lim => edist z w) ⁻¹' (Set.Iic r) := rfl
    rw [hset]
    exact IsClosed.preimage hcont isClosed_Iic
  · intro w hw
    have hw' : Manifold.riemannianEDist I z w ≤ r := hw
    have hwr : w ∈ Set.range (S.toSeqSystem.incl k) :=
      hk w (hw'.trans le_self_add)
    have hlt : Manifold.riemannianEDist I z w < r + 1 :=
      hw'.trans_lt (ENNReal.lt_add_right hr one_ne_zero)
    have hstage := S.riemannianEDist_invIncl_le g hg k hlt hk
    refine ⟨Function.invFun (S.toSeqSystem.incl k) w, hstage, Function.invFun_eq hwr⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def hasCompactBallCover (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) : Prop :=
  ∀ (z : S.toSeqSystem.Lim) (r : ENNReal), r ≠ ⊤ →
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    ∃ k, ∃ K : Set (A k), IsCompact K ∧
      ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ S.toSeqSystem.incl k '' K

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [∀ k, SigmaCompactSpace (A k)] in
theorem hasCompactBallCover_of_step (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal),
      r ≠ ⊤ →
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      ∃ k, ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ Set.range (S.toSeqSystem.incl k))
    (hstep : ∀ k, ∃ K : Set (A (k + 1)), IsCompact K ∧
      Set.range (S.toSeqSystem.F (Nat.le_succ k)) ⊆ K) :
    S.hasCompactBallCover g hg := by
  intro z r hr
  obtain ⟨k, hk⟩ := hexh z r hr
  obtain ⟨K, hK, hFK⟩ := hstep k
  refine ⟨k + 1, K, hK, fun w hw => ?_⟩
  obtain ⟨a, rfl⟩ := hk w hw
  refine ⟨S.toSeqSystem.F (Nat.le_succ k) a, hFK ⟨a, rfl⟩, ?_⟩
  exact S.toSeqSystem.incl_comp (Nat.le_succ k) a

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem isCompact_limit_closedBall_of_cover (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (hcover : S.hasCompactBallCover g hg)
    (z : S.toSeqSystem.Lim) (r : ENNReal) (hr : r ≠ ⊤) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    IsCompact {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r} := by
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  obtain ⟨k, K, hK, hsub⟩ := hcover z r hr
  have himg : IsCompact (S.toSeqSystem.incl k '' K) :=
    hK.image (S.toSeqSystem.continuous_incl k)
  refine IsCompact.of_isClosed_subset himg ?_ ?_
  · let : IsManifold I 1 S.toSeqSystem.Lim :=
      IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    let : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
      Manifold.metrizableSpace I S.toSeqSystem.Lim
    let : T3Space S.toSeqSystem.Lim := inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
        by intro x v w; rfl⟩⟩
    let : EMetricSpace S.toSeqSystem.Lim :=
      EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
    have hcont : Continuous fun w : S.toSeqSystem.Lim => edist z w :=
      continuous_const.edist continuous_id
    have hset : {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r} =
        (fun w : S.toSeqSystem.Lim => edist z w) ⁻¹' Set.Iic r := rfl
    rw [hset]
    exact IsClosed.preimage hcont isClosed_Iic
  · intro w hw
    change Manifold.riemannianEDist I z w ≤ r at hw
    exact hsub w hw


end SmoothSeqSystem
end DifferentialGeometry
