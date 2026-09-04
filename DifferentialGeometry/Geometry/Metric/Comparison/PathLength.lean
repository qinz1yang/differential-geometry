import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Bundle Manifold
open scoped Manifold ContDiff ENNReal

theorem edist_comp_le_of_path_length_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoEMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M → N) {K : ENNReal} (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hpath :
      ∀ {x y : M}, ∀ γ : Path x y, CMDiff 1 γ →
        ∃ η : Path (F x) (F y), CMDiff 1 η ∧
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) ≤
            K * (∫⁻ t, ‖mfderiv% γ t 1‖ₑ))
    (x y : M) :
    edist (F x) (F y) ≤ K * edist x y := by
  rw [IsRiemannianManifold.out (I := I) (F x) (F y)]
  rw [IsRiemannianManifold.out (I := I) x y]
  conv_rhs => rw [riemannianEDist]
  rw [ENNReal.mul_iInf_of_ne hK0 hKtop]
  refine le_iInf ?_
  intro γ
  rw [ENNReal.mul_iInf_of_ne hK0 hKtop]
  refine le_iInf ?_
  intro hγ
  rcases hpath γ hγ with ⟨η, hη, hlen⟩
  have htarget :
      riemannianEDist I (F x) (F y) ≤
        ∫⁻ t, ‖mfderiv% η t 1‖ₑ := by
    rw [riemannianEDist]
    exact (iInf_le _ η).trans (iInf_le _ hη)
  exact htarget.trans hlen

theorem path_length_le_of_speed_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [TopologicalSpace N] [ChartedSpace H N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    (F : M → N) {K : ENNReal} (hKtop : K ≠ ⊤)
    (hspeed :
      ∀ {x y : M}, ∀ γ : Path x y, CMDiff 1 γ →
        ∃ η : Path (F x) (F y), CMDiff 1 η ∧
          ∀ t : Set.Icc (0 : Real) 1,
            ‖mfderiv% η t 1‖ₑ ≤ K * ‖mfderiv% γ t 1‖ₑ) :
    ∀ {x y : M}, ∀ γ : Path x y, CMDiff 1 γ →
      ∃ η : Path (F x) (F y), CMDiff 1 η ∧
        (∫⁻ t, ‖mfderiv% η t 1‖ₑ) ≤
          K * (∫⁻ t, ‖mfderiv% γ t 1‖ₑ) := by
  intro x y γ hγ
  rcases hspeed γ hγ with ⟨η, hη, hη_speed⟩
  refine ⟨η, hη, ?_⟩
  calc
    (∫⁻ t, ‖mfderiv% η t 1‖ₑ)
        ≤ ∫⁻ t, K * ‖mfderiv% γ t 1‖ₑ :=
      MeasureTheory.lintegral_mono hη_speed
    _ = K * (∫⁻ t, ‖mfderiv% γ t 1‖ₑ) := by
      rw [MeasureTheory.lintegral_const_mul' K _ hKtop]

theorem dist_comp_le_of_path_length_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M → N) {K : NNReal} (hK : 0 < K)
    (hpath :
      ∀ {x y : M}, ∀ γ : Path x y, CMDiff 1 γ →
        ∃ η : Path (F x) (F y), CMDiff 1 η ∧
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) ≤
            (K : ENNReal) * (∫⁻ t, ‖mfderiv% γ t 1‖ₑ))
    (x y : M) :
    dist (F x) (F y) ≤ (K : Real) * dist x y := by
  have hF : LipschitzWith K F := fun x y =>
    edist_comp_le_of_path_length_le (I := I) F
      (by exact_mod_cast hK.ne') ENNReal.coe_ne_top hpath x y
  exact hF.dist_le_mul x y

theorem dist_comp_le_of_speed_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M → N) {K : NNReal} (hK : 0 < K)
    (hspeed :
      ∀ {x y : M}, ∀ γ : Path x y, CMDiff 1 γ →
        ∃ η : Path (F x) (F y), CMDiff 1 η ∧
          ∀ t : Set.Icc (0 : Real) 1,
            ‖mfderiv% η t 1‖ₑ ≤
              (K : ENNReal) * ‖mfderiv% γ t 1‖ₑ)
    (x y : M) :
    dist (F x) (F y) ≤ (K : Real) * dist x y := by
  exact dist_comp_le_of_path_length_le (I := I) F hK
    (path_length_le_of_speed_le (I := I) F ENNReal.coe_ne_top hspeed) x y

theorem image_ball_subset_ball_of_path_length_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M → N) {K : NNReal} (hK : 0 < K)
    (hpath :
      ∀ {x y : M}, ∀ γ : Path x y, CMDiff 1 γ →
        ∃ η : Path (F x) (F y), CMDiff 1 η ∧
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) ≤
            (K : ENNReal) * (∫⁻ t, ‖mfderiv% γ t 1‖ₑ))
    (x₀ : M) (r : Real) :
    F '' Metric.ball x₀ r ⊆ Metric.ball (F x₀) ((K : Real) * r) := by
  have hF : LipschitzWith K F :=
    LipschitzWith.of_dist_le_mul
      (dist_comp_le_of_path_length_le (I := I) F hK hpath)
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact hF.mapsTo_ball hK.ne' x₀ r hx

theorem image_ball_subset_ball_of_speed_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M → N) {K : NNReal} (hK : 0 < K)
    (hspeed :
      ∀ {x y : M}, ∀ γ : Path x y, CMDiff 1 γ →
        ∃ η : Path (F x) (F y), CMDiff 1 η ∧
          ∀ t : Set.Icc (0 : Real) 1,
            ‖mfderiv% η t 1‖ₑ ≤
              (K : ENNReal) * ‖mfderiv% γ t 1‖ₑ)
    (x₀ : M) (r : Real) :
    F '' Metric.ball x₀ r ⊆ Metric.ball (F x₀) ((K : Real) * r) := by
  exact image_ball_subset_ball_of_path_length_le (I := I) F hK
    (path_length_le_of_speed_le (I := I) F ENNReal.coe_ne_top hspeed) x₀ r

theorem image_eball_subset_closedEBall_of_path_length_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoEMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M → N) {K : ENNReal} {r : Real} (x₀ : M)
    (hpath : ∀ {y : M} (γ : ℝ → M), (CMDiff[Set.Icc (0 : ℝ) 1] 1 γ) →
      γ 0 = x₀ → γ 1 = y →
      Manifold.pathELength (I := I) γ 0 1 < ENNReal.ofReal r →
      ∃ η : ℝ → N, (CMDiff[Set.Icc (0 : ℝ) 1] 1 η) ∧ η 0 = F x₀ ∧ η 1 = F y ∧
        Manifold.pathELength (I := I) η 0 1 ≤
          K * Manifold.pathELength (I := I) γ 0 1) :
    F '' Metric.eball x₀ (ENNReal.ofReal r) ⊆
      Metric.closedEBall (F x₀) (K * ENNReal.ofReal r) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_eball, edist_comm, IsRiemannianManifold.out (I := I) x₀ x] at hx
  obtain ⟨γ, hγ0, hγ1, hγC, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := I) hx
  obtain ⟨η, hηC, hη0, hη1, hηlen⟩ := hpath γ hγC hγ0 hγ1 hγlen
  rw [Metric.mem_closedEBall, edist_comm, IsRiemannianManifold.out (I := I) (F x₀) (F x)]
  calc
    Manifold.riemannianEDist I (F x₀) (F x)
        ≤ Manifold.pathELength (I := I) η 0 1 := by
      refine Manifold.riemannianEDist_le_pathELength hηC ?_ ?_ zero_le_one
      · exact hη0
      · exact hη1
    _ ≤ K * Manifold.pathELength (I := I) γ 0 1 := hηlen
    _ ≤ K * ENNReal.ofReal r := by
      gcongr

end Riemannian
end Geometry
end DifferentialGeometry
