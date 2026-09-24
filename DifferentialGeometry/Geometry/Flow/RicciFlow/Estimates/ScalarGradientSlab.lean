import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.Local

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator (gradientFun)
open Perelman (FlowMetricBall)
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_uniform_scalar_gradient_bound_on_Icc
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) {a b c K : ℝ} (hac : a < c)
    (hreg : Icc a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc a b,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hRm : ∀ t ∈ Icc a b, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4
        (S.base.rm04 t x) ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc c b, ∀ x (v : TangentSpace I x),
      |(S.base.metric t).inner x
        (gradientFun (S.base.metric t) (S.scalar t) x) v| ≤
          C * Real.sqrt ((S.base.metric t).inner x v v) := by
  obtain ⟨theta, A, htheta, hthetaOne, hA, hgrad⟩ :=
    Perelman.FlowMetricBall.scalar_gradient_estimate (E := E) (I := I) (M := M)
  have h₂ : ContinuousAt (fun rho : ℝ => rho ^ 2) 0 :=
    continuousAt_id.pow 2
  have h₄ : ContinuousAt (fun rho : ℝ => rho ^ 4 * K) 0 :=
    (continuousAt_id.pow 4).mul continuousAt_const
  have hsmall : ∀ᶠ rho in 𝓝 (0 : ℝ), rho ^ 2 < c - a ∧ rho ^ 4 * K < 1 :=
    (h₂.eventually_lt continuousAt_const (by simpa using sub_pos.mpr hac)).and
      (h₄.eventually_lt continuousAt_const (by norm_num))
  have hpos : ∀ᶠ rho in 𝓝[>] (0 : ℝ), 0 < rho := self_mem_nhdsWithin
  obtain ⟨rho, hrho, hrhoTime, hrhoRm⟩ :=
    (hpos.and (hsmall.filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨A / rho ^ 3, div_nonneg hA.le (pow_nonneg hrho.le 3), ?_⟩
  intro t ht x v
  let time : D.FlowTime :=
    ⟨t, D.regular_subset (hreg ⟨hac.le.trans ht.1, ht.2⟩)⟩
  let B : FlowMetricBall S time :=
    { center := x
      radius := rho
      radius_pos := hrho }
  have hballSlab : Icc (t - rho ^ 2) t ⊆ Icc a b := by
    intro q hq
    exact ⟨by linarith [hq.1, ht.1, hrhoTime], hq.2.trans ht.2⟩
  have hB : B.IsRmControlled := by
    constructor
    · intro q hq
      exact D.regular_subset (hreg (hballSlab hq))
    · intro q hq y _
      change rho ^ 4 *
        Tensor0SBundle.normSq0S (I := I) (S.base.metric q) y 4
          (S.base.rm04 q y) ≤ 1
      exact (mul_le_mul_of_nonneg_left (hRm q (hballSlab hq) y)
        (pow_nonneg hrho.le 4)).trans hrhoRm.le
  have hregB : Ioc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.regular := by
    intro q hq
    exact hreg (hballSlab ⟨hq.1.le, hq.2⟩)
  have hcompleteB : ∀ q ∈ Icc
      ((time : ℝ) - theta * B.radius ^ 2) (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric q) := by
    intro q hq
    apply hcomplete q
    apply hballSlab
    change t - theta * rho ^ 2 ≤ q ∧ q ≤ t at hq
    have hscale := mul_le_mul_of_nonneg_right hthetaOne.le (sq_nonneg rho)
    exact ⟨by linarith [hq.1], hq.2⟩
  have htB : t ∈ Icc
      ((time : ℝ) - theta * B.radius ^ 2 / 2) (time : ℝ) := by
    change t - theta * rho ^ 2 / 2 ≤ t ∧ t ≤ t
    exact ⟨sub_le_self _ (div_nonneg (mul_nonneg htheta.le (sq_nonneg rho))
      (by norm_num)), le_rfl⟩
  have hx : riemannianEDistOf (I := I) (S.base.metric t) B.center x <
      ENNReal.ofReal (B.radius / 8) := by
    change riemannianEDistOf (I := I) (S.base.metric t) x x <
      ENNReal.ofReal (rho / 8)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hrho (by norm_num))
  simpa only [B] using hgrad hS B hB hregB hcompleteB t htB x v hx

end DifferentialGeometry.PDE.RicciFlow
