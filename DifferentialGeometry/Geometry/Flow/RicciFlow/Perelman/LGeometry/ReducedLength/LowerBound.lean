import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.ScalarLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ActionIntegrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Injectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Curvature.ScalarBound

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold Topology

universe u uE uH

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redLength_lExp_ge_of_scalar_lower_bound
    [I.Boundaryless] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) {tau : ℝ}
    (hmin : (Z, tau) ∈ lMinDomain (I := I) S T x) (K : ℝ)
    (hR : ∀ s ∈ Icc (0 : ℝ) (Real.sqrt tau),
      -K ≤ S.scalar (T - s ^ 2) (lRegularizedCurve S T x Z s)) :
    -(K * tau / 3) ≤ redLength S T x (lExp S T x Z tau) tau := by
  have hm : IsLMinimizingVector (I := I) S T x Z tau := hmin
  have hd := (mem_lExpPosDom S T x Z tau).mp hm.1
  have htau : 0 < tau := hd.1
  have hsqrt : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  let alpha := lRegularizedCurve S T x Z
  have hlag := intervalIntegrable_lRegularizedLagrangian_lRegularizedCurve S hS T x Z
    hsqrt hd.2.2
  have hden : IntervalIntegrable (lDensity S T (squareRootReparametrization alpha))
      volume 0 tau := by
    simpa only [zero_pow two_ne_zero, Real.sq_sqrt htau.le] using
      (intervalIntegrable_lDensity_squareRootReparametrization_sq_iff S T alpha
        0 (Real.sqrt tau) le_rfl hsqrt.le).mpr hlag
  have hbound := lLength_ge_of_scalar_lower_bound S T 0 tau K le_rfl htau.le
    (squareRootReparametrization alpha) (fun s hs => by
      have h := hR (Real.sqrt s)
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hs.2⟩
      simpa only [Real.sq_sqrt hs.1, squareRootReparametrization, alpha] using h) hden
  have hcost : lLength S T (squareRootReparametrization alpha) 0 tau =
      lCost S T x (lExp S T x Z tau) tau := hm.2
  rw [hcost] at hbound
  simp only [zero_mul, sub_zero] at hbound
  change -(K * tau / 3) ≤ lCost S T x (lExp S T x Z tau) tau / (2 * Real.sqrt tau)
  apply (le_div_iff₀ (mul_pos (by norm_num) hsqrt)).mpr
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redLength_lExp_ge_of_range_subset_flowMetricBall
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N] [T2Space N] [CompactSpace N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D) (hS : IsSolutionOn (I := J) S)
    (time : RealTimeInterval.FlowTime D) {eps : Real} (heps : 0 < eps)
    (heps1 : eps ≤ 1)
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    (Z : TangentSpace J B.center)
    (hZinj : Z ∈ lInjDomain S (time : Real) B.center
      (eps * B.radius ^ 2))
    (hrange :
      let b := Real.sqrt eps * B.radius
      ∀ s ∈ Icc (0 : Real) b,
        lRegularizedCurve S (time : Real) B.center Z s ∈
          B.setAt ((time : Real) - s ^ 2)) :
    -((Module.finrank Real F : Real) ^ 2 * eps / 3) ≤
      redLength S (time : Real) B.center
        (lExp S (time : Real) B.center Z (eps * B.radius ^ 2))
        (eps * B.radius ^ 2) := by
  let tau : ℝ := eps * B.radius ^ 2
  let K : ℝ := (Module.finrank ℝ F : ℝ) ^ 2 * Real.sqrt (1 / B.radius ^ 4)
  have htau : 0 < tau := mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hb : Real.sqrt tau = Real.sqrt eps * B.radius := by
    dsimp only [tau]
    rw [Real.sqrt_mul heps.le, Real.sqrt_sq_eq_abs, abs_of_pos B.radius_pos]
  obtain ⟨sigma, hsigma, hmin⟩ := hZinj
  have hm : (Z, tau) ∈ lMinDomain S (time : ℝ) B.center :=
    lMinDomain_down S hS (time : ℝ) B.center Z hmin htau hsigma.le
  have hR : ∀ s ∈ Icc (0 : ℝ) (Real.sqrt tau),
      -K ≤ S.scalar ((time : ℝ) - s ^ 2)
        (lRegularizedCurve S (time : ℝ) B.center Z s) := by
    intro s hs
    have hsSq : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
          (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).mpr hs.2
        _ = tau := Real.sq_sqrt htau.le
    have htauR : tau ≤ B.radius ^ 2 := by
      dsimp only [tau]
      exact mul_le_of_le_one_left (sq_nonneg _) heps1
    have ht : (time : ℝ) - s ^ 2 ∈
        Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) :=
      ⟨by linarith, by nlinarith [sq_nonneg s]⟩
    have hsc := scalar_ge_of_rm (I := J) B hB ht
      (hrange s (by simpa only [hb] using hs))
    rw [show Module.finrank ℝ
      (TangentSpace J (lRegularizedCurve S (time : ℝ) B.center Z s)) =
      Module.finrank ℝ F from rfl] at hsc
    simpa only [K, SolutionOn.scalar, SolutionFamily.scalar] using hsc
  have h := redLength_lExp_ge_of_scalar_lower_bound S hS (time : ℝ) B.center Z hm K hR
  have hscale : K * tau = (Module.finrank ℝ F : ℝ) ^ 2 * eps := by
    dsimp only [K, tau]
    have hr2 : 0 < B.radius ^ 2 := sq_pos_of_pos B.radius_pos
    rw [show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring,
      show 1 / (B.radius ^ 2) ^ 2 = (1 / B.radius ^ 2) ^ 2 by field_simp,
      Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr2)]
    field_simp [B.radius_pos.ne']
  simpa only [hscale] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman
