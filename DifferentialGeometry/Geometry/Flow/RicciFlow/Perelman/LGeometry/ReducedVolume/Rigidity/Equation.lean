import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.FinitePoleRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.GaussianJacobian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RedJacobian
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff Manifold _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private theorem lExpTrace_eq_laplacian_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : E} {tau : ℝ} (hZ : Z ∈ lInjDomain S T x tau)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    (1 / 2 : ℝ) * Matrix.trace
        ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) =
      laplacian (LeviCivita (S.base.metric (T - tau))) (S.base.metric (T - tau))
        (fun y => redLength S T x y tau) (lExp S T x Z tau) +
      S.scalar (T - tau) (lExp S T x Z tau) := by
  let g := S.base.metric (T - tau)
  let y := lExp S T x Z tau
  let A := lActBranch S hS T x Z tau hdom hnconj
  let c : ℝ := 1 / (2 * Real.sqrt tau)
  obtain ⟨U, hU, hyU, hA⟩ := lActBranch_smooth S hS T x Z tau hdom hnconj
  have hAat : ContMDiffAt I 𝓘(ℝ) ∞ A y :=
    (hA y hyU).contMDiffAt (hU.mem_nhds hyU)
  have hAc : ContMDiffAt I 𝓘(ℝ) ∞ (c • A) y := by
    change ContMDiffAt I 𝓘(ℝ) ∞ (fun z => c * A z) y
    exact contMDiffAt_const.mul hAat
  have heq : (fun z => redLength S T x z tau) =ᶠ[𝓝 y] c • A := by
    filter_upwards [lCost_eq_branch_of_rm S hS T hg x hRm hZ hdom hnconj] with z hz
    simp only [redLength, hz, Pi.smul_apply, smul_eq_mul, c, A]
    ring
  have hlc : laplacian (LeviCivita g) g (c • A) y =
      c * laplacian (LeviCivita g) g A y := by
    apply laplacian_smul_at
    · filter_upwards [hU.mem_nhds hyU] with z hz
      exact ((hA z hz).contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt (by simp)
    · exact (gradientFun_contMDiffAt g hAat).mdifferentiableAt (by simp)
  have hl := laplacian_congr_of_eventuallyEq (LeviCivita g) g
    (hAc.congr_of_eventuallyEq heq) hAc heq
  rw [hlc, lap_eq_hess_on g hU hA hyU] at hl
  rw [lExpTrace_eq_branch S hS T x Z tau hdom hnconj]
  exact congrArg (fun r => r + S.scalar (T - tau) y) hl.symm

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem rm_bound_of_mem_lMinDomain
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : E} {sigma : ℝ} (hmin : (Z, sigma) ∈ lMinDomain S T x) :
    ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K := by
  have hdom := ((mem_lMinDomain S T x Z sigma).mp hmin).1
  have hsigma := lMinDomain_pos S T x Z sigma hmin
  apply hRm sigma hsigma
  intro t ht
  have ht0 : 0 ≤ T - t := sub_nonneg.mpr ht.2
  have htS : T - t ≤ sigma := by linarith only [ht.1]
  have hsqrt : Real.sqrt (T - t) ∈ Icc (0 : ℝ) (Real.sqrt sigma) :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt htS⟩
  have h := lExpPosDom_regularity S T x Z hdom hsqrt
  have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by rw [Real.sq_sqrt ht0]; ring
  simpa only [heq] using h


omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem lK_quotient_eq_of_mem_lMinDomain
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {Z : E} {s : ℝ}
    (hmin : (Z, s) ∈ lMinDomain S T x) :
    lK S T (lRegularizedCurve S T x Z) (Real.sqrt s) / (2 * s * Real.sqrt s) =
      redLength S T x (lExp S T x Z s) s / (2 * s) -
        (S.scalar (T - s) (lExp S T x Z s) +
          lSpeedSq S T (fun r => lExp S T x Z r) s) / 2 := by
  have hs := lMinDomain_pos S T x Z s hmin
  have hdom := ((mem_lMinDomain S T x Z s).mp hmin).1
  have hbdom := ((mem_lExpPosDom S T x Z s).mp hdom).2.2
  have hcost := ((mem_lMinDomain S T x Z s).mp hmin).2
  let b := Real.sqrt s
  have hb : 0 < b := Real.sqrt_pos.mpr hs
  have hbsq : b ^ 2 = s := Real.sq_sqrt hs.le
  have hact : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b =
      lCost S T x (lExp S T x Z s) s := by
    rw [← hcost]
    exact (lLength_squareRootReparametrization_eq_lRegularizedAction S T
      (lRegularizedCurve S T x Z) s hs.le).symm
  have henergy := lK_ray_energy S hS T x Z hb hbdom
  have hvel : lVelocity (I := I) (lRegularizedCurve S T x Z) b =
      (2 * b) • lVelocity (I := I) (fun r => lExp S T x Z r) s :=
    lExp_velocity_sqrt S T x Z hs
  have hend : lRegularizedCurve S T x Z b = lExp S T x Z s := rfl
  have hlag : lRegularizedLagrangian S T (lRegularizedCurve S T x Z) b =
      2 * s * (lSpeedSq S T (fun r => lExp S T x Z r) s +
        S.scalar (T - s) (lExp S T x Z s)) := by
    simp only [lRegularizedLagrangian, hvel, hbsq, hend]
    change (1 / 2 : ℝ) * (S.base.metric (T - s)).inner (lExp S T x Z s)
        ((2 * b) • lVelocity (I := I) (fun r => lExp S T x Z r) s)
        ((2 * b) • lVelocity (I := I) (fun r => lExp S T x Z r) s) + _ = _
    simp only [map_smul, smul_apply, smul_eq_mul, lSpeedSq]
    rw [← hbsq]
    ring
  change lK S T (lRegularizedCurve S T x Z) b / (2 * s * b) = _
  rw [henergy, hact, hlag]
  simp only [redLength]
  change (lCost S T x (lExp S T x Z s) s -
      b * (2 * s * (lSpeedSq S T (fun r => lExp S T x Z r) s +
        S.scalar (T - s) (lExp S T x Z s)))) / 2 / (2 * s * b) =
    (lCost S T x (lExp S T x Z s) s / (2 * b)) / (2 * s) - _
  field_simp [hs.ne', hb.ne']
  ring

variable [ConnectedSpace M]

theorem redLength_laplacian_eq_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) {Z : E}
    (hZ : Z ∈ lInjDomain S T x s) :
    laplacian (LeviCivita (S.base.metric (T - s))) (S.base.metric (T - s))
        (fun y => redLength S T x y s) (lExp S T x Z s) =
      (Module.finrank ℝ E : ℝ) / (2 * s) -
        S.scalar (T - s) (lExp S T x Z s) -
        lK S T (lRegularizedCurve S T x Z) (Real.sqrt s) /
          (2 * s * Real.sqrt s) := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  obtain ⟨K, hK⟩ := rm_bound_of_mem_lMinDomain S T x hRm hmin
  have hssigma := hsigma
  have hmins := lMinDomain_down_of_rm S hS K T x Z hmin hs hssigma.le hK
  have hdom := ((mem_lMinDomain S T x Z s).mp hmins).1
  have hnconj := lMinVec_nconj_lt_of_rm S hS K T x hmin hssigma hK
  let rho : ℝ := min tau ((s + sigma) / 2)
  have hsrho : s < rho := lt_min hstau (by linarith only [hsigma])
  have hrhosigma : rho < sigma :=
    (min_le_right tau ((s + sigma) / 2)).trans_lt (by linarith only [hsigma])
  have hrhotau : rho ≤ tau := min_le_left _ _
  have hslabrho : Icc (T - rho) T ⊆ D.regular :=
    (Icc_subset_Icc (sub_le_sub_left hrhotau T) le_rfl).trans hslab
  have hvolrho : redVolume S T x rho = 1 := by
    apply le_antisymm
    · exact DifferentialGeometry.PDE.RicciFlow.redVolume_le_one_of_rm
        S hS T hg x hRm rho (hs.trans hsrho) hslabrho
    · have hm := DifferentialGeometry.PDE.RicciFlow.redVolume_anti_of_rm
        S hS T hg x hRm (hs.trans hsrho) hrhotau hslab
      change redVolume S T x tau ≤ redVolume S T x rho at hm
      rwa [hvol] at hm
  have hz := hasDerivAt_lReducedJacobian_zero_of_redVolume_eq_one
    S hS T hg x hRm hs hsrho hslabrho hvolrho ⟨sigma, hrhosigma, hmin⟩
  have hj := lRedJac_hasDeriv_of_rm S hS K T x hmin hs hssigma hK
  have heq := hj.unique hz
  have hJpos : 0 < lReducedJacobian S T x Z s := Real.exp_pos _
  have hzero := (mul_eq_zero.mp heq).resolve_left hJpos.ne'
  rw [lExpTrace_eq_laplacian_of_rm S hS T hg x hRm
    ⟨sigma, hssigma, hmin⟩ hdom hnconj] at hzero
  linarith only [hzero]

theorem redLength_conjugateHeat_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) {Z : E}
    (hZ : Z ∈ lInjDomain S T x s) :
    deriv (fun r => redLength S T x (lExp S T x Z s) r) s -
        laplacian (LeviCivita (S.base.metric (T - s))) (S.base.metric (T - s))
          (fun y => redLength S T x y s) (lExp S T x Z s) +
        (S.base.metric (T - s)).inner (lExp S T x Z s)
          (gradientFun (S.base.metric (T - s))
            (fun y => redLength S T x y s) (lExp S T x Z s))
          (gradientFun (S.base.metric (T - s))
            (fun y => redLength S T x y s) (lExp S T x Z s)) -
        S.scalar (T - s) (lExp S T x Z s) +
        (Module.finrank ℝ E : ℝ) / (2 * s) = 0 := by
  have hlap := redLength_laplacian_eq_of_redVolume_eq_one
    S hS T hg x hRm hs hstau hslab hvol hZ
  have ht := (redLength_hasDeriv_of_rm S hS T hg x hRm hs hZ).deriv
  have hgrad := redLength_grad_ray_of_rm S hS T hg x hRm hs hZ
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  obtain ⟨K, hK⟩ := rm_bound_of_mem_lMinDomain S T x hRm hmin
  have hmins := lMinDomain_down_of_rm S hS K T x Z hmin hs hsigma.le hK
  have henergy := lK_quotient_eq_of_mem_lMinDomain S hS T x hmins
  rw [ht, hlap, hgrad, henergy]
  simp only [lSpeedSq]
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman
