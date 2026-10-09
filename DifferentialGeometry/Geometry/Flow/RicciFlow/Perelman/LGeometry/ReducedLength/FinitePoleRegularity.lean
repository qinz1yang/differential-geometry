import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.LocalCostBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InjOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinNonconjugacy


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped ContDiff Manifold _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

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
private theorem lMinDomain_down_of_slab_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    (Z : E) {sigma rho : ℝ} (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hrho : 0 < rho) (hle : rho ≤ sigma) : (Z, rho) ∈ lMinDomain S T x := by
  obtain ⟨K, hK⟩ := rm_bound_of_mem_lMinDomain S T x hRm hmin
  exact lMinDomain_down_of_rm S hS K T x Z hmin hrho hle hK

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem lMinimizingVector_nconj_lt_of_slab_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : E} {sigma rho : ℝ} (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hle : rho < sigma) : ¬ IsLConjugate S T x Z rho := by
  obtain ⟨K, hK⟩ := rm_bound_of_mem_lMinDomain S T x hRm hmin
  exact lMinVec_nconj_lt_of_rm S hS K T x hmin hle hK

theorem lCost_eq_branch_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (hZ : Z ∈ lInjDomain S T x tau)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConjugate S T x Z tau) :
    (fun y : M ↦ lCost S T x y tau) =ᶠ[nhds (lExp S T x Z tau)]
      lActBranch S hS T x Z tau hdom hconj := by
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  let z : M := lExp S T x Z tau
  have hinvZ : hloc.localInverse z = Z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hsrc : hloc.localInverse.source ∈ nhds z :=
    hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source
  have hpre : hloc.localInverse ⁻¹' lInjDomain S T x tau ∈ nhds z := by
    apply hloc.contMDiffAt_localInverse.continuousAt.preimage_mem_nhds
    rw [hinvZ]
    exact (lInj_isOpen_of_rm S hS T hg x hRm tau).mem_nhds hZ
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _hTtau, _hZdom⟩
  filter_upwards [hsrc, hpre] with y hySource hyInj
  let W : TangentSpace I x := hloc.localInverse y
  obtain ⟨sigma, hsigma, hWmin⟩ := hyInj
  have hWminTau : (W, tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_slab_bounds S hS T x hRm W hWmin htau hsigma.le
  have hright : lExp S T x W tau = y :=
    hloc.localInverse_right_inv hySource
  have hleft : hloc.localInverse (lExp S T x W tau) = W := by
    apply hloc.localInverse_left_inv
    exact hloc.localInverse.map_source hySource
  have hlen :
      lLength S T (fun r : Real ↦ lExp S T x W r) 0 tau =
        lRegularizedAction S T (lRegularizedCurve S T x W) 0 (Real.sqrt tau) := by
    change lLength S T (squareRootReparametrization (lRegularizedCurve S T x W)) 0 tau =
      lRegularizedAction S T (lRegularizedCurve S T x W) 0 (Real.sqrt tau)
    exact lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T
      (lRegularizedCurve S T x W) tau htau.le
  change lCost S T x y tau =
    lRegularizedAction S T (lRegularizedCurve S T x (hloc.localInverse y))
      0 (Real.sqrt tau)
  rw [← hright, hleft, ← hlen]
  exact ((mem_lMinDomain S T x W tau).1 hWminTau).2.symm

theorem lCost_smooth_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    ∃ U : Set M, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf Real Real) ∞
        (fun y : M ↦ lCost S T x y tau) U := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_slab_bounds S hS T x hRm Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConjugate S T x Z tau :=
    lMinimizingVector_nconj_lt_of_slab_bounds S hS T x hRm hmin hsigma
  obtain ⟨U, hUopen, hyU, hsmooth⟩ :=
    lActBranch_smooth S hS T x Z tau hdom hconj
  have heq := lCost_eq_branch_of_rm S hS T hg x hRm
    (Z := Z) (tau := tau) ⟨sigma, hsigma, hmin⟩ hdom hconj
  obtain ⟨V, hVsub, hVopen, hyV⟩ := mem_nhds_iff.mp heq
  refine ⟨U ∩ V, hUopen.inter hVopen, ⟨hyU, hyV⟩, ?_⟩
  refine (hsmooth.mono Set.inter_subset_left).congr ?_
  intro y hy
  exact hVsub hy.2

theorem lCost_hasMFD_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    HasMFDerivAt I (modelWithCornersSelf Real Real)
      (fun y : M ↦ lCost S T x y tau) (lExp S T x Z tau)
      (LinearMap.toContinuousLinearMap
        (metricFlatMap (I := I) (S.base.metric (T - tau))
          (lExp S T x Z tau)
          (lVelocity (I := I) (lRegularizedCurve S T x Z)
            (Real.sqrt tau)))) := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_slab_bounds S hS T x hRm Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConjugate S T x Z tau :=
    lMinimizingVector_nconj_lt_of_slab_bounds S hS T x hRm hmin hsigma
  exact (lActBranch_hasMFD S hS T x Z tau hdom hconj).congr_of_eventuallyEq
    (lCost_eq_branch_of_rm S hS T hg x hRm ⟨sigma, hsigma, hmin⟩ hdom hconj)

theorem lCost_grad_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    gradientFun (I := I) (S.base.metric (T - tau))
        (fun y : M ↦ lCost S T x y tau) (lExp S T x Z tau) =
      lVelocity (I := I) (lRegularizedCurve S T x Z) (Real.sqrt tau) := by
  apply gradientFun_eq_of_flat
  ext V
  have hmfd := lCost_hasMFD_of_rm S hS T hg x hRm htau hZ
  have hd := congrArg (fun L : TangentSpace I (lExp S T x Z tau) →L[Real]
    TangentSpace (modelWithCornersSelf Real Real)
      (lCost S T x (lExp S T x Z tau) tau) ↦ L V) hmfd.mfderiv
  change mvfderiv (I := I) (fun y : M ↦ lCost S T x y tau)
    (lExp S T x Z tau) V = _
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
  have hd' := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real)
      (lCost S T x (lExp S T x Z tau) tau)) hd
  have hcast :
      (LinearMap.toContinuousLinearMap
        (metricFlatMap (I := I) (S.base.metric (T - tau))
          (lExp S T x Z tau)
          (lVelocity (I := I) (lRegularizedCurve S T x Z)
            (Real.sqrt tau)))) V =
        (NormedSpace.fromTangentSpace (𝕜 := Real)
          (lCost S T x (lExp S T x Z tau) tau)).symm
            (metricFlatEquiv (I := I) (S.base.metric (T - tau))
              (lExp S T x Z tau)
              (lVelocity (I := I) (lRegularizedCurve S T x Z)
                (Real.sqrt tau)) V) := by
    rfl
  calc
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real)
        (lCost S T x (lExp S T x Z tau) tau))
          ((LinearMap.toContinuousLinearMap
            (metricFlatMap (I := I) (S.base.metric (T - tau))
              (lExp S T x Z tau)
              (lVelocity (I := I) (lRegularizedCurve S T x Z)
                (Real.sqrt tau)))) V) := hd'
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real)
        (lCost S T x (lExp S T x Z tau) tau))
          ((NormedSpace.fromTangentSpace (𝕜 := Real)
            (lCost S T x (lExp S T x Z tau) tau)).symm
              (metricFlatEquiv (I := I) (S.base.metric (T - tau))
                (lExp S T x Z tau)
                (lVelocity (I := I) (lRegularizedCurve S T x Z)
                  (Real.sqrt tau)) V)) :=
      congrArg (NormedSpace.fromTangentSpace (𝕜 := Real)
        (lCost S T x (lExp S T x Z tau) tau)) hcast
    _ = _ := ContinuousLinearEquiv.apply_symm_apply _ _


theorem redLength_smooth_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    ∃ U : Set M, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf Real Real) ∞
        (fun y : M ↦ redLength S T x y tau) U := by
  obtain ⟨U, hUopen, hyU, hsmooth⟩ :=
    lCost_smooth_of_rm S hS T hg x hRm htau hZ
  refine ⟨U, hUopen, hyU, ?_⟩
  have hmul := (contMDiffOn_const
    (c := (2 * Real.sqrt tau)⁻¹)).mul hsmooth
  refine hmul.congr ?_
  intro y _hy
  change lCost S T x y tau / (2 * Real.sqrt tau) =
    (2 * Real.sqrt tau)⁻¹ * lCost S T x y tau
  rw [div_eq_mul_inv, mul_comm]


theorem redLength_hasMFD_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    HasMFDerivAt I (modelWithCornersSelf Real Real)
      (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau)
      ((2 * Real.sqrt tau)⁻¹ • LinearMap.toContinuousLinearMap
        (metricFlatMap (I := I) (S.base.metric (T - tau))
          (lExp S T x Z tau)
          (lVelocity (I := I) (lRegularizedCurve S T x Z)
            (Real.sqrt tau)))) := by
  have hcost :=
    (lCost_hasMFD_of_rm S hS T hg x hRm htau hZ).const_smul
      (2 * Real.sqrt tau)⁻¹
  apply hcost.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, redLength, div_eq_mul_inv]
    exact mul_comm _ _

theorem redLength_grad_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    gradientFun (I := I) (S.base.metric (T - tau))
        (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) =
      (2 * Real.sqrt tau)⁻¹ •
        lVelocity (I := I) (lRegularizedCurve S T x Z) (Real.sqrt tau) := by
  have hfun :
      (fun y : M ↦ redLength S T x y tau) =
        (2 * Real.sqrt tau)⁻¹ • (fun y : M ↦ lCost S T x y tau) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, redLength, div_eq_mul_inv]
    exact mul_comm _ _
  rw [hfun]
  rw [gradientFun_const_smul (I := I) (S.base.metric (T - tau))
    (2 * Real.sqrt tau)⁻¹
    (lCost_hasMFD_of_rm S hS T hg x hRm htau hZ).mdifferentiableAt]
  rw [lCost_grad_of_rm S hS T hg x hRm htau hZ]
  rfl

theorem redLength_grad_ray_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    gradientFun (I := I) (S.base.metric (T - tau))
        (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) =
      lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau := by
  rw [redLength_grad_of_rm S hS T hg x hRm htau hZ]
  rw [lExp_velocity_sqrt S T x Z htau]
  have hden : 2 * Real.sqrt tau ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.sqrt_pos.2 htau).ne'
  exact inv_smul_smul₀ hden _

theorem lCost_hasDeriv_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    HasDerivAt
      (fun r : Real ↦ lCost S T x (lExp S T x Z tau) r)
      (Real.sqrt tau *
        (S.scalar (T - tau) (lExp S T x Z tau) -
          lSpeedSq S T (fun r : Real ↦ lExp S T x Z r) tau)) tau := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_slab_bounds S hS T x hRm Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConjugate S T x Z tau :=
    lMinimizingVector_nconj_lt_of_slab_bounds S hS T x hRm hmin hsigma
  let J := (modelWithCornersSelf Real E).prod
    (modelWithCornersSelf Real Real)
  let K := I.prod (modelWithCornersSelf Real Real)
  let f : E × Real → M := fun p ↦ lExp S T x p.1 p.2
  let F : E × Real → M × Real := fun p ↦ (f p, p.2)
  let y : M := lExp S T x Z tau
  let q : Real → M × Real := fun r ↦ (y, r)
  let p : Real → E × Real := fun r ↦
    (lExpTime_local S hS T x Z tau hdom hconj).localInverse (q r)
  let A : E × Real → Real := fun z ↦
    lRegularizedAction S T (lRegularizedCurve S T x z.1) 0 (Real.sqrt z.2)
  let hloc : IsLocalDiffeomorphAt J K ∞ F (Z, tau) := by
    simpa only [J, K, F, f] using
      lExpTime_local S hS T x Z tau hdom hconj
  have hp0 : p tau = (Z, tau) := by
    have hp0' :=
      hloc.localInverse_left_inv hloc.localInverse_mem_target
    change hloc.localInverse (F (Z, tau)) = (Z, tau) at hp0'
    change p tau = (Z, tau)
    exact hp0'
  let b : Real := Real.sqrt tau
  let endMap : E → M := fun W ↦ lExp S T x W tau
  let Lz : E →L[Real] Real :=
    ((S.base.metric (T - tau)).inner y
      (lVelocity (I := I) (lRegularizedCurve S T x Z) b)).comp
        (mfderiv (modelWithCornersSelf Real E) I endMap Z)
  let c : Real := lRegularizedLagrangian S T (lRegularizedCurve S T x Z) b / (2 * b)
  let L : E × Real →L[Real] Real :=
    Lz.comp (ContinuousLinearMap.fst Real E Real) +
      c • ContinuousLinearMap.snd Real E Real
  have hJoint : HasFDerivAt A L (Z, tau) := by
    exact hasFDerivAt_lRegularizedAction_lRegularizedCurve_sqrt S hS T x Z hdom
  have hq : HasMFDerivAt (modelWithCornersSelf Real Real) K q tau
      ((0 : TangentSpace (modelWithCornersSelf Real Real) tau →L[Real]
          TangentSpace I y).prod
        (ContinuousLinearMap.id Real
          (TangentSpace (modelWithCornersSelf Real Real) tau))) := by
    change HasMFDerivAt (modelWithCornersSelf Real Real) K
      (fun r ↦ (y, id r)) tau _
    exact (hasMFDerivAt_const (c := y) (x := tau)).prodMk
      (hasMFDerivAt_id tau)
  have hInv : MDifferentiableAt K J hloc.localInverse (q tau) := by
    simpa only [q, y, F, f] using
      hloc.mdifferentiableAt_localInverse (by simp)
  have hpM : HasMFDerivAt (modelWithCornersSelf Real Real) J p tau
      ((mfderiv K J hloc.localInverse (q tau)).comp
        ((0 : TangentSpace (modelWithCornersSelf Real Real) tau →L[Real]
            TangentSpace I y).prod
          (ContinuousLinearMap.id Real
            (TangentSpace (modelWithCornersSelf Real Real) tau)))) := by
    change HasMFDerivAt (modelWithCornersSelf Real Real) J
      (hloc.localInverse ∘ q) tau _
    exact hInv.hasMFDerivAt.comp tau hq
  let eT : E × Real := ((0 : E), (1 : Real))
  let v : E × Real := mfderiv K J hloc.localInverse (q tau) eT
  have hJointP : HasMFDerivAt J (modelWithCornersSelf Real Real)
      A (p tau) L := by
    rw [hp0]
    exact hJoint.hasMFDerivAt
  have hbranch : HasDerivAt (fun r : Real ↦ A (p r)) (L v) tau := by
    have hcomp := hJointP.hasFDerivAt.comp tau hpM.hasFDerivAt
    have hraw := hcomp.hasDerivAt
    change HasDerivAt (A ∘ p) (L v) tau
    exact hraw
  have hright : mfderiv J K F (Z, tau) v = eT := by
    have hright' :=
      (hloc.mfderivToContinuousLinearEquiv (by simp)).right_inv eT
    change mfderiv J K F (Z, tau)
      (mfderiv K J hloc.localInverse (q tau) eT) = eT at hright'
    exact hright'
  have hfdiff : MDifferentiableAt J I f (Z, tau) := by
    have hf := ((lExp_smoothOn S hS T x).contMDiffAt
      ((lExpPosDom_open S hS T x).mem_nhds hdom)).mdifferentiableAt
        (by simp)
    change MDifferentiableAt J I f (Z, tau) at hf
    exact hf
  have hsndDiff : MDifferentiableAt J (modelWithCornersSelf Real Real)
      (@Prod.snd E Real) (Z, tau) := by
    simpa only [J] using
      (mdifferentiableAt_snd : MDifferentiableAt J
        (modelWithCornersSelf Real Real) (@Prod.snd E Real) (Z, tau))
  have hFderiv : mfderiv J K F (Z, tau) =
      (mfderiv J I f (Z, tau)).prod
        (mfderiv J (modelWithCornersSelf Real Real) (@Prod.snd E Real)
          (Z, tau)) := by
    simpa only [F] using mfderiv_prodMk hfdiff hsndDiff
  have hsndDeriv :=
    (mfderiv_snd : mfderiv
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) (@Prod.snd E Real) (Z, tau) =
        ContinuousLinearMap.snd Real
          (TangentSpace (modelWithCornersSelf Real E) (show E from Z))
          (TangentSpace (modelWithCornersSelf Real Real) tau))
  rw [hFderiv, hsndDeriv] at hright
  change (mfderiv J I f (Z, tau) v, v.2) = ((0 : E), (1 : Real)) at hright
  have hExpZero : mfderiv J I f (Z, tau) v = 0 :=
    congrArg Prod.fst hright
  have hv2 : v.2 = 1 := congrArg Prod.snd hright
  have hsplit := mfderiv_prod_eq_add_apply hfdiff (v := v)
  have htimeVelocity :
      mfderiv (modelWithCornersSelf Real Real) I
          (fun r : Real ↦ f (Z, r)) tau v.2 =
        lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau := by
    rw [hv2]
    rfl
  have hsum :
      mfderiv (modelWithCornersSelf Real E) I
          (fun W : E ↦ f (W, tau)) Z v.1 +
        lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau = 0 := by
    rw [← htimeVelocity]
    exact hsplit.symm.trans hExpZero
  have hspace :
      mfderiv (modelWithCornersSelf Real E) I endMap Z v.1 =
        -lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau := by
    change mfderiv (modelWithCornersSelf Real E) I
      (fun W : E ↦ f (W, tau)) Z v.1 = _
    exact eq_neg_of_add_eq_zero_left hsum
  have hvel :
      lVelocity (I := I) (lRegularizedCurve S T x Z) b =
        (2 * b) • lVelocity (I := I)
          (fun r : Real ↦ lExp S T x Z r) tau := by
    simpa only [b] using lExp_velocity_sqrt S T x Z htau
  have hb0 : b ≠ 0 := (Real.sqrt_pos.2 htau).ne'
  have hbsq : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hLv : L v =
      b * (S.scalar (T - tau) y -
        lSpeedSq S T (fun r : Real ↦ lExp S T x Z r) tau) := by
    change ((S.base.metric (T - tau)).inner y
        (lVelocity (I := I) (lRegularizedCurve S T x Z) b))
          (mfderiv (modelWithCornersSelf Real E) I endMap Z v.1) +
        c * v.2 = _
    simp only [c, lRegularizedLagrangian]
    rw [hspace, hv2, hvel]
    have hendb : lRegularizedCurve S T x Z b = y := by
      simp only [b, y, lExp]
    rw [hbsq, hendb]
    simp only [lSpeedSq]
    simp only [((S.base.metric (T - tau)).inner y).map_smul,
      smul_apply]
    simp only [((S.base.metric (T - tau)).inner y
      (lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau)).map_smul,
      ((S.base.metric (T - tau)).inner y
        (lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau)).map_neg,
      smul_eq_mul]
    field_simp [hb0]
    rw [hbsq]
    rw [show lExp S T x Z tau = y by rfl]
    ring
  have hEq : (fun r : Real ↦ A (p r)) =ᶠ[nhds tau]
      fun r : Real ↦ lCost S T x y r := by
    let rho : Real := (tau + sigma) / 2
    have htRho : tau < rho := by
      dsimp only [rho]
      linarith
    have hRhoS : rho < sigma := by
      dsimp only [rho]
      linarith
    have hZrho : Z ∈ lInjDomain S T x rho := ⟨sigma, hRhoS, hmin⟩
    have hsrc : ∀ᶠ r in nhds tau, q r ∈ hloc.localInverse.source := by
      apply hq.continuousAt.eventually
      have hcenter : q tau = F (Z, tau) := by rfl
      rw [hcenter]
      exact hloc.localInverse_open_source.mem_nhds
        hloc.localInverse_mem_source
    have hpos : ∀ᶠ r in nhds tau, 0 < r := eventually_gt_nhds htau
    have hlt : ∀ᶠ r in nhds tau, r < rho := eventually_lt_nhds htRho
    have hinj : ∀ᶠ r in nhds tau,
        (p r).1 ∈ lInjDomain S T x rho := by
      apply hpM.continuousAt.fst.eventually
      change lInjDomain S T x rho ∈ nhds (p tau).1
      rw [hp0]
      exact (lInj_isOpen_of_rm S hS T hg x hRm rho).mem_nhds hZrho
    filter_upwards [hsrc, hpos, hlt, hinj] with r hrSource hrpos hrRho hpr
    have hright' := hloc.localInverse_right_inv hrSource
    have hp2 : (p r).2 = r := by
      simpa only [F, f, q] using congrArg Prod.snd hright'
    have hend : lExp S T x (p r).1 r = y := by
      have hend' := congrArg Prod.fst hright'
      have hend'' : lExp S T x (p r).1 (p r).2 = y := by
        simpa only [F, f, q, p, hloc] using hend'
      rwa [hp2] at hend''
    obtain ⟨theta, hRhoTheta, hWmin⟩ := hpr
    have hrt : r ≤ theta := (hrRho.trans hRhoTheta).le
    have hWminr : ((p r).1, r) ∈ lMinDomain S T x :=
      lMinDomain_down_of_slab_bounds S hS T x hRm (p r).1 hWmin hrpos hrt
    have hcost := ((mem_lMinDomain S T x (p r).1 r).1 hWminr).2
    change lRegularizedAction S T (lRegularizedCurve S T x (p r).1) 0
        (Real.sqrt (p r).2) = lCost S T x y r
    rw [hp2]
    calc
      lRegularizedAction S T (lRegularizedCurve S T x (p r).1) 0 (Real.sqrt r) =
          lLength S T (fun s : Real ↦ lExp S T x (p r).1 s) 0 r := by
        change lRegularizedAction S T (lRegularizedCurve S T x (p r).1) 0 (Real.sqrt r) =
          lLength S T (squareRootReparametrization (lRegularizedCurve S T x (p r).1)) 0 r
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T
          (lRegularizedCurve S T x (p r).1) r hrpos.le).symm
      _ = lCost S T x (lExp S T x (p r).1 r) r := hcost
      _ = lCost S T x y r := by rw [hend]
  have hcost := hbranch.congr_of_eventuallyEq hEq.symm
  rw [hLv] at hcost
  simpa only [A, p, y, b] using hcost

theorem redLength_hasDeriv_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    HasDerivAt
      (fun r : Real ↦ redLength S T x (lExp S T x Z tau) r)
      ((S.scalar (T - tau) (lExp S T x Z tau) -
          lSpeedSq S T (fun r : Real ↦ lExp S T x Z r) tau) / 2 -
        redLength S T x (lExp S T x Z tau) tau / (2 * tau)) tau := by
  let y : M := lExp S T x Z tau
  let gamma : Real → M := fun r ↦ lExp S T x Z r
  let b : Real := Real.sqrt tau
  have hcost : HasDerivAt (fun r : Real ↦ lCost S T x y r)
      (b * (S.scalar (T - tau) y - lSpeedSq S T gamma tau)) tau := by
    simpa only [y, gamma, b] using lCost_hasDeriv_of_rm S hS T hg x hRm htau hZ
  have hb0 : b ≠ 0 := (Real.sqrt_pos.2 htau).ne'
  have hden0 : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb0
  have hquot := hcost.div
    ((Real.hasDerivAt_sqrt htau.ne').const_mul 2) hden0
  have hbsq : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hderiv :
      (b * (S.scalar (T - tau) y - lSpeedSq S T gamma tau) *
          (2 * b) - lCost S T x y tau * (2 * (1 / (2 * b)))) /
          (2 * b) ^ 2 =
        (S.scalar (T - tau) y - lSpeedSq S T gamma tau) / 2 -
          redLength S T x y tau / (2 * tau) := by
    simp only [redLength]
    change _ =
      (S.scalar (T - tau) y - lSpeedSq S T gamma tau) / 2 -
        (lCost S T x y tau / (2 * b)) / (2 * tau)
    rw [← hbsq]
    field_simp [hb0]
  have hquot' : HasDerivAt
      ((fun r : Real ↦ lCost S T x y r) /
        fun r : Real ↦ 2 * Real.sqrt r)
      ((S.scalar (T - tau) y - lSpeedSq S T gamma tau) / 2 -
        redLength S T x y tau / (2 * tau)) tau := by
    apply hquot.congr_deriv
    simpa only [b] using hderiv
  have hred := hquot'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r ↦ by
      change redLength S T x y r = lCost S T x y r / (2 * Real.sqrt r)
      rfl)
  simpa only [y, gamma] using hred

theorem redLength_HJ_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    deriv (fun r : Real ↦ redLength S T x (lExp S T x Z tau) r) tau +
        (1 / 2 : Real) *
          (S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (gradientFun (I := I) (S.base.metric (T - tau))
              (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau))
            (gradientFun (I := I) (S.base.metric (T - tau))
              (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau)) -
        (1 / 2 : Real) * S.scalar (T - tau) (lExp S T x Z tau) +
        redLength S T x (lExp S T x Z tau) tau / (2 * tau) = 0 := by
  rw [(redLength_hasDeriv_of_rm S hS T hg x hRm htau hZ).deriv]
  rw [redLength_grad_ray_of_rm S hS T hg x hRm htau hZ]
  simp only [lSpeedSq]
  ring


end DifferentialGeometry.PDE.RicciFlow.Perelman
