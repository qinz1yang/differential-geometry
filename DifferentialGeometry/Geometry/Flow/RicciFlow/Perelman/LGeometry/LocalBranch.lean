import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RayEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Conjugate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CostContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RayGlobalize
import DifferentialGeometry.Geometry.Comparison.Variation.BoundedCurve
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Gradient
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import DifferentialGeometry.Analysis.Calculus.BumpClamp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

section Barrier

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]

theorem upper_deriv_eq
    {f F G : X → Real} {x : X}
    (hf : DifferentiableAt Real f x)
    (hF : DifferentiableAt Real F x) (hG : DifferentiableAt Real G x)
    (hFup : f ≤ᶠ[nhds x] F) (hGup : f ≤ᶠ[nhds x] G)
    (hFx : F x = f x) (hGx : G x = f x) :
    fderiv Real F x = fderiv Real G x := by
  have hFmin : IsLocalMin (fun y ↦ F y - f y) x := by
    change ∀ᶠ y in nhds x, F x - f x ≤ F y - f y
    filter_upwards [hFup] with y hy
    rw [hFx, sub_self]
    exact sub_nonneg.mpr hy
  have hGmin : IsLocalMin (fun y ↦ G y - f y) x := by
    change ∀ᶠ y in nhds x, G x - f x ≤ G y - f y
    filter_upwards [hGup] with y hy
    rw [hGx, sub_self]
    exact sub_nonneg.mpr hy
  have hFzero := hFmin.fderiv_eq_zero
  have hGzero := hGmin.fderiv_eq_zero
  change fderiv Real (F - f) x = 0 at hFzero
  change fderiv Real (G - f) x = 0 at hGzero
  rw [fderiv_sub hF hf] at hFzero
  rw [fderiv_sub hG hf] at hGzero
  have hFzero' : fderiv Real F x - fderiv Real f x = 0 := by
    exact hFzero
  have hGzero' : fderiv Real G x - fderiv Real f x = 0 := by
    exact hGzero
  exact sub_eq_zero.mp hFzero' |>.trans (sub_eq_zero.mp hGzero').symm

theorem not_diff_two_upper
    {f F G : X → Real} {x : X}
    (hF : DifferentiableAt Real F x) (hG : DifferentiableAt Real G x)
    (hFup : f ≤ᶠ[nhds x] F) (hGup : f ≤ᶠ[nhds x] G)
    (hFx : F x = f x) (hGx : G x = f x)
    (hne : fderiv Real F x ≠ fderiv Real G x) :
    ¬ DifferentiableAt Real f x := by
  intro hf
  exact hne (upper_deriv_eq hf hF hG hFup hGup hFx hGx)

end Barrier

private theorem exists_open_clamp
    {K : Set Real} {b : Real} (hKopen : IsOpen K)
    (hKconn : IsPreconnected K) (h0K : (0 : Real) ∈ K)
    (hbK : b ∈ K) (hb0 : 0 < b) :
    ∃ rho : Real → Real, ∃ a d : Real,
      a < 0 ∧ b < d ∧ ContDiff Real ∞ rho ∧
      Set.EqOn rho id (Set.Icc a d) ∧
      ∀ s : Real, rho s ∈ K := by
  have hseg : Set.Icc (0 : Real) b ⊆ K := by
    simpa only [Set.uIcc_of_le hb0.le] using
      hKconn.ordConnected.uIcc_subset h0K hbK
  obtain ⟨margin, hmargin, hbuffer⟩ :=
    isCompact_Icc.exists_cthickening_subset_open hKopen hseg
  let a : Real := -(margin / 2)
  let d : Real := b + margin / 2
  let eps : Real := margin / 4
  have ha0 : a < 0 := by
    dsimp only [a]
    linarith
  have hbd : b < d := by
    dsimp only [d]
    linarith
  have had : a < d := lt_trans ha0 (hb0.trans hbd)
  have heps : 0 < eps := by
    dsimp only [eps]
    linarith
  obtain ⟨rho, hrho, hrho_id, _hrho_deriv, hrho_range⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp a d eps had heps
  refine ⟨rho, a, d, ha0, hbd, hrho, ?_, fun s ↦ hbuffer ?_⟩
  · intro s hs
    simpa only [id_eq] using hrho_id s hs
  · by_cases hs0 : rho s ≤ 0
    · refine Metric.mem_cthickening_of_dist_le (rho s) 0 margin
        (Set.Icc (0 : Real) b) ⟨le_rfl, hb0.le⟩ ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonpos hs0]
      have hlo := (hrho_range s).1
      dsimp only [a, eps] at hlo
      linarith
    · by_cases hsb : rho s ≤ b
      · refine Metric.mem_cthickening_of_dist_le (rho s) (rho s) margin
          (Set.Icc (0 : Real) b) ⟨(not_le.mp hs0).le, hsb⟩ ?_
        simpa using hmargin.le
      · refine Metric.mem_cthickening_of_dist_le (rho s) b margin
          (Set.Icc (0 : Real) b) ⟨hb0.le, le_rfl⟩ ?_
        rw [Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (not_le.mp hsb).le)]
        have hhi := (hrho_range s).2
        dsimp only [d, eps] at hhi
        linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRayAct_contAt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (b : Real)
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    ContinuousAt
      (fun W : E ↦ lRegAction S T (lRegCurve S T x W) 0 b) Z := by
  change Tendsto (fun W : E ↦
    lRegAction S T (lRegCurve S T x W) 0 b) (nhds Z)
      (nhds (lRegAction S T (lRegCurve S T x Z) 0 b))
  apply tendsto_nhds_iff_seq_tendsto.2
  intro W hW
  change Tendsto (fun n ↦
    lRegAction S T (lRegCurve S T x (show TangentSpace I x from W n)) 0 b)
      atTop (nhds (lRegAction S T (lRegCurve S T x Z) 0 b))
  exact lRayAct_tendsto S hS T x hb0 hb hW tendsto_const_nhds

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lRayAct_smooth
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (b : Real)
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    ∃ U : Set E, IsOpen U ∧ Z ∈ U ∧
      ContDiffOn Real ∞
        (fun W : E ↦ lRegAction S T (lRegCurve S T x W) 0 b) U := by
  obtain ⟨J, hJopen, hJconn, h0J, hbJ, hchosen⟩ :=
    lRegChosen_spec S T x Z hb
  obtain ⟨V, hVopen, hZV, K, hKopen, hKconn, h0K, hbK,
      alpha, _halpha, hcurves⟩ :=
    lRegFamily_extend S hS T hJopen hJconn h0J hbJ hchosen
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrhoK⟩ :=
    exists_open_clamp hKopen hKconn h0K hbK hb0
  obtain ⟨eps, heps, hball⟩ := (Metric.isOpen_iff.mp hVopen)
    (show E from Z) hZV
  let bump : ContDiffBump (0 : E) :=
    { rIn := eps / 2
      rOut := eps
      rIn_pos := half_pos heps
      rIn_lt_rOut := half_lt_self heps }
  let z : E := Z
  let phi : E → E := fun W ↦ z + bump.radial (W - z)
  have hphi : ContDiff Real ∞ phi := by
    exact contDiff_const.add
      (bump.radial_contDiff.comp (contDiff_id.sub contDiff_const))
  have hphiV : ∀ W : E, phi W ∈ V := by
    intro W
    apply hball
    have hw := bump.radial_mapsTo (Set.mem_univ (W - z))
    rw [Metric.mem_ball] at hw ⊢
    change dist (z + bump.radial (W - z)) z < eps
    simpa only [dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
  have hVK : V ×ˢ K ⊆ lRegJointDom S T x := by
    intro q hq
    change q.2 ∈ lRegDomain S T x q.1
    exact ⟨fun s ↦ alpha (q.1, s), K, hKopen, hKconn, h0K, hq.2,
      hcurves q.1 hq.1⟩
  have hlag := (lRayLag_smooth S hS T x).mono hVK
  let G : E → Real → Real := fun W u ↦
    b * lRegLag S T (lRegCurve S T x (phi W)) (rho (b * u))
  have hG : ContDiffOn Real ∞
      (fun q : E × Real ↦ G q.1 q.2) Set.univ := by
    intro q _hq
    have hfirst : ContDiffAt Real ∞ (fun r : E × Real ↦ phi r.1) q :=
      hphi.contDiffAt.comp q contDiffAt_fst
    have htime : ContDiffAt Real ∞
        (fun r : E × Real ↦ rho (b * r.2)) q :=
      hrho.contDiffAt.comp q (contDiffAt_const.mul contDiffAt_snd)
    have hpair := hfirst.prodMk htime
    have hmem : (phi q.1, rho (b * q.2)) ∈ V ×ˢ K :=
      ⟨hphiV q.1, hrhoK _⟩
    have hcomp := (hlag.contDiffAt
      ((hVopen.prod hKopen).mem_nhds hmem)).comp q hpair
    change ContDiffWithinAt Real ∞
      (fun r : E × Real ↦
        b * lRegLag S T (lRegCurve S T x (phi r.1)) (rho (b * r.2)))
      Set.univ q
    exact (contDiffAt_const.mul hcomp).contDiffWithinAt
  let A : E → Real := fun W ↦ ∫ u in (0 : Real)..1, G W u
  have hA : ContDiffOn Real ∞ A Set.univ :=
    DifferentialGeometry.Analysis.Calculus.contDiffOn_paramIntervalIntegral
      (E₀ := E) G hG
  let U : Set E := Metric.ball z (eps / 2)
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hZU : Z ∈ U := by
    change z ∈ Metric.ball z (eps / 2)
    simpa only [Metric.mem_ball, dist_self] using half_pos heps
  have hEq : Set.EqOn A
      (fun W : E ↦ lRegAction S T (lRegCurve S T x W) 0 b) U := by
    intro W hWU
    have hrad : bump.radial (W - z) = W - z := by
      apply bump.radial_eq_self
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa only [Metric.mem_ball, dist_eq_norm] using
        (Metric.mem_ball.mp hWU).le
    have hphiW : phi W = W := by
      change z + bump.radial (W - z) = W
      rw [hrad]
      abel
    have hclamp : Set.EqOn (fun u : Real ↦ rho (b * u))
        (fun u : Real ↦ b * u) (Set.Icc 0 1) := by
      intro u hu
      apply hrho_id
      exact ⟨ha0.le.trans (mul_nonneg hb0.le hu.1),
        (mul_le_of_le_one_right hb0.le hu.2).trans hbd.le⟩
    have hcongr : A W = ∫ u in (0 : Real)..1,
        b * lRegLag S T (lRegCurve S T x W) (b * u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Set.Icc (0 : Real) 1 := by
        simpa only [Set.uIcc_of_le zero_le_one] using hu
      simp only [G, hphiW, hclamp hu']
    rw [hcongr]
    simp only [lRegAction]
    simpa only [smul_eq_mul, zero_mul, one_mul, mul_zero, mul_one,
      intervalIntegral.integral_const_mul] using
      (intervalIntegral.smul_integral_comp_mul_left
        (a := (0 : Real)) (b := (1 : Real))
        (fun s : Real ↦ lRegLag S T (lRegCurve S T x W) s) b)
  refine ⟨U, hUopen, hZU, ?_⟩
  exact (hA.mono (Set.subset_univ U)).congr fun W hW ↦ (hEq hW).symm

omit [SigmaCompactSpace M] in
def lActBranch
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) (y : M) : Real :=
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  lRegAction S T
    (lRegCurve S T x (hloc.localInverse y)) 0 (Real.sqrt tau)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lActBranch_smooth
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    ∃ U : Set M, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf Real Real) ∞
        (lActBranch S hS T x Z tau hdom hconj) U := by
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _htime, hb⟩
  obtain ⟨V, hVopen, hZV, hact⟩ :=
    lRayAct_smooth S hS T x Z (Real.sqrt tau)
      (Real.sqrt_pos.2 htau) hb
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  let U : Set M := hloc.localInverse.source ∩ hloc.localInverse ⁻¹' V
  have hUopen : IsOpen U :=
    hloc.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hVopen
  have hinv : hloc.localInverse (lExp S T x Z tau) = Z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hyU : lExp S T x Z tau ∈ U := by
    refine ⟨hloc.localInverse_mem_source, ?_⟩
    change hloc.localInverse (lExp S T x Z tau) ∈ V
    rw [hinv]
    exact hZV
  have hray : ContMDiffOn (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real Real) ∞
      (fun W : E ↦ lRegAction S T (lRegCurve S T x W) 0
        (Real.sqrt tau)) V :=
    contMDiffOn_iff_contDiffOn.mpr hact
  have hinvMD := hloc.localInverse_contMDiffOn.mono
    (Set.inter_subset_left : U ⊆ hloc.localInverse.source)
  have hcomp := hray.comp hinvMD
    (fun y hy ↦ hy.2)
  refine ⟨U, hUopen, hyU, ?_⟩
  change ContMDiffOn I (modelWithCornersSelf Real Real) ∞
    ((fun W : E ↦ lRegAction S T (lRegCurve S T x W) 0
      (Real.sqrt tau)) ∘ hloc.localInverse) U
  exact hcomp

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lActBranch_cont
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    ContinuousAt (lActBranch S hS T x Z tau hdom hconj)
      (lExp S T x Z tau) := by
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _hTtau, hb⟩
  have hact := lRayAct_contAt (I := I) S hS T x Z
    (Real.sqrt tau) (Real.sqrt_pos.2 htau) hb
  have hinv := hloc.localInverse_contMDiffAt.continuousAt
  have hinvZ : hloc.localInverse (lExp S T x Z tau) = Z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hcomp := hact.comp_of_eq hinv hinvZ
  change ContinuousAt
    ((fun W : E ↦ lRegAction S T (lRegCurve S T x W) 0
      (Real.sqrt tau)) ∘ hloc.localInverse) (lExp S T x Z tau)
  exact hcomp

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lActBranch_hasMFD
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    HasMFDerivAt I (modelWithCornersSelf Real Real)
      (lActBranch S hS T x Z tau hdom hconj)
      (lExp S T x Z tau)
      (LinearMap.toContinuousLinearMap
        (metricFlatMap (I := I) (S.base.metric (T - tau))
          (lExp S T x Z tau)
          (lVelocity (I := I) (lRegCurve S T x Z)
            (Real.sqrt tau)))) := by
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  let y : M := lExp S T x Z tau
  let z : E := Z
  let rayAct : E → Real := fun W ↦
    lRegAction S T (lRegCurve S T x W) 0 (Real.sqrt tau)
  let alpha : TangentSpace I y →L[Real] Real :=
    (S.base.metric (T - tau)).inner y
      (lVelocity (I := I) (lRegCurve S T x Z) (Real.sqrt tau))
  have hinvZ : hloc.localInverse y = z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hRay : HasFDerivAt rayAct
      (alpha.comp
        (mfderiv (modelWithCornersSelf Real E) I
          (fun W : E ↦ lExp S T x W tau) z)) z := by
    simpa only [rayAct, alpha, y, z] using
      lRayAct_hasFDeriv S hS T x Z hdom
  have hRayM := hRay.hasMFDerivAt
  have hRayInv : HasMFDerivAt (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real Real) rayAct (hloc.localInverse y)
      (alpha.comp
        (mfderiv (modelWithCornersSelf Real E) I
          (fun W : E ↦ lExp S T x W tau) z)) := by
    rw [hinvZ]
    exact hRayM
  have hInv : MDifferentiableAt I (modelWithCornersSelf Real E)
      hloc.localInverse y :=
    hloc.localInverse_mdifferentiableAt (by simp)
  have hdomE := hdom
  change (show E from Z, tau) ∈ lExpPosDom S T x at hdomE
  have hExp : MDifferentiableAt (modelWithCornersSelf Real E) I
      (fun W : E ↦ lExp S T x W tau) z := by
    have hJoint := (lExp_smoothOn S hS T x (z, tau) (by
      exact hdomE)).contMDiffAt
      ((lExpPosDom_open S hS T x).mem_nhds hdomE)
    exact (hJoint.comp z (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
      (by simp)
  have hcomp := hRayInv.comp y hInv.hasMFDerivAt
  have hEq : ((fun W : E ↦ lExp S T x W tau) ∘ hloc.localInverse) =ᶠ[nhds y]
      id := by
    exact Filter.eventuallyEq_of_mem
      (hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source)
      (fun q hq ↦ hloc.localInverse_right_inv hq)
  have hExpInv : MDifferentiableAt (modelWithCornersSelf Real E) I
      (fun W : E ↦ lExp S T x W tau) (hloc.localInverse y) := by
    rw [hinvZ]
    exact hExp
  have hchain := mfderiv_comp y hExpInv hInv
  have hcancel :
      (mfderiv (modelWithCornersSelf Real E) I
        (fun W : E ↦ lExp S T x W tau) z).comp
          (mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y) =
        ContinuousLinearMap.id Real (TangentSpace I y) := by
    have hd := hEq.mfderiv_eq (I := I) (I' := I)
    have hc := hchain.symm.trans hd
    rw [hinvZ, mfderiv_id] at hc
    exact hc
  have hderiv :
      (alpha.comp
        (mfderiv (modelWithCornersSelf Real E) I
          (fun W : E ↦ lExp S T x W tau) z)).comp
        (mfderiv I (modelWithCornersSelf Real E)
          hloc.localInverse y) = alpha := by
    ext Y
    have hright := congrArg
      (fun L : TangentSpace I y →L[Real] TangentSpace I y ↦ L Y) hcancel
    change alpha
        (mfderiv (modelWithCornersSelf Real E) I
          (fun W : E ↦ lExp S T x W tau) z
          (mfderiv I (modelWithCornersSelf Real E)
            hloc.localInverse y Y)) = alpha Y
    exact congrArg alpha hright
  have hcomp' := hcomp.congr_mfderiv hderiv
  have halpha : alpha = LinearMap.toContinuousLinearMap
      (metricFlatMap (I := I) (S.base.metric (T - tau)) y
        (lVelocity (I := I) (lRegCurve S T x Z) (Real.sqrt tau))) := by
    ext V
    rfl
  exact hcomp'.congr_mfderiv halpha

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lActBranch_mfd_at
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) (y : M)
    (hy : y ∈ (lExp_localDiffeo S hS T x Z tau hdom hconj).localInverse.source)
    (hyDom : ((lExp_localDiffeo S hS T x Z tau hdom hconj).localInverse y,
      tau) ∈ lExpPosDom S T x) :
    HasMFDerivAt I (modelWithCornersSelf Real Real)
      (lActBranch S hS T x Z tau hdom hconj) y
      (LinearMap.toContinuousLinearMap
        (metricFlatMap (I := I) (S.base.metric (T - tau)) y
          (lVelocity (I := I)
            (lRegCurve S T x
              ((lExp_localDiffeo S hS T x Z tau hdom hconj).localInverse y))
            (Real.sqrt tau)))) := by
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  let W : E := hloc.localInverse y
  let rayAct : E → Real := fun Q ↦
    lRegAction S T (lRegCurve S T x Q) 0 (Real.sqrt tau)
  let alpha : TangentSpace I (lExp S T x W tau) →L[Real] Real :=
    (S.base.metric (T - tau)).inner (lExp S T x W tau)
      (lVelocity (I := I) (lRegCurve S T x W) (Real.sqrt tau))
  have hright : lExp S T x W tau = y := hloc.localInverse_right_inv hy
  have hRay : HasFDerivAt rayAct
      (alpha.comp (mfderiv (modelWithCornersSelf Real E) I
        (fun Q : E ↦ lExp S T x Q tau) W)) W := by
    simpa only [rayAct, alpha, W] using
      lRayAct_hasFDeriv S hS T x W hyDom
  have hInv : MDifferentiableAt I (modelWithCornersSelf Real E)
      hloc.localInverse y :=
    (hloc.localInverse_contMDiffOn y hy).contMDiffAt
      (hloc.localInverse_open_source.mem_nhds hy) |>.mdifferentiableAt (by simp)
  have hExp : MDifferentiableAt (modelWithCornersSelf Real E) I
      (fun Q : E ↦ lExp S T x Q tau) W := by
    have hJoint := (lExp_smoothOn S hS T x (W, tau) hyDom).contMDiffAt
      ((lExpPosDom_open S hS T x).mem_nhds hyDom)
    exact (hJoint.comp W (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
      (by simp)
  have hcomp := hRay.hasMFDerivAt.comp y hInv.hasMFDerivAt
  have hEq : ((fun Q : E ↦ lExp S T x Q tau) ∘ hloc.localInverse) =ᶠ[nhds y]
      id := by
    exact Filter.eventuallyEq_of_mem
      (hloc.localInverse_open_source.mem_nhds hy)
      (fun q hq ↦ hloc.localInverse_right_inv hq)
  have hchain := mfderiv_comp y hExp hInv
  have hcancel :
      (mfderiv (modelWithCornersSelf Real E) I
        (fun Q : E ↦ lExp S T x Q tau) W).comp
          (mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y) =
        ContinuousLinearMap.id Real (TangentSpace I y) := by
    have hd := hEq.mfderiv_eq (I := I) (I' := I)
    have hc := hchain.symm.trans hd
    change (mfderiv (modelWithCornersSelf Real E) I
      (fun Q : E ↦ lExp S T x Q tau) W).comp
        (mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y) =
      mfderiv I I id y at hc
    rw [mfderiv_id] at hc
    exact hc
  have hderiv :
      (alpha.comp (mfderiv (modelWithCornersSelf Real E) I
        (fun Q : E ↦ lExp S T x Q tau) W)).comp
          (mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y) = alpha := by
    ext V
    have hc := congrArg (fun L : TangentSpace I y →L[Real] TangentSpace I y ↦ L V)
      hcancel
    change alpha
      (mfderiv (modelWithCornersSelf Real E) I
        (fun Q : E ↦ lExp S T x Q tau) W
        (mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y V)) =
      alpha V
    exact congrArg alpha hc
  have hout := hcomp.congr_mfderiv hderiv
  have hout' : HasMFDerivAt I (modelWithCornersSelf Real Real)
      (lActBranch S hS T x Z tau hdom hconj) y alpha := by
    change HasMFDerivAt I (modelWithCornersSelf Real Real)
      (rayAct ∘ hloc.localInverse) y alpha
    exact hout
  apply hout'.congr_mfderiv
  ext V
  change (S.base.metric (T - tau)).inner (lExp S T x W tau)
      (lVelocity (I := I) (lRegCurve S T x W) (Real.sqrt tau)) V =
    (S.base.metric (T - tau)).inner y
      (lVelocity (I := I) (lRegCurve S T x W) (Real.sqrt tau)) V
  rw [hright]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lActBranch_grad_on
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    ∃ U : Set M, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf Real Real) ∞
        (lActBranch S hS T x Z tau hdom hconj) U ∧
      ∀ y ∈ U,
        gradientFun (I := I) (S.base.metric (T - tau))
            (lActBranch S hS T x Z tau hdom hconj) y =
          lVelocity (I := I)
            (lRegCurve S T x
              ((lExp_localDiffeo S hS T x Z tau hdom hconj).localInverse y))
            (Real.sqrt tau) := by
  obtain ⟨U₀, hU₀open, hyU₀, hsmooth⟩ :=
    lActBranch_smooth S hS T x Z tau hdom hconj
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  let P : Set E := {W : E | (W, tau) ∈ lExpPosDom S T x}
  have hPopen : IsOpen P := by
    exact (lExpPosDom_open S hS T x).preimage
      (continuous_id.prodMk continuous_const)
  have hpreOpen : IsOpen
      (hloc.localInverse.source ∩ hloc.localInverse ⁻¹' P) :=
    hloc.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hPopen
  let U : Set M := U₀ ∩
    (hloc.localInverse.source ∩ hloc.localInverse ⁻¹' P)
  have hUopen : IsOpen U := hU₀open.inter hpreOpen
  have hinv : hloc.localInverse (lExp S T x Z tau) = Z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hyU : lExp S T x Z tau ∈ U := by
    refine ⟨hyU₀, hloc.localInverse_mem_source, ?_⟩
    change hloc.localInverse (lExp S T x Z tau) ∈ P
    rw [hinv]
    exact hdom
  refine ⟨U, hUopen, hyU, hsmooth.mono Set.inter_subset_left, ?_⟩
  intro y hy
  apply gradientFun_eq_of_flat
  have hmfd := lActBranch_mfd_at S hS T x Z tau hdom hconj y
    hy.2.1 hy.2.2
  ext V
  have hd := congrArg (fun L : TangentSpace I y →L[Real]
    TangentSpace (modelWithCornersSelf Real Real)
      (lActBranch S hS T x Z tau hdom hconj y) ↦ L V) hmfd.mfderiv
  change mvfderiv (I := I) (lActBranch S hS T x Z tau hdom hconj) y V = _
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
  have hd' := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real)
      (lActBranch S hS T x Z tau hdom hconj y)) hd
  have hcast :
      (LinearMap.toContinuousLinearMap
        (metricFlatMap (I := I) (S.base.metric (T - tau)) y
          (lVelocity (I := I)
            (lRegCurve S T x (hloc.localInverse y)) (Real.sqrt tau)))) V =
        (NormedSpace.fromTangentSpace (𝕜 := Real)
          (lActBranch S hS T x Z tau hdom hconj y)).symm
            (metricFlatEquiv (I := I) (S.base.metric (T - tau)) y
              (lVelocity (I := I)
                (lRegCurve S T x (hloc.localInverse y)) (Real.sqrt tau)) V) := by
    rfl
  calc
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real)
        (lActBranch S hS T x Z tau hdom hconj y))
          ((LinearMap.toContinuousLinearMap
            (metricFlatMap (I := I) (S.base.metric (T - tau)) y
              (lVelocity (I := I)
                (lRegCurve S T x (hloc.localInverse y)) (Real.sqrt tau)))) V) := hd'
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real)
        (lActBranch S hS T x Z tau hdom hconj y))
          ((NormedSpace.fromTangentSpace (𝕜 := Real)
            (lActBranch S hS T x Z tau hdom hconj y)).symm
              (metricFlatEquiv (I := I) (S.base.metric (T - tau)) y
                (lVelocity (I := I)
                  (lRegCurve S T x (hloc.localInverse y)) (Real.sqrt tau)) V)) :=
      congrArg (NormedSpace.fromTangentSpace (𝕜 := Real)
        (lActBranch S hS T x Z tau hdom hconj y)) hcast
    _ = _ := ContinuousLinearEquiv.apply_symm_apply _ _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lEndVel_cov
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) (Y : TangentSpace I
      (lExp S T x Z tau)) :
    let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
    let W := mfderiv I (modelWithCornersSelf Real E) hloc.localInverse
      (lExp S T x Z tau) Y
    (LeviCivita (I := I) (S.base.metric (T - tau))).toFun
        (fun y ↦ gradientFun (I := I) (S.base.metric (T - tau))
          (lActBranch S hS T x Z tau hdom hconj) y)
        (lExp S T x Z tau) Y =
      covDerivAlong (I := I) (S.base.metric (T - tau))
        (lRegCurve S T x Z) (lRegJacobiField S T x Z W)
        (Real.sqrt tau) := by
  dsimp only
  let b : Real := Real.sqrt tau
  let y : M := lExp S T x Z tau
  let g := S.base.metric (T - tau)
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  let W : E := mfderiv I (modelWithCornersSelf Real E)
    hloc.localInverse y Y
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _htime, hb⟩
  have hb0 : 0 < b := Real.sqrt_pos.2 htau
  obtain ⟨U₀, hU₀open, hyU₀, hsmooth, hgrad⟩ :=
    lActBranch_grad_on S hS T x Z tau hdom hconj
  obtain ⟨J₀, hJopen, hJconn, h0J, hbJ, hchosen⟩ :=
    lRegChosen_spec S T x Z hb
  obtain ⟨V₀, hVopen, hZV, K, hKopen, hKconn, h0K, hbK,
      alpha, halpha, hcurves⟩ :=
    lRegFamily_extend S hS T hJopen hJconn h0J hbJ hchosen
  have hZVE := hZV
  change (show E from Z) ∈ V₀ at hZVE
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrhoK⟩ :=
    exists_open_clamp hKopen hKconn h0K hbK hb0
  let U : Set M := U₀ ∩
    (hloc.localInverse.source ∩ hloc.localInverse ⁻¹' V₀)
  have hpreOpen : IsOpen
      (hloc.localInverse.source ∩ hloc.localInverse ⁻¹' V₀) :=
    hloc.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hVopen
  have hUopen : IsOpen U := hU₀open.inter hpreOpen
  have hinvZ : hloc.localInverse y = Z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hyU : y ∈ U := by
    refine ⟨hyU₀, hloc.localInverse_mem_source, ?_⟩
    change hloc.localInverse y ∈ V₀
    rw [hinvZ]
    exact hZV
  obtain ⟨eta, heta, hetaU, heta0, hetaVel⟩ :=
    exists_smooth_curve y Y U hUopen hyU
  let zeta : Real → E := fun s ↦ hloc.localInverse (eta s)
  have hzeta : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real E) ∞ zeta := by
    rw [← contMDiffOn_univ]
    exact hloc.localInverse_contMDiffOn.comp heta.contMDiffOn
      (fun s _hs ↦ (hetaU s).2.1)
  have hzetaV : ∀ s : Real, zeta s ∈ V₀ :=
    fun s ↦ (hetaU s).2.2
  have hzeta0 : zeta 0 = Z := by
    dsimp only [zeta]
    rw [heta0]
    exact hinvZ
  have hzetaVel : mfderiv (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real E) zeta 0 (1 : Real) = W := by
    have hInv0 : MDifferentiableAt I (modelWithCornersSelf Real E)
        hloc.localInverse (eta 0) := by
      simpa only [heta0, y] using
        hloc.localInverse_contMDiffAt.mdifferentiableAt (by simp)
    have hc := mfderiv_comp 0 hInv0
      (heta.contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real E) (hloc.localInverse ∘ eta) 0 1 = W
    rw [hc]
    change mfderiv I (modelWithCornersSelf Real E) hloc.localInverse
        (eta 0) (mfderiv (modelWithCornersSelf Real Real) I eta 0 1) = W
    rw [heta0]
    change mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y
        (mfderiv (modelWithCornersSelf Real Real) I eta 0 1) =
      mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y Y
    exact congrArg
      (mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y) hetaVel
  have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  let F : Real → Real → M := fun s t ↦ alpha (zeta s, rho t)
  have hpair : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      (fun p : Real × Real ↦ (zeta p.1, rho p.2)) :=
    (hzeta.comp contMDiff_fst).prodMk (hrhoM.comp contMDiff_snd)
  have hF : IsSmoothVariation (I := I) F := by
    unfold IsSmoothVariation
    rw [← contMDiffOn_univ]
    change ContMDiffOn
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real)) I (8 : Nat)
      (alpha ∘ fun p : Real × Real ↦ (zeta p.1, rho p.2)) Set.univ
    exact (halpha.of_le (by
      change (↑(8 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)).comp
      (hpair.of_le (by
        change (↑(8 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).contMDiffOn
      (fun p _hp ↦ ⟨hzetaV p.1, hrhoK p.2⟩)
  have h0ad : (0 : Real) ∈ Set.Icc a d :=
    ⟨ha0.le, (hb0.trans hbd).le⟩
  have hbad : b ∈ Set.Icc a d :=
    ⟨(ha0.trans hb0).le, hbd.le⟩
  have hrho0 : rho 0 = 0 := hrho_id h0ad
  have hrhob : rho b = b := hrho_id hbad
  have hcanon : ∀ s : Real, Set.EqOn
      (lRegCurve S T x (zeta s))
      (fun t : Real ↦ alpha (zeta s, t)) K := by
    intro s
    exact lRegCurve_eqOn S hS T hKopen hKconn h0K
      (hcurves (zeta s) (hzetaV s))
  have hend : (fun s : Real ↦ F s b) = eta := by
    funext s
    have hright := hloc.localInverse_right_inv (hetaU s).2.1
    change alpha (zeta s, rho b) = eta s
    rw [hrhob]
    calc
      alpha (zeta s, b) = lRegCurve S T x (zeta s) b :=
        (hcanon s hbK).symm
      _ = eta s := by
        simpa only [lExp, Real.sq_sqrt htau.le, zeta, b] using hright
  let Vterm : ∀ s, TangentSpace I (eta s) := fun s ↦
    lVelocity (I := I) (lRegCurve S T x (zeta s)) b
  have hgradEv :
      (fun s ↦ gradientFun (I := I) g
        (lActBranch S hS T x Z tau hdom hconj) (eta s)) =ᶠ[nhds 0]
        Vterm := by
    exact Filter.Eventually.of_forall fun s ↦ by
      change (show E from gradientFun (I := I) g
        (lActBranch S hS T x Z tau hdom hconj) (eta s)) =
        (show E from lVelocity (I := I)
          (lRegCurve S T x (zeta s)) b)
      have hs := hgrad (eta s) (hetaU s).1
      change (show E from gradientFun (I := I) g
        (lActBranch S hS T x Z tau hdom hconj) (eta s)) =
        (show E from lVelocity (I := I)
          (lRegCurve S T x (hloc.localInverse (eta s))) (Real.sqrt tau)) at hs
      simpa only [zeta, b] using hs
  have hcovGrad := covDerivAlong_congr_of_eventuallyEq
    (I := I) g eta hgradEv
  obtain ⟨f₀, hf₀, hf₀eq⟩ :=
    DifferentialGeometry.exists_smooth_germ (I := I) hU₀open hyU₀ hsmooth
  have hgradEq :
      (T% fun q ↦ gradientFun (I := I) g f₀ q) =ᶠ[nhds y]
        (T% fun q ↦ gradientFun (I := I) g
          (lActBranch S hS T x Z tau hdom hconj) q) := by
    filter_upwards [hf₀eq.eventuallyEq_nhds] with q hq
    change TotalSpace.mk' E q (gradientFun (I := I) g f₀ q) =
      TotalSpace.mk' E q
        (gradientFun (I := I) g
          (lActBranch S hS T x Z tau hdom hconj) q)
    unfold gradientFun
    unfold mvfderiv
    rw [hq.mfderiv_eq, hq.eq_of_nhds]
  have hgradAt : MDifferentiableAt I
      (I.prod (modelWithCornersSelf Real E))
      (fun q ↦ TotalSpace.mk' E q
        (gradientFun (I := I) g
          (lActBranch S hS T x Z tau hdom hconj) q)) y := by
    have hs := gradientFun_smooth (I := I) g hf₀
    have hsAt := hs.contMDiffAt.congr_of_eventuallyEq hgradEq.symm
    exact hsAt.mdifferentiableAt (by simp)
  have hchain := covDerivAlong_restrict_eq_leviCivita
    (I := I) g eta
      (fun q ↦ gradientFun (I := I) g
        (lActBranch S hS T x Z tau hdom hconj) q) 0 heta
      (by simpa only [heta0] using hgradAt)
  have hchain' :
      covDerivAlong (I := I) g eta
          (fun s ↦ gradientFun (I := I) g
            (lActBranch S hS T x Z tau hdom hconj) (eta s)) 0 =
        (LeviCivita (I := I) g).toFun
          (fun q ↦ gradientFun (I := I) g
            (lActBranch S hS T x Z tau hdom hconj) q) y Y := by
    rw [heta0] at hchain
    exact hchain.trans (congrArg
      (fun Q : TangentSpace I y ↦
        (LeviCivita (I := I) g).toFun
          (fun q ↦ gradientFun (I := I) g
            (lActBranch S hS T x Z tau hdom hconj) q) y Q) hetaVel)
  have hcomm := commute_ds_dt_intrinsic (I := I) g F hF b
  have hbase : (fun t : Real ↦ F 0 t) =ᶠ[nhds b]
      lRegCurve S T x Z := by
    filter_upwards [isOpen_Ioo.mem_nhds
      ⟨ha0.trans hb0, hbd⟩] with t ht
    change alpha (zeta 0, rho t) = lRegCurve S T x Z t
    have hrt : rho t = t := hrho_id ⟨ht.1.le, ht.2.le⟩
    have htK : t ∈ K := by simpa only [hrt] using hrhoK t
    rw [hrt]
    have hc := hcanon 0 htK
    simpa only [hzeta0] using hc.symm
  have hfield : (fun t : Real ↦
      mfderiv (modelWithCornersSelf Real Real) I (fun s ↦ F s t) 0
        (1 : Real)) =ᶠ[nhds b]
      lRegJacobiField S T x Z W := by
    filter_upwards [isOpen_Ioo.mem_nhds
      ⟨ha0.trans hb0, hbd⟩] with t ht
    have hrt : rho t = t := hrho_id ⟨ht.1.le, ht.2.le⟩
    have htK : t ∈ K := by simpa only [hrt] using hrhoK t
    let z₀ : E := Z
    have hparamEq : (fun Q : E ↦ alpha (Q, t)) =ᶠ[nhds z₀]
        (fun Q : E ↦ lRegCurve S T x Q t) := by
      filter_upwards [hVopen.mem_nhds (by simpa only [z₀] using hZVE)] with Q hQ
      exact (lRegCurve_eqOn S hS T hKopen hKconn h0K
        (hcurves Q hQ) htK).symm
    have hαdiff : MDifferentiableAt (modelWithCornersSelf Real E) I
        (fun Q : E ↦ alpha (Q, t)) z₀ := by
      have hp : (z₀, t) ∈ V₀ ×ˢ K :=
        ⟨by simpa only [z₀] using hZVE, htK⟩
      have hj := (halpha (z₀, t) hp).contMDiffAt
        ((hVopen.prod hKopen).mem_nhds hp)
      exact (hj.comp z₀ (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
        (by simp)
    have hαdiff0 : MDifferentiableAt (modelWithCornersSelf Real E) I
        (fun Q : E ↦ alpha (Q, t)) (zeta 0) := by
      simpa only [hzeta0, z₀] using hαdiff
    have hzcomp := mfderiv_comp 0 hαdiff0
      (hzeta.contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv (modelWithCornersSelf Real Real) I
      (fun s ↦ alpha (zeta s, rho t)) 0 (1 : Real) = _
    rw [hrt]
    change mfderiv (modelWithCornersSelf Real Real) I
      ((fun Q : E ↦ alpha (Q, t)) ∘ zeta) 0 (1 : Real) = _
    rw [hzcomp, hzeta0]
    change mfderiv (modelWithCornersSelf Real E) I
      (fun Q : E ↦ alpha (Q, t)) Z
        (mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real E) zeta 0 1) = _
    calc
      _ = mfderiv (modelWithCornersSelf Real E) I
          (fun Q : E ↦ alpha (Q, t)) Z W := congrArg _ hzetaVel
      _ = _ := congrArg (fun L ↦ L W)
        (hparamEq.mfderiv_eq
          (I := modelWithCornersSelf Real E) (I' := I))
  have hcomm' : covDerivAlong (I := I) g eta Vterm 0 =
      covDerivAlong (I := I) g (lRegCurve S T x Z)
        (lRegJacobiField S T x Z W) b := by
    have hendVel : (fun s : Real ↦
        lVelocity (I := I) (fun t ↦ F s t) b) = Vterm := by
      funext s
      have heq : (fun t ↦ F s t) =ᶠ[nhds b]
          lRegCurve S T x (zeta s) := by
        filter_upwards [isOpen_Ioo.mem_nhds
          ⟨ha0.trans hb0, hbd⟩] with t ht
        change alpha (zeta s, rho t) = lRegCurve S T x (zeta s) t
        have hrt : rho t = t := hrho_id ⟨ht.1.le, ht.2.le⟩
        have htK : t ∈ K := by simpa only [hrt] using hrhoK t
        rw [hrt]
        exact (hcanon s htK).symm
      unfold lVelocity
      exact congrArg (fun L ↦ L (1 : Real))
        (heq.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I))
    change covDerivAlong (I := I) g (fun s ↦ F s b)
        (fun s ↦ lVelocity (I := I) (fun t ↦ F s t) b) 0 = _ at hcomm
    rw [hend, hendVel] at hcomm
    have hc := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) g _ _ hbase hfield
    exact hcomm.trans (by simpa using hc)
  exact hchain'.symm.trans (hcovGrad.trans hcomm')

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lActBranch_hess
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau)
    (Y V : TangentSpace I (lExp S T x Z tau)) :
    let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
    let W := mfderiv I (modelWithCornersSelf Real E) hloc.localInverse
      (lExp S T x Z tau) Y
    hessFun (I := I) (S.base.metric (T - tau))
        (lActBranch S hS T x Z tau hdom hconj)
        (lExp S T x Z tau) Y V =
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau))
          (lRegCurve S T x Z) (lRegJacobiField S T x Z W)
          (Real.sqrt tau)) V := by
  dsimp only
  obtain ⟨U, hUopen, hyU, hsmooth, _hgrad⟩ :=
    lActBranch_grad_on S hS T x Z tau hdom hconj
  have hhess := hessFun_eq_cov_local (I := I)
    (S.base.metric (T - tau)) hUopen hsmooth hyU Y V
  have hcov := lEndVel_cov S hS T x Z tau hdom hconj Y
  simp only [gradient_eq_gradFun] at hcov
  exact hhess.trans (congrArg
    (fun Q : TangentSpace I (lExp S T x Z tau) ↦
      (S.base.metric (T - tau)).inner (lExp S T x Z tau) Q V) hcov)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lActBranch_upper
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    (fun y ↦ lCost S T x y tau) ≤ᶠ[nhds (lExp S T x Z tau)]
      lActBranch S hS T x Z tau hdom hconj := by
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  let z : M := lExp S T x Z tau
  let U : Set E := {W : E | (W, tau) ∈ lExpPosDom S T x}
  have hUopen : IsOpen U := by
    have hpair : Continuous (fun W : E ↦ (W, tau)) :=
      continuous_id.prodMk continuous_const
    exact (lExpPosDom_open S hS T x).preimage hpair
  have hZU : Z ∈ U := hdom
  have hinvZ : hloc.localInverse z = Z := by
    exact hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hsrc : hloc.localInverse.source ∈ nhds z :=
    hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source
  have hpre : hloc.localInverse ⁻¹' U ∈ nhds z := by
    apply hloc.localInverse_contMDiffAt.continuousAt.preimage_mem_nhds
    rw [hinvZ]
    exact hUopen.mem_nhds hZU
  filter_upwards [hsrc, hpre] with y hySrc hyU
  let W : E := hloc.localInverse y
  have hWpos : (W, tau) ∈ lExpPosDom S T x := hyU
  rcases (mem_lExpPosDom S T x W tau).1 hWpos with
    ⟨htau, _hTtau, hWdom⟩
  have hright : lExp S T x W tau = y :=
    hloc.localInverse_right_inv hySrc
  have hleft : hloc.localInverse (lExp S T x W tau) = W := by
    apply hloc.localInverse_left_inv
    exact hloc.localInverse.map_source hySrc
  have hle := lCost_le_ray (I := I) S hS T x W (Real.sqrt tau)
    (Real.sqrt_pos.2 htau) hWdom
  have hle' : lCost S T x (lExp S T x W tau) tau ≤
      lRegAction S T (lRegCurve S T x W) 0 (Real.sqrt tau) := by
    simpa only [lExp, Real.sq_sqrt htau.le] using hle
  rw [← hright]
  change lCost S T x (lExp S T x W tau) tau ≤
    lRegAction S T
      (lRegCurve S T x (hloc.localInverse (lExp S T x W tau)))
      0 (Real.sqrt tau)
  rw [hleft]
  exact hle'

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_branch_deriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    ∃ U : Set M, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ∀ (eta : Real → M),
        ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat) eta →
        (∀ u : Real, eta u ∈ U) →
        eta 0 = lExp S T x Z tau →
        HasDerivAt
          (fun u : Real ↦
            lActBranch S hS T x Z tau hdom hconj (eta u))
          ((S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (lVelocity (I := I) eta 0)
            (lVelocity (I := I) (lRegCurve S T x Z)
              (Real.sqrt tau))) 0 := by
  let b : Real := Real.sqrt tau
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _hTtau, hb⟩
  have hb0 : 0 < b := Real.sqrt_pos.2 htau
  obtain ⟨J, hJopen, hJconn, h0J, hbJ, hchosen⟩ :=
    lRegChosen_spec S T x Z hb
  obtain ⟨V, hVopen, hZV, K, hKopen, hKconn, h0K, hbK,
      alpha, halpha, hcurves⟩ :=
    lRegFamily_extend S hS T hJopen hJconn h0J hbJ hchosen
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrhoK⟩ :=
    exists_open_clamp hKopen hKconn h0K hbK hb0
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  let U : Set M :=
    hloc.localInverse.source ∩ hloc.localInverse ⁻¹' V
  have hUopen : IsOpen U := by
    exact hloc.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hVopen
  have hinvZ : hloc.localInverse (lExp S T x Z tau) = Z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hyU : lExp S T x Z tau ∈ U := by
    refine ⟨hloc.localInverse_mem_source, ?_⟩
    change hloc.localInverse (lExp S T x Z tau) ∈ V
    rw [hinvZ]
    exact hZV
  refine ⟨U, hUopen, hyU, ?_⟩
  intro eta heta hetaU heta0
  have h8inf : (↑(8 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat) :=
    WithTop.coe_le_coe.mpr le_top
  let zeta : Real → E := fun u ↦ hloc.localInverse (eta u)
  have hzeta : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real E) (8 : Nat) zeta := by
    rw [← contMDiffOn_univ]
    exact (hloc.localInverse_contMDiffOn.of_le h8inf).comp heta.contMDiffOn
      (fun u _hu ↦ (hetaU u).1)
  have hzetaV : ∀ u : Real, zeta u ∈ V :=
    fun u ↦ (hetaU u).2
  have hzeta0 : zeta 0 = Z := by
    dsimp only [zeta]
    rw [heta0]
    exact hinvZ
  have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho := by
    exact contMDiff_iff_contDiff.mpr hrho
  let f : Real → Real → M :=
    fun u s ↦ alpha (zeta u, rho s)
  have hpair : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) (8 : Nat)
      (fun p : Real × Real ↦ (zeta p.1, rho p.2)) := by
    exact (hzeta.comp contMDiff_fst).prodMk
      ((hrhoM.of_le h8inf).comp contMDiff_snd)
  have hpairVK : ∀ p : Real × Real,
      (zeta p.1, rho p.2) ∈ V ×ˢ K := by
    exact fun p ↦ ⟨hzetaV p.1, hrhoK p.2⟩
  have hf : IsSmoothVariation (I := I) f := by
    unfold IsSmoothVariation
    rw [← contMDiffOn_univ]
    change ContMDiffOn
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real)) I (8 : Nat)
      (alpha ∘ fun p : Real × Real ↦ (zeta p.1, rho p.2)) Set.univ
    exact (halpha.of_le h8inf).comp hpair.contMDiffOn
      (fun p _hp ↦ hpairVK p)
  have h0ad : (0 : Real) ∈ Set.Icc a d :=
    ⟨ha0.le, (hb0.trans hbd).le⟩
  have hbad : b ∈ Set.Icc a d :=
    ⟨(ha0.trans hb0).le, hbd.le⟩
  have hrho0 : rho 0 = 0 := hrho_id h0ad
  have hrhob : rho b = b := hrho_id hbad
  have hf0 : ∀ u : Real, f u 0 = x := by
    intro u
    change alpha (zeta u, rho 0) = x
    rw [hrho0]
    exact (hcurves (zeta u) (hzetaV u)).1
  have hfix : ∀ u : Real, f u 0 = f 0 0 := by
    intro u
    rw [hf0 u, hf0 0]
  have hseg : Set.Icc (0 : Real) b ⊆ K :=
    by
      simpa only [b, Set.uIcc_of_le hb0.le] using
        hKconn.ordConnected.uIcc_subset h0K hbK
  have hcenter : IsLRegCurveOn S T (f 0)
      (Set.uIcc (0 : Real) b) x Z := by
    refine ⟨hf0 0, ?_, ?_⟩
    · have heq : (f 0) =ᶠ[nhds (0 : Real)]
          (fun s : Real ↦ alpha (Z, s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨ha0, hb0.trans hbd⟩] with s hs
        change alpha (zeta 0, rho s) = alpha (Z, s)
        rw [hzeta0]
        simpa only [id_eq] using congrArg (fun r ↦ alpha (Z, r))
          (hrho_id ⟨hs.1.le, hs.2.le⟩)
      unfold lVelocity
      rw [heq.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I)]
      exact (hcurves Z hZV).2.1
    · intro s hs
      have hsI : s ∈ Set.Icc (0 : Real) b := by
        simpa only [Set.uIcc_of_le hb0.le] using hs
      have hsad : s ∈ Set.Ioo a d :=
        ⟨ha0.trans_le hsI.1, hsI.2.trans_lt hbd⟩
      have heq : (f 0) =ᶠ[nhds s]
          (fun r : Real ↦ alpha (Z, r)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hsad] with r hr
        change alpha (zeta 0, rho r) = alpha (Z, r)
        rw [hzeta0]
        simpa only [id_eq] using congrArg (fun q ↦ alpha (Z, q))
          (hrho_id ⟨hr.1.le, hr.2.le⟩)
      exact lRegData_congr S T s heq
        ((hcurves Z hZV).2.2 s (hseg hsI))
  have hcanon : ∀ u : Real, Set.EqOn
      (lRegCurve S T x (zeta u))
      (fun s : Real ↦ alpha (zeta u, s)) K := by
    intro u
    exact lRegCurve_eqOn S hS T hKopen hKconn h0K
      (hcurves (zeta u) (hzetaV u))
  have hfu : ∀ u : Real, Set.EqOn (f u)
      (lRegCurve S T x (zeta u)) (Set.Icc (0 : Real) b) := by
    intro u s hs
    change alpha (zeta u, rho s) = lRegCurve S T x (zeta u) s
    have hrhos : rho s = s := by
      simpa only [id_eq] using
        hrho_id ⟨(ha0.trans_le hs.1).le, hs.2.trans hbd.le⟩
    rw [hrhos]
    exact (hcanon u (hseg hs)).symm
  have hact : (fun u : Real ↦ lRegAction S T (f u) 0 b) =
      fun u : Real ↦
        lActBranch S hS T x Z tau hdom hconj (eta u) := by
    funext u
    have heq := lRegAction_congr (I := I) S T (f u)
      (lRegCurve S T x (zeta u)) 0 b (by
        intro s hs
        apply hfu u
        simpa only [Set.uIcc_of_le hb0.le] using
          Set.uIoo_subset_uIcc_self hs)
    simpa only [lActBranch, hloc, zeta, b] using heq
  have hend : (fun u : Real ↦ f u b) = eta := by
    funext u
    have hright := hloc.localInverse_right_inv (hetaU u).1
    change alpha (zeta u, rho b) = eta u
    rw [hrhob]
    calc
      alpha (zeta u, b) = lRegCurve S T x (zeta u) b :=
        (hcanon u (by simpa only [b] using hbK)).symm
      _ = eta u := by
        simpa only [lExp, Real.sq_sqrt htau.le, zeta, b] using hright
  have hcentVel : lVelocity (I := I) (f 0) b =
      lVelocity (I := I) (lRegCurve S T x Z) b := by
    have heq : (f 0) =ᶠ[nhds b] lRegCurve S T x Z := by
      filter_upwards [isOpen_Ioo.mem_nhds
        ⟨ha0.trans hb0, hbd⟩] with s hs
      change alpha (zeta 0, rho s) = lRegCurve S T x Z s
      have hrhos : rho s = s := by
        simpa only [id_eq] using hrho_id ⟨hs.1.le, hs.2.le⟩
      have hsK : s ∈ K := by
        rw [← hrhos]
        exact hrhoK s
      rw [hzeta0, hrhos]
      have hc := hcanon 0 hsK
      rw [hzeta0] at hc
      exact hc.symm
    unfold lVelocity
    exact congrArg (fun L ↦ L (1 : Real))
      (heq.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I))
  have hfirst := lRegAction_bdry S hS T f hf b x Z hcenter hfix
  rw [hact] at hfirst
  rw [show T - b ^ 2 = T - tau by simp only [b, Real.sq_sqrt htau.le],
    show f 0 b = lExp S T x Z tau by
      rw [show f 0 b = eta 0 by exact congrFun hend 0, heta0],
    show lVelocity (I := I) (fun u : Real ↦ f u b) 0 =
        lVelocity (I := I) eta 0 by rw [hend],
    hcentVel] at hfirst
  exact hfirst

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lActBranch_touch
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    lActBranch S hS T x Z tau
        ((mem_lMinDomain S T x Z tau).1 hmin).1 hconj
        (lExp S T x Z tau) =
      lCost S T x (lExp S T x Z tau) tau := by
  let hdom := ((mem_lMinDomain S T x Z tau).1 hmin).1
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  have hinv : hloc.localInverse (lExp S T x Z tau) = Z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have htau : 0 ≤ tau := (lMinDomain_pos S T x Z tau hmin).le
  have hlen :
      lLength S T (fun r : Real ↦ lExp S T x Z r) 0 tau =
        lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau) := by
    change lLength S T (sqrtReparam (lRegCurve S T x Z)) 0 tau =
      lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau)
    exact lLength_sqrt (I := I) S T (lRegCurve S T x Z) tau htau
  change lRegAction S T
      (lRegCurve S T x (hloc.localInverse (lExp S T x Z tau)))
        0 (Real.sqrt tau) = _
  rw [hinv, ← hlen]
  exact ((mem_lMinDomain S T x Z tau).1 hmin).2

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lCost_nondiff_two
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z W : TangentSpace I x} {tau : Real}
    (hZmin : (Z, tau) ∈ lMinDomain S T x)
    (hWmin : (W, tau) ∈ lMinDomain S T x)
    (hZconj : ¬ IsLConj S T x Z tau)
    (hWconj : ¬ IsLConj S T x W tau)
    (hZW : Z ≠ W)
    (hpos : lExp S T x Z tau = lExp S T x W tau) :
    ¬ MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun y : M ↦ lCost S T x y tau) (lExp S T x Z tau) := by
  let hZdom := ((mem_lMinDomain S T x Z tau).1 hZmin).1
  let hWdom := ((mem_lMinDomain S T x W tau).1 hWmin).1
  let b : Real := Real.sqrt tau
  let y : M := lExp S T x Z tau
  let vZ : TangentSpace I y :=
    lVelocity (I := I) (lRegCurve S T x Z) b
  let vW : TangentSpace I y :=
    lVelocity (I := I) (lRegCurve S T x W) b
  let V : TangentSpace I y := vZ - vW
  obtain ⟨UZ, hUZopen, hyUZ, hZder⟩ :=
    exists_branch_deriv S hS T x Z tau hZdom hZconj
  obtain ⟨UW, hUWopen, hyWU, hWder⟩ :=
    exists_branch_deriv S hS T x W tau hWdom hWconj
  have hyUW : y ∈ UW := by
    dsimp only [y]
    rw [hpos]
    exact hyWU
  obtain ⟨eta, heta, hetaU, heta0, hetaVel⟩ :=
    exists_smooth_curve y V (UZ ∩ UW) (hUZopen.inter hUWopen)
      ⟨by simpa only [y] using hyUZ, hyUW⟩
  have hetaZ : ∀ u : Real, eta u ∈ UZ :=
    fun u ↦ (hetaU u).1
  have hetaW : ∀ u : Real, eta u ∈ UW :=
    fun u ↦ (hetaU u).2
  have heta0Z : eta 0 = lExp S T x Z tau := by
    simpa only [y] using heta0
  have heta0W : eta 0 = lExp S T x W tau := heta0Z.trans hpos
  have hetaVel' : lVelocity (I := I) eta 0 = V := by
    simpa only [lVelocity] using hetaVel
  let F : Real → Real := fun u ↦
    lActBranch S hS T x Z tau hZdom hZconj (eta u)
  let G : Real → Real := fun u ↦
    lActBranch S hS T x W tau hWdom hWconj (eta u)
  let c : Real → Real := fun u ↦ lCost S T x (eta u) tau
  have heta8 : ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat) eta :=
    heta.of_le (by
      change (↑(8 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hFd : HasDerivAt F
      ((S.base.metric (T - tau)).inner y V vZ) 0 := by
    simpa only [F, y, b, vZ, hetaVel'] using
      hZder eta heta8 hetaZ heta0Z
  have hGd : HasDerivAt G
      ((S.base.metric (T - tau)).inner y V vW) 0 := by
    have hraw := hWder eta heta8 hetaW heta0W
    rw [← hpos] at hraw
    simpa only [G, y, b, vW, hetaVel'] using hraw
  have hZup : c ≤ᶠ[nhds (0 : Real)] F := by
    have htend : Tendsto eta (nhds (0 : Real)) (nhds y) := by
      have hcont : ContinuousAt eta (0 : Real) :=
        heta.continuous.continuousAt
      change Tendsto eta (nhds (0 : Real)) (nhds (eta 0)) at hcont
      rw [heta0] at hcont
      exact hcont
    have hup := htend.eventually
      (lActBranch_upper S hS T x Z tau hZdom hZconj)
    change ∀ᶠ u in nhds (0 : Real),
      lCost S T x (eta u) tau ≤
        lActBranch S hS T x Z tau hZdom hZconj (eta u)
    exact hup
  have hWup : c ≤ᶠ[nhds (0 : Real)] G := by
    have htend : Tendsto eta (nhds (0 : Real))
        (nhds (lExp S T x W tau)) := by
      have hcont : ContinuousAt eta (0 : Real) :=
        heta.continuous.continuousAt
      change Tendsto eta (nhds (0 : Real)) (nhds (eta 0)) at hcont
      rw [heta0W] at hcont
      exact hcont
    have hup := htend.eventually
      (lActBranch_upper S hS T x W tau hWdom hWconj)
    change ∀ᶠ u in nhds (0 : Real),
      lCost S T x (eta u) tau ≤
        lActBranch S hS T x W tau hWdom hWconj (eta u)
    exact hup
  have hFtouch : F 0 = c 0 := by
    simpa only [F, c, heta0Z] using
      lActBranch_touch S hS T x Z tau hZmin hZconj
  have hGtouch : G 0 = c 0 := by
    simpa only [G, c, heta0W] using
      lActBranch_touch S hS T x W tau hWmin hWconj
  rcases (mem_lExpPosDom S T x Z tau).1 hZdom with
    ⟨htau, _hZtau, hZb⟩
  rcases (mem_lExpPosDom S T x W tau).1 hWdom with
    ⟨_hWtau, _hWtau0, hWb⟩
  have hvelNe : vZ ≠ vW := by
    apply lRay_end_vel_ne S hS T x hZb hWb hZW
    simpa only [vZ, vW, y, b, lExp] using hpos
  have hVne : V ≠ 0 := sub_ne_zero.mpr hvelNe
  have hvalNe :
      (S.base.metric (T - tau)).inner y V vZ ≠
        (S.base.metric (T - tau)).inner y V vW := by
    intro heq
    have hzero : (S.base.metric (T - tau)).inner y V V = 0 := by
      dsimp only [V]
      rw [((S.base.metric (T - tau)).inner y (vZ - vW)).map_sub,
        heq, sub_self]
    exact (ne_of_gt ((S.base.metric (T - tau)).pos y V hVne)) hzero
  have hderNe : fderiv Real F 0 ≠ fderiv Real G 0 := by
    intro heq
    have happ := congrArg (fun L : Real →L[Real] Real ↦ L (1 : Real)) heq
    rw [hFd.hasFDerivAt.fderiv, hGd.hasFDerivAt.fderiv] at happ
    exact hvalNe (by simpa using happ)
  have hcnot : ¬ DifferentiableAt Real c 0 :=
    not_diff_two_upper hFd.differentiableAt hGd.differentiableAt
      hZup hWup hFtouch hGtouch hderNe
  intro hcost
  have hetaMd : MDifferentiableAt (modelWithCornersSelf Real Real) I eta 0 :=
    heta.mdifferentiableAt (by norm_num)
  have hcomp : MDifferentiableAt (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real)
      ((fun q : M ↦ lCost S T x q tau) ∘ eta) 0 :=
    MDifferentiableAt.comp_of_eq (x := (0 : Real)) (f := eta)
      hcost hetaMd heta0Z
  apply hcnot
  exact mdifferentiableAt_iff_differentiableAt.mp
    (by
      change MDifferentiableAt (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real)
        (fun u : Real ↦ lCost S T x (eta u) tau) 0 at hcomp
      exact hcomp)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
