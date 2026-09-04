import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set Topology
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

private theorem slice_inj_small
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (Phi : E × Real → E) (K V : Set E) (S : Set Real)
    (hKcpt : IsCompact K) (hKconv : Convex Real K)
    (hV : IsOpen V) (hKV : K ⊆ V)
    (hS : IsOpen S) (h0S : (0 : Real) ∈ S)
    (hPhi : ContDiffOn Real 2 Phi (V ×ˢ S))
    (hzero : ∀ z ∈ V, Phi (z, 0) = 0)
    (hlaunch : ∀ z ∈ V,
      (fderiv Real Phi (z, 0)) ((0 : E), (1 : Real)) = z) :
    ∃ eps : Real, 0 < eps ∧ ∀ b : Real, 0 < b → b < eps →
      Set.InjOn (fun z : E ↦ Phi (z, b)) K := by
  let G : E × Real → E := fun p ↦
    (fderiv Real Phi p) ((0 : E), (1 : Real))
  let B : E × Real → E →L[Real] E := fun p ↦
    fderiv Real (fun z : E ↦ G (z, p.2)) p.1
  have hVS : IsOpen (V ×ˢ S) := hV.prod hS
  have hG : ContDiffOn Real 1 G (V ×ˢ S) := by
    exact (hPhi.fderiv_of_isOpen hVS (by norm_num)).clm_apply contDiffOn_const
  have hB : ContinuousOn B (V ×ˢ S) := by
    have hBc : ContDiffOn Real 0 B (V ×ˢ S) := by
      rw [hVS.contDiffOn_iff] at hG ⊢
      intro p hp
      apply ContDiffAt.fderiv (n := (1 : WithTop ℕ∞))
          (m := (0 : WithTop ℕ∞))
      · exact (hG hp).comp _
          (by
            fun_prop : ContDiffAt Real 1
              (fun w : (E × Real) × E ↦ (w.2, w.1.2)) (p, p.1))
      · fun_prop
      · norm_num
    exact hBc.continuousOn
  have hB0 : ∀ z ∈ V, B (z, 0) = ContinuousLinearMap.id Real E := by
    intro z hz
    have heq : (fun y : E ↦ G (y, 0)) =ᶠ[𝓝 z] id := by
      filter_upwards [hV.mem_nhds hz] with y hy
      exact hlaunch y hy
    have hf := Filter.EventuallyEq.fderiv_eq (𝕜 := Real) heq
    simpa only [B, fderiv_id] using hf
  have hUniform := DifferentialGeometry.Analysis.Calculus.paramInt_tendstoUniform
    B K V S hKcpt hKV hS h0S hB
  rw [Metric.tendstoUniformlyOn_iff] at hUniform
  have hnear := hUniform (1 / 2 : Real) (by norm_num)
  have hnear' : ∀ᶠ b : Real in 𝓝 0, ∀ z ∈ K,
      dist (∫ t in (0 : Real)..1, B (z, t * b)) (B (z, 0)) < 1 / 2 := by
    filter_upwards [hnear] with b hb z hz
    simpa only [dist_comm] using hb z hz
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp hS 0 h0S
  have hr2 : 0 < r / 2 := by positivity
  have hgood :
      {b : Real | ∀ z ∈ K,
        dist (∫ t in (0 : Real)..1, B (z, t * b)) (B (z, 0)) < 1 / 2} ∩
          Metric.ball 0 (r / 2) ∈ 𝓝 (0 : Real) :=
    Filter.inter_mem hnear' (Metric.ball_mem_nhds 0 hr2)
  obtain ⟨eps, heps, heps_sub⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨eps, heps, ?_⟩
  intro b hb hb_eps
  have hb_ball : b ∈ Metric.ball (0 : Real) eps := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hb] using hb_eps
  have hb_good := heps_sub hb_ball
  have hb_near := hb_good.1
  have hb_r2 : |b| < r / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hb_good.2
  let S1 : Set Real := Set.Ioo (-1 : Real) 2
  have hS1 : IsOpen S1 := isOpen_Ioo
  have hIccS1 : Set.uIcc (0 : Real) 1 ⊆ S1 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmap : Set.MapsTo (fun p : E × Real ↦ (p.1, p.2 * b))
      (V ×ˢ S1) (V ×ˢ S) := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    refine ⟨hz, hrS ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_mul]
    have ht_abs : |t| < 2 := by
      by_cases ht0 : 0 ≤ t
      · rw [abs_of_nonneg ht0]
        exact ht.2
      · rw [abs_of_neg (lt_of_not_ge ht0)]
        linarith [ht.1]
    calc
      |t| * |b| < 2 * |b| :=
        mul_lt_mul_of_pos_right ht_abs (abs_pos.mpr hb.ne')
      _ < 2 * (r / 2) := mul_lt_mul_of_pos_left hb_r2 (by norm_num)
      _ = r := by ring
  have hGb : ContDiffOn Real 1 (fun p : E × Real ↦ G (p.1, p.2 * b))
      (V ×ˢ S1) := by
    exact hG.comp
      (contDiffOn_fst.prodMk (contDiffOn_snd.mul contDiffOn_const)) hmap
  let Q : E → E := fun z ↦ ∫ t in (0 : Real)..1, G (z, t * b)
  have hQderiv : ∀ z ∈ V, HasFDerivAt Q
      (∫ t in (0 : Real)..1, B (z, t * b)) z := by
    intro z hz
    simpa only [Q, B] using
      (DifferentialGeometry.Analysis.Calculus.hasFDerivAt_paramInt
        (fun z : E ↦ fun t : Real ↦ G (z, t * b)) V hV 0 1 S1 hS1
        hIccS1 z hz hGb)
  have hQinj : Set.InjOn Q K := by
    apply DifferentialGeometry.Coordinates.injOn_of_fderiv_near_id
      hKconv (ε := (1 / 2 : Real)) (by norm_num)
    · intro z hz
      exact (hQderiv z (hKV hz)).differentiableAt
    · intro z hz
      rw [(hQderiv z (hKV hz)).fderiv]
      rw [← hB0 z (hKV hz), norm_sub_rev, ← dist_eq_norm]
      exact (hb_near z hz).le
  have hPhiQ : ∀ z ∈ K, Phi (z, b) = b • Q z := by
    intro z hz
    have hzV : z ∈ V := hKV hz
    have hsegS : Set.uIcc (0 : Real) b ⊆ S := by
      rw [Set.uIcc_of_le hb.le]
      intro t ht
      have hb_r : b < r := by
        rw [abs_of_pos hb] at hb_r2
        linarith
      exact hrS (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
        exact ht.2.trans_lt hb_r)
    have hdiff : ∀ t ∈ Set.uIcc (0 : Real) b,
        DifferentiableAt Real (fun s : Real ↦ Phi (z, s)) t := by
      intro t ht
      have hp : (z, t) ∈ V ×ˢ S := ⟨hzV, hsegS ht⟩
      have hpat : DifferentiableAt Real Phi (z, t) :=
        ((hPhi.differentiableOn (by norm_num)) (z, t) hp).differentiableAt
          (hVS.mem_nhds hp)
      exact hpat.comp t (hasFDerivAt_prodMk_right z t).differentiableAt
    have hderiv : ∀ t ∈ Set.uIcc (0 : Real) b,
        deriv (fun s : Real ↦ Phi (z, s)) t = G (z, t) := by
      intro t ht
      have hp : (z, t) ∈ V ×ˢ S := ⟨hzV, hsegS ht⟩
      have hpat : HasFDerivAt Phi (fderiv Real Phi (z, t)) (z, t) :=
        (((hPhi.differentiableOn (by norm_num)) (z, t) hp).differentiableAt
          (hVS.mem_nhds hp)).hasFDerivAt
      have hcomp : HasFDerivAt (fun s : Real ↦ Phi (z, s))
          ((fderiv Real Phi (z, t)).comp (ContinuousLinearMap.inr Real E Real)) t := by
        have hraw := hpat.comp t (hasFDerivAt_prodMk_right z t)
        have hfun : Phi ∘ Prod.mk z = fun s : Real ↦ Phi (z, s) := by
          rfl
        rw [hfun] at hraw
        exact hraw
      rw [hcomp.hasDerivAt.deriv]
      simp only [G, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply]
    have hGint : IntervalIntegrable (fun t : Real ↦ G (z, t))
        MeasureTheory.volume 0 b := by
      have hcont : ContinuousOn (fun t : Real ↦ G (z, t))
          (Set.uIcc (0 : Real) b) := by
        exact hG.continuousOn.comp
          (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht ↦ ⟨hzV, hsegS ht⟩)
      exact hcont.intervalIntegrable
    have hderivInt : IntervalIntegrable (deriv (fun s : Real ↦ Phi (z, s)))
        MeasureTheory.volume 0 b :=
      hGint.congr fun t ht ↦ (hderiv t (Set.uIoc_subset_uIcc ht)).symm
    have hftc := intervalIntegral.integral_deriv_eq_sub hdiff hderivInt
    have hIntEq : (∫ t in (0 : Real)..b, deriv (fun s : Real ↦ Phi (z, s)) t) =
        ∫ t in (0 : Real)..b, G (z, t) := by
      exact intervalIntegral.integral_congr fun t ht ↦
        hderiv t ht
    have hscale := intervalIntegral.smul_integral_comp_mul_left
      (a := (0 : Real)) (b := (1 : Real)) (fun t : Real ↦ G (z, t)) b
    rw [hzero z hzV, sub_zero] at hftc
    calc
      Phi (z, b) = ∫ t in (0 : Real)..b,
          deriv (fun s : Real ↦ Phi (z, s)) t := hftc.symm
      _ = ∫ t in (0 : Real)..b, G (z, t) := hIntEq
      _ = b • Q z := by
        simpa only [Q, mul_zero, mul_one, mul_comm] using hscale.symm
  intro z hz w hw hEq
  apply hQinj hz hw
  have hscaled : b • Q z = b • Q w := by
    change Phi (z, b) = Phi (w, b) at hEq
    rw [← hPhiQ z hz, ← hPhiQ w hw]
    exact hEq
  have hcancel := congrArg (fun v : E ↦ b⁻¹ • v) hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hb.ne', one_smul] using hcancel

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegularizedCurve_endpoint_injOn_closedBall_of_small_time
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (R : Real) (hT : T ∈ D.regular) :
    ∃ eps : Real, 0 < eps ∧ ∀ b : Real, 0 < b → b < eps →
      Set.InjOn (fun W : TangentSpace I x ↦ lRegularizedCurve S T x W b)
        (Metric.closedBall 0 R) := by
  let F : E × Real → M := fun p ↦ lRegularizedCurve S T x p.1 p.2
  let U : Set (E × Real) :=
    lRegularizedJointDom S T x ∩ F ⁻¹' (chartAt H x).source
  let Phi : E × Real → E := fun p ↦
    (1 / 2 : Real) • ((extChartAt I x) (F p) - (extChartAt I x) x)
  let K : Set E := Metric.closedBall 0 R
  have hFall : ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ F
      (lRegularizedJointDom S T x) := lRegularizedCurve_smoothOn S hS T x
  have hU : IsOpen U := hFall.continuousOn.isOpen_inter_preimage
    (lRegularizedJointDom_open S hS T x) (chartAt H x).open_source
  have hKcpt : IsCompact K := isCompact_closedBall 0 R
  have hKconv : Convex Real K := convex_closedBall 0 R
  have hK0 : K ×ˢ ({0} : Set Real) ⊆ U := by
    rintro ⟨W, _⟩ ⟨hW, rfl⟩
    refine ⟨zero_mem_lRegularizedDomain S hS T x W hT, ?_⟩
    change F (W, 0) ∈ (chartAt H x).source
    rw [show F (W, 0) = x by
      change lRegularizedCurve S T x W 0 = x
      exact lRegularizedCurve_zero S T x W]
    exact mem_chart_source H x
  have hK0compact : IsCompact (K ×ˢ ({0} : Set Real)) :=
    hKcpt.prod isCompact_singleton
  obtain ⟨d, hd, hdU⟩ := hK0compact.exists_thickening_subset_open hU hK0
  let r : Real := d / 3
  let V : Set E := Metric.thickening r K
  let St : Set Real := Set.Ioo (-r) r
  have hr : 0 < r := div_pos hd (by norm_num)
  have hV : IsOpen V := Metric.isOpen_thickening
  have hKV : K ⊆ V := Metric.self_subset_thickening hr K
  have hSt : IsOpen St := isOpen_Ioo
  have h0St : (0 : Real) ∈ St := by exact ⟨by linarith, by linarith⟩
  have hVSU : V ×ˢ St ⊆ U := by
    rintro ⟨W, s⟩ ⟨hW, hs⟩
    apply hdU
    rw [Metric.mem_thickening_iff]
    rw [Metric.mem_thickening_iff] at hW
    obtain ⟨Z, hZ, hWZ⟩ := hW
    refine ⟨(Z, (0 : Real)), ⟨hZ, rfl⟩, ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, sub_zero]
    have hsabs : |s| < r := by
      by_cases hs0 : 0 ≤ s
      · simpa only [abs_of_nonneg hs0] using hs.2
      · rw [abs_of_neg (lt_of_not_ge hs0)]
        linarith [hs.1]
    have hmax : max (dist W Z) |s| < r := max_lt hWZ hsabs
    exact hmax.trans (by dsimp only [r]; linarith)
  have hPhiM : ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real))
      𝓘(Real, E) 2 Phi U := by
    have hchart : ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real))
        𝓘(Real, E) 2 (fun p ↦ (extChartAt I x) (F p)) U :=
      (contMDiffOn_extChartAt (I := I) (n := 2) (x := x)).comp
        ((hFall.of_le (by decide :
          (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mono inter_subset_left)
          inter_subset_right
    have hc : ContMDiffOn (modelWithCornersSelf Real E |>.prod
        (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) 2
          (fun _ : E × Real ↦ (1 / 2 : Real)) U :=
      contMDiffOn_const
    have hdifference : ContMDiffOn (modelWithCornersSelf Real E |>.prod
        (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real E) 2
          (fun p ↦ (extChartAt I x) (F p) - (extChartAt I x) x) U :=
      hchart.sub contMDiffOn_const
    have hsmul := hc.smul hdifference
    have hfun :
        (fun _ : E × Real ↦ (1 / 2 : Real)) •
            (fun p ↦ (extChartAt I x) (F p) - (extChartAt I x) x) =
          (fun p ↦ (1 / 2 : Real) •
            ((extChartAt I x) (F p) - (extChartAt I x) x)) := by
      funext p
      rfl
    rw [hfun] at hsmul
    exact hsmul
  have hPhi : ContDiffOn Real 2 Phi (V ×ˢ St) := by
    have hPhiU : ContDiffOn Real 2 Phi U := by
      rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
        ← chartedSpaceSelf_prod]
      exact hPhiM
    exact hPhiU.mono hVSU
  have hzero : ∀ W ∈ V, Phi (W, 0) = 0 := by
    intro W _
    change (1 / 2 : Real) •
      ((extChartAt I x) (F (W, 0)) - (extChartAt I x) x) = 0
    rw [show F (W, 0) = x by
      change lRegularizedCurve S T x W 0 = x
      exact lRegularizedCurve_zero S T x W]
    simp only [sub_self, smul_zero]
  have hlaunch : ∀ W ∈ V,
      (fderiv Real Phi (W, 0)) ((0 : E), (1 : Real)) = W := by
    intro W hW
    have hp : (W, (0 : Real)) ∈ V ×ˢ St := ⟨hW, h0St⟩
    have hPhiDiff : DifferentiableAt Real Phi (W, 0) :=
      ((hPhi.differentiableOn (by norm_num)) (W, 0) hp).differentiableAt
        ((hV.prod hSt).mem_nhds hp)
    have htime := hPhiDiff.hasFDerivAt.comp (0 : Real)
      (hasFDerivAt_prodMk_right W 0)
    have hchartvel :
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun s : Real ↦ F (W, s)) 0) (1 : Real) = (2 : Real) • W := by
      have hfun : (fun s : Real ↦ F (W, s)) = lRegularizedCurve S T x W := by
        funext s
        rfl
      rw [hfun]
      exact lRegularizedCurve_velocity_zero S hS T x W hT
    have hcurveM : ContMDiffAt (modelWithCornersSelf Real Real) I 1
        (fun s : Real ↦ F (W, s)) 0 := by
      have hcomp : ContMDiffAt (modelWithCornersSelf Real Real) I ∞
          ((fun p : E × Real ↦ lRegularizedCurve S T x p.1 p.2) ∘ Prod.mk W) 0 :=
        (lRegularizedCurve_smoothAt S hS T x W hT).comp (0 : Real)
          (contMDiff_const.prodMk contMDiff_id).contMDiffAt
      have hfun :
          (fun p : E × Real ↦ lRegularizedCurve S T x p.1 p.2) ∘ Prod.mk W =
            (fun s : Real ↦ F (W, s)) := by
        funext s
        rfl
      rw [hfun] at hcomp
      exact hcomp.of_le (by norm_num)
    have hcurveD : HasMFDerivAt (modelWithCornersSelf Real Real) I
        (fun s : Real ↦ F (W, s)) 0
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun s : Real ↦ F (W, s)) 0) :=
      (hcurveM.mdifferentiableAt (by norm_num)).hasMFDerivAt
    have hextD : HasMFDerivAt I (modelWithCornersSelf Real E)
        (extChartAt I x) x (ContinuousLinearMap.id Real E) := by
      have hm := ((contMDiffAt_extChartAt (I := I) (n := 1) (x := x)).mdifferentiableAt
        (by norm_num)).hasMFDerivAt
      rw [mfderiv_extChartAt_self (I := I) (x := x)] at hm
      exact hm
    have hcurve0 : F (W, 0) = x := by
      change lRegularizedCurve S T x W 0 = x
      exact lRegularizedCurve_zero S T x W
    have hextD' : HasMFDerivAt I (modelWithCornersSelf Real E)
        (extChartAt I x) (F (W, 0)) (ContinuousLinearMap.id Real E) := by
      rw [hcurve0]
      exact hextD
    have hchart : HasFDerivAt (fun s : Real ↦ (extChartAt I x) (F (W, s)))
        (tangentLinearMapToModel
          (mfderiv (modelWithCornersSelf Real Real) I
            (fun s : Real ↦ F (W, s)) 0)) 0 := by
      have hm := hextD'.comp 0 hcurveD
      have hf := hasMFDerivAt_iff_hasFDerivAt.mp hm
      have hfun : (extChartAt I x) ∘ (fun s : Real ↦ F (W, s)) =
          (fun s : Real ↦ (extChartAt I x) (F (W, s))) := by
        rfl
      rw [hfun] at hf
      apply hf.congr_fderiv
      apply ContinuousLinearMap.ext
      intro v
      with_unfolding_all rfl
    have htime' : HasFDerivAt (fun s : Real ↦ Phi (W, s))
        ((1 / 2 : Real) •
          tangentLinearMapToModel
            (mfderiv (modelWithCornersSelf Real Real) I
              (fun s : Real ↦ F (W, s)) 0)) 0 := by
      exact (hchart.sub_const _).const_smul (1 / 2 : Real)
    have heq := htime.unique htime'
    have heq1 := congrArg (fun L : Real →L[Real] E ↦ L 1) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at heq1
    change (fderiv Real Phi (W, 0)) ((0 : E), (1 : Real)) =
      (1 / 2 : Real) •
        tangentLinearMapToModel
          (mfderiv (modelWithCornersSelf Real Real) I
            (fun s : Real ↦ F (W, s)) 0) 1 at heq1
    let v0 : E :=
      tangentLinearMapToModel
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun s : Real ↦ F (W, s)) 0) 1
    have hv0 : v0 = (2 : Real) • W := by
      have hmodel := congrArg (tangentSpaceModelContinuousLinearEquiv
        (I := I) (F (W, 0))) hchartvel
      rw [hcurve0] at hmodel
      dsimp only [v0]
      convert hmodel using 1 <;> with_unfolding_all rfl
    have heq1' : (fderiv Real Phi (W, 0)) ((0 : E), (1 : Real)) =
        (1 / 2 : Real) • v0 := by
      exact heq1
    rw [hv0, smul_smul] at heq1'
    norm_num at heq1'
    exact heq1'
  obtain ⟨eps, heps, hinj⟩ := slice_inj_small
    Phi K V St hKcpt hKconv hV hKV hSt h0St hPhi hzero hlaunch
  refine ⟨eps, heps, ?_⟩
  intro b hb hb_eps W hW Z hZ hEq
  apply hinj b hb hb_eps hW hZ
  exact congrArg (fun y : M ↦
    (1 / 2 : Real) • ((extChartAt I x) y - (extChartAt I x) x)) hEq

end DifferentialGeometry.PDE.RicciFlow.Perelman
