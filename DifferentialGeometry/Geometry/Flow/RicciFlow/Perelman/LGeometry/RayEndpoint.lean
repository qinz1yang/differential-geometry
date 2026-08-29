import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Exp
import DifferentialGeometry.Geometry.Comparison.Variation.FixedChartIdentities
import DifferentialGeometry.Geometry.Comparison.Variation.BoundedCurve
import DifferentialGeometry.Analysis.Calculus.SmoothClamp
import DifferentialGeometry.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem rayVel_smooth
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) :
    ContMDiffOn
      ((modelWithCornersSelf Real E).prod (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : E × Real ↦
        (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (lRegCurve S T x q.1 q.2)
          (lVelocity (I := I) (fun s ↦ lRegCurve S T x q.1 s) q.2) :
            TangentBundle I M))
      (lRegJointDom S T x) := by
  let J :=
    (modelWithCornersSelf Real E).prod (modelWithCornersSelf Real Real)
  let U := lRegJointDom S T x
  let F : E × Real → M := fun q ↦ lRegCurve S T x q.1 q.2
  have hUopen : IsOpen U := lRegJointDom_open S hS T x
  have hF : ContMDiffOn J I ∞ F U := by
    simpa only [J, F, U] using lRegCurve_smoothOn S hS T x
  have htm :=
    hF.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hUopen.uniqueMDiffOn
  have hunit : ContMDiff J J.tangent ∞
      (fun q : E × Real ↦
        (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)) :
          TangentBundle J (E × Real))) := by
    have hE : ContMDiff (modelWithCornersSelf Real E)
        (modelWithCornersSelf Real E).tangent ∞
        (fun z : E ↦
          (TotalSpace.mk' E z (0 : E) :
            TangentBundle (modelWithCornersSelf Real E) E)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : E ↦ (0 : E))).mpr contDiff_const
    have hR : ContMDiff (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real).tangent ∞
        (fun r : Real ↦
          (TotalSpace.mk' Real r (1 : Real) :
            TangentBundle (modelWithCornersSelf Real Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    have hpair := (hE.comp contMDiff_fst).prodMk (hR.comp contMDiff_snd)
    have hsymm : ContMDiff
        ((modelWithCornersSelf Real E).tangent.prod
          (modelWithCornersSelf Real Real).tangent) J.tangent ∞
        ((equivTangentBundleProd (modelWithCornersSelf Real E) E
          (modelWithCornersSelf Real Real) Real).symm) :=
      contMDiff_equivTangentBundleProd_symm
    with_unfolding_all exact hsymm.comp hpair
  have hcomp : ContMDiffOn J I.tangent ∞
      (fun q : E × Real ↦
        tangentMapWithin J I F U
          (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)))) U :=
    htm.comp (hunit.contMDiffOn (s := U)) (fun _ hq ↦ hq)
  refine hcomp.congr ?_
  intro q hq
  have hwithin : mfderivWithin J I F U q = mfderiv J I F q :=
    mfderivWithin_of_isOpen hUopen hq
  have hdiff : MDifferentiableAt J I F q :=
    ((hF q hq).contMDiffAt (hUopen.mem_nhds hq)).mdifferentiableAt (by simp)
  have hsplit := mfderiv_prod_eq_add_apply
    (I := modelWithCornersSelf Real E)
    (I' := modelWithCornersSelf Real Real) (I'' := I)
    (f := F) (p := q) (v := ((0 : E), (1 : Real))) hdiff
  have hzero : mfderiv (modelWithCornersSelf Real E) I
      (fun z : E ↦ F (z, q.2)) q.1 (0 : E) = 0 := map_zero _
  rw [hzero, zero_add] at hsplit
  have hjoint : mfderiv J I F q ((0 : E), (1 : Real)) =
      lVelocity (I := I) (fun s ↦ F (q.1, s)) q.2 := by
    simpa only [lVelocity] using hsplit
  change TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
      (F q) (lVelocity (I := I) (fun s ↦ F (q.1, s)) q.2) =
    tangentMapWithin J I F U
      (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)))
  simp only [tangentMapWithin, hwithin, hjoint]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRayLag_smooth
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) :
    ContDiffOn Real ∞
      (fun q : E × Real ↦
        lRegLag S T (fun s ↦ lRegCurve S T x q.1 s) q.2)
      (lRegJointDom S T x) := by
  let J :=
    (modelWithCornersSelf Real E).prod (modelWithCornersSelf Real Real)
  let U := lRegJointDom S T x
  let F : E × Real → M := fun q ↦ lRegCurve S T x q.1 q.2
  intro q hq
  have hUopen : IsOpen U := lRegJointDom_open S hS T x
  have hF : ContMDiffAt J I ∞ F q :=
    (lRegCurve_smoothOn S hS T x q hq).contMDiffAt
      (hUopen.mem_nhds hq)
  have harg : ContMDiffAt J
      ((modelWithCornersSelf Real Real).prod I) ∞
      (fun p : E × Real ↦ (T - p.2 ^ 2, F p)) q :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hF
  have hreg : T - q.2 ^ 2 ∈ D.regular :=
    lRegDomain_reg S T x q.1 hq
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T - q.2 ^ 2) (x := F q)
    (D.regular_isOpen.mem_nhds hreg)
  have hmetric : ContMDiffAt J
      (I.prod (modelWithCornersSelf Real
        (E →L[Real] E →L[Real] Real))) ∞
      (fun p : E × Real ↦
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y ↦ TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (F p) ((S.base.metric (T - p.2 ^ 2)).inner (F p))) q := by
    have h := hmetric₀.comp q harg
    change ContMDiffAt J
      (I.prod (modelWithCornersSelf Real
        (E →L[Real] E →L[Real] Real))) ∞
      (fun p : E × Real ↦
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y ↦ TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (F p) ((S.base.metric (T - p.2 ^ 2)).inner (F p))) q at h
    exact h
  have hvel : ContMDiffAt J (I.prod (modelWithCornersSelf Real E)) ∞
      (fun p : E × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (F p)
          (lVelocity (I := I) (fun s ↦ F (p.1, s)) p.2) :
            TangentBundle I M)) q := by
    exact (rayVel_smooth S hS T x q hq).contMDiffAt
      (hUopen.mem_nhds hq)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M ↦ TangentSpace I y)
    (E₂ := fun y : M ↦ TangentSpace I y)
    (E₃ := fun _ : M ↦ Real) hmetric hvel hvel
  have hkin : ContMDiffAt J (modelWithCornersSelf Real Real) ∞
      (fun p : E × Real ↦
        (S.base.metric (T - p.2 ^ 2)).inner (F p)
          (lVelocity (I := I) (fun s ↦ F (p.1, s)) p.2)
          (lVelocity (I := I) (fun s ↦ F (p.1, s)) p.2)) q := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    have h := htotal.2
    change ContMDiffAt J (modelWithCornersSelf Real Real) ∞
      (fun p : E × Real ↦
        (S.base.metric (T - p.2 ^ 2)).inner (F p)
          (lVelocity (I := I) (fun s ↦ F (p.1, s)) p.2)
          (lVelocity (I := I) (fun s ↦ F (p.1, s)) p.2)) q at h
    exact h
  have hscalar₀ : ContMDiffAt
      ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M ↦ S.scalar p.1 p.2)
      (T - q.2 ^ 2, F q) :=
    (scalar_joint (I := I) S hS).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds hreg) Filter.univ_mem)
  have hscalar : ContMDiffAt J (modelWithCornersSelf Real Real) ∞
      (fun p : E × Real ↦ S.scalar (T - p.2 ^ 2) (F p)) q :=
    hscalar₀.comp q harg
  have hlag : ContMDiffAt J (modelWithCornersSelf Real Real) ∞
      (fun p : E × Real ↦
        (1 / 2 : Real) *
            (S.base.metric (T - p.2 ^ 2)).inner (F p)
              (lVelocity (I := I) (fun s ↦ F (p.1, s)) p.2)
              (lVelocity (I := I) (fun s ↦ F (p.1, s)) p.2) +
          2 * p.2 ^ 2 * S.scalar (T - p.2 ^ 2) (F p)) q :=
    (contMDiffAt_const.mul hkin).add
      ((contMDiffAt_const.mul (contMDiffAt_snd.pow 2)).mul hscalar)
  have hcd : ContDiffAt Real ∞
      (fun p : E × Real ↦
        lRegLag S T (fun s ↦ lRegCurve S T x p.1 s) p.2) q := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    simpa only [J, F, lRegLag] using hlag
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lRayAct_fderivInt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {b : Real}
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    HasFDerivAt (E := E)
      (fun W : E ↦ lRegAction S T (lRegCurve S T x W) 0 b)
      (∫ s in (0 : Real)..b,
        fderiv Real
          (fun W : E ↦
            lRegLag S T (fun r ↦ lRegCurve S T x W r) s) Z) Z := by
  obtain ⟨J, hJopen, hJconn, h0J, hbJ, hchosen⟩ :=
    lRegChosen_spec S T x Z hb
  obtain ⟨V, hVopen, hZV, K, hKopen, hKconn, h0K, hbK,
      _alpha, _halpha, hcurves⟩ :=
    lRegFamily_extend S hS T hJopen hJconn h0J hbJ hchosen
  have hseg : Set.uIcc (0 : Real) b ⊆ K := by
    simpa only [Set.uIcc_of_le hb0.le] using
      hKconn.ordConnected.uIcc_subset h0K hbK
  have hVK : V ×ˢ K ⊆ lRegJointDom S T x := by
    intro q hq
    change q.2 ∈ lRegDomain S T x q.1
    exact ⟨fun s ↦ _alpha (q.1, s), K, hKopen, hKconn, h0K, hq.2,
      hcurves q.1 hq.1⟩
  have hlag : ContDiffOn Real 2
      (fun q : E × Real ↦
        lRegLag S T (fun s ↦ lRegCurve S T x q.1 s) q.2)
      (V ×ˢ K) :=
    ((lRayLag_smooth S hS T x).of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)).mono hVK
  simpa only [lRegAction] using
    DifferentialGeometry.Analysis.Calculus.hasFDerivAt_paramInt
      (f := fun W : E ↦ fun s : Real ↦
        lRegLag S T (fun r ↦ lRegCurve S T x W r) s)
      V hVopen 0 b K hKopen hseg Z hZV (hlag.of_le (by norm_num))

private theorem rayOpenClamp
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

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegAction_bdry
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (uIcc (0 : Real) b) x Z)
    (hfix : ∀ u : Real, f u 0 = f 0 0) :
    HasDerivAt (fun u : Real ↦ lRegAction S T (f u) 0 b)
      ((S.base.metric (T - b ^ 2)).inner (f 0 b)
        (lVelocity (I := I) (fun u : Real ↦ f u b) 0)
        (lVelocity (I := I) (f 0) b)) 0 := by
  have ht : ∀ s ∈ uIcc (0 : Real) b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have hzero : lVelocity (I := I) (fun u : Real ↦ f u 0) 0 = 0 := by
    have heq : (fun u : Real ↦ f u 0) = fun _ : Real ↦ f 0 0 := by
      funext u
      exact hfix u
    rw [heq]
    simp only [lVelocity, mfderiv_const]
    rfl
  have heuler : ∀ s ∈ uIcc (0 : Real) b,
      lRegEulerPair S T (f 0) s
        (lVelocity (I := I) (fun u : Real ↦ f u s) 0) = 0 := by
    intro s hs
    simp only [lRegEulerPair]
    rw [(hgeo.2.2 s hs).2.2.2, sub_self, map_zero]
  have hint : (∫ s in (0 : Real)..b,
      lRegEulerPair S T (f 0) s
        (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) = 0 := by
    calc
      (∫ s in (0 : Real)..b,
          lRegEulerPair S T (f 0) s
            (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) =
          ∫ _s in (0 : Real)..b, (0 : Real) := by
            apply intervalIntegral.integral_congr
            intro s hs
            exact heuler s hs
      _ = 0 := by simp only [intervalIntegral.integral_zero]
  have hfirst := lRegAction_first (I := I) S hS T f hf 0 b ht
  simpa only [hzero, map_zero, zero_apply, hint,
    sub_zero] using hfirst

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRayAct_hasFDeriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {tau : Real}
    (hdom : (Z, tau) ∈ lExpPosDom S T x) :
    HasFDerivAt (E := E)
      (fun W : E ↦
        lRegAction S T (lRegCurve S T x W) 0 (Real.sqrt tau))
      (((S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (lVelocity (I := I) (lRegCurve S T x Z) (Real.sqrt tau))).comp
        (mfderiv (modelWithCornersSelf Real E) I
          (fun W : E ↦ lExp S T x W tau) (show E from Z) :
            E →L[Real] TangentSpace I (lExp S T x Z tau))) (show E from Z) := by
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _htime, hb⟩
  let b : Real := Real.sqrt tau
  have hb0 : 0 < b := Real.sqrt_pos.2 htau
  let A : E → Real := fun W ↦
    lRegAction S T (lRegCurve S T x W) 0 b
  let Lint : E →L[Real] Real :=
    ∫ s in (0 : Real)..b,
      fderiv Real
        (fun W : E ↦
          lRegLag S T (fun r ↦ lRegCurve S T x W r) s) Z
  let endMap : E → M := fun W ↦ lExp S T x W tau
  let L : E →L[Real] Real :=
    ((S.base.metric (T - tau)).inner (lExp S T x Z tau)
      (lVelocity (I := I) (lRegCurve S T x Z) b)).comp
        (mfderiv (modelWithCornersSelf Real E) I endMap Z)
  have hInt : HasFDerivAt A Lint Z := by
    simpa only [A, Lint, b] using
      lRayAct_fderivInt S hS T x Z hb0 hb
  have hL : Lint = L := by
    ext Y
    obtain ⟨J, hJopen, hJconn, h0J, hbJ, hchosen⟩ :=
      lRegChosen_spec S T x Z hb
    obtain ⟨V, hVopen, hZV, K, hKopen, hKconn, h0K, hbK,
        alpha, halpha, hcurves⟩ :=
      lRegFamily_extend S hS T hJopen hJconn h0J hbJ hchosen
    obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrhoK⟩ :=
      rayOpenClamp hKopen hKconn h0K hbK hb0
    obtain ⟨zeta, hzeta, hzetaV, hzeta0, hzetaVel⟩ :=
      exists_smooth_curve (I := modelWithCornersSelf Real E) (M := E)
        Z Y V hVopen hZV
    have h8inf : (↑(8 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat) :=
      WithTop.coe_le_coe.mpr le_top
    have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) ∞ rho :=
      contMDiff_iff_contDiff.mpr hrho
    let f : Real → Real → M := fun u s ↦ alpha (zeta u, rho s)
    have hpair : ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ((modelWithCornersSelf Real E).prod
          (modelWithCornersSelf Real Real)) (8 : Nat)
        (fun p : Real × Real ↦ (zeta p.1, rho p.2)) :=
      ((hzeta.of_le h8inf).comp contMDiff_fst).prodMk
        ((hrhoM.of_le h8inf).comp contMDiff_snd)
    have hpairVK : ∀ p : Real × Real,
        (zeta p.1, rho p.2) ∈ V ×ˢ K :=
      fun p ↦ ⟨hzetaV p.1, hrhoK p.2⟩
    have hf : IsSmoothVariation (I := I) f := by
      unfold IsSmoothVariation
      rw [← contMDiffOn_univ]
      have hpairOn : ContMDiffOn
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real))
          ((modelWithCornersSelf Real E).prod
            (modelWithCornersSelf Real Real)) (8 : Nat)
          (fun p : Real × Real ↦ (zeta p.1, rho p.2)) Set.univ :=
        hpair.contMDiffOn
      have h := (halpha.of_le h8inf).comp hpairOn
        (fun p _hp ↦ hpairVK p)
      change ContMDiffOn
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real)) I (8 : Nat)
        (fun p : Real × Real ↦ alpha (zeta p.1, rho p.2)) Set.univ at h
      exact h
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
    have hseg : Set.Icc (0 : Real) b ⊆ K := by
      simpa only [b, Set.uIcc_of_le hb0.le] using
        hKconn.ordConnected.uIcc_subset h0K hbK
    have hcenter : IsLRegCurveOn S T (f 0)
        (Set.uIcc (0 : Real) b) x Z := by
      refine ⟨hf0 0, ?_, ?_⟩
      · have heq : (f 0) =ᶠ[nhds (0 : Real)]
            (fun s : Real ↦ alpha (Z, s)) := by
          filter_upwards
              [isOpen_Ioo.mem_nhds ⟨ha0, hb0.trans hbd⟩] with s hs
          change alpha (zeta 0, rho s) = alpha (Z, s)
          rw [hzeta0]
          simpa only [id_eq] using congrArg (fun r ↦ alpha (Z, r))
            (hrho_id ⟨hs.1.le, hs.2.le⟩)
        unfold lVelocity
        rw [heq.mfderiv_eq (I := modelWithCornersSelf Real Real)
          (I' := I)]
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
        fun u : Real ↦ A (zeta u) := by
      funext u
      have heq := lRegAction_congr (I := I) S T (f u)
        (lRegCurve S T x (zeta u)) 0 b (by
          intro s hs
          apply hfu u
          simpa only [Set.uIcc_of_le hb0.le] using
            Set.uIoo_subset_uIcc_self hs)
      simpa only [A] using heq
    have hend : (fun u : Real ↦ f u b) =
        fun u : Real ↦ endMap (zeta u) := by
      funext u
      change alpha (zeta u, rho b) = lExp S T x (zeta u) tau
      rw [hrhob]
      calc
        alpha (zeta u, b) = lRegCurve S T x (zeta u) b :=
          (hcanon u hbK).symm
        _ = lExp S T x (zeta u) tau := by
          simp only [lExp, b]
    have hcentVel : lVelocity (I := I) (f 0) b =
        lVelocity (I := I) (lRegCurve S T x Z) b := by
      have heq : (f 0) =ᶠ[nhds b] lRegCurve S T x Z := by
        filter_upwards
            [isOpen_Ioo.mem_nhds ⟨ha0.trans hb0, hbd⟩] with s hs
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
      rw [heq.mfderiv_eq (I := modelWithCornersSelf Real Real)
        (I' := I)]
      rfl
    have hExpAt : ContMDiffAt (modelWithCornersSelf Real E) I ∞
        endMap Z := by
      have hopen := lExpPosDom_open S hS T x
      have hjoint := (lExp_smoothOn S hS T x (Z, tau) hdom).contMDiffAt
        (hopen.mem_nhds hdom)
      have hpairAt : ContMDiffAt (modelWithCornersSelf Real E)
          ((modelWithCornersSelf Real E).prod
            (modelWithCornersSelf Real Real)) ∞
          (fun W : E ↦ (W, tau)) Z :=
        contMDiffAt_id.prodMk contMDiffAt_const
      have h := hjoint.comp (f := fun W : E ↦ (W, tau)) (show E from Z) hpairAt
      change ContMDiffAt (modelWithCornersSelf Real E) I ∞ endMap Z at h
      exact h
    have hzetaMD : MDifferentiableAt (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real E) zeta 0 :=
      hzeta.contMDiffAt.mdifferentiableAt (by norm_num)
    have hExpMD : MDifferentiableAt (modelWithCornersSelf Real E) I
        endMap Z :=
      hExpAt.mdifferentiableAt (by simp)
    have hExpMD0 : MDifferentiableAt (modelWithCornersSelf Real E) I
        endMap (zeta 0) := by
      simpa only [hzeta0] using hExpMD
    have hcompMF := hExpMD0.hasMFDerivAt.comp 0 hzetaMD.hasMFDerivAt
    have hendVel : lVelocity (I := I) (fun u : Real ↦ f u b) 0 =
        mfderiv (modelWithCornersSelf Real E) I endMap Z Y := by
      unfold lVelocity
      rw [hend]
      change (mfderiv (modelWithCornersSelf Real Real) I
        (endMap ∘ zeta) 0) (1 : Real) =
          mfderiv (modelWithCornersSelf Real E) I endMap Z Y
      rw [hcompMF.mfderiv]
      change mfderiv (modelWithCornersSelf Real E) I endMap (zeta 0)
          (mfderiv (modelWithCornersSelf Real Real)
            (modelWithCornersSelf Real E) zeta 0 (1 : Real)) =
        mfderiv (modelWithCornersSelf Real E) I endMap Z Y
      rw [hzetaVel, hzeta0]
    have hbdry := lRegAction_bdry S hS T f hf b x Z hcenter hfix
    have hbdry' : HasDerivAt (fun u : Real ↦ A (zeta u))
        ((S.base.metric (T - b ^ 2)).inner (f 0 b)
          (mfderiv (modelWithCornersSelf Real E) I endMap Z Y)
          (lVelocity (I := I) (lRegCurve S T x Z) b)) 0 := by
      rw [← hact]
      simpa only [hendVel, hcentVel] using hbdry
    have hzetaF := hzetaMD.hasMFDerivAt.hasFDerivAt
    have hInt0 : HasFDerivAt A Lint (zeta 0) := by
      simpa only [hzeta0] using hInt
    have hlineF := hInt0.comp 0 hzetaF
    have hline : HasDerivAt (fun u : Real ↦ A (zeta u)) (Lint Y) 0 := by
      have hraw := hlineF.hasDerivAt
      change HasDerivAt (A ∘ zeta)
        (Lint (mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real E) zeta 0 (1 : Real))) 0 at hraw
      rw [hzetaVel] at hraw
      exact hraw
    have hval := hline.unique hbdry'
    have hfb : f 0 b = lExp S T x Z tau := by
      have := congrFun hend 0
      simpa only [endMap, hzeta0] using this
    have hbsq : T - b ^ 2 = T - tau := by
      rw [show b ^ 2 = tau by simp only [b, Real.sq_sqrt htau.le]]
    rw [hfb, hbsq] at hval
    calc
      Lint Y = (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (mfderiv (modelWithCornersSelf Real E) I endMap Z Y)
          (lVelocity (I := I) (lRegCurve S T x Z) b) := hval
      _ = (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (lVelocity (I := I) (lRegCurve S T x Z) b)
          (mfderiv (modelWithCornersSelf Real E) I endMap Z Y) :=
        (S.base.metric (T - tau)).symm (lExp S T x Z tau) _ _
      _ = L Y := by
        rfl
  have hIntL : HasFDerivAt A L Z := by
    rw [← hL]
    exact hInt
  with_unfolding_all exact hIntL

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRayAct_joint
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {tau : Real}
    (hdom : (Z, tau) ∈ lExpPosDom S T x) :
    HasFDerivAt
      (fun p : E × Real ↦
        lRegAction S T (lRegCurve S T x p.1) 0 (Real.sqrt p.2))
      (((((S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (lVelocity (I := I) (lRegCurve S T x Z) (Real.sqrt tau))).comp
          (mfderiv (modelWithCornersSelf Real E) I
            (fun W : E ↦ lExp S T x W tau) (show E from Z) :
              E →L[Real] TangentSpace I (lExp S T x Z tau))).comp
        (ContinuousLinearMap.fst Real E Real)) +
      (lRegLag S T (lRegCurve S T x Z) (Real.sqrt tau) /
          (2 * Real.sqrt tau)) •
        ContinuousLinearMap.snd Real E Real) (Z, tau) := by
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _htime, hb⟩
  let b : Real := Real.sqrt tau
  have hb0 : 0 < b := Real.sqrt_pos.2 htau
  obtain ⟨J, hJopen, hJconn, h0J, hbJ, hchosen⟩ :=
    lRegChosen_spec S T x Z hb
  obtain ⟨V, hVopen, hZV, K, hKopen, hKconn, h0K, hbK,
      _alpha, _halpha, hcurves⟩ :=
    lRegFamily_extend S hS T hJopen hJconn h0J hbJ hchosen
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrhoK⟩ :=
    rayOpenClamp hKopen hKconn h0K hbK hb0
  have hd0 : 0 < d := hb0.trans hbd
  let U : Set (E × Real) := V ×ˢ Set.Ioo 0 (d ^ 2)
  have hUopen : IsOpen U := hVopen.prod (isOpen_Ioo)
  have htauD : tau < d ^ 2 := by
    rw [← Real.sq_sqrt htau.le]
    nlinarith
  have hpU : (Z, tau) ∈ U := ⟨hZV, htau, htauD⟩
  let G : (E × Real) → Real → Real := fun p u ↦
    Real.sqrt p.2 *
      lRegLag S T (lRegCurve S T x p.1)
        (rho (Real.sqrt p.2 * u))
  have hlag : ContDiffOn Real 2
      (fun q : E × Real ↦
        lRegLag S T (fun s ↦ lRegCurve S T x q.1 s) q.2)
      (V ×ˢ K) := by
    apply ((lRayLag_smooth S hS T x).of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)).mono
    intro q hq
    change q.2 ∈ lRegDomain S T x q.1
    exact ⟨fun s ↦ _alpha (q.1, s), K, hKopen, hKconn, h0K, hq.2,
      hcurves q.1 hq.1⟩
  have hG : ContDiffOn Real 2
      (fun q : (E × Real) × Real ↦ G q.1 q.2)
      (U ×ˢ Set.univ) := by
    intro q hq
    have hp2 : ContDiffAt Real 2
        (fun r : (E × Real) × Real ↦ r.1.2) q :=
      contDiffAt_snd.comp q contDiffAt_fst
    have hsqrt : ContDiffAt Real 2
        (fun r : (E × Real) × Real ↦ Real.sqrt r.1.2) q :=
      hp2.sqrt hq.1.2.1.ne'
    have hscaled : ContDiffAt Real 2
        (fun r : (E × Real) × Real ↦ Real.sqrt r.1.2 * r.2) q :=
      hsqrt.mul contDiffAt_snd
    have h2inf : (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat) :=
      WithTop.coe_le_coe.mpr le_top
    have hrho2 : ContDiff Real 2 rho := hrho.of_le h2inf
    have hrhoAt : ContDiffAt Real 2
        (fun r : (E × Real) × Real ↦ rho (Real.sqrt r.1.2 * r.2)) q :=
      hrho2.contDiffAt.comp q hscaled
    have hfirst : ContDiffAt Real 2
        (fun r : (E × Real) × Real ↦ r.1.1) q :=
      contDiffAt_fst.comp q contDiffAt_fst
    have hpair : ContDiffAt Real 2
        (fun r : (E × Real) × Real ↦
          (r.1.1, rho (Real.sqrt r.1.2 * r.2))) q :=
      hfirst.prodMk hrhoAt
    have hpairMem :
        (q.1.1, rho (Real.sqrt q.1.2 * q.2)) ∈ V ×ˢ K :=
      ⟨hq.1.1, hrhoK _⟩
    have hlagAt : ContDiffAt Real 2
        (fun r : E × Real ↦
          lRegLag S T (fun s ↦ lRegCurve S T x r.1 s) r.2)
        (q.1.1, rho (Real.sqrt q.1.2 * q.2)) :=
      hlag.contDiffAt ((hVopen.prod hKopen).mem_nhds hpairMem)
    have hcomp := hlagAt.comp q hpair
    have h := (hsqrt.mul hcomp).contDiffWithinAt (s := U ×ˢ Set.univ)
    change ContDiffWithinAt Real 2
      (fun r : (E × Real) × Real ↦ G r.1 r.2) (U ×ˢ Set.univ) q at h
    exact h
  have hInt :=
    DifferentialGeometry.Analysis.Calculus.hasFDerivAt_paramInt
      G U hUopen 0 1 Set.univ isOpen_univ
      (by simp only [Set.uIcc_of_le zero_le_one, Set.subset_univ])
      (Z, tau) hpU (hG.of_le (by norm_num))
  let A : E × Real → Real := fun p ↦
    lRegAction S T (lRegCurve S T x p.1) 0 (Real.sqrt p.2)
  have hEq : A =ᶠ[nhds (Z, tau)]
      fun p : E × Real ↦ ∫ u in (0 : Real)..1, G p u := by
    filter_upwards [hUopen.mem_nhds hpU] with p hp
    have hbp0 : 0 < Real.sqrt p.2 := Real.sqrt_pos.2 hp.2.1
    have hbpd : Real.sqrt p.2 < d :=
      (Real.sqrt_lt' hd0).2 hp.2.2
    have hclamp : Set.EqOn
        (fun u : Real ↦ rho (Real.sqrt p.2 * u))
        (fun u : Real ↦ Real.sqrt p.2 * u) (Set.Icc 0 1) := by
      intro u hu
      apply hrho_id
      constructor
      · exact ha0.le.trans (mul_nonneg hbp0.le hu.1)
      · exact (mul_le_of_le_one_right hbp0.le hu.2).trans hbpd.le
    have hcongr :
        (∫ u in (0 : Real)..1, G p u) =
          ∫ u in (0 : Real)..1,
            Real.sqrt p.2 *
              lRegLag S T (lRegCurve S T x p.1)
                (Real.sqrt p.2 * u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Set.Icc (0 : Real) 1 := by
        simpa only [Set.uIcc_of_le zero_le_one] using hu
      have hru := hclamp hu'
      change rho (Real.sqrt p.2 * u) = Real.sqrt p.2 * u at hru
      simp only [G]
      rw [hru]
    change lRegAction S T (lRegCurve S T x p.1) 0 (Real.sqrt p.2) = _
    rw [hcongr]
    simp only [lRegAction]
    simpa only [smul_eq_mul, zero_mul, one_mul, mul_zero, mul_one,
      intervalIntegral.integral_const_mul] using
      (intervalIntegral.smul_integral_comp_mul_left
        (a := (0 : Real)) (b := (1 : Real))
        (fun s : Real ↦ lRegLag S T (lRegCurve S T x p.1) s)
        (Real.sqrt p.2)).symm
  have hA : DifferentiableAt Real A (Z, tau) :=
    (hInt.congr_of_eventuallyEq hEq).differentiableAt
  let Lz : E →L[Real] Real :=
    ((S.base.metric (T - tau)).inner (lExp S T x Z tau)
      (lVelocity (I := I) (lRegCurve S T x Z) b)).comp
        (mfderiv (modelWithCornersSelf Real E) I
          (fun W : E ↦ lExp S T x W tau) Z)
  let c : Real := lRegLag S T (lRegCurve S T x Z) b / (2 * b)
  let z : E := Z
  have hbase : HasFDerivAt A (fderiv Real A (Z, tau)) (Z, tau) :=
    hA.hasFDerivAt
  have hins : HasFDerivAt (fun W : E ↦ (W, tau))
      ((1 : E →L[Real] E).prod (0 : E →L[Real] Real)) z :=
    hasFDerivAt_prodMk_left z tau
  have hbaseZ : HasFDerivAt A (fderiv Real A (Z, tau)) (z, tau) := by
    simpa only [z] using hbase
  have hZslice := hbaseZ.comp z hins
  have hZgiven : HasFDerivAt (fun W : E ↦ A (W, tau)) Lz z := by
    with_unfolding_all exact lRayAct_hasFDeriv S hS T x Z hdom
  have hZeq := hZslice.unique hZgiven
  let lag : Real → Real := fun s ↦
    lRegLag S T (lRegCurve S T x Z) s
  have hlagK : ContinuousOn lag K := by
    have hzV : z ∈ V := by
      with_unfolding_all exact hZV
    have hcomp := hlag.continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun s hs ↦ ⟨hzV, hs⟩)
    change ContinuousOn lag K at hcomp
    exact hcomp
  have hseg : Set.uIcc (0 : Real) b ⊆ K := by
    simpa only [b] using hKconn.ordConnected.uIcc_subset h0K hbK
  have hupper : HasDerivAt
      (fun r : Real ↦ ∫ s in (0 : Real)..r, lag s) (lag b) b :=
    intervalIntegral.integral_hasDerivAt_right
      ((hlagK.mono hseg).intervalIntegrable)
      (hlagK.stronglyMeasurableAtFilter hKopen b hbK)
      (hlagK.continuousAt (hKopen.mem_nhds hbK))
  have htime : HasDerivAt (fun r : Real ↦ A (Z, r)) c tau := by
    have hcomp := hupper.comp tau (Real.hasDerivAt_sqrt htau.ne')
    have hfun :
        ((fun r : Real ↦ ∫ s in (0 : Real)..r, lag s) ∘ Real.sqrt) =
          fun r : Real ↦ A (Z, r) := by
      funext r
      rfl
    rw [hfun] at hcomp
    simpa only [c, b, lag, div_eq_mul_inv, one_div, one_mul] using hcomp
  have htins : HasFDerivAt (fun r : Real ↦ (z, r))
      (ContinuousLinearMap.inr Real E Real) tau :=
    hasFDerivAt_prodMk_right z tau
  have htslice := (hbaseZ.comp tau htins).hasDerivAt
  have htimeZ : HasDerivAt (fun r : Real ↦ A (z, r)) c tau := by
    simpa only [z] using htime
  have hteq := htslice.unique htimeZ
  have hfd : fderiv Real A (Z, tau) =
      Lz.comp (ContinuousLinearMap.fst Real E Real) +
        c • ContinuousLinearMap.snd Real E Real := by
    apply ContinuousLinearMap.ext
    intro p
    have hZval := congrArg (fun L : E →L[Real] Real ↦ L p.1) hZeq
    have hZ0 : fderiv Real A (Z, tau) (p.1, 0) = Lz p.1 := by
      simpa [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.prod_apply] using hZval
    have htval : fderiv Real A (Z, tau) (0, (1 : Real)) = c := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply] using hteq
    calc
      fderiv Real A (Z, tau) p =
          fderiv Real A (Z, tau) (p.1, 0) +
            fderiv Real A (Z, tau) (0, p.2) := by
        rw [← map_add]
        congr 1
        ext <;> simp
      _ = Lz p.1 + p.2 * c := by
        rw [show (0, p.2) = p.2 • ((0 : E), (1 : Real)) by
          ext <;> simp, map_smul, htval]
        rw [hZ0]
        simp only [smul_eq_mul]
      _ = (Lz.comp (ContinuousLinearMap.fst Real E Real) +
          c • ContinuousLinearMap.snd Real E Real) p := by
        change Lz p.1 + p.2 * c = Lz p.1 + c * p.2
        ring
  have hfinal : HasFDerivAt A
      (Lz.comp (ContinuousLinearMap.fst Real E Real) +
        c • ContinuousLinearMap.snd Real E Real) (Z, tau) := by
    rw [← hfd]
    exact hbase
  with_unfolding_all exact hfinal

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRay_phase_inj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z W : TangentSpace I x} {b : Real}
    (hZ : b ∈ lRegDomain S T x Z) (hW : b ∈ lRegDomain S T x W)
    (hpos : lRegCurve S T x Z b = lRegCurve S T x W b)
    (hvel : lVelocity (I := I) (lRegCurve S T x Z) b =
      lVelocity (I := I) (lRegCurve S T x W) b) :
    Z = W := by
  obtain ⟨JZ, hJZopen, hJZconn, h0JZ, hbJZ, hchosenZ⟩ :=
    lRegChosen_spec S T x Z hZ
  obtain ⟨JW, hJWopen, hJWconn, h0JW, hbJW, hchosenW⟩ :=
    lRegChosen_spec S T x W hW
  let alphaZ := lRegChosen S T x Z hZ
  let alphaW := lRegChosen S T x W hW
  have heqZ := lRegCurve_eqOn S hS T hJZopen hJZconn h0JZ hchosenZ
  have heqW := lRegCurve_eqOn S hS T hJWopen hJWconn h0JW hchosenW
  have hZgerm : Filter.EventuallyEq (nhds b)
      (lRegCurve S T x Z) alphaZ := by
    filter_upwards [hJZopen.mem_nhds hbJZ] with s hs
    exact heqZ hs
  have hWgerm : Filter.EventuallyEq (nhds b)
      (lRegCurve S T x W) alphaW := by
    filter_upwards [hJWopen.mem_nhds hbJW] with s hs
    exact heqW hs
  have hposChosen : alphaZ b = alphaW b :=
    hZgerm.eq_of_nhds.symm.trans (hpos.trans hWgerm.eq_of_nhds)
  have hvelChosen : lVelocity (I := I) alphaZ b =
      lVelocity (I := I) alphaW b := by
    unfold lVelocity
    rw [← hZgerm.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I),
      ← hWgerm.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I)]
    exact hvel
  have hsolEq := lRegSol_eqOn S hS T hJZopen hJZconn hbJZ
    hJWopen hJWconn hbJW hchosenZ.2.2 hchosenW.2.2
    hposChosen hvelChosen
  have heq0 : Filter.EventuallyEq (nhds (0 : Real)) alphaZ alphaW := by
    filter_upwards [(hJZopen.inter hJWopen).mem_nhds ⟨h0JZ, h0JW⟩] with s hs
    exact hsolEq hs
  have hvel0 : lVelocity (I := I) alphaZ 0 =
      lVelocity (I := I) alphaW 0 := by
    unfold lVelocity
    exact congrArg (fun L ↦ L (1 : Real))
      (heq0.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I))
  have hZ2 : lVelocity (I := I) alphaZ 0 = (2 : Real) • Z :=
    hchosenZ.2.1.trans (Nat.cast_smul_eq_nsmul Real 2 Z).symm
  have hW2 : lVelocity (I := I) alphaW 0 = (2 : Real) • W :=
    hchosenW.2.1.trans (Nat.cast_smul_eq_nsmul Real 2 W).symm
  apply smul_right_injective (TangentSpace I x) (by norm_num : (2 : Real) ≠ 0)
  exact hZ2.symm.trans (hvel0.trans hW2)

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRay_end_vel_ne
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z W : TangentSpace I x} {b : Real}
    (hZ : b ∈ lRegDomain S T x Z) (hW : b ∈ lRegDomain S T x W)
    (hZW : Z ≠ W)
    (hpos : lRegCurve S T x Z b = lRegCurve S T x W b) :
    lVelocity (I := I) (lRegCurve S T x Z) b ≠
      lVelocity (I := I) (lRegCurve S T x W) b := by
  intro hvel
  exact hZW (lRay_phase_inj S hS T x hZ hW hpos hvel)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
