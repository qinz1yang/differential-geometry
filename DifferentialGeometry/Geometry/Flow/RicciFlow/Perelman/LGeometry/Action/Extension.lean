import DifferentialGeometry.Analysis.Calculus.PuncturedDerivative
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.LocalExistence.Curve

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem phase_of_germ
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    {r : Real} {alpha beta : Real → M} {v : Real → E}
    (hcurve : alpha =ᶠ[𝓝 r] beta)
    (hv : v =ᶠ[𝓝 r]
      chartRepAtBase (I := I) x beta
        (fun s ↦ lVelocity (I := I) beta s))
    (hsrc : beta r ∈ (chartAt H x).source)
    (hsol :
      MDifferentiableAt (modelWithCornersSelf Real Real) I beta r ∧
        DifferentiableAt Real
          (chartRepAt (I := I) beta
            (fun s ↦ lVelocity (I := I) beta s) r) r ∧
        covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) beta
            (fun s ↦ lVelocity (I := I) beta s) r =
          lRegAccel S T r (beta r) (lVelocity (I := I) beta r)) :
    HasDerivAt
      (fun s ↦ (chartCurve (I := I) x alpha s, v s))
      (lPhaseField S T x r (chartCurve (I := I) x alpha r, v r)) r := by
  let X : ∀ s, TangentSpace I (beta s) :=
    fun s ↦ lVelocity (I := I) beta s
  let zbeta : Real → E × E := fun s ↦
    (chartCurve (I := I) x beta s, chartRepAtBase (I := I) x beta X s)
  let zalpha : Real → E × E := fun s ↦
    (chartCurve (I := I) x alpha s, v s)
  have hz : zalpha =ᶠ[𝓝 r] zbeta := by
    filter_upwards [hcurve, hv] with s hcurve_s hv_s
    apply Prod.ext
    · exact congrArg (extChartAt I x) hcurve_s
    · exact hv_s
  have hphase : HasDerivAt zbeta
      (lPhaseField S T x r (zbeta r)) r := by
    simpa only [zbeta, X] using
      lRegCurve_phase (I := I) S T x beta r
        hsol.1 hsrc hsol.2.1 hsol.2.2
  have hphase' := hphase.congr_of_eventuallyEq hz
  exact hphase'.congr_deriv (by
    rw [show (chartCurve (I := I) x alpha r, v r) = zbeta r by
      simpa only [zalpha] using hz.eq_of_nhds])

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem regAt_of_punct
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T c : Real)
    (alpha : Real → M) (v : Real → E)
    (hreg : T - c ^ 2 ∈ D.regular)
    (hqcont : ContinuousAt (chartCurve (I := I) (alpha c) alpha) c)
    (hvcont : ContinuousAt v c)
    (hsrc : ∀ᶠ r in 𝓝 c, alpha r ∈ (chartAt H (alpha c)).source)
    (hmdpunct : ∀ᶠ r in 𝓝[≠] c,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hphasepunct : ∀ᶠ r in 𝓝[≠] c,
      HasDerivAt
        (fun s ↦ (chartCurve (I := I) (alpha c) alpha s, v s))
        (lPhaseField S T (alpha c) r
          (chartCurve (I := I) (alpha c) alpha r, v r)) r) :
    MDifferentiableAt (modelWithCornersSelf Real Real) I alpha c ∧
      DifferentiableAt Real
        (chartRepAt (I := I) alpha
          (fun s ↦ lVelocity (I := I) alpha s) c) c ∧
      covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha
          (fun s ↦ lVelocity (I := I) alpha s) c =
        lRegAccel S T c (alpha c) (lVelocity (I := I) alpha c) := by
  let x : M := alpha c
  let X : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ lVelocity (I := I) alpha r
  let q : Real → E := chartCurve (I := I) x alpha
  have hqpunct : ∀ᶠ r in 𝓝[≠] c, HasDerivAt q (v r) r := by
    filter_upwards [hphasepunct] with r hr
    have hfst := hasFDerivAt_fst.comp_hasDerivAt r hr
    change HasDerivAt (chartCurve (I := I) (alpha c) alpha) (v r) r at hfst
    simpa only [q, x] using hfst
  have hqder : HasDerivAt q (v c) c := by
    exact DifferentialGeometry.hasDerivAt_of_punct
      (by simpa only [q, x] using hqpunct)
      (by simpa only [q, x] using hqcont) hvcont
  have hxc : alpha c ∈ (chartAt H x).source := by
    simpa only [x] using mem_chart_source H (alpha c)
  have htarget : (q c) ∈ interior (extChartAt I x).target := by
    rw [(isOpen_extChartAt_target (I := I) x).interior_eq]
    exact (extChartAt I x).map_source (by
      simpa only [q, x, chartCurve, extChartAt_source] using hxc)
  let z : Real → E × E := fun r ↦ (q r, v r)
  have hcurve : lPhaseCurve (I := I) x z =ᶠ[𝓝 c] alpha := by
    filter_upwards [hsrc] with r hrsrc
    simp only [lPhaseCurve, z, q, chartCurve]
    exact (extChartAt I x).left_inv (by
      simpa only [x, extChartAt_source] using hrsrc)
  have hmdiff : MDifferentiableAt
      (modelWithCornersSelf Real Real) I alpha c := by
    have hphase := lPhaseCurve_mdiff (I := I) x z c
      (by simpa only [z] using hqder.differentiableAt) htarget
    exact hphase.congr_of_eventuallyEq hcurve.symm
  have hrep_punct :
      (fun r ↦ chartRepAtBase (I := I) x alpha X r) =ᶠ[𝓝[≠] c] v := by
    filter_upwards [hqpunct, hmdpunct,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hsrc]
      with r hqr hmdr hrsrc
    have hbridge :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) hmdr x hrsrc
    have hderiv : deriv ((extChartAt I x) ∘ alpha) r = v r := by
      have h := hqr.deriv
      change deriv ((extChartAt I x) ∘ alpha) r = v r at h
      exact h
    rw [fderiv_apply_one_eq_deriv, hderiv] at hbridge
    simpa only [q, X, chartCurve, chartRepAtBase_apply, lVelocity] using hbridge
  have hrep_c : chartRepAtBase (I := I) x alpha X c = v c := by
    have hbridge :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) hmdiff x hxc
    have hderiv : deriv ((extChartAt I x) ∘ alpha) c = v c := by
      have h := hqder.deriv
      change deriv ((extChartAt I x) ∘ alpha) c = v c at h
      exact h
    rw [fderiv_apply_one_eq_deriv, hderiv] at hbridge
    simpa only [q, X, chartCurve, chartRepAtBase_apply, lVelocity] using hbridge
  have hrep :
      (fun r ↦ chartRepAtBase (I := I) x alpha X r) =ᶠ[𝓝 c] v :=
    eventuallyEq_nhds_of_eventuallyEq_nhdsNE hrep_punct hrep_c
  have hzcont : ContinuousAt z c := by
    have hqcont' : ContinuousAt q c := by
      simpa only [q, x] using hqcont
    exact hqcont'.prodMk hvcont
  have hzc : (z c).1 ∈ interior (extChartAt I x).target := by
    simpa only [z] using htarget
  have hgcont : ContinuousAt
      (fun r ↦ lPhaseField S T x r (z r)) c := by
    exact (lPhaseField_smoothAt S hS T x hreg hzc).continuousAt.comp_of_eq
      (continuousAt_id.prodMk hzcont) rfl
  have hzder : HasDerivAt z (lPhaseField S T x c (z c)) c :=
    DifferentialGeometry.hasDerivAt_of_punct
      (by simpa only [z, q, x] using hphasepunct) hzcont hgcont
  have hveldiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha X c) c := by
    have hsnd := hasFDerivAt_snd.comp_hasDerivAt c hzder
    have hv : DifferentiableAt Real v c := by
      have h := hsnd.differentiableAt
      change DifferentiableAt Real v c at h
      exact h
    exact hv.congr_of_eventuallyEq (by
      simpa only [X, x, chartRepAtBase_foot] using hrep)
  have hphase := lPhase_accel (I := I) S T x z c hzder hzc
  have hvelEq : ∀ᶠ r in 𝓝 c,
      (lPhaseVel (I := I) x z r : E) = (X r : E) := by
    filter_upwards [hsrc, hrep] with r hrsrc hrepr
    have hrbase : alpha r ∈
        (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hrsrc
    simp only [lPhaseVel, lPhaseCurve, z, q, chartCurve]
    rw [(extChartAt I x).left_inv (by
      simpa only [x, extChartAt_source] using hrsrc)]
    rw [← hrepr]
    simp only [chartRepAtBase_apply]
    exact congrArg (fun A : TangentSpace I (alpha r) ↦ (A : E))
      (trivFromE_trivToE (I := I) x hrbase (X r))
  have hcov :=
    DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) (S.base.metric (T - c ^ 2))
      (lPhaseVel (I := I) x z) X hcurve hvelEq
  refine ⟨hmdiff, hveldiff, ?_⟩
  change
    (covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha X c : E) =
      (lRegAccel S T c (alpha c) (X c) : E)
  rw [← hcov]
  have hphaseE :
      (covDerivAlong (I := I) (S.base.metric (T - c ^ 2))
        (lPhaseCurve (I := I) x z) (lPhaseVel (I := I) x z) c : E) =
        (lRegAccel S T c (lPhaseCurve (I := I) x z c)
          (lPhaseVel (I := I) x z c) : E) :=
    congrArg
      (fun A : TangentSpace I (lPhaseCurve (I := I) x z c) ↦ (A : E)) hphase
  rw [hphaseE, hcurve.self_of_nhds, hvelEq.self_of_nhds]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lRegExtOn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b) (gamma : Real → M)
    (hc1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma (Icc a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hsol : ∀ s ∈ Ioo a b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s =
          lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s)) :
    ∃ alpha : Real → M,
      EqOn alpha gamma (Icc a b) ∧
        ∃ e : Real, 0 < e ∧
          ∀ s ∈ Ioo (a - e) (b + e),
          T - s ^ 2 ∈ D.regular ∧
            MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s ∧
            DifferentiableAt Real
              (chartRepAt (I := I) alpha
                (fun r ↦ lVelocity (I := I) alpha r) s) s ∧
            covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
                (fun r ↦ lVelocity (I := I) alpha r) s =
              lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s) := by
  classical
  let xa : M := gamma a
  let xb : M := gamma b
  have hga_cont : ContinuousWithinAt gamma (Icc a b) a :=
    hc1.continuousOn a ⟨le_rfl, hab.le⟩
  have hgb_cont : ContinuousWithinAt gamma (Icc a b) b :=
    hc1.continuousOn b ⟨hab.le, le_rfl⟩
  have hga_src0 : gamma a ∈ (chartAt H xa).source := by
    simpa only [xa] using mem_chart_source H (gamma a)
  have hgb_src0 : gamma b ∈ (chartAt H xb).source := by
    simpa only [xb] using mem_chart_source H (gamma b)
  have hga_pre : gamma ⁻¹' (chartAt H xa).source ∈ 𝓝[Icc a b] a :=
    hga_cont.preimage_mem_nhdsWithin
      ((chartAt H xa).open_source.mem_nhds hga_src0)
  have hgb_pre : gamma ⁻¹' (chartAt H xb).source ∈ 𝓝[Icc a b] b :=
    hgb_cont.preimage_mem_nhdsWithin
      ((chartAt H xb).open_source.mem_nhds hgb_src0)
  rw [nhdsWithin_Icc_eq_nhdsGE hab] at hga_pre
  rw [nhdsWithin_Icc_eq_nhdsLE hab] at hgb_pre
  obtain ⟨da0, hada0, hda0_src⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hga_pre
  obtain ⟨db0, hdb0b, hdb0_src⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hgb_pre
  let da : Real := min da0 b
  let db : Real := max db0 a
  have hada : a < da := by simpa only [da] using lt_min hada0 hab
  have hdbb : db < b := by simpa only [db] using max_lt hdb0b hab
  have hda_le : da ≤ b := min_le_right _ _
  have ha_db : a ≤ db := le_max_right _ _
  have hda_src : MapsTo gamma (Icc a da) (chartAt H xa).source := by
    intro s hs
    exact hda0_src ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
  have hdb_src : MapsTo gamma (Icc db b) (chartAt H xb).source := by
    intro s hs
    exact hdb0_src ⟨(le_max_left _ _).trans hs.1, hs.2⟩
  let qa : Real → E := chartCurve (I := I) xa gamma
  let qb : Real → E := chartCurve (I := I) xb gamma
  have hqa1 : ContDiffOn Real 1 qa (Icc a da) := by
    have hchart :=
      ((contMDiffOn_iff_target.mp (hc1.mono (fun (s : Real) (hs : s ∈ Icc a da) ↦
        ⟨hs.1, hs.2.trans hda_le⟩))).2 xa).mono
        (fun s hs ↦ ⟨hs, by
          rw [extChartAt_source]
          exact hda_src hs⟩)
    have h := hchart.contDiffOn
    change ContDiffOn Real 1 qa (Icc a da) at h
    exact h
  have hqb1 : ContDiffOn Real 1 qb (Icc db b) := by
    have hchart :=
      ((contMDiffOn_iff_target.mp (hc1.mono (fun (s : Real) (hs : s ∈ Icc db b) ↦
        ⟨ha_db.trans hs.1, hs.2⟩))).2 xb).mono
        (fun s hs ↦ ⟨hs, by
          rw [extChartAt_source]
          exact hdb_src hs⟩)
    have h := hchart.contDiffOn
    change ContDiffOn Real 1 qb (Icc db b) at h
    exact h
  let va : Real → E := derivWithin qa (Icc a da)
  let vb : Real → E := derivWithin qb (Icc db b)
  have hva_cont : ContinuousOn va (Icc a da) := by
    simpa only [va] using
      hqa1.continuousOn_derivWithin (uniqueDiffOn_Icc hada) (by norm_num)
  have hvb_cont : ContinuousOn vb (Icc db b) := by
    simpa only [vb] using
      hqb1.continuousOn_derivWithin (uniqueDiffOn_Icc hdbb) (by norm_num)
  let Aa : TangentSpace I xa :=
    trivFromE (I := I) xa xa (va a)
  let Ab : TangentSpace I xb :=
    trivFromE (I := I) xb xb (vb b)
  obtain ⟨epsa, hepsa, eta, heta0, hetaVel, hetaSol⟩ :=
    exists_lRegCurve_at S hS T a xa Aa (hreg a ⟨le_rfl, hab.le⟩)
  obtain ⟨epsb, hepsb, theta, htheta0, hthetaVel, hthetaSol⟩ :=
    exists_lRegCurve_at S hS T b xb Ab (hreg b ⟨hab.le, le_rfl⟩)
  let alpha : Real → M := fun s ↦
    if s < a then eta s else if s ≤ b then gamma s else theta s
  have halpha_a : alpha a = gamma a := by simp only [alpha, lt_self_iff_false,
    if_false, hab.le, if_true]
  have halpha_b : alpha b = gamma b := by simp only [alpha, not_lt_of_ge hab.le,
    if_false, le_rfl, if_true]
  have halpha_eq : EqOn alpha gamma (Icc a b) := by
    intro s hs
    simp only [alpha, if_neg (not_lt_of_ge hs.1), if_pos hs.2]
  have ha_local : a ∈ Ioo (a - epsa) (a + epsa) := ⟨by linarith, by linarith⟩
  have hb_local : b ∈ Ioo (b - epsb) (b + epsb) := ⟨by linarith, by linarith⟩
  have heta_a := hetaSol a ha_local
  have htheta_b := hthetaSol b hb_local
  have heta_cont : ContinuousAt eta a := heta_a.1.continuousAt
  have htheta_cont : ContinuousAt theta b := htheta_b.1.continuousAt
  have halpha_cont_a : ContinuousAt alpha a := by
    have hleft : ContinuousWithinAt alpha (Iic a) a := by
      apply heta_cont.continuousWithinAt.congr
      · intro s hs
        rcases lt_or_eq_of_le (show s ≤ a from hs) with hsa | rfl
        · simp only [alpha, if_pos hsa]
        · simpa only [halpha_a] using heta0.symm
      · simpa only [halpha_a] using heta0.symm
    have hright0 : ContinuousWithinAt gamma (Ici a) a :=
      hga_cont.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
    have hright : ContinuousWithinAt alpha (Ici a) a := by
      apply hright0.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin,
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (Iic_mem_nhds hab)] with s hs hsb
        simp only [alpha, if_neg (not_lt_of_ge (show a ≤ s from hs)), if_pos hsb]
      · exact halpha_a
    have hunion := hleft.union hright
    simpa only [Iic_union_Ici, continuousWithinAt_univ] using hunion
  have halpha_cont_b : ContinuousAt alpha b := by
    have hleft0 : ContinuousWithinAt gamma (Iic b) b :=
      hgb_cont.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)
    have hleft : ContinuousWithinAt alpha (Iic b) b := by
      apply hleft0.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin,
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (Ioi_mem_nhds hab)] with s hs has
        simp only [alpha, if_neg (not_lt_of_ge has.le),
          if_pos (show s ≤ b from hs)]
      · exact halpha_b
    have hright : ContinuousWithinAt alpha (Ici b) b := by
      apply htheta_cont.continuousWithinAt.congr
      · intro s hs
        rcases eq_or_lt_of_le (show b ≤ s from hs) with rfl | hbs
        · simpa only [halpha_b] using htheta0.symm
        · simp only [alpha, if_neg (not_lt_of_ge (hab.trans hbs).le),
            if_neg (not_le_of_gt hbs)]
      · simpa only [halpha_b] using htheta0.symm
    have hunion := hleft.union hright
    simpa only [Iic_union_Ici, continuousWithinAt_univ] using hunion
  let Xeta : ∀ s, TangentSpace I (eta s) :=
    fun s ↦ lVelocity (I := I) eta s
  let Xtheta : ∀ s, TangentSpace I (theta s) :=
    fun s ↦ lVelocity (I := I) theta s
  let veta : Real → E := chartRepAtBase (I := I) xa eta Xeta
  let vtheta : Real → E := chartRepAtBase (I := I) xb theta Xtheta
  have heta_src_a : eta a ∈ (chartAt H xa).source := by
    rw [heta0]
    exact hga_src0
  have htheta_src_b : theta b ∈ (chartAt H xb).source := by
    rw [htheta0]
    exact hgb_src0
  have veta_diff : DifferentiableAt Real veta a := by
    simpa only [veta, Xeta] using
      chartRep_base_diff (I := I) eta Xeta a xa heta_a.1 heta_src_a heta_a.2.1
  have vtheta_diff : DifferentiableAt Real vtheta b := by
    simpa only [vtheta, Xtheta] using
      chartRep_base_diff (I := I) theta Xtheta b xb htheta_b.1
        htheta_src_b htheta_b.2.1
  have veta_a : veta a = va a := by
    change trivToE (I := I) xa (eta a) (lVelocity (I := I) eta a) = va a
    rw [heta0, hetaVel]
    simp only [Aa]
    exact trivToE_trivFromE (I := I) xa
      (FiberBundle.mem_baseSet_trivializationAt' xa) (va a)
  have vtheta_b : vtheta b = vb b := by
    change trivToE (I := I) xb (theta b) (lVelocity (I := I) theta b) = vb b
    rw [htheta0, hthetaVel]
    simp only [Ab]
    exact trivToE_trivFromE (I := I) xb
      (FiberBundle.mem_baseSet_trivializationAt' xb) (vb b)
  let vA : Real → E := fun s ↦ if s < a then veta s else va s
  let vB : Real → E := fun s ↦ if s ≤ b then vb s else vtheta s
  have hvA_cont : ContinuousAt vA a := by
    have hleft : ContinuousWithinAt vA (Iic a) a := by
      apply veta_diff.continuousAt.continuousWithinAt.congr
      · intro s hs
        rcases lt_or_eq_of_le (show s ≤ a from hs) with hsa | rfl
        · simp only [vA, if_pos hsa]
        · simp only [vA, lt_self_iff_false, if_false, veta_a]
      · simp only [vA, lt_self_iff_false, if_false, veta_a]
    have hright : ContinuousWithinAt vA (Ici a) a := by
      have h := (hva_cont a ⟨le_rfl, hada.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE hada)
      apply h.congr
      · intro s hs
        simp only [vA, if_neg (not_lt_of_ge (show a ≤ s from hs))]
      · simp only [vA, lt_self_iff_false, if_false]
    have hunion := hleft.union hright
    simpa only [Iic_union_Ici, continuousWithinAt_univ] using hunion
  have hvB_cont : ContinuousAt vB b := by
    have hleft : ContinuousWithinAt vB (Iic b) b := by
      have h := (hvb_cont b ⟨hdbb.le, le_rfl⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE hdbb)
      apply h.congr
      · intro s hs
        simp only [vB, if_pos (show s ≤ b from hs)]
      · simp only [vB, le_rfl, if_true]
    have hright : ContinuousWithinAt vB (Ici b) b := by
      apply vtheta_diff.continuousAt.continuousWithinAt.congr
      · intro s hs
        rcases eq_or_lt_of_le (show b ≤ s from hs) with rfl | hbs
        · simp only [vB, le_rfl, if_true, vtheta_b]
        · simp only [vB, if_neg (not_le_of_gt hbs)]
      · simp only [vB, le_rfl, if_true, vtheta_b]
    have hunion := hleft.union hright
    simpa only [Iic_union_Ici, continuousWithinAt_univ] using hunion
  have hsrcA : ∀ᶠ s in 𝓝 a, alpha s ∈ (chartAt H (alpha a)).source :=
    halpha_cont_a.eventually
      ((chartAt H (alpha a)).open_source.mem_nhds
        (mem_chart_source H (alpha a)))
  have hsrcB : ∀ᶠ s in 𝓝 b, alpha s ∈ (chartAt H (alpha b)).source :=
    halpha_cont_b.eventually
      ((chartAt H (alpha b)).open_source.mem_nhds
        (mem_chart_source H (alpha b)))
  have hqcontA : ContinuousAt
      (chartCurve (I := I) (alpha a) alpha) a := by
    exact (continuousAt_extChartAt (I := I) (alpha a)).comp halpha_cont_a
  have hqcontB : ContinuousAt
      (chartCurve (I := I) (alpha b) alpha) b := by
    exact (continuousAt_extChartAt (I := I) (alpha b)).comp halpha_cont_b
  have heta_src : ∀ᶠ s in 𝓝 a, eta s ∈ (chartAt H xa).source :=
    heta_cont.eventually ((chartAt H xa).open_source.mem_nhds heta_src_a)
  have htheta_src : ∀ᶠ s in 𝓝 b, theta s ∈ (chartAt H xb).source :=
    htheta_cont.eventually ((chartAt H xb).open_source.mem_nhds htheta_src_b)
  have hphaseA : ∀ᶠ r in 𝓝[≠] a,
      HasDerivAt
        (fun s ↦ (chartCurve (I := I) (alpha a) alpha s, vA s))
        (lPhaseField S T (alpha a) r
          (chartCurve (I := I) (alpha a) alpha r, vA r)) r := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (isOpen_Ioo.mem_nhds ha_local),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hada),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds heta_src]
      with r hra hrlocal hrda hreta_src
    have hrne : r ≠ a := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hra
    rcases lt_or_gt_of_ne hrne with hra' | har'
    · have hcurve : alpha =ᶠ[𝓝 r] eta := by
        filter_upwards [Iio_mem_nhds hra'] with s hsa
        simp only [alpha, if_pos (show s < a from hsa)]
      have hv : vA =ᶠ[𝓝 r] chartRepAtBase (I := I) xa eta Xeta := by
        filter_upwards [Iio_mem_nhds hra'] with s hsa
        simp only [vA, if_pos (show s < a from hsa), veta]
      simpa only [halpha_a, xa] using
        phase_of_germ (I := I) S T xa hcurve hv hreta_src
          (hetaSol r hrlocal)
    · have hrb : r < b := hrda.trans_le hda_le
      have hrgerm : alpha =ᶠ[𝓝 r] gamma := by
        filter_upwards [Ioo_mem_nhds har' hrb] with s hs
        simp only [alpha, if_neg (not_lt_of_ge hs.1.le), if_pos hs.2.le]
      have hvgerm : vA =ᶠ[𝓝 r]
          chartRepAtBase (I := I) xa gamma
            (fun s ↦ lVelocity (I := I) gamma s) := by
        filter_upwards [Ioo_mem_nhds har' hrda] with s hs
        simp only [vA, if_neg (not_lt_of_ge hs.1.le)]
        have hsfull : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le hda_le⟩
        have hsdata := hsol s hsfull
        have hs_src := hda_src ⟨hs.1.le, hs.2.le⟩
        have hbridge :=
          DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
            (I := I) (M := M) hsdata.1 xa hs_src
        have hmem : Icc a da ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
        rw [fderiv_apply_one_eq_deriv, ← derivWithin_of_mem_nhds hmem] at hbridge
        have hbridge' := hbridge.symm
        change derivWithin qa (Icc a da) s = _ at hbridge'
        simpa only [va, chartRepAtBase_apply, lVelocity] using hbridge'
      have hr_src := hda_src ⟨har'.le, hrda.le⟩
      simpa only [halpha_a, xa] using
        phase_of_germ (I := I) S T xa hrgerm hvgerm hr_src
          (hsol r ⟨har', hrb⟩)
  have hmdA : ∀ᶠ r in 𝓝[≠] a,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (isOpen_Ioo.mem_nhds ha_local),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hada)]
      with r hra hrlocal hrda
    have hrne : r ≠ a := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hra
    rcases lt_or_gt_of_ne hrne with hra' | har'
    · have hcurve : alpha =ᶠ[𝓝 r] eta := by
        filter_upwards [Iio_mem_nhds hra'] with s hsa
        simp only [alpha, if_pos (show s < a from hsa)]
      exact (hetaSol r hrlocal).1.congr_of_eventuallyEq hcurve
    · have hrb : r < b := hrda.trans_le hda_le
      have hcurve : alpha =ᶠ[𝓝 r] gamma := by
        filter_upwards [Ioo_mem_nhds har' hrb] with s hs
        simp only [alpha, if_neg (not_lt_of_ge hs.1.le), if_pos hs.2.le]
      exact (hsol r ⟨har', hrb⟩).1.congr_of_eventuallyEq hcurve
  have hregA := regAt_of_punct (I := I) S hS T a alpha vA
    (hreg a ⟨le_rfl, hab.le⟩) hqcontA hvA_cont hsrcA hmdA hphaseA
  have hphaseB : ∀ᶠ r in 𝓝[≠] b,
      HasDerivAt
        (fun s ↦ (chartCurve (I := I) (alpha b) alpha s, vB s))
        (lPhaseField S T (alpha b) r
          (chartCurve (I := I) (alpha b) alpha r, vB r)) r := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (isOpen_Ioo.mem_nhds hb_local),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hdbb),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds htheta_src]
      with r hrb hrlocal hdbr hrtheta_src
    have hrne : r ≠ b := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hrb
    rcases lt_or_gt_of_ne hrne with hrb' | hbr'
    · have har : a < r := lt_of_le_of_lt ha_db hdbr
      have hrgerm : alpha =ᶠ[𝓝 r] gamma := by
        filter_upwards [Ioo_mem_nhds har hrb'] with s hs
        simp only [alpha, if_neg (not_lt_of_ge hs.1.le), if_pos hs.2.le]
      have hvgerm : vB =ᶠ[𝓝 r]
          chartRepAtBase (I := I) xb gamma
            (fun s ↦ lVelocity (I := I) gamma s) := by
        filter_upwards [Ioo_mem_nhds hdbr hrb'] with s hs
        simp only [vB, if_pos hs.2.le]
        have hsfull : s ∈ Ioo a b := ⟨lt_of_le_of_lt ha_db hs.1, hs.2⟩
        have hsdata := hsol s hsfull
        have hs_src := hdb_src ⟨hs.1.le, hs.2.le⟩
        have hbridge :=
          DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
            (I := I) (M := M) hsdata.1 xb hs_src
        have hmem : Icc db b ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
        rw [fderiv_apply_one_eq_deriv, ← derivWithin_of_mem_nhds hmem] at hbridge
        have hbridge' := hbridge.symm
        change derivWithin qb (Icc db b) s = _ at hbridge'
        simpa only [vb, chartRepAtBase_apply, lVelocity] using hbridge'
      have hr_src := hdb_src ⟨hdbr.le, hrb'.le⟩
      simpa only [halpha_b, xb] using
        phase_of_germ (I := I) S T xb hrgerm hvgerm hr_src
          (hsol r ⟨har, hrb'⟩)
    · have hcurve : alpha =ᶠ[𝓝 r] theta := by
        filter_upwards [Ioi_mem_nhds hbr'] with s hbs
        simp only [alpha, if_neg (not_lt_of_ge (hab.trans hbs).le),
          if_neg (not_le_of_gt (show b < s from hbs))]
      have hv : vB =ᶠ[𝓝 r] chartRepAtBase (I := I) xb theta Xtheta := by
        filter_upwards [Ioi_mem_nhds hbr'] with s hbs
        simp only [vB, if_neg (not_le_of_gt (show b < s from hbs)), vtheta]
      simpa only [halpha_b, xb] using
        phase_of_germ (I := I) S T xb hcurve hv hrtheta_src
          (hthetaSol r hrlocal)
  have hmdB : ∀ᶠ r in 𝓝[≠] b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (isOpen_Ioo.mem_nhds hb_local),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hdbb)]
      with r hrb hrlocal hdbr
    have hrne : r ≠ b := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hrb
    rcases lt_or_gt_of_ne hrne with hrb' | hbr'
    · have har : a < r := lt_of_le_of_lt ha_db hdbr
      have hcurve : alpha =ᶠ[𝓝 r] gamma := by
        filter_upwards [Ioo_mem_nhds har hrb'] with s hs
        simp only [alpha, if_neg (not_lt_of_ge hs.1.le), if_pos hs.2.le]
      exact (hsol r ⟨har, hrb'⟩).1.congr_of_eventuallyEq hcurve
    · have hcurve : alpha =ᶠ[𝓝 r] theta := by
        filter_upwards [Ioi_mem_nhds hbr'] with s hbs
        simp only [alpha, if_neg (not_lt_of_ge (hab.trans hbs).le),
          if_neg (not_le_of_gt (show b < s from hbs))]
      exact (hthetaSol r hrlocal).1.congr_of_eventuallyEq hcurve
  have hregB := regAt_of_punct (I := I) S hS T b alpha vB
    (hreg b ⟨hab.le, le_rfl⟩) hqcontB hvB_cont hsrcB hmdB hphaseB
  have hclosed : ∀ s ∈ Icc a b,
      T - s ^ 2 ∈ D.regular ∧
        MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) alpha
            (fun r ↦ lVelocity (I := I) alpha r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
            (fun r ↦ lVelocity (I := I) alpha r) s =
          lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s) := by
    intro s hs
    refine ⟨hreg s hs, ?_⟩
    rcases eq_or_lt_of_le hs.1 with rfl | has
    · exact hregA
    rcases eq_or_lt_of_le hs.2 with rfl | hsb
    · exact hregB
    have hsopen : s ∈ Ioo a b := ⟨has, hsb⟩
    have hsdata := hsol s hsopen
    have heq : alpha =ᶠ[𝓝 s] gamma := by
      filter_upwards [Ioo_mem_nhds has hsb] with r hr
      simp only [alpha, if_neg (not_lt_of_ge hr.1.le), if_pos hr.2.le]
    exact (lRegData_congr (I := I) S T s heq ⟨hreg s hs, hsdata⟩).2
  let timeMap : Real → Real := fun s ↦ T - s ^ 2
  have htime_cont : Continuous timeMap :=
    continuous_const.sub (continuous_id.pow 2)
  have hregOpen : IsOpen (timeMap ⁻¹' D.regular) :=
    D.regular_isOpen.preimage htime_cont
  have haReg : a ∈ timeMap ⁻¹' D.regular :=
    hreg a ⟨le_rfl, hab.le⟩
  have hbReg : b ∈ timeMap ⁻¹' D.regular :=
    hreg b ⟨hab.le, le_rfl⟩
  obtain ⟨ra, hra, hraSub⟩ := Metric.isOpen_iff.mp hregOpen a haReg
  obtain ⟨rb, hrb, hrbSub⟩ := Metric.isOpen_iff.mp hregOpen b hbReg
  let e : Real := min (min epsa epsb) (min ra rb)
  have he : 0 < e := by
    simpa only [e] using lt_min (lt_min hepsa hepsb) (lt_min hra hrb)
  have he_epsa : e ≤ epsa :=
    (min_le_left _ _).trans (min_le_left _ _)
  have he_epsb : e ≤ epsb :=
    (min_le_left _ _).trans (min_le_right _ _)
  have he_ra : e ≤ ra :=
    (min_le_right _ _).trans (min_le_left _ _)
  have he_rb : e ≤ rb :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨alpha, halpha_eq, e, he, ?_⟩
  intro s hs
  by_cases hsa : s < a
  · have hlocal : s ∈ Ioo (a - epsa) (a + epsa) := by
      constructor
      · exact (sub_le_sub_left he_epsa a).trans_lt hs.1
      · linarith
    have hsReg : T - s ^ 2 ∈ D.regular := by
      apply hraSub
      rw [Metric.mem_ball, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hsa.le)]
      linarith [hs.1, he_ra]
    have heq : alpha =ᶠ[𝓝 s] eta := by
      filter_upwards [Iio_mem_nhds hsa] with r hr
      change r < a at hr
      simp only [alpha, if_pos hr]
    exact lRegData_congr (I := I) S T s heq ⟨hsReg, hetaSol s hlocal⟩
  by_cases hbs : b < s
  · have hlocal : s ∈ Ioo (b - epsb) (b + epsb) := by
      constructor
      · linarith
      · linarith [hs.2, he_epsb]
    have hsReg : T - s ^ 2 ∈ D.regular := by
      apply hrbSub
      rw [Metric.mem_ball, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr hbs.le)]
      linarith [hs.2, he_rb]
    have heq : alpha =ᶠ[𝓝 s] theta := by
      filter_upwards [Ioi_mem_nhds hbs] with r hr
      change b < r at hr
      simp only [alpha, if_neg (not_lt_of_ge (hab.trans hr).le),
        if_neg (not_le_of_gt hr)]
    exact lRegData_congr (I := I) S T s heq ⟨hsReg, hthetaSol s hlocal⟩
  exact hclosed s ⟨le_of_not_gt hsa, le_of_not_gt hbs⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lRegExt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b) (gamma : Real → M)
    (hc1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma (Icc a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hsol : ∀ s ∈ Ioo a b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s =
          lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s)) :
    ∃ alpha : Real → M,
      EqOn alpha gamma (Icc a b) ∧
        ∀ s ∈ Icc a b,
          T - s ^ 2 ∈ D.regular ∧
            MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s ∧
            DifferentiableAt Real
              (chartRepAt (I := I) alpha
                (fun r ↦ lVelocity (I := I) alpha r) s) s ∧
            covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
                (fun r ↦ lVelocity (I := I) alpha r) s =
              lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s) := by
  obtain ⟨alpha, halpha, e, he, hsolOpen⟩ :=
    exists_lRegExtOn (I := I) S hS T a b hab gamma hc1 hreg hsol
  refine ⟨alpha, halpha, fun s hs ↦ hsolOpen s ?_⟩
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
