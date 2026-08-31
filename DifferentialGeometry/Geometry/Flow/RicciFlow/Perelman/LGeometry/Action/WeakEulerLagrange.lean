import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeNonlinearEuler
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Force
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.MetricFamilyVelocity
import DifferentialGeometry.Geometry.Operator.Gradient

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Variation.Aux5
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private noncomputable def lWeakCoeff
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    (r : Real) (x : E) : E →L[Real] E :=
  (1 / 2 : Real) • chartGramOp (I := I) S.family p
    (T - (a + r) ^ 2, x)

private noncomputable def lWeakCoeffD
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    (r : Real) (x : E) : E →L[Real] (E →L[Real] E) :=
  (1 / 2 : Real) •
    (fderiv Real (chartGramOp (I := I) S.family p)
      (T - (a + r) ^ 2, x)).comp (ContinuousLinearMap.inr Real Real E)

private noncomputable def lWeakScal
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    (r : Real) (x : E) : Real :=
  2 * (a + r) ^ 2 * S.scalar (T - (a + r) ^ 2)
    ((extChartAt I p).symm x)

private noncomputable def lWeakScalLine
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u v : timeH1 E L) (q : Real × Real) : Real :=
  lWeakScal (I := I) S T a p q.2
    (u.toFun q.2 + q.1 • v.toFun q.2)

private noncomputable def lWeakScalCov
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    (r : Real) (x : E) : E →L[Real] Real :=
  (2 * (a + r) ^ 2) •
    chartScalCov (I := I) S p (T - (a + r) ^ 2, x)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
private theorem lWeakScal_fderiv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    (r : Real) (x : E)
    (ht : T - (a + r) ^ 2 ∈ D.regular)
    (hx : x ∈ interior (extChartAt I p).target) :
    HasFDerivAt (lWeakScal (I := I) S T a p r)
      (lWeakScalCov (I := I) S T a p r x) x := by
  let f : M → Real := S.scalar (T - (a + r) ^ 2)
  have hxt : x ∈ (extChartAt I p).target := interior_subset hx
  have hf : ContMDiff I 𝓘(Real, Real) ∞ f := by
    simpa only [f] using scalarSmoothOfSol (I := I) S (T - (a + r) ^ 2)
  have hcoord : ContDiffAt Real ∞ (scalarOnE (I := I) p f) x :=
    (scalarOnE_contDiffOn (I := I) p hf).contDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hxt)
  have hbase := hcoord.differentiableAt (by simp) |>.hasFDerivAt
  have hscaled := hbase.const_smul (2 * (a + r) ^ 2)
  rw [lWeakScalCov, chartScalCov_eq (I := I) S hS p ht hx]
  change HasFDerivAt
    ((2 * (a + r) ^ 2) • scalarOnE (I := I) p f)
    ((2 * (a + r) ^ 2) • fderiv Real (scalarOnE (I := I) p f) x) x
  exact hscaled

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem lWeakScal_dcont
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (u v : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hbuf : MapsTo
      (fun q : Real × Real ↦ u.toFun q.2 + q.1 • v.toFun q.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    ContinuousOn
      (fun q : Real × Real ↦ lWeakScalCov (I := I) S T a p q.2
        (u.toFun q.2 + q.1 • v.toFun q.2) (v.toFun q.2))
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L) := by
  let K : Set (Real × Real) :=
    Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L
  let U : Set (Real × E) :=
    D.regular ×ˢ interior (extChartAt I p).target
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let pos : Real × Real → E :=
    fun q ↦ u.toFun q.2 + q.1 • v.toFun q.2
  have htau : ContinuousOn (fun q : Real × Real ↦ tau q.2) K := by
    exact continuousOn_const.sub
      ((continuousOn_const.add continuousOn_snd).pow 2)
  have hpos : ContinuousOn pos K := by
    exact (u.continuousOn_toFun.comp continuousOn_snd fun q hq ↦ hq.2).add
      (continuousOn_fst.smul
        (v.continuousOn_toFun.comp continuousOn_snd fun q hq ↦ hq.2))
  have hpair : ContinuousOn
      (fun q : Real × Real ↦ (tau q.2, pos q)) K := htau.prodMk hpos
  have hpair_mem : MapsTo (fun q : Real × Real ↦ (tau q.2, pos q)) K U := by
    intro q hq
    exact ⟨hreg q.2 hq.2, hbuf hq⟩
  have hcov : ContinuousOn
      (fun q : Real × Real ↦ chartScalCov (I := I) S p (tau q.2, pos q)) K :=
    (chartScalCov_smooth (I := I) S hS p).continuousOn.comp hpair hpair_mem
  have hscaled : ContinuousOn
      (fun q : Real × Real ↦ lWeakScalCov (I := I) S T a p q.2 (pos q)) K := by
    exact (((continuousOn_const.add continuousOn_snd).pow 2 |>.const_mul 2).smul
      hcov)
  exact hscaled.clm_apply
    (v.continuousOn_toFun.comp continuousOn_snd fun q hq ↦ hq.2)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem lWeakScalLine_cont
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (u v : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hbuf : MapsTo
      (fun q : Real × Real ↦ u.toFun q.2 + q.1 • v.toFun q.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    ContinuousOn (lWeakScalLine (I := I) S T a p u v)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L) := by
  let K : Set (Real × Real) :=
    Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let pos : Real × Real → E :=
    fun q ↦ u.toFun q.2 + q.1 • v.toFun q.2
  have htau : ContinuousOn (fun q : Real × Real ↦ tau q.2) K := by
    exact continuousOn_const.sub
      ((continuousOn_const.add continuousOn_snd).pow 2)
  have hpos : ContinuousOn pos K := by
    exact (u.continuousOn_toFun.comp continuousOn_snd fun q hq ↦ hq.2).add
      (continuousOn_fst.smul
        (v.continuousOn_toFun.comp continuousOn_snd fun q hq ↦ hq.2))
  have hchart : ContinuousOn
      (fun q : Real × Real ↦ (extChartAt I p).symm (pos q)) K := by
    exact (continuousOn_extChartAt_symm (I := I) p).comp' hpos
      (fun q hq ↦ interior_subset (hbuf hq))
  have hweight : ContinuousOn
      (fun q : Real × Real ↦ 2 * (a + q.2) ^ 2) K :=
    ((continuousOn_const.add continuousOn_snd).pow 2).const_mul 2
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  rw [continuousOn_iff_continuous_domRestrict]
  let tau' : K → {t : Real // t ∈ D.carrier} := fun q ↦
    ⟨tau q.1.2, D.regular_subset (hreg q.1.2 q.2.2)⟩
  have htau' : Continuous tau' := by
    exact continuous_induced_rng.mpr htau.domRestrict
  have hchart' : Continuous (fun q : K ↦
      (extChartAt I p).symm (pos q.1)) := hchart.domRestrict
  have hscalar' : Continuous (fun q : K ↦
      S.scalar (tau q.1.2) ((extChartAt I p).symm (pos q.1))) := by
    have h := hSc.continuous_subtype.comp (htau'.prodMk hchart')
    with_unfolding_all exact h
  exact (hweight.domRestrict.mul hscalar').congr fun _ ↦ rfl

private theorem compactLine_deriv
    {L : Real} (hL : 0 ≤ L) (lag dLag : Real → Real → Real)
    (hlagJoint : ContinuousOn (fun q : Real × Real ↦ lag q.1 q.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L))
    (hdJoint : ContinuousOn (fun q : Real × Real ↦ dLag q.1 q.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L))
    (hslice : ∀ c r, c ∈ Icc (-1 : Real) 1 → r ∈ Icc (0 : Real) L →
      HasDerivAt (fun z : Real ↦ lag z r) (dLag c r) c) :
    (∀ c ∈ Icc (-1 : Real) 1,
      IntervalIntegrable (lag c) volume 0 L) ∧
      IntervalIntegrable (dLag 0) volume 0 L ∧
        HasDerivAt (fun c : Real ↦ ∫ r in (0 : Real)..L, lag c r)
          (∫ r in (0 : Real)..L, dLag 0 r) 0 := by
  let K : Set (Real × Real) :=
    Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L
  have hlagInt : ∀ c ∈ Icc (-1 : Real) 1,
      IntervalIntegrable (lag c) volume 0 L := by
    intro c hc
    have hs : ContinuousOn (lag c) (Icc (0 : Real) L) := by
      with_unfolding_all
        exact hlagJoint.comp (continuousOn_const.prodMk continuousOn_id)
          (fun r hr ↦ ⟨hc, hr⟩)
    exact ContinuousOn.intervalIntegrable_of_Icc hL hs
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hKcompact.bddAbove_image hdJoint.norm
  let C : Real := max C₀ 0
  have hC : ∀ q ∈ K, ‖dLag q.1 q.2‖ ≤ C := by
    intro q hq
    exact (hC₀ ⟨q, hq, rfl⟩).trans (le_max_left C₀ 0)
  refine ⟨hlagInt, ?_⟩
  exact intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := lag) (F' := dLag) (x₀ := (0 : Real)) (μ := volume)
      (s := Icc (-1 : Real) 1) (a := (0 : Real)) (b := L)
      (bound := fun _ : Real ↦ C)
      (Icc_mem_nhds (by norm_num) (by norm_num))
      (by
        filter_upwards [Icc_mem_nhds (by norm_num : (-1 : Real) < 0)
          (by norm_num : (0 : Real) < 1)] with c hc
        exact (hlagInt c hc).def'.aestronglyMeasurable)
      (hlagInt 0 (by norm_num))
      (by
        have hs : ContinuousOn (dLag 0) (Icc (0 : Real) L) := by
          with_unfolding_all
            exact hdJoint.comp (continuousOn_const.prodMk continuousOn_id)
              (fun r hr ↦ ⟨by norm_num, hr⟩)
        exact (hs.mono (by
          simpa only [uIcc_of_le hL] using
            (uIoc_subset_uIcc : uIoc (0 : Real) L ⊆ uIcc (0 : Real) L)))
          |>.aestronglyMeasurable measurableSet_uIoc)
      (Eventually.of_forall fun r hr c hc ↦
        hC (c, r) ⟨hc, by
          simpa only [uIcc_of_le hL] using uIoc_subset_uIcc hr⟩)
      continuousOn_const.intervalIntegrable
      (Eventually.of_forall fun r hr c hc ↦
        hslice c r hc (by
          simpa only [uIcc_of_le hL] using uIoc_subset_uIcc hr))

private theorem cont_zero_slice
    {Y : Type*} [TopologicalSpace Y] {L : Real}
    {f : Real × Real → Y}
    (hf : ContinuousOn f
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)) :
    ContinuousOn (fun r : Real ↦ f (0, r)) (Icc (0 : Real) L) := by
  exact hf.comp' (continuousOn_const.prodMk continuousOn_id)
    (fun _ hr ↦ ⟨by norm_num, hr⟩)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
private theorem lWeakScal_line
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 ≤ L) (u v : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hbuf : MapsTo
      (fun q : Real × Real ↦ u.toFun q.2 + q.1 • v.toFun q.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    (∀ c ∈ Icc (-1 : Real) 1, IntervalIntegrable
      (fun r ↦ lWeakScal (I := I) S T a p r
        ((u + c • v).toFun r)) volume 0 L) ∧
      IntervalIntegrable
          (fun r ↦ lWeakScalCov (I := I) S T a p r
            (u.toFun r) (v.toFun r)) volume 0 L ∧
        HasDerivAt
        (fun c : Real ↦ ∫ r in (0 : Real)..L,
          lWeakScal (I := I) S T a p r ((u + c • v).toFun r))
        (∫ r in (0 : Real)..L,
          lWeakScalCov (I := I) S T a p r (u.toFun r) (v.toFun r)) 0 := by
  classical
  let K : Set (Real × Real) :=
    Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L
  let pos : Real × Real → E :=
    fun q ↦ u.toFun q.2 + q.1 • v.toFun q.2
  let lag : Real → Real → Real :=
    fun c r ↦ lWeakScal (I := I) S T a p r (pos (c, r))
  let dLag : Real → Real → Real :=
    fun c r ↦ lWeakScalCov (I := I) S T a p r (pos (c, r)) (v.toFun r)
  have hlagJoint : ContinuousOn (fun q : Real × Real ↦ lag q.1 q.2) K :=
    lWeakScalLine_cont (I := I) S hS T a p u v hreg hbuf
  have hdJoint : ContinuousOn (fun q : Real × Real ↦ dLag q.1 q.2) K :=
    lWeakScal_dcont (I := I) S hS T a p u v hreg hbuf
  have hslice (c r : Real) (hc : c ∈ Icc (-1 : Real) 1)
      (hr : r ∈ Icc (0 : Real) L) :
      HasDerivAt (fun z : Real ↦ lag z r) (dLag c r) c := by
    have hline : HasDerivAt (fun z : Real ↦ u.toFun r + z • v.toFun r)
        (v.toFun r) c := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id c).smul_const (v.toFun r)).const_add (u.toFun r)
    exact (lWeakScal_fderiv (I := I) S hS T a p r (pos (c, r))
      (hreg r hr) (hbuf ⟨hc, hr⟩)).comp_hasDerivAt c hline
  have hparam := compactLine_deriv hL lag dLag hlagJoint hdJoint hslice
  have hlineEq (c : Real) :
      (∫ r in (0 : Real)..L,
        lWeakScal (I := I) S T a p r ((u + c • v).toFun r)) =
      ∫ r in (0 : Real)..L, lag c r := by
    apply intervalIntegral.integral_congr
    intro r hr
    change lWeakScal (I := I) S T a p r ((u + c • v).toFun r) =
      lWeakScal (I := I) S T a p r (pos (c, r))
    rw [timeH1.toFun_add u (c • v) (by simpa only [uIcc_of_le hL] using hr),
      timeH1.toFun_smul c v (by simpa only [uIcc_of_le hL] using hr)]
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    apply (hparam.1 c hc).congr
    intro r hr
    have hr' : r ∈ Icc (0 : Real) L := by
      simpa only [uIcc_of_le hL] using uIoc_subset_uIcc hr
    change lWeakScal (I := I) S T a p r (pos (c, r)) =
      lWeakScal (I := I) S T a p r ((u + c • v).toFun r)
    rw [timeH1.toFun_add u (c • v) hr', timeH1.toFun_smul c v hr']
  · simpa only [dLag, pos, zero_smul, add_zero] using hparam.2.1
  · have hder :=
      hparam.2.2.congr_of_eventuallyEq (Eventually.of_forall hlineEq)
    refine hder.congr_deriv ?_
    apply intervalIntegral.integral_congr
    intro r _
    simp only [dLag, pos, zero_smul, add_zero]

private theorem bilin_cont_bound
    {Q : Type*} [TopologicalSpace Q] (K : Set Q) (hK : IsCompact K)
    (F : Q → E →L[Real] (E →L[Real] E)) (hF : ContinuousOn F K) :
    ∃ C : Real, 0 ≤ C ∧ ∀ q ∈ K, ∀ x y : E,
      ‖F q x y‖ ≤ C * ‖x‖ * ‖y‖ := by
  have hfin : 0 < Module.finrank Real E :=
    Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  let : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := Real) (M := E) hfin
  let K3 : Set (Q × (E × E)) :=
    K ×ˢ (Metric.closedBall (0 : E) 1 ×ˢ Metric.closedBall (0 : E) 1)
  have hK3 : IsCompact K3 :=
    hK.prod
      ((isCompact_closedBall (0 : E) 1).prod (isCompact_closedBall (0 : E) 1))
  have hEval : ContinuousOn
      (fun z : Q × (E × E) ↦ F z.1 z.2.1 z.2.2) K3 := by
    exact ((hF.comp continuousOn_fst fun z hz ↦ hz.1).clm_apply
      ((continuous_fst.comp continuous_snd).continuousOn)).clm_apply
        ((continuous_snd.comp continuous_snd).continuousOn)
  obtain ⟨C₀, hC₀⟩ := hK3.exists_bound_of_continuousOn hEval
  let C : Real := max C₀ 0
  refine ⟨C, le_max_right C₀ 0, ?_⟩
  intro q hq x y
  by_cases hx0 : x = 0
  · subst x
    simp
  by_cases hy0 : y = 0
  · subst y
    simp
  let xn : E := ‖x‖⁻¹ • x
  let yn : E := ‖y‖⁻¹ • y
  have hxn : ‖xn‖ = 1 := by
    simp [xn, norm_smul, norm_inv, (norm_ne_zero_iff.mpr hx0)]
  have hyn : ‖yn‖ = 1 := by
    simp [yn, norm_smul, norm_inv, (norm_ne_zero_iff.mpr hy0)]
  have hxmem : xn ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hxn]
  have hymem : yn ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hyn]
  have hxrepr : ‖x‖ • xn = x := by
    simp [xn, smul_smul, (norm_ne_zero_iff.mpr hx0)]
  have hyrepr : ‖y‖ • yn = y := by
    simp [yn, smul_smul, (norm_ne_zero_iff.mpr hy0)]
  have houter : F q (‖x‖ • xn) = ‖x‖ • F q xn :=
    ContinuousLinearMap.map_smul (F q) ‖x‖ xn
  have hinner : F q xn (‖y‖ • yn) = ‖y‖ • F q xn yn :=
    ContinuousLinearMap.map_smul (F q xn) ‖y‖ yn
  have hscale : F q x y = (‖x‖ * ‖y‖) • F q xn yn := by
    calc
      F q x y = F q (‖x‖ • xn) (‖y‖ • yn) := by rw [hxrepr, hyrepr]
      _ = (‖x‖ • F q xn) (‖y‖ • yn) :=
        congrArg (fun A : E →L[Real] E ↦ A (‖y‖ • yn)) houter
      _ = ‖x‖ • F q xn (‖y‖ • yn) := by
        rw [smul_apply]
      _ = ‖x‖ • (‖y‖ • F q xn yn) := congrArg (fun z : E ↦ ‖x‖ • z) hinner
      _ = _ := by rw [smul_smul]
  rw [hscale, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
  calc
    (‖x‖ * ‖y‖) * ‖F q xn yn‖ ≤ (‖x‖ * ‖y‖) * C := by
      gcongr
      exact (hC₀ (q, (xn, yn)) ⟨hq, hxmem, hymem⟩).trans
        (le_max_left C₀ 0)
    _ = C * ‖x‖ * ‖y‖ := by ring

omit [NeZero (Module.finrank Real E)] in
private theorem coeff_lag_int
    {L : Real} (hL : 0 ≤ L) (B : Real → E → E →L[Real] E)
    (u v : timeH1 E L) (C : NNReal)
    (hcont : ContinuousOn
      (fun q : Real × Real ↦ B q.2 (u.toFun q.2 + q.1 • v.toFun q.2))
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L))
    (hbound : ∀ q ∈ Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L,
      ‖B q.2 (u.toFun q.2 + q.1 • v.toFun q.2)‖ ≤ (C : Real)) :
    ∀ c ∈ Icc (-1 : Real) 1,
      IntervalIntegrable
        (fun r ↦ inner Real
          (B r ((u + c • v).toFun r) ((u + c • v).deriv r))
          ((u + c • v).deriv r)) volume 0 L := by
  intro c hc
  let wc : timeH1 E L := u + c • v
  have hAc : ContinuousOn
      (fun r ↦ B r (u.toFun r + c • v.toFun r)) (Icc (0 : Real) L) :=
    hcont.comp (continuousOn_const.prodMk continuousOn_id)
      (fun r hr ↦ ⟨hc, hr⟩)
  have hAcMeas : AEStronglyMeasurable (fun r ↦ B r (wc.toFun r))
      (timeMeasure L) := by
    have heq : EqOn (fun r ↦ B r (u.toFun r + c • v.toFun r))
        (fun r ↦ B r (wc.toFun r)) (Icc (0 : Real) L) := by
      intro r hr
      simp only [wc, timeH1.toFun_add u (c • v) hr,
        timeH1.toFun_smul c v hr]
    simpa only [timeMeasure] using
      (hAc.congr heq.symm).aestronglyMeasurable measurableSet_Icc
  have hAcb : ∀ᵐ r ∂timeMeasure L, ‖B r (wc.toFun r)‖ ≤ (C : Real) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simp only [wc, timeH1.toFun_add u (c • v) hr,
      timeH1.toFun_smul c v hr]
    exact hbound (c, r) ⟨hc, hr⟩
  exact timeQuad_int (fun r ↦ B r (wc.toFun r))
    hAcMeas C hAcb hL wc.deriv

omit [NeZero (Module.finrank Real E)] in
private theorem coeff_lag_meas
    {L : Real} (hL : 0 ≤ L) (B : Real → E → E →L[Real] E)
    (u v : timeH1 E L)
    (hcont : ContinuousOn
      (fun q : Real × Real ↦ B q.2 (u.toFun q.2 + q.1 • v.toFun q.2))
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)) :
    ∀ᶠ c in nhds (0 : Real), AEStronglyMeasurable
      (coeffLineLag B u v c) (volume.restrict (uIoc (0 : Real) L)) := by
  filter_upwards [Icc_mem_nhds (by norm_num : (-1 : Real) < 0)
    (by norm_num : (0 : Real) < 1)] with c hc
  have hAc : ContinuousOn
      (fun r ↦ B r (u.toFun r + c • v.toFun r)) (Icc (0 : Real) L) :=
    hcont.comp (continuousOn_const.prodMk continuousOn_id)
      (fun r hr ↦ ⟨hc, hr⟩)
  have hAcMeas : AEStronglyMeasurable
      (fun r ↦ B r (u.toFun r + c • v.toFun r)) (timeMeasure L) := by
    simpa only [timeMeasure] using
      hAc.aestronglyMeasurable measurableSet_Icc
  have hpMeas : AEStronglyMeasurable
      (fun r ↦ u.deriv r + c • v.deriv r) (timeMeasure L) :=
    (Lp.aestronglyMeasurable u.deriv).add
      ((Lp.aestronglyMeasurable v.deriv).const_smul c)
  have heval : Continuous (fun q : (E →L[Real] E) × E ↦ q.1 q.2) := by
    fun_prop
  have hinner : Continuous (fun q : E × E ↦ inner Real q.1 q.2) := by
    fun_prop
  have hm := hinner.comp_aestronglyMeasurable
    (AEStronglyMeasurable.prodMk
      (heval.comp_aestronglyMeasurable
        (AEStronglyMeasurable.prodMk hAcMeas hpMeas)) hpMeas)
  simp only [timeMeasure] at hm
  rw [uIoc_of_le hL, restrict_Ioc_eq_restrict_Icc]
  refine hm.congr (Eventually.of_forall fun r ↦ ?_)
  rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem coeff_int_deriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 ≤ L) (u v : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hbuf : MapsTo
      (fun q : Real × Real ↦ u.toFun q.2 + q.1 • v.toFun q.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    IntervalIntegrable
        (coeffLineDeriv
          (lWeakCoeff (I := I) S T a p)
          (lWeakCoeffD (I := I) S T a p) u v 0) volume 0 L ∧
      HasDerivAt
      (fun c : Real ↦
        timeCoeffAction (lWeakCoeff (I := I) S T a p) (u + c • v))
      (∫ r in (0 : Real)..L,
        coeffLineDeriv
          (lWeakCoeff (I := I) S T a p)
          (lWeakCoeffD (I := I) S T a p) u v 0 r) 0 := by
  have hfin : 0 < Module.finrank Real E :=
    Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  let : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := Real) (M := E) hfin
  classical
  let K : Set (Real × Real) :=
    Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L
  let U : Set (Real × E) :=
    D.regular ×ˢ interior (extChartAt I p).target
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let pos : Real × Real → E :=
    fun q ↦ u.toFun q.2 + q.1 • v.toFun q.2
  have htau : ContinuousOn (fun q : Real × Real ↦ tau q.2) K := by
    exact continuousOn_const.sub
      ((continuousOn_const.add continuousOn_snd).pow 2)
  have hpos : ContinuousOn pos K := by
    exact (u.continuousOn_toFun.comp continuousOn_snd fun q hq ↦ hq.2).add
      (continuousOn_fst.smul
        (v.continuousOn_toFun.comp continuousOn_snd fun q hq ↦ hq.2))
  have hpair : ContinuousOn
      (fun q : Real × Real ↦ (tau q.2, pos q)) K := htau.prodMk hpos
  have hpair_mem : MapsTo (fun q : Real × Real ↦ (tau q.2, pos q)) K U := by
    intro q hq
    exact ⟨hreg q.2 hq.2, hbuf hq⟩
  have hUopen : IsOpen U := D.regular_isOpen.prod isOpen_interior
  have hGram : ContDiffOn Real ∞
      (chartGramOp (I := I) S.family p) U := by
    simpa only [U] using chartGramOp_smooth (I := I) hS.smoothMetric p
      (K := interior (extChartAt I p).target) Subset.rfl
  have hGramFd : ContinuousOn
      (fderiv Real (chartGramOp (I := I) S.family p)) U :=
    hGram.continuousOn_fderiv_of_isOpen hUopen (by simp)
  have hBJoint : ContinuousOn
      (fun q : Real × Real ↦
        lWeakCoeff (I := I) S T a p q.2 (pos q)) K := by
    exact (hGram.continuousOn.comp hpair hpair_mem).const_smul (1 / 2 : Real)
  have hpost : Continuous
      (fun A : (Real × E) →L[Real] (E →L[Real] E) ↦
        A.comp (ContinuousLinearMap.inr Real Real E)) := by
    fun_prop
  have hDBJoint : ContinuousOn
      (fun q : Real × Real ↦
        lWeakCoeffD (I := I) S T a p q.2 (pos q)) K := by
    exact (hpost.comp_continuousOn (hGramFd.comp hpair hpair_mem)).const_smul
      (1 / 2 : Real)
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hBNorm : ContinuousOn
      (fun q ↦ ‖lWeakCoeff (I := I) S T a p q.2 (pos q)‖) K :=
    continuous_norm.comp_continuousOn hBJoint
  obtain ⟨CB₀, hCB₀⟩ := hKcompact.bddAbove_image hBNorm
  let CB : Real := max CB₀ 0
  have hCB0 : 0 ≤ CB := le_max_right CB₀ 0
  have hCB : ∀ q ∈ K,
      ‖lWeakCoeff (I := I) S T a p q.2 (pos q)‖ ≤ CB := by
    intro q hq
    exact (hCB₀ ⟨q, hq, rfl⟩).trans (le_max_left CB₀ 0)
  obtain ⟨CD, hCD0, hCD⟩ := bilin_cont_bound K hKcompact
    (fun q ↦ lWeakCoeffD (I := I) S T a p q.2 (pos q)) hDBJoint
  obtain ⟨V₀, hV₀⟩ := isCompact_Icc.bddAbove_image
    v.continuousOn_toFun.norm
  let V : Real := max V₀ 0
  have hV0 : 0 ≤ V := le_max_right V₀ 0
  have hV : ∀ r ∈ Icc (0 : Real) L, ‖v.toFun r‖ ≤ V := by
    intro r hr
    exact (hV₀ ⟨r, hr, rfl⟩).trans (le_max_left V₀ 0)
  have hB_on : ∀ᵐ r ∂volume, r ∈ uIoc (0 : Real) L →
      ∀ c ∈ Icc (-1 : Real) 1,
        HasFDerivAt (lWeakCoeff (I := I) S T a p r)
          (lWeakCoeffD (I := I) S T a p r
            (u.toFun r + c • v.toFun r))
          (u.toFun r + c • v.toFun r) := by
    filter_upwards [] with r hr c hc
    have hr' : r ∈ Icc (0 : Real) L := by
      simpa only [uIcc_of_le hL] using uIoc_subset_uIcc hr
    have hchart : u.toFun r + c • v.toFun r ∈
        interior (extChartAt I p).target :=
      hbuf (show (c, r) ∈ K from ⟨hc, hr'⟩)
    have hq : (tau r, u.toFun r + c • v.toFun r) ∈ U := by
      exact ⟨hreg r hr', hchart⟩
    have hfull := (hGram.contDiffAt (hUopen.mem_nhds hq)).differentiableAt
      (by simp) |>.hasFDerivAt
    have hinr : HasFDerivAt
        (fun x : E ↦ (tau r, x)) (ContinuousLinearMap.inr Real Real E)
        (u.toFun r + c • v.toFun r) :=
      (hasFDerivAt_const (𝕜 := Real) (x := u.toFun r + c • v.toFun r)
        (c := tau r)).prodMk (hasFDerivAt_id (u.toFun r + c • v.toFun r))
    with_unfolding_all exact
      (hfull.comp (u.toFun r + c • v.toFun r) hinr).const_smul (1 / 2 : Real)
  have hself_on : ∀ᵐ r ∂volume, r ∈ uIoc (0 : Real) L →
      ∀ c ∈ Icc (-1 : Real) 1,
        IsSelfAdjoint (lWeakCoeff (I := I) S T a p r
          (u.toFun r + c • v.toFun r)) := by
    exact Eventually.of_forall fun r _ c _ ↦ by
      rw [lWeakCoeff]
      exact (IsSelfAdjoint.all (1 / 2 : Real)).smul
        (chartGramOp_self (I := I) S.family p
          (T - (a + r) ^ 2, u.toFun r + c • v.toFun r))
  let CBn : NNReal := ⟨CB, hCB0⟩
  have hlagInt := coeff_lag_int hL
    (lWeakCoeff (I := I) S T a p) u v CBn hBJoint
    (fun q hq ↦ by
      change ‖lWeakCoeff (I := I) S T a p q.2
        (u.toFun q.2 + q.1 • v.toFun q.2)‖ ≤ CB
      exact hCB q hq)
  have hlineMeas : ∀ᶠ c in nhds (0 : Real),
      AEStronglyMeasurable
        (coeffLineLag (lWeakCoeff (I := I) S T a p) u v c)
        (volume.restrict (uIoc (0 : Real) L)) :=
    coeff_lag_meas hL (lWeakCoeff (I := I) S T a p) u v hBJoint
  have hA0 : AEStronglyMeasurable
      (fun r ↦ lWeakCoeff (I := I) S T a p r (u.toFun r))
      (timeMeasure L) := by
    have hc : ContinuousOn
        (fun r ↦ lWeakCoeff (I := I) S T a p r (pos (0, r)))
        (Icc (0 : Real) L) :=
      cont_zero_slice hBJoint
    simpa only [timeMeasure, pos, zero_smul, add_zero] using
      hc.aestronglyMeasurable measurableSet_Icc
  have hA0b : ∀ᵐ r ∂timeMeasure L,
      ‖lWeakCoeff (I := I) S T a p r (u.toFun r)‖ ≤ (CBn : Real) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    change ‖lWeakCoeff (I := I) S T a p r (u.toFun r)‖ ≤ CB
    have h := hCB (0, r) ⟨by norm_num, hr⟩
    simpa only [pos, zero_smul, add_zero] using h
  have hint : IntervalIntegrable
      (coeffLineLag (lWeakCoeff (I := I) S T a p) u v 0) volume 0 L := by
    refine (timeQuad_int
        (fun r ↦ lWeakCoeff (I := I) S T a p r (u.toFun r))
        hA0 CBn hA0b hL u.deriv).congr ?_
    intro r _
    simp only [coeffLineLag, zero_smul, add_zero]
  have hD0Meas : AEStronglyMeasurable
      (fun r ↦ lWeakCoeffD (I := I) S T a p r (u.toFun r))
      (timeMeasure L) := by
    have hc : ContinuousOn
        (fun r ↦ lWeakCoeffD (I := I) S T a p r (pos (0, r)))
        (Icc (0 : Real) L) :=
      cont_zero_slice hDBJoint
    simpa only [timeMeasure, pos, zero_smul, add_zero] using
      hc.aestronglyMeasurable measurableSet_Icc
  have hdlineMeas : AEStronglyMeasurable
      (coeffLineDeriv
        (lWeakCoeff (I := I) S T a p)
        (lWeakCoeffD (I := I) S T a p) u v 0)
      (volume.restrict (uIoc (0 : Real) L)) := by
    have hpMeas := Lp.aestronglyMeasurable u.deriv
    have hvMeas : AEStronglyMeasurable v.toFun (timeMeasure L) := by
      simpa only [timeMeasure] using
        v.continuousOn_toFun.aestronglyMeasurable measurableSet_Icc
    have hvdMeas := Lp.aestronglyMeasurable v.deriv
    have hcfCont : Continuous
        (fun q : (E →L[Real] (E →L[Real] E)) × E ↦
          coeffForce q.1 q.2) := by
      unfold coeffForce
      fun_prop
    have hforce := hcfCont.comp_aestronglyMeasurable
      (hD0Meas.prodMk hpMeas)
    have hBvec : AEStronglyMeasurable
        (fun r ↦ lWeakCoeff (I := I) S T a p r (u.toFun r) (u.deriv r))
        (timeMeasure L) := by
      have heval : Continuous (fun q : (E →L[Real] E) × E ↦ q.1 q.2) := by
        fun_prop
      exact heval.comp_aestronglyMeasurable (hA0.prodMk hpMeas)
    have hinner : Continuous (fun q : E × E ↦ inner Real q.1 q.2) := by
      fun_prop
    have hfirst := hinner.comp_aestronglyMeasurable (hforce.prodMk hvMeas)
    have hsecond := (hinner.comp_aestronglyMeasurable
      (hBvec.prodMk hvdMeas)).const_mul 2
    have hm := hfirst.add hsecond
    have hm' : AEStronglyMeasurable
        (fun r ↦
          inner Real
              (coeffForce
                (lWeakCoeffD (I := I) S T a p r (u.toFun r)) (u.deriv r))
              (v.toFun r) +
            2 * inner Real
              (lWeakCoeff (I := I) S T a p r (u.toFun r) (u.deriv r))
              (v.deriv r))
        (volume.restrict (uIoc (0 : Real) L)) := by
      simp only [timeMeasure] at hm
      rw [uIoc_of_le hL, restrict_Ioc_eq_restrict_Icc]
      refine hm.congr (Eventually.of_forall fun r ↦ ?_)
      rfl
    refine hm'.congr (Eventually.of_forall fun r ↦ ?_)
    simp only [coeffLineDeriv, zero_smul, add_zero]
  let C : Real := 2 * CD * V + 3 * CB
  let bound : Real → Real := fun r ↦
    C * (‖u.deriv r‖ ^ 2 + ‖v.deriv r‖ ^ 2)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hbound : ∀ᵐ r ∂volume, r ∈ uIoc (0 : Real) L →
      ∀ c ∈ Icc (-1 : Real) 1,
        ‖coeffLineDeriv
          (lWeakCoeff (I := I) S T a p)
          (lWeakCoeffD (I := I) S T a p) u v c r‖ ≤ bound r := by
    filter_upwards [] with r hr c hc
    have hr' : r ∈ Icc (0 : Real) L := by
      simpa only [uIcc_of_le hL] using uIoc_subset_uIcc hr
    have hcabs : ‖c‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      exact hc
    let q : Real × Real := (c, r)
    let z : E := u.deriv r + c • v.deriv r
    have hz : ‖z‖ ≤ ‖u.deriv r‖ + ‖v.deriv r‖ := by
      calc
        ‖z‖ ≤ ‖u.deriv r‖ + ‖c • v.deriv r‖ := norm_add_le _ _
        _ = ‖u.deriv r‖ + ‖c‖ * ‖v.deriv r‖ := by rw [norm_smul]
        _ ≤ ‖u.deriv r‖ + 1 * ‖v.deriv r‖ := by gcongr
        _ = ‖u.deriv r‖ + ‖v.deriv r‖ := by ring
    have hb := hCB q ⟨hc, hr'⟩
    have hvb := hV r hr'
    have hforce :
        ‖inner Real
          (coeffForce
            (lWeakCoeffD (I := I) S T a p r (pos q)) z)
          (v.toFun r)‖ ≤
          CD * (‖u.deriv r‖ + ‖v.deriv r‖) ^ 2 * V := by
      rw [coeffForce_apply]
      calc
        ‖inner Real
            (lWeakCoeffD (I := I) S T a p r (pos q) (v.toFun r) z) z‖ ≤
            ‖lWeakCoeffD (I := I) S T a p r (pos q) (v.toFun r) z‖ *
              ‖z‖ := norm_inner_le_norm _ _
        _ ≤ (CD * ‖v.toFun r‖ * ‖z‖) * ‖z‖ := by
          gcongr
          exact hCD q ⟨hc, hr'⟩ (v.toFun r) z
        _ ≤ (CD * V * (‖u.deriv r‖ + ‖v.deriv r‖)) *
              (‖u.deriv r‖ + ‖v.deriv r‖) := by gcongr
        _ = (CD * (‖u.deriv r‖ + ‖v.deriv r‖) ^ 2) * V := by ring
        _ = CD * (‖u.deriv r‖ + ‖v.deriv r‖) ^ 2 * V := rfl
    have hmom :
        ‖2 * inner Real
          (lWeakCoeff (I := I) S T a p r (pos q) z) (v.deriv r)‖ ≤
          2 * CB * (‖u.deriv r‖ + ‖v.deriv r‖) * ‖v.deriv r‖ := by
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
      calc
        2 * ‖inner Real
            (lWeakCoeff (I := I) S T a p r (pos q) z) (v.deriv r)‖ ≤
            2 * (‖lWeakCoeff (I := I) S T a p r (pos q) z‖ *
              ‖v.deriv r‖) := by gcongr; exact norm_inner_le_norm _ _
        _ ≤ 2 * ((‖lWeakCoeff (I := I) S T a p r (pos q)‖ * ‖z‖) *
              ‖v.deriv r‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ 2 * ((CB * (‖u.deriv r‖ + ‖v.deriv r‖)) *
              ‖v.deriv r‖) := by gcongr
        _ = 2 * CB * (‖u.deriv r‖ + ‖v.deriv r‖) * ‖v.deriv r‖ := by ring
    change ‖inner Real
        (coeffForce
          (lWeakCoeffD (I := I) S T a p r (pos q)) z) (v.toFun r) +
      2 * inner Real
        (lWeakCoeff (I := I) S T a p r (pos q) z) (v.deriv r)‖ ≤ bound r
    have hsumSq : (‖u.deriv r‖ + ‖v.deriv r‖) ^ 2 ≤
        2 * (‖u.deriv r‖ ^ 2 + ‖v.deriv r‖ ^ 2) := by
      nlinarith [sq_nonneg (‖u.deriv r‖ - ‖v.deriv r‖)]
    have hforceQuad :
        CD * (‖u.deriv r‖ + ‖v.deriv r‖) ^ 2 * V ≤
          2 * CD * V * (‖u.deriv r‖ ^ 2 + ‖v.deriv r‖ ^ 2) := by
      calc
        CD * (‖u.deriv r‖ + ‖v.deriv r‖) ^ 2 * V =
            (CD * V) * (‖u.deriv r‖ + ‖v.deriv r‖) ^ 2 := by ring
        _ ≤ (CD * V) *
            (2 * (‖u.deriv r‖ ^ 2 + ‖v.deriv r‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsumSq (mul_nonneg hCD0 hV0)
        _ = _ := by ring
    have hcrossBase :
        2 * (‖u.deriv r‖ + ‖v.deriv r‖) * ‖v.deriv r‖ ≤
          3 * (‖u.deriv r‖ ^ 2 + ‖v.deriv r‖ ^ 2) := by
      nlinarith [sq_nonneg (‖u.deriv r‖ - ‖v.deriv r‖),
        sq_nonneg ‖u.deriv r‖]
    have hmomQuad :
        2 * CB * (‖u.deriv r‖ + ‖v.deriv r‖) * ‖v.deriv r‖ ≤
          3 * CB * (‖u.deriv r‖ ^ 2 + ‖v.deriv r‖ ^ 2) := by
      calc
        2 * CB * (‖u.deriv r‖ + ‖v.deriv r‖) * ‖v.deriv r‖ =
            CB * (2 * (‖u.deriv r‖ + ‖v.deriv r‖) * ‖v.deriv r‖) := by ring
        _ ≤ CB * (3 * (‖u.deriv r‖ ^ 2 + ‖v.deriv r‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hcrossBase hCB0
        _ = _ := by ring
    calc
      _ ≤ ‖inner Real
          (coeffForce
            (lWeakCoeffD (I := I) S T a p r (pos q)) z) (v.toFun r)‖ +
          ‖2 * inner Real
            (lWeakCoeff (I := I) S T a p r (pos q) z) (v.deriv r)‖ :=
        norm_add_le _ _
      _ ≤ CD * (‖u.deriv r‖ + ‖v.deriv r‖) ^ 2 * V +
          2 * CB * (‖u.deriv r‖ + ‖v.deriv r‖) * ‖v.deriv r‖ :=
        add_le_add hforce hmom
      _ ≤ 2 * CD * V * (‖u.deriv r‖ ^ 2 + ‖v.deriv r‖ ^ 2) +
          3 * CB * (‖u.deriv r‖ ^ 2 + ‖v.deriv r‖ ^ 2) :=
        add_le_add hforceQuad hmomQuad
      _ = bound r := by
        dsimp only [bound, C]
        ring
  have huSq : Integrable (fun r ↦ ‖u.deriv r‖ ^ 2) (timeMeasure L) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u.deriv)).mp
      (Lp.memLp u.deriv)
  have hvSq : Integrable (fun r ↦ ‖v.deriv r‖ ^ 2) (timeMeasure L) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v.deriv)).mp
      (Lp.memLp v.deriv)
  have hboundInt : IntervalIntegrable bound volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL]
    with_unfolding_all exact (huSq.add hvSq).const_mul C
  have hmain := timeCoeff_line_on hL
    (lWeakCoeff (I := I) S T a p)
    (lWeakCoeffD (I := I) S T a p) u v hB_on hself_on bound
    hlineMeas hint hdlineMeas hbound hboundInt
  exact hmain

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lWeakCoeff_line
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 ≤ L) (u v : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hbuf : MapsTo
      (fun q : Real × Real ↦ u.toFun q.2 + q.1 • v.toFun q.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    (∀ c ∈ Icc (-1 : Real) 1, IntervalIntegrable
      (fun r ↦ inner Real
        (lWeakCoeff (I := I) S T a p r ((u + c • v).toFun r)
          ((u + c • v).deriv r))
        ((u + c • v).deriv r)) volume 0 L) ∧
      IntervalIntegrable
          (coeffLineDeriv
            (lWeakCoeff (I := I) S T a p)
            (lWeakCoeffD (I := I) S T a p) u v 0) volume 0 L ∧
        HasDerivAt
        (fun c : Real ↦
          timeCoeffAction (lWeakCoeff (I := I) S T a p) (u + c • v))
        (∫ r in (0 : Real)..L,
          coeffLineDeriv
            (lWeakCoeff (I := I) S T a p)
            (lWeakCoeffD (I := I) S T a p) u v 0 r) 0 := by
  have hfin : 0 < Module.finrank Real E :=
    Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  let : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := Real) (M := E) hfin
  let K : Set (Real × Real) :=
    Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L
  let U : Set (Real × E) :=
    D.regular ×ˢ interior (extChartAt I p).target
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let pos : Real × Real → E :=
    fun q ↦ u.toFun q.2 + q.1 • v.toFun q.2
  have hpair : ContinuousOn (fun q : Real × Real ↦ (tau q.2, pos q)) K :=
    (continuousOn_const.sub
      ((continuousOn_const.add continuousOn_snd).pow 2)).prodMk
      ((u.continuousOn_toFun.comp continuousOn_snd fun q hq ↦ hq.2).add
        (continuousOn_fst.smul
          (v.continuousOn_toFun.comp continuousOn_snd fun q hq ↦ hq.2)))
  have hpair_mem : MapsTo (fun q : Real × Real ↦ (tau q.2, pos q)) K U := by
    intro q hq
    exact ⟨hreg q.2 hq.2, hbuf hq⟩
  have hGram : ContDiffOn Real ∞ (chartGramOp (I := I) S.family p) U := by
    simpa only [U] using chartGramOp_smooth (I := I) hS.smoothMetric p
      (K := interior (extChartAt I p).target) Subset.rfl
  have hBJoint : ContinuousOn
      (fun q : Real × Real ↦ lWeakCoeff (I := I) S T a p q.2 (pos q)) K :=
    (hGram.continuousOn.comp hpair hpair_mem).const_smul (1 / 2 : Real)
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hBNorm : ContinuousOn
      (fun q ↦ ‖lWeakCoeff (I := I) S T a p q.2 (pos q)‖) K :=
    continuous_norm.comp_continuousOn hBJoint
  obtain ⟨CB₀, hCB₀⟩ := hKcompact.bddAbove_image hBNorm
  let CB : Real := max CB₀ 0
  let CBn : NNReal := ⟨CB, le_max_right CB₀ 0⟩
  have hlag := coeff_lag_int hL (lWeakCoeff (I := I) S T a p) u v CBn
    hBJoint (fun q hq ↦ by
      exact (hCB₀ ⟨q, hq, rfl⟩).trans (le_max_left CB₀ 0))
  exact ⟨hlag, coeff_int_deriv (I := I) S hS T a p hL u v hreg hbuf⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem lWeak_pos_pair
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) (w : E) :
    T - (a + r) ^ 2 ∈ D.regular →
    u.toFun r ∈ interior (extChartAt I p).target →
    inner Real
        (coeffForce (lWeakCoeffD (I := I) S T a p r (u.toFun r))
          (u.deriv r)) w +
      lWeakScalCov (I := I) S T a p r (u.toFun r) w =
      inner Real (lChartForce (I := I) S T a p u r) w := by
  intro ht hx
  let f : M → Real := S.scalar (T - (a + r) ^ 2)
  let y : M := (extChartAt I p).symm (u.toFun r)
  have hxt : u.toFun r ∈ (extChartAt I p).target := interior_subset hx
  have hysrc : y ∈ (chartAt H p).source := by
    have hyext : y ∈ (extChartAt I p).source :=
      (extChartAt I p).map_target hxt
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hyext
  have hright : extChartAt I p y = u.toFun r :=
    (extChartAt I p).right_inv hxt
  have hf : ContMDiff I 𝓘(Real, Real) ∞ f := by
    simpa only [f] using scalarSmoothOfSol (I := I) S (T - (a + r) ^ 2)
  have hcovBasis (i : Fin (Module.finrank Real E)) :
      chartScalCov (I := I) S p (T - (a + r) ^ 2, u.toFun r)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) =
        mvfderiv (I := I) f y
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i y) := by
    rw [chartScalCov_apply (I := I) S hS p ht hx]
    rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
    rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt
      (I := I) p (hf.mdifferentiableAt (by simp)) hysrc
        (by simpa only [hright] using hx) i]
    simp only [DifferentialGeometry.Tensor.Coordinates.partialDeriv, hright, f]
    rfl
  have hcovDecomp :
      chartScalCov (I := I) S p (T - (a + r) ^ 2, u.toFun r) w =
        ∑ i : Fin (Module.finrank Real E),
          mvfderiv (I := I) f y
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i y) *
            chartCoordCLM E i w := by
    conv_lhs => rw [← (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr w]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, hcovBasis]
    have hc : chartCoordCLM E i w = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w i := rfl
    rw [hc, mul_comm]
  have hscal :
      lWeakScalCov (I := I) S T a p r (u.toFun r) w =
        ∑ i : Fin (Module.finrank Real E),
          2 * (a + r) ^ 2 *
              mvfderiv (I := I) (S.scalar (T - (a + r) ^ 2))
                ((extChartAt I p).symm (u.toFun r))
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i
                  ((extChartAt I p).symm (u.toFun r))) *
            chartCoordCLM E i w := by
    rw [lWeakScalCov, smul_apply, smul_eq_mul, hcovDecomp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [f, y]
    ring
  rw [lChartForce_inner, coeffForce_apply]
  rw [lChartPosDeriv]
  simp only [sum_apply, smul_apply,
    smul_eq_mul, lWeakCoeffD, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  rw [hscal]
  change
    inner Real
          (((1 / 2 : Real) •
            (fderiv Real (chartGramOp (I := I) S.family p)
              (T - (a + r) ^ 2, u.toFun r)) (0, w)) (u.deriv r))
          (u.deriv r) +
        ∑ i : Fin (Module.finrank Real E),
          2 * (a + r) ^ 2 *
              mvfderiv (I := I) (S.scalar (T - (a + r) ^ 2))
                ((extChartAt I p).symm (u.toFun r))
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i
                  ((extChartAt I p).symm (u.toFun r))) *
            chartCoordCLM E i w =
      ∑ i : Fin (Module.finrank Real E),
        (inner Real
            (((1 / 2 : Real) •
              (fderiv Real (chartGramOp (I := I) S.family p)
                (T - (a + r) ^ 2, u.toFun r))
                (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (u.deriv r))
            (u.deriv r) +
          2 * (a + r) ^ 2 *
            mvfderiv (I := I) (S.scalar (T - (a + r) ^ 2))
              ((extChartAt I p).symm (u.toFun r))
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i
                ((extChartAt I p).symm (u.toFun r)))) *
          chartCoordCLM E i w
  have hsplit :
      (∑ i : Fin (Module.finrank Real E),
        (inner Real
            (((1 / 2 : Real) •
              (fderiv Real (chartGramOp (I := I) S.family p)
                (T - (a + r) ^ 2, u.toFun r))
                (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (u.deriv r))
            (u.deriv r) +
          2 * (a + r) ^ 2 *
            mvfderiv (I := I) (S.scalar (T - (a + r) ^ 2))
              ((extChartAt I p).symm (u.toFun r))
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i
                ((extChartAt I p).symm (u.toFun r)))) *
          chartCoordCLM E i w) =
        (∑ i : Fin (Module.finrank Real E),
          inner Real
              (((1 / 2 : Real) •
                (fderiv Real (chartGramOp (I := I) S.family p)
                  (T - (a + r) ^ 2, u.toFun r))
                  (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (u.deriv r))
              (u.deriv r) * chartCoordCLM E i w) +
        ∑ i : Fin (Module.finrank Real E),
          2 * (a + r) ^ 2 *
              mvfderiv (I := I) (S.scalar (T - (a + r) ^ 2))
                ((extChartAt I p).symm (u.toFun r))
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i
                  ((extChartAt I p).symm (u.toFun r))) *
            chartCoordCLM E i w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_mul]
  rw [hsplit]
  congr 1
  · have hcoord (i : Fin (Module.finrank Real E)) :
        chartCoordCLM E i w = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w i := rfl
    simp_rw [hcoord]
    conv_lhs => rw [← (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr w]
    simp only [smul_apply, real_inner_smul_left]
    change (1 / 2 : Real) * inner Real
        (((fderiv Real (chartGramOp (I := I) S.family p)
          (T - (a + r) ^ 2, u.toFun r)).comp
            (ContinuousLinearMap.inr Real Real E))
          (∑ i, ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w i) • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (u.deriv r))
        (u.deriv r) = _
    rw [map_sum, sum_apply, sum_inner]
    simp only [map_smul, smul_apply,
      real_inner_smul_left]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inr_apply]
    ring

omit [SigmaCompactSpace M] in
theorem lChartAct_line
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 ≤ L) (u v : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hbuf : MapsTo
      (fun q : Real × Real ↦ u.toFun q.2 + q.1 • v.toFun q.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    HasDerivAt (fun c : Real ↦ lChartAct S T a p (u + c • v))
      (∫ r in (0 : Real)..L,
        inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
          inner Real
            (chartGramOp (I := I) S.family p
              (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
            (v.deriv r)) 0 := by
  have hkin := lWeakCoeff_line (I := I) S hS T a p hL u v hreg hbuf
  have hpot := lWeakScal_line (I := I) S hS T a p hL u v hreg hbuf
  have hsum := hkin.2.2.add hpot.2.2
  have hsplit (c : Real) (hc : c ∈ Icc (-1 : Real) 1) :
      lChartAct S T a p (u + c • v) =
        timeCoeffAction (lWeakCoeff (I := I) S T a p) (u + c • v) +
          ∫ r in (0 : Real)..L,
            lWeakScal (I := I) S T a p r ((u + c • v).toFun r) := by
    unfold lChartAct lChartLag timeCoeffAction
    change (∫ r in (0 : Real)..L,
      inner Real
          (lWeakCoeff (I := I) S T a p r ((u + c • v).toFun r)
            ((u + c • v).deriv r)) ((u + c • v).deriv r) +
        lWeakScal (I := I) S T a p r ((u + c • v).toFun r)) = _
    rw [intervalIntegral.integral_add (hkin.1 c hc) (hpot.1 c hc)]
  have heq : ∀ᶠ c in nhds (0 : Real),
      lChartAct S T a p (u + c • v) =
        timeCoeffAction (lWeakCoeff (I := I) S T a p) (u + c • v) +
          ∫ r in (0 : Real)..L,
            lWeakScal (I := I) S T a p r ((u + c • v).toFun r) := by
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : Real) < 0)
      (by norm_num : (0 : Real) < 1)] with c hc
    exact hsplit c hc
  have hder := hsum.congr_of_eventuallyEq heq
  refine hder.congr_deriv ?_
  rw [← intervalIntegral.integral_add hkin.2.1 hpot.2.1]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc (0 : Real) L := by
    simpa only [uIcc_of_le hL] using hr
  have hx : u.toFun r ∈ interior (extChartAt I p).target := by
    simpa only [zero_smul, add_zero] using
      hbuf (show ((0 : Real), r) ∈
        Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L from ⟨by norm_num, hr'⟩)
  simp only [coeffLineDeriv, zero_smul, add_zero]
  rw [← lWeak_pos_pair (I := I) S hS T a p u r (v.toFun r)
    (hreg r hr') hx]
  simp only [lWeakCoeff, smul_apply, real_inner_smul_left]
  ring

omit [SigmaCompactSpace M] in
theorem lChart_weak_euler
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hmin : IsLocalMinOn (lChartAct S T a p) (sameTimeEnds u) u) :
    IntegrableOn (lChartForce (I := I) S T a p u)
        (Icc (0 : Real) L) volume ∧
      ∀ v : timeH1 E L, v.init = 0 → v.toFun L = 0 →
        (∫ r in (0 : Real)..L,
          inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
            inner Real
              (chartGramOp (I := I) S.family p
                (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
              (v.deriv r)) = 0 := by
  refine ⟨lChartForce_int (I := I) S hS T a p hL u hreg hchart, ?_⟩
  intro v hv0 hvL
  let Ku : Set E := u.toFun '' Icc (0 : Real) L
  have hKuc : IsCompact Ku :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hKuchart : Ku ⊆ interior (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact hchart hr
  obtain ⟨δ, hδ, hδsub⟩ := hKuc.exists_cthickening_subset_open
    isOpen_interior hKuchart
  obtain ⟨V₀, hV₀⟩ := isCompact_Icc.bddAbove_image
    v.continuousOn_toFun.norm
  let V : Real := max V₀ 0
  have hV0 : 0 ≤ V := le_max_right V₀ 0
  have hV : ∀ r ∈ Icc (0 : Real) L, ‖v.toFun r‖ ≤ V := by
    intro r hr
    exact (hV₀ ⟨r, hr, rfl⟩).trans (le_max_left V₀ 0)
  let scale : Real := δ / (V + 1)
  have hden : 0 < V + 1 := by linarith
  have hscale : 0 < scale := div_pos hδ hden
  have hscaleV : scale * V ≤ δ := by
    calc
      scale * V ≤ scale * (V + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hscale.le
      _ = δ := by
        dsimp only [scale]
        field_simp
  let w : timeH1 E L := scale • v
  have hbuf : MapsTo
      (fun q : Real × Real ↦ u.toFun q.2 + q.1 • w.toFun q.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)
      (interior (extChartAt I p).target) := by
    intro q hq
    apply hδsub
    refine Metric.mem_cthickening_of_dist_le
      (u.toFun q.2 + q.1 • w.toFun q.2) (u.toFun q.2) δ Ku
      ⟨q.2, hq.2, rfl⟩ ?_
    rw [dist_eq_norm, add_sub_cancel_left,
      timeH1.toFun_smul scale v hq.2, smul_smul, norm_smul]
    have hc : ‖q.1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      exact hq.1
    have hs : ‖q.1 * scale‖ ≤ scale := by
      have hcabs : |q.1| ≤ 1 := by
        simpa only [Real.norm_eq_abs] using hc
      rw [norm_mul]
      simp only [Real.norm_eq_abs, abs_of_pos hscale]
      nlinarith [abs_nonneg q.1]
    calc
      ‖q.1 * scale‖ * ‖v.toFun q.2‖ ≤ scale * V := by
        exact mul_le_mul hs (hV q.2 hq.2) (norm_nonneg _) hscale.le
      _ ≤ δ := hscaleV
  have hw0 : w.init = 0 := by
    simp only [w, timeH1.init_smul, hv0, smul_zero]
  have hwL : w.toFun L = 0 := by
    rw [show w = scale • v from rfl,
      timeH1.toFun_smul scale v ⟨hL.le, le_rfl⟩, hvL, smul_zero]
  let line : Real → timeH1 E L := fun c ↦ u + c • w
  have hline0 : line 0 = u := by
    simp only [line, zero_smul, add_zero]
  have hmaps : univ ⊆ line ⁻¹' sameTimeEnds u := by
    intro c _
    constructor
    · simp only [line, timeH1.init_add, timeH1.init_smul,
        hw0, smul_zero, add_zero]
    · change (u + c • w).toFun L = u.toFun L
      rw [timeH1.toFun_add u (c • w) ⟨hL.le, le_rfl⟩,
        timeH1.toFun_smul c w ⟨hL.le, le_rfl⟩, hwL, smul_zero, add_zero]
  have hscalar : IsLocalMin (lChartAct S T a p ∘ line) 0 := by
    rw [← isLocalMinOn_univ_iff]
    have hmin' : IsLocalMinOn (lChartAct S T a p) (sameTimeEnds u) (line 0) := by
      simpa only [hline0] using hmin
    exact hmin'.comp_continuousOn hmaps
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (mem_univ (0 : Real))
  have hline := lChartAct_line (I := I) S hS T a p hL.le u w hreg hbuf
  have hzero := hscalar.deriv_eq_zero
  have hline' : HasDerivAt (lChartAct S T a p ∘ line)
      (∫ r in (0 : Real)..L,
        inner Real (lChartForce (I := I) S T a p u r) (w.toFun r) +
          inner Real
            (chartGramOp (I := I) S.family p
              (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
            (w.deriv r)) 0 := by
    with_unfolding_all exact hline
  rw [hline'.deriv] at hzero
  have hd : ⇑w.deriv =ᵐ[timeMeasure L]
      fun r ↦ scale • v.deriv r := by
    have heq : w.deriv = scale • v.deriv := by
      simp only [w, timeH1.deriv_smul]
    rw [heq]
    exact Lp.coeFn_smul scale v.deriv
  have hd' : ⇑w.deriv =ᵐ[volume.restrict (uIoc (0 : Real) L)]
      fun r ↦ scale • v.deriv r := by
    have hsub : uIoc (0 : Real) L ⊆ Icc (0 : Real) L := by
      simpa only [uIcc_of_le hL.le] using
        (uIoc_subset_uIcc : uIoc (0 : Real) L ⊆ uIcc (0 : Real) L)
    have hm := hd.filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    simpa only [timeMeasure] using hm
  have hscaled :
      (∫ r in (0 : Real)..L,
        inner Real (lChartForce (I := I) S T a p u r) (w.toFun r) +
          inner Real
            (chartGramOp (I := I) S.family p
              (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
            (w.deriv r)) =
        scale * (∫ r in (0 : Real)..L,
          inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
            inner Real
              (chartGramOp (I := I) S.family p
                (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
              (v.deriv r)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hd', ae_restrict_mem measurableSet_uIoc] with r hdr hr
    have hr' : r ∈ Icc (0 : Real) L := by
      simpa only [uIcc_of_le hL.le] using uIoc_subset_uIcc hr
    rw [show w = scale • v from rfl,
      timeH1.toFun_smul scale v hr', hdr]
    simp only [real_inner_smul_right]
    ring
  rw [hscaled] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hscale.ne'

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
