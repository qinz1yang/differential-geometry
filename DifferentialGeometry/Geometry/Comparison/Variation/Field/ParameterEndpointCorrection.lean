import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve
import DifferentialGeometry.Topology.Manifold.CurveExtension
import DifferentialGeometry.Topology.Manifold.SmoothInterval

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {P E H M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
private theorem chartCoord_mfderiv_parameter_apply_eq_fderiv
    {gamma : P → M} {z : P} (hgamma : MDifferentiableAt 𝓘(ℝ, P) I gamma z)
    (p : M) (hz : gamma z ∈ (chartAt H p).source) (Z : P) :
    ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (gamma z))
        ((mfderiv 𝓘(ℝ, P) I gamma z) Z) =
      (fderiv ℝ ((extChartAt I p) ∘ gamma) z) Z := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
    (x₀ := p) (x := gamma z) hz]
  have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) (gamma z) :=
    mdifferentiableAt_extChartAt (I := I) (x := p) hz
  have hchain :
      mfderiv 𝓘(ℝ, P) 𝓘(ℝ, E) ((extChartAt I p) ∘ gamma) z =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p) (gamma z)).comp
          (mfderiv 𝓘(ℝ, P) I gamma z) :=
    mfderiv_comp z hchart hgamma
  have heval := congrArg
    (fun L => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt I p (gamma z)))
      (L ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm Z))) hchain
  rw [mfderiv_eq_fderiv] at heval
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at heval
  exact heval.symm

omit [I.Boundaryless] in
private theorem raw_mfderiv_parameter_apply_eq_symmL_fderiv
    {gamma : P → M} {z : P} (hgamma : MDifferentiableAt 𝓘(ℝ, P) I gamma z)
    (p : M) (hz : gamma z ∈ (chartAt H p).source) (Z : P) :
    ((mfderiv 𝓘(ℝ, P) I gamma z) Z : E) =
      ((trivializationAt E (TangentSpace I) p).symmL ℝ (gamma z))
        ((fderiv ℝ ((extChartAt I p) ∘ gamma) z) Z) := by
  have hcoord := chartCoord_mfderiv_parameter_apply_eq_fderiv hgamma p hz Z
  have hbase : gamma z ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hz
  have hround :
      ((trivializationAt E (TangentSpace I) p).symmL ℝ (gamma z))
          (((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (gamma z))
            ((mfderiv 𝓘(ℝ, P) I gamma z) Z)) =
        ((mfderiv 𝓘(ℝ, P) I gamma z) Z) :=
    (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt
      (R := ℝ) hbase _
  exact hround.symm.trans (congrArg
    ((trivializationAt E (TangentSpace I) p).symmL ℝ (gamma z)) hcoord)

/-- Correct one endpoint of a family with a vector parameter, preserving its
central curve, its complete first derivative in the parameter, and a second
endpoint. The construction uses only a manifold chart and a time cutoff. -/
theorem correct_parameter_variation_endpoint [FiniteDimensional ℝ P]
    (f : P × ℝ → M) {U : Set P} (hU : IsOpen U) (h0 : (0 : P) ∈ U)
    (hf : ContMDiffOn 𝓘(ℝ, P × ℝ) I (8 : ℕ) f (U ×ˢ univ))
    (beta : P → M) (hb : ContMDiffOn 𝓘(ℝ, P) I (8 : ℕ) beta U)
    (c k : ℝ) (hck : c ≠ k) (hb0 : beta 0 = f (0, c))
    (hbv : (mfderiv 𝓘(ℝ, P) I beta 0 : P →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, P) I (fun e : P => f (e, c)) 0 : P →L[ℝ] E)) :
    ∃ V : Set P, IsOpen V ∧ (0 : P) ∈ V ∧ V ⊆ U ∧
      ∃ F : P × ℝ → M,
        ContMDiffOn 𝓘(ℝ, P × ℝ) I (8 : ℕ) F (V ×ˢ univ) ∧
        (∀ t, F (0, t) = f (0, t)) ∧
        (∀ t, (mfderiv 𝓘(ℝ, P) I (fun e : P => F (e, t)) 0 : P →L[ℝ] E) =
          (mfderiv 𝓘(ℝ, P) I (fun e : P => f (e, t)) 0 : P →L[ℝ] E)) ∧
        (∀ e ∈ V, F (e, c) = beta e) ∧
        (∀ e ∈ V, F (e, k) = f (e, k)) := by
  classical
  let p := f (0, c)
  let q := extChartAt I p p
  have hfAt (z : P × ℝ) (hz : z.1 ∈ U) :
      ContMDiffAt 𝓘(ℝ, P × ℝ) I (8 : ℕ) f z :=
    (hf z ⟨hz, mem_univ _⟩).contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)
  have hbAt : ContMDiffAt 𝓘(ℝ, P) I (8 : ℕ) beta 0 :=
    (hb 0 h0).contMDiffAt (hU.mem_nhds h0)
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := I) p) q (mem_extChartAt_target p)
  let r := eps / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hcoord : ContinuousAt (fun z : P × ℝ => extChartAt I p (f z)) (0, c) :=
    (continuousAt_extChartAt (I := I) p).comp (hfAt (0, c) h0).continuousAt
  have hgood : {z : P × ℝ | z.1 ∈ U ∧ f z ∈ (extChartAt I p).source ∧
      extChartAt I p (f z) ∈ Metric.ball q r} ∈ 𝓝 (0, c) := by
    filter_upwards [continuous_fst.continuousAt.eventually (hU.mem_nhds h0),
      (hfAt (0, c) h0).continuousAt.eventually
        ((isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)),
      hcoord.eventually (Metric.ball_mem_nhds q hr)] with z hz hsrc hq
    exact ⟨hz, hsrc, hq⟩
  obtain ⟨d, hd, hdgood⟩ := Metric.mem_nhds_iff.mp hgood
  have hbgood : {e : P | beta e ∈ (extChartAt I p).source ∧
      extChartAt I p (beta e) ∈ Metric.ball q r} ∈ 𝓝 0 := by
    have hbsource : beta 0 ∈ (extChartAt I p).source := by
      rw [hb0]; exact mem_extChartAt_source p
    have hbcoord : ContinuousAt (fun e => extChartAt I p (beta e)) 0 :=
      (continuousAt_extChartAt' hbsource).comp hbAt.continuousAt
    filter_upwards [hbAt.continuousAt.eventually
      ((isOpen_extChartAt_source (I := I) p).mem_nhds hbsource),
      hbcoord.eventually (by
        change Metric.ball q r ∈ 𝓝 (extChartAt I p (beta 0))
        rw [hb0]
        exact Metric.ball_mem_nhds q hr)] with e hsrc hq
    exact ⟨hsrc, hq⟩
  obtain ⟨db, hdb, hdbgood⟩ := Metric.mem_nhds_iff.mp hbgood
  let delta := min d db / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdeltaD : delta < d := (half_lt_self (lt_min hd hdb)).trans_le (min_le_left _ _)
  have hdeltaB : delta < db := (half_lt_self (lt_min hd hdb)).trans_le (min_le_right _ _)
  have heD (e : P) (he : e ∈ Metric.ball (0 : P) delta) : dist e 0 < d :=
    (Metric.mem_ball.mp he).trans hdeltaD
  have heB (e : P) (he : e ∈ Metric.ball (0 : P) delta) : dist e 0 < db :=
    (Metric.mem_ball.mp he).trans hdeltaB
  have h0d : (0 : P) ∈ Metric.ball (0 : P) delta := Metric.mem_ball_self hdelta
  let W := Metric.ball c d
  have hmem (e : P) (t : ℝ) (he : e ∈ Metric.ball (0 : P) delta) (ht : t ∈ W) :
      e ∈ U ∧ f (e, t) ∈ (extChartAt I p).source ∧
        extChartAt I p (f (e, t)) ∈ Metric.ball q r := by
    apply hdgood (a := (e, t))
    change dist (e, t) (0, c) < d
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨heD e he, ht⟩
  have hcW : c ∈ W := Metric.mem_ball_self hd
  have hsub : Metric.ball (0 : P) delta ⊆ U := fun e he => (hmem e c he hcW).1
  let radius := min d (dist k c)
  have hrad : 0 < radius := lt_min hd (dist_pos.mpr (Ne.symm hck))
  let cut : ContDiffBump c :=
    { rIn := radius / 4, rOut := radius / 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hcutk : cut k = 0 := cut.zero_of_le_dist (by
    change radius / 2 ≤ dist k c
    have := min_le_right d (dist k c)
    change radius ≤ dist k c at this
    linarith)
  let B : P → E := fun e => extChartAt I p (beta e) - extChartAt I p (f (e, c))
  let coord : P × ℝ → E := fun z => extChartAt I p (f z) + cut z.2 • B z.1
  let F : P × ℝ → M := fun z =>
    if z.2 ∈ W then (extChartAt I p).symm (coord z) else f z
  have htarget (e : P) (t : ℝ) (he : e ∈ Metric.ball (0 : P) delta) (ht : t ∈ W) :
      coord (e, t) ∈ (extChartAt I p).target := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hft := (hmem e t he ht).2.2
    have hfc := (hmem e c he hcW).2.2
    have hbe := (hdbgood (heB e he)).2
    rw [Metric.mem_ball, dist_eq_norm] at hft hfc hbe
    have hBd : ‖B e‖ < 2 * r := by
      calc
        ‖B e‖ = ‖(extChartAt I p (beta e) - q) - (extChartAt I p (f (e, c)) - q)‖ := by
          congr 1; dsimp only [B]; abel
        _ ≤ ‖extChartAt I p (beta e) - q‖ + ‖extChartAt I p (f (e, c)) - q‖ := norm_sub_le _ _
        _ < 2 * r := by linarith
    have hcutBd : ‖cut t • B e‖ ≤ ‖B e‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg cut.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) cut.le_one
    calc
      ‖coord (e, t) - q‖ = ‖(extChartAt I p (f (e, t)) - q) + cut t • B e‖ := by
        congr 1; dsimp only [coord]; abel
      _ ≤ ‖extChartAt I p (f (e, t)) - q‖ + ‖cut t • B e‖ := norm_add_le _ _
      _ < eps := by dsimp only [r] at *; linarith
  have hzero (e : P) (t : ℝ) (he : e ∈ Metric.ball (0 : P) delta) (hz : cut t = 0) :
      F (e, t) = f (e, t) := by
    dsimp only [F]
    split_ifs with ht
    · dsimp only [coord]; rw [hz, zero_smul, add_zero]
      exact (extChartAt I p).left_inv (hmem e t he ht).2.1
    · rfl
  have hchart {x : M} (hx : x ∈ (extChartAt I p).source) :
      ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I p) x :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)
  have hcoordAt (z : P × ℝ) (he : z.1 ∈ Metric.ball (0 : P) delta) (ht : z.2 ∈ W) :
      ContMDiffAt 𝓘(ℝ, P × ℝ) 𝓘(ℝ, E) (8 : ℕ) coord z := by
    have hfc : ContMDiffAt 𝓘(ℝ, P) I (8 : ℕ) (fun e => f (e, c)) z.1 :=
      (hfAt (z.1, c) (hsub he)).comp z.1 ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
    have hbeta := (hb z.1 (hsub he)).contMDiffAt (hU.mem_nhds (hsub he))
    have hbcoord := (hchart
      (hdbgood (heB z.1 he)).1).comp z.1 hbeta
    have hfcoord := (hchart
      (hmem z.1 c he hcW).2.1).comp z.1 hfc
    have hB : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, E) (8 : ℕ) B z.1 := by
      apply contMDiffAt_iff_contDiffAt.mpr
      exact (contMDiffAt_iff_contDiffAt.mp hbcoord).sub
        (contMDiffAt_iff_contDiffAt.mp hfcoord)
    exact ((hchart
      (hmem z.1 z.2 he ht).2.1).comp z (hfAt z (hsub he))).add
      (((cut.contDiff.comp contDiff_snd).of_le (by exact WithTop.coe_le_coe.mpr le_top : (8 : WithTop ℕ∞) ≤ ∞)).contMDiff.contMDiffAt.smul
        (hB.comp z contDiff_fst.contMDiff.contMDiffAt))
  have hFAt (z : P × ℝ) (he : z.1 ∈ Metric.ball (0 : P) delta) :
      ContMDiffAt 𝓘(ℝ, P × ℝ) I (8 : ℕ) F z := by
    by_cases ht : z.2 ∈ W
    · have hi := (contMDiffOn_extChartAt_symm (I := I) (n := (8 : ℕ)) p _
        (htarget z.1 z.2 he ht)).contMDiffAt
        ((isOpen_extChartAt_target (I := I) p).mem_nhds (htarget z.1 z.2 he ht))
      apply (hi.comp z (hcoordAt z he ht)).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.eventually (Metric.isOpen_ball.mem_nhds ht)] with y hy
      exact ite_eq_left (show y.2 ∈ W from hy)
    · have hout : radius / 2 < dist z.2 c := by
        have hn : d ≤ dist z.2 c := le_of_not_gt ht
        have hrD : radius ≤ d := min_le_left _ _
        linarith
      have hcutzero : ∀ᶠ t in 𝓝 z.2, cut t = 0 := by
        filter_upwards [(continuous_id.dist continuous_const).continuousAt.eventually (Ioi_mem_nhds hout)] with t ht
        exact cut.zero_of_le_dist ht.le
      apply (hfAt z (hsub he)).congr_of_eventuallyEq
      filter_upwards [continuous_fst.continuousAt.eventually (Metric.isOpen_ball.mem_nhds he),
        continuous_snd.continuousAt.tendsto.eventually hcutzero] with y hy hc
      exact hzero y.1 y.2 hy hc
  have hcenter (t : ℝ) : F (0, t) = f (0, t) := by
    dsimp only [F]
    split_ifs with ht
    · have hB0 : B 0 = 0 := by simp only [B, hb0, sub_self]
      dsimp only [coord]; rw [hB0, smul_zero, add_zero]
      exact (extChartAt I p).left_inv (hmem 0 t h0d ht).2.1
    · rfl
  have hfcAt : ContMDiffAt 𝓘(ℝ, P) I (8 : ℕ) (fun e => f (e, c)) 0 :=
    (hfAt (0, c) h0).comp 0 ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
  have hBd : HasFDerivAt B (0 : P →L[ℝ] E) 0 := by
    have hbcoord := (hchart
      (hdbgood (heB 0 h0d)).1).comp 0 hbAt
    have hfcoord := (hchart
      (hmem 0 c h0d hcW).2.1).comp 0 hfcAt
    have hderiv : fderiv ℝ (fun e : P => extChartAt I p (beta e)) 0 =
        fderiv ℝ (fun e : P => extChartAt I p (f (e, c))) 0 := by
      apply ContinuousLinearMap.ext
      intro Z
      change fderiv ℝ ((extChartAt I p) ∘ beta) 0 Z =
        fderiv ℝ ((extChartAt I p) ∘ (fun e : P => f (e, c))) 0 Z
      rw [← chartCoord_mfderiv_parameter_apply_eq_fderiv
        (hbAt.mdifferentiableAt (by norm_num)) p (by
          simpa only [extChartAt_source] using (hdbgood (heB 0 h0d)).1) Z,
        ← chartCoord_mfderiv_parameter_apply_eq_fderiv
        (hfcAt.mdifferentiableAt (by norm_num)) p (by
          simpa only [extChartAt_source] using (hmem 0 c h0d hcW).2.1) Z]
      erw [hb0, hbv]
    have hbD := (contMDiffAt_iff_contDiffAt.mp hbcoord).differentiableAt (by norm_num)
    have hfD := (contMDiffAt_iff_contDiffAt.mp hfcoord).differentiableAt (by norm_num)
    have hraw := hbD.hasFDerivAt.sub hfD.hasFDerivAt
    change HasFDerivAt B
      (fderiv ℝ (fun e : P => extChartAt I p (beta e)) 0 -
        fderiv ℝ (fun e : P => extChartAt I p (f (e, c))) 0) 0 at hraw
    rwa [hderiv, sub_self] at hraw
  have hfield (t : ℝ) :
      (mfderiv 𝓘(ℝ, P) I (fun e : P => F (e, t)) 0 : P →L[ℝ] E) =
        (mfderiv 𝓘(ℝ, P) I (fun e : P => f (e, t)) 0 : P →L[ℝ] E) := by
    by_cases ht : t ∈ W
    · have hfat : ContMDiffAt 𝓘(ℝ, P) I (8 : ℕ) (fun e => f (e, t)) 0 :=
        (hfAt (0, t) h0).comp 0
          ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
      have hFat : ContMDiffAt 𝓘(ℝ, P) I (8 : ℕ) (fun e => F (e, t)) 0 :=
        (hFAt (0, t) h0d).comp 0
          ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
      have hsrc := (hmem 0 t h0d ht).2.1
      have heq : (fun e : P => extChartAt I p (F (e, t))) =ᶠ[𝓝 0]
          fun e => coord (e, t) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds h0d] with e he
        dsimp only [F]; rw [ite_eq_left ht]
        exact (extChartAt I p).right_inv (htarget e t he ht)
      have hfd := (contMDiffAt_iff_contDiffAt.mp
        ((hchart hsrc).comp 0 hfat)).differentiableAt (by norm_num)
      have hraw := hfd.hasFDerivAt.add (hBd.const_smul (cut t))
      change HasFDerivAt (fun e : P => coord (e, t))
        (fderiv ℝ (fun e : P => extChartAt I p (f (e, t))) 0 +
          cut t • (0 : P →L[ℝ] E)) 0 at hraw
      have hcoordDerivative : fderiv ℝ (fun e : P => extChartAt I p (F (e, t))) 0 =
          fderiv ℝ (fun e : P => extChartAt I p (f (e, t))) 0 := by
        rw [heq.fderiv_eq]
        simpa only [smul_zero, add_zero] using hraw.fderiv
      apply ContinuousLinearMap.ext
      intro Z
      erw [raw_mfderiv_parameter_apply_eq_symmL_fderiv
        (hFat.mdifferentiableAt (by norm_num)) p (by
          simpa only [hcenter, extChartAt_source] using hsrc) Z,
        raw_mfderiv_parameter_apply_eq_symmL_fderiv
        (hfat.mdifferentiableAt (by norm_num)) p (by
          simpa only [extChartAt_source] using hsrc) Z, hcenter]
      exact congrArg
        (fun L : P →L[ℝ] E =>
          ((trivializationAt E (TangentSpace I) p).symmL ℝ (f (0, t))) (L Z))
        hcoordDerivative
    · have heq : (fun e : P => F (e, t)) = fun e => f (e, t) := by
        funext e; exact ite_eq_right ht
      let Dparam : (P → M) → P →L[ℝ] E := fun z => mfderiv 𝓘(ℝ, P) I z 0
      exact congrArg Dparam heq
  refine ⟨Metric.ball (0 : P) delta, Metric.isOpen_ball, h0d, hsub, F,
    fun z hz => (hFAt z hz.1).contMDiffWithinAt,
    hcenter, hfield, ?_, ?_⟩
  · intro e he
    have hone : cut c = 1 := cut.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    dsimp only [F]; rw [ite_eq_left hcW]
    dsimp only [coord, B]; rw [hone, one_smul, add_sub_cancel]
    exact (extChartAt I p).left_inv (hdbgood (heB e he)).1
  · intro e he
    exact hzero e k he hcutk

end DifferentialGeometry.Geometry.Riemannian.Variation
