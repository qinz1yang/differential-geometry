import DifferentialGeometry.Geometry.Comparison.Variation.Field.PairRealization
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve
import DifferentialGeometry.Topology.Manifold.CurveExtension
import DifferentialGeometry.Topology.Manifold.SmoothInterval
noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem correct_variation_endpoint
    (f : ℝ × ℝ → M) {P : Set ℝ} (hP : IsOpen P) (h0 : (0 : ℝ) ∈ P)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) f (P ×ˢ univ))
    (beta : ℝ → M) (hb : ContMDiffOn 𝓘(ℝ, ℝ) I (8 : ℕ) beta P)
    (c k : ℝ) (hck : c ≠ k) (hb0 : beta 0 = f (0, c))
    (hbv : (mfderiv 𝓘(ℝ, ℝ) I beta 0 1 : E) =
      mfderiv 𝓘(ℝ, ℝ) I (fun e => f (e, c)) 0 1) :
    ∃ delta : ℝ, 0 < delta ∧ Ioo (-delta) delta ⊆ P ∧
      ∃ F : ℝ × ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) F (Ioo (-delta) delta ×ˢ univ) ∧
        (∀ t, F (0, t) = f (0, t)) ∧
        (∀ t, (mfderiv 𝓘(ℝ, ℝ) I (fun e => F (e, t)) 0 1 : E) =
          mfderiv 𝓘(ℝ, ℝ) I (fun e => f (e, t)) 0 1) ∧
        (∀ e ∈ Ioo (-delta) delta, F (e, c) = beta e) ∧
        (∀ e ∈ Ioo (-delta) delta, F (e, k) = f (e, k)) := by
  classical
  let p := f (0, c)
  let q := extChartAt I p p
  have hfAt (z : ℝ × ℝ) (hz : z.1 ∈ P) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) f z :=
    (hf z ⟨hz, mem_univ _⟩).contMDiffAt ((hP.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)
  have hbAt : ContMDiffAt 𝓘(ℝ, ℝ) I (8 : ℕ) beta 0 :=
    (hb 0 h0).contMDiffAt (hP.mem_nhds h0)
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := I) p) q (mem_extChartAt_target p)
  let r := eps / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hcoord : ContinuousAt (fun z : ℝ × ℝ => extChartAt I p (f z)) (0, c) :=
    (continuousAt_extChartAt (I := I) p).comp (hfAt (0, c) h0).continuousAt
  have hgood : {z : ℝ × ℝ | z.1 ∈ P ∧ f z ∈ (extChartAt I p).source ∧
      extChartAt I p (f z) ∈ Metric.ball q r} ∈ 𝓝 (0, c) := by
    filter_upwards [continuous_fst.continuousAt.eventually (hP.mem_nhds h0),
      (hfAt (0, c) h0).continuousAt.eventually
        ((isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)),
      hcoord.eventually (Metric.ball_mem_nhds q hr)] with z hz hsrc hq
    exact ⟨hz, hsrc, hq⟩
  obtain ⟨d, hd, hdgood⟩ := Metric.mem_nhds_iff.mp hgood
  have hbgood : {e : ℝ | beta e ∈ (extChartAt I p).source ∧
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
  have heD (e : ℝ) (he : e ∈ Ioo (-delta) delta) : dist e 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [he.1, he.2]
  have heB (e : ℝ) (he : e ∈ Ioo (-delta) delta) : dist e 0 < db := by
    rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [he.1, he.2]
  have h0d : (0 : ℝ) ∈ Ioo (-delta) delta := by constructor <;> linarith
  let W := Metric.ball c d
  have hmem (e t : ℝ) (he : e ∈ Ioo (-delta) delta) (ht : t ∈ W) :
      e ∈ P ∧ f (e, t) ∈ (extChartAt I p).source ∧
        extChartAt I p (f (e, t)) ∈ Metric.ball q r := by
    apply hdgood (a := (e, t))
    change dist (e, t) (0, c) < d
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨heD e he, ht⟩
  have hcW : c ∈ W := Metric.mem_ball_self hd
  have hsub : Ioo (-delta) delta ⊆ P := fun e he => (hmem e c he hcW).1
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
  let B : ℝ → E := fun e => extChartAt I p (beta e) - extChartAt I p (f (e, c))
  let coord : ℝ × ℝ → E := fun z => extChartAt I p (f z) + cut z.2 • B z.1
  let F : ℝ × ℝ → M := fun z =>
    if z.2 ∈ W then (extChartAt I p).symm (coord z) else f z
  have htarget (e t : ℝ) (he : e ∈ Ioo (-delta) delta) (ht : t ∈ W) :
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
  have hzero (e t : ℝ) (he : e ∈ Ioo (-delta) delta) (hz : cut t = 0) :
      F (e, t) = f (e, t) := by
    dsimp only [F]
    split_ifs with ht
    · dsimp only [coord]; rw [hz, zero_smul, add_zero]
      exact (extChartAt I p).left_inv (hmem e t he ht).2.1
    · rfl
  have hchart {x : M} (hx : x ∈ (extChartAt I p).source) :
      ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I p) x :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)
  have hcoordAt (z : ℝ × ℝ) (he : z.1 ∈ Ioo (-delta) delta) (ht : z.2 ∈ W) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (8 : ℕ) coord z := by
    have hfc : ContMDiffAt 𝓘(ℝ, ℝ) I (8 : ℕ) (fun e => f (e, c)) z.1 :=
      (hfAt (z.1, c) (hsub he)).comp z.1 ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
    have hbeta := (hb z.1 (hsub he)).contMDiffAt (hP.mem_nhds (hsub he))
    have hbcoord := (hchart
      (hdbgood (heB z.1 he)).1).comp z.1 hbeta
    have hfcoord := (hchart
      (hmem z.1 c he hcW).2.1).comp z.1 hfc
    have hB : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (8 : ℕ) B z.1 := hbcoord.sub hfcoord
    exact ((hchart
      (hmem z.1 z.2 he ht).2.1).comp z (hfAt z (hsub he))).add
      (((cut.contDiff.comp contDiff_snd).of_le (by exact WithTop.coe_le_coe.mpr le_top : (8 : WithTop ℕ∞) ≤ ∞)).contMDiff.contMDiffAt.smul
        (hB.comp z contDiff_fst.contMDiff.contMDiffAt))
  have hFAt (z : ℝ × ℝ) (he : z.1 ∈ Ioo (-delta) delta) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) F z := by
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
      filter_upwards [continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds he),
        continuous_snd.continuousAt.tendsto.eventually hcutzero] with y hy hc
      exact hzero y.1 y.2 hy hc
  have hcenter (t : ℝ) : F (0, t) = f (0, t) := by
    dsimp only [F]
    split_ifs with ht
    · have hB0 : B 0 = 0 := by simp only [B, hb0, sub_self]
      dsimp only [coord]; rw [hB0, smul_zero, add_zero]
      exact (extChartAt I p).left_inv (hmem 0 t h0d ht).2.1
    · rfl
  have hfcAt : ContMDiffAt 𝓘(ℝ, ℝ) I (8 : ℕ) (fun e => f (e, c)) 0 :=
    (hfAt (0, c) h0).comp 0 ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
  have hBd : HasDerivAt B 0 0 := by
    have hbcoord := (hchart
      (hdbgood (heB 0 h0d)).1).comp 0 hbAt
    have hfcoord := (hchart
      (hmem 0 c h0d hcW).2.1).comp 0 hfcAt
    have hderiv : deriv (fun e => extChartAt I p (beta e)) 0 =
        deriv (fun e => extChartAt I p (f (e, c))) 0 := by
      rw [← fderiv_apply_one_eq_deriv, ← fderiv_apply_one_eq_deriv]
      change fderiv ℝ ((extChartAt I p) ∘ beta) 0 1 =
        fderiv ℝ ((extChartAt I p) ∘ (fun e => f (e, c))) 0 1
      rw [← MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (hbAt.mdifferentiableAt (by norm_num)) p (by
          simpa only [extChartAt_source] using (hdbgood (heB 0 h0d)).1),
        ← MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (hfcAt.mdifferentiableAt (by norm_num)) p (by
          simpa only [extChartAt_source] using (hmem 0 c h0d hcW).2.1)]
      erw [hb0, hbv]
      rfl
    have hbD := (contMDiffAt_iff_contDiffAt.mp hbcoord).differentiableAt (by norm_num)
    have hfD := (contMDiffAt_iff_contDiffAt.mp hfcoord).differentiableAt (by norm_num)
    have hraw := hbD.hasDerivAt.sub hfD.hasDerivAt
    change HasDerivAt B
      (deriv (fun e => extChartAt I p (beta e)) 0 -
        deriv (fun e => extChartAt I p (f (e, c))) 0) 0 at hraw
    rwa [hderiv, sub_self] at hraw
  have hfield (t : ℝ) : (mfderiv 𝓘(ℝ, ℝ) I (fun e => F (e, t)) 0 1 : E) =
      mfderiv 𝓘(ℝ, ℝ) I (fun e => f (e, t)) 0 1 := by
    by_cases ht : t ∈ W
    · have hfat : ContMDiffAt 𝓘(ℝ, ℝ) I (8 : ℕ) (fun e => f (e, t)) 0 := (hfAt (0, t) h0).comp 0 ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
      have hFat : ContMDiffAt 𝓘(ℝ, ℝ) I (8 : ℕ) (fun e => F (e, t)) 0 := (hFAt (0, t) h0d).comp 0 ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
      have hsrc := (hmem 0 t h0d ht).2.1
      erw [MFDerivAlongCurve.raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
        (hFat.mdifferentiableAt (by norm_num)) p (by
          simpa only [hcenter, extChartAt_source] using hsrc),
        MFDerivAlongCurve.raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
        (hfat.mdifferentiableAt (by norm_num)) p (by
          simpa only [extChartAt_source] using hsrc), hcenter]
      congr 1
      have heq : (fun e => extChartAt I p (F (e, t))) =ᶠ[𝓝 0]
          fun e => coord (e, t) := by
        filter_upwards [isOpen_Ioo.mem_nhds h0d] with e he
        dsimp only [F]; rw [ite_eq_left ht]
        exact (extChartAt I p).right_inv (htarget e t he ht)
      dsimp only [Function.comp_def, id_eq]
      rw [heq.fderiv_eq, fderiv_apply_one_eq_deriv, fderiv_apply_one_eq_deriv]
      have hfd := (contMDiffAt_iff_contDiffAt.mp
        ((hchart hsrc).comp 0 hfat)).differentiableAt
          (by norm_num)
      have hraw := hfd.hasDerivAt.add (hBd.const_smul (cut t))
      change HasDerivAt (fun e => coord (e, t))
        (deriv (fun e => extChartAt I p (f (e, t))) 0 + cut t • (0 : E)) 0 at hraw
      simpa only [smul_zero, add_zero] using hraw.deriv
    · have heq : (fun e => F (e, t)) = fun e => f (e, t) := by
        funext e; exact ite_eq_right ht
      exact congrArg (fun z : ℝ → M => (mfderiv 𝓘(ℝ, ℝ) I z 0 1 : E)) heq
  refine ⟨delta, hdelta, hsub, F, fun z hz => (hFAt z hz.1).contMDiffWithinAt,
    hcenter, hfield, ?_, ?_⟩
  · intro e he
    have hone : cut c = 1 := cut.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    dsimp only [F]; rw [ite_eq_left hcW]
    dsimp only [coord, B]; rw [hone, one_smul, add_sub_cancel]
    exact (extChartAt I p).left_inv (hdbgood (heB e he)).1
  · intro e he
    exact hzero e k he hcutk

theorem exists_var_with_endpoint_paths
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (Y : ℝ → E)
    {a b : ℝ} (hab : a < b) {J : Set ℝ} (hJ : IsOpen J) (habJ : Icc a b ⊆ J)
    (hY : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (⟨gamma t, Y t⟩ : TangentBundle I M)) J)
    (betaA betaB : ℝ → M) {P : Set ℝ} (hP : IsOpen P) (h0 : (0 : ℝ) ∈ P)
    (hbetaA : ContMDiffOn 𝓘(ℝ, ℝ) I (8 : ℕ) betaA P)
    (hbetaB : ContMDiffOn 𝓘(ℝ, ℝ) I (8 : ℕ) betaB P)
    (hA0 : betaA 0 = gamma a) (hB0 : betaB 0 = gamma b)
    (hAv : (mfderiv 𝓘(ℝ, ℝ) I betaA 0 1 : E) = Y a)
    (hBv : (mfderiv 𝓘(ℝ, ℝ) I betaB 0 1 : E) = Y b) :
    ∃ f : ℝ → ℝ → M, IsSmoothVariation (I := I) f ∧
      (∀ t ∈ Icc a b, f 0 =ᶠ[𝓝 t] gamma) ∧
      (∀ t ∈ Icc a b,
        (fun r => (mfderiv 𝓘(ℝ, ℝ) I (fun e => f e r) 0 1 : E)) =ᶠ[𝓝 t] Y) ∧
      (fun e => f e a) =ᶠ[𝓝 0] betaA ∧ (fun e => f e b) =ᶠ[𝓝 0] betaB := by
  let L : ℝ → TangentBundle I M := fun t => ⟨gamma t, Y t⟩
  let U := (fun t : ℝ => a + t) ⁻¹' J
  have hU : IsOpen U := hJ.preimage (continuous_const.add continuous_id)
  have hLU : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞ (fun t => L (a + t)) U :=
    hY.comp (contMDiff_const.add contMDiff_id).contMDiffOn (fun _ ht => ht)
  have hseg : Icc (0 : ℝ) (b - a) ⊆ U := by
    intro t ht
    exact habJ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨Z, hZ, hZgerm⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval
      (I := I.tangent) (sub_pos.mpr hab).le hU hseg hLU
  let Z' : ℝ → TangentBundle I M := fun t => Z (t - a)
  have hZ' : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ Z' :=
    hZ.comp (contMDiff_id.sub contMDiff_const)
  have hZ'eq (t : ℝ) (ht : t ∈ Icc a b) : Z' =ᶠ[𝓝 t] L := by
    have heq := (hZgerm (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩).comp_tendsto
      (continuous_id.sub continuous_const).continuousAt.tendsto
    filter_upwards [heq] with r hr
    have hsum : a + (r - a) = r := by ring
    simpa only [Z', Function.comp_apply, Pi.sub_apply, id_eq, hsum] using hr
  let gamma' : ℝ → M := fun t => (Z' t).proj
  let Y' : ℝ → E := fun t => (Z' t).snd
  have hY' : ContMDiff 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t => (⟨gamma' t, Y' t⟩ : TangentBundle I M)) :=
    hZ'.of_le (WithTop.coe_le_coe.mpr le_top)
  have hbase (t : ℝ) (ht : t ∈ Icc a b) : gamma' =ᶠ[𝓝 t] gamma := by
    filter_upwards [hZ'eq t ht] with r hr
    exact congrArg (fun z : TangentBundle I M => z.proj) hr
  have hfield (t : ℝ) (ht : t ∈ Icc a b) : Y' =ᶠ[𝓝 t] Y := by
    filter_upwards [hZ'eq t ht] with r hr
    exact congrArg (fun z : TangentBundle I M => (z.snd : E)) hr
  obtain ⟨f0, _, hf0, _, hcenter0, _, hfield0, _, _, _, _⟩ :=
    exists_var_pair g gamma' Y' Y' (a - 1) (b + 1) hY' hY'
  let F0 : ℝ × ℝ → M := fun z => f0 z.1 z.2
  have hF0 : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) F0 := by
    have hh := hf0
    change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) F0 at hh
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact hh
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hbig (t : ℝ) (ht : t ∈ Icc a b) : t ∈ uIcc (a - 1) (b + 1) := by
    rw [uIcc_of_le (by linarith : a - 1 ≤ b + 1)]
    constructor <;> linarith [ht.1, ht.2]
  have hA0' : betaA 0 = F0 (0, a) := by
    change betaA 0 = f0 0 a
    rw [hcenter0]
    exact hA0.trans ((hbase a ha).self_of_nhds.symm)
  have hB0' : betaB 0 = F0 (0, b) := by
    change betaB 0 = f0 0 b
    rw [hcenter0]
    exact hB0.trans ((hbase b hb).self_of_nhds.symm)
  have hAv' : (mfderiv 𝓘(ℝ, ℝ) I betaA 0 1 : E) =
      (mfderiv 𝓘(ℝ, ℝ) I (fun e => F0 (e, a)) 0 1 : E) := by
    exact hAv.trans (((hfield0 a (hbig a ha)).trans (hfield a ha).self_of_nhds).symm)
  have hBv' : (mfderiv 𝓘(ℝ, ℝ) I betaB 0 1 : E) =
      (mfderiv 𝓘(ℝ, ℝ) I (fun e => F0 (e, b)) 0 1 : E) := by
    exact hBv.trans (((hfield0 b (hbig b hb)).trans (hfield b hb).self_of_nhds).symm)
  obtain ⟨dA, hdA, hdAP, FA, hFA, hFA0, hFAv, hFAA, hFAB⟩ :=
    correct_variation_endpoint F0 hP h0 hF0.contMDiffOn betaA
      hbetaA a b hab.ne hA0' hAv'
  have h0A : (0 : ℝ) ∈ Ioo (-dA) dA := ⟨neg_neg_of_pos hdA, hdA⟩
  have hB0A : betaB 0 = FA (0, b) := hB0'.trans (hFA0 b).symm
  have hBvA : (mfderiv 𝓘(ℝ, ℝ) I betaB 0 1 : E) =
      (mfderiv 𝓘(ℝ, ℝ) I (fun e => FA (e, b)) 0 1 : E) :=
    hBv'.trans (hFAv b).symm
  obtain ⟨dB, hdB, hdBA, FB, hFB, hFB0, hFBv, hFBB, hFBA⟩ :=
    correct_variation_endpoint FA isOpen_Ioo h0A hFA betaB
      (hbetaB.mono hdAP)
      b a hab.ne' hB0A hBvA
  obtain ⟨sigma, hsigma, hsigmaId, hsigmaBound⟩ :=
    DifferentialGeometry.exists_smooth_bounded_eventuallyEq_id (half_pos hdB)
  have hsigma0 : sigma 0 = 0 := hsigmaId.self_of_nhds
  have hsigmaRange (e : ℝ) : sigma e ∈ Ioo (-dB) dB := by
    have h := (abs_le.mp (hsigmaBound e))
    constructor <;> linarith [h.1, h.2]
  let f : ℝ → ℝ → M := fun e t => FB (sigma e, t)
  have hf : IsSmoothVariation (I := I) f := by
    have hcomp : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) (fun z : ℝ × ℝ => FB (sigma z.1, z.2)) :=
      hFB.comp_contMDiff
        (((hsigma.comp contDiff_fst).prodMk contDiff_snd).of_le
          (WithTop.coe_le_coe.mpr le_top)).contMDiff
        (fun z => ⟨hsigmaRange z.1, mem_univ _⟩)
    change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (fun z : ℝ × ℝ => f z.1 z.2)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hcomp
  have hfinalCenter (t : ℝ) : f 0 t = gamma' t := by
    change FB (sigma 0, t) = gamma' t
    rw [hsigma0, hFB0, hFA0]
    exact hcenter0 t
  have hfinalField (t : ℝ) : (mfderiv 𝓘(ℝ, ℝ) I (fun e => f e t) 0 1 : E) =
      (mfderiv 𝓘(ℝ, ℝ) I (fun e => F0 (e, t)) 0 1 : E) := by
    have heq : (fun e => f e t) =ᶠ[𝓝 0] fun e => FB (e, t) := by
      filter_upwards [hsigmaId] with e he
      exact congrArg (fun z => FB (z, t)) he
    have hvel := congrArg (fun D : ℝ →L[ℝ] E => D 1) (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))
    exact hvel.trans ((hFBv t).trans (hFAv t))
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · intro t ht
    filter_upwards [hbase t ht] with r hr
    exact (hfinalCenter r).trans hr
  · intro t ht
    filter_upwards [hfield t ht, Ioo_mem_nhds (show a - 1 < t by linarith [ht.1])
      (show t < b + 1 by linarith [ht.2])] with r hr hlarge
    exact (hfinalField r).trans ((hfield0 r (by
      rw [uIcc_of_le (by linarith : a - 1 ≤ b + 1)]
      exact ⟨hlarge.1.le, hlarge.2.le⟩)).trans hr)
  · filter_upwards [hsigmaId, isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-dB) dB from
      ⟨neg_neg_of_pos hdB, hdB⟩)] with e he heB
    change sigma e = e at he
    change FB (sigma e, a) = betaA e
    rw [he, hFBA e heB]
    exact hFAA e (hdBA heB)
  · filter_upwards [hsigmaId, isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-dB) dB from
      ⟨neg_neg_of_pos hdB, hdB⟩)] with e he heB
    change sigma e = e at he
    change FB (sigma e, b) = betaB e
    rw [he]
    exact hFBB e heB

end DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.Variation

universe uM uE uH

theorem exists_compatible_variations_of_endpoint_fields
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (g : (i : Fin (n + 1)) → SmoothRiemannianMetric I (M i))
    (alpha : (i : Fin (n + 1)) → ℝ → M i) (Y : Fin (n + 1) → ℝ → E)
    (a b : Fin (n + 1) → ℝ) (hab : ∀ i, a i < b i)
    (J : Fin (n + 1) → Set ℝ) (hJ : ∀ i, IsOpen (J i))
    (hseg : ∀ i, Icc (a i) (b i) ⊆ J i)
    (hY : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (⟨alpha i t, Y i t⟩ : TangentBundle I (M i))) (J i))
    (F : (i : Fin n) → M i.castSucc → M i.succ)
    (U : (i : Fin n) → Set (M i.castSucc)) (hUopen : ∀ i, IsOpen (U i))
    (hF : ∀ i, ContMDiffOn I I (8 : ℕ) (F i) (U i))
    (hsource : ∀ i, alpha i.castSucc (b i.castSucc) ∈ U i)
    (hpoint : ∀ i, F i (alpha i.castSucc (b i.castSucc)) = alpha i.succ (a i.succ))
    (hfield : ∀ i,
      (mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc))
        (Y i.castSucc (b i.castSucc)) : E) = Y i.succ (a i.succ))
    (hfirst : Y 0 (a 0) = 0) :
    ∃ f : (i : Fin (n + 1)) → ℝ → ℝ → M i,
      (∀ i, IsSmoothVariation (I := I) (f i)) ∧
      (∀ i t, t ∈ Icc (a i) (b i) → f i 0 =ᶠ[𝓝 t] alpha i) ∧
      (∀ i t, t ∈ Icc (a i) (b i) →
        (fun r => (mfderiv 𝓘(ℝ, ℝ) I (fun e => f i e r) 0 1 : E)) =ᶠ[𝓝 t] Y i) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), f 0 e (a 0) = alpha 0 (a 0)) ∧
      ∀ᶠ e in 𝓝 (0 : ℝ), ∀ i : Fin n,
        f i.castSucc e (b i.castSucc) ∈ U i ∧
        F i (f i.castSucc e (b i.castSucc)) = f i.succ e (a i.succ) := by
  classical
  let V : (i : Fin (n + 1)) → Set (M i) :=
    Fin.lastCases (motive := fun i => Set (M i)) univ U
  have hV (i : Fin (n + 1)) : V i ∈ 𝓝 (alpha i (b i)) := by
    cases i using Fin.lastCases with
    | last => simp only [V, Fin.lastCases_last]; exact univ_mem
    | cast i =>
      simpa only [V, Fin.lastCases_castSucc] using (hUopen i).mem_nhds (hsource i)
  have hex (i : Fin (n + 1)) := exists_contMDiff_curve_with_velocity_range_subset
    (I := I) (BoundarylessManifold.isInteriorPoint (I := I)) (Y i (b i)) (hV i)
  choose beta hbeta hrange hjet using hex
  have hbeta0 (i : Fin (n + 1)) : beta i 0 = alpha i (b i) :=
    congrArg TotalSpace.proj (hjet i)
  have hbetav (i : Fin (n + 1)) :
      (mfderiv 𝓘(ℝ, ℝ) I (beta i) 0 1 : E) = Y i (b i) :=
    congrArg (fun z : TangentBundle I (M i) => (z.2 : E)) (hjet i)
  have hbetaSource (i : Fin n) (e : ℝ) : beta i.castSucc e ∈ U i := by
    simpa only [V, Fin.lastCases_castSucc] using hrange i.castSucc (mem_range_self e)
  let betaA : (i : Fin (n + 1)) → ℝ → M i :=
    Fin.cases (motive := fun i => ℝ → M i) (fun _ => alpha 0 (a 0))
      (fun i e => F i (beta i.castSucc e))
  have hbetaA (i : Fin (n + 1)) : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (betaA i) := by
    cases i using Fin.cases with
    | zero => simpa only [betaA, Fin.cases_zero] using
        (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun _ : ℝ => alpha 0 (a 0)))
    | succ i =>
      simpa only [betaA, Fin.cases_succ, Function.comp_def] using
        (hF i).comp_contMDiff
          ((hbeta i.castSucc).of_le (WithTop.coe_le_coe.mpr le_top)) (hbetaSource i)
  have hbetaA0 (i : Fin (n + 1)) : betaA i 0 = alpha i (a i) := by
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [betaA, Fin.cases_succ, hbeta0] using hpoint i
  have hbetaAv (i : Fin (n + 1)) :
      (mfderiv 𝓘(ℝ, ℝ) I (betaA i) 0 1 : E) = Y i (a i) := by
    cases i using Fin.cases with
    | zero =>
      simp only [betaA, Fin.cases_zero, mfderiv_const, hfirst]
      rfl
    | succ i =>
      have heq := mfderiv_comp_apply 0
        (((hF i _ (hbetaSource i 0)).contMDiffAt
          ((hUopen i).mem_nhds (hbetaSource i 0))).mdifferentiableAt (by norm_num))
        ((hbeta i.castSucc).mdifferentiableAt (by simp)) (1 : ℝ)
      change (mfderiv 𝓘(ℝ, ℝ) I (betaA i.succ) 0 1 : E) =
        (mfderiv I I (F i : M i.castSucc → M i.succ) (beta i.castSucc 0) : E →L[ℝ] E)
          (mfderiv 𝓘(ℝ, ℝ) I (beta i.castSucc) 0 1) at heq
      have hmap : (mfderiv I I (F i : M i.castSucc → M i.succ) (beta i.castSucc 0) : E →L[ℝ] E) =
          mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc)) :=
        mfderiv_congr_point (hbeta0 i.castSucc)
      rw [hbetav] at heq
      exact heq.trans ((congrArg (fun L : E →L[ℝ] E => L (Y i.castSucc (b i.castSucc)))
        hmap).trans (hfield i))
  have hvar (i : Fin (n + 1)) := exists_var_with_endpoint_paths
    (g i) (alpha i) (Y i) (hab i) (hJ i) (hseg i) (hY i)
    (betaA i) (beta i) isOpen_univ (mem_univ (0 : ℝ))
    (hbetaA i).contMDiffOn
    ((hbeta i).of_le (WithTop.coe_le_coe.mpr le_top)).contMDiffOn
    (hbetaA0 i) (hbeta0 i) (hbetaAv i) (hbetav i)
  choose f hf hcenter hvariation hleft hright using hvar
  refine ⟨f, hf, hcenter, hvariation, ?_, ?_⟩
  · filter_upwards [hleft 0] with e he
    exact he
  · have hjoin (i : Fin n) : ∀ᶠ e in 𝓝 (0 : ℝ),
        f i.castSucc e (b i.castSucc) ∈ U i ∧
        F i (f i.castSucc e (b i.castSucc)) = f i.succ e (a i.succ) := by
      filter_upwards [hright i.castSucc, hleft i.succ] with e heR heL
      rw [heR, heL]
      exact ⟨hbetaSource i e, rfl⟩
    exact eventually_all.mpr hjoin

end DifferentialGeometry.Geometry.Riemannian.Variation
