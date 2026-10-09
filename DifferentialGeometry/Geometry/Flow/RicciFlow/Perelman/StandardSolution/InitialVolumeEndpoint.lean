import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierJoinCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierActionDilation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostChartLipComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeBounds
import DifferentialGeometry.Geometry.Metric.Path.Length
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bundle Filter Function MeasureTheory Set Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [ConnectedSpace M] {D : RealTimeInterval}

omit [I.Boundaryless] [T2Space M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lCost_competitors_nonempty
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x y : M)
    (tau : ℝ) (htau : 0 < tau) :
    Set.Nonempty {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
        alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
        lLength S T (squareRootReparametrization alpha) 0 tau = r} := by
  let g := S.base.metric T
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  have hxy : Manifold.riemannianEDist I x y < (⊤ : ENNReal) :=
    lt_of_le_of_ne le_top
      (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
        (I := I) x y)
  obtain ⟨p, hp, _hlen⟩ :=
    Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt
      (I := I) hxy
  let b : ℝ := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  let alpha : ℝ → M := fun s ↦ p.extend (s / b)
  have halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha := by
    apply hp.contMDiff.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  refine ⟨lLength S T (squareRootReparametrization alpha) 0 tau, alpha, halpha, ?_, ?_, rfl⟩
  · simp only [alpha, zero_div, Path.extend_zero]
  · change p.extend (b / b) = y
    simp only [div_self hb.ne', Path.extend_one]

omit [I.Boundaryless] in
theorem lCost_upperSemicontinuousWithinAt_of_rm_on_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (B T : ℝ) (x y : M) (tau : ℝ) (htau : 0 < tau)
    (hcarrier : Icc (T - tau) T ⊆ D.carrier)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B) :
    UpperSemicontinuousWithinAt
      (fun r : ℝ ↦ lCost S T x y r) (Ioc 0 tau) tau := by
  rw [upperSemicontinuousWithinAt_iff]
  intro A hA
  obtain ⟨a, ⟨alpha, halpha, hstart, hend, ha⟩, haA⟩ :=
    exists_lt_of_csInf_lt (lCost_competitors_nonempty S T x y tau htau) hA
  have hact : lRegularizedAction S T alpha 0 (Real.sqrt tau) < A := by
    rw [← lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T alpha tau htau.le, ha]
    exact haA
  have hslab : Icc (T - (Real.sqrt tau) ^ 2) T ⊆ D.carrier := by
    simpa only [Real.sq_sqrt htau.le] using hcarrier
  have hdil := lRegAction_dilation_tendsto_on_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T (Real.sqrt tau)
    (Real.sqrt_pos.mpr htau) hslab alpha halpha
  have hsqrt : Tendsto Real.sqrt (𝓝[Ioc (0 : ℝ) tau] tau)
      (𝓝[Ioc (0 : ℝ) (Real.sqrt tau)] (Real.sqrt tau)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Real.continuous_sqrt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ⟨Real.sqrt_pos.mpr hr.1, Real.sqrt_le_sqrt hr.2⟩
  have hnear := (hdil.comp hsqrt).eventually (Iio_mem_nhds hact)
  filter_upwards [hnear, self_mem_nhdsWithin] with r hrA hr
  let beta : ℝ → M := fun s ↦ alpha (Real.sqrt tau * s / Real.sqrt r)
  have hbeta : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 beta := by
    have hclock : ContDiff ℝ 1
        (fun s : ℝ ↦ Real.sqrt tau * s / Real.sqrt r) :=
      (contDiff_const.mul contDiff_id).div_const (Real.sqrt r)
    exact halpha.comp hclock.contMDiff
  have hbstart : beta 0 = x := by
    simpa only [beta, mul_zero, zero_div] using hstart
  have hbend : beta (Real.sqrt r) = y := by
    simpa only [beta, mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hr.1).ne'] using hend
  have hback : ∀ s ∈ Icc (0 : ℝ) (Real.sqrt r), T - s ^ 2 ∈ D.carrier := by
    intro s hs
    have hs2 : s ^ 2 ≤ r := by
      simpa only [Real.sq_sqrt hr.1.le] using
        (sq_le_sq₀ hs.1 (Real.sqrt_nonneg r)).mpr hs.2
    exact hcarrier ⟨by linarith only [hs2, hr.2], sub_le_self T (sq_nonneg s)⟩
  have hbound : ∀ t ∈ Icc (T - (Real.sqrt r) ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B := by
    intro t ht z
    rw [Real.sq_sqrt hr.1.le] at ht
    exact hRm t ⟨by linarith only [ht.1, hr.2], ht.2⟩ z
  have hbdd := lCost_competitors_bddBelow_of_rm_on_carrier
    S hS B T (Real.sqrt r) (Real.sqrt_nonneg r) x y hback hbound
  rw [Real.sq_sqrt hr.1.le] at hbdd
  have hcost : lCost S T x y r ≤ lRegularizedAction S T beta 0 (Real.sqrt r) := by
    change sInf _ ≤ _
    apply csInf_le hbdd
    exact ⟨beta, hbeta, hbstart, hbend, lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T beta r hr.1.le⟩
  exact hcost.trans_lt hrA

omit [I.Boundaryless] in
theorem redDensity_lowerSemicontinuousWithinAt_of_rm_on_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (B T : ℝ) (x y : M) (tau : ℝ) (htau : 0 < tau)
    (hcarrier : Icc (T - tau) T ⊆ D.carrier)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B) :
    LowerSemicontinuousWithinAt
      (fun r : ℝ ↦ ENNReal.ofReal (redDensity S T x y r)) (Ioc 0 tau) tau := by
  have hcost := lCost_upperSemicontinuousWithinAt_of_rm_on_carrier
    S hS B T x y tau htau hcarrier hRm
  have hred : UpperSemicontinuousWithinAt
      (fun r : ℝ ↦ redLength S T x y r) (Ioc 0 tau) tau := by
    rw [upperSemicontinuousWithinAt_iff]
    intro A hA
    have hden : 0 < 2 * Real.sqrt tau := mul_pos (by norm_num) (Real.sqrt_pos.mpr htau)
    have hgap : lCost S T x y tau < A * (2 * Real.sqrt tau) :=
      (div_lt_iff₀ hden).mp hA
    obtain ⟨C, hC, hCA⟩ := exists_between hgap
    have hnearCost := (upperSemicontinuousWithinAt_iff.mp hcost) C hC
    have hdenCont : ContinuousAt (fun r : ℝ ↦ A * (2 * Real.sqrt r)) tau :=
      continuousAt_const.mul (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
    have hnearDen : ∀ᶠ r in 𝓝[Ioc (0 : ℝ) tau] tau,
        C < A * (2 * Real.sqrt r) :=
      (hdenCont.tendsto.mono_left nhdsWithin_le_nhds).eventually (Ioi_mem_nhds hCA)
    filter_upwards [hnearCost, hnearDen, self_mem_nhdsWithin] with r hrC hrDen hr
    change lCost S T x y r / (2 * Real.sqrt r) < A
    exact (div_lt_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr hr.1))).mpr
      (hrC.trans hrDen)
  let n : ℝ := Module.finrank ℝ E
  have hlog : ContinuousAt (fun r : ℝ ↦ (n / 2) * Real.log r) tau :=
    continuousAt_const.mul (Real.continuousAt_log htau.ne')
  have hsum : UpperSemicontinuousWithinAt
      (fun r : ℝ ↦ redLength S T x y r +
        (n / 2) * Real.log r + (n / 2) * Real.log (4 * Real.pi))
      (Ioc 0 tau) tau :=
    (hred.add hlog.continuousWithinAt.upperSemicontinuousWithinAt).add
      upperSemicontinuousWithinAt_const
  have houter : Continuous (fun q : ℝ ↦ Real.exp (-q)) :=
    Real.continuous_exp.comp continuous_neg
  have hanti : Antitone (fun q : ℝ ↦ Real.exp (-q)) :=
    fun _ _ hab ↦ Real.exp_le_exp.mpr (neg_le_neg hab)
  have hexp := houter.continuousAt.comp_upperSemicontinuousWithinAt_antitone hsum hanti
  have hof := ENNReal.continuous_ofReal.continuousAt.comp_lowerSemicontinuousWithinAt
    hexp (fun _ _ hab ↦ ENNReal.ofReal_le_ofReal hab)
  have heq : (ENNReal.ofReal ∘ (fun q : ℝ ↦ Real.exp (-q)) ∘
      fun r : ℝ ↦ redLength S T x y r +
        (n / 2) * Real.log r + (n / 2) * Real.log (4 * Real.pi)) =
      fun r : ℝ ↦ ENNReal.ofReal (redDensity S T x y r) := by
    funext r
    apply congrArg ENNReal.ofReal
    apply congrArg Real.exp
    dsimp only [Function.comp_apply, redDensity, n]
    ring
  rw [heq] at hof
  exact hof

variable [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [ConnectedSpace M] in
private theorem original_redDensity_measurable_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (B T : ℝ) (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B) :
    Measurable (fun y : M ↦ ENNReal.ofReal (redDensity S T x y tau)) := by
  have hlocal (p : M) : ContinuousOn (fun y : M ↦ lCost S T x y tau)
      (extChartAt I p).source := by
    have hchart := (lCost_chart_lip_of_rm S hS B T hg x tau htau hslab hRm p).continuousOn
    have hcomp := hchart.comp (continuousOn_extChartAt (I := I) p)
      (fun y hy ↦ (extChartAt I p).map_source hy)
    apply hcomp.congr
    intro y hy
    simp only [Function.comp_apply, (extChartAt I p).left_inv hy]
  have hcost : Continuous (fun y : M ↦ lCost S T x y tau) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (hlocal y y (mem_extChartAt_source (I := I) y)).continuousAt
      ((isOpen_extChartAt_source (I := I) y).mem_nhds (mem_extChartAt_source (I := I) y))
  have hred : Continuous (fun y : M ↦ redDensity S T x y tau) := by
    unfold redDensity redLength
    exact Real.continuous_exp.comp
      (((hcost.div_const (2 * Real.sqrt tau)).neg.sub continuous_const).sub continuous_const)
  exact ENNReal.measurable_ofReal.comp hred.measurable

omit [ConnectedSpace M] [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
private theorem original_initial_measure_le_evolved
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (B T : ℝ) (hcarrier : Icc (0 : ℝ) T ⊆ D.carrier)
    (hreg : Ioc (0 : ℝ) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    riemannianVolumeMeasure (I := I) (M := M) (S.base.metric 0) ≤
      ENNReal.ofReal (Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 * Real.sqrt B * t)) •
        riemannianVolumeMeasure (I := I) (M := M) (S.base.metric t) := by
  let k : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B
  have hric : ∀ s ∈ Icc (0 : ℝ) T, ∀ z : M, ∀ v : TangentSpace I z,
      |ricciTensor (I := I) (S.base.metric s) z v v| ≤
        k * (S.base.metric s).inner z v v := by
    intro s hs z v
    exact ricci_quadratic_form_bound_of_solution_curvature_bound S z v (hRm s hs z)
  have hequiv := metricEquiv_Icc S.base.metric
    (metricPDE_Icc S hS hcarrier (fun _ ht ↦ hreg ⟨ht.1, ht.2.le⟩)) hric
  have hcomp : ∀ z : M, ∀ v : TangentSpace I z,
      (S.base.metric 0).inner z v v ≤
        Real.exp (2 * k * t) * (S.base.metric t).inner z v v := by
    intro z v
    have hlow := (hequiv t ht z v).1
    simp only [sub_zero] at hlow
    calc
      (S.base.metric 0).inner z v v =
          Real.exp (2 * k * t) *
            (Real.exp (-(2 * k * t)) * (S.base.metric 0).inner z v v) := by
        rw [Real.exp_neg, ← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul]
      _ ≤ Real.exp (2 * k * t) * (S.base.metric t).inner z v v :=
        mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
  have hmeasure := volumeMeasure_le (I := I) (S.base.metric t) (S.base.metric 0)
    (Real.exp_pos (2 * k * t)) hcomp
  have hpow : (Real.exp (2 * k * t)) ^ Module.finrank ℝ E =
      (Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 * Real.sqrt B * t)) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    norm_num
    dsimp only [k]
    ring
  rw [hpow, Real.sqrt_sq (Real.exp_pos _).le] at hmeasure
  exact hmeasure

theorem redVolume_initial_le_liminf_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (B T : ℝ) (hT : 0 < T)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T)) (x : M)
    (hcarrier : Icc (0 : ℝ) T ⊆ D.carrier)
    (hreg : Ioc (0 : ℝ) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B)
    (tau : ℕ → ℝ) (htau : ∀ j, 0 < tau j ∧ tau j < T)
    (hlim : Tendsto tau atTop (𝓝 T)) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x T ≤
      liminf (fun j ↦ DifferentialGeometry.PDE.RicciFlow.redVolume S T x (tau j)) atTop := by
  let mu0 := riemannianVolumeMeasure (I := I) (M := M) (S.base.metric 0)
  let F : ℝ → M → ℝ≥0∞ := fun r y ↦ ENNReal.ofReal (redDensity S T x y r)
  let c : ℝ := (Module.finrank ℝ E : ℝ) ^ 3 * Real.sqrt B
  let q : ℕ → ℝ≥0∞ := fun j ↦ ENNReal.ofReal (Real.exp (c * (T - tau j)))
  let V : ℕ → ℝ≥0∞ := fun j ↦ DifferentialGeometry.PDE.RicciFlow.redVolume S T x (tau j)
  have hmeas (j : ℕ) : Measurable (F (tau j)) := by
    apply original_redDensity_measurable_of_rm S hS B T hg x (tau j) (htau j).1
    · intro t ht
      exact hreg ⟨(sub_pos.mpr (htau j).2).trans_le ht.1, ht.2⟩
    · intro t ht z
      exact hRm t ⟨(sub_pos.mpr (htau j).2).le.trans ht.1, ht.2⟩ z
  have hclock : Tendsto tau atTop (𝓝[Ioc (0 : ℝ) T] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall (fun j ↦ ⟨(htau j).1, (htau j).2.le⟩)⟩
  have hpoint (y : M) : F T y ≤ liminf (fun j ↦ F (tau j) y) atTop := by
    have hlsc := redDensity_lowerSemicontinuousWithinAt_of_rm_on_carrier
      S hS B T x y T hT (by simpa only [sub_self] using hcarrier)
      (by simpa only [sub_self] using hRm)
    exact hlsc.le_liminf.trans hclock.liminf_le_liminf_comp
  have hcomparison (j : ℕ) : (∫⁻ y : M, F (tau j) y ∂mu0) ≤ q j * V j := by
    have hmeasure := original_initial_measure_le_evolved S hS B T hcarrier hreg hRm
      (T - tau j) ⟨(sub_pos.mpr (htau j).2).le, sub_le_self T (htau j).1.le⟩
    have hlin := lintegral_mono' hmeasure (le_refl (F (tau j)))
    rw [lintegral_smul_measure, smul_eq_mul] at hlin
    exact hlin
  have hq : Tendsto q atTop (𝓝 (1 : ℝ≥0∞)) := by
    have hc : Continuous (fun r : ℝ ↦ ENNReal.ofReal (Real.exp (c * (T - r)))) :=
      ENNReal.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id)))
    simpa only [q, Function.comp_def, sub_self, mul_zero, Real.exp_zero, ENNReal.ofReal_one] using
      hc.continuousAt.tendsto.comp hlim
  have hmul : liminf (q * V) atTop ≤ liminf V atTop := by
    have hmul := ENNReal.liminf_mul_le (u := q) (v := V) (f := atTop)
      (Or.inl (by rw [hq.limsup_eq]; norm_num))
      (Or.inl (by rw [hq.limsup_eq]; norm_num))
    simpa only [hq.limsup_eq, one_mul] using hmul
  calc
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x T = ∫⁻ y : M, F T y ∂mu0 := by
      simp only [DifferentialGeometry.PDE.RicciFlow.redVolume, F, mu0, sub_self]
    _ ≤ ∫⁻ y : M, liminf (fun j ↦ F (tau j) y) atTop ∂mu0 := lintegral_mono hpoint
    _ ≤ liminf (fun j ↦ ∫⁻ y : M, F (tau j) y ∂mu0) atTop := lintegral_liminf_le hmeas
    _ ≤ liminf (q * V) atTop := liminf_le_liminf (Eventually.of_forall hcomparison)
    _ ≤ liminf V atTop := hmul

theorem redVolume_initial_le_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (B T : ℝ) (hT : 0 < T)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T)) (x : M)
    (hcarrier : Icc (0 : ℝ) T ⊆ D.carrier)
    (hreg : Ioc (0 : ℝ) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B)
    (hRmQual : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    (tau : ℝ) (htau : 0 < tau) (htauT : tau < T) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x T ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau := by
  let u : ℕ → ℝ := fun j ↦ T - (T - tau) * (1 / ((j : ℝ) + 1))
  have hu (j : ℕ) : tau ≤ u j ∧ u j < T := by
    have hden : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hfracpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hfracle : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 :=
      (div_le_one hden).mpr (by linarith only [Nat.cast_nonneg (α := ℝ) j])
    have hdiff : 0 < T - tau := sub_pos.mpr htauT
    have hprod := mul_le_mul_of_nonneg_left hfracle hdiff.le
    have hprodpos := mul_pos hdiff hfracpos
    constructor <;> dsimp only [u] <;> nlinarith
  have hup (j : ℕ) : 0 < u j ∧ u j < T := ⟨htau.trans_le (hu j).1, (hu j).2⟩
  have hulim : Tendsto u atTop (𝓝 T) := by
    simpa only [u, mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
  have hanti (j : ℕ) : DifferentialGeometry.PDE.RicciFlow.redVolume S T x (u j) ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau := by
    apply redVolume_anti_of_rm S hS T hg x hRmQual htau (hu j).1
    intro t ht
    exact hreg ⟨(sub_pos.mpr (hu j).2).trans_le ht.1, ht.2⟩
  exact (redVolume_initial_le_liminf_of_rm S hS B T hT hg x hcarrier hreg hRm
    u hup hulim).trans
      (liminf_le_of_frequently_le (Eventually.of_forall hanti).frequently)

theorem redVolume_initial_le_of_bounded_rm_on_nonnegative_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (hg : RiemannianMetricComplete (I := I) (S.base.metric T)) (x : M)
    (hnonneg : D.carrier ⊆ Ici (0 : ℝ))
    (hcarrier : Icc (0 : ℝ) T ⊆ D.carrier)
    (hreg : Ioc (0 : ℝ) T ⊆ D.regular)
    (hRm : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B)
    (tau : ℝ) (htau : 0 < tau) (htauT : tau < T) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x T ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau := by
  obtain ⟨B, hB⟩ := hRm
  apply redVolume_initial_le_of_rm S hS B T (htau.trans htauT) hg x hcarrier hreg hB
    ?_ tau htau htauT
  intro sigma _hsigma hslab
  refine ⟨B, ?_⟩
  intro t ht z
  exact hB t ⟨hnonneg (D.regular_subset (hslab ht)), ht.2⟩ z

end DifferentialGeometry.PDE.RicciFlow

end
