import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.JointParameter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function Manifold Matrix MeasureTheory Set
open scoped ContDiff ENNReal Manifold Matrix Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
private theorem sqrt_back_mem {T tau : Real} (htau : 0 ≤ tau) :
    ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ Icc (T - tau) T := by
  intro s hs
  have hsSq : s ^ 2 ≤ tau := by
    calc
      s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
        (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).2 hs.2
      _ = tau := Real.sq_sqrt htau
  exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
private theorem back_slab {R tau : Real} {U : Set Real}
    (hback : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau), R - s ^ 2 ∈ U) :
    Icc (R - tau) R ⊆ U := by
  intro t ht
  let s := Real.sqrt (R - t)
  have hsub : 0 ≤ R - t := sub_nonneg.mpr ht.2
  have hsuble : R - t ≤ tau := by linarith [ht.1]
  have hs : s ∈ Icc (0 : Real) (Real.sqrt tau) := by
    exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hsuble⟩
  have hsSq : s ^ 2 = R - t := Real.sq_sqrt hsub
  simpa only [s, hsSq, sub_sub_cancel] using hback s hs

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
private theorem uscAt_of_seq
    {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X]
    {f : X → Real} {x : X}
    (hseq : ∀ q : Nat → X, Tendsto q atTop (nhds x) →
      ∀ A, f x < A → ∀ᶠ n in atTop, f (q n) < A) :
    UpperSemicontinuousAt f x := by
  rw [upperSemicontinuousAt_iff]
  intro A hA
  by_contra hev
  have hfreq : ∃ᶠ z in nhds x, A ≤ f z := by
    simpa only [not_lt] using (not_eventually.mp hev)
  have hxcl : x ∈ closure {z | A ≤ f z} :=
    mem_closure_iff_frequently.mpr hfreq
  obtain ⟨q, hqmem, hq⟩ := mem_closure_iff_seq_limit.mp hxcl
  obtain ⟨n, hnmem, hnlt⟩ :=
    ((Frequently.of_forall hqmem).and_eventually (hseq q hq A hA)).exists
  exact (not_lt_of_ge hnmem) hnlt

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
private theorem lscAt_of_seq
    {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X]
    {f : X → ENNReal} {x : X}
    (hseq : ∀ q : Nat → X, Tendsto q atTop (nhds x) →
      f x ≤ liminf (fun n ↦ f (q n)) atTop) :
    LowerSemicontinuousAt f x := by
  rw [lowerSemicontinuousAt_iff]
  intro a ha
  by_contra hev
  have hfreq : ∃ᶠ z in nhds x, f z ≤ a := by
    simpa only [not_lt] using not_eventually.mp hev
  have hxcl : x ∈ closure {z | f z ≤ a} :=
    mem_closure_iff_frequently.mpr hfreq
  obtain ⟨q, hqmem, hq⟩ := mem_closure_iff_seq_limit.mp hxcl
  have hlim : f x ≤ liminf (fun n ↦ f (q n)) atTop := hseq q hq
  have hlimle : liminf (fun n ↦ f (q n)) atTop ≤ a :=
    liminf_le_of_frequently_le' (Frequently.of_forall hqmem)
  exact (not_lt_of_ge (hlim.trans hlimle)) ha

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
private theorem exists_cost_curve
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x y : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (A : Real) (hA : lCost S T x y tau < A) :
    ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
          lRegAction S T alpha 0 (Real.sqrt tau) < A := by
  let g := S.base.metric T
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  have hxy : Manifold.riemannianEDist I x y < (⊤ : ENNReal) :=
    lt_of_le_of_ne le_top
      (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
        (I := I) x y)
  obtain ⟨p, hp, _hlen⟩ :=
    DifferentialGeometry.Geometry.Riemannian.CGT.exists_flat_path
      (I := I) hxy
  let b : Real := Real.sqrt tau
  have hb : 0 < b := by simpa only [b] using Real.sqrt_pos.2 htau
  let alpha₀ : Real → M := fun s ↦ p.extend (s / b)
  have halpha₀ : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha₀ := by
    apply hp.c1.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  have ha₀ : alpha₀ 0 = x := by
    simp only [alpha₀, zero_div, Path.extend_zero]
  have hb₀ : alpha₀ b = y := by
    simp only [alpha₀, div_self hb.ne', Path.extend_one]
  have hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - tau) T := by
    simpa only [b] using sqrt_back_mem (T := T) htau.le
  have htime : Icc (T - tau) T ⊆ D.carrier :=
    fun _ hr ↦ D.regular_subset (hslab hr)
  obtain ⟨gamma, _m, _t, _p, _uLim, beta, _u, _hgamma, _hga, _hgb,
      heq, _hmin, _htmono, _ht0, _htlast, _hsrc, _hrep, hbeta,
      hbetaa, hbetab, _hsrcBeta, _hrepBeta, _hu, _hunifBeta, hbetaAct⟩ :=
    exists_lRegMinC1 (I := I) S hS T (T - tau) T 0 b hb.le htime hback
      x y alpha₀ halpha₀ ha₀ hb₀ (fun s hs ↦ hslab (hback s hs))
  have hgammaA : lRegAction S T gamma 0 b < A := by
    rw [heq, ← lCost_eq_reg (I := I) S T x y tau htau.le]
    exact hA
  have hev : ∀ᶠ n in atTop, lRegAction S T (beta n) 0 b < A :=
    hbetaAct.eventually (Iio_mem_nhds hgammaA)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨beta n, hbeta n, hbetaa n, by simpa only [b] using hbetab n,
    by simpa only [b] using hn⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
private theorem lCost_param_usc
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x y : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    UpperSemicontinuousAt
      (fun p : Real × M ↦ lCost S p.1 p.2 y tau) (T, x) := by
  apply uscAt_of_seq
  intro q hq A hA
  obtain ⟨alpha, halpha, hstart, hend, halphaA⟩ :=
    exists_cost_curve (I := I) S hS T x y tau htau hslab A hA
  have hT : Tendsto (fun n ↦ (q n).1) atTop (nhds T) := by
    simpa only [Function.comp_def] using continuous_fst.continuousAt.tendsto.comp hq
  have hx : Tendsto (fun n ↦ (q n).2) atTop (nhds x) := by
    simpa only [Function.comp_def] using continuous_snd.continuousAt.tendsto.comp hq
  exact lCost_lt_param (I := I) S hS hT htau x y alpha halpha hstart hend
    (fun s hs ↦ hslab (sqrt_back_mem (T := T) htau.le s hs))
    A halphaA (fun n ↦ (q n).2) hx

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
private theorem lCost_y_usc
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    UpperSemicontinuous (fun y : M ↦ lCost S T x y tau) := by
  intro y
  apply uscAt_of_seq
  intro q hq A hA
  obtain ⟨alpha, halpha, hstart, hend, halphaA⟩ :=
    exists_cost_curve (I := I) S hS T x y tau htau hslab A hA
  exact lCost_lt_event (I := I) S hS T (T - tau) T tau htau
    (fun _ hr ↦ D.regular_subset (hslab hr))
    (sqrt_back_mem (T := T) htau.le) x y alpha halpha hstart hend
    (fun s hs ↦ hslab (sqrt_back_mem (T := T) htau.le s hs))
    A halphaA q hq

omit [NeZero (Module.finrank Real E)] in
private theorem redDensity_param_lsc
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x y : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    LowerSemicontinuousAt
      (fun p : Real × M ↦ redDensity S p.1 p.2 y tau) (T, x) := by
  let phi : Real → Real := fun r ↦ Real.exp
    (-r / (2 * Real.sqrt tau) -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  have hphi : Continuous phi := by
    dsimp only [phi]
    fun_prop
  have hphiAnti : Antitone phi := by
    intro a b hab
    apply Real.exp_le_exp.mpr
    have hden : 0 < 2 * Real.sqrt tau := mul_pos (by norm_num) (Real.sqrt_pos.2 htau)
    have hdiv : a / (2 * Real.sqrt tau) ≤ b / (2 * Real.sqrt tau) :=
      (div_le_div_iff_of_pos_right hden).2 hab
    have hneg : -b / (2 * Real.sqrt tau) ≤ -a / (2 * Real.sqrt tau) := by
      simpa only [neg_div] using neg_le_neg hdiv
    exact sub_le_sub_right
      (sub_le_sub_right hneg
        (((Module.finrank Real E : Real) / 2) * Real.log tau))
      (((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  have hcost := lCost_param_usc (I := I) S hS T x y tau htau hslab
  simpa only [Function.comp_def, phi, redDensity, redLength, neg_div] using
    hphi.continuousAt.comp_upperSemicontinuousAt_antitone hcost hphiAnti

omit [NeZero (Module.finrank Real E)] in
private theorem redDensity_y_lsc
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    LowerSemicontinuous (fun y : M ↦ redDensity S T x y tau) := by
  let phi : Real → Real := fun r ↦ Real.exp
    (-r / (2 * Real.sqrt tau) -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  have hphi : Continuous phi := by
    dsimp only [phi]
    fun_prop
  have hphiAnti : Antitone phi := by
    intro a b hab
    apply Real.exp_le_exp.mpr
    have hden : 0 < 2 * Real.sqrt tau := mul_pos (by norm_num) (Real.sqrt_pos.2 htau)
    have hdiv : a / (2 * Real.sqrt tau) ≤ b / (2 * Real.sqrt tau) :=
      (div_le_div_iff_of_pos_right hden).2 hab
    have hneg : -b / (2 * Real.sqrt tau) ≤ -a / (2 * Real.sqrt tau) := by
      simpa only [neg_div] using neg_le_neg hdiv
    exact sub_le_sub_right
      (sub_le_sub_right hneg
        (((Module.finrank Real E : Real) / 2) * Real.log tau))
      (((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  simpa only [Function.comp_def, phi, redDensity, redLength, neg_div] using
    hphi.comp_upperSemicontinuous_antitone
      (lCost_y_usc (I := I) S hS T x tau htau hslab) hphiAnti

omit [NeZero (Module.finrank Real E)] [CompactSpace M] in
private theorem chartDensity_time_cont
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {t : Real} (ht : t ∈ D.regular)
    (alpha : M) {z : E} (hz : z ∈ (extChartAt I alpha).target) :
    ContinuousAt
      (fun r ↦ chartDensity (I := I) (S.base.metric r) alpha
        ((extChartAt I alpha).symm z)) t := by
  classical
  have hzInt : z ∈ interior (extChartAt I alpha).target := by
    simpa only [(isOpen_extChartAt_target (I := I) alpha).interior_eq] using hz
  have hentry (i j : Fin (Module.finrank Real E)) : ContinuousAt
      (fun r ↦ chartGramOnE (I := I) (S.base.metric r) alpha i j z) t := by
    have hjoint :=
      (MetricFamilySmoothOn.chartGramOnE_contDiffOn
        (I := I) (G := S.family) hS.smoothMetric
        (J := D.regular) (fun _ hr ↦ hr) alpha i j).continuousOn
    have hat : ContinuousAt
        (fun q : Real × E ↦
          chartGramOnE (I := I) (S.base.metric q.1) alpha i j q.2) (t, z) :=
      hjoint.continuousAt
        ((D.regular_isOpen.prod isOpen_interior).mem_nhds ⟨ht, hzInt⟩)
    have hpair : ContinuousAt (fun r : Real ↦ (r, z)) t := by fun_prop
    change Tendsto (fun r ↦
      chartGramOnE (I := I) (S.base.metric r) alpha i j z)
      (nhds t) (nhds (chartGramOnE (I := I) (S.base.metric t) alpha i j z))
    simpa only [Function.comp_def] using
      (@Filter.Tendsto.comp Real (Real × E) Real
        (fun r : Real ↦ (r, z))
        (fun q : Real × E ↦
          chartGramOnE (I := I) (S.base.metric q.1) alpha i j q.2)
        (nhds t) (nhds (t, z))
        (nhds (chartGramOnE (I := I) (S.base.metric t) alpha i j z))
        hat hpair)
  have hdet : ContinuousAt
      (fun r ↦
        (chartGramMatrix (I := I) (S.base.metric r) alpha
          ((extChartAt I alpha).symm z)).det) t := by
    have hmat : ContinuousAt
        (fun r ↦ chartGramMatrix (I := I) (S.base.metric r) alpha
          ((extChartAt I alpha).symm z)) t :=
      continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ by
        simpa only [chartGramOnE_def] using hentry i j
    exact (continuous_id.matrix_det).continuousAt.comp hmat
  simpa only [Function.comp_def, chartDensity] using
    Real.continuous_sqrt.continuousAt.comp hdet

private def chartRedTerm
    (S : SolutionOn (I := I) (M := M) D) (tau : Real)
    (p : Real × M) (alpha : M) : ENNReal :=
  ∫⁻ z in (extChartAt I alpha).target,
    ENNReal.ofReal (chartDensity (I := I) (S.base.metric (p.1 - tau))
        alpha ((extChartAt I alpha).symm z)) *
      (ENNReal.ofReal
          ((chartAtlasPOU I M alpha : M → Real)
            ((extChartAt I alpha).symm z)) *
        ENNReal.ofReal
          (redDensity S p.1 p.2 ((extChartAt I alpha).symm z) tau))
    ∂modelHaar (E := E)

omit [NeZero (Module.finrank Real E)] in
private theorem redVolume_chart_sum
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    redVolume S T x tau =
      ∑ alpha ∈ chartAtlasPOUFinset (I := I) (M := M),
        chartRedTerm (I := I) S tau (T, x) alpha := by
  classical
  let F : M → ENNReal := fun y ↦ ENNReal.ofReal (redDensity S T x y tau)
  have hF : Measurable F := by
    exact ENNReal.measurable_ofReal.comp
      (redDensity_y_lsc (I := I) S hS T x tau htau hslab).measurable
  unfold redVolume
  rw [riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M),
    lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro alpha _halpha
  let rho : M → ENNReal := fun y ↦
    ENNReal.ofReal ((chartAtlasPOU I M alpha : M → Real) y)
  have hrho : Measurable rho :=
    measurable_ofReal_pou_weight (chartAtlasPOU I M) alpha
  have hprod : Measurable (rho * F) := hrho.mul hF
  rw [lintegral_withDensity_eq_lintegral_mul
      (μ := chartLocalMeasure (I := I) (S.base.metric (T - tau)) alpha)
      (f := rho) hrho (g := F) hF,
    chartLocalMeasure_lintegral (I := I) (S.base.metric (T - tau)) alpha hprod]
  rfl

omit [NeZero (Module.finrank Real E)] in
private theorem chartRedTerm_liminf
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (q : Nat → Real × M) (hq : Tendsto q atTop (nhds (T, x)))
    (hslabq : ∀ n, Icc ((q n).1 - tau) (q n).1 ⊆ D.regular)
    (alpha : M) :
    chartRedTerm (I := I) S tau (T, x) alpha ≤
      liminf (fun n ↦ chartRedTerm (I := I) S tau (q n) alpha) atTop := by
  let mu : Measure E :=
    (modelHaar (E := E)).restrict (extChartAt I alpha).target
  let A : Nat → E → ENNReal := fun n z ↦
    ENNReal.ofReal (chartDensity (I := I) (S.base.metric ((q n).1 - tau))
      alpha ((extChartAt I alpha).symm z))
  let A₀ : E → ENNReal := fun z ↦
    ENNReal.ofReal (chartDensity (I := I) (S.base.metric (T - tau))
      alpha ((extChartAt I alpha).symm z))
  let B : E → ENNReal := fun z ↦
    ENNReal.ofReal ((chartAtlasPOU I M alpha : M → Real)
      ((extChartAt I alpha).symm z))
  let C : Nat → E → ENNReal := fun n z ↦
    ENNReal.ofReal (redDensity S (q n).1 (q n).2
      ((extChartAt I alpha).symm z) tau)
  let C₀ : E → ENNReal := fun z ↦
    ENNReal.ofReal (redDensity S T x ((extChartAt I alpha).symm z) tau)
  have hsymm : AEMeasurable (extChartAt I alpha).symm mu := by
    simpa only [mu] using
      aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) alpha
  have hA (n : Nat) : AEMeasurable (A n) mu := by
    simpa only [A, mu] using
      aemeasurable_chartDensity_symm_pullback
        (I := I) (S.base.metric ((q n).1 - tau)) alpha
  have hA₀ : AEMeasurable A₀ mu := by
    simpa only [A₀, mu] using
      aemeasurable_chartDensity_symm_pullback
        (I := I) (S.base.metric (T - tau)) alpha
  have hB : AEMeasurable B mu := by
    have hpou : Measurable (fun y : M ↦
        (chartAtlasPOU I M alpha : M → Real) y) :=
      (chartAtlasPOU I M alpha).contMDiff.continuous.measurable
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (hpou.comp_aemeasurable hsymm)
  have hC (n : Nat) : AEMeasurable (C n) mu := by
    have hred : Measurable (fun y : M ↦
        redDensity S (q n).1 (q n).2 y tau) :=
      (redDensity_y_lsc (I := I) S hS (q n).1 (q n).2 tau htau
        (hslabq n)).measurable
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (hred.comp_aemeasurable hsymm)
  have hC₀ : AEMeasurable C₀ mu := by
    have hred : Measurable (fun y : M ↦ redDensity S T x y tau) :=
      (redDensity_y_lsc (I := I) S hS T x tau htau hslab).measurable
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (hred.comp_aemeasurable hsymm)
  have htime : Tendsto (fun n ↦ (q n).1 - tau) atTop (nhds (T - tau)) := by
    have hT : Tendsto (fun n ↦ (q n).1) atTop (nhds T) := by
      simpa only [Function.comp_def] using continuous_fst.continuousAt.tendsto.comp hq
    exact hT.sub tendsto_const_nhds
  have hpoint : ∀ᵐ z ∂mu,
      A₀ z * (B z * C₀ z) ≤
        liminf (fun n ↦ A n z * (B z * C n z)) atTop := by
    have htarget : ∀ᵐ z ∂mu, z ∈ (extChartAt I alpha).target := by
      simpa only [mu] using
        ae_restrict_mem (measurableSet_extChartAt_target (I := I) alpha)
    filter_upwards [htarget] with z hz
    have hAtend : Tendsto (fun n ↦ A n z) atTop (nhds (A₀ z)) := by
      have hdensity : Tendsto
          (fun n ↦ chartDensity (I := I) (S.base.metric ((q n).1 - tau))
            alpha ((extChartAt I alpha).symm z)) atTop
          (nhds (chartDensity (I := I) (S.base.metric (T - tau))
            alpha ((extChartAt I alpha).symm z))) :=
        (chartDensity_time_cont S hS (hslab ⟨le_rfl, sub_le_self T htau.le⟩)
          alpha hz).tendsto.comp htime
      exact (ENNReal.continuous_ofReal.tendsto _).comp hdensity
    have hABtend : Tendsto (fun n ↦ A n z * B z) atTop
        (nhds (A₀ z * B z)) := by
      apply ENNReal.Tendsto.mul_const hAtend
      exact Or.inr ENNReal.ofReal_ne_top
    have hCred : LowerSemicontinuousAt
        (fun p : Real × M ↦ ENNReal.ofReal
          (redDensity S p.1 p.2 ((extChartAt I alpha).symm z) tau)) (T, x) :=
      ENNReal.continuous_ofReal.continuousAt.comp_lowerSemicontinuousAt
        (redDensity_param_lsc (I := I) S hS T x
          ((extChartAt I alpha).symm z) tau htau hslab) ENNReal.ofReal_mono
    have hCliminf : C₀ z ≤ liminf (fun n ↦ C n z) atTop := by
      apply (le_liminf_iff).2
      intro c hc
      exact hq (hCred c hc)
    calc
      A₀ z * (B z * C₀ z) = (A₀ z * B z) * C₀ z := by ac_rfl
      _ ≤ liminf (fun n ↦ A n z * B z) atTop *
          liminf (fun n ↦ C n z) atTop := by
        rw [hABtend.liminf_eq]
        exact mul_le_mul' le_rfl hCliminf
      _ ≤ liminf (fun n ↦ (A n z * B z) * C n z) atTop :=
        ENNReal.le_liminf_mul
      _ = liminf (fun n ↦ A n z * (B z * C n z)) atTop := by
        congr 1
        funext n
        ac_rfl
  have hfatou :
      (∫⁻ z, A₀ z * (B z * C₀ z) ∂mu) ≤
        liminf (fun n ↦ ∫⁻ z, A n z * (B z * C n z) ∂mu) atTop := by
    calc
      (∫⁻ z, A₀ z * (B z * C₀ z) ∂mu) ≤
          ∫⁻ z, liminf (fun n ↦ A n z * (B z * C n z)) atTop ∂mu :=
        lintegral_mono_ae hpoint
      _ ≤ liminf (fun n ↦ ∫⁻ z, A n z * (B z * C n z) ∂mu) atTop :=
        lintegral_liminf_le' fun n ↦ (hA n).mul (hB.mul (hC n))
  simpa only [chartRedTerm, mu, A, A₀, B, C, C₀] using hfatou

omit [NeZero (Module.finrank Real E)] in
private theorem slab_eventually
    (D : RealTimeInterval) (T tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    ∀ᶠ R in nhds T, Icc (R - tau) R ⊆ D.regular := by
  have hreg : ∀ s ∈ uIcc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hslab
    apply sqrt_back_mem htau.le s
    simpa only [uIcc_of_le (Real.sqrt_nonneg tau)] using hs
  filter_upwards [lRegTime_nhds D T 0 (Real.sqrt tau) hreg] with R hback
  apply back_slab
  intro s hs
  apply hback s
  simpa only [uIcc_of_le (Real.sqrt_nonneg tau)] using hs

omit [NeZero (Module.finrank Real E)] in
private theorem chartRedTerm_seq
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (alpha : M) (q : Nat → Real × M)
    (hq : Tendsto q atTop (nhds (T, x))) :
    chartRedTerm (I := I) S tau (T, x) alpha ≤
      liminf (fun n ↦ chartRedTerm (I := I) S tau (q n) alpha) atTop := by
  have hT : Tendsto (fun n ↦ (q n).1) atTop (nhds T) :=
    continuous_fst.continuousAt.tendsto.comp hq
  have hslabq : ∀ᶠ n in atTop,
      Icc ((q n).1 - tau) (q n).1 ⊆ D.regular :=
    hT (slab_eventually D T tau htau hslab)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hslabq
  let q' : Nat → Real × M := fun n ↦ q (n + N)
  have hq' : Tendsto q' atTop (nhds (T, x)) :=
    hq.comp (tendsto_add_atTop_nat N)
  have hslabq' (n : Nat) : Icc ((q' n).1 - tau) (q' n).1 ⊆ D.regular := by
    exact hN (n + N) (Nat.le_add_left N n)
  have hshift :=
    chartRedTerm_liminf (I := I) S hS T x tau htau hslab q' hq'
      hslabq' alpha
  calc
    chartRedTerm (I := I) S tau (T, x) alpha ≤
        liminf (fun n ↦ chartRedTerm (I := I) S tau (q (n + N)) alpha) atTop := by
      simpa only [q'] using hshift
    _ = liminf (fun n ↦ chartRedTerm (I := I) S tau (q n) alpha) atTop :=
      liminf_nat_add
        (fun n ↦ chartRedTerm (I := I) S tau (q n) alpha) N

omit [NeZero (Module.finrank Real E)] in
private theorem chartRedTerm_lsc
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) (alpha : M) :
    LowerSemicontinuousAt
      (fun p : Real × M ↦ chartRedTerm (I := I) S tau p alpha) (T, x) := by
  apply lscAt_of_seq
  intro q hq
  exact chartRedTerm_seq (I := I) S hS T x tau htau hslab alpha q hq

omit [NeZero (Module.finrank Real E)] in
theorem redVolume_lsc
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    LowerSemicontinuousAt
      (fun p : Real × M ↦ redVolume S p.1 p.2 tau) (T, x) := by
  classical
  let K : Finset M := chartAtlasPOUFinset (I := I) (M := M)
  have hsum : LowerSemicontinuousAt
      (fun p : Real × M ↦
        ∑ alpha ∈ K, chartRedTerm (I := I) S tau p alpha) (T, x) := by
    apply lowerSemicontinuousAt_sum
    intro alpha _halpha
    exact chartRedTerm_lsc (I := I) S hS T x tau htau hslab alpha
  have hslabnh : ∀ᶠ p : Real × M in nhds (T, x),
      Icc (p.1 - tau) p.1 ⊆ D.regular := by
    have hfirst : Tendsto (fun p : Real × M ↦ p.1)
        (nhds (T, x)) (nhds T) := by
      simpa only using continuous_fst.continuousAt.tendsto
    exact hfirst.eventually (slab_eventually D T tau htau hslab)
  rw [← lowerSemicontinuousWithinAt_univ_iff] at hsum ⊢
  apply hsum.congr_of_eventuallyEq (mem_univ (T, x))
  have hslabnh' : ∀ᶠ p : Real × M in nhdsWithin (T, x) univ,
      Icc (p.1 - tau) p.1 ⊆ D.regular := by
    simpa only [nhdsWithin_univ] using hslabnh
  filter_upwards [hslabnh'] with p hp
  exact (redVolume_chart_sum (I := I) S hS p.1 p.2 tau htau hp).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman
