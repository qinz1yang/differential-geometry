import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTensorContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureBound
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Analysis.Calculus.FDeriv.Extend

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem riemannianBallOf_subset_riemannianClosedBallOf_of_inner_le_mul
    (g h : SmoothRiemannianMetric I M) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ x v, h.inner x v v ≤ c * g.inner x v v) (p : M) (r : ℝ) :
    riemannianBallOf (I := I) g p r ⊆
      riemannianClosedBallOf (I := I) h p (Real.sqrt c * r) := by
  intro y hy
  simp only [riemannianClosedBallOf, riemannianBallOf, Set.mem_ofPred_eq] at hy ⊢
  calc riemannianEDistOf (I := I) h p y
      ≤ ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g p y :=
        edistOf_le_of_quad g h hc hgh p y
    _ ≤ ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal r :=
        mul_le_mul_right hy.le _
    _ = ENNReal.ofReal (Real.sqrt c * r) :=
        (ENNReal.ofReal_mul (Real.sqrt_nonneg c)).symm

private theorem riemannianBallOf_subset_of_mul_inner_le
    (g h : SmoothRiemannianMetric I M) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ x v, c * g.inner x v v ≤ h.inner x v v) (p : M) (r : ℝ) :
    riemannianBallOf (I := I) h p (Real.sqrt c * r) ⊆
      riemannianBallOf (I := I) g p r := by
  intro y hy
  simp only [riemannianBallOf, Set.mem_ofPred_eq] at hy ⊢
  have hle := le_edistOf_of_quad g h hc hgh p y
  have hlt : ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g p y <
      ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal r := by
    refine lt_of_le_of_lt hle ?_
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
    exact hy
  have hc0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have htop : ENNReal.ofReal (Real.sqrt c) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_lt_mul_iff_right hc0 htop).mp hlt

end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem standardCapA0_gt_neg_three : -3 < standardCapA0 := by
  have hpi : 0 < Real.pi / Real.sqrt 2 :=
    div_pos Real.pi_pos (Real.sqrt_pos.2 (by norm_num))
  rw [standardCapA0]
  linarith

private theorem standardCapA0_lt_four : standardCapA0 < 4 := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hpi : Real.pi / Real.sqrt 2 ≤ Real.pi := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    nlinarith [Real.pi_pos]
  rw [standardCapA0]
  linarith [Real.pi_lt_four]

theorem standardCapClosedCore_eq_riemannianClosedBallOf :
    standardCapClosedCore = riemannianClosedBallOf standardCapMetric 0 standardCapL := by
  have hL : 0 < standardCapL := by
    have hpi : 0 < Real.pi / Real.sqrt 2 :=
      div_pos Real.pi_pos (Real.sqrt_pos.2 (by norm_num))
    rw [standardCapL, standardCapA0]
    linarith
  ext y
  rw [standardCapClosedCore, Metric.mem_closedBall, riemannianClosedBallOf, Set.mem_ofPred_eq,
    standardCap_edist_zero]
  simp only [dist_eq_norm, sub_zero]
  exact (ENNReal.ofReal_le_ofReal_iff hL.le).symm

theorem riemannianBallOf_standardCapMetric {r : ℝ} (hr : 0 < r) :
    riemannianBallOf standardCapMetric 0 r = Metric.ball (0 : ThreeSpace) r := by
  ext y
  rw [riemannianBallOf, Set.mem_ofPred_eq, Metric.mem_ball, standardCap_edist_zero]
  simp only [dist_eq_norm, sub_zero]
  exact ENNReal.ofReal_lt_ofReal_iff hr

private theorem capRadius_lower {ε R : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 200)
    (hR₁ : 1 ≤ R) (hR₂ : R ≤ 200) : R - 1 ≤ Real.sqrt (1 - ε) * R := by
  have h1 : 0 ≤ 1 - ε := by linarith
  have h2 : 1 - ε ≤ 1 := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hsqrt : 1 - ε ≤ Real.sqrt (1 - ε) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hmul : (1 - ε) * R ≤ Real.sqrt (1 - ε) * R := mul_le_mul_of_nonneg_right hsqrt hR0
  nlinarith

private theorem capRadius_upper {ε R : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 200)
    (hR₁ : 1 ≤ R) (hR₂ : R ≤ 200) : Real.sqrt (1 + ε) * R ≤ R + 1 := by
  have hR0 : 0 ≤ R := by linarith
  have hsqrt : Real.sqrt (1 + ε) ≤ 1 + ε := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hmul : Real.sqrt (1 + ε) * R ≤ (1 + ε) * R := mul_le_mul_of_nonneg_right hsqrt hR0
  nlinarith

theorem riemannianBallOf_sandwich_of_quadratic_close
    (h : SmoothRiemannianMetric ThreeModel ThreeSpace) {ε R s : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < 1 / 200) (hR₁ : 1 ≤ R) (hR₂ : R ≤ 200) (hs : 0 < s)
    (hupper : ∀ x v, h.inner x v v ≤ (1 + ε) * standardCapMetric.inner x v v)
    (hlower : ∀ x v, (1 - ε) * standardCapMetric.inner x v v ≤ h.inner x v v)
    (p : ThreeSpace) :
    riemannianBallOf h p ((R - 1) * s) ⊆ riemannianBallOf standardCapMetric p (R * s) ∧
      riemannianBallOf standardCapMetric p (R * s) ⊆
        riemannianClosedBallOf h p ((R + 1) * s) := by
  have hc₁ : (0 : ℝ) < 1 - ε := by linarith
  have hc₂ : (0 : ℝ) < 1 + ε := by linarith
  have houter := riemannianBallOf_subset_riemannianClosedBallOf_of_inner_le_mul
    standardCapMetric h hc₂ hupper p (R * s)
  have hinner := riemannianBallOf_subset_of_mul_inner_le standardCapMetric h hc₁ hlower p (R * s)
  have hlow := capRadius_lower hε0 hε hR₁ hR₂
  have hup := capRadius_upper hε0 hε hR₁ hR₂
  refine ⟨(riemannianBallOf_mono h p ?_).trans hinner, houter.trans ?_⟩
  · have hstep : (R - 1) * s ≤ (Real.sqrt (1 - ε) * R) * s :=
      mul_le_mul_of_nonneg_right hlow hs.le
    simpa only [mul_assoc] using hstep
  · refine riemannianClosedBallOf_mono h p ?_
    have hstep : (Real.sqrt (1 + ε) * R) * s ≤ (R + 1) * s :=
      mul_le_mul_of_nonneg_right hup hs.le
    simpa only [mul_assoc] using hstep

theorem standardCapBall_sandwich_of_quadratic_close
    (h : SmoothRiemannianMetric ThreeModel ThreeSpace) {ε s : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < 1 / 200) (hs : 0 < s)
    (hupper : ∀ x v, h.inner x v v ≤ (1 + ε) * standardCapMetric.inner x v v)
    (hlower : ∀ x v, (1 - ε) * standardCapMetric.inner x v v ≤ h.inner x v v)
    (p : ThreeSpace) :
    riemannianBallOf h p ((standardCapA0 + 3) * s) ⊆
        riemannianBallOf standardCapMetric p ((standardCapA0 + 4) * s) ∧
      riemannianBallOf standardCapMetric p ((standardCapA0 + 4) * s) ⊆
        riemannianClosedBallOf h p ((standardCapA0 + 5) * s) := by
  have h1 := standardCapA0_gt_neg_three
  have h2 := standardCapA0_lt_four
  have hmain := riemannianBallOf_sandwich_of_quadratic_close (R := standardCapA0 + 4) h hε0 hε
    (by linarith) (by linarith) hs hupper hlower p
  simpa only [show standardCapA0 + 4 - 1 = standardCapA0 + 3 from by ring,
    show standardCapA0 + 4 + 1 = standardCapA0 + 5 from by ring] using hmain

namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}}

namespace IncomingSlab

variable {a s : ℝ} (G : P.IncomingSlab a s)

theorem continuousOn_riemannNorm :
    ContinuousOn (fun q : ℝ × P.Carrier =>
      Real.sqrt (normSq0S (G.flow.base.metric q.1) q.2 4 (G.flow.base.rm04 q.1 q.2)))
      (Ico a s ×ˢ univ) :=
  (P.tensorFamily_normSq_continuousOn G.equation.smoothMetric.metricTensor_cont
    G.equation.rm04Cont).sqrt

theorem continuousOn_riemannNorm_apply (x : P.Carrier) :
    ContinuousOn (fun t : ℝ => G.riemannNorm t x) (Ico a s) := by
  have hpair : ContinuousOn (fun t : ℝ => (t, x)) (Ico a s) :=
    continuousOn_id.prodMk continuousOn_const
  have hmaps : MapsTo (fun t : ℝ => (t, x)) (Ico a s) (Ico a s ×ˢ (univ : Set P.Carrier)) :=
    fun _ ht => ⟨ht, mem_univ x⟩
  have hcomp := (G.continuousOn_riemannNorm).comp hpair hmaps
  simpa [riemannNorm, Function.comp_def] using hcomp

theorem tendsto_riemannNorm_nhdsGT (x : P.Carrier) :
    Tendsto (fun t : ℝ => G.riemannNorm t x) (𝓝[>] a) (𝓝 (G.riemannNorm a x)) := by
  have hci : ContinuousWithinAt (fun t : ℝ => G.riemannNorm t x) (Ico a s) a :=
    (G.continuousOn_riemannNorm_apply x).continuousWithinAt ⟨le_rfl, G.lt⟩
  have hle : 𝓝[Ioo a s] a ≤ 𝓝[Ico a s] a :=
    nhdsWithin_mono a fun t ht => ⟨ht.1.le, ht.2⟩
  have h2 : Tendsto (fun t : ℝ => G.riemannNorm t x) (𝓝[Ioo a s] a)
      (𝓝 (G.riemannNorm a x)) := hci.mono_left hle
  rwa [nhdsWithin_Ioo_eq_nhdsGT G.lt] at h2

theorem continuousOn_ricciAt (x : P.Carrier) (X Y : TangentSpace ThreeModel x) :
    ContinuousOn (fun t => G.flow.ricciAt t x (vec2 X Y)) (Ico a s) := by
  have heval := tensor0SFamilyContinuousOnSet.eval_continuous
    (I := ThreeModel) (M := P.Carrier) (s := 2) G.equation.ricciCont
    (P := Ico a s) (τ := fun t => t.1) (b := fun _ => x)
    continuous_subtype_val (fun t => t.2) continuous_const
    (v := fun i _ => vec2 X Y i) (fun _ => continuous_const)
  rw [continuousOn_iff_continuous_domRestrict]
  exact heval

end IncomingSlab

private theorem hasDerivWithinAt_of_continuousOn_Ico
    {a s : ℝ} (has : a < s) {f F : ℝ → ℝ}
    (hf : ContinuousOn f (Ico a s)) (hF : ContinuousOn F (Ico a s))
    (hderiv : ∀ t ∈ Ioo a s, HasDerivWithinAt f (F t) (Ico a s) t) :
    HasDerivWithinAt f (F a) (Ici a) a := by
  have hd (t : ℝ) (ht : t ∈ Ioo a s) : HasDerivAt f (F t) t :=
    (hderiv t ht).hasDerivAt (Ico_mem_nhds ht.1 ht.2)
  have hdiff : DifferentiableOn ℝ f (Ioo a s) :=
    fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  have hFlim0 : Tendsto F (𝓝[Ioo a s] a) (𝓝 (F a)) :=
    (hF.continuousWithinAt ⟨le_rfl, has⟩).mono_left
      (nhdsWithin_mono a fun t ht => ⟨ht.1.le, ht.2⟩)
  have hFlim : Tendsto F (𝓝[>] a) (𝓝 (F a)) := by
    rwa [nhdsWithin_Ioo_eq_nhdsGT has] at hFlim0
  refine hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
    ((hf.continuousWithinAt ⟨le_rfl, has⟩).mono fun t ht => ⟨ht.1.le, ht.2⟩)
    (Ioo_mem_nhdsGT has) ?_
  refine hFlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT has] with t ht
  exact (hd t ht).deriv.symm

namespace IncomingSlab

variable {a s : ℝ} (G : P.IncomingSlab a s)

theorem hasDerivWithinAt_inner_at_start (x : P.Carrier) (X Y : TangentSpace ThreeModel x) :
    HasDerivWithinAt (fun t => (G.flow.base.metric t).inner x X Y)
      (-2 * G.flow.ricciAt a x (vec2 X Y)) (Ici a) a := by
  refine hasDerivWithinAt_of_continuousOn_Ico
    (f := fun t : ℝ => (G.flow.base.metric t).inner x X Y)
    (F := fun t : ℝ => -2 * G.flow.ricciAt t x (vec2 X Y)) G.lt ?_ ?_ ?_
  · have h : ContinuousOn (fun t : ℝ => (G.flow.base.metric t).inner x X Y) (Ico a s) :=
      G.equation.smoothMetric.coeff_cont x X Y
    exact h
  · exact continuousOn_const.mul (G.continuousOn_ricciAt x X Y)
  · intro t ht
    exact G.equation.equation ⟨t, ht⟩ x X Y

theorem not_exists_closedSlab_of_singularEndpoint (h : G.SingularEndpoint) :
    ¬ ∃ H : P.ClosedSlab a s, H.flow.base = G.flow.base := by
  rintro ⟨H, hbase⟩
  obtain ⟨K, hK, hbound⟩ := H.curvature_bound P
  refine G.terminalRegularRegion_ne_univ_of_singularEndpoint h ?_
  apply eq_univ_of_forall
  intro x
  refine ⟨univ, isOpen_univ, mem_univ x, a, ⟨le_rfl, G.lt⟩, K, hK, ?_⟩
  intro y _ t ht
  have hy := hbound t ⟨ht.1, ht.2.le⟩ y
  simpa only [riemannNorm, ← hbase] using hy

end IncomingSlab

end OrientedThreeStage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
