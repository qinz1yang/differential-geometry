import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Family.Comparison
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundaryDerivLimit

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set DifferentialGeometry.Tensor0SBundle

open scoped Manifold ContDiff Bundle Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
private theorem tensor_eval_cont
    {K : Set Real}
    {A : (t : Real) → (x : M) →
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun s : Real ↦ A s x (vec2 v w)) K := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact hA.eval_continuous (P := {s : Real // s ∈ K}) (τ := Subtype.val)
    (b := fun _ ↦ x) continuous_subtype_val (fun p ↦ p.2) continuous_const
    (v := fun i _ ↦ vec2 v w i) (fun _ ↦ continuous_const)

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricPDE_Icc
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real}
    (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) :
    ∀ t ∈ Set.Icc a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : Real ↦ (S.base.metric s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (S.base.metric t) x v w)
        (Set.Icc a b) t := by
  have hmetricCont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun s : Real ↦ (S.base.metric s).inner x v w)
        (Set.Icc a b) := by
    intro x v w
    refine (tensor_eval_cont (I := I) hS.smoothMetric.metricTensor_cont x v w).mono ?_
    exact hslab
  have hricCont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn
        (fun s : Real ↦
          (-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w)
        (Set.Icc a b) := by
    intro x v w
    have hcont := (tensor_eval_cont (I := I) hS.ricciCont x v w).mono hslab
    refine (hcont.congr fun s _ ↦ ?_).const_mul (-2)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
      SolutionFamily.ricciAt]
    exact (metricRicciAt_apply_eq_ricciTensor (S.base.metric s) x v w).symm
  intro t ht x v w
  apply Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Icc_of_hasDerivAt_Ioo
    (hmetricCont x v w) (hricCont x v w) ?_ ht
  intro s hs
  have hraw := metricDerivAt (I := I) S hS (⟨s, hreg hs⟩ : RealTimeInterval.RegularTime D) x v w
  simpa [SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor] using hraw

end

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem metric_inner_antitoneOn_of_ricci_nonnegative
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (_hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioc a b ⊆ D.regular)
    (hRic : ∀ t ∈ Set.Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      0 ≤ ricciTensor (I := I) (S.base.metric t) x v v)
    (x : M) (v : TangentSpace I x) :
    AntitoneOn (fun t : Real ↦ (S.base.metric t).inner x v v)
      (Set.Icc a b) := by
  have hpde := metricPDE_Icc (I := I) S hS hslab
    (fun t ht => hreg ⟨ht.1, ht.2.le⟩)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
  · intro t ht
    exact (hpde t ht x v v).continuousWithinAt
  · intro t ht
    exact (hpde t (interior_subset ht) x v v).mono interior_subset
  · intro t ht
    have hnonneg := hRic t (interior_subset ht) x v
    nlinarith

theorem exp_bounds_log
    {fa fb R : Real} (hfa : 0 < fa) (hfb : 0 < fb)
    (hlog : |Real.log fb - Real.log fa| ≤ R) :
    Real.exp (-R) * fa ≤ fb ∧ fb ≤ Real.exp R * fa := by
  have hlo : -R ≤ Real.log fb - Real.log fa := (abs_le.mp hlog).1
  have hhi : Real.log fb - Real.log fa ≤ R := (abs_le.mp hlog).2
  constructor
  · have hratio : Real.exp (-R) ≤ fb / fa := by
      apply (Real.le_log_iff_exp_le (div_pos hfb hfa)).mp
      simpa [Real.log_div hfb.ne' hfa.ne'] using hlo
    calc
      Real.exp (-R) * fa ≤ (fb / fa) * fa :=
        mul_le_mul_of_nonneg_right hratio hfa.le
      _ = fb := by field_simp
  · have hratio : fb / fa ≤ Real.exp R := by
      apply (Real.log_le_iff_le_exp (div_pos hfb hfa)).mp
      simpa [Real.log_div hfb.ne' hfa.ne'] using hhi
    calc
      fb = (fb / fa) * fa := by field_simp
      _ ≤ Real.exp R * fa := mul_le_mul_of_nonneg_right hratio hfa.le

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [IsManifold I 1 M]
  [SigmaCompactSpace M] in
private theorem metric_deriv_bound
    (g : ℝ → SmoothRiemannianMetric I M) {a b K : ℝ}
    (hpde : ∀ r ∈ Set.Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      HasDerivWithinAt (fun u => (g u).inner x v v)
        (-2 * ricciTensor (g r) x v v) (Set.Icc a b) r)
    (hric : ∀ r ∈ Set.Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (g r) x v v| ≤ K * (g r).inner x v v) :
    ∀ r ∈ Set.Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      ∃ d : ℝ, HasDerivWithinAt (fun u => (g u).inner x v v) d (Set.Icc a b) r ∧
        |d| ≤ (2 * K) * (g r).inner x v v := by
  intro r hr x v
  refine ⟨_, hpde r hr x v, ?_⟩
  rw [abs_mul, abs_neg, abs_two]
  calc
    2 * |ricciTensor (g r) x v v| ≤ 2 * (K * (g r).inner x v v) :=
      mul_le_mul_of_nonneg_left (hric r hr x v) (by norm_num)
    _ = (2 * K) * (g r).inner x v v := by ring

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M] in
private theorem metric_pair_Icc
    (g : Real → SmoothRiemannianMetric I M)
    {a b K s t : Real}
    (hpde : ∀ r ∈ Set.Icc a b, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun u : Real ↦ (g u).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (g r) x v w)
          (Set.Icc a b) r)
    (hric : ∀ r ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (g r) x v v| ≤
          K * (g r).inner x v v)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (x : M) (v : TangentSpace I x) :
    Real.exp (-(2 * K * |s - t|)) * (g t).inner x v v ≤
        (g s).inner x v v ∧
      (g s).inner x v v ≤
        Real.exp (2 * K * |s - t|) * (g t).inner x v v := by
  have hd := metric_deriv_bound g (fun r hr x v => hpde r hr x v v) hric
  have hst := inner_le_exp_mul_inner_of_abs_deriv_le g x v (fun r hr => hd r hr x v) hs ht
  have hts := inner_le_exp_mul_inner_of_abs_deriv_le g x v (fun r hr => hd r hr x v) ht hs
  rw [abs_sub_comm t s] at hts
  refine ⟨?_, hst⟩
  calc
    Real.exp (-(2 * K * |s - t|)) * (g t).inner x v v ≤
        Real.exp (-(2 * K * |s - t|)) *
          (Real.exp (2 * K * |s - t|) * (g s).inner x v v) :=
      mul_le_mul_of_nonneg_left hts (Real.exp_pos _).le
    _ = (g s).inner x v v := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

omit [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
  [IsManifold I 1 M]
  [SigmaCompactSpace M] in
theorem metricEquiv_Icc_on
    (g : Real → SmoothRiemannianMetric I M) (B : Set M)
    {a b K : Real}
    (hpde : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : Real ↦ (g s).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (g t) x v w)
          (Set.Icc a b) t)
    (hric : ∀ t ∈ Set.Icc a b, ∀ x ∈ B,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (g t) x v v| ≤
          K * (g t).inner x v v) :
    ∀ s ∈ Set.Icc a b, ∀ x ∈ B,
      ∀ v : TangentSpace I x,
        Real.exp (-(2 * K * (s - a))) * (g a).inner x v v ≤
            (g s).inner x v v ∧
          (g s).inner x v v ≤
            Real.exp (2 * K * (s - a)) * (g a).inner x v v := by
  intro s hs x hxB v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hpos : ∀ t : Real, 0 < (g t).inner x v v :=
    fun t ↦ (g t).pos x v hv
  have hsub : Set.Icc a s ⊆ Set.Icc a b :=
    fun _ ht ↦ ⟨ht.1, ht.2.trans hs.2⟩
  have hderiv : ∀ t ∈ Set.Icc a s,
      HasDerivWithinAt
        (fun r : Real ↦ Real.log ((g r).inner x v v))
        ((-2 : Real) * ricciTensor (I := I) (g t) x v v /
          (g t).inner x v v)
        (Set.Icc a s) t := by
    intro t ht
    exact ((hpde t (hsub ht) x v v).mono hsub).log (hpos t).ne'
  have hbound : ∀ t ∈ Set.Icc a s,
      ‖(-2 : Real) * ricciTensor (I := I) (g t) x v v /
          (g t).inner x v v‖ ≤ 2 * K := by
    intro t ht
    have hden := hpos t
    have hricT := hric t (hsub ht) x hxB v
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    rw [abs_mul]
    norm_num
    nlinarith
  have hmvt := (convex_Icc a s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.mpr hs.1) (Set.right_mem_Icc.mpr hs.1)
  have hlog :
      |Real.log ((g s).inner x v v) - Real.log ((g a).inner x v v)| ≤
        2 * K * (s - a) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hs.1)] at hmvt
    exact hmvt
  exact exp_bounds_log (hpos a) (hpos s) hlog

omit [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
  [IsManifold I 1 M]
  [SigmaCompactSpace M] in
theorem metricEquiv_Icc
    (g : Real → SmoothRiemannianMetric I M)
    {a b K : Real}
    (hpde : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : Real ↦ (g s).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (g t) x v w)
          (Set.Icc a b) t)
    (hric : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (g t) x v v| ≤
          K * (g t).inner x v v) :
    ∀ s ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        Real.exp (-(2 * K * (s - a))) * (g a).inner x v v ≤
            (g s).inner x v v ∧
          (g s).inner x v v ≤
            Real.exp (2 * K * (s - a)) * (g a).inner x v v := by
  intro s hs x v
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hs.1.trans hs.2⟩
  simpa only [abs_of_nonneg (sub_nonneg.mpr hs.1)] using
    metric_pair_Icc g hpde hric hs ha x v

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [IsManifold I 1 M]
  [SigmaCompactSpace M] in
theorem riemannianEDistOf_exp_bounds_of_abs_ricciTensor_le
    (g : ℝ → SmoothRiemannianMetric I M) {a b K s t : ℝ}
    (hpde : ∀ r ∈ Set.Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      HasDerivWithinAt (fun u => (g u).inner x v v)
        (-2 * ricciTensor (g r) x v v) (Set.Icc a b) r)
    (hric : ∀ r ∈ Set.Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (g r) x v v| ≤ K * (g r).inner x v v)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (x y : M) :
    ENNReal.ofReal (Real.exp (-K * |s - t|)) * riemannianEDistOf (g t) x y ≤
        riemannianEDistOf (g s) x y ∧
      riemannianEDistOf (g s) x y ≤
        ENNReal.ofReal (Real.exp (K * |s - t|)) * riemannianEDistOf (g t) x y := by
  have hd := metric_deriv_bound g hpde hric
  have hst := riemannianEDistOf_le_exp_mul_of_abs_deriv_le g hd hs ht x y
  have hts := riemannianEDistOf_le_exp_mul_of_abs_deriv_le g hd ht hs x y
  rw [show 2 * K / 2 = K by ring] at hst hts
  rw [abs_sub_comm t s] at hts
  refine ⟨?_, hst⟩
  calc
    ENNReal.ofReal (Real.exp (-K * |s - t|)) * riemannianEDistOf (g t) x y ≤
        ENNReal.ofReal (Real.exp (-K * |s - t|)) *
          (ENNReal.ofReal (Real.exp (K * |s - t|)) * riemannianEDistOf (g s) x y) :=
      mul_le_mul' le_rfl hts
    _ = riemannianEDistOf (g s) x y := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        show -K * |s - t| + K * |s - t| = 0 by ring,
        Real.exp_zero, ENNReal.ofReal_one, one_mul]

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem edistCont_Icc
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b K : Real}
    (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular)
    (hric : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (S.base.metric t) x v v| ≤
          K * (S.base.metric t).inner x v v)
    (O : M) :
    ContinuousOn
      (fun p : Real × M ↦
        riemannianEDistOf (I := I) (S.base.metric p.1) O p.2)
      (Set.Icc a b ×ˢ (Set.univ : Set M)) := by
  have hpde := metricPDE_Icc (I := I) S hS hslab hreg
  intro p hp
  let A : Real × M → Real := fun q ↦ 2 * K * |q.1 - p.1|
  let d₀ : Real × M → ENNReal := fun q ↦
    riemannianEDistOf (I := I) (S.base.metric p.1) O q.2
  have hA : Continuous A :=
    continuous_const.mul (continuous_fst.sub continuous_const).abs
  have hd₀ : Continuous d₀ := by
    have hdist : Continuous (fun y : M ↦
        riemannianEDistOf (I := I) (S.base.metric p.1) O y) := by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist
        (I := I) (S.base.metric p.1) O
    exact hdist.comp continuous_snd
  have hlo : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (-A q)))) :=
    ENNReal.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (Real.continuous_exp.comp hA.neg))
  have hhi : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (A q)))) :=
    ENNReal.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (Real.continuous_exp.comp hA))
  have hlo_mul : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (-A q))) * d₀ q) :=
    hlo.ennreal_mul hd₀
      (fun q ↦ Or.inl (ne_of_gt
        (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 (Real.exp_pos _)))))
      (fun _ ↦ Or.inr ENNReal.ofReal_ne_top)
  have hhi_mul : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (A q))) * d₀ q) :=
    hhi.ennreal_mul hd₀
      (fun q ↦ Or.inl (ne_of_gt
        (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 (Real.exp_pos _)))))
      (fun _ ↦ Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (-A q))) * d₀ q)
    (h := fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (A q))) * d₀ q)
    ?_ ?_ ?_ ?_
  · change Filter.Tendsto _ (𝓝 p ⊓ Filter.principal (Set.Icc a b ×ˢ Set.univ)) _
    simpa only [A, d₀, sub_self, abs_zero, mul_zero, neg_zero,
      Real.exp_zero, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
      (hlo_mul.tendsto p).mono_left inf_le_left
  · change Filter.Tendsto _ (𝓝 p ⊓ Filter.principal (Set.Icc a b ×ˢ Set.univ)) _
    simpa only [A, d₀, sub_self, abs_zero, mul_zero, neg_zero,
      Real.exp_zero, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
      (hhi_mul.tendsto p).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hpair := metric_pair_Icc (I := I)
      (fun r ↦ S.base.metric r) hpde hric hq.1 hp.1
    exact le_edistOf_of_quad
      (I := I) (S.base.metric p.1) (S.base.metric q.1)
      (Real.exp_pos _) (fun y v ↦ (hpair y v).1) O q.2
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hpair := metric_pair_Icc (I := I)
      (fun r ↦ S.base.metric r) hpde hric hq.1 hp.1
    exact edistOf_le_of_quad
      (I := I) (S.base.metric p.1) (S.base.metric q.1)
      (Real.exp_pos _) (fun y v ↦ (hpair y v).2) O q.2

end

omit [NeZero (Module.finrank ℝ E)] in
theorem complete_of_ricBound
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b K : Real}
    (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioc a b ⊆ D.regular)
    (hK : 0 ≤ K)
    (hric : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (S.base.metric t) x v v| ≤
          K * (S.base.metric t).inner x v v)
    (ha : RiemannianMetricComplete (I := I) (S.base.metric a))
    {s : Real} (hs : s ∈ Set.Icc a b) :
    RiemannianMetricComplete (I := I) (S.base.metric s) := by
  rcases eq_or_lt_of_le hs.1 with rfl | has
  · exact ha
  · have hslab' : Set.Icc a s ⊆ D.carrier :=
      fun _ ht ↦ hslab ⟨ht.1, ht.2.trans hs.2⟩
    have hreg' : Set.Ioc a s ⊆ D.regular :=
      fun _ ht ↦ hreg ⟨ht.1, ht.2.trans hs.2⟩
    have hpde := metricPDE_Icc (I := I) S hS hslab' (fun _ h => hreg' ⟨h.1, h.2.le⟩)
    have hequiv := metricEquiv_Icc (I := I) (fun t ↦ S.base.metric t) hpde
      (fun t ht x v ↦ hric t ⟨ht.1, ht.2.trans hs.2⟩ x v)
      s ⟨has.le, le_rfl⟩
    have hC : 1 ≤ Real.exp (2 * K * (s - a)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonneg (mul_nonneg (by norm_num) hK) (sub_nonneg.mpr has.le))
    refine RiemannianMetricComplete.of_uniformEquiv ha hC ?_
    intro x v
    simpa only [Real.exp_neg] using hequiv x v

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [T2Space M]

theorem metric_inner_antitoneOn_of_ricci_nonnegative_interior
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {a b : ℝ}
    (hslab : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular)
    (hRic : ∀ s ∈ Set.Ioo a b, ∀ y : M, ∀ w : TangentSpace I y,
      0 ≤ S.ricciAt s y (vec2 w w))
    (x : M) (v : TangentSpace I x) :
    AntitoneOn (fun s : ℝ => (S.base.metric s).inner x v v) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun s : ℝ => (S.base.metric s).inner x v v) D.carrier := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hS.smoothMetric.metricTensor_cont.eval_continuous
      (P := {s : ℝ // s ∈ D.carrier}) (τ := Subtype.val) (b := fun _ => x)
      continuous_subtype_val (fun p => p.2) continuous_const
      (v := fun i _ => vec2 v v i) (fun _ => continuous_const)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (f' := fun s => (-2 : ℝ) * S.ricciAt s x (vec2 v v)) (hcont.mono hslab)
  · intro s hs
    have hs' : s ∈ Set.Ioo a b := by simpa only [interior_Icc] using hs
    exact (metricDerivAt (I := I) S hS ⟨s, hreg hs'⟩ x v v).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Set.Ioo a b := by simpa only [interior_Icc] using hs
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hRic s hs' x v)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem complete_at_earlier_time_of_ricci_nonnegative
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b s : ℝ}
    (hslab : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular)
    (hRic : ∀ t ∈ Set.Ioo a b, ∀ x : M, ∀ v : TangentSpace I x,
      0 ≤ S.ricciAt t x (vec2 v v))
    (hb : RiemannianMetricComplete (I := I) (S.base.metric b))
    (hs : s ∈ Set.Icc a b) :
    RiemannianMetricComplete (I := I) (S.base.metric s) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  refine RiemannianMetricComplete.of_lower hb (c := 1) zero_lt_one ?_
  intro x v
  have hanti :=
    Perelman.CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior
      S hS hslab hreg hRic x v
  simpa only [one_mul] using hanti hs ⟨hs.1.trans hs.2, le_rfl⟩ hs.2

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Set DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem complete_of_abs_ricciTensor_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b K s t : ℝ}
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hRic : ∀ r ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (S.base.metric r) x v v| ≤ K * (S.base.metric r).inner x v v)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hcomplete : RiemannianMetricComplete (S.base.metric t)) :
    RiemannianMetricComplete (S.base.metric s) := by
  have hpde := metricPDE_Icc S hS hslab hreg
  refine RiemannianMetricComplete.of_lower hcomplete
    (Real.exp_pos (-(2 * K * |t - s|))) ?_
  intro x v
  have hderiv : ∀ r ∈ Icc a b,
      ∃ d : ℝ, HasDerivWithinAt (fun u => (S.base.metric u).inner x v v)
        d (Icc a b) r ∧ |d| ≤ (2 * K) * (S.base.metric r).inner x v v := by
    intro r hr
    refine ⟨_, hpde r hr x v v, ?_⟩
    rw [abs_mul, abs_neg, abs_two]
    calc
      2 * |ricciTensor (S.base.metric r) x v v| ≤
          2 * (K * (S.base.metric r).inner x v v) :=
        mul_le_mul_of_nonneg_left (hRic r hr x v) (by norm_num)
      _ = (2 * K) * (S.base.metric r).inner x v v := by ring
  have hbound := inner_le_exp_mul_inner_of_abs_deriv_le S.base.metric x v hderiv ht hs
  calc
    Real.exp (-(2 * K * |t - s|)) * (S.base.metric t).inner x v v ≤
        Real.exp (-(2 * K * |t - s|)) *
          (Real.exp (2 * K * |t - s|) * (S.base.metric s).inner x v v) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = (S.base.metric s).inner x v v := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

theorem complete_of_curvature_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b C s t : ℝ}
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hcurv : ∀ r ∈ Icc a b, ∀ x : M,
      normSq0S (S.base.metric r) x 4 (S.base.rm04 r x) ≤ C)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hcomplete : RiemannianMetricComplete (S.base.metric t)) :
    RiemannianMetricComplete (S.base.metric s) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact complete_of_abs_ricciTensor_le S hS hslab hreg
    (fun r hr x v => ricci_quadratic_form_bound_of_solution_curvature_bound
      S x v (hcurv r hr x)) hs ht hcomplete

end DifferentialGeometry.PDE.RicciFlow
