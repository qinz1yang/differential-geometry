import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.QuadraticBound
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity

set_option autoImplicit false

/-!
# Metric comparison along a Ricci flow

This file gives the closed-time-slab metric comparison needed to transport
Riemannian completeness from the left endpoint of a Ricci-flow slab.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff Bundle Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
private theorem tensor_eval_cont
    {K : Set Real}
    {A : (t : Real) → (x : M) →
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun s : Real ↦ A s x (vec2 v w)) K := by
  rw [continuousOn_iff_continuous_restrict]
  exact hA.eval_continuous (P := {s : Real // s ∈ K}) (τ := Subtype.val)
    (b := fun _ ↦ x) continuous_subtype_val (fun p ↦ p.2) continuous_const
    (v := fun i _ ↦ vec2 v w i) (fun _ ↦ continuous_const)

private theorem deriv_Ici_start
    {a b : Real} (hab : a < b) (f e : Real → Real)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hecont : ContinuousWithinAt e (Set.Ioi a) a)
    (hint : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (e t) (Set.Ici a) t) :
    HasDerivWithinAt f (e a) (Set.Ici a) a := by
  have hopen : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hsub : Set.Ioo a b ⊆ Set.Ici a := fun _ ht ↦ ht.1.le
  have hwithin : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (e t) (Set.Ioo a b) t :=
    fun t ht ↦ (hint t ht).mono hsub
  have hdiff : DifferentiableOn Real f (Set.Ioo a b) :=
    fun t ht ↦ (hwithin t ht).differentiableWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b, deriv f t = e t := by
    intro t ht
    rw [← derivWithin_of_isOpen hopen ht]
    exact (hwithin t ht).derivWithin (hopen.uniqueDiffWithinAt ht)
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo a b)
    hdiff ?_ ?_ ?_
  · exact (hcont.continuousWithinAt ⟨le_rfl, hab.le⟩).mono
      Set.Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsGT hab
  · exact hecont.tendsto.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hab) hderiv).symm

/-- A Ricci-flow solution satisfies the metric PDE on a closed slab, with a
one-sided derivative at its left endpoint. -/
theorem metricPDE_Icc
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioc a b ⊆ D.regular) :
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
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · have hecont : ContinuousWithinAt
        (fun s : Real ↦
          (-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w)
        (Set.Ioi a) a := by
      have hmem : Set.Icc a b ∈ nhdsWithin a (Set.Ioi a) :=
        Filter.mem_of_superset (Ioo_mem_nhdsGT hab)
          (fun s hs ↦ ⟨hs.1.le, hs.2.le⟩)
      exact ((hricCont x v w).continuousWithinAt ⟨le_rfl, hab.le⟩)
        |>.mono_of_mem_nhdsWithin hmem
    have hint : ∀ s ∈ Set.Ioo a b,
        HasDerivWithinAt
          (fun r : Real ↦ (S.base.metric r).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w)
          (Set.Ici a) s := by
      intro s hs
      let τ : RealTimeInterval.RegularTime D :=
        ⟨s, hreg ⟨hs.1, hs.2.le⟩⟩
      have hraw := metricDerivAt (I := I) S hS τ x v w
      simpa [SolutionFamily.ricciAt, metricRicciAt,
        metricRicciAt_apply_eq_ricciTensor] using hraw.hasDerivWithinAt
    exact (deriv_Ici_start hab _ _ (hmetricCont x v w) hecont hint).mono
      (fun _ hs ↦ hs.1)
  · let τ : RealTimeInterval.RegularTime D :=
      ⟨t, hreg ⟨hat, ht.2⟩⟩
    have hraw := metricDerivAt (I := I) S hS τ x v w
    simpa [SolutionFamily.ricciAt, metricRicciAt,
      metricRicciAt_apply_eq_ricciTensor] using hraw.hasDerivWithinAt

/-- A bound on the logarithmic ratio of two positive numbers gives
multiplicative exponential bounds. -/
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

set_option linter.unusedSectionVars false in
/-- A quadratic Ricci bound gives pointwise exponential comparison with the
metric at the left endpoint of a closed time slab. -/
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
    have hricT := hric t (hsub ht) x v
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
  rcases le_total t s with hts | hst
  · have hsub : Set.Icc t s ⊆ Set.Icc a b := by
      intro r hr
      exact ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩
    have hequiv := metricEquiv_Icc (I := I) g
      (fun r hr y w z ↦ (hpde r (hsub hr) y w z).mono hsub)
      (fun r hr y w ↦ hric r (hsub hr) y w)
      s ⟨hts, le_rfl⟩ x v
    simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using hequiv
  · have hsub : Set.Icc s t ⊆ Set.Icc a b := by
      intro r hr
      exact ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
    have hequiv := metricEquiv_Icc (I := I) g
      (fun r hr y w z ↦ (hpde r (hsub hr) y w z).mono hsub)
      (fun r hr y w ↦ hric r (hsub hr) y w)
      t ⟨hst, le_rfl⟩ x v
    have hleft :
        Real.exp (-(2 * K * (t - s))) * (g t).inner x v v ≤
          (g s).inner x v v := by
      calc
        Real.exp (-(2 * K * (t - s))) * (g t).inner x v v ≤
            Real.exp (-(2 * K * (t - s))) *
              (Real.exp (2 * K * (t - s)) * (g s).inner x v v) :=
          mul_le_mul_of_nonneg_left hequiv.2 (Real.exp_pos _).le
        _ = (g s).inner x v v := by
          rw [← mul_assoc, ← Real.exp_add]
          simp only [neg_add_cancel, Real.exp_zero, one_mul]
    have hright :
        (g s).inner x v v ≤
          Real.exp (2 * K * (t - s)) * (g t).inner x v v := by
      calc
        (g s).inner x v v =
            Real.exp (2 * K * (t - s)) *
              (Real.exp (-(2 * K * (t - s))) * (g s).inner x v v) := by
          rw [← mul_assoc, ← Real.exp_add]
          simp only [add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (2 * K * (t - s)) * (g t).inner x v v :=
          mul_le_mul_of_nonneg_left hequiv.1 (Real.exp_pos _).le
    simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using
      And.intro hleft hright

/-- On a Ricci-bounded closed time slab, Riemannian extended distance from a
fixed point is jointly continuous in time and the moving endpoint. -/
theorem edistCont_Icc
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b K : Real} (hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioc a b ⊆ D.regular)
    (hric : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (S.base.metric t) x v v| ≤
          K * (S.base.metric t).inner x v v)
    (O : M) :
    ContinuousOn
      (fun p : Real × M ↦
        riemannianEDistOf (I := I) (S.base.metric p.1) O p.2)
      (Set.Icc a b ×ˢ (Set.univ : Set M)) := by
  have hpde := metricPDE_Icc (I := I) S hS hab hslab hreg
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
  · simpa only [A, d₀, sub_self, abs_zero, mul_zero, neg_zero,
      Real.exp_zero, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
      (hlo_mul.tendsto p).mono_left inf_le_left
  · simpa only [A, d₀, sub_self, abs_zero, mul_zero, neg_zero,
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

/-- A globally Ricci-bounded solution remains complete on every slice of a
closed time slab when its left endpoint is complete. -/
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
    have hpde := metricPDE_Icc (I := I) S hS has hslab' hreg'
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
