import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CostContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [CompactSpace M] in
theorem lRegLag_time_cont
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha) :
    ContinuousOn
      (fun q : Real × Real ↦ lRegLag S q.1 alpha q.2)
      {q : Real × Real | q.1 - q.2 ^ 2 ∈ D.regular} := by
  let U : Set (Real × Real) :=
    {q : Real × Real | q.1 - q.2 ^ 2 ∈ D.regular}
  let P := {q : Real × Real // q ∈ U}
  let timeLift : P → {t : Real // t ∈ D.carrier} := fun q ↦
    ⟨q.1.1 - q.1.2 ^ 2, D.regular_subset q.2⟩
  let velLift : P → TangentBundle I M := fun q ↦
    ⟨alpha q.1.2, lVelocity (I := I) alpha q.1.2⟩
  have htime : Continuous timeLift := by
    exact (((continuous_fst.comp continuous_subtype_val).sub
      ((continuous_snd.comp continuous_subtype_val).pow 2)).subtype_mk _)
  have hvel : Continuous velLift := by
    exact
      (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (n := (1 : WithTop ℕ∞)) (by simp) halpha).comp
        (continuous_snd.comp continuous_subtype_val)
  have hbase : Continuous (fun q : P ↦ alpha q.1.2) :=
    halpha.continuous.comp (continuous_snd.comp continuous_subtype_val)
  have hquad :=
    metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      (I := I) (M := M) S.family.metric hS.smoothMetric
      (K := D.carrier) (fun _ ht ↦ ht)
  have hkin0 := hquad.comp (htime.prodMk hvel)
  have hkin : Continuous (fun q : P ↦
      (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
        (lVelocity (I := I) alpha q.1.2)
        (lVelocity (I := I) alpha q.1.2)) := by
    have heq : (DifferentialGeometry.metricTimeBundleQuad
        (I := I) S.family.metric D.carrier ∘ fun q : P ↦
          (timeLift q, velLift q)) = fun q : P ↦
        (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
          (lVelocity (I := I) alpha q.1.2)
          (lVelocity (I := I) alpha q.1.2) := by
      funext q
      rfl
    rw [heq] at hkin0
    exact hkin0
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hscalar := hSc.continuous_subtype.comp (htime.prodMk hbase)
  have hlag : Continuous (fun q : P ↦
      (1 / 2 : Real) *
          (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
            (lVelocity (I := I) alpha q.1.2)
            (lVelocity (I := I) alpha q.1.2) +
        2 * q.1.2 ^ 2 * S.scalar (q.1.1 - q.1.2 ^ 2) (alpha q.1.2)) :=
    continuous_const.mul hkin |>.add
      ((continuous_const.mul
        ((continuous_snd.comp continuous_subtype_val).pow 2)).mul hscalar)
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : U.domRestrict (fun q : Real × Real ↦
      lRegLag S q.1 alpha q.2) = fun q : P ↦
        (1 / 2 : Real) *
            (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
              (lVelocity (I := I) alpha q.1.2)
              (lVelocity (I := I) alpha q.1.2) +
          2 * q.1.2 ^ 2 * S.scalar (q.1.1 - q.1.2 ^ 2) (alpha q.1.2) := by
    funext q
    rfl
  change Continuous (U.domRestrict (fun q : Real × Real ↦
    lRegLag S q.1 alpha q.2))
  rw [heq]
  exact hlag

theorem lRegTime_nhds (D : RealTimeInterval) (T a b : Real)
    (hreg : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular) :
    ∀ᶠ R in nhds T, ∀ s ∈ uIcc a b, R - s ^ 2 ∈ D.regular := by
  let J₀ : Set Real := (fun s : Real ↦ T - s ^ 2) '' uIcc a b
  have hJ₀c : IsCompact J₀ :=
    isCompact_uIcc.image_of_continuousOn
      (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hJ₀reg : J₀ ⊆ D.regular := by
    rintro _ ⟨s, hs, rfl⟩
    exact hreg s hs
  obtain ⟨delta, hdelta, hthick⟩ :=
    hJ₀c.exists_thickening_subset_open D.regular_isOpen hJ₀reg
  filter_upwards [Metric.ball_mem_nhds T hdelta] with R hR s hs
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  refine ⟨T - s ^ 2, ⟨s, hs, rfl⟩, ?_⟩
  rw [Metric.mem_ball] at hR
  simpa only [dist_sub_right] using hR

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [CompactSpace M] in
theorem lRegAction_T_cont
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (hreg : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular) :
    ContinuousAt (fun R ↦ lRegAction S R alpha a b) T := by
  have hlag := lRegLag_time_cont (I := I) S hS alpha halpha
  let J₀ : Set Real := (fun s : Real ↦ T - s ^ 2) '' uIcc a b
  have hJ₀c : IsCompact J₀ :=
    isCompact_uIcc.image_of_continuousOn
      (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hJ₀reg : J₀ ⊆ D.regular := by
    rintro _ ⟨s, hs, rfl⟩
    exact hreg s hs
  obtain ⟨delta, hdelta, hthick⟩ :=
    hJ₀c.exists_thickening_subset_open D.regular_isOpen hJ₀reg
  let eta : Real := delta / 2
  have heta : 0 < eta := half_pos hdelta
  let KT : Set Real := Icc (T - eta) (T + eta)
  let K : Set (Real × Real) := KT ×ˢ uIcc a b
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_uIcc
  have hKreg : K ⊆ {q : Real × Real | q.1 - q.2 ^ 2 ∈ D.regular} := by
    intro q hq
    apply hthick
    apply Metric.mem_thickening_iff.mpr
    refine ⟨T - q.2 ^ 2, ⟨q.2, hq.2, rfl⟩, ?_⟩
    rw [Real.dist_eq]
    have hdist : |q.1 - T| ≤ eta := by
      rw [abs_le]
      exact ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
    simpa only [sub_sub_sub_cancel_right] using hdist.trans_lt (half_lt_self hdelta)
  have hlagK : ContinuousOn
      (fun q : Real × Real ↦ lRegLag S q.1 alpha q.2) K :=
    hlag.mono hKreg
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hlagK
  let C₀ : Real := max C 0
  have hTnh : KT ∈ nhds T := by
    apply Icc_mem_nhds
    · change T - eta < T
      linarith
    · change T < T + eta
      linarith
  apply intervalIntegral.continuousAt_of_dominated_interval
      (F := fun R s ↦ lRegLag S R alpha s) (bound := fun _ ↦ C₀)
  · filter_upwards [hTnh] with R hR
    exact ((hlagK.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs ↦ ⟨hR, uIoc_subset_uIcc hs⟩))).aestronglyMeasurable
        measurableSet_uIoc
  · filter_upwards [hTnh] with R hR
    exact ae_of_all _ fun s hs ↦ by
      exact (hC (R, s) ⟨hR, uIoc_subset_uIcc hs⟩).trans
        (le_max_left C 0)
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun s hs ↦ by
      have hregTs : T - s ^ 2 ∈ D.regular :=
        hreg s (uIoc_subset_uIcc hs)
      have hpair : ContinuousAt (fun R : Real ↦ (R, s)) T :=
        continuousAt_id.prodMk continuousAt_const
      have hout := (hlag (T, s) hregTs).continuousAt
        ((D.regular_isOpen.preimage
          (continuous_fst.sub (continuous_snd.pow 2))).mem_nhds hregTs)
      exact ContinuousAt.comp' (f := fun R : Real ↦ (R, s)) hout hpair

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
theorem lCost_lt_T_event
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {Tn : Nat → Real} {T tau : Real} (hTn : Tendsto Tn atTop (nhds T))
    (htau : 0 < tau) (x y : M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (halpha0 : alpha 0 = x) (halphab : alpha (Real.sqrt tau) = y)
    (hreg : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular) (A : Real)
    (hA : lRegAction S T alpha 0 (Real.sqrt tau) < A) :
    ∀ᶠ n in atTop, lCost S (Tn n) x y tau < A := by
  have hb0 : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  have hregU : ∀ s ∈ uIcc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular := by
    simpa only [uIcc_of_le hb0.le] using hreg
  have hregEvent : ∀ᶠ n in atTop, ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      Tn n - s ^ 2 ∈ D.regular := by
    have hnh := lRegTime_nhds D T 0 (Real.sqrt tau) hregU
    filter_upwards [hTn.eventually hnh] with n hn
    simpa only [uIcc_of_le hb0.le] using hn
  have hactEvent : ∀ᶠ n in atTop,
      lRegAction S (Tn n) alpha 0 (Real.sqrt tau) < A :=
    ((lRegAction_T_cont (I := I) S hS T 0 (Real.sqrt tau) alpha halpha
      hregU).tendsto.comp hTn).eventually (Iio_mem_nhds hA)
  filter_upwards [hregEvent, hactEvent] with n hnReg hnAct
  rw [lCost_eq_reg (I := I) S (Tn n) x y tau htau.le]
  have htime : Icc (Tn n - tau) (Tn n) ⊆ D.carrier := by
    intro r hr
    have hnonneg : 0 ≤ Tn n - r := by linarith [hr.2]
    have hle : Tn n - r ≤ tau := by linarith [hr.1]
    have hsqrt : Real.sqrt (Tn n - r) ∈ Icc (0 : Real) (Real.sqrt tau) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hle⟩
    have hregR := hnReg (Real.sqrt (Tn n - r)) hsqrt
    have heqR : Tn n - (Real.sqrt (Tn n - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    exact D.regular_subset (by simpa only [heqR] using hregR)
  have hback : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      Tn n - s ^ 2 ∈ Icc (Tn n - tau) (Tn n) := by
    intro s hs
    have hsq : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
          (sq_le_sq₀ hs.1 hb0.le).2 hs.2
        _ = tau := Real.sq_sqrt htau.le
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  exact (lRegCostC1_le (I := I) S hS
    (Tn n) (Tn n - tau) (Tn n) 0 (Real.sqrt tau) hb0.le
    htime hback x y alpha halpha halpha0 halphab hnReg).trans_lt hnAct

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
