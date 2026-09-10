import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimMetricControl

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH

section Metric

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private local instance timeControlMetricC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem metric_inner_time_difference_le_of_ricci_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b C : ℝ} (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (x : M) (v : TangentSpace I x)
    (hRic : ∀ q ∈ Ioo a b, ‖S.ricciAt q x (vec2 v v)‖ ≤ C)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |(S.base.metric t).inner x v v - (S.base.metric s).inner x v v| ≤
      (2 * C) * |t - s| := by
  let f : ℝ → ℝ := fun q => (S.base.metric q).inner x v v
  have hcont : ContinuousOn f D.carrier := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hS.smoothMetric.metricTensor_cont.eval_continuous
      (P := {q : ℝ // q ∈ D.carrier}) (τ := Subtype.val) (b := fun _ => x)
      continuous_subtype_val (fun q => q.2) continuous_const
      (v := fun i _ => vec2 v v i) (fun _ => continuous_const)
  have hderiv (q : ℝ) (hq : q ∈ Ioo a b) :
      HasDerivAt f ((-2 : ℝ) * S.ricciAt q x (vec2 v v)) q :=
    metricDerivAt (I := I) S hS ⟨q, hreg hq⟩ x v v
  have hdiff : DifferentiableOn ℝ f (interior (Icc a b)) := by
    intro q hq
    have hq' : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    exact (hderiv q hq').differentiableAt.differentiableWithinAt
  have hbound (q : ℝ) (hq : q ∈ interior (Icc a b)) : |deriv f q| ≤ 2 * C := by
    have hq' : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    rw [(hderiv q hq').deriv, ← Real.norm_eq_abs, norm_mul]
    norm_num only [norm_neg, Real.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (hRic q hq') (by norm_num)
  have hordered (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b)
      (hst : s ≤ t) : |f t - f s| ≤ (2 * C) * |t - s| := by
    have hupper := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
      (hcont.mono hslab) hdiff (fun q hq => (abs_le.mp (hbound q hq)).2) s hs t ht hst
    have hlower := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      (hcont.mono hslab) hdiff (fun q hq => (abs_le.mp (hbound q hq)).1) s hs t ht hst
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact abs_le.mpr ⟨by linarith, hupper⟩
  rcases le_total s t with hst | hts
  · exact hordered s hs t ht hst
  · simpa only [abs_sub_comm] using hordered t ht s hs hts

end Metric

section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval}

private local instance timeControlTopology (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    TopologicalSpace F.M := F.topology
private local instance timeControlCharted (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    ChartedSpace H F.M := F.charted
private local instance timeControlSmooth (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    IsManifold I ∞ F.M := F.smooth
private local instance timeControlT2 (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    T2Space F.M := F.t2

theorem KLim.metric_inner_time_difference_le
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa C a s t : ℝ}
    (hK : KLim kappa F) (hs : s ∈ Icc a 0) (ht : t ∈ Icc a 0)
    (x : F.M) (hC : F.S.scalar 0 x ≤ C) (v : TangentSpace I x) :
    |(F.S.base.metric t).inner x v v - (F.S.base.metric s).inner x v v| ≤
      ((C * Real.exp (C * (-a))) * (F.S.base.metric 0).inner x v v) * |t - s| := by
  have hslab : Icc a 0 ⊆ D.carrier := by
    intro q hq
    simpa only [hK.carrier_eq, mem_Iic] using hq.2
  have hreg : Ioo a 0 ⊆ D.regular := by
    intro q hq
    simpa only [hK.regular_eq, mem_Iio] using hq.2
  have hRic (q : ℝ) (hq : q ∈ Ioo a 0) :
      ‖F.S.ricciAt q x (vec2 v v)‖ ≤
        ((C / 2) * Real.exp (C * (-a))) * (F.S.base.metric 0).inner x v v :=
    hK.ricci_energy_bound_on_backward_slab ⟨hq.1.le, hq.2.le⟩ x hC v le_rfl
  have h := metric_inner_time_difference_le_of_ricci_bound
    F.S F.isSolution hslab hreg x v hRic hs ht
  convert h using 1
  ring

end Pointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
