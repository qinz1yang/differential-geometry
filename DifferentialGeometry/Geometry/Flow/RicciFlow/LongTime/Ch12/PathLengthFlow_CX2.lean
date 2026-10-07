import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SmoothFirstExit_CX2
import DifferentialGeometry.Geometry.Comparison.Variation.ArcLengthContinuity
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

omit [T2Space M] in
/-- The real and extended-nonnegative length conventions agree. -/
theorem pathLength_eq_ofReal_arcLength_CX2 (g : SmoothRiemannianMetric ThreeModel M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ) :
    metricPathELength g γ 0 1 = ENNReal.ofReal (Variation.arcLength g γ 0 1) := by
  rw [metricPathELength_eq]
  unfold Variation.arcLength
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((Geodesic.speedSqrt_integrableOn_Icc_of_C1 g zero_le_one hγ.contMDiffOn).mono_set Ioo_subset_Icc_self)
    (ae_of_all _ (fun _ => Real.sqrt_nonneg _))).symm

/-- Continuity of the length of a fixed smooth path needs no compactness or
completeness of the ambient manifold. -/
theorem continuousOn_pathLength_CX2 {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : Icc a b ⊆ D.carrier) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ) :
    ContinuousOn (fun t => metricPathELength (S.base.metric t) γ 0 1) (Icc a b) := by
  have hv : Continuous (fun z : ℝ =>
      (⟨γ z, mfderiv 𝓘(ℝ, ℝ) ThreeModel γ z (1 : ℝ)⟩ : TangentBundle ThreeModel M)) :=
    MFDerivAlongCurve.continuous_tangentMap_unitLift le_rfl hγ
  have hc := Variation.continuousOn_arcLength_of_continuous_tangentLift
    isCompact_Icc zero_le_one S.base.metric hS.smoothMetric.metricTensor_cont
    id continuousOn_id hcarrier (fun _ : ℝ => γ) (hv.comp continuous_snd).continuousOn
  exact (ENNReal.continuous_ofReal.comp_continuousOn hc).congr
    (fun t _ => pathLength_eq_ofReal_arcLength_CX2 (S.base.metric t) hγ)

omit [T2Space M] in
/-- Quadratic comparison along the path, on an arbitrary three-manifold. -/
theorem pathLength_quad_CX2 (g h : SmoothRiemannianMetric ThreeModel M)
    (γ : ℝ → M) {L : ℝ} (hL : 0 ≤ L)
    (hquad : ∀ z ∈ Ioo (0 : ℝ) 1, ∀ v : TangentSpace ThreeModel (γ z),
      g.inner (γ z) v v ≤ L ^ 2 * h.inner (γ z) v v) :
    metricPathELength g γ 0 1 ≤ ENNReal.ofReal L * metricPathELength h γ 0 1 := by
  rw [metricPathELength_eq, metricPathELength_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro z hz
  have hroot := Real.sqrt_le_sqrt (hquad z hz (mfderiv 𝓘(ℝ, ℝ) ThreeModel γ z 1))
  rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL] at hroot
  simpa only [ENNReal.ofReal_mul hL] using ENNReal.ofReal_le_ofReal hroot

/-- The exponential length comparison retains the actual elapsed time, so
its factors multiply correctly when several surgery stages are traversed. -/
theorem pathLength_exp_CX2 {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    {a b K v w : ℝ} (hK : 0 ≤ K) (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular) (γ : ℝ → M)
    (hRm : ∀ t ∈ Icc a b, ∀ z ∈ Icc (0 : ℝ) 1,
      Real.sqrt (normSq0S (S.base.metric t) (γ z) 4 (S.base.rm04 t (γ z))) ≤ K)
    (hv : v ∈ Icc a b) (hw : w ∈ Icc a b) :
    metricPathELength (S.base.metric v) γ 0 1 ≤
      ENNReal.ofReal (Real.exp (9 * K * |v - w|)) * metricPathELength (S.base.metric w) γ 0 1 := by
  apply pathLength_quad_CX2 _ _ γ (Real.exp_pos _).le
  intro z hz V
  have hm := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular (γ z)
    (fun t ht => (Real.sqrt_le_iff.mp (hRm t ht z ⟨hz.1.le, hz.2.le⟩)).2) hv hw V).2
  rw [Real.sqrt_sq hK] at hm
  norm_num [ThreeSpace] at hm
  have heq : Real.exp (18 * K * |v - w|) = Real.exp (9 * K * |v - w|) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [heq] at hm

/-- First exit formulated with length rather than ambient distance. This
also applies to the noncompact regular open of a terminal limit metric. -/
theorem pathLength_first_exit_CX2 {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    {a b K ℓ R : ℝ} (hab : a ≤ b) (hK : 0 ≤ K) (hℓ : 0 ≤ ℓ)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hlen : metricPathELength (S.base.metric b) γ 0 1 ≤ ENNReal.ofReal ℓ)
    (hroom : Real.exp (9 * K * (b - a)) * ℓ < R)
    (hRm : ∀ t ∈ Icc a b, metricPathELength (S.base.metric t) γ 0 1 < ENNReal.ofReal R →
      ∀ z ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (S.base.metric t) (γ z) 4 (S.base.rm04 t (γ z))) ≤ K) :
    ∀ t ∈ Icc a b,
      metricPathELength (S.base.metric t) γ 0 1 ≤
        ENNReal.ofReal (Real.exp (9 * K * (b - t))) * metricPathELength (S.base.metric b) γ 0 1 ∧
      metricPathELength (S.base.metric t) γ 0 1 < ENNReal.ofReal R ∧
      ∀ z ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (S.base.metric t) (γ z) 4 (S.base.rm04 t (γ z))) ≤ K := by
  let B := Real.exp (9 * K * (b - a))
  have hB : 0 < B := Real.exp_pos _
  have hB1 : 1 ≤ B := Real.one_le_exp (mul_nonneg (by positivity) (sub_nonneg.mpr hab))
  have hℓR : ℓ < R := (le_mul_of_one_le_left hℓ hB1).trans_lt hroom
  have hR : 0 < R := hℓ.trans_lt hℓR
  have hc := continuousOn_pathLength_CX2 S hS hcarrier hγ
  let f : ℝ × Unit → ℝ≥0∞ := fun q => metricPathELength (S.base.metric q.1) γ 0 1
  have hfc : ContinuousOn f (Icc a b ×ˢ (univ : Set Unit)) :=
    hc.comp continuousOn_fst (fun _ h => h.1)
  have hfinal : ∀ z : Unit, f (b, z) < ENNReal.ofReal R := fun _ =>
    hlen.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hℓR)
  have hstay : ∀ t ∈ Icc a b, metricPathELength (S.base.metric t) γ 0 1 < ENNReal.ofReal R := by
    have hh := compact_backward_first_exit_CX2 hfc
      ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hroom) hfinal
    apply fun t ht => hh ?_ t ht ()
    intro v hv hgood z
    have hb := pathLength_exp_CX2 S hS hK
      (fun t ht => hcarrier ⟨hv.1.trans ht.1, ht.2⟩)
      (fun t ht => hregular ⟨hv.1.trans_lt ht.1, ht.2⟩) γ
      (fun t ht => hRm t ⟨hv.1.trans ht.1, ht.2⟩ (hgood t ht ()))
      ⟨le_rfl, hv.2⟩ ⟨hv.2, le_rfl⟩
    have he : Real.exp (9 * K * |v - b|) ≤ B := by
      rw [abs_of_nonpos (sub_nonpos.mpr hv.2)]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hK (sub_nonneg.mpr hv.1)]
    have hmul := mul_le_mul' (ENNReal.ofReal_le_ofReal he) hlen
    exact (hb.trans hmul).trans_eq (ENNReal.ofReal_mul hB.le).symm
  intro t ht
  refine ⟨?_, hstay t ht, hRm t ht (hstay t ht)⟩
  have hb := pathLength_exp_CX2 S hS hK hcarrier hregular γ
    (fun v hv => hRm v hv (hstay v hv)) ht ⟨hab, le_rfl⟩
  simpa only [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using hb

end GC.LongTime.Ch12
