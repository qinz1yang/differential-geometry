import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.MaximumPrinciple
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] [CompactSpace M]

theorem hamilton_ivey_pinching_scaled
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T C : Real} (hT : 0 ≤ T) (hC : 0 < C)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, -C ≤
      2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩) :
    ∀ t ∈ Set.Icc t0 (t0 + T), ∀ x : M,
      let nu := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩
      nu < 0 → S.scalar t x ≥ (-nu) * (Real.log ((C⁻¹ + t - t0) * (-nu)) - 3) := by
  have hinit' : ∀ x : M,
      curvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ (C / 2) := by
    intro x
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t0) x hdim
    rw [curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt
      (I := I) (S.base.metric t0) x basis horth]
    linarith [hinit x]
  have hpinch := (hamilton_ivey_pinching (I := I) S hS hT (half_pos hC)
    hslab hreg hdim hinit').2
  intro t ht x nu hnu
  let k := leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hk : k < 0 := by change 2 * k < 0 at hnu; linarith
  have htime : 0 < 1 + 2 * (C / 2) * (t - t0) := by
    nlinarith [mul_nonneg hC.le (sub_nonneg.mpr ht.1)]
  have harg : (C⁻¹ + t - t0) * (-nu) =
      ((-k) / (C / 2)) * (1 + 2 * (C / 2) * (t - t0)) := by
    change (C⁻¹ + t - t0) * (-(2 * k)) = _
    field_simp
    ring
  have h := hpinch t ht x hk
  change 2 * (-k) *
    (Real.log ((-k) / (C / 2)) + Real.log (1 + 2 * (C / 2) * (t - t0)) - 3) ≤
      S.scalar t x at h
  rw [harg, Real.log_mul (ne_of_gt (div_pos (neg_pos.mpr hk) (half_pos hC)))
    htime.ne']
  change -(2 * k) * _ ≤ _
  nlinarith [h]

theorem hamilton_ivey_pinching_normalized
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T : Real} (hT : 0 ≤ T)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, -1 ≤
      2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩) :
    ∀ t ∈ Set.Icc t0 (t0 + T), ∀ x : M,
      let nu := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩
      nu < 0 → S.scalar t x ≥
        (-nu) * (Real.log (-nu) + Real.log (1 + t - t0) - 3) := by
  intro t ht x nu hnu
  have h := hamilton_ivey_pinching_scaled (I := I) S hS hT
    (by norm_num : 0 < (1 : Real)) hslab hreg hdim hinit t ht x hnu
  have htime : 0 < 1 + t - t0 := by linarith [ht.1]
  change (-nu) * (Real.log (((1 : Real)⁻¹ + t - t0) * (-nu)) - 3) ≤ _ at h
  rw [inv_one, Real.log_mul htime.ne' (neg_pos.mpr hnu).ne'] at h
  simpa only [add_comm] using h

theorem hamilton_ivey_pinching_positive_time
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {s t : Real} (hst : s < t)
    (hslab : Set.Icc s t ⊆ D.carrier)
    (hreg : Set.Ioo s t ⊆ D.regular)
    (hdim : Module.finrank Real E = 3) (x : M) :
    let nu := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩
    nu < 0 → S.scalar t x ≥ (-nu) * (Real.log ((t - s) * (-nu)) - 3) := by
  intro nu hnu
  obtain ⟨K, hK, hinit⟩ := exists_curvatureOperatorLowerBoundAt_metricRm04
    (I := I) (S.base.metric s) hdim
  have hpinch := (hamilton_ivey_pinching (I := I) S hS (sub_nonneg.mpr hst.le) hK
    (by simpa only [add_sub_cancel] using hslab)
    (by simpa only [add_sub_cancel] using hreg) hdim hinit).2
  let k := leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hk : k < 0 := by change 2 * k < 0 at hnu; linarith
  have h := hpinch t ⟨hst.le, by simp⟩ x hk
  change 2 * (-k) *
    (Real.log ((-k) / K) + Real.log (1 + 2 * K * (t - s)) - 3) ≤ _ at h
  have htime : 0 < 1 + 2 * K * (t - s) := by
    nlinarith [mul_pos hK (sub_pos.mpr hst)]
  have harg : 0 < (t - s) * (-nu) := mul_pos (sub_pos.mpr hst) (neg_pos.mpr hnu)
  have hargle : (t - s) * (-nu) ≤ ((-k) / K) * (1 + 2 * K * (t - s)) := by
    change (t - s) * (-(2 * k)) ≤ _
    have heq : ((-k) / K) * (1 + 2 * K * (t - s)) =
        (-k) / K + (t - s) * (-(2 * k)) := by field_simp; ring
    rw [heq]
    linarith [div_pos (neg_pos.mpr hk) hK]
  have hlog := Real.log_le_log harg hargle
  rw [Real.log_mul (div_pos (neg_pos.mpr hk) hK).ne' htime.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlog 3) (neg_pos.mpr hnu).le
  change -(2 * k) * _ ≤ -(2 * k) * _ at hmul
  change -(2 * k) * _ ≤ _
  nlinarith [h, hmul]

theorem curvatureOperatorNonnegative_of_ancient
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hancient : Set.Iio T ⊆ D.regular)
    (hdim : Module.finrank Real E = 3) {t : Real} (ht : t < T) (x : M) :
    (⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hnonneg : 0 ≤ leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A := by
    by_contra h
    have hneg := lt_of_not_ge h
    let q := -(2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A)
    have hq : 0 < q := by dsimp [q]; linarith
    let a := Real.exp (S.scalar t x / q + 4) / q
    have ha : 0 < a := div_pos (Real.exp_pos _) hq
    have hst : t - a < t := sub_lt_self _ ha
    have hslab : Set.Icc (t - a) t ⊆ D.carrier := by
      intro r hr
      exact D.regular_subset (hancient (hr.2.trans_lt ht))
    have hreg : Set.Ioo (t - a) t ⊆ D.regular := by
      intro r hr
      exact hancient (hr.2.trans ht)
    have hpinch := hamilton_ivey_pinching_positive_time (I := I) S hS hst hslab hreg hdim x
      (by change 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A < 0
          linarith)
    change q * (Real.log ((t - (t - a)) * q) - 3) ≤ S.scalar t x at hpinch
    have harg : (t - (t - a)) * q = Real.exp (S.scalar t x / q + 4) := by
      dsimp [a]
      field_simp
      ring
    rw [harg, Real.log_exp] at hpinch
    have hcancel : q * (S.scalar t x / q) = S.scalar t x :=
      mul_div_cancel₀ _ hq.ne'
    nlinarith [hpinch]
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t) x hdim
  have hbound : curvatureOperatorLowerBoundAt (I := I) (S.base.metric t) x A 0 := by
    rw [curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt
      (I := I) (S.base.metric t) x basis horth, neg_zero]
    exact hnonneg
  exact mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    (fun n c v w => by simpa only [zero_mul, add_zero] using hbound n c v w)

theorem hamilton_ivey_negative_ratio_tendsto_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 C : Real} (hC : 0 < C)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, -C ≤
      2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩)
    {α : Type*} {l : Filter α} (time : α → Real) (point : α → M)
    (htime : ∀ i, t0 ≤ time i)
    (hslab : ∀ i, Set.Icc t0 (time i) ⊆ D.carrier)
    (hreg : ∀ i, Set.Ioo t0 (time i) ⊆ D.regular)
    (hneg : ∀ i,
      2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric (time i)) (point i)
        ⟨S.base.rm04 (time i) (point i), metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric (time i)) (point i)⟩ < 0)
    (hblowup : Filter.Tendsto (fun i => (C⁻¹ + time i - t0) *
      (-(2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric (time i)) (point i)
        ⟨S.base.rm04 (time i) (point i), metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric (time i)) (point i)⟩))) l Filter.atTop) :
    (∀ᶠ i in l, 0 < S.scalar (time i) (point i)) ∧
      Filter.Tendsto (fun i =>
        (-(2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric (time i)) (point i)
          ⟨S.base.rm04 (time i) (point i), metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric (time i)) (point i)⟩)) /
          S.scalar (time i) (point i)) l (𝓝 0) := by
  let q : α → Real := fun i =>
    -(2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric (time i)) (point i)
      ⟨S.base.rm04 (time i) (point i), metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric (time i)) (point i)⟩)
  have hq : ∀ i, 0 < q i := fun i => neg_pos.mpr (hneg i)
  have hlog : Filter.Tendsto (fun i => Real.log ((C⁻¹ + time i - t0) * q i) - 3)
      l Filter.atTop := by
    simpa only [sub_eq_add_neg, Function.comp_apply, q] using
      Filter.tendsto_atTop_add_const_right l (-3) (Real.tendsto_log_atTop.comp hblowup)
  have hratio : Filter.Tendsto (fun i => S.scalar (time i) (point i) / q i)
      l Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ hlog
    intro i
    apply (le_div_iff₀ (hq i)).mpr
    have h := hamilton_ivey_pinching_scaled (I := I) S hS (sub_nonneg.mpr (htime i)) hC
      (by simpa only [add_sub_cancel] using hslab i)
      (by simpa only [add_sub_cancel] using hreg i) hdim hinit
      (time i) ⟨htime i, by simp⟩ (point i) (hneg i)
    simpa only [mul_comm] using h
  constructor
  · exact (hratio.eventually_gt_atTop 0).mono fun i hi =>
      (div_pos_iff_of_pos_right (hq i)).mp hi
  · have hinv : Filter.Tendsto (fun i => (S.scalar (time i) (point i) / q i)⁻¹)
        l (𝓝 0) := hratio.inv_tendsto_atTop
    simpa only [inv_div] using hinv

end DifferentialGeometry.PDE.RicciFlow
