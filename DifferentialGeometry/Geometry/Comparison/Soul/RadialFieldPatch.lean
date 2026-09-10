import DifferentialGeometry.Geometry.Comparison.Soul.DistanceGradient
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_infDist_annulus_cutoff
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (_hbc : b < c) (hcr : c < r) :
    ∃ χ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯,
      HasCompactSupport (χ : M → ℝ) ∧
      (∀ q, χ q ∈ Icc 0 1) ∧
      tsupport (χ : M → ℝ) ⊆
        {q : M | a / 2 < Metric.infDist q S ∧ Metric.infDist q S < (c + r) / 2} ∧
      ∀ᶠ q in 𝓝ˢ {q : M | b ≤ Metric.infDist q S ∧ Metric.infDist q S ≤ c}, χ q = 1 := by
  let d : M → ℝ := fun q => Metric.infDist q S
  let K : Set M := {q | b ≤ d q ∧ d q ≤ c}
  let U : Set M := {q | a / 2 < d q ∧ d q < (c + r) / 2}
  have hd : Continuous d := Metric.continuous_infDist_pt S
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const hd).inter (isClosed_le hd continuous_const)
  have hK : IsCompact K :=
    (isCompact_infDist_sublevel g hEnorm hS hSne c).of_isClosed_subset hKclosed
      (fun _ hq => hq.2)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const hd).inter (isOpen_lt hd continuous_const)
  have hKU : K ⊆ U := by
    intro q hq
    change b ≤ d q ∧ d q ≤ c at hq
    change a / 2 < d q ∧ d q < (c + r) / 2
    constructor <;> linarith
  obtain ⟨χ, hχzero, hχone, hχrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (n := (⊤ : ℕ∞)) I
      hU.isClosed_compl hK.isClosed (Set.disjoint_compl_left_iff_subset.mpr hKU)
  have hχsupport : tsupport (χ : M → ℝ) ⊆ U := by
    intro q hq
    by_contra hqU
    have hz : (χ : M → ℝ) =ᶠ[𝓝 q] 0 :=
      hχzero.filter_mono (nhds_le_nhdsSet hqU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hq
  have hχcompact : HasCompactSupport (χ : M → ℝ) :=
    (isCompact_infDist_sublevel g hEnorm hS hSne ((c + r) / 2)).of_isClosed_subset
      (isClosed_tsupport _) (fun q hq => (hχsupport hq).2.le)
  exact ⟨χ, hχcompact, hχrange, hχsupport, hχone⟩

theorem exists_radial_outward_field_patch
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcr : c < r)
    (hd : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => Metric.infDist q S)
      {q : M | 0 < Metric.infDist q S ∧ Metric.infDist q S < r})
    (W : Cₛ^∞⟮I; E, TangentSpace I⟯) (C : ℝ) (hC : 0 ≤ C)
    (hWbound : ∀ q, g.inner q (W q) (W q) ≤ C ^ 2)
    (hWout : ∀ q : M, a ≤ Metric.infDist q S → ∀ u : TangentSpace I q,
      g.inner q u u = 1 → intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
      g.inner q (W q) u < 0) :
    ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ q, g.inner q (V q) (V q) ≤ (max 1 C) ^ 2) ∧
      (∀ q, Real.sqrt (g.inner q (V q) (V q)) ≤ max 1 C) ∧
      (∀ᶠ q in 𝓝ˢ {q : M | b ≤ Metric.infDist q S ∧ Metric.infDist q S ≤ c},
        V q = gradientFun g (fun x => Metric.infDist x S) q) ∧
      (∀ q, Metric.infDist q S ≤ a / 2 ∨ (c + r) / 2 ≤ Metric.infDist q S → V q = W q) ∧
      ∀ q : M, a ≤ Metric.infDist q S → ∀ u : TangentSpace I q,
        g.inner q u u = 1 → intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
        g.inner q (V q) u < 0 := by
  classical
  let d : M → ℝ := fun q => Metric.infDist q S
  let U : Set M := {q | 0 < d q ∧ d q < r}
  let G : (q : M) → TangentSpace I q := gradientFun g d
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (Metric.continuous_infDist_pt S)).inter
      (isOpen_lt (Metric.continuous_infDist_pt S) continuous_const)
  obtain ⟨hGsmooth, hG⟩ := infDist_gradient_smooth_outward_on g hEnorm hS hSne
    hU hd (fun _ hq => hq.1)
  obtain ⟨χ, _, hχrange, hχsupp, hχone⟩ :=
    exists_infDist_annulus_cutoff g hEnorm hS hSne ha hab hbc hcr
  have hχsuppU : tsupport (χ : M → ℝ) ⊆ U := by
    intro q hq
    have hq' := hχsupp hq
    change 0 < d q ∧ d q < r
    constructor <;> linarith [hq'.1, hq'.2]
  have hχG : ContMDiff I I.tangent ∞ (T% fun q => χ q • G q) :=
    χ.contMDiff.contMDiffOn.smul_section_of_tsupport hU hχsuppU hGsmooth
  have hχW : ContMDiff I I.tangent ∞ (T% fun q => (1 - χ q) • W q) :=
    (contMDiff_const.sub χ.contMDiff).smul_section W.contMDiff
  let V : Cₛ^∞⟮I; E, TangentSpace I⟯ :=
    ⟨fun q => χ q • G q + (1 - χ q) • W q, hχG.add_section hχW⟩
  have hVzero (q : M) (hχq : χ q = 0) : V q = W q := by
    simp only [V, ContMDiffSection.coeFn_mk, hχq, zero_smul, sub_zero, one_smul, zero_add]
  have hB0 : 0 ≤ max 1 C := zero_le_one.trans (le_max_left 1 C)
  have hCB : C ^ 2 ≤ (max 1 C) ^ 2 := by
    nlinarith [le_max_right (1 : ℝ) C]
  have h1B : (1 : ℝ) ≤ (max 1 C) ^ 2 := by
    nlinarith [le_max_left (1 : ℝ) C]
  have hbound (q : M) : g.inner q (V q) (V q) ≤ (max 1 C) ^ 2 := by
    by_cases hχq : χ q = 0
    · rw [hVzero q hχq]
      exact (hWbound q).trans hCB
    have hqU : q ∈ U := hχsuppU (subset_tsupport _ hχq)
    have hunit : g.inner q (G q) (G q) = 1 := (hG q hqU).1
    have hnonneg := (hχrange q).1
    have hrem : 0 ≤ 1 - χ q := sub_nonneg.mpr (hχrange q).2
    have hvariance : g.inner q (V q) (V q) =
        χ q * g.inner q (G q) (G q) + (1 - χ q) * g.inner q (W q) (W q) -
          χ q * (1 - χ q) * g.inner q (G q - W q) (G q - W q) := by
      change g.inner q (χ q • G q + (1 - χ q) • W q)
        (χ q • G q + (1 - χ q) • W q) = _
      simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul,
        map_sub, sub_apply, g.symm q (W q) (G q)]
      ring
    have hvarpos := mul_nonneg (mul_nonneg hnonneg hrem)
      (gInner_self_nonneg g q (G q - W q))
    calc
      g.inner q (V q) (V q) ≤ χ q * 1 + (1 - χ q) * g.inner q (W q) (W q) := by
        rw [hvariance, hunit]
        exact sub_le_self _ hvarpos
      _ ≤ χ q * (max 1 C) ^ 2 + (1 - χ q) * (max 1 C) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left h1B hnonneg)
          (mul_le_mul_of_nonneg_left ((hWbound q).trans hCB) hrem)
      _ = (max 1 C) ^ 2 := by ring
  refine ⟨V, hbound, fun q => Real.sqrt_le_iff.mpr ⟨hB0, hbound q⟩, ?_, ?_, ?_⟩
  · filter_upwards [hχone] with q hq
    simp only [V, ContMDiffSection.coeFn_mk, hq, one_smul, sub_self, zero_smul, add_zero]
    rfl
  · intro q hq
    apply hVzero
    apply image_eq_zero_of_notMem_tsupport
    intro hsupp
    have hs := hχsupp hsupp
    rcases hq with hq | hq
    · exact (not_lt_of_ge hq) hs.1
    · exact (not_lt_of_ge hq) hs.2
  · intro q hq u hu hend
    by_cases hχq : χ q = 0
    · rw [hVzero q hχq]
      exact hWout q hq u hu hend
    have hqU : q ∈ U := hχsuppU (subset_tsupport _ hχq)
    have hGu : g.inner q (G q) u = -1 := (hG q hqU).2 u hu hend
    have hWu := hWout q hq u hu hend
    have hχpos : 0 < χ q := lt_of_le_of_ne (hχrange q).1 (Ne.symm hχq)
    have hrem : 0 ≤ 1 - χ q := sub_nonneg.mpr (hχrange q).2
    change g.inner q (χ q • G q + (1 - χ q) • W q) u < 0
    simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul, hGu]
    exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hχpos (by norm_num))
      (mul_nonpos_of_nonneg_of_nonpos hrem hWu.le)

end DifferentialGeometry.Geometry.Topology

end
