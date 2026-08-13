import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.POUFDerivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBoundChartPouEuclFderiv
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponentRawNorm
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.CompChainRuleK
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBoundChartPushedPartialDeriv
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpBoundK
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma ofReal_sq_eq_enorm_sq (r : ℝ) :
    ENNReal.ofReal (r ^ 2) = (‖r‖ₑ : ℝ≥0∞) ^ 2 := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma tensorChartComponent_ae_eq_chartPushed_pou_mul_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2
        =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2) := by
  filter_upwards [self_mem_ae_restrict (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet]
    with y hy
  rw [tensorChartComponent_def]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (tensorChartComponentPou (I := I) (M := M) g r s S α P₀.1 P₀.2) hy]
  unfold tensorChartComponentPou
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartSmoothExt_pou_value_bounded
    (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : EuclN, |chartSmoothExt (I := I) (M := M) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y| ≤ C := by
  classical
  let f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hCD : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α
  have hHCS : HasCompactSupport f :=
    hasCompactSupport_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α
  have hK_compact : IsCompact (closure (Function.support f)) := by
    simpa [tsupport] using hHCS
  by_cases hK_empty : closure (Function.support f) = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro y
    have h : y ∉ Function.support f := by
      intro hy
      have hyK : y ∈ closure (Function.support f) := subset_closure hy
      rw [hK_empty] at hyK
      exact absurd hyK (Set.notMem_empty y)
    have hf : f y = 0 := by
      by_contra hfy
      exact h (by simp [Function.support, hfy])
    simpa [f] using hf
  · have hK_ne : (closure (Function.support f)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hK_empty
    have h_abs_cont : ContinuousOn (fun y : EuclN => |f y|) (closure (Function.support f)) :=
      continuous_abs.comp_continuousOn (hCD.continuous.continuousOn)
    obtain ⟨y0, _hy0, hmax⟩ := hK_compact.exists_isMaxOn hK_ne h_abs_cont
    have hmax' : ∀ x, x ∈ closure (Function.support f) → |f x| ≤ |f y0| := hmax
    refine ⟨|f y0|, abs_nonneg _, ?_⟩
    intro y
    by_cases hy : y ∈ closure (Function.support f)
    · exact hmax' y hy
    · have h : y ∉ Function.support f := by
        intro hsupport
        have hyK : y ∈ closure (Function.support f) := subset_closure hsupport
        exact hy hyK
      have hf : f y = 0 := by
        by_contra hfy
        exact h (by simp [Function.support, hfy])
      rw [show chartSmoothExt (I := I) (M := M) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y = 0 by simpa [f] using hf]
      simp

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma tensorChartComponentRaw_eq_zero_of_notMem_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∀ x : M, x ∉ (chartAt H α).source →
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x = 0 := by
  classical
  intro x hx_src
  have hbase : (trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α).baseSet = (chartAt H α).source := by
    change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).baseSet) =
      (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  have hx_base : x ∉ (trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α).baseSet := by
    rw [hbase]
    exact hx_src
  have hzero : tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x = 0 := by
    have hx_base' : x ∉ (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).toPretrivialization.baseSet := by
      change x ∉ (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).baseSet
      exact hx_base
    rw [tensorChartComponentRaw_def]
    unfold tensorTrivProj
    have hCLM_zero : (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).continuousLinearMapAt ℝ x = 0 := by
      have hlin : (trivializationAt (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) α).linearMapAt ℝ x = 0 :=
        Bundle.Trivialization.linearMapAt_def_of_notMem
          (e := (trivializationAt (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x) α)) (R := ℝ) hx_base
      ext y
      simp [Bundle.Trivialization.continuousLinearMapAt, hlin]
    rw [hCLM_zero]
    simp
  exact hzero

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
lemma norm_iteratedFDerivWithin_mul_le_of_bounded
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {η u : EuclN → ℝ} {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ l ≤ m, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ l η x‖ ≤ C)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Ω,
      ‖iteratedFDerivWithin ℝ m (fun y => η y * u y) Ω x‖ ≤
        K * ∑ l ∈ Finset.range (m + 1),
          ‖iteratedFDerivWithin ℝ l u Ω x‖ := by
  classical
  set K : ℝ := ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * C with hK_def
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (by positivity) hC)
  · intro x hx
    have hn_top : (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞))
    have hbound := norm_iteratedFDerivWithin_mul_le
      (𝕜 := ℝ) (f := η) (g := u) (s := Ω) (x := x) (n := m)
      hη.contDiffOn hu hΩ_open.uniqueDiffOn hx
      hn_top
    have hη_le : ∀ l ∈ Finset.range (m + 1),
        ‖iteratedFDerivWithin ℝ l η Ω x‖ ≤ C := by
      intro l hl
      have hl' : l ≤ m := by
        rw [Finset.mem_range] at hl
        omega
      have h_eq : iteratedFDerivWithin ℝ l η Ω x = iteratedFDeriv ℝ l η x := by
        exact iteratedFDerivWithin_eq_iteratedFDeriv hΩ_open.uniqueDiffOn
          (hη.contDiffAt.of_le (by
            exact_mod_cast (le_top : (l : ℕ∞) ≤ (⊤ : ℕ∞)))) hx
      rw [h_eq]
      exact hη_bound l hl' x hx
    have hA_nonneg : 0 ≤ ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * C :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (by positivity) hC)
    have hreindex :
        (∑ l ∈ Finset.range (m + 1),
          ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖) =
        (∑ l ∈ Finset.range (m + 1),
          ‖iteratedFDerivWithin ℝ l u Ω x‖) := by
      simpa using (Finset.sum_range_reflect
        (fun l => ‖iteratedFDerivWithin ℝ l u Ω x‖) (m + 1))
    have hterm : ∀ l ∈ Finset.range (m + 1),
        (m.choose l : ℝ) * C * ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ ≤
          (∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * C) *
            ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ := by
      intro l hl
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun r => (m.choose r : ℝ) * C)
          (fun r _ => mul_nonneg (by positivity) hC) hl) (norm_nonneg _)
    calc
      ‖iteratedFDerivWithin ℝ m (fun y => η y * u y) Ω x‖
          ≤ ∑ l ∈ Finset.range (m + 1),
              (m.choose l : ℝ) * ‖iteratedFDerivWithin ℝ l η Ω x‖ *
                ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ := hbound
      _ ≤ ∑ l ∈ Finset.range (m + 1),
              (m.choose l : ℝ) * C * ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ := by
            refine Finset.sum_le_sum ?_
            intro l hl
            have hη_le_l := hη_le l hl
            have hnn : 0 ≤ (m.choose l : ℝ) := by positivity
            have hnn' : 0 ≤ ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ := norm_nonneg _
            have hstep : (m.choose l : ℝ) * ‖iteratedFDerivWithin ℝ l η Ω x‖ ≤
                (m.choose l : ℝ) * C :=
              mul_le_mul_of_nonneg_left hη_le_l hnn
            exact mul_le_mul_of_nonneg_right hstep hnn'
      _ ≤ (∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * C) *
              (∑ l ∈ Finset.range (m + 1),
                ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖) := by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum hterm
      _ = (∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * C) *
              (∑ l ∈ Finset.range (m + 1),
                ‖iteratedFDerivWithin ℝ l u Ω x‖) := by
            rw [hreindex]
      _ = K * ∑ l ∈ Finset.range (m + 1),
              ‖iteratedFDerivWithin ℝ l u Ω x‖ := by
            rw [hK_def]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
private lemma norm_iteratedFDeriv_sum_mul_le_of_bounded
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {K : Set EuclN} (hK_sub : K ⊆ Ω)
    {ι : Type*} [Fintype ι]
    (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    {c : ι → EuclN → ℝ} {u : ι → EuclN → ℝ}
    (hc_smooth : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (c i) Ω)
    (hc_bound : ∀ i, ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (c i) x‖ ≤ C)
    (hu_smooth : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) Ω) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ x ∈ K, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (fun z : EuclN => ∑ j, c j z * u j z) x‖ ≤
        K' * (∑ j, ∑ l ∈ Finset.range (i + 1), ‖iteratedFDeriv ℝ l (u j) x‖) := by
  classical
  set Ki : ℕ → ℝ := fun n => ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) * C with hKi_def
  set K' : ℝ := ∑ i ∈ Finset.range (m + 1), Ki i with hK'_def
  have hKi_nn : ∀ n, 0 ≤ Ki n := fun n => by
    dsimp [Ki]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (by positivity) hC)
  have hK'_nn : 0 ≤ K' := by
    dsimp [K']
    exact Finset.sum_nonneg (fun i _ => hKi_nn i)
  refine ⟨K', hK'_nn, ?_⟩
  intro x hxK i hi
  have hxΩ : x ∈ Ω := hK_sub hxK
  have hn_top : (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (i : ℕ∞) ≤ (⊤ : ℕ∞))
  let w : ι → EuclN → ℝ := fun j z => c j z * u j z
  have hw_smooth : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (w j) Ω := fun j =>
    (hc_smooth j).mul (hu_smooth j)
  have h_within_sum :
      iteratedFDerivWithin ℝ i (fun z => ∑ j, w j z) Ω x =
        ∑ j, iteratedFDerivWithin ℝ i (w j) Ω x := by
    simpa using iteratedFDerivWithin_fun_sum_apply hΩ_open.uniqueDiffOn hxΩ
      (fun j _ => ((hw_smooth j).contDiffWithinAt hxΩ).of_le (by
        exact_mod_cast (le_top : (i : ℕ∞) ≤ (⊤ : ℕ∞))))
  have h_global_eq :
      iteratedFDerivWithin ℝ i (fun z => ∑ j, w j z) Ω x =
        iteratedFDeriv ℝ i (fun z => ∑ j, w j z) x := by
    exact iteratedFDerivWithin_of_isOpen i hΩ_open hxΩ
  have hc_within : ∀ j, ∀ l ≤ i, ‖iteratedFDerivWithin ℝ l (c j) Ω x‖ ≤ C := by
    intro j l hl
    rw [iteratedFDerivWithin_of_isOpen l hΩ_open hxΩ]
    exact hc_bound j l (hl.trans hi) x hxK
  have hu_within : ∀ j, ∀ l,
      iteratedFDerivWithin ℝ l (u j) Ω x = iteratedFDeriv ℝ l (u j) x := fun j l =>
    iteratedFDerivWithin_of_isOpen l hΩ_open hxΩ
  have hterm : ∀ j,
      ‖iteratedFDerivWithin ℝ i (w j) Ω x‖ ≤
        ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * C *
          ‖iteratedFDeriv ℝ (i - l) (u j) x‖ := by
    intro j
    have hmul := norm_iteratedFDerivWithin_mul_le (f := c j) (g := u j)
      (s := Ω) (x := x) (n := i) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (hc_smooth j) (hu_smooth j) hΩ_open.uniqueDiffOn hxΩ hn_top
    calc
      ‖iteratedFDerivWithin ℝ i (w j) Ω x‖
          ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
              ‖iteratedFDerivWithin ℝ l (c j) Ω x‖ *
              ‖iteratedFDerivWithin ℝ (i - l) (u j) Ω x‖ := by
            simpa [w] using hmul
      _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * C *
              ‖iteratedFDerivWithin ℝ (i - l) (u j) Ω x‖ := by
            refine Finset.sum_le_sum ?_
            intro l hl
            have hnn1 : 0 ≤ (i.choose l : ℝ) := by positivity
            have hnn2 : 0 ≤ ‖iteratedFDerivWithin ℝ (i - l) (u j) Ω x‖ := norm_nonneg _
            have hl' : l ≤ i := by
              rw [Finset.mem_range] at hl
              omega
            have hstep : (i.choose l : ℝ) * ‖iteratedFDerivWithin ℝ l (c j) Ω x‖ ≤
                (i.choose l : ℝ) * C :=
              mul_le_mul_of_nonneg_left (hc_within j l hl') hnn1
            exact mul_le_mul_of_nonneg_right hstep hnn2
      _ = ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * C *
              ‖iteratedFDeriv ℝ (i - l) (u j) x‖ := by
            refine Finset.sum_congr rfl ?_
            intro l hl
            rw [hu_within j (i - l)]
  have hKi_le : Ki i ≤ K' := by
    dsimp [K']
    exact Finset.single_le_sum (f := Ki) (fun i' _ => hKi_nn i') (Finset.mem_range.mpr
      (Nat.lt_succ_of_le hi))
  have hstep_inner : ∀ l ≤ i, (i.choose l : ℝ) * C ≤ Ki i := by
    intro l hl
    dsimp [Ki]
    exact Finset.single_le_sum
      (f := fun l' => (i.choose l' : ℝ) * C)
      (fun l' _ => mul_nonneg (by positivity) hC)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
  calc
    ‖iteratedFDeriv ℝ i (fun z => ∑ j, w j z) x‖
        = ‖iteratedFDerivWithin ℝ i (fun z => ∑ j, w j z) Ω x‖ := by rw [h_global_eq]
    _ = ‖∑ j, iteratedFDerivWithin ℝ i (w j) Ω x‖ := by rw [h_within_sum]
    _ ≤ ∑ j, ‖iteratedFDerivWithin ℝ i (w j) Ω x‖ := norm_sum_le _ _
    _ ≤ ∑ j, ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * C *
            ‖iteratedFDeriv ℝ (i - l) (u j) x‖ := by
          exact Finset.sum_le_sum (fun j _ => hterm j)
    _ ≤ ∑ j, ∑ l ∈ Finset.range (i + 1), Ki i *
            ‖iteratedFDeriv ℝ (i - l) (u j) x‖ := by
          refine Finset.sum_le_sum ?_
          intro j _
          refine Finset.sum_le_sum ?_
          intro l hl
          have hl' : l ≤ i := by
            rw [Finset.mem_range] at hl
            omega
          exact mul_le_mul_of_nonneg_right (hstep_inner l hl') (norm_nonneg _)
    _ = ∑ j, Ki i * (∑ l ∈ Finset.range (i + 1),
            ‖iteratedFDeriv ℝ (i - l) (u j) x‖) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact (Finset.mul_sum (Finset.range (i + 1))
            (fun l => ‖iteratedFDeriv ℝ (i - l) (u j) x‖) (Ki i)).symm
    _ = ∑ j, Ki i * (∑ l ∈ Finset.range (i + 1),
            ‖iteratedFDeriv ℝ l (u j) x‖) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          refine congr_arg (fun s : ℝ => Ki i * s) ?_
          simpa using (Finset.sum_range_reflect (fun l => ‖iteratedFDeriv ℝ l (u j) x‖) (i + 1))
    _ ≤ ∑ j, K' * (∑ l ∈ Finset.range (i + 1),
            ‖iteratedFDeriv ℝ l (u j) x‖) := by
          refine Finset.sum_le_sum ?_
          intro j _
          exact mul_le_mul_of_nonneg_right hKi_le
            (Finset.sum_nonneg (fun l _ => norm_nonneg _))
    _ = K' * (∑ j, ∑ l ∈ Finset.range (i + 1), ‖iteratedFDeriv ℝ l (u j) x‖) := by
          rw [← Finset.mul_sum]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
private lemma norm_iteratedFDerivWithin_comp_contDiffOn_le
    {d kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω')
    {n : ℕ} (hn : n ≤ kmax) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) {C : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i u Ω' (Φ.toFun x)‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun y => u (Φ.toFun y)) Ω x‖ ≤
      n.factorial * C * Φ.derivBoundMaxOne ^ n := by
  classical
  set D := Φ.derivBoundMaxOne with hD_def
  have hD_ge_1 : 1 ≤ D := Φ.derivBoundMaxOne_ge_one
  have hn_le : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))
  have hΦ_iter : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i Φ.toFun Ω x‖ ≤ D ^ i := by
    intro i hi1 hin
    have hi_le_kmax : i ≤ kmax := hin.trans hn
    have hbound := Φ.iter_deriv_bounded_at i hi_le_kmax x
    have hbnd' : ‖iteratedFDeriv ℝ i Φ.toFun x‖ ≤ D :=
      hbound.trans Φ.deriv_bound_le_derivBoundMaxOne
    have hwithin : iteratedFDerivWithin ℝ i Φ.toFun Ω x = iteratedFDeriv ℝ i Φ.toFun x := by
      exact iteratedFDerivWithin_of_isOpen i hΩ_open hx
    rw [hwithin]
    rcases i with _ | i
    · exact (Nat.lt_irrefl 0 hi1).elim
    · have h_pow_mono : D ≤ D ^ (i + 1) := by
        have hpw : 1 ≤ D ^ i := one_le_pow₀ hD_ge_1
        calc D = D * 1 := by ring
          _ ≤ D * D ^ i := mul_le_mul_of_nonneg_left hpw Φ.derivBoundMaxOne_pos.le
          _ = D ^ (i + 1) := by ring
      exact hbnd'.trans h_pow_mono
  have hst : Set.MapsTo Φ.toFun Ω Ω' := Φ.bijOn.mapsTo
  have hf_cd : ContDiffOn ℝ (⊤ : ℕ∞) Φ.toFun Ω :=
    (Φ.toFun_smooth.contDiffOn).mono (subset_univ Ω)
  exact norm_iteratedFDerivWithin_comp_le (g := u) (f := Φ.toFun) (n := n)
    (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    hu hf_cd hn_le hΩ'_open.uniqueDiffOn hΩ_open.uniqueDiffOn hst hx
    (C := C) (D := D) hC hΦ_iter

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
private lemma uniform_iteratedFDeriv_bound_on_compact_of_contDiffOn
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {K : Set EuclN} (hK : IsCompact K) (hK_sub : K ⊆ Ω) (m : ℕ)
    {ι : Type*} [Finite ι] {c : ι → EuclN → ℝ}
    (hc : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (c i) Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (c i) x‖ ≤ C := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  by_cases hKne : K.Nonempty
  · have hmax : ∀ i, ∀ j ≤ m, ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ j (c i) x‖ ≤ M := by
      intro i j hj
      have hwithin_cont : ContinuousOn (fun x : EuclN => iteratedFDerivWithin ℝ j (c i) Ω x) Ω :=
        (hc i).continuousOn_iteratedFDerivWithin (by
          exact_mod_cast (le_top : (j : ℕ∞) ≤ (⊤ : ℕ∞))) hΩ_open.uniqueDiffOn
      have h_eq_on : ∀ x ∈ Ω, ‖iteratedFDerivWithin ℝ j (c i) Ω x‖ = ‖iteratedFDeriv ℝ j (c i) x‖ :=
        fun x hx => by rw [iteratedFDerivWithin_of_isOpen j hΩ_open hx]
      have hcont_norm_Ω : ContinuousOn (fun x : EuclN => ‖iteratedFDeriv ℝ j (c i) x‖) Ω :=
        hwithin_cont.norm.congr (fun x hx => by
          rw [iteratedFDerivWithin_of_isOpen j hΩ_open hx])
      have hcont_norm_K : ContinuousOn (fun x : EuclN => ‖iteratedFDeriv ℝ j (c i) x‖) K :=
        hcont_norm_Ω.mono hK_sub
      obtain ⟨x₀, hx₀K, hx₀max⟩ := hK.exists_isMaxOn hKne hcont_norm_K
      refine ⟨‖iteratedFDeriv ℝ j (c i) x₀‖, norm_nonneg _, ?_⟩
      intro x hx
      exact hx₀max hx
    choose M hM_nn hM_bd using hmax
    let Ci : ι → ℝ := fun i => (Finset.range (m + 1)).sup' (by simp) fun j =>
      if hj : j ≤ m then M i j hj else 0
    let C : ℝ := ∑ i, Ci i
    have hCi_nn : ∀ i, 0 ≤ Ci i := by
      intro i
      dsimp [Ci]
      refine Finset.le_sup'_of_le _ (by simp : (0 : ℕ) ∈ Finset.range (m + 1)) ?_
      simp only [Nat.zero_le, dif_pos]
      exact hM_nn i 0 (Nat.zero_le m)
    have hC_nn : 0 ≤ C := by
      dsimp [C]
      exact Finset.sum_nonneg (fun i _ => hCi_nn i)
    refine ⟨C, hC_nn, ?_⟩
    intro i j hj x hx
    refine (hM_bd i j hj x hx).trans ?_
    have hmem : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have h_le_Ci : M i j hj ≤ Ci i := by
      dsimp [Ci]
      refine Finset.le_sup'_of_le _ hmem ?_
      simp only [hj, dif_pos, le_refl]
    refine h_le_Ci.trans ?_
    dsimp [C]
    exact Finset.single_le_sum (f := Ci) (fun i' _ => hCi_nn i') (Finset.mem_univ i)
  · refine ⟨0, le_refl _, ?_⟩
    intro i j hj x hx
    exact absurd ⟨x, hx⟩ hKne

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private noncomputable def transitionCoeffOnEuclid
    (r s : ℕ) (γ α : M) (P₀ Q : TensorCompIdx (E := E) r s) (y : EuclN) : ℝ :=
  transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q
    ((extChartAt I γ).symm ((toEuclidean (E := E)).symm y))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] private lemma transitionCoeffOnEuclid_def
    (r s : ℕ) (γ α : M) (P₀ Q : TensorCompIdx (E := E) r s) (y : EuclN) :
    transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s γ α P₀ Q y =
      transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q
        ((extChartAt I γ).symm ((toEuclidean (E := E)).symm y)) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma transitionCoeffOnEuclid_contDiffOn_overlap
    (r s : ℕ) (γ α : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s γ α P₀ Q)
      (chartOverlapEuclid (I := I) (M := M) γ α) := by
  classical
  have h_chart_symm : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I γ).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) γ) :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.contMDiffOn_chart_symm (I := I) γ
  have h_tc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q)
      ((chartAt H γ).source ∩ (chartAt H α).source) :=
    contMDiffOn_transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q
  have h_maps : Set.MapsTo
      (fun y : EuclN => (extChartAt I γ).symm ((toEuclidean (E := E)).symm y))
      (chartOverlapEuclid (I := I) (M := M) γ α)
      ((chartAt H γ).source ∩ (chartAt H α).source) := by
    intro y hy
    rcases hy with ⟨w, ⟨x, hx, hxw⟩, hwy⟩
    have hx_ext : x ∈ (extChartAt I γ).source := by
      rw [extChartAt_source (I := I)]
      exact hx.1
    have h_γinv : (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) = x := by
      rw [← hwy, ← hxw, (toEuclidean (E := E)).symm_apply_apply]
      exact (extChartAt I γ).left_inv hx_ext
    change (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H γ).source ∩ (chartAt H α).source
    rw [h_γinv]
    exact ⟨hx.1, hx.2⟩
  have h_sub : chartOverlapEuclid (I := I) (M := M) γ α ⊆
      chartTargetEuclid (I := I) (M := M) γ :=
    chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ α
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞
      (fun y : EuclN => transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q
        ((extChartAt I γ).symm ((toEuclidean (E := E)).symm y)))
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    h_tc.comp (h_chart_symm.mono h_sub) h_maps
  simpa [transitionCoeffOnEuclid_def] using (contMDiffOn_iff_contDiffOn).mp h_comp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
private lemma lintegral_comp_toFun_le_const
    {d kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    (hΩ_open : IsOpen Ω)
    (F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    (∫⁻ y in Ω, F (Φ.toFun y) ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) ≤
      ENNReal.ofReal (1 / Φ.jacobian_lower_bound) *
        (∫⁻ z in Ω', F z ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) := by
  classical
  have h_aux := Φ.lintegral_image_eq hΩ_open F
  have h_mono : ENNReal.ofReal Φ.jacobian_lower_bound *
        (∫⁻ y in Ω, F (Φ.toFun y) ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) ≤
      ∫⁻ y in Ω,
        ENNReal.ofReal |(fderiv ℝ Φ.toFun y).det| * F (Φ.toFun y)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' hΩ_open.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro y hy
    have hdet : ENNReal.ofReal Φ.jacobian_lower_bound ≤
        ENNReal.ofReal |(fderiv ℝ Φ.toFun y).det| :=
      ENNReal.ofReal_le_ofReal (Φ.jacobian_lower y hy)
    exact mul_le_mul_of_nonneg_right hdet (zero_le _)
  have h_le : ENNReal.ofReal Φ.jacobian_lower_bound *
        (∫⁻ y in Ω, F (Φ.toFun y) ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) ≤
      ∫⁻ z in Ω', F z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    h_mono.trans_eq h_aux.symm
  have h_jac_ne : ENNReal.ofReal Φ.jacobian_lower_bound ≠ 0 := by
    exact (ENNReal.ofReal_ne_zero_iff.mpr Φ.jacobian_lower_bound_pos)
  have h_mul_inv : ENNReal.ofReal (1 / Φ.jacobian_lower_bound) *
        ENNReal.ofReal Φ.jacobian_lower_bound = 1 := by
    rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) Φ.jacobian_lower_bound_pos.le)]
    rw [show (1 / Φ.jacobian_lower_bound) * Φ.jacobian_lower_bound = 1 from
      div_mul_cancel₀ (a := (1 : ℝ)) (b := Φ.jacobian_lower_bound)
        Φ.jacobian_lower_bound_pos.ne']
    norm_num
  have hstep : ENNReal.ofReal (1 / Φ.jacobian_lower_bound) *
        (ENNReal.ofReal Φ.jacobian_lower_bound *
          (∫⁻ y in Ω, F (Φ.toFun y) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))))) ≤
      ENNReal.ofReal (1 / Φ.jacobian_lower_bound) *
        (∫⁻ z in Ω', F z ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) :=
    mul_le_mul_of_nonneg_left h_le (zero_le _)
  calc
    (∫⁻ y in Ω, F (Φ.toFun y) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))))
        = ENNReal.ofReal (1 / Φ.jacobian_lower_bound) *
              (ENNReal.ofReal Φ.jacobian_lower_bound *
                (∫⁻ y in Ω, F (Φ.toFun y) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))))) := by
          rw [← mul_assoc, h_mul_inv, one_mul]
    _ ≤ ENNReal.ofReal (1 / Φ.jacobian_lower_bound) *
          (∫⁻ z in Ω', F z ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) := hstep

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
private lemma finset_sum_le_finset_sum_mul_of_forall
    {ι : Type*} [Fintype ι] (m : ℕ) (c : ℝ≥0∞)
    (x y : ι → ℕ → ℝ≥0∞)
    (h : ∀ Q, ∀ j ∈ Finset.range (m + 1), x Q j ≤ c * y Q j) :
    (∑ Q, ∑ j ∈ Finset.range (m + 1), x Q j) ≤
      c * (∑ Q, ∑ j ∈ Finset.range (m + 1), y Q j) := by
  classical
  calc
    (∑ Q, ∑ j ∈ Finset.range (m + 1), x Q j)
        ≤ ∑ Q, ∑ j ∈ Finset.range (m + 1), c * y Q j := by
          refine Finset.sum_le_sum ?_
          intro Q _
          exact Finset.sum_le_sum (fun j hj => h Q j hj)
    _ = c * (∑ Q, ∑ j ∈ Finset.range (m + 1), y Q j) := by
          have h1 : c * (∑ Q, ∑ j ∈ Finset.range (m + 1), y Q j) =
              ∑ Q, c * (∑ j ∈ Finset.range (m + 1), y Q j) :=
            Finset.mul_sum (Finset.univ) (fun Q => ∑ j ∈ Finset.range (m + 1), y Q j) c
          have h2 : (∑ Q, c * (∑ j ∈ Finset.range (m + 1), y Q j)) =
              ∑ Q, ∑ j ∈ Finset.range (m + 1), c * y Q j := by
            refine Finset.sum_congr rfl ?_
            intro Q _
            exact Finset.mul_sum (Finset.range (m + 1)) (fun j => y Q j) c
          exact h2.symm.trans h1.symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private lemma mul_le_mul_sum_trans
    {a b c : ℝ≥0∞} {T S1 S2 : ℝ≥0∞}
    (hab : a * b = c) (hT : T ≤ b * S1) (hS : S1 ≤ S2) :
    a * T ≤ c * S2 := by
  calc
    a * T ≤ a * (b * S1) := mul_le_mul_of_nonneg_left hT (zero_le _)
    _ = (a * b) * S1 := by rw [← mul_assoc]
    _ = c * S1 := by rw [hab]
    _ ≤ c * S2 := mul_le_mul_of_nonneg_left hS (zero_le _)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
private lemma lintegral_le_const_mul_lintegral_of_ae_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s t : Set α)
    (hs : MeasurableSet s) (hst : s ⊆ t) (a : ℝ≥0∞) (ha : a ≠ ⊤)
    {f g : α → ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, x ∈ s → f x ≤ a * g x) :
    (∫⁻ x in s, f x ∂μ) ≤ a * (∫⁻ x in t, g x ∂μ) := by
  have hf' : f ≤ᵐ[μ.restrict s] (fun x => a * g x) := by
    change ∀ᵐ x ∂(μ.restrict s), f x ≤ a * g x
    exact (ae_restrict_iff' hs).mpr hf
  calc
    (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in s, a * g x ∂μ := lintegral_mono_ae hf'
    _ ≤ ∫⁻ x in t, a * g x ∂μ := lintegral_mono_set hst
    _ = a * (∫⁻ x in t, g x ∂μ) := lintegral_const_mul' a g ha

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
private lemma lintegral_inter_eq_of_eq_zero_outside
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A C : Set α} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (f : α → ℝ≥0∞) (hf : ∀ x ∈ A, x ∉ C → f x = 0) :
    (∫⁻ x in A, f x ∂μ) = ∫⁻ x in A ∩ C, f x ∂μ := by
  rw [← lintegral_indicator hA, ← lintegral_indicator (hA.inter hC)]
  apply lintegral_congr
  intro x
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA]
    by_cases hxC : x ∈ C
    · have hxAC : x ∈ A ∩ C := ⟨hxA, hxC⟩
      rw [Set.indicator_of_mem hxAC]
    · rw [Set.indicator_of_notMem (fun hx => hxC hx.2), hf x hxA hxC]
  · rw [Set.indicator_of_notMem hxA,
      Set.indicator_of_notMem (fun hx => hxA hx.1)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
private irreducible_def pouCoordValue (γ : M) (z : EuclN) : ℝ :=
  ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    ((extChartAt I γ).symm ((toEuclidean (E := E)).symm z))

private irreducible_def rawChartFderivNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ : M) (Q : TensorCompIdx (E := E) r s) (j : ℕ) (z : EuclN) : ℝ :=
  ‖iteratedFDeriv ℝ j (chartPushedRaw (I := I) (M := M) γ
    (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)) z‖

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private irreducible_def pouWeightedIntegrand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ : M) (Q : TensorCompIdx (E := E) r s) (j : ℕ) (z : EuclN) : ℝ≥0∞ :=
  ENNReal.ofReal (pouCoordValue (I := I) (M := M) γ z *
    (rawChartFderivNorm (I := I) (M := M) g r s T γ Q j z) ^ 2)

private irreducible_def pouWeightedF0
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) (y : EuclN) : ℝ≥0∞ :=
  ENNReal.ofReal (
    ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
    ‖iteratedFDeriv ℝ m (chartPushedRaw (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)) y‖ ^ 2)

private irreducible_def pouWeightedG
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ : M) (m : ℕ) (z : EuclN) : ℝ≥0∞ :=
  ∑ Q : TensorCompIdx (E := E) r s, ∑ j ∈ Finset.range (m + 1),
    pouWeightedIntegrand (I := I) (M := M) g r s T γ Q j z

private irreducible_def pouWeightedSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ : M) (m : ℕ) (Ω : Set EuclN) : ℝ≥0∞ :=
  ∑ Q : TensorCompIdx (E := E) r s, ∑ j ∈ Finset.range (m + 1),
    ∫⁻ z in Ω, pouWeightedIntegrand (I := I) (M := M) g r s T γ Q j z ∂(volume : Measure EuclN)

private irreducible_def pouWeightedSumComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ : M) (m : ℕ) (Ω : Set EuclN) (φ : EuclN → EuclN) : ℝ≥0∞ :=
  ∑ Q : TensorCompIdx (E := E) r s, ∑ j ∈ Finset.range (m + 1),
    ∫⁻ y in Ω, pouWeightedIntegrand (I := I) (M := M) g r s T γ Q j (φ y) ∂(volume : Measure EuclN)

private irreducible_def pouSqrtIntegrand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ : M) (Q : TensorCompIdx (E := E) r s) (j : ℕ) (z : EuclN) : ℝ :=
  Real.sqrt (pouCoordValue (I := I) (M := M) γ z) *
    rawChartFderivNorm (I := I) (M := M) g r s T γ Q j z

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouWeightedIntegrand_comp_aemeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ : M) (m : ℕ) {Ω Ω' : Set EuclN}
    (hΩ : MeasurableSet Ω) (hΩ'_open : IsOpen Ω')
    (hΩ'_target : Ω' ⊆ chartTargetEuclid (I := I) (M := M) γ)
    (Φ : SmoothDiffeoBoundedAtOrder (Module.finrank ℝ E) Ω Ω' m)
    (hv : ∀ Q : TensorCompIdx (E := E) r s,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (chartPushedRaw (I := I) (M := M) γ
          (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)) Ω') :
    ∀ Q : TensorCompIdx (E := E) r s, ∀ j : ℕ,
      AEMeasurable
        (fun y => pouWeightedIntegrand (I := I) (M := M) g r s T γ Q j (Φ.toFun y))
        ((volume : Measure EuclN).restrict Ω) := by
  have h_norm_cont : ∀ Q : TensorCompIdx (E := E) r s, ∀ j : ℕ,
      ContinuousOn (fun y : EuclN =>
        rawChartFderivNorm (I := I) (M := M) g r s T γ Q j y) Ω' := by
    intro Q j
    have hwithin : ContinuousOn (fun y : EuclN => iteratedFDerivWithin ℝ j
        (chartPushedRaw (I := I) (M := M) γ
          (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)) Ω' y) Ω' :=
      (hv Q).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ (⊤ : ℕ∞))) hΩ'_open.uniqueDiffOn
    have hglobal : ContinuousOn (fun y : EuclN => ‖iteratedFDeriv ℝ j
        (chartPushedRaw (I := I) (M := M) γ
          (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)) y‖) Ω' :=
      hwithin.norm.congr (fun y hy => by
        rw [iteratedFDerivWithin_of_isOpen j hΩ'_open hy])
    simpa only [rawChartFderivNorm] using hglobal
  have h_pou_cont : ContinuousOn (fun y : EuclN =>
      pouCoordValue (I := I) (M := M) γ y) Ω' := by
    have h_toE : ContinuousOn (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) γ) :=
      (toEuclidean (E := E)).symm.continuous.continuousOn
    have h_symm : ContinuousOn (extChartAt I γ).symm ((extChartAt I γ).target) :=
      continuousOn_extChartAt_symm (I := I) γ
    have h_symm_cont : ContinuousOn (fun y : EuclN =>
        (extChartAt I γ).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) γ) := by
      refine h_symm.comp h_toE ?_
      intro y hy
      simpa [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] using hy
    have h_pou : Continuous ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      (chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
    simpa only [pouCoordValue] using
      h_pou.comp_continuousOn (h_symm_cont.mono hΩ'_target)
  intro Q j
  have h1 : ContinuousOn (fun y : EuclN =>
      pouCoordValue (I := I) (M := M) γ (Φ.toFun y)) Ω :=
    h_pou_cont.comp Φ.continuous_toFun.continuousOn (fun y hy => Φ.bijOn.mapsTo hy)
  have h2 : ContinuousOn (fun y : EuclN =>
      rawChartFderivNorm (I := I) (M := M) g r s T γ Q j (Φ.toFun y)) Ω :=
    (h_norm_cont Q j).comp Φ.continuous_toFun.continuousOn
      (fun y hy => Φ.bijOn.mapsTo hy)
  have hcont : ContinuousOn (fun y : EuclN =>
      ENNReal.ofReal (pouCoordValue (I := I) (M := M) γ (Φ.toFun y) *
        (rawChartFderivNorm (I := I) (M := M) g r s T γ Q j (Φ.toFun y)) ^ 2)) Ω :=
    ENNReal.continuous_ofReal.comp_continuousOn (h1.mul (h2.pow 2))
  simpa only [pouWeightedIntegrand] using hcont.aemeasurable hΩ

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma lintegral_pouWeightedF0_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    {Ω Ω' C : Set EuclN} (hΩ_open : IsOpen Ω) (hC : MeasurableSet C)
    (hΩ'_target : Ω' ⊆ chartTargetEuclid (I := I) (M := M) γ)
    (Φ : SmoothDiffeoBoundedAtOrder (Module.finrank ℝ E) Ω Ω' m)
    (a : ℝ≥0∞) (ha : a ≠ ⊤)
    (hpt : ∀ y ∈ Ω ∩ C,
      pouWeightedF0 (I := I) (M := M) g r s T γ α P₀ m y ≤
        a * pouWeightedG (I := I) (M := M) g r s T γ m (Φ.toFun y))
    (hmeas : ∀ Q : TensorCompIdx (E := E) r s, ∀ j : ℕ,
      AEMeasurable
        (fun y => pouWeightedIntegrand (I := I) (M := M) g r s T γ Q j (Φ.toFun y))
        ((volume : Measure EuclN).restrict Ω)) :
    (∫⁻ y in Ω ∩ C,
      pouWeightedF0 (I := I) (M := M) g r s T γ α P₀ m y ∂volume) ≤
      (a * ENNReal.ofReal (1 / Φ.jacobian_lower_bound)) *
        pouWeightedSum (I := I) (M := M) g r s T γ m
          (chartTargetEuclid (I := I) (M := M) γ) := by
  have hsum_integral :
      (∫⁻ y in Ω, pouWeightedG (I := I) (M := M) g r s T γ m (Φ.toFun y)
          ∂volume) =
        pouWeightedSumComp (I := I) (M := M) g r s T γ m Ω Φ.toFun := by
    simp only [pouWeightedG, pouWeightedSumComp]
    rw [lintegral_finset_sum' Finset.univ (fun Q _ =>
      Finset.aemeasurable_fun_sum (Finset.range (m + 1)) (fun j _ => hmeas Q j))]
    refine Finset.sum_congr rfl ?_
    intro Q _
    rw [lintegral_finset_sum' (Finset.range (m + 1)) (fun j _ => hmeas Q j)]
  have hchange : pouWeightedSumComp (I := I) (M := M) g r s T γ m Ω Φ.toFun ≤
      ENNReal.ofReal (1 / Φ.jacobian_lower_bound) *
        pouWeightedSum (I := I) (M := M) g r s T γ m Ω' := by
    simp only [pouWeightedSumComp, pouWeightedSum]
    exact finset_sum_le_finset_sum_mul_of_forall m
      (ENNReal.ofReal (1 / Φ.jacobian_lower_bound))
      (fun Q j => ∫⁻ y in Ω,
        pouWeightedIntegrand (I := I) (M := M) g r s T γ Q j (Φ.toFun y) ∂volume)
      (fun Q j => ∫⁻ z in Ω',
        pouWeightedIntegrand (I := I) (M := M) g r s T γ Q j z ∂volume)
      (fun Q j _ => lintegral_comp_toFun_le_const Φ hΩ_open
        (pouWeightedIntegrand (I := I) (M := M) g r s T γ Q j))
  have hmono : pouWeightedSum (I := I) (M := M) g r s T γ m Ω' ≤
      pouWeightedSum (I := I) (M := M) g r s T γ m
        (chartTargetEuclid (I := I) (M := M) γ) := by
    simp only [pouWeightedSum]
    refine Finset.sum_le_sum ?_
    intro Q _
    refine Finset.sum_le_sum ?_
    intro j _
    exact lintegral_mono_set hΩ'_target
  have hpointwise := lintegral_le_const_mul_lintegral_of_ae_le
    (volume : Measure EuclN) (Ω ∩ C) Ω
    (hΩ_open.measurableSet.inter hC) (fun _ hy => hy.1) a ha
    (f := pouWeightedF0 (I := I) (M := M) g r s T γ α P₀ m)
    (g := fun y => pouWeightedG (I := I) (M := M) g r s T γ m (Φ.toFun y))
    (Filter.Eventually.of_forall (fun y hy => hpt y hy))
  calc
    (∫⁻ y in Ω ∩ C,
        pouWeightedF0 (I := I) (M := M) g r s T γ α P₀ m y ∂volume)
        ≤ a * (∫⁻ y in Ω,
          pouWeightedG (I := I) (M := M) g r s T γ m (Φ.toFun y) ∂volume) :=
      hpointwise
    _ = a * pouWeightedSumComp (I := I) (M := M) g r s T γ m Ω Φ.toFun := by
      rw [hsum_integral]
    _ ≤ a * (ENNReal.ofReal (1 / Φ.jacobian_lower_bound) *
        pouWeightedSum (I := I) (M := M) g r s T γ m Ω') :=
      mul_le_mul_of_nonneg_left hchange (zero_le _)
    _ ≤ a * (ENNReal.ofReal (1 / Φ.jacobian_lower_bound) *
        pouWeightedSum (I := I) (M := M) g r s T γ m
          (chartTargetEuclid (I := I) (M := M) γ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmono (zero_le _)) (zero_le _)
    _ = (a * ENNReal.ofReal (1 / Φ.jacobian_lower_bound)) *
        pouWeightedSum (I := I) (M := M) g r s T γ m
          (chartTargetEuclid (I := I) (M := M) γ) := by rw [mul_assoc]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartAtlasPOU_sum_eq_one_on_chartTarget
    (α : M) (y : EuclN) :
    (∑ γ ∈ chartAtlasPOU_finset (I := I) (M := M),
      ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = 1 := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hsum_fin : (∑ᶠ γ : M,
      ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = 1 :=
    SmoothPartitionOfUnity.sum_eq_one (f := chartAtlasPOU I M)
      (x := x) (by simp : x ∈ (univ : Set M))
  rw [← hsum_fin]
  exact (finsum_eq_sum_of_support_subset
    (f := fun γ : M => ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    (s := chartAtlasPOU_finset (I := I) (M := M))
    (by
      intro γ hγ_supp
      by_contra hγ
      have hzero : ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
        chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hγ x
      exact hγ_supp (by simpa [Function.support] using hzero))).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M]
    [SigmaCompactSpace M] in
lemma eLpNorm_iterWeakPartial_le_basis
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {u : EuclN → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_supp : HasCompactSupport u) (hu_sub : tsupport u ⊆ Ω)
    {m : ℕ} (β : Fin m → Fin (Module.finrank ℝ E)) :
    eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β u Ω) 2
        (volume.restrict Ω) ≤
      eLpNorm (fun y => Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m u y‖) 2
        (volume.restrict Ω) := by
  classical
  have hae := iterWeakPartial_smooth_ae_eq_iterClassicalPartial
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open m β
    hu_smooth hu_supp hu_sub
  rw [eLpNorm_congr_ae (p := 2) hae]
  have hpt : ∀ᵐ y ∂(volume.restrict Ω),
      ‖iterClassicalPartial (d := Module.finrank ℝ E) m β u y‖ ≤
        Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m u y‖ := by
    filter_upwards with y
    have hle : ‖iterClassicalPartial (d := Module.finrank ℝ E) m β u y‖ ≤
        ‖iteratedFDeriv ℝ m u y‖ :=
      norm_iterClassicalPartial_le_iteratedFDeriv (d := Module.finrank ℝ E) m β hu_smooth y
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (m + 1 : ℝ) := by
      have hle' : (1 : ℝ) ^ 2 ≤ (m + 1 : ℝ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      exact (Real.le_sqrt (by positivity : 0 ≤ (1 : ℝ))
        (by positivity : 0 ≤ (m + 1 : ℝ))).2 hle'
    calc
      ‖iterClassicalPartial (d := Module.finrank ℝ E) m β u y‖
          ≤ ‖iteratedFDeriv ℝ m u y‖ := hle
      _ ≤ Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m u y‖ := by
            exact le_mul_of_one_le_left (norm_nonneg _) hsqrt
  have hpt' : ∀ᵐ y ∂(volume.restrict Ω),
      ‖iterClassicalPartial (d := Module.finrank ℝ E) m β u y‖ ≤
        ‖(Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m u y‖ : ℝ)‖ := by
    filter_upwards [hpt] with y hy
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _)] using hy
  exact eLpNorm_mono_ae hpt'

lemma iteratedWeakSobolevNorm_tensorChartComp_le_rawClassical
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C * (∑ m ∈ Finset.range (k + 1),
          eLpNorm (fun y =>
            ‖iteratedFDeriv ℝ m (chartPushedRaw (I := I) (M := M) α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)) y‖) 2
            (volume.restrict (tsupport (chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set η : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hη_def
  set v : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) with hv_def
  set K : Set EuclN := tsupport η with hK_def
  set f : EuclN → ℝ := tensorChartComp (I := I) (M := M) g r s T α Idx Jdx with hf_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    rw [hη_def]
    exact chartSmoothExt_chartAtlasPOU_contDiff (I := I) (M := M) α
  obtain ⟨Cη, hCη_nn, hη_bound⟩ :=
    exists_iteratedFDeriv_bound_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α k
  have hf_eq : f = fun y : EuclN => η y * v y := by
    rw [hf_def]
    exact tensorChartComp_eq_chartSmoothExt_mul_chartPushedRaw_raw
      (I := I) (M := M) g r s T α Idx Jdx
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf_def]
    exact (tensorChartComponent_contMDiff (I := I) (M := M) g r s T α Idx Jdx).contDiff
  have hf_cpt : HasCompactSupport f := by
    rw [hf_def]
    exact tensorChartComponent_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
  have hf_sub : tsupport f ⊆ Ω := by
    rw [hf_def, tensorChartComp_def, tensorChartComponent_def]
    exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
      (I := I) (M := M)
      (tensorChartComponentPou_support_subset_chart_source (I := I) (M := M) g r s T α Idx Jdx)
  have hts_f_η : tsupport f ⊆ tsupport η := by
    have hsup : Function.support f ⊆ Function.support η := by
      intro z hz
      by_contra hη0
      have hfz : f z = 0 := by
        rw [hf_eq]
        change η z * v z = 0
        have hηz : η z = 0 := by
          by_contra hηz
          exact hη0 (by simpa [Function.support] using hηz)
        simp [hηz]
      exact hz hfz
    exact (closure_mono hsup).trans (by
      simp [tsupport])
  have hPOU_tsupp : tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) α
  have hts_η_Ω : tsupport η ⊆ Ω := by
    set KP : Set EuclN := (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)))
      with hKP_def
    have hη_supp_KP : Function.support η ⊆ KP := by
      intro y hy
      by_contra hyK
      apply hy
      by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
      · obtain ⟨z, hz_target, hzy⟩ := hy_target
        have hy_symm : (toEuclidean (E := E)).symm y = z := by
          rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
        have hval : chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y =
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
          change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0) = _
          rw [if_pos (by rw [hy_symm]; exact hz_target)]
        rw [hη_def]
        rw [hval]
        rw [hy_symm]
        by_contra hne
        apply hyK
        have hsymm_in_supp : (extChartAt I α).symm z ∈ tsupport
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
          subset_tsupport _ (Function.mem_support.mpr hne)
        have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
          (extChartAt I α).right_inv hz_target
        refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_supp, hz_eq⟩, hzy⟩
      · rw [hη_def]
        change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          else 0) = 0
        rw [if_neg]
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
        exact hy_target
    have hKP_compact : IsCompact KP :=
      by
      have hts_compact : IsCompact (tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
        (isClosed_tsupport _).isCompact
      have hcont_ext : ContinuousOn (extChartAt I α) (tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
        refine (continuousOn_extChartAt (I := I) α).mono ?_
        intro x hx
        have hxsrc : x ∈ (chartAt H α).source := hPOU_tsupp hx
        rw [← extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hxsrc
        exact hxsrc
      exact (hts_compact.image_of_continuousOn hcont_ext).image
        (toEuclidean (E := E)).continuous
    have hKP_closed : IsClosed KP := hKP_compact.isClosed
    have hη_ts_KP : tsupport η ⊆ KP := by
      rw [tsupport]
      exact hKP_closed.closure_subset_iff.mpr hη_supp_KP
    have hKP_Ω : KP ⊆ Ω := by
      intro y hy
      rcases hy with ⟨z, ⟨x, hx_supp, hxz⟩, hzy⟩
      have hxsrc : x ∈ (chartAt H α).source := hPOU_tsupp hx_supp
      have hx_ext : x ∈ (extChartAt I α).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I) (M := M)]; exact hxsrc
      have hz_target : z ∈ (extChartAt I α).target := by
        rw [← hxz]; exact (extChartAt I α).map_source hx_ext
      exact ⟨z, hz_target, hzy⟩
    exact hη_ts_KP.trans hKP_Ω
  have hv_smooth_Ω : ContDiffOn ℝ (⊤ : ℕ∞) v Ω := by
    rw [hv_def]
    exact chartPushedRaw_tensorChartComponentRaw_contDiffOn
      (I := I) (M := M) g r s T α Idx Jdx
  have hK_meas : MeasurableSet K :=
    (isClosed_tsupport η).measurableSet
  have hK_sub_Ω : K ⊆ Ω := hts_η_Ω
  have hpt_mul : ∀ m ≤ k, ∃ Km : ℝ, 0 ≤ Km ∧ ∀ y ∈ Ω,
      ‖iteratedFDeriv ℝ m (fun y : EuclN => η y * v y) y‖ ≤
        Km * (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
    intro m hm
    have hη_bound_m : ∀ l ≤ m, ∀ y ∈ Ω, ‖iteratedFDeriv ℝ l η y‖ ≤ Cη := by
      intro l hl y hy
      exact hη_bound y l (hl.trans hm)
    obtain ⟨Km, hKm_nn, hKm_bound⟩ :=
      norm_iteratedFDerivWithin_mul_le_of_bounded hΩ_open hCη_nn
        hη_smooth hη_bound_m hv_smooth_Ω
    refine ⟨Km, hKm_nn, ?_⟩
    intro y hy
    have hbound := hKm_bound y hy
    have hfc_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : EuclN => η y * v y) y :=
      hη_smooth.contDiffAt.mul (hv_smooth_Ω.contDiffAt (hΩ_open.mem_nhds hy))
    have h_within :
        iteratedFDerivWithin ℝ m (fun y : EuclN => η y * v y) Ω y =
          iteratedFDeriv ℝ m (fun y : EuclN => η y * v y) y := by
      exact iteratedFDerivWithin_eq_iteratedFDeriv hΩ_open.uniqueDiffOn
        (hfc_at.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞)))) hy
    have hv_within : ∀ l ≤ m,
        iteratedFDerivWithin ℝ l v Ω y = iteratedFDeriv ℝ l v y := by
      intro l hl
      exact iteratedFDerivWithin_eq_iteratedFDeriv hΩ_open.uniqueDiffOn
        (hv_smooth_Ω.contDiffAt (hΩ_open.mem_nhds hy) |>.of_le (by
          exact_mod_cast (le_top : (l : ℕ∞) ≤ (⊤ : ℕ∞)))) hy
    rw [← h_within]
    calc
      ‖iteratedFDerivWithin ℝ m (fun y : EuclN => η y * v y) Ω y‖
          ≤ Km * (∑ l ∈ Finset.range (m + 1),
              ‖iteratedFDerivWithin ℝ l v Ω y‖) := hbound
      _ = Km * (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
            have hsum_eq : (∑ l ∈ Finset.range (m + 1),
                  ‖iteratedFDerivWithin ℝ l v Ω y‖) =
                (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
              refine Finset.sum_congr rfl ?_
              intro l hl
              have hl' : l ≤ m := by
                rw [Finset.mem_range] at hl
                omega
              rw [hv_within l hl']
            rw [hsum_eq]
  have hper : ∀ (m : ℕ) (hm : m ≤ k), ∀ β : Fin m → Fin (Module.finrank ℝ E),
      eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
          (volume.restrict Ω) ≤
        ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * (hpt_mul m hm).choose) *
          (∑ l ∈ Finset.range (m + 1),
            eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
              (volume.restrict K)) := by
    intro m hm β
    let Km : ℝ := (hpt_mul m hm).choose
    have hKm_nn : 0 ≤ Km := (Classical.choose_spec (hpt_mul m hm)).1
    have hKm_bound : ∀ y ∈ Ω,
        ‖iteratedFDeriv ℝ m (fun y : EuclN => η y * v y) y‖ ≤
          Km * (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) :=
      (Classical.choose_spec (hpt_mul m hm)).2
    have hKm_eq : Km = (hpt_mul m hm).choose := rfl
    have hb := eLpNorm_iterWeakPartial_le_basis hΩ_open hf_smooth hf_cpt hf_sub β
    have hder_supp : Function.support (iteratedFDeriv ℝ m f) ⊆ K := by
      intro y hy
      exact hts_f_η ((tsupport_iteratedFDeriv_subset m)
        (subset_tsupport (iteratedFDeriv ℝ m f) hy))
    have hg_supp_K : Function.support (fun y : EuclN =>
        Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) ⊆ K := by
      intro y hy
      have hder : ‖iteratedFDeriv ℝ m f y‖ ≠ 0 := by
        by_contra hz
        exact hy (by simp [hz])
      exact hder_supp (by
        have hder0 : iteratedFDeriv ℝ m f y ≠ 0 := by
          intro hz
          exact hder (by simp [hz])
        simpa [Function.support] using hder0)
    have hrest : eLpNorm (fun y : EuclN =>
        Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) 2
          (volume.restrict Ω) =
        eLpNorm (fun y : EuclN =>
          Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) 2
          (volume.restrict K) := by
      have h := eLpNorm_restrict_eq_of_support_subset (p := 2) (μ := volume.restrict Ω)
        (s := K) hg_supp_K
      rw [← h]
      congr 1
      exact Measure.restrict_restrict_of_subset hK_sub_Ω
    have hpt : ∀ᵐ y ∂(volume.restrict K),
        Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖ ≤
          Real.sqrt (m + 1 : ℝ) * Km *
            (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
      rw [ae_restrict_iff' hK_meas]
      refine Filter.Eventually.of_forall ?_
      intro y hy
      have hyΩ : y ∈ Ω := hK_sub_Ω hy
      have hbound := hKm_bound y hyΩ
      rw [hf_eq]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)
    calc
      eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
          (volume.restrict Ω)
          ≤ eLpNorm (fun y : EuclN =>
              Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) 2
              (volume.restrict Ω) := hb
      _ = eLpNorm (fun y : EuclN =>
              Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) 2
              (volume.restrict K) := hrest
      _ ≤ eLpNorm (fun y : EuclN =>
              Real.sqrt (m + 1 : ℝ) * Km *
                (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖)) 2
              (volume.restrict K) := by
            have hpt' : ∀ᵐ y ∂(volume.restrict K),
                ‖(Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖ : ℝ)‖ ≤
                  ‖(Real.sqrt (m + 1 : ℝ) * Km *
                    (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) : ℝ)‖ := by
              filter_upwards [hpt] with y hy
              have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖ :=
                Finset.sum_nonneg (fun _ _ => norm_nonneg _)
              simpa [Real.norm_eq_abs, abs_mul,
                abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _),
                abs_of_nonneg hKm_nn, abs_of_nonneg hsum_nn] using hy
            exact eLpNorm_mono_ae hpt'
      _ ≤ ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Km) *
              (∑ l ∈ Finset.range (m + 1),
                eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                  (volume.restrict K)) := by
            have hconst := eLpNorm_const_smul (c := Real.sqrt (m + 1 : ℝ) * Km)
              (f := fun y : EuclN => ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖)
              (p := 2) (μ := volume.restrict K)
            have hcont_der : ∀ l : ℕ, ContinuousOn
                (fun y : EuclN => iteratedFDeriv ℝ l v y) Ω := by
              intro l
              have hw : ContinuousOn
                  (fun y : EuclN => iteratedFDerivWithin ℝ l v Ω y) Ω :=
                hv_smooth_Ω.continuousOn_iteratedFDerivWithin (m := l) (by
                  exact_mod_cast (le_top : (l : ℕ∞) ≤ (⊤ : ℕ∞)))
                  hΩ_open.uniqueDiffOn
              refine hw.congr ?_
              intro y hy
              have hcont_at : ContDiffAt ℝ l v y :=
                (hv_smooth_Ω.contDiffAt (hΩ_open.mem_nhds hy)).of_le (by
                  exact_mod_cast (le_top : (l : ℕ∞) ≤ (⊤ : ℕ∞)))
              exact (iteratedFDerivWithin_eq_iteratedFDeriv hΩ_open.uniqueDiffOn hcont_at hy).symm
            have hfs : ∀ i, i ∈ Finset.range (m + 1) → AEStronglyMeasurable
                (fun y : EuclN => ‖iteratedFDeriv ℝ i v y‖)
                (volume.restrict K) := by
              intro i hi
              exact ContinuousOn.aestronglyMeasurable
                ((hcont_der i).norm.mono (by intro y hy; exact hK_sub_Ω hy)) hK_meas
            have hsum := eLpNorm_sum_le
              (s := Finset.range (m + 1))
              (f := fun l => fun y : EuclN => ‖iteratedFDeriv ℝ l v y‖)
              hfs (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            have hc_nn : 0 ≤ Real.sqrt (m + 1 : ℝ) * Km :=
              mul_nonneg (Real.sqrt_nonneg _) hKm_nn
            have henorm : ‖(Real.sqrt (m + 1 : ℝ) * Km : ℝ)‖ₑ =
                ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Km) := by
              rw [← ofReal_norm_eq_enorm (Real.sqrt (m + 1 : ℝ) * Km)]
              congr 1
              rw [Real.norm_eq_abs, abs_of_nonneg hc_nn]
            calc
              eLpNorm (fun y : EuclN =>
                  (Real.sqrt (m + 1 : ℝ) * Km) *
                    (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖)) 2
                  (volume.restrict K)
                  = ‖(Real.sqrt (m + 1 : ℝ) * Km : ℝ)‖ₑ *
                      eLpNorm (fun y : EuclN =>
                        ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K) := by
                    change eLpNorm ((Real.sqrt (m + 1 : ℝ) * Km) •
                        (fun y : EuclN => ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖)) 2
                        (volume.restrict K) = _
                    exact hconst
              _ = ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Km) *
                      eLpNorm (fun y : EuclN =>
                        ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K) := by
                    rw [henorm]
              _ ≤ ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * (hpt_mul m hm).choose) *
                      (∑ l ∈ Finset.range (m + 1),
                        eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                          (volume.restrict K)) := by
                    rw [hKm_eq]
                    have hsum' : eLpNorm (fun y : EuclN =>
                          ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) 2
                          (volume.restrict K) ≤
                        ∑ l ∈ Finset.range (m + 1),
                          eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                            (volume.restrict K) := by
                      have hfun_eq : (∑ l ∈ Finset.range (m + 1),
                            fun y : EuclN => ‖iteratedFDeriv ℝ l v y‖) =
                          (fun y : EuclN =>
                            ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
                        funext y
                        simp [Finset.sum_apply]
                      rw [← hfun_eq]
                      exact hsum
                    exact mul_le_mul_of_nonneg_left hsum' (zero_le _)
  let Kmfun : (m : ℕ) → m ≤ k → ℝ := fun m hm => (hpt_mul m hm).choose
  have hKmfun_nn : ∀ m hm, 0 ≤ Kmfun m hm := fun m hm =>
    (hpt_mul m hm).choose_spec.1
  let hm_of_mem : ∀ m : ℕ, m ∈ Finset.range (k + 1) → m ≤ k :=
    fun m hm => by rw [Finset.mem_range] at hm; omega
  let C : ℝ := (Finset.range (k + 1)).attach.sum
    (fun ⟨m, hm⟩ =>
      (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ) *
        Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm))
  have hC_nn : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg (fun x hx => mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (hKmfun_nn x.1 (hm_of_mem x.1 x.2)))
  refine ⟨C, hC_nn, ?_⟩
  rw [wkpNorm_eq_sum]
  rw [← Finset.sum_attach]
  have hsum_bdd : (Finset.range (k + 1)).attach.sum
        (fun ⟨m, hm⟩ =>
          ∑ β : Fin m → Fin (Module.finrank ℝ E),
            eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
              (volume.restrict Ω)) ≤
      (Finset.range (k + 1)).attach.sum
        (fun ⟨m, hm⟩ =>
          (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
            ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm)) *
              (∑ l ∈ Finset.range (m + 1),
                eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                  (volume.restrict K))) := by
    refine Finset.sum_le_sum ?_
    intro ⟨m, hm⟩ _
    have hm_le : m ≤ k := by
      rw [Finset.mem_range] at hm
      omega
    calc
      (∑ β : Fin m → Fin (Module.finrank ℝ E),
          eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
            (volume.restrict Ω))
          ≤ (∑ β : Fin m → Fin (Module.finrank ℝ E),
              ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m hm_le) *
                (∑ l ∈ Finset.range (m + 1),
                  eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                    (volume.restrict K))) :=
            Finset.sum_le_sum (fun β _ => hper m hm_le β)
      _ = (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
              ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m hm_le) *
                (∑ l ∈ Finset.range (m + 1),
                  eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                    (volume.restrict K)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
  have hinner_le : ∀ (m : ℕ) (hm : m ∈ Finset.range (k + 1)),
      (∑ l ∈ Finset.range (m + 1),
        eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
          (volume.restrict K)) ≤
        (∑ l ∈ Finset.range (k + 1),
          eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
            (volume.restrict K)) := by
    intro m hm
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro l hl; exact Finset.mem_range.mpr (by
        rw [Finset.mem_range] at hl hm
        omega)) (fun _ _ _ => bot_le)
  have hweights_nn : ∀ (m : ℕ) (hm : m ∈ Finset.range (k + 1)),
      0 ≤ (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
        ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm)) := by
    intro m hm
    exact mul_nonneg (by positivity)
      (by positivity : 0 ≤ ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm)))
  calc
    (Finset.range (k + 1)).attach.sum
        (fun ⟨m, hm⟩ =>
          ∑ β : Fin m → Fin (Module.finrank ℝ E),
            eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
              (volume.restrict Ω))
        ≤ (Finset.range (k + 1)).attach.sum
            (fun ⟨m, hm⟩ =>
              (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm)) *
                  (∑ l ∈ Finset.range (m + 1),
                    eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                      (volume.restrict K))) := hsum_bdd
    _ ≤ (Finset.range (k + 1)).attach.sum
            (fun ⟨m, hm⟩ =>
              (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm))) *
          (∑ l ∈ Finset.range (k + 1),
            eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
              (volume.restrict K)) := by
          have hper : ∀ x ∈ (Finset.range (k + 1)).attach,
              (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                  ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                    (∑ l ∈ Finset.range (x.1 + 1),
                      eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K)) ≤
              (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                  ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                    (∑ l ∈ Finset.range (k + 1),
                      eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K)) := by
            intro x hx
            exact mul_le_mul_of_nonneg_left (hinner_le x.1 x.2) (hweights_nn x.1 x.2)
          calc
            (∑ x ∈ (Finset.range (k + 1)).attach,
              (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                  ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                    (∑ l ∈ Finset.range (x.1 + 1),
                      eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K)))
                ≤ (∑ x ∈ (Finset.range (k + 1)).attach,
                    (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                      ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                        (∑ l ∈ Finset.range (k + 1),
                          eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                            (volume.restrict K))) :=
                  Finset.sum_le_sum hper
            _ = (∑ x ∈ (Finset.range (k + 1)).attach,
                    (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                      ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2))) *
                  (∑ l ∈ Finset.range (k + 1),
                    eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                      (volume.restrict K)) := by
                  have hmul : (∑ x ∈ (Finset.range (k + 1)).attach,
                        (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                          ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1
                            (hm_of_mem x.1 x.2))) *
                      (∑ l ∈ Finset.range (k + 1),
                        eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                          (volume.restrict K)) =
                    (∑ x ∈ (Finset.range (k + 1)).attach,
                      (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                        ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                          (∑ l ∈ Finset.range (k + 1),
                            eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                              (volume.restrict K))) := by
                    exact Finset.sum_mul
                      (s := (Finset.range (k + 1)).attach)
                      (f := fun x : {m : ℕ // m ∈ Finset.range (k + 1)} =>
                        (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                          ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)))
                      (a := (∑ l ∈ Finset.range (k + 1),
                        eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                          (volume.restrict K)))
                  rw [← hmul]
    _ = ENNReal.ofReal C * (∑ l ∈ Finset.range (k + 1),
            eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
              (volume.restrict K)) := by
          congr 1
          have hsum_eq : (Finset.range (k + 1)).attach.sum
                (fun x : {m : ℕ // m ∈ Finset.range (k + 1)} =>
                  (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                    ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2))) =
              ENNReal.ofReal ((Finset.range (k + 1)).attach.sum
                (fun x : {m : ℕ // m ∈ Finset.range (k + 1)} =>
                  (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ) *
                    Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2))) := by
            rw [ENNReal.ofReal_sum_of_nonneg
              (s := (Finset.range (k + 1)).attach)
              (f := fun x : {m : ℕ // m ∈ Finset.range (k + 1)} =>
                (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ) *
                  Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2))
              (fun x hx => mul_nonneg
                (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
                (hKmfun_nn x.1 (hm_of_mem x.1 x.2)))]
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hnn : 0 ≤ Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2) :=
              mul_nonneg (Real.sqrt_nonneg _) (hKmfun_nn x.1 (hm_of_mem x.1 x.2))
            have hcard : (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) =
                ENNReal.ofReal (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ) := by
              exact (ENNReal.ofReal_natCast
                (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)))).symm
            rw [hcard]
            rw [← ENNReal.ofReal_mul (by positivity :
              0 ≤ (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ))]
            congr 1
            ring
          rw [hsum_eq]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPushedRaw_raw_eq_sum_transCoeffE_raw_on_pou_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ α : M) (P₀ : TensorCompIdx (E := E) r s)
    {x : M} (hx : x ∈ tsupport
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∩
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        ((toEuclidean (E := E)) (extChartAt I α x)) =
      ∑ Q : TensorCompIdx (E := E) r s,
        transCoeffE (I := I) (M := M) g r s γ α P₀ Q
            ((toEuclidean (E := E)) (extChartAt I γ x)) *
          chartPushedRaw (I := I) (M := M) γ
            (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)
            ((toEuclidean (E := E)) (extChartAt I γ x)) := by
  classical
  have hxγ : x ∈ (chartAt H γ).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) γ hx.1
  have hxα : x ∈ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) α hx.2
  have hx_ext_γ : x ∈ (extChartAt I γ).source := by
    rw [extChartAt_source (I := I)]; exact hxγ
  have hx_ext_α : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hxα
  have hL :
      chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
          ((toEuclidean (E := E)) (extChartAt I α x)) =
        tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2 x := by
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) α hxα)]
    congr 1
    rw [(toEuclidean (E := E)).symm_apply_apply, (extChartAt I α).left_inv hx_ext_α]
  have hsum := tensorChartComponentRaw_eq_transitionCoeff_sum
    (I := I) (M := M) g r s T γ α P₀ ⟨hxγ, hxα⟩
  have hQ : ∀ Q : TensorCompIdx (E := E) r s,
      transCoeffE (I := I) (M := M) g r s γ α P₀ Q
          ((toEuclidean (E := E)) (extChartAt I γ x)) *
        chartPushedRaw (I := I) (M := M) γ
          (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)
          ((toEuclidean (E := E)) (extChartAt I γ x)) =
        transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q x *
          tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2 x := by
    intro Q
    have hR :
        chartPushedRaw (I := I) (M := M) γ
            (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)
            ((toEuclidean (E := E)) (extChartAt I γ x)) =
          tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2 x := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) γ
        (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)
        (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) γ hxγ)]
      congr 1
      rw [(toEuclidean (E := E)).symm_apply_apply, (extChartAt I γ).left_inv hx_ext_γ]
    have htrans := transCoeffE_apply (I := I) (M := M) g r s γ α P₀ Q hxγ
    have hcutα : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) α hx.2
    have hcutγ : ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) γ hx.1
    have htrans_eq : transCoeffE (I := I) (M := M) g r s γ α P₀ Q
          ((toEuclidean (E := E)) (extChartAt I γ x)) =
        transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q x := by
      rw [htrans]
      rw [transportCoeffManifold_apply]
      rw [hcutα, hcutγ]
      ring
    rw [htrans_eq, hR]
  calc
    chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        ((toEuclidean (E := E)) (extChartAt I α x))
        = tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2 x := hL
    _ = ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2 x := hsum
    _ = ∑ Q : TensorCompIdx (E := E) r s,
          transCoeffE (I := I) (M := M) g r s γ α P₀ Q
              ((toEuclidean (E := E)) (extChartAt I γ x)) *
            chartPushedRaw (I := I) (M := M) γ
              (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)
              ((toEuclidean (E := E)) (extChartAt I γ x)) := by
      refine Finset.sum_congr rfl ?_
      intro Q _
      exact (hQ Q).symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tsupport_chartSmoothExt_pou_subset_chartImage
    (α : M) :
    tsupport (chartSmoothExt (I := I) (M := M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
        (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  classical
  set KP : Set EuclN := (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)))
    with hKP_def
  have hPOU_tsupp : tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) α
  have hη_supp_KP : Function.support (chartSmoothExt (I := I) (M := M) α
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆ KP := by
    intro y hy
    by_contra hyK
    apply hy
    by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
    · obtain ⟨z, hz_target, hzy⟩ := hy_target
      have hy_symm : (toEuclidean (E := E)).symm y = z := by
        rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
      have hval : chartSmoothExt (I := I) (M := M) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y =
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
        change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          else 0) = _
        rw [if_pos (by rw [hy_symm]; exact hz_target)]
      rw [hval]
      rw [hy_symm]
      by_contra hne
      apply hyK
      have hsymm_in_supp : (extChartAt I α).symm z ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        subset_tsupport _ (Function.mem_support.mpr hne)
      have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
        (extChartAt I α).right_inv hz_target
      refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_supp, hz_eq⟩, hzy⟩
    · change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        else 0) = 0
      rw [if_neg]
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
  have hKP_compact : IsCompact KP := by
    have hts_compact : IsCompact (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
      (isClosed_tsupport _).isCompact
    have hcont_ext : ContinuousOn (extChartAt I α) (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
      refine (continuousOn_extChartAt (I := I) α).mono ?_
      intro x hx
      have hxsrc : x ∈ (chartAt H α).source := hPOU_tsupp hx
      rw [← extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hxsrc
      exact hxsrc
    exact (hts_compact.image_of_continuousOn hcont_ext).image
      (toEuclidean (E := E)).continuous
  have hKP_closed : IsClosed KP := hKP_compact.isClosed
  rw [tsupport]
  rw [← Set.image_image]
  exact hKP_closed.closure_subset_iff.mpr hη_supp_KP

lemma eLpNorm_pou_weighted_raw_transition_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (γ α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α ∩
          tsupport (chartSmoothExt (I := I) (M := M) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
        ENNReal.ofReal (
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ‖iteratedFDeriv ℝ m (chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)) y‖ ^ 2)
        ∂(volume : Measure EuclN) ≤
      ENNReal.ofReal C * (∑ Q : TensorCompIdx (E := E) r s,
        ∑ m' ∈ Finset.range (m + 1),
          ∫⁻ z in chartTargetEuclid (I := I) (M := M) γ,
            ENNReal.ofReal (
              ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I γ).symm ((toEuclidean (E := E)).symm z)) *
              ‖iteratedFDeriv ℝ m' (chartPushedRaw (I := I) (M := M) γ
                (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)) z‖ ^ 2)
            ∂(volume : Measure EuclN)) := by
  classical
  set v_α : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α
    (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) with hvα_def
  set v_γ : (Q : TensorCompIdx (E := E) r s) → EuclN → ℝ := fun Q =>
    chartPushedRaw (I := I) (M := M) γ
      (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2) with hvγ_def
  set K_α : Set EuclN := tsupport (chartSmoothExt (I := I) (M := M) α
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) with hKα_def
  set K_M : Set M := tsupport
      ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∩
    tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKM_def
  have hKM_compact : IsCompact K_M :=
    (isClosed_tsupport _).isCompact.inter_right (isClosed_tsupport _)
  have hKM_in_γ : K_M ⊆ (chartAt H γ).source := fun x hx =>
    chartAtlasPOU_isSubordinate (I := I) (M := M) γ hx.1
  have hKM_in_α : K_M ⊆ (chartAt H α).source := fun x hx =>
    chartAtlasPOU_isSubordinate (I := I) (M := M) α hx.2
  obtain ⟨Ω_αγ, Ω_γα, hΩαγ_open, hΩγα_open, hΩαγ_subset_target,
      hΩγα_subset_target, hΩαγ_overlap, hΩγα_overlap, hKα_image_in_Ωαγ, Φ,
      hΦ_eq, hΦ_inv_eq⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M) α γ
      hKM_compact hKM_in_α hKM_in_γ m
  have hKα_sub_chartImage : K_α ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
        (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
    simpa [K_α] using tsupport_chartSmoothExt_pou_subset_chartImage
      (I := I) (M := M) α
  have hΩα_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have hKα_meas : MeasurableSet K_α :=
    (isClosed_tsupport _).measurableSet
  have hΩαγ_meas : MeasurableSet Ω_αγ := hΩαγ_open.measurableSet
  have hΩγα_meas : MeasurableSet Ω_γα := hΩγα_open.measurableSet
  have hPOUγ_le_one : ∀ x : M, (chartAtlasPOU I M γ : M → ℝ) x ≤ 1 :=
    fun x => (chartAtlasPOU I M).le_one γ x
  have hPOUγ_nn : ∀ x : M, 0 ≤ (chartAtlasPOU I M γ : M → ℝ) x :=
    fun x => (chartAtlasPOU I M).nonneg γ x
  have hF_supp : ∀ y, y ∈ chartTargetEuclid (I := I) (M := M) α ∩ K_α →
      ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ‖iteratedFDeriv ℝ m v_α y‖ ^ 2 ≠ 0 →
      y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_M := by
    intro y hy_dom hyF
    rcases hy_dom with ⟨hy_target, hyKα⟩
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have hy_target' : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      (show (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target from by
        simpa [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] using hy_target)
    have hPOUγ_ne : ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0 := by
      intro hz
      exact hyF (by simp [hz])
    have hx_tsuppγ : x ∈ tsupport
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ hPOUγ_ne
    have hx_tsuppα : x ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      rcases hKα_sub_chartImage hyKα with ⟨x', hx'_tsuppα, hxz⟩
      have hx'_eq : x' = x := by
        have hzx : (toEuclidean (E := E)) (extChartAt I α x') = y := hxz
        have hxx : (toEuclidean (E := E)) (extChartAt I α x) = y := by
          rw [hx_def, (extChartAt I α).right_inv hy_target']
          exact (toEuclidean (E := E)).apply_symm_apply y
        have hx'_src : x' ∈ (extChartAt I α).source := by
          have hx'_chart : x' ∈ (chartAt H α).source :=
            chartAtlasPOU_isSubordinate (I := I) (M := M) α hx'_tsuppα
          rw [← extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hx'_chart
          exact hx'_chart
        have hx_src : x ∈ (extChartAt I α).source :=
          (extChartAt I α).map_target hy_target'
        have hcoor_eq : (toEuclidean (E := E)) (extChartAt I α x') =
            (toEuclidean (E := E)) (extChartAt I α x) := by
          rw [hzx, hxx]
        have hcoord_eq : extChartAt I α x' = extChartAt I α x :=
          (toEuclidean (E := E)).injective hcoor_eq
        exact (extChartAt I α).injOn hx'_src hx_src hcoord_eq
      rw [← hx'_eq]
      exact hx'_tsuppα
    have hy_eq : y = (toEuclidean (E := E)) (extChartAt I α x) := by
      rw [hx_def, (extChartAt I α).right_inv hy_target']
      exact ((toEuclidean (E := E)).apply_symm_apply y).symm
    exact ⟨x, ⟨hx_tsuppγ, hx_tsuppα⟩, hy_eq.symm⟩
  set C : Set EuclN := (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_M
    with hC_def
  have hC_meas_top : MeasurableSet C := by
    have hcont : ContinuousOn (fun x : M =>
        (toEuclidean (E := E)) (extChartAt I α x)) K_M :=
      (toEuclidean (E := E)).continuous.comp_continuousOn
        ((continuousOn_extChartAt (I := I) α).mono (by
          intro x hx
          have hxsrc : x ∈ (chartAt H α).source := hKM_in_α hx
          rw [← extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hxsrc
          exact hxsrc))
    exact (hKM_compact.image_of_continuousOn hcont).isClosed.measurableSet
  have hC_sub_Ωαγ : C ⊆ Ω_αγ := by
    intro y hy
    exact hKα_image_in_Ωαγ (by simpa [C, hKM_def] using hy)
  have hLHS_le : (∫⁻ y in chartTargetEuclid (I := I) (M := M) α ∩ K_α,
        ENNReal.ofReal (
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ‖iteratedFDeriv ℝ m v_α y‖ ^ 2)
        ∂(volume : Measure EuclN)) ≤
      (∫⁻ y in Ω_αγ ∩ C,
        ENNReal.ofReal (
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ‖iteratedFDeriv ℝ m v_α y‖ ^ 2)
        ∂(volume : Measure EuclN)) := by
    set F : EuclN → ℝ≥0∞ := fun y =>
      ENNReal.ofReal (
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        ‖iteratedFDeriv ℝ m v_α y‖ ^ 2) with hF_def
    set A : Set EuclN := chartTargetEuclid (I := I) (M := M) α ∩ K_α with hA_def
    have hA_meas : MeasurableSet A := hΩα_meas.inter hKα_meas
    have hF_zero : ∀ y ∈ A, y ∉ C → F y = 0 := by
      intro y hyA hyC
      have hprod :
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              ‖iteratedFDeriv ℝ m v_α y‖ ^ 2 = 0 := by
        by_contra hne
        exact hyC (by simpa [C, A] using hF_supp y (by simpa [A] using hyA) hne)
      change ENNReal.ofReal (
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ‖iteratedFDeriv ℝ m v_α y‖ ^ 2) = 0
      rw [hprod, ENNReal.ofReal_zero]
    have h_step1 := lintegral_inter_eq_of_eq_zero_outside
      (volume : Measure EuclN) hA_meas hC_meas_top F hF_zero
    have hsubset : A ∩ C ⊆ Ω_αγ ∩ C := fun _ hy => ⟨hC_sub_Ωαγ hy.2, hy.2⟩
    calc
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α ∩ K_α,
          ENNReal.ofReal (
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ‖iteratedFDeriv ℝ m v_α y‖ ^ 2)
          ∂(volume : Measure EuclN)) = ∫⁻ y in A, F y ∂volume := by
        simp [A, F]
      _ = ∫⁻ y in A ∩ C, F y ∂volume := h_step1
      _ ≤ ∫⁻ y in Ω_αγ ∩ C, F y ∂volume := lintegral_mono_set hsubset
  set U : EuclN → ℝ := fun z =>
    ∑ Q : TensorCompIdx (E := E) r s,
      transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s γ α P₀ Q z * v_γ Q z
    with hU_def
  set K_E_γ : Set EuclN := (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K_M
    with hKEγ_def
  set Kchg : ℝ := (1 / Φ.jacobian_lower_bound) ^ (1 / (2 : ℝ≥0∞).toReal) with hKchg_def
  have hK_Eγ_compact : IsCompact K_E_γ := by
    have hcont : ContinuousOn (fun x : M =>
        (toEuclidean (E := E)) (extChartAt I γ x)) K_M :=
      (toEuclidean (E := E)).continuous.comp_continuousOn
        ((continuousOn_extChartAt (I := I) γ).mono (by
          intro x hx
          have hxsrc : x ∈ (chartAt H γ).source := hKM_in_γ hx
          rw [← extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hxsrc
          exact hxsrc))
    simpa [K_E_γ] using hKM_compact.image_of_continuousOn hcont
  have hΦC_eq : Φ.toFun '' C = K_E_γ := by
    ext z
    constructor
    · rintro ⟨y, hyC, hyz⟩
      rcases hyC with ⟨x, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      have hyΩ : (toEuclidean (E := E)) (extChartAt I α x) ∈ Ω_αγ :=
        hKα_image_in_Ωαγ ⟨x, hxK, rfl⟩
      have hΦy : Φ.toFun ((toEuclidean (E := E)) (extChartAt I α x)) =
          chartTransitionEuclid (I := I) (M := M) α γ
            ((toEuclidean (E := E)) (extChartAt I α x)) :=
        hΦ_eq _ hyΩ
      calc
        (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) x
            = (toEuclidean (E := E)) (extChartAt I γ x) := rfl
        _ = chartTransitionEuclid (I := I) (M := M) α γ
              ((toEuclidean (E := E)) (extChartAt I α x)) :=
              (chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α γ (hKM_in_α hxK)).symm
        _ = Φ.toFun ((toEuclidean (E := E)) (extChartAt I α x)) := hΦy.symm
        _ = Φ.toFun y := by
              exact congrArg Φ.toFun (by simpa using hxy)
        _ = z := hyz
    · rintro ⟨x, hxK, hxz⟩
      refine ⟨(toEuclidean (E := E)) (extChartAt I α x), ⟨x, hxK, rfl⟩, ?_⟩
      have hyΩ : (toEuclidean (E := E)) (extChartAt I α x) ∈ Ω_αγ :=
        hKα_image_in_Ωαγ ⟨x, hxK, rfl⟩
      have hΦy : Φ.toFun ((toEuclidean (E := E)) (extChartAt I α x)) =
          chartTransitionEuclid (I := I) (M := M) α γ
            ((toEuclidean (E := E)) (extChartAt I α x)) :=
        hΦ_eq _ hyΩ
      calc
        Φ.toFun ((toEuclidean (E := E)) (extChartAt I α x))
            = chartTransitionEuclid (I := I) (M := M) α γ
                ((toEuclidean (E := E)) (extChartAt I α x)) := hΦy
        _ = (toEuclidean (E := E)) (extChartAt I γ x) :=
              chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α γ (hKM_in_α hxK)
        _ = z := by simpa using hxz
  have hK_Eγ_sub_Ωγα : K_E_γ ⊆ Ω_γα := by
    rw [← hΦC_eq]
    intro z hz
    rcases hz with ⟨y, hyC, hyz⟩
    rw [← hyz]
    exact Φ.bijOn.mapsTo (hC_sub_Ωαγ hyC)
  have hK_Eγ_sub_overlap_E : K_E_γ ⊆ chartOverlapEuclid (I := I) (M := M) γ α := by
    intro z hz
    rcases hz with ⟨x, hxK, hxz⟩
    refine ⟨extChartAt I γ x,
      ⟨x, ⟨hKM_in_γ hxK, hKM_in_α hxK⟩, rfl⟩, hxz⟩
  obtain ⟨C_tr, hC_tr_nn, hC_tr_bound⟩ :=
    uniform_iteratedFDeriv_bound_on_compact_of_contDiffOn
      (Ω := chartOverlapEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid_isOpen (I := I) (M := M) γ α)
      hK_Eγ_compact hK_Eγ_sub_overlap_E (m + 1)
      (fun Q => transitionCoeffOnEuclid_contDiffOn_overlap
        (E := E) (I := I) (M := M) r s γ α P₀ Q)
  have h_coeff_cd : ∀ Q, ContDiffOn ℝ (⊤ : ℕ∞)
      (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s γ α P₀ Q) Ω_γα := fun Q =>
    (transitionCoeffOnEuclid_contDiffOn_overlap
      (E := E) (I := I) (M := M) r s γ α P₀ Q).mono hΩγα_overlap
  have h_vγ_cd : ∀ Q, ContDiffOn ℝ (⊤ : ℕ∞) (v_γ Q) Ω_γα := fun Q => by
    rw [hvγ_def]
    exact (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I)
      (M := M) g r s T γ Q.1 Q.2).mono
      hΩγα_subset_target
  have hU_cd : ContDiffOn ℝ (⊤ : ℕ∞) U Ω_γα := by
    rw [hU_def]
    exact ContDiffOn.sum (s := Finset.univ) (fun Q _ =>
      (h_coeff_cd Q).mul (h_vγ_cd Q))
  have h_vα_cd : ContDiffOn ℝ (⊤ : ℕ∞) v_α Ω_αγ := by
    rw [hvα_def]
    exact (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I)
      (M := M) g r s T α P₀.1 P₀.2).mono
      hΩαγ_subset_target
  have h_coeff_bdd : ∀ Q, ∀ j ≤ m, ∀ z ∈ K_E_γ,
      ‖iteratedFDeriv ℝ j (transitionCoeffOnEuclid (E := E) (I := I)
        (M := M) r s γ α P₀ Q) z‖ ≤ C_tr := by
    intro Q j hj z hz
    have hj' : j ≤ m + 1 := by omega
    exact hC_tr_bound Q j hj' z hz
  obtain ⟨K_mul, hK_mul_nn, hK_mul_bound⟩ :=
    norm_iteratedFDeriv_sum_mul_le_of_bounded (Ω := Ω_γα) hΩγα_open
      (K := K_E_γ) hK_Eγ_sub_Ωγα m hC_tr_nn h_coeff_cd h_coeff_bdd h_vγ_cd
  have h_mul : ∀ z ∈ K_E_γ, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i U z‖ ≤
        K_mul * (∑ Q : TensorCompIdx (E := E) r s,
          ∑ j ∈ Finset.range (i + 1), ‖iteratedFDeriv ℝ j (v_γ Q) z‖) := by
    intro z hz i hi
    have hb := hK_mul_bound z hz i hi
    simpa [U, hU_def] using hb
  have h_id : ∀ y ∈ Ω_αγ, v_α y = U (Φ.toFun y) := by
    intro y hy
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hΩαγ_subset_target hy
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) α γ := hΩαγ_overlap hy
    rcases hy_overlap with ⟨w, ⟨z, hz_in, hzw⟩, hwy⟩
    have hy_eq2 : y = (toEuclidean (E := E)) (extChartAt I α z) := by
      rw [← hwy, ← hzw]
    have hz_extchart : z ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]
      exact hz_in.1
    have hz_eq_x : z = x := by
      rw [hx_def, hy_eq2, (toEuclidean (E := E)).symm_apply_apply,
        (extChartAt I α).left_inv hz_extchart]
    have hxα : x ∈ (chartAt H α).source := hz_eq_x ▸ hz_in.1
    have hxγ : x ∈ (chartAt H γ).source := hz_eq_x ▸ hz_in.2
    have hy_eq_x : y = (toEuclidean (E := E)) (extChartAt I α x) := by
      rw [← hz_eq_x]
      exact hy_eq2
    have hx_ext_α : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]
      exact hxα
    have hx_ext_γ : x ∈ (extChartAt I γ).source := by
      rw [extChartAt_source (I := I)]
      exact hxγ
    have hΦy : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I γ x) := by
      rw [hΦ_eq y hy, hy_eq_x]
      exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α γ hxα
    have h_vα : v_α y = tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2 x := by
      calc
        v_α y = chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) y := by
              rw [hvα_def]
        _ = tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
              rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
        _ = tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2 x := by
              rfl
    have h_vγ : ∀ Q, v_γ Q (Φ.toFun y) =
        tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2 x := by
      intro Q
      have hz_target : Φ.toFun y ∈ chartTargetEuclid (I := I) (M := M) γ :=
        hΩγα_subset_target (Φ.bijOn.mapsTo hy)
      calc
        v_γ Q (Φ.toFun y) = chartPushedRaw (I := I) (M := M) γ
            (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2) (Φ.toFun y) := by
              rw [hvγ_def]
        _ = tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2
              ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) := by
              rw [chartPushedRaw_apply_of_mem (I := I) (M := M) γ _ hz_target]
        _ = tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2 x := by
              congr 1
              rw [hΦy, (toEuclidean (E := E)).symm_apply_apply]
              exact (extChartAt I γ).left_inv hx_ext_γ
    have h_cQ : ∀ Q, transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s γ α P₀ Q (Φ.toFun y) =
        transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q x := by
      intro Q
      rw [transitionCoeffOnEuclid_def, hΦy, (toEuclidean (E := E)).symm_apply_apply]
      congr 1
      exact (extChartAt I γ).left_inv hx_ext_γ
    have hsum := tensorChartComponentRaw_eq_transitionCoeff_sum
      (I := I) (M := M) g r s T γ α P₀ ⟨hxγ, hxα⟩
    calc
      v_α y = tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2 x := h_vα
      _ = ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2 x := hsum
      _ = ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s γ α P₀ Q (Φ.toFun y) *
              v_γ Q (Φ.toFun y) := by
            refine Finset.sum_congr rfl ?_
            intro Q _
            rw [h_cQ Q, h_vγ Q]
      _ = U (Φ.toFun y) := by rw [hU_def]
  have h_deriv : ∀ y ∈ Ω_αγ, iteratedFDeriv ℝ m v_α y =
      iteratedFDerivWithin ℝ m (fun y => U (Φ.toFun y)) Ω_αγ y := by
    intro y hy
    rw [← iteratedFDerivWithin_of_isOpen m hΩαγ_open hy]
    exact iteratedFDerivWithin_congr (fun x hx => h_id x hx) hy m
  have h_chain : ∀ y ∈ Ω_αγ, ‖iteratedFDeriv ℝ m v_α y‖ ≤
      m.factorial *
        (∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i U (Φ.toFun y)‖) *
        Φ.derivBoundMaxOne ^ m := by
    intro y hy
    rw [h_deriv y hy]
    let Cv : ℝ := ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i U (Φ.toFun y)‖
    have hC : ∀ i, i ≤ m → ‖iteratedFDerivWithin ℝ i U Ω_γα (Φ.toFun y)‖ ≤ Cv := by
      intro i hi
      rw [iteratedFDerivWithin_of_isOpen i hΩγα_open (Φ.bijOn.mapsTo hy)]
      dsimp [Cv]
      exact Finset.single_le_sum
        (f := fun l => ‖iteratedFDeriv ℝ l U (Φ.toFun y)‖)
        (fun l _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact norm_iteratedFDerivWithin_comp_contDiffOn_le Φ hΩαγ_open hΩγα_open hU_cd
      le_rfl hy hC
  set K_pw : ℝ := m.factorial * (m + 1 : ℝ) * K_mul * Φ.derivBoundMaxOne ^ m with hK_pw_def
  have hK_pw_nn : 0 ≤ K_pw := by
    dsimp [K_pw]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK_mul_nn)
      (pow_nonneg Φ.derivBoundMaxOne_pos.le m)
  have h_pw : ∀ y ∈ Ω_αγ ∩ C, ‖iteratedFDeriv ℝ m v_α y‖ ≤
      K_pw * (∑ Q : TensorCompIdx (E := E) r s,
        ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖) := by
    intro y hy
    rcases hy with ⟨hyΩ, hyC⟩
    have h_z : Φ.toFun y ∈ K_E_γ := by
      rw [← hΦC_eq]
      exact mem_image_of_mem Φ.toFun hyC
    set S : ℝ := ∑ Q : TensorCompIdx (E := E) r s,
      ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖
    have hstep : ∀ i ∈ Finset.range (m + 1),
        ‖iteratedFDeriv ℝ i U (Φ.toFun y)‖ ≤ K_mul * S := by
      intro i hi
      have hi' : i ≤ m := by
        rw [Finset.mem_range] at hi
        omega
      have hb := h_mul (Φ.toFun y) h_z i hi'
      refine hb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK_mul_nn
      refine Finset.sum_le_sum ?_
      intro Q _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega)) (fun j _ _ => norm_nonneg _)
    have h_sum_i : (∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i U (Φ.toFun y)‖) ≤
        (m + 1 : ℝ) * K_mul * S := by
      calc
        (∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i U (Φ.toFun y)‖)
            ≤ ∑ i ∈ Finset.range (m + 1), K_mul * S := Finset.sum_le_sum hstep
        _ = (m + 1 : ℝ) * (K_mul * S) := by
              simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = (m + 1 : ℝ) * K_mul * S := by ring
    have h_chain_at := h_chain y hyΩ
    calc
      ‖iteratedFDeriv ℝ m v_α y‖
          ≤ m.factorial * (∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i U (Φ.toFun y)‖) *
              Φ.derivBoundMaxOne ^ m := h_chain_at
      _ ≤ m.factorial * ((m + 1 : ℝ) * K_mul * S) * Φ.derivBoundMaxOne ^ m := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_sum_i (by positivity : 0 ≤ (m.factorial : ℝ)))
              (pow_nonneg Φ.derivBoundMaxOne_pos.le m)
      _ = m.factorial * (m + 1 : ℝ) * K_mul * Φ.derivBoundMaxOne ^ m * S := by ring
      _ = K_pw * S := by rw [hK_pw_def]
  set N_terms : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * (m + 1 : ℝ)
    with hN_def
  have hN_nn : 0 ≤ N_terms := by
    dsimp [N_terms]
    positivity
  have h_sq : ∀ y ∈ Ω_αγ ∩ C, ‖iteratedFDeriv ℝ m v_α y‖ ^ 2 ≤
      K_pw ^ 2 * N_terms * (∑ Q : TensorCompIdx (E := E) r s,
        ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) := by
    intro y hy
    have hb := h_pw y hy
    set S : ℝ := ∑ Q : TensorCompIdx (E := E) r s,
      ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖
    set S2 : ℝ := ∑ Q : TensorCompIdx (E := E) r s,
      ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun Q _ =>
      Finset.sum_nonneg (fun j _ => norm_nonneg _))
    have hS2_nn : 0 ≤ S2 := Finset.sum_nonneg (fun Q _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have h_inner : ∀ Q, (∑ j ∈ Finset.range (m + 1),
          ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖) ^ 2 ≤
        (m + 1 : ℝ) * (∑ j ∈ Finset.range (m + 1),
          ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) := by
      intro Q
      simpa [Finset.card_range] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1))
          (f := fun j => ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖))
    have h_outer : S ^ 2 ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * (m + 1 : ℝ) * S2 := by
      calc
        S ^ 2 ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
              (∑ Q, (∑ j ∈ Finset.range (m + 1),
                ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖) ^ 2) := by
              simpa [S] using
                (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
                  (f := fun Q => ∑ j ∈ Finset.range (m + 1),
                    ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖))
        _ ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
              (∑ Q, (m + 1 : ℝ) * (∑ j ∈ Finset.range (m + 1),
                ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact Finset.sum_le_sum (fun Q _ => h_inner Q)
        _ = (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * (m + 1 : ℝ) * S2 := by
              have h_pull :
                  (∑ Q : TensorCompIdx (E := E) r s,
                    (m + 1 : ℝ) * (∑ j ∈ Finset.range (m + 1),
                      ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2)) =
                    (m + 1 : ℝ) * (∑ Q : TensorCompIdx (E := E) r s,
                      ∑ j ∈ Finset.range (m + 1),
                        ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) :=
                (Finset.mul_sum (Finset.univ)
                  (fun Q => ∑ j ∈ Finset.range (m + 1),
                    ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) (m + 1 : ℝ)).symm
              rw [h_pull]
              ring
    have hsq' : ‖iteratedFDeriv ℝ m v_α y‖ ^ 2 ≤ (K_pw * S) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hb 2
    calc
      ‖iteratedFDeriv ℝ m v_α y‖ ^ 2 ≤ (K_pw * S) ^ 2 := hsq'
      _ = K_pw ^ 2 * S ^ 2 := by ring
      _ ≤ K_pw ^ 2 * ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * (m + 1 : ℝ) * S2) := by
            exact mul_le_mul_of_nonneg_left h_outer (sq_nonneg _)
      _ = K_pw ^ 2 * N_terms * S2 := by rw [hN_def]; ring
  have h_pou_comp : ∀ y ∈ Ω_αγ,
      ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) := by
    intro y hy
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hΩαγ_subset_target hy
    have hy_target' : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      (show (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target from by
        simpa [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] using hy_target)
    have hxα : x ∈ (chartAt H α).source := by
      have hx_src : x ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy_target'
      rwa [extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hx_src
    have hxγ : x ∈ (chartAt H γ).source := by
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) α γ := hΩαγ_overlap hy
      rcases hy_overlap with ⟨w, ⟨z, hz_in, hzw⟩, hwy⟩
      have hy_eq2 : y = (toEuclidean (E := E)) (extChartAt I α z) := by
        rw [← hwy, ← hzw]
      have hz_extchart : z ∈ (extChartAt I α).source := by
        rw [extChartAt_source (I := I)]
        exact hz_in.1
      have hz_eq_x : z = x := by
        rw [hx_def, hy_eq2, (toEuclidean (E := E)).symm_apply_apply,
          (extChartAt I α).left_inv hz_extchart]
      exact hz_eq_x ▸ hz_in.2
    have hx_ext_α : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]
      exact hxα
    have hx_ext_γ : x ∈ (extChartAt I γ).source := by
      rw [extChartAt_source (I := I)]
      exact hxγ
    have hΦy : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I γ x) := by
      rw [hΦ_eq y hy]
      have hy_eq_x : y = (toEuclidean (E := E)) (extChartAt I α x) := by
        rw [hx_def, (extChartAt I α).right_inv hy_target']
        exact ((toEuclidean (E := E)).apply_symm_apply y).symm
      rw [hy_eq_x]
      exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α γ hxα
    congr 1
    rw [hΦy, (toEuclidean (E := E)).symm_apply_apply]
    exact ((extChartAt I γ).left_inv hx_ext_γ).symm
  have h_pt : ∀ y ∈ Ω_αγ ∩ C, pouWeightedF0 (I := I) (M := M) g r s T γ α P₀ m y ≤
      ENNReal.ofReal (K_pw ^ 2 * N_terms) * pouWeightedG (I := I) (M := M) g r s T γ m
        (Φ.toFun y) := by
    intro y hy
    rcases hy with ⟨hyΩ, hyC⟩
    have hsqy := h_sq y ⟨hyΩ, hyC⟩
    have hpou := h_pou_comp y hyΩ
    have h_dist : ∀ (POU : ℝ), POU * (∑ Q : TensorCompIdx (E := E) r s,
          ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) =
        ∑ Q : TensorCompIdx (E := E) r s, ∑ j ∈ Finset.range (m + 1),
          POU * ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2 := by
      intro POU
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro Q _
      rw [Finset.mul_sum]
    have hreal : ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ‖iteratedFDeriv ℝ m v_α y‖ ^ 2 ≤
        (K_pw ^ 2 * N_terms) * (∑ Q : TensorCompIdx (E := E) r s,
          ∑ j ∈ Finset.range (m + 1),
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) *
            ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) := by
      calc
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ‖iteratedFDeriv ℝ m v_α y‖ ^ 2
            ≤ ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
                (K_pw ^ 2 * N_terms * (∑ Q : TensorCompIdx (E := E) r s,
                  ∑ j ∈ Finset.range (m + 1),
                    ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2)) := by
              exact mul_le_mul_of_nonneg_left hsqy (hPOUγ_nn
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        _ = (K_pw ^ 2 * N_terms) * (((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              (∑ Q : TensorCompIdx (E := E) r s,
                ∑ j ∈ Finset.range (m + 1),
                  ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2)) := by
              ring
        _ = (K_pw ^ 2 * N_terms) * (∑ Q : TensorCompIdx (E := E) r s,
              ∑ j ∈ Finset.range (m + 1),
                ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
                ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) := by
              rw [h_dist]
        _ = (K_pw ^ 2 * N_terms) * (∑ Q : TensorCompIdx (E := E) r s,
              ∑ j ∈ Finset.range (m + 1),
                ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) *
                ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) := by
              rw [hpou]
    have h_ofReal_sum :
        ENNReal.ofReal (∑ Q : TensorCompIdx (E := E) r s,
            ∑ j ∈ Finset.range (m + 1),
              ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) *
              ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) =
          ∑ Q : TensorCompIdx (E := E) r s, ∑ j ∈ Finset.range (m + 1),
            ENNReal.ofReal (
              ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) *
              ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun Q => ∑ j ∈ Finset.range (m + 1),
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) *
          ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2)
        (fun Q _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hPOUγ_nn
          ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y)))) (sq_nonneg _)))]
      refine Finset.sum_congr rfl ?_
      intro Q _
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.range (m + 1))
        (f := fun j =>
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) *
          ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2)
        (fun j _ => mul_nonneg (hPOUγ_nn
          ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y)))) (sq_nonneg _))]
    calc
      pouWeightedF0 (I := I) (M := M) g r s T γ α P₀ m y ≤ ENNReal.ofReal (
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ‖iteratedFDeriv ℝ m v_α y‖ ^ 2) := by
            simp [pouWeightedF0, hvα_def]
      _ ≤ ENNReal.ofReal ((K_pw ^ 2 * N_terms) * (∑ Q : TensorCompIdx (E := E) r s,
            ∑ j ∈ Finset.range (m + 1),
              ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) *
              ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2)) :=
            ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (K_pw ^ 2 * N_terms) *
            ENNReal.ofReal (∑ Q : TensorCompIdx (E := E) r s,
              ∑ j ∈ Finset.range (m + 1),
                ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) *
                ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2) := by
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ K_pw ^ 2 * N_terms)]
      _ = ENNReal.ofReal (K_pw ^ 2 * N_terms) * (∑ Q : TensorCompIdx (E := E) r s,
            ∑ j ∈ Finset.range (m + 1),
              ENNReal.ofReal (
                ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I γ).symm ((toEuclidean (E := E)).symm (Φ.toFun y))) *
                ‖iteratedFDeriv ℝ j (v_γ Q) (Φ.toFun y)‖ ^ 2)) := by
            rw [h_ofReal_sum]
      _ = ENNReal.ofReal (K_pw ^ 2 * N_terms) * pouWeightedG (I := I) (M := M) g r s T γ m
        (Φ.toFun y) := by
            simp only [pouWeightedG, hvγ_def, pouWeightedIntegrand, pouCoordValue,
              rawChartFderivNorm]
  have h_main : (∫⁻ y in Ω_αγ ∩ C, pouWeightedF0 (I := I) (M := M) g r s T γ α P₀ m y ∂volume) ≤
      ENNReal.ofReal (K_pw ^ 2 * N_terms * Kchg ^ 2) *
        pouWeightedSum (I := I) (M := M) g r s T γ m
          (chartTargetEuclid (I := I) (M := M) γ) := by
    have h_meas := pouWeightedIntegrand_comp_aemeasurable
      (I := I) (M := M) g r s T γ m hΩαγ_meas hΩγα_open
        hΩγα_subset_target Φ (by simpa only [v_γ] using h_vγ_cd)
    have hraw := lintegral_pouWeightedF0_le
      (I := I) (M := M) g r s T γ α P₀ m hΩαγ_open hC_meas_top
        hΩγα_subset_target Φ (ENNReal.ofReal (K_pw ^ 2 * N_terms))
        ENNReal.ofReal_ne_top h_pt h_meas
    have h_jac_inv : Kchg ^ 2 = 1 / Φ.jacobian_lower_bound := by
      dsimp [Kchg]
      rw [← Real.rpow_natCast, ← Real.rpow_mul
        (div_nonneg (by norm_num) Φ.jacobian_lower_bound_pos.le)]
      norm_num
    have hK_prod : ENNReal.ofReal (K_pw ^ 2 * N_terms) * ENNReal.ofReal (Kchg ^ 2) =
        ENNReal.ofReal (K_pw ^ 2 * N_terms * Kchg ^ 2) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hN_nn)]
    rw [← h_jac_inv, hK_prod] at hraw
    exact hraw
  refine ⟨K_pw ^ 2 * N_terms * Kchg ^ 2, ?_, ?_⟩
  · positivity
  · calc
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α ∩ K_α,
          ENNReal.ofReal (
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ‖iteratedFDeriv ℝ m v_α y‖ ^ 2)
          ∂(volume : Measure EuclN)) ≤ ∫⁻ y in Ω_αγ ∩ C,
            pouWeightedF0 (I := I) (M := M) g r s T γ α P₀ m y ∂volume := by
            simpa [pouWeightedF0] using hLHS_le
      _ ≤ ENNReal.ofReal (K_pw ^ 2 * N_terms * Kchg ^ 2) *
            pouWeightedSum (I := I) (M := M) g r s T γ m
              (chartTargetEuclid (I := I) (M := M) γ) :=
            h_main
      _ = ENNReal.ofReal (K_pw ^ 2 * N_terms * Kchg ^ 2) *
            (∑ Q : TensorCompIdx (E := E) r s,
              ∑ j ∈ Finset.range (m + 1),
                ∫⁻ z in chartTargetEuclid (I := I) (M := M) γ,
                  pouWeightedIntegrand (I := I) (M := M) g r s T γ Q j z ∂volume) := by
            simp only [pouWeightedSum]
      _ = ENNReal.ofReal (K_pw ^ 2 * N_terms * Kchg ^ 2) *
            (∑ Q : TensorCompIdx (E := E) r s,
              ∑ m' ∈ Finset.range (m + 1),
                ∫⁻ z in chartTargetEuclid (I := I) (M := M) γ,
                  ENNReal.ofReal (
                    ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                      ((extChartAt I γ).symm ((toEuclidean (E := E)).symm z)) *
                    ‖iteratedFDeriv ℝ m' (chartPushedRaw (I := I) (M := M) γ
                      (tensorChartComponentRaw (I := I) (M := M) g r s T γ Q.1 Q.2)) z‖ ^ 2)
                  ∂(volume : Measure EuclN)) := by
            simp only [pouWeightedIntegrand, pouCoordValue, rawChartFderivNorm]
end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
