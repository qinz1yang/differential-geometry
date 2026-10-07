import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartCovCore_O35
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# CH12-O35 chartCov (model norms): both directions on a compact chart set

`F_j := tensor0SModelInChart (s+j) c (∇^j T)`, `V := target ∩ symm⁻¹ W`.
* `chartCovModel_O35` (chartCov-A, `[FROZEN] CH12-O35 chartCov`): `‖D^{k'} F_0‖ ≤ C Σ_{i≤k} ‖F_i‖`.
* `chartCovModelRev_O35` (chartCov-A', reverse; for S80's `hchart`): `‖F_j‖ ≤ C Σ_{i≤j} ‖D^i F_0‖`.
Both from the formula `D F_j = curryLeft F_{j+1} + B(Γ, F_j)` (`fderiv_iter_model_O35`) and the
bilinear Leibniz bound; constants are uniform in `T`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
theorem isOpen_chartSet_O35 (c : M) {W : Set M} (hW : IsOpen W) :
    IsOpen ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) :=
  (continuousOn_extChartAt_symm c).isOpen_inter_preimage (isOpen_extChartAt_target c) hW

omit [T2Space M] in
/-- The Levi-Civita connection endomorphism is smooth on the chart target. -/
theorem contDiffOn_connChart_O35 (g : SmoothRiemannianMetric I M) (c : M) :
    ContDiffOn ℝ ∞ (connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) c)
      (extChartAt I c).target := by
  intro y hy
  have h := connectionEndomorphismInChartL_contDiffWithinAt (leviCivitaConnectionOfMetric g)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g) c hy
  rw [I.range_eq_univ, contDiffWithinAt_univ] at h
  exact h.contDiffWithinAt

omit [T2Space M] in
/-- Uniform bounds for the chart jets of `Γ` on a compact subset of the target. -/
theorem connChart_bound_O35 (g : SmoothRiemannianMetric I M) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ k, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ i (connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) c) y‖
        ≤ B := by
  induction k with
  | zero =>
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      (f := fun y => ‖iteratedFDeriv ℝ 0
        (connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) c) y‖)
      (fun y hy => by
        have h := ((contDiffOn_connChart_O35 g c).contDiffAt
          ((isOpen_extChartAt_target c).mem_nhds (hKt hy))).iteratedFDeriv_right
          (m := 0) (i := 0) (by simp)
        exact h.continuousAt.norm.continuousWithinAt)
    refine ⟨max B 0, le_max_right _ _, fun i hi y hy => ?_⟩
    obtain rfl : i = 0 := by omega
    exact ((le_abs_self _).trans (hB y hy)).trans (le_max_left _ _)
  | succ k ih =>
    obtain ⟨B₀, hB₀, hB⟩ := ih
    obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn
      (f := fun y => ‖iteratedFDeriv ℝ (k + 1)
        (connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) c) y‖)
      (fun y hy => by
        have h := ((contDiffOn_connChart_O35 g c).contDiffAt
          ((isOpen_extChartAt_target c).mem_nhds (hKt hy))).iteratedFDeriv_right
          (m := 0) (i := k + 1) (by simp)
        exact h.continuousAt.norm.continuousWithinAt)
    refine ⟨max B₀ B₁, hB₀.trans (le_max_left _ _), fun i hi y hy => ?_⟩
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact (hB i (by omega) y hy).trans (le_max_left _ _)
    · obtain rfl : i = k + 1 := by omega
      exact ((le_abs_self _).trans (hB₁ y hy)).trans (le_max_right _ _)

/-- **One step** (both directions) of the fixed-chart jet comparison, within `V`. -/
theorem iter_step_O35 (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : (p : M) → Tensor0SSpace s I p) (c : M) {W : Set M} (hW : IsOpen W)
    (hT : ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W)
    {y : E} (hy : y ∈ (extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) (j k : ℕ) :
    haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
    let V := (extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W
    let F : (j : ℕ) → E → Tensor0SModel (s + j) ℝ E := fun j =>
      tensor0SModelInChart (s + j) c (iteratedMetricCovariantDerivative g s T j)
    let Γ := connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) c
    let R := ‖corrBilin_O35 (E := E) (s + j)‖ * ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i Γ V y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (F j) V y‖
    ‖iteratedFDerivWithin ℝ (k + 1) (F j) V y‖ ≤ ‖iteratedFDerivWithin ℝ k (F (j + 1)) V y‖ + R ∧
      ‖iteratedFDerivWithin ℝ k (F (j + 1)) V y‖ ≤ ‖iteratedFDerivWithin ℝ (k + 1) (F j) V y‖ + R := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro V F Γ R
  have hV : IsOpen V := isOpen_chartSet_O35 c hW
  have hU : UniqueDiffOn ℝ V := hV.uniqueDiffOn
  have hF : ∀ j, ContDiffOn ℝ ∞ (F j) V := fun j z hz =>
    (contDiffAt_iter_model_O35 g s T c hW hT hz.1 hz.2 j).contDiffWithinAt
  have hΓ : ContDiffOn ℝ ∞ Γ V := (contDiffOn_connChart_O35 g c).mono inter_subset_left
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + j + 1) => E) ℝ
  let Bt : E → (E →L[ℝ] Tensor0SModel (s + j) ℝ E) := fun z =>
    corrBilin_O35 (E := E) (s + j) (Γ z) (F j z)
  have hL : ContDiffOn ℝ ∞ (⇑L ∘ F (j + 1)) V :=
    L.toContinuousLinearEquiv.contDiff.comp_contDiffOn (hF (j + 1))
  have hB : ContDiffOn ℝ ∞ Bt V :=
    ((corrBilin_O35 (E := E) (s + j)).contDiff.comp_contDiffOn hΓ).clm_apply (hF j)
  have heq : EqOn (fderivWithin ℝ (F j) V) ((⇑L ∘ F (j + 1)) + Bt) V := fun z hz => by
    rw [fderivWithin_of_isOpen hV hz]
    exact fderiv_iter_model_O35 g s T c hW hT hz.1 hz.2 j
  have hsplit : iteratedFDerivWithin ℝ k (fderivWithin ℝ (F j) V) V y =
      iteratedFDerivWithin ℝ k (⇑L ∘ F (j + 1)) V y + iteratedFDerivWithin ℝ k Bt V y := by
    rw [iteratedFDerivWithin_congr heq hy k]
    exact iteratedFDerivWithin_add_apply (hL.of_le (by exact_mod_cast le_top) y hy)
      (hB.of_le (by exact_mod_cast le_top) y hy) hU hy
  have h1 : ‖iteratedFDerivWithin ℝ (k + 1) (F j) V y‖ =
      ‖iteratedFDerivWithin ℝ k (fderivWithin ℝ (F j) V) V y‖ :=
    (norm_iteratedFDerivWithin_fderivWithin hU hy).symm
  have h2 : ‖iteratedFDerivWithin ℝ k (⇑L ∘ F (j + 1)) V y‖ =
      ‖iteratedFDerivWithin ℝ k (F (j + 1)) V y‖ :=
    L.norm_iteratedFDerivWithin_comp_left _ hU hy k
  have h3 : ‖iteratedFDerivWithin ℝ k Bt V y‖ ≤ R :=
    (corrBilin_O35 (E := E) (s + j)).norm_iteratedFDerivWithin_le_of_bilinear hΓ (hF j) hU hy
      (by exact_mod_cast le_top)
  rw [h1, hsplit]
  constructor
  · exact (norm_add_le _ _).trans (by rw [h2]; linarith)
  · have := norm_sub_le (iteratedFDerivWithin ℝ k (⇑L ∘ F (j + 1)) V y +
      iteratedFDerivWithin ℝ k Bt V y) (iteratedFDerivWithin ℝ k Bt V y)
    rw [add_sub_cancel_right, h2] at this
    linarith

omit [FiniteDimensional ℝ E] in
theorem sum_shift_le_O35 (N : ℕ → ℝ) (hN : ∀ n, 0 ≤ N n) (j k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), N (j + 1 + i) ≤ ∑ i ∈ Finset.range (k + 1 + 1), N (j + i) := by
  rw [Finset.sum_range_succ' (fun i => N (j + i)) (k + 1)]
  have : ∑ i ∈ Finset.range (k + 1), N (j + 1 + i) = ∑ i ∈ Finset.range (k + 1), N (j + (i + 1)) :=
    Finset.sum_congr rfl (fun i _ => by rw [show j + 1 + i = j + (i + 1) by omega])
  rw [this]
  exact le_add_of_nonneg_right (hN _)

omit [FiniteDimensional ℝ E] in
theorem sum_mono_O35 (N : ℕ → ℝ) (hN : ∀ n, 0 ≤ N n) {a b : ℕ} (h : a ≤ b) :
    ∑ i ∈ Finset.range a, N i ≤ ∑ i ∈ Finset.range b, N i :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => hN i)

/-- chartCov-A, within `V`, for all base orders `j` (induction on `k`). -/
theorem chartCovModel_within_O35 (g : SmoothRiemannianMetric I M) (c : M) {W : Set M}
    (hW : IsOpen W) {K : Set E} (hK : IsCompact K)
    (hKW : K ⊆ (extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) (s k : ℕ) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ T : (p : M) → Tensor0SSpace s I p,
      ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W →
      ∀ y ∈ K, ∀ k' ≤ k,
        ‖iteratedFDerivWithin ℝ k' (tensor0SModelInChart (s + j) c
          (iteratedMetricCovariantDerivative g s T j))
          ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ ≤
        C * ∑ i ∈ Finset.range (k + 1), ‖tensor0SModelInChart (s + (j + i)) c
          (iteratedMetricCovariantDerivative g s T (j + i)) y‖ := by
  have hV := isOpen_chartSet_O35 (I := I) c hW
  induction k with
  | zero =>
    intro j
    refine ⟨1, zero_le_one, fun T hT y hy k' hk' => ?_⟩
    obtain rfl : k' = 0 := by omega
    rw [norm_iteratedFDerivWithin_zero, Finset.sum_range_one, one_mul]
    exact le_rfl
  | succ k ih =>
    intro j
    obtain ⟨C₁, hC₁, h₁⟩ := ih j
    obtain ⟨C₂, hC₂, h₂⟩ := ih (j + 1)
    obtain ⟨MΓ, hMΓ, hΓ⟩ := connChart_bound_O35 g c hK (fun y hy => (hKW hy).1) k
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    set b := ‖corrBilin_O35 (E := E) (s + j)‖
    refine ⟨C₁ + C₂ + b * MΓ * C₁ * 2 ^ k, by positivity, fun T hT y hy k' hk' => ?_⟩
    set N : ℕ → ℝ := fun n => ‖tensor0SModelInChart (s + n) c
      (iteratedMetricCovariantDerivative g s T n) y‖ with hNdef
    have hN : ∀ n, 0 ≤ N n := fun n => norm_nonneg _
    have hS : ∑ i ∈ Finset.range (k + 1), N (j + i) ≤ ∑ i ∈ Finset.range (k + 1 + 1), N (j + i) :=
      sum_mono_O35 (fun i => N (j + i)) (fun i => hN _) (by omega)
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), N (j + i) :=
      Finset.sum_nonneg (fun i _ => hN _)
    rcases Nat.lt_or_ge k' (k + 1) with hlt | hge
    · have := h₁ T hT y hy k' (by omega)
      calc _ ≤ C₁ * ∑ i ∈ Finset.range (k + 1), N (j + i) := this
        _ ≤ C₁ * ∑ i ∈ Finset.range (k + 1 + 1), N (j + i) := by gcongr
        _ ≤ _ := by
          gcongr
          have : 0 ≤ b * MΓ * C₁ * 2 ^ k := by positivity
          linarith
    · obtain rfl : k' = k + 1 := by omega
      have hstep := (iter_step_O35 g s T c hW hT (hKW hy) j k).1
      simp only at hstep
      have hA := h₂ T hT y hy k le_rfl
      have hA' : ∑ i ∈ Finset.range (k + 1), N (j + 1 + i) ≤
          ∑ i ∈ Finset.range (k + 1 + 1), N (j + i) := sum_shift_le_O35 N hN j k
      have hR : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (connectionEndomorphismInChartL
            (leviCivitaConnectionOfMetric g) c)
            ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (tensor0SModelInChart (s + j) c
            (iteratedMetricCovariantDerivative g s T j))
            ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ ≤
          ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            (MΓ * (C₁ * ∑ i ∈ Finset.range (k + 1), N (j + i))) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [mul_assoc]
        gcongr
        · rw [iteratedFDerivWithin_of_isOpen i hV (hKW hy)]
          exact hΓ i (by simp at hi; omega) y hy
        · exact h₁ T hT y hy (k - i) (by omega)
      rw [← Finset.sum_mul] at hR
      have hch : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [hch] at hR
      have hb : 0 ≤ b := norm_nonneg _
      have e1 : C₂ * ∑ i ∈ Finset.range (k + 1), N (j + 1 + i) ≤
          C₂ * ∑ i ∈ Finset.range (k + 1 + 1), N (j + i) := by gcongr
      have e2 : b * (2 ^ k * (MΓ * (C₁ * ∑ i ∈ Finset.range (k + 1), N (j + i)))) ≤
          b * MΓ * C₁ * 2 ^ k * ∑ i ∈ Finset.range (k + 1 + 1), N (j + i) := by
        have : b * (2 ^ k * (MΓ * (C₁ * ∑ i ∈ Finset.range (k + 1), N (j + i)))) =
            b * MΓ * C₁ * 2 ^ k * ∑ i ∈ Finset.range (k + 1), N (j + i) := by ring
        rw [this]; gcongr
      have e3 : 0 ≤ C₁ * ∑ i ∈ Finset.range (k + 1 + 1), N (j + i) :=
        mul_nonneg hC₁ (hS0.trans hS)
      have hbR := mul_le_mul_of_nonneg_left hR hb
      calc _ ≤ _ := hstep
        _ ≤ C₂ * ∑ i ∈ Finset.range (k + 1), N (j + 1 + i) +
            b * (2 ^ k * (MΓ * (C₁ * ∑ i ∈ Finset.range (k + 1), N (j + i)))) := add_le_add hA hbR
        _ ≤ _ := by nlinarith

/-- **chartCov-A** (`[FROZEN] CH12-O35 chartCov`): coordinate jets of a tensor field in a fixed
chart are bounded, on a compact chart set, by its covariant jets (model norms); `C` uniform in `T`. -/
theorem chartCovModel_O35 (g : SmoothRiemannianMetric I M) (c : M) {W : Set M} (hW : IsOpen W)
    {K : Set E} (hK : IsCompact K)
    (hKW : K ⊆ (extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : (p : M) → Tensor0SSpace s I p,
      ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W →
      ∀ y ∈ K, ∀ k' ≤ k, ‖iteratedFDeriv ℝ k' (tensor0SModelInChart s c T) y‖ ≤
        C * ∑ i ∈ Finset.range (k + 1),
          ‖tensor0SModelInChart (s + i) c (iteratedMetricCovariantDerivative g s T i) y‖ := by
  obtain ⟨C, hC, h⟩ := chartCovModel_within_O35 g c hW hK hKW s k 0
  refine ⟨C, hC, fun T hT y hy k' hk' => ?_⟩
  have h0 := h T hT y hy k' hk'
  rw [iteratedFDerivWithin_of_isOpen k' (isOpen_chartSet_O35 c hW) (hKW hy)] at h0
  refine h0.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.zero_add]

/-- chartCov-A' within `V` (reverse direction, induction on the covariant order `j`). -/
theorem chartCovModelRev_within_O35 (g : SmoothRiemannianMetric I M) (c : M) {W : Set M}
    (hW : IsOpen W) {K : Set E} (hK : IsCompact K)
    (hKW : K ⊆ (extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) (s j : ℕ) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ T : (p : M) → Tensor0SSpace s I p,
      ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W →
      ∀ y ∈ K,
        ‖iteratedFDerivWithin ℝ k (tensor0SModelInChart (s + j) c
          (iteratedMetricCovariantDerivative g s T j))
          ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ ≤
        C * ∑ i ∈ Finset.range (j + k + 1), ‖iteratedFDerivWithin ℝ i
          (tensor0SModelInChart (s + 0) c (iteratedMetricCovariantDerivative g s T 0))
          ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ := by
  have hV := isOpen_chartSet_O35 (I := I) c hW
  induction j with
  | zero =>
    intro k
    refine ⟨1, zero_le_one, fun T hT y hy => ?_⟩
    rw [one_mul]
    exact Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i
      (tensor0SModelInChart (s + 0) c (iteratedMetricCovariantDerivative g s T 0))
      ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  | succ j ih =>
    intro k
    choose Cf hCf0 hCf using ih
    obtain ⟨MΓ, hMΓ, hΓ⟩ := connChart_bound_O35 g c hK (fun y hy => (hKW hy).1) k
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    set b := ‖corrBilin_O35 (E := E) (s + j)‖
    set A := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cf (k - i)
    have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hCf0 _))
    refine ⟨Cf (k + 1) + b * MΓ * A,
      add_nonneg (hCf0 _) (mul_nonneg (mul_nonneg (norm_nonneg _) hMΓ) hA0),
      fun T hT y hy => ?_⟩
    set G : ℕ → ℝ := fun n => ‖iteratedFDerivWithin ℝ n
      (tensor0SModelInChart (s + 0) c (iteratedMetricCovariantDerivative g s T 0))
      ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ with hGdef
    have hG : ∀ n, 0 ≤ G n := fun n => norm_nonneg _
    set S := ∑ i ∈ Finset.range (j + 1 + k + 1), G i
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => hG i)
    have hstep := (iter_step_O35 g s T c hW hT (hKW hy) j k).2
    simp only at hstep
    have h1 : ‖iteratedFDerivWithin ℝ (k + 1) (tensor0SModelInChart (s + j) c
        (iteratedMetricCovariantDerivative g s T j))
        ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ ≤ Cf (k + 1) * S := by
      refine (hCf (k + 1) T hT y hy).trans (le_of_eq ?_)
      rw [show j + (k + 1) + 1 = j + 1 + k + 1 by omega]
    have hR : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (connectionEndomorphismInChartL
          (leviCivitaConnectionOfMetric g) c)
          ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (tensor0SModelInChart (s + j) c
          (iteratedMetricCovariantDerivative g s T j))
          ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ ≤
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cf (k - i) * (MΓ * S) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hi' : i ≤ k := by simp at hi; omega
      have hΓi : ‖iteratedFDerivWithin ℝ i (connectionEndomorphismInChartL
          (leviCivitaConnectionOfMetric g) c)
          ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ ≤ MΓ := by
        rw [iteratedFDerivWithin_of_isOpen i hV (hKW hy)]
        exact hΓ i hi' y hy
      have hFi := (hCf (k - i) T hT y hy).trans
        (mul_le_mul_of_nonneg_left (sum_mono_O35 G hG (show j + (k - i) + 1 ≤ j + 1 + k + 1 by omega))
          (hCf0 _))
      have hc : (0 : ℝ) ≤ k.choose i := by positivity
      calc (k.choose i : ℝ) * _ * _ ≤ (k.choose i : ℝ) * MΓ * (Cf (k - i) * S) := by gcongr
        _ = _ := by ring
    rw [← Finset.sum_mul] at hR
    have hb : 0 ≤ b := norm_nonneg _
    have hbR := mul_le_mul_of_nonneg_left hR hb
    calc _ ≤ _ := hstep
      _ ≤ Cf (k + 1) * S + b * (A * (MΓ * S)) := add_le_add h1 hbR
      _ = _ := by ring

/-- **chartCov-A'** (reverse direction; covariant jets ≤ coordinate jets, model norms). -/
theorem chartCovModelRev_O35 (g : SmoothRiemannianMetric I M) (c : M) {W : Set M}
    (hW : IsOpen W) {K : Set E} (hK : IsCompact K)
    (hKW : K ⊆ (extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) (s j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : (p : M) → Tensor0SSpace s I p,
      ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W →
      ∀ y ∈ K, ‖tensor0SModelInChart (s + j) c (iteratedMetricCovariantDerivative g s T j) y‖ ≤
        C * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i (tensor0SModelInChart s c T) y‖ := by
  obtain ⟨C, hC, h⟩ := chartCovModelRev_within_O35 g c hW hK hKW s j 0
  refine ⟨C, hC, fun T hT y hy => ?_⟩
  have h0 := h T hT y hy
  rw [norm_iteratedFDerivWithin_zero] at h0
  refine h0.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [iteratedFDerivWithin_of_isOpen i (isOpen_chartSet_O35 c hW) (hKW hy)]
  rfl

end GC.LongTime.Ch12
