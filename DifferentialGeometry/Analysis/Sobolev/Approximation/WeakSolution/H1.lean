import DifferentialGeometry.Analysis.Sobolev.Solutions.SmoothSequence
import DifferentialGeometry.Analysis.Sobolev.Solutions.WeakSolution
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Mollification
import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.WeakDerivative

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.BoundedSmoothSolutionSequence

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma contDiff_mollifyEps_of_memLp_two
    {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu : MemLp u 2 (volume : Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyEps (d := d) hε u) :=
  mollifyEps_contDiff hε (hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))

private lemma is_smooth_weak_solution_mollifyEps
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : MemLp u 2 (volume : Measure E))
    {ε : ℝ} (hε : 0 < ε) :
    B.IsSmoothWeakSolution
      (mollifyEps (d := d) hε u)
      (B.classicalApply (mollifyEps (d := d) hε u)) :=
  SmoothEllipticBilinearForm.mollifyEps_isSmoothWeakSolution_classicalApply
    (d := d) hΩ B (hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hε

omit [NeZero d] in
private lemma memLp_two_restrict_of_memLp_two
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E)) (S : Set E) :
    MemLp f 2 (volume.restrict S) :=
  hf.restrict S

omit [NeZero d] in
private lemma integral_sq_le_eLpNorm_sq
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E))
    {S : Set E} :
    ∫ x in S, (f x) ^ 2 ∂(volume : Measure E) ≤
      ((eLpNorm f 2 (volume : Measure E)).toReal) ^ 2 := by
  classical
  have hf_sq_int : Integrable (fun x => (f x) ^ 2) (volume : Measure E) := by
    have h_norm_eq : ∀ x : E, (f x) ^ 2 = ‖f x‖ ^ (2 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]
    have h_funeq : (fun x : E => (f x) ^ 2) = (fun x : E => ‖f x‖ ^ (2 : ℝ)) := by
      funext x; exact h_norm_eq x
    rw [h_funeq]
    have := hf.integrable_norm_rpow (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    simpa using this
  have h_int_le_E :
      ∫ x in S, (f x) ^ 2 ∂(volume : Measure E) ≤
      ∫ x, (f x) ^ 2 ∂(volume : Measure E) := by
    refine integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hf_sq_int
  have h_int_E : ∫ x, (f x) ^ 2 ∂(volume : Measure E) =
      ((eLpNorm f 2 (volume : Measure E)).toReal) ^ 2 := by
    have h_norm_eq : ∀ x : E, (f x) ^ 2 = ‖f x‖ ^ (2 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]
    have h_funeq_int : ∫ x, (f x) ^ 2 ∂(volume : Measure E) =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure E) := by
      refine integral_congr_ae ?_
      filter_upwards with x using h_norm_eq x
    rw [h_funeq_int]
    have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h_2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have h_eLp := hf.eLpNorm_eq_integral_rpow_norm h_2_ne_zero h_2_ne_top
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal] at h_eLp
    have h_int_nn : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure E) :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have h_pow_nn : 0 ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure E)) ^ ((2 : ℝ)⁻¹) :=
      Real.rpow_nonneg h_int_nn _
    have hh : (eLpNorm f 2 (volume : Measure E)).toReal =
        (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure E)) ^ ((2 : ℝ)⁻¹) := by
      rw [h_eLp]
      exact ENNReal.toReal_ofReal h_pow_nn
    rw [hh]
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul h_int_nn]
    norm_num
  rw [h_int_E] at h_int_le_E
  exact h_int_le_E

theorem exists_mollification
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Set.univ)
    {ε : ℕ → ℝ} (hε_pos : ∀ n, 0 < ε n) (hε_zero : Tendsto ε atTop (𝓝 0))
    {M : ℝ} (hM_nn : 0 ≤ M)
    (hM_bound : ∀ n,
      eLpNorm (B.classicalApply (mollifyEps (d := d) (hε_pos n) u))
        2 (volume : Measure E) ≤ ENNReal.ofReal M) :
    ∃ S : BoundedSmoothSolutionSequence B,
      S.uSeq = (fun n => mollifyEps (d := d) (hε_pos n) u) ∧
      S.fSeq = (fun n => B.classicalApply (S.uSeq n)) ∧
      Tendsto (fun n => eLpNorm (fun x => S.uSeq n x - u x)
        2 (volume : Measure E)) atTop (𝓝 0) ∧
      ∀ j : Fin d,
        Tendsto (fun n => eLpNorm (fun x =>
          (fderiv ℝ (S.uSeq n) x) (EuclideanSpace.single j 1) - hu.weakGrad x j)
          2 (volume : Measure E)) atTop (𝓝 0) := by
  classical
  have hu_l2 : MemLp u 2 (volume : Measure E) := by
    simpa only [Measure.restrict_univ] using hu.memLp
  have hpartial_l2 : ∀ j : Fin d,
      MemLp (fun x => hu.weakGrad x j) 2 (volume : Measure E) := by
    intro j
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp j
  let uSeq : ℕ → E → ℝ := fun n => mollifyEps (d := d) (hε_pos n) u
  let fSeq : ℕ → E → ℝ := fun n => B.classicalApply (uSeq n)
  have huSeq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n) := fun n =>
    contDiff_mollifyEps_of_memLp_two (hε_pos n) hu_l2
  have h_smooth_weak : ∀ n, B.IsSmoothWeakSolution (uSeq n) (fSeq n) := fun n =>
    is_smooth_weak_solution_mollifyEps hΩ B hu_l2 (hε_pos n)
  have huSeq_l2 : ∀ n, MemLp (uSeq n) 2 (volume : Measure E) := fun n => by
    have h_eLp : eLpNorm (uSeq n) 2 (volume : Measure E) ≤
        eLpNorm u 2 (volume : Measure E) :=
      eLpNorm_mollifyEps_le (hε_pos n) hu_l2
    exact lt_of_le_of_lt h_eLp hu_l2.eLpNorm_lt_top
  have hgrad_l2 : ∀ n, ∀ j : Fin d, MemLp
      (fun x : E => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single j 1))
      2 (volume : Measure E) := fun n j => by
    have h_eLp : eLpNorm
        (fun x : E => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single j 1)) 2
        (volume : Measure E) ≤
      eLpNorm (fun x => hu.weakGrad x j) 2 (volume : Measure E) :=
      eLpNorm_partial_mollifyEps_le_of_weakPartial_univ (hε_pos n)
        (hu_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
        (hpartial_l2 j) (hu.isWeakGrad j)
    exact lt_of_le_of_lt h_eLp (hpartial_l2 j).eLpNorm_lt_top
  have hfSeq_l2 : ∀ n, MemLp (fSeq n) 2 (volume : Measure E) := fun n =>
    lt_of_le_of_lt (hM_bound n) ENNReal.ofReal_lt_top
  set DB : ℝ :=
    ((eLpNorm u 2 (volume : Measure E)).toReal) ^ 2 +
      (∑ j : Fin d,
        ((eLpNorm (fun x => hu.weakGrad x j) 2 (volume : Measure E)).toReal) ^ 2) +
      M ^ 2 with hDB_def
  have hDB_nn : 0 ≤ DB := by
    refine add_nonneg (add_nonneg (sq_nonneg _) ?_) (sq_nonneg _)
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hf_seq_l2_local : ∀ n, ∀ {S : Set E}, IsCompact (closure S) →
      MemLp (fSeq n) 2 (volume.restrict S) := fun n {S} _ =>
    memLp_two_restrict_of_memLp_two (hfSeq_l2 n) S
  have hu_seq_l2_local : ∀ n, ∀ {S : Set E}, IsCompact (closure S) →
      MemLp (uSeq n) 2 (volume.restrict S) := fun n {S} _ =>
    memLp_two_restrict_of_memLp_two (huSeq_l2 n) S
  have hgrad_seq_l2_local : ∀ n, ∀ {S : Set E}, IsCompact (closure S) →
      ∀ j : Fin d, MemLp
        (fun y : E => (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))
        2 (volume.restrict S) := fun n {S} _ j =>
    memLp_two_restrict_of_memLp_two (hgrad_l2 n j) S
  refine ⟨{
    uSeq := uSeq
    fSeq := fSeq
    u_seq_smooth := huSeq_smooth
    is_smooth_weak_solution := h_smooth_weak
    f_seq_l2_local := hf_seq_l2_local
    u_seq_l2_local := hu_seq_l2_local
    grad_seq_l2_local := hgrad_seq_l2_local
    dataBound := DB
    data_bound_nn := hDB_nn
    data_integrated_bound := ?_
  }, rfl, rfl, ?_, ?_⟩
  · intro Ω' _ _
    refine ⟨1, by norm_num, fun n => ?_⟩
    have h_grad_each : ∀ j : Fin d,
        ∫ y in Ω', ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E) ≤
        ((eLpNorm (fun x => hu.weakGrad x j) 2 (volume : Measure E)).toReal) ^ 2 := by
      intro j
      have h_partial_bound := integral_sq_le_eLpNorm_sq (S := Ω') (hgrad_l2 n j)
      refine h_partial_bound.trans ?_
      have h_eLp_bound :
          eLpNorm (fun x : E => (fderiv ℝ (uSeq n) x)
              (EuclideanSpace.single j 1)) 2 (volume : Measure E) ≤
          eLpNorm (fun x => hu.weakGrad x j) 2 (volume : Measure E) :=
        eLpNorm_partial_mollifyEps_le_of_weakPartial_univ (hε_pos n)
          (hu_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
          (hpartial_l2 j) (hu.isWeakGrad j)
      have h_lhs_top : eLpNorm (fun x : E => (fderiv ℝ (uSeq n) x)
          (EuclideanSpace.single j 1)) 2 (volume : Measure E) ≠ ∞ :=
        (hgrad_l2 n j).eLpNorm_ne_top
      have h_rhs_top : eLpNorm (fun x => hu.weakGrad x j) 2 (volume : Measure E) ≠ ∞ :=
        (hpartial_l2 j).eLpNorm_ne_top
      have h_toReal_le := (ENNReal.toReal_le_toReal h_lhs_top h_rhs_top).mpr h_eLp_bound
      have h_lhs_nn : 0 ≤ (eLpNorm (fun x : E => (fderiv ℝ (uSeq n) x)
          (EuclideanSpace.single j 1)) 2 (volume : Measure E)).toReal :=
        ENNReal.toReal_nonneg
      exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
    have h_u_bound :
        ∫ y in Ω', (uSeq n y) ^ 2 ∂(volume : Measure E) ≤
        ((eLpNorm u 2 (volume : Measure E)).toReal) ^ 2 := by
      refine (integral_sq_le_eLpNorm_sq (S := Ω') (huSeq_l2 n)).trans ?_
      have h_eLp_bound : eLpNorm (uSeq n) 2 (volume : Measure E) ≤
          eLpNorm u 2 (volume : Measure E) :=
        eLpNorm_mollifyEps_le (hε_pos n) hu_l2
      have h_lhs_top : eLpNorm (uSeq n) 2 (volume : Measure E) ≠ ∞ :=
        (huSeq_l2 n).eLpNorm_ne_top
      have h_rhs_top : eLpNorm u 2 (volume : Measure E) ≠ ∞ :=
        hu_l2.eLpNorm_ne_top
      have h_toReal_le := (ENNReal.toReal_le_toReal h_lhs_top h_rhs_top).mpr h_eLp_bound
      have h_lhs_nn : 0 ≤ (eLpNorm (uSeq n) 2 (volume : Measure E)).toReal :=
        ENNReal.toReal_nonneg
      exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
    have h_f_bound :
        ∫ y in Ω', (fSeq n y) ^ 2 ∂(volume : Measure E) ≤
        M ^ 2 := by
      refine (integral_sq_le_eLpNorm_sq (S := Ω') (hfSeq_l2 n)).trans ?_
      have h_eLp_bound : eLpNorm (fSeq n) 2 (volume : Measure E) ≤
          ENNReal.ofReal M := hM_bound n
      have h_lhs_top : eLpNorm (fSeq n) 2 (volume : Measure E) ≠ ∞ :=
        (hfSeq_l2 n).eLpNorm_ne_top
      have h_rhs_top : ENNReal.ofReal M ≠ ∞ := ENNReal.ofReal_ne_top
      have h_toReal_le :
          (eLpNorm (fSeq n) 2 (volume : Measure E)).toReal ≤
            (ENNReal.ofReal M).toReal :=
        (ENNReal.toReal_le_toReal h_lhs_top h_rhs_top).mpr h_eLp_bound
      rw [ENNReal.toReal_ofReal hM_nn] at h_toReal_le
      have h_lhs_nn : 0 ≤ (eLpNorm (fSeq n) 2 (volume : Measure E)).toReal :=
        ENNReal.toReal_nonneg
      exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
    have h_grad_sum_int :
        ∫ y in Ω', ∑ j : Fin d,
            ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E) =
        ∑ j : Fin d, ∫ y in Ω',
            ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E) := by
      refine integral_finsetSum (μ := (volume : Measure E).restrict Ω') Finset.univ ?_
      intro j _
      have h_norm_eq : ∀ y : E,
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2 =
          ‖((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))‖ ^ (2 : ℝ) := by
        intro y
        rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]
      have h_funeq : (fun y : E =>
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2) =
          (fun y : E =>
          ‖((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))‖ ^ (2 : ℝ)) := by
        funext y; exact h_norm_eq y
      rw [h_funeq]
      have h_int_E : Integrable (fun y : E =>
          ‖((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))‖ ^ (2 : ℝ))
          (volume : Measure E) := by
        have := (hgrad_l2 n j).integrable_norm_rpow
          (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        simpa using this
      exact h_int_E.restrict
    rw [h_grad_sum_int]
    have h_grad_sum_le :
        ∑ j : Fin d, ∫ y in Ω',
            ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E) ≤
        ∑ j : Fin d, ((eLpNorm (fun x => hu.weakGrad x j) 2 (volume : Measure E)).toReal) ^ 2 :=
      Finset.sum_le_sum (fun j _ => h_grad_each j)
    have h_combined :
        (∑ j : Fin d, ∫ y in Ω',
            ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E)) +
        (∫ y in Ω', (uSeq n y) ^ 2 ∂(volume : Measure E)) +
        (∫ y in Ω', (fSeq n y) ^ 2 ∂(volume : Measure E)) ≤
        (∑ j : Fin d, ((eLpNorm (fun x => hu.weakGrad x j) 2 (volume : Measure E)).toReal) ^ 2) +
        ((eLpNorm u 2 (volume : Measure E)).toReal) ^ 2 +
        M ^ 2 := by
      linarith
    refine h_combined.trans ?_
    rw [hDB_def]
    rw [one_mul]
    linarith
  · exact Euclidean.tendsto_eLpNorm_mollifyEps_sub_of_memLp hu_l2 hε_pos hε_zero
  · intro j
    exact Euclidean.tendsto_eLpNorm_partial_mollifyEps_sub_weakGrad hu hε_pos hε_zero j

end DifferentialGeometry.Analysis.Sobolev.BoundedSmoothSolutionSequence
