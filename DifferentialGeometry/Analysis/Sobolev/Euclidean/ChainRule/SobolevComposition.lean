import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.DerivativeBounds
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
import Mathlib.Data.Nat.Choose.Bounds

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

theorem SmoothDiffeoBoundedAtOrder.eLpNorm_comp_toFun_le_const
    {d kmax : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    eLpNorm (fun x => f (Φ.toFun x)) p (volume.restrict Ω) ≤
      ENNReal.ofReal
          ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
        eLpNorm f p (volume.restrict Ω') := by
  classical
  have hp_zero : p ≠ 0 := by
    intro hpz; rw [hpz] at hp_one
    exact absurd hp_one (by norm_num)
  set q := p.toReal with hq_def
  have hq_pos : 0 < q := ENNReal.toReal_pos hp_zero hp_top
  have hjLB_pos : 0 < Φ.jacobianLowerBound := Φ.jacobian_lower_bound_pos
  by_cases hf : AEStronglyMeasurable f (volume.restrict Ω')
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos (one_div_pos.mpr hjLB_pos) _)))]
    exact le_top
  have hcomp : AEStronglyMeasurable (fun x => f (Φ.toFun x)) (volume.restrict Ω) :=
    hf.comp_quasiMeasurePreserving Φ.toFun_quasiMeasurePreserving
  have hjLB_ne_top : ENNReal.ofReal Φ.jacobianLowerBound ≠ ⊤ := ENNReal.ofReal_ne_top
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  have hint_le :
      ENNReal.ofReal Φ.jacobianLowerBound *
          ∫⁻ x, ‖f (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) ≤
        ∫⁻ x,
          ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * ‖f (Φ.toFun x)‖ₑ ^ q
            ∂(volume.restrict Ω) := by
    rw [← MeasureTheory.lintegral_const_mul' _ _ hjLB_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    rw [MeasureTheory.ae_restrict_iff' hΩ_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have h_le : ENNReal.ofReal Φ.jacobianLowerBound ≤
        ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| :=
      ENNReal.ofReal_le_ofReal (Φ.jacobian_lower x hx)
    exact mul_le_mul_of_nonneg_right h_le (zero_le)
  have hchg := Φ.lintegral_image_eq hΩ (fun y => ‖f y‖ₑ ^ q)
  have hint_le' :
      ENNReal.ofReal Φ.jacobianLowerBound *
          ∫⁻ x, ‖f (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) ≤
        ∫⁻ y, ‖f y‖ₑ ^ q ∂(volume.restrict Ω') := by
    rw [hchg]; exact hint_le
  have h_LHS_pow_eq :
      ∫⁻ x, ‖f (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) =
        eLpNorm (fun x => f (Φ.toFun x)) p (volume.restrict Ω) ^ q := by
    rw [eLpNorm_eq_eLpNorm' hp_zero hp_top hcomp, hq_def]
    exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hq_pos
  have h_RHS_pow_eq :
      ∫⁻ y, ‖f y‖ₑ ^ q ∂(volume.restrict Ω') =
        eLpNorm f p (volume.restrict Ω') ^ q := by
    rw [eLpNorm_eq_eLpNorm' hp_zero hp_top hf, hq_def]
    exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hq_pos
  rw [h_LHS_pow_eq, h_RHS_pow_eq] at hint_le'
  set A : ℝ≥0∞ := eLpNorm (fun x => f (Φ.toFun x)) p (volume.restrict Ω)
    with hA_def
  set B : ℝ≥0∞ := eLpNorm f p (volume.restrict Ω') with hB_def
  set j : ℝ≥0∞ := ENNReal.ofReal Φ.jacobianLowerBound with hj_def
  have hj_pos : 0 < j := by rw [hj_def]; exact ENNReal.ofReal_pos.mpr hjLB_pos
  have hj_ne_zero : j ≠ 0 := hj_pos.ne'
  have hj_ne_top : j ≠ ⊤ := by rw [hj_def]; exact ENNReal.ofReal_ne_top
  have h_Aq_le : A ^ q ≤ j⁻¹ * B ^ q := by
    have h1 : A ^ q = j⁻¹ * (j * A ^ q) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hj_ne_zero hj_ne_top, one_mul]
    rw [h1]
    gcongr
  have h_1q_nonneg : (0 : ℝ) ≤ 1 / q := by positivity
  have h_pow_le : (A ^ q) ^ (1 / q) ≤ (j⁻¹ * B ^ q) ^ (1 / q) :=
    ENNReal.rpow_le_rpow h_Aq_le h_1q_nonneg
  have h_LHS_simp : (A ^ q) ^ (1 / q) = A := by
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hq_pos.ne', ENNReal.rpow_one]
  have h_RHS_simp : (j⁻¹ * B ^ q) ^ (1 / q) = j⁻¹ ^ (1 / q) * B := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ h_1q_nonneg]
    congr 1
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hq_pos.ne', ENNReal.rpow_one]
  rw [h_LHS_simp, h_RHS_simp] at h_pow_le
  have h_inv_real : j⁻¹ = ENNReal.ofReal (1 / Φ.jacobianLowerBound) := by
    change (ENNReal.ofReal Φ.jacobianLowerBound)⁻¹ =
      ENNReal.ofReal (1 / Φ.jacobianLowerBound)
    rw [← ENNReal.ofReal_inv_of_pos hjLB_pos, one_div]
  rw [h_inv_real,
      ENNReal.ofReal_rpow_of_pos
        (by positivity : (0 : ℝ) < 1 / Φ.jacobianLowerBound)] at h_pow_le
  exact h_pow_le


variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma euclidean_coord_le_norm
    (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |v i| ≤ ‖v‖ := by
  classical
  have h_sq : (v i)^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h_le := Finset.single_le_sum
      (f := fun j : Fin d => (v j)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    convert h_le
  have hv_norm_nn : 0 ≤ ‖v‖ := norm_nonneg _
  have h_abs_sq : |v i|^2 = (v i)^2 := sq_abs _
  rw [show |v i| = Real.sqrt ((v i)^2) from (Real.sqrt_sq_eq_abs _).symm]
  rw [show ‖v‖ = Real.sqrt (‖v‖^2) from (Real.sqrt_sq hv_norm_nn).symm]
  exact Real.sqrt_le_sqrt h_sq

omit [NeZero d] in
private lemma continuousMultilinearMap_norm_le_sum_basis
    {n : ℕ}
    (f : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) ℝ) :
    ‖f‖ ≤ ∑ β : Fin n → Fin d,
      |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| := by
  classical
  set M : ℝ := ∑ β : Fin n → Fin d,
      |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| with hM_def
  have hM_nonneg : 0 ≤ M :=
    Finset.sum_nonneg (fun β _ => abs_nonneg _)
  refine ContinuousMultilinearMap.opNorm_le_bound hM_nonneg ?_
  intro m
  have h_expand : ∀ i : Fin n, m i =
      ∑ α : Fin d, (m i α) • EuclideanSpace.single α (1 : ℝ) := by
    intro i
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (m i)
    rw [show (fun α : Fin d => (m i α) • EuclideanSpace.single α (1 : ℝ)) =
      (fun α : Fin d => (EuclideanSpace.basisFun (Fin d) ℝ).repr (m i) α •
        (EuclideanSpace.basisFun (Fin d) ℝ) α) from ?_, h]
    funext α
    rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have h_f_expand :
      f m = ∑ β : Fin n → Fin d,
        (∏ i : Fin n, m i (β i)) *
          f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) := by
    have h_step1 : f m = f (fun i : Fin n =>
        ∑ α : Fin d, (m i α) • EuclideanSpace.single α (1 : ℝ)) := by
      congr; funext i; exact h_expand i
    rw [h_step1]
    have h_mult_sum :
        (f.toMultilinearMap fun i : Fin n =>
          ∑ α : Fin d, (m i α) • EuclideanSpace.single α (1 : ℝ)) =
        ∑ β : Fin n → Fin d,
          f.toMultilinearMap fun i : Fin n =>
            (m i (β i)) • EuclideanSpace.single (β i) (1 : ℝ) := by
      exact f.toMultilinearMap.map_sum
        (fun (i : Fin n) (α : Fin d) =>
          (m i α) • EuclideanSpace.single α (1 : ℝ))
    change f.toMultilinearMap _ = _
    rw [h_mult_sum]
    refine Finset.sum_congr rfl ?_
    intro β _
    rw [f.toMultilinearMap.map_smul_univ
      (c := fun i : Fin n => m i (β i))
      (m := fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))]
    rw [smul_eq_mul]
    rfl
  rw [Real.norm_eq_abs]
  rw [h_f_expand]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h_inner_bound : ∀ β : Fin n → Fin d,
      |(∏ i : Fin n, m i (β i)) *
          f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| ≤
        (∏ i : Fin n, ‖m i‖) *
          |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| := by
    intro β
    rw [abs_mul]
    have h_prod_le : |∏ i : Fin n, m i (β i)| ≤ ∏ i : Fin n, ‖m i‖ := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod₀ ?_ ?_
      · intro i _; exact abs_nonneg _
      · intro i _; exact euclidean_coord_le_norm (d := d) (m i) (β i)
    exact mul_le_mul_of_nonneg_right h_prod_le (abs_nonneg _)
  refine (Finset.sum_le_sum (fun β _ => h_inner_bound β)).trans ?_
  have h_factor :
      ∑ β : Fin n → Fin d,
        (∏ i : Fin n, ‖m i‖) *
          |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| =
      (∏ i : Fin n, ‖m i‖) * M := by
    rw [← Finset.mul_sum]
  rw [h_factor]
  exact le_of_eq (mul_comm _ _)

omit [NeZero d] in
private lemma norm_iteratedFDeriv_le_sum_basis
    (n : ℕ) {ψ : E → ℝ} (y : E) :
    ‖iteratedFDeriv ℝ n ψ y‖ ≤
      ∑ β : Fin n → Fin d,
        |iteratedFDeriv ℝ n ψ y
          (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| :=
  continuousMultilinearMap_norm_le_sum_basis (d := d) (iteratedFDeriv ℝ n ψ y)

omit [NeZero d] in
private lemma iteratedFDeriv_clm_apply_basis
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F →L[ℝ] ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : F)
    (β : Fin n → Fin d) (y : E) :
    iteratedFDeriv ℝ n g y
      (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) v =
    iteratedFDeriv ℝ n (fun y' => g y' v) y
      (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) := by
  have h := iteratedFDeriv_clm_apply_const_apply (𝕜 := ℝ)
    (n := (⊤ : ℕ∞)) (c := g) (u := v) (i := n) (x := y)
    (m := fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))
    hg (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  exact h.symm

omit [NeZero d] in
private lemma iteratedFDeriv_basis_eq_iterClassicalPartial_rev :
    ∀ (n : ℕ) (β : Fin n → Fin d) {f : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) f → ∀ y : E,
        iteratedFDeriv ℝ n f y
          (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) =
        iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y := by
  intro n
  induction n with
  | zero =>
      intro β f _ y
      simp [iteratedFDeriv_zero_apply, iterClassicalPartial_zero]
  | succ n ih =>
      intro β f hf y
      rw [show (fun i : Fin (n + 1) => EuclideanSpace.single (β i) (1 : ℝ)) =
        Fin.snoc (fun i : Fin n => EuclideanSpace.single (β i.castSucc) (1 : ℝ))
          (EuclideanSpace.single (β (Fin.last n)) (1 : ℝ)) by
        ext i
        induction i using Fin.lastCases with
        | last => simp
        | cast j => simp]
      rw [iteratedFDeriv_succ_apply_right]
      rw [Fin.init_snoc, Fin.snoc_last]
      have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by
        have hf_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by simpa using hf
        have h := hf_top.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        simpa using h
      rw [iteratedFDeriv_clm_apply_basis (d := d)
        (g := fderiv ℝ f) hfd (EuclideanSpace.single (β (Fin.last n)) (1 : ℝ))
        (β := fun i : Fin n => β i.castSucc) y]
      have h_inner_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun y' : E => (fderiv ℝ f y') (EuclideanSpace.single (β (Fin.last n)) (1 : ℝ))) :=
        hfd.clm_apply contDiff_const
      rw [ih (fun i : Fin n => β i.castSucc) h_inner_smooth y]
      rw [iterClassicalPartial_succ]
      have h_index_eq :
          (fun i : Fin n => β i.rev.castSucc) =
          (fun i : Fin n => β i.succ.rev) := by
        funext i
        rw [Fin.rev_succ]
      have h_first_eq : β (Fin.last n) = β (Fin.rev 0) := by
        rw [Fin.rev_zero]
      rw [h_index_eq, h_first_eq]

omit [NeZero d] in
private lemma norm_iteratedFDeriv_le_sum_iterClassicalPartial
    (n : ℕ) {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : E) :
    ‖iteratedFDeriv ℝ n f y‖ ≤
      ∑ β : Fin n → Fin d, |iterClassicalPartial (d := d) n β f y| := by
  classical
  have h1 := norm_iteratedFDeriv_le_sum_basis (d := d) n (ψ := f) y
  have h2 : ∀ β : Fin n → Fin d,
      |iteratedFDeriv ℝ n f y
        (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| =
      |iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y| := by
    intro β
    rw [iteratedFDeriv_basis_eq_iterClassicalPartial_rev (d := d) n β hf y]
  have h3 : ∑ β : Fin n → Fin d,
      |iteratedFDeriv ℝ n f y
        (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| =
      ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y| :=
    Finset.sum_congr rfl (fun β _ => h2 β)
  rw [h3] at h1
  have h_equiv :
      ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y| =
      ∑ β : Fin n → Fin d, |iterClassicalPartial (d := d) n β f y| := by
    have h_invol : ∀ β : Fin n → Fin d,
        (fun i : Fin n => (fun j : Fin n => β j.rev) i.rev) = β := by
      intro β
      funext i
      simp [Fin.rev_rev]
    refine Finset.sum_bij (fun β _ => fun i : Fin n => β i.rev) ?_ ?_ ?_ ?_
    · intro β _; exact Finset.mem_univ _
    · intro β1 _ β2 _ h
      have h_apply : ∀ i : Fin n,
          (fun j : Fin n => β1 j.rev) i = (fun j : Fin n => β2 j.rev) i :=
        fun i => congrFun h i
      funext i
      have := h_apply i.rev
      simpa [Fin.rev_rev] using this
    · intro β _
      refine ⟨fun i : Fin n => β i.rev, Finset.mem_univ _, ?_⟩
      funext i
      simp [Fin.rev_rev]
    · intro β _; rfl
  rw [h_equiv] at h1
  exact h1

omit [NeZero d] in
private lemma eLpNorm_iteratedFDeriv_le_sum_iterClassicalPartial
    (n : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : E → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (Ω : Set E) :
    eLpNorm (fun y => ‖iteratedFDeriv ℝ n f y‖) p (volume.restrict Ω) ≤
      ∑ β : Fin n → Fin d,
        eLpNorm (iterClassicalPartial (d := d) n β f) p (volume.restrict Ω) := by
  classical
  have h_pt : ∀ y, ‖iteratedFDeriv ℝ n f y‖ ≤
      ∑ β : Fin n → Fin d, |iterClassicalPartial (d := d) n β f y| :=
    fun y => norm_iteratedFDeriv_le_sum_iterClassicalPartial (d := d) n hf_smooth y
  have h_eLp_le :
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n f y‖) p (volume.restrict Ω) ≤
      eLpNorm (fun y => ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n β f y|) p (volume.restrict Ω) := by
    refine eLpNorm_mono_ae
      (hf_smooth.continuous_iteratedFDeriv (m := n)
        (by exact_mod_cast le_top)).norm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg]
    · exact h_pt y
    · exact Finset.sum_nonneg (fun β _ => abs_nonneg _)
  refine h_eLp_le.trans ?_
  have h_strong_meas : ∀ β : Fin n → Fin d,
      AEStronglyMeasurable
        (fun y => |iterClassicalPartial (d := d) n β f y|) (volume.restrict Ω) := by
    intro β
    have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (iterClassicalPartial (d := d) n β f) :=
      contDiff_iterClassicalPartial (d := d) n β hf_smooth
    have h_aem : AEStronglyMeasurable
        (iterClassicalPartial (d := d) n β f) (volume.restrict Ω) :=
      h_smooth.continuous.aestronglyMeasurable
    have h_norm := h_aem.norm
    refine h_norm.congr (Filter.Eventually.of_forall ?_)
    intro y
    exact (Real.norm_eq_abs _).symm
  have h_triangle :
      eLpNorm (fun y => ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n β f y|) p (volume.restrict Ω) ≤
      ∑ β : Fin n → Fin d,
        eLpNorm (fun y => |iterClassicalPartial (d := d) n β f y|) p (volume.restrict Ω) := by
    have hsum := eLpNorm_sum_le
      (μ := volume.restrict Ω) (p := p)
      (s := (Finset.univ : Finset (Fin n → Fin d)))
      (f := fun β y => |iterClassicalPartial (d := d) n β f y|)
      hp
    have h_eq : (fun y => ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n β f y|) =
        ((Finset.univ : Finset (Fin n → Fin d)).sum
          (fun β => fun y => |iterClassicalPartial (d := d) n β f y|)) := by
      funext y; rw [Finset.sum_apply]
    rw [h_eq]
    exact hsum
  refine h_triangle.trans ?_
  refine Finset.sum_le_sum (fun β _ => ?_)
  refine eLpNorm_mono_ae (h_strong_meas β) ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  rw [Real.norm_eq_abs, abs_abs]
  exact le_of_eq rfl

omit [NeZero d] in
lemma eLpNorm_iteratedFDeriv_le_wkpNorm
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    (k : ℕ)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω) :
    ∑ n ∈ Finset.range (k + 1),
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p (volume.restrict Ω) ≤
    iteratedWeakSobolevNorm (d := d) k p ψ Ω := by
  classical
  have h_per_n : ∀ n, n ≤ k →
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p (volume.restrict Ω) ≤
      ∑ β : Fin n → Fin d,
        eLpNorm (iterClassicalPartial (d := d) n β ψ) p (volume.restrict Ω) := fun n _ =>
    eLpNorm_iteratedFDeriv_le_sum_iterClassicalPartial (d := d) n hp_one
      hψ_smooth Ω
  have h_iter_eq : ∀ n β,
      eLpNorm (iterClassicalPartial (d := d) n β ψ) p (volume.restrict Ω) =
      eLpNorm (iterWeakPartial (d := d) p n β ψ Ω) p (volume.restrict Ω) := fun n β => by
    refine eLpNorm_congr_ae ?_
    exact (iterWeakPartial_smooth_ae_eq_iterClassicalPartial
      (d := d) hp_one hΩ_open n β hψ_smooth hψ_compact hψ_support).symm
  unfold iteratedWeakSobolevNorm
  refine Finset.sum_le_sum ?_
  intro n hn
  have hn_le : n ≤ k := by rw [Finset.mem_range] at hn; omega
  refine (h_per_n n hn_le).trans ?_
  refine Finset.sum_le_sum ?_
  intro β _
  rw [h_iter_eq]


omit [NeZero d] in
private lemma SmoothDiffeoBoundedAtOrder.norm_iteratedFDeriv_comp_toFun_le_sum
    {kmax : ℕ} {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {j : ℕ} (hj : j ≤ kmax) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => ψ (Φ.toFun y)) x‖ ≤
      j.factorial * Φ.derivBoundMaxOne ^ j *
        ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ := by
  classical
  set C : ℝ := ∑ n ∈ Finset.range (j + 1),
      ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ with hC_def
  have hC_bound : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i ψ (Φ.toFun x)‖ ≤ C := by
    intro i hi
    have hi_mem : i ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    exact Finset.single_le_sum
      (f := fun n => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖)
      (fun n _ => norm_nonneg _) hi_mem
  have h := Φ.norm_iteratedFDeriv_comp_toFun_le hψ_smooth hj x (C := C) hC_bound
  have h_rearrange : (j.factorial : ℝ) * C * Φ.derivBoundMaxOne ^ j =
      j.factorial * Φ.derivBoundMaxOne ^ j * C := by ring
  rw [h_rearrange] at h
  exact h

omit [NeZero d] in
private lemma SmoothDiffeoBoundedAtOrder.norm_iterClassicalPartial_comp_le_uniform
    {kmax : ℕ} {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (k : ℕ) (hk : k ≤ kmax) :
    ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k → ∀ x : E,
      ‖iterClassicalPartial (d := d) j β (fun y => ψ (Φ.toFun y)) x‖ ≤
        (k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k *
          ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ := by
  classical
  intro j β hj x
  have hj_le_kmax : j ≤ kmax := hj.trans hk
  have hcomp_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => ψ (Φ.toFun y)) :=
    Φ.comp_toFun_contDiff hψ_smooth
  have h1 := norm_iterClassicalPartial_le_iteratedFDeriv (d := d) j β hcomp_smooth x
  have h2 := Φ.norm_iteratedFDeriv_comp_toFun_le_sum hψ_smooth hj_le_kmax x
  have h3 := h1.trans h2
  set D : ℝ := Φ.derivBoundMaxOne with hD_def
  have hD_ge_1 : 1 ≤ D := Φ.derivBoundMaxOne_ge_one
  have hD_nonneg : 0 ≤ D := (lt_of_lt_of_le zero_lt_one hD_ge_1).le
  have h_fact_le : (j.factorial : ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hj
  have h_pow_le : D ^ j ≤ D ^ k := pow_le_pow_right₀ hD_ge_1 hj
  have h_inner_sum_le :
      ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ ≤
      ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn; rw [Finset.mem_range] at hn ⊢; omega
    · intro _ _ _; exact norm_nonneg _
  have h_pow_nn : (0 : ℝ) ≤ D ^ j := pow_nonneg hD_nonneg j
  have h_sum_inner_nn : (0 : ℝ) ≤
      ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ :=
    Finset.sum_nonneg (fun n _ => norm_nonneg _)
  have h_left_le :
      (j.factorial : ℝ) * D ^ j ≤ (k.factorial : ℝ) * D ^ k := by
    have h_step : (j.factorial : ℝ) * D ^ j ≤ (k.factorial : ℝ) * D ^ j :=
      mul_le_mul_of_nonneg_right h_fact_le h_pow_nn
    refine h_step.trans ?_
    have h_kf_nn : (0 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.zero_le _
    exact mul_le_mul_of_nonneg_left h_pow_le h_kf_nn
  refine h3.trans ?_
  have h_left_step : (j.factorial : ℝ) * D ^ j *
      ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ ≤
      (k.factorial : ℝ) * D ^ k *
        ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ :=
    mul_le_mul_of_nonneg_right h_left_le h_sum_inner_nn
  refine h_left_step.trans ?_
  have h_outer_nn : (0 : ℝ) ≤ (k.factorial : ℝ) * D ^ k := by
    have h_kf_nn : (0 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.zero_le _
    exact mul_nonneg h_kf_nn (pow_nonneg hD_nonneg k)
  exact mul_le_mul_of_nonneg_left h_inner_sum_le h_outer_nn

omit [NeZero d] in
private lemma SmoothDiffeoBoundedAtOrder.exists_cutoff_for_comp
    {kmax : ℕ} {Ωsource Ωtarget : Set E}
    (Φ : SmoothDiffeoBoundedAtOrder d Ωsource Ωtarget kmax) (hΩ_open : IsOpen Ωsource)
    {ψ : E → ℝ} (hψ_compact : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ Ωtarget) :
    ∃ (η : E → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      tsupport η ⊆ Ωsource ∧
      (∀ x ∈ Ωsource, η x * ψ (Φ.toFun x) = ψ (Φ.toFun x)) := by
  classical
  set Ktarget : Set E := tsupport ψ with hKtarget_def
  have hKtarget_compact : IsCompact Ktarget := hψ_compact
  have hKtargetΩtarget : Ktarget ⊆ Ωtarget := hψ_support
  set Ksource : Set E := Φ.invFun '' Ktarget with hKsource_def
  have hKsource_compact : IsCompact Ksource :=
    hKtarget_compact.image Φ.continuous_invFun
  have hKsourceΩsource : Ksource ⊆ Ωsource := by
    intro x hx
    rcases hx with ⟨y, hy_in, hxy⟩
    rw [← hxy]
    exact Φ.mapsTo_invFun (hKtargetΩtarget hy_in)
  obtain ⟨δ, η, hδ_pos, _hδ_subset, hη_smooth, hη_compact, _hη_range, hη_one, hη_support⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d) hKsource_compact hΩ_open
      hKsourceΩsource
  refine ⟨η, hη_smooth, hη_compact, hη_support, ?_⟩
  intro x hx
  by_cases hxK : x ∈ Ksource
  · have hx_cthick : x ∈ Metric.cthickening δ Ksource :=
      Metric.self_subset_cthickening _ hxK
    have hη_x : η x = 1 := hη_one x hx_cthick
    rw [hη_x, one_mul]
  · have h_φx_not_Ktarget : Φ.toFun x ∉ Ktarget := by
      intro h_in
      apply hxK
      refine ⟨Φ.toFun x, h_in, ?_⟩
      exact Φ.left_inv hx
    have hψ_zero : ψ (Φ.toFun x) = 0 :=
      image_eq_zero_of_notMem_tsupport h_φx_not_Ktarget
    rw [hψ_zero, mul_zero]

omit [NeZero d] in
private lemma iterClassicalPartial_eqOn_of_eqOn_local
    {Ω : Set E} (hΩ_open : IsOpen Ω) :
    ∀ (j : ℕ) (β : Fin j → Fin d) {g h : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ (⊤ : ℕ∞) h →
      Set.EqOn g h Ω →
      Set.EqOn (iterClassicalPartial (d := d) j β g)
        (iterClassicalPartial (d := d) j β h) Ω := by
  intro j
  induction j with
  | zero =>
      intro β g h _ _ hgh x hx
      simpa [iterClassicalPartial_zero] using hgh hx
  | succ j ih =>
      intro β g h hg_smooth hh_smooth hgh x hx
      rw [iterClassicalPartial_succ, iterClassicalPartial_succ]
      have h_partial_eqOn :
          Set.EqOn (fun y => (fderiv ℝ g y) (EuclideanSpace.single (β 0) 1))
            (fun y => (fderiv ℝ h y) (EuclideanSpace.single (β 0) 1)) Ω := by
        intro y hy
        have hy_eq : g =ᶠ[𝓝 y] h := by
          rw [Filter.eventuallyEq_iff_exists_mem]
          exact ⟨Ω, hΩ_open.mem_nhds hy, hgh⟩
        have hfd : fderiv ℝ g y = fderiv ℝ h y := hy_eq.fderiv_eq
        simp [hfd]
      have h_inner_g_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun y => (fderiv ℝ g y) (EuclideanSpace.single (β 0) 1)) :=
        (hg_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      have h_inner_h_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun y => (fderiv ℝ h y) (EuclideanSpace.single (β 0) 1)) :=
        (hh_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      exact ih (fun i : Fin j => β i.succ)
        h_inner_g_smooth h_inner_h_smooth h_partial_eqOn hx

omit [NeZero d] in
private theorem SmoothDiffeoBoundedAtOrder.comp_smooth_compactSupport_memWkp
    {kmax : ℕ} {Ωsource Ωtarget : Set E}
    (Φ : SmoothDiffeoBoundedAtOrder d Ωsource Ωtarget kmax) (hΩ_open : IsOpen Ωsource)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ωtarget)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ) :
    MemWkp (d := d) k p (fun x => ψ (Φ.toFun x)) Ωsource := by
  classical
  obtain ⟨η, hη_smooth, hη_compact, hη_support, h_eq_on_Ω⟩ :=
    Φ.exists_cutoff_for_comp hΩ_open hψ_compact hψ_support
  let g : E → ℝ := fun x => η x * ψ (Φ.toFun x)
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    hη_smooth.mul (Φ.comp_toFun_contDiff hψ_smooth)
  have hg_compact : HasCompactSupport g :=
    HasCompactSupport.mul_right hη_compact
  have hg_support : tsupport g ⊆ Ωsource :=
    (tsupport_mul_subset_left (f := η) (g := fun x => ψ (Φ.toFun x))).trans hη_support
  have hg_mem : MemWkp (d := d) k p g Ωsource :=
    MemWkp_of_smooth_compactSupport (d := d) hΩ_open hg_smooth hg_compact hg_support hp k
  have h_ae : (fun x => ψ (Φ.toFun x)) =ᵐ[volume.restrict Ωsource] g := by
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    change ψ (Φ.toFun x) = η x * ψ (Φ.toFun x)
    rw [h_eq_on_Ω x hx]
  exact (MemWkp_congr_ae (d := d) hp hΩ_open h_ae).mpr hg_mem

omit [NeZero d] in
private theorem SmoothDiffeoBoundedAtOrder.iterWeakPartial_comp_smooth_ae_eq_iterClassicalPartial
    {kmax : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    (j : ℕ) (β : Fin j → Fin d)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω') :
    iterWeakPartial (d := d) p j β (fun x => ψ (Φ.toFun x)) Ω
      =ᵐ[volume.restrict Ω]
      iterClassicalPartial (d := d) j β (fun x => ψ (Φ.toFun x)) := by
  classical
  obtain ⟨η, hη_smooth, hη_compact, hη_support, h_eq_on_Ω⟩ :=
    Φ.exists_cutoff_for_comp hΩ hψ_compact hψ_support
  let g : E → ℝ := fun x => η x * ψ (Φ.toFun x)
  let comp_smooth : E → ℝ := fun x => ψ (Φ.toFun x)
  have hcomp_smooth_smooth : ContDiff ℝ (⊤ : ℕ∞) comp_smooth :=
    Φ.comp_toFun_contDiff hψ_smooth
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    hη_smooth.mul hcomp_smooth_smooth
  have hg_compact : HasCompactSupport g :=
    HasCompactSupport.mul_right hη_compact
  have hg_support : tsupport g ⊆ Ω :=
    (tsupport_mul_subset_left (f := η) (g := comp_smooth)).trans hη_support
  have h_g_ae :=
    iterWeakPartial_smooth_ae_eq_iterClassicalPartial
      (d := d) hp_one hΩ j β hg_smooth hg_compact hg_support
  have h_comp_ae_g : comp_smooth =ᵐ[volume.restrict Ω] g := by
    refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    change ψ (Φ.toFun x) = η x * ψ (Φ.toFun x)
    rw [h_eq_on_Ω x hx]
  have h_weak_ae :=
    iterWeakPartial_ae_congr (d := d) hp_one hΩ j β h_comp_ae_g
  have h_classical_eqOn :
      Set.EqOn (iterClassicalPartial (d := d) j β g)
        (iterClassicalPartial (d := d) j β comp_smooth) Ω := by
    have h_g_eqOn_comp : Set.EqOn g comp_smooth Ω := by
      intro x hx
      change η x * ψ (Φ.toFun x) = ψ (Φ.toFun x)
      exact h_eq_on_Ω x hx
    exact iterClassicalPartial_eqOn_of_eqOn_local (d := d) hΩ j β
      hg_smooth hcomp_smooth_smooth h_g_eqOn_comp
  refine h_weak_ae.trans (h_g_ae.trans ?_)
  refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro x hx
  exact h_classical_eqOn hx

omit [NeZero d] in
private lemma SmoothDiffeoBoundedAtOrder.eLpNorm_iterWeakPartial_comp_le
    {kmax : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    (k : ℕ) (hk : k ≤ kmax)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω')
    (j : ℕ) (β : Fin j → Fin d) (hj : j ≤ k) :
    eLpNorm
        (iterWeakPartial (d := d) p j β (fun x => ψ (Φ.toFun x)) Ω) p
        (volume.restrict Ω) ≤
      ENNReal.ofReal ((k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k) *
        ∑ n ∈ Finset.range (k + 1),
          eLpNorm
            (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) p
            (volume.restrict Ω) := by
  classical
  have h_eq := Φ.iterWeakPartial_comp_smooth_ae_eq_iterClassicalPartial
    hp_one hΩ j β hψ_smooth hψ_compact hψ_support
  rw [eLpNorm_congr_ae h_eq]
  have h_pt := Φ.norm_iterClassicalPartial_comp_le_uniform
    hψ_smooth k hk j β hj
  set D := Φ.derivBoundMaxOne with hD_def
  set Const : ℝ := (k.factorial : ℝ) * D ^ k with hConst_def
  have hConst_nonneg : 0 ≤ Const := by
    refine mul_nonneg ?_ ?_
    · exact_mod_cast Nat.zero_le _
    · exact pow_nonneg
        (lt_of_lt_of_le zero_lt_one Φ.derivBoundMaxOne_ge_one).le k
  have h_eLp_le :
      eLpNorm (iterClassicalPartial (d := d) j β
          (fun x => ψ (Φ.toFun x))) p (volume.restrict Ω) ≤
        eLpNorm (fun x => Const *
          ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) p
          (volume.restrict Ω) := by
    refine eLpNorm_mono_ae
      (contDiff_iterClassicalPartial j β (hψ_smooth.comp Φ.toFun_smooth)).continuous.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have h_rhs_nonneg : 0 ≤ Const *
        ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ := by
      refine mul_nonneg hConst_nonneg ?_
      exact Finset.sum_nonneg (fun n _ => norm_nonneg _)
    rw [Real.norm_eq_abs (Const * _)]
    rw [abs_of_nonneg h_rhs_nonneg]
    exact (h_pt x).trans_eq rfl
  refine h_eLp_le.trans ?_
  have h_smul_eq : (fun x => Const *
      ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) =
      (Const : ℝ) • (fun x => ∑ n ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) := by
    funext x; simp [Pi.smul_apply, smul_eq_mul]
  rw [h_smul_eq, eLpNorm_const_smul]
  have hConst_norm : (‖Const‖ₑ : ℝ≥0∞) = ENNReal.ofReal Const :=
    Real.enorm_of_nonneg hConst_nonneg
  rw [hConst_norm]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le)
  have h_pointwise_eq : (fun x => ∑ n ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) =
      ∑ n ∈ Finset.range (k + 1),
        (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) := by
    funext x; rw [Finset.sum_apply]
  rw [h_pointwise_eq]
  exact eLpNorm_sum_le hp_one

omit [NeZero d] in
private lemma SmoothDiffeoBoundedAtOrder.eLpNorm_iteratedFDeriv_comp_le
    {kmax : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    {ψ : E → ℝ} (n : ℕ) :
    eLpNorm (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) p
        (volume.restrict Ω) ≤
      ENNReal.ofReal
        ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p (volume.restrict Ω') :=
  Φ.eLpNorm_comp_toFun_le_const hp_one hp_top hΩ
    (fun y => ‖iteratedFDeriv ℝ n ψ y‖)

noncomputable def SmoothDiffeoBoundedAtOrder.wkpCompositionConstant
    {kmax : ℕ} {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax) (k : ℕ) (p : ℝ≥0∞) : ℝ :=
  ((Finset.range (k + 1)).sum (fun j => (Fintype.card (Fin j → Fin d) : ℝ))) *
    ((k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k) *
    ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
    ((k + 1 : ℕ) : ℝ)

private lemma SmoothDiffeoBoundedAtOrder.wkpCompositionConstant_pos
    {kmax : ℕ} {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax) (k : ℕ) (p : ℝ≥0∞)
    (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    0 < Φ.wkpCompositionConstant k p := by
  have hp_zero : p ≠ 0 := by
    intro hpz; rw [hpz] at hp_one
    exact absurd hp_one (by norm_num)
  have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
  have hjLB_pos : 0 < Φ.jacobianLowerBound := Φ.jacobian_lower_bound_pos
  have hjLB_inv_pos : 0 < 1 / Φ.jacobianLowerBound := by positivity
  have hKchg_pos : 0 < (1 / Φ.jacobianLowerBound) ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos hjLB_inv_pos _
  unfold wkpCompositionConstant
  have h_zero_in : (0 : ℕ) ∈ Finset.range (k + 1) :=
    Finset.mem_range.mpr (Nat.zero_lt_succ _)
  have h_at_zero : (Fintype.card (Fin 0 → Fin d) : ℝ) = 1 := by
    have h_card : Fintype.card (Fin 0 → Fin d) = 1 := by
      rw [Fintype.card_fun]; simp
    exact_mod_cast h_card
  have h_card_pos : 0 < (Finset.range (k + 1)).sum
      (fun j => (Fintype.card (Fin j → Fin d) : ℝ)) := by
    have h_le := Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun j => (Fintype.card (Fin j → Fin d) : ℝ))
      (fun j _ => by positivity) h_zero_in
    nlinarith [h_le, h_at_zero]
  have h_kfact_D_pos : 0 < (k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k := by
    refine mul_pos ?_ ?_
    · exact_mod_cast Nat.factorial_pos k
    · exact pow_pos Φ.derivBoundMaxOne_pos k
  have h_k1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ k
  positivity

theorem SmoothDiffeoBoundedAtOrder.wkpNorm_comp_smooth_le
    {kmax : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω Ω' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax) (k : ℕ) (hk : k ≤ kmax)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω') :
    iteratedWeakSobolevNorm (d := d) k p (fun x => ψ (Φ.toFun x)) Ω ≤
      ENNReal.ofReal (Φ.wkpCompositionConstant k p) *
        iteratedWeakSobolevNorm (d := d) k p ψ Ω' := by
  classical
  set Comp_const : ℝ := (k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k with hComp_const_def
  have hComp_const_nonneg : 0 ≤ Comp_const :=
    mul_nonneg (by exact_mod_cast Nat.zero_le _)
      (pow_nonneg
        (lt_of_lt_of_le zero_lt_one Φ.derivBoundMaxOne_ge_one).le k)
  set Kchg : ℝ := (1 / Φ.jacobianLowerBound) ^ (1 / p.toReal) with hKchg_def
  have hjLB_pos : 0 < Φ.jacobianLowerBound := Φ.jacobian_lower_bound_pos
  have hKchg_nonneg : 0 ≤ Kchg := by
    have hjLB_inv_pos : 0 < 1 / Φ.jacobianLowerBound := by positivity
    exact (Real.rpow_pos_of_pos hjLB_inv_pos _).le
  set CardSum : ℝ := (Finset.range (k + 1)).sum
    (fun j => (Fintype.card (Fin j → Fin d) : ℝ)) with hCardSum_def
  have hCardSum_nn : 0 ≤ CardSum :=
    Finset.sum_nonneg (fun j _ => by exact_mod_cast Nat.zero_le _)
  unfold iteratedWeakSobolevNorm
  have h_each_jβ : ∀ j ∈ Finset.range (k + 1), ∀ β : Fin j → Fin d,
      eLpNorm
          (iterWeakPartial (d := d) p j β (fun x => ψ (Φ.toFun x)) Ω) p
          (volume.restrict Ω) ≤
        ENNReal.ofReal Comp_const * ENNReal.ofReal Kchg *
          iteratedWeakSobolevNorm (d := d) k p ψ Ω' := by
    intro j hj β
    have hjk : j ≤ k := by rw [Finset.mem_range] at hj; omega
    have h1 := Φ.eLpNorm_iterWeakPartial_comp_le hp_one hΩ k hk
      hψ_smooth hψ_compact hψ_support j β hjk
    have h_per_n : ∀ n,
        eLpNorm (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) p
            (volume.restrict Ω) ≤
          ENNReal.ofReal Kchg *
            eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p
              (volume.restrict Ω') := fun n =>
      Φ.eLpNorm_iteratedFDeriv_comp_le hp_one hp_top hΩ (ψ := ψ) n
    have h_sum_le_chg :
        ∑ n ∈ Finset.range (k + 1),
          eLpNorm (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) p
            (volume.restrict Ω) ≤
          ENNReal.ofReal Kchg *
            ∑ n ∈ Finset.range (k + 1),
              eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p
                (volume.restrict Ω') := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun n _ => h_per_n n)
    have h_iter_le := eLpNorm_iteratedFDeriv_le_wkpNorm
      (d := d) hΩ' hp_one k hψ_smooth hψ_compact hψ_support
    refine h1.trans ?_
    refine (mul_le_mul_of_nonneg_left h_sum_le_chg (zero_le)).trans ?_
    have h_step :
        ENNReal.ofReal Comp_const *
          (ENNReal.ofReal Kchg *
            ∑ n ∈ Finset.range (k + 1),
              eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p
                (volume.restrict Ω')) ≤
          ENNReal.ofReal Comp_const *
            (ENNReal.ofReal Kchg * iteratedWeakSobolevNorm (d := d) k p ψ Ω') := by
      gcongr
    refine h_step.trans ?_
    rw [show (ENNReal.ofReal Comp_const *
        (ENNReal.ofReal Kchg * iteratedWeakSobolevNorm (d := d) k p ψ Ω')) =
        ENNReal.ofReal Comp_const * ENNReal.ofReal Kchg *
          iteratedWeakSobolevNorm (d := d) k p ψ Ω' from by ring]
  have h_outer :
      ∑ j ∈ Finset.range (k + 1),
        ∑ β : Fin j → Fin d,
          eLpNorm
            (iterWeakPartial (d := d) p j β (fun x => ψ (Φ.toFun x)) Ω) p
            (volume.restrict Ω) ≤
        ∑ j ∈ Finset.range (k + 1),
          ∑ _β : Fin j → Fin d,
            (ENNReal.ofReal Comp_const * ENNReal.ofReal Kchg *
              iteratedWeakSobolevNorm (d := d) k p ψ Ω') := by
    refine Finset.sum_le_sum ?_
    intro j hj
    refine Finset.sum_le_sum ?_
    intro β _
    exact h_each_jβ j hj β
  refine h_outer.trans ?_
  have h_inner_const : ∀ j ∈ Finset.range (k + 1),
      (∑ _β : Fin j → Fin d,
          (ENNReal.ofReal Comp_const * ENNReal.ofReal Kchg *
            iteratedWeakSobolevNorm (d := d) k p ψ Ω')) =
        (Fintype.card (Fin j → Fin d) : ℝ≥0∞) *
          (ENNReal.ofReal Comp_const * ENNReal.ofReal Kchg *
            iteratedWeakSobolevNorm (d := d) k p ψ Ω') := by
    intro j _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h_inner_const]
  rw [← Finset.sum_mul]
  have h_card_sum_eq :
      (∑ j ∈ Finset.range (k + 1),
          (Fintype.card (Fin j → Fin d) : ℝ≥0∞)) =
        ENNReal.ofReal CardSum := by
    rw [hCardSum_def]
    rw [show ((Finset.range (k + 1)).sum
          (fun j => (Fintype.card (Fin j → Fin d) : ℝ))) =
        ∑ j ∈ Finset.range (k + 1),
          (Fintype.card (Fin j → Fin d) : ℝ) from rfl]
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun j _ => by exact_mod_cast Nat.zero_le _)]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact (ENNReal.ofReal_natCast _).symm
  rw [h_card_sum_eq]
  have h_wc : Φ.wkpCompositionConstant k p =
      CardSum * Comp_const * Kchg * ((k + 1 : ℕ) : ℝ) := rfl
  rw [h_wc]
  have hk1_nn : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_combine :
      ENNReal.ofReal (CardSum * Comp_const * Kchg * ((k + 1 : ℕ) : ℝ)) =
      ENNReal.ofReal CardSum * ENNReal.ofReal Comp_const *
        ENNReal.ofReal Kchg * ENNReal.ofReal ((k + 1 : ℕ) : ℝ) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ CardSum * Comp_const * Kchg)]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ CardSum * Comp_const)]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ CardSum)]
  rw [h_combine]
  have h_LHS_eq :
      ENNReal.ofReal CardSum *
        (ENNReal.ofReal Comp_const * ENNReal.ofReal Kchg *
          iteratedWeakSobolevNorm (d := d) k p ψ Ω') =
      ENNReal.ofReal CardSum * ENNReal.ofReal Comp_const *
        ENNReal.ofReal Kchg * iteratedWeakSobolevNorm (d := d) k p ψ Ω' := by ring
  rw [h_LHS_eq]
  have h_k1_ennreal : ENNReal.ofReal ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ≥0∞) :=
    ENNReal.ofReal_natCast (k + 1)
  rw [h_k1_ennreal]
  have h_one_le : (1 : ℝ≥0∞) ≤ ((k + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
  set A := ENNReal.ofReal CardSum * ENNReal.ofReal Comp_const *
    ENNReal.ofReal Kchg with hA_def
  set W := iteratedWeakSobolevNorm (d := d) k p ψ Ω' with hW_def
  change A * W ≤ A * ((k + 1 : ℕ) : ℝ≥0∞) * W
  calc A * W = A * 1 * W := by ring
    _ ≤ A * ((k + 1 : ℕ) : ℝ≥0∞) * W := by gcongr

private theorem SmoothDiffeoBoundedAtOrder.exists_limit_comp_of_smooth_approximation
    {kmax : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω Ω' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax) (k : ℕ) (hk : k ≤ kmax)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω')
    (ψ : ℕ → E → ℝ)
    (hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n))
    (hψ_compact : ∀ n, HasCompactSupport (ψ n))
    (hψ_support : ∀ n, tsupport (ψ n) ⊆ Ω')
    (hψ_close : ∀ n,
      iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' ≤
        ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ))) :
    ∃ v : E → ℝ,
      MemWkp (d := d) k p v Ω ∧
      Filter.Tendsto
        (fun n => iteratedWeakSobolevNorm (d := d) k p
          (fun x => v x - ψ n (Φ.toFun x)) Ω)
        atTop (𝓝 0) ∧
      v =ᵐ[volume.restrict Ω] (fun x => u (Φ.toFun x)) := by
  classical
  set K_const : ℝ := Φ.wkpCompositionConstant k p with hK_def
  have hK_pos : 0 < K_const :=
    Φ.wkpCompositionConstant_pos k p hp_one hp_top
  have hK_nonneg : 0 ≤ K_const := hK_pos.le
  have hψ_mem_target : ∀ n, MemWkp (d := d) k p (ψ n) Ω' := fun n =>
    MemWkp_of_smooth_compactSupport
      (d := d) hΩ' (hψ_smooth n) (hψ_compact n) (hψ_support n) hp_one k
  have hψ_comp_mem : ∀ n, MemWkp (d := d) k p (fun x => ψ n (Φ.toFun x)) Ω :=
    fun n =>
      Φ.comp_smooth_compactSupport_memWkp hΩ
        (hψ_smooth n) (hψ_compact n) (hψ_support n) hp_one k
  have h_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      iteratedWeakSobolevNorm (d := d) k p
        (fun x => (ψ m (Φ.toFun x)) - (ψ n (Φ.toFun x))) Ω ≤
        ENNReal.ofReal ε := by
    intro ε hε
    have hε_K_pos : 0 < ε / (2 * K_const) := by positivity
    obtain ⟨N0, hN0_real⟩ := exists_nat_gt (1 / (ε / (2 * K_const)) - 1)
    have hN1_pos : (0 : ℝ) < (N0 : ℝ) + 1 := by
      have : 0 < 1 / (ε / (2 * K_const)) := by positivity
      linarith
    have hN0_inv : (1 : ℝ) / (N0 + 1 : ℝ) ≤ ε / (2 * K_const) := by
      rw [div_le_iff₀ hN1_pos]
      have h1 : (1 : ℝ) = (ε / (2 * K_const)) * (1 / (ε / (2 * K_const))) := by
        rw [mul_one_div, div_self hε_K_pos.ne']
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ hε_K_pos.le
      linarith
    refine ⟨N0, ?_⟩
    intro m n hm hn
    let δ : E → ℝ := fun x => ψ m x - ψ n x
    have hδ_smooth : ContDiff ℝ (⊤ : ℕ∞) δ := (hψ_smooth m).sub (hψ_smooth n)
    have hδ_compact : HasCompactSupport δ := (hψ_compact m).sub (hψ_compact n)
    have hδ_support : tsupport δ ⊆ Ω' := by
      have h_support_sub : Function.support δ ⊆
          Function.support (ψ m) ∪ Function.support (ψ n) := by
        intro x hx
        by_cases hxm : x ∈ Function.support (ψ m)
        · exact Or.inl hxm
        · right
          change ψ n x ≠ 0
          intro hxn
          apply hx
          change ψ m x - ψ n x = 0
          rw [Function.notMem_support.mp hxm, hxn, sub_zero]
      have h_tsupp_sub : tsupport δ ⊆ tsupport (ψ m) ∪ tsupport (ψ n) := by
        unfold tsupport
        refine (closure_mono h_support_sub).trans ?_
        rw [closure_union]
      exact h_tsupp_sub.trans (Set.union_subset (hψ_support m) (hψ_support n))
    have hS1 := Φ.wkpNorm_comp_smooth_le hp_one hp_top hΩ hΩ'
      k hk hδ_smooth hδ_compact hδ_support
    have h_δ_alg : δ = (fun x => (u x - ψ n x) - (u x - ψ m x)) := by
      funext x
      change ψ m x - ψ n x = u x - ψ n x - (u x - ψ m x)
      ring
    have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem_target n)
    have h_uψm_mem : MemWkp (d := d) k p (fun x => u x - ψ m x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem_target m)
    have h_δ_wkp_le :
        iteratedWeakSobolevNorm (d := d) k p δ Ω' ≤
          iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' +
            iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ m x) Ω' := by
      rw [h_δ_alg]
      have hneg : MemWkp (d := d) k p (fun x => -(u x - ψ m x)) Ω' :=
        MemWkp.neg (d := d) hp_one hΩ' h_uψm_mem
      have h_eq :
          (fun x => u x - ψ n x - (u x - ψ m x)) =
            (fun x => (u x - ψ n x) + (-(u x - ψ m x))) := by
        funext x; ring
      rw [h_eq]
      have h_add := wkpNorm_add_le (d := d) hp_one hΩ' h_uψn_mem hneg
      refine h_add.trans ?_
      have h_neg_eq :
          iteratedWeakSobolevNorm (d := d) k p (fun x => -(u x - ψ m x)) Ω' =
            iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ m x) Ω' := by
        have h_eq_smul : (fun x => -(u x - ψ m x)) =
            (fun x => (-1 : ℝ) * (u x - ψ m x)) := by funext x; ring
        rw [h_eq_smul, wkpNorm_const_smul (d := d) hp_one hΩ' h_uψm_mem (-1)]
        simp
      rw [h_neg_eq]
    have hψm_close := hψ_close m
    have hψn_close := hψ_close n
    have h_n_le : ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) ≤
        ENNReal.ofReal ((1 : ℝ) / (N0 + 1 : ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      apply div_le_div_of_nonneg_left zero_le_one hN1_pos
      have hN0n : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h_m_le : ENNReal.ofReal ((1 : ℝ) / (m + 1 : ℝ)) ≤
        ENNReal.ofReal ((1 : ℝ) / (N0 + 1 : ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      apply div_le_div_of_nonneg_left zero_le_one hN1_pos
      have hN0m : (N0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h_δ_le_2N0 :
        iteratedWeakSobolevNorm (d := d) k p δ Ω' ≤
          ENNReal.ofReal (2 * ((1 : ℝ) / (N0 + 1 : ℝ))) := by
      refine h_δ_wkp_le.trans ?_
      refine (add_le_add hψn_close hψm_close).trans ?_
      refine (add_le_add h_n_le h_m_le).trans ?_
      have h2 : (2 * ((1 : ℝ) / (N0 + 1 : ℝ))) =
          ((1 : ℝ) / (N0 + 1 : ℝ)) + ((1 : ℝ) / (N0 + 1 : ℝ)) := by ring
      rw [h2]
      have h_pos : 0 ≤ (1 : ℝ) / (N0 + 1 : ℝ) := by positivity
      rw [ENNReal.ofReal_add h_pos h_pos]
    have h_δcomp_eq : (fun x => δ (Φ.toFun x)) =
        (fun x => ψ m (Φ.toFun x) - ψ n (Φ.toFun x)) := by
      funext x; rfl
    rw [h_δcomp_eq] at hS1
    refine hS1.trans ?_
    refine (mul_le_mul_of_nonneg_left h_δ_le_2N0 (zero_le)).trans ?_
    rw [← ENNReal.ofReal_mul hK_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    calc K_const * (2 * ((1 : ℝ) / (N0 + 1 : ℝ)))
        = (2 * K_const) * ((1 : ℝ) / (N0 + 1 : ℝ)) := by ring
      _ ≤ (2 * K_const) * (ε / (2 * K_const)) := by
            apply mul_le_mul_of_nonneg_left hN0_inv
            positivity
      _ = ε := by
            have h_pos : 0 < 2 * K_const := by positivity
            field_simp
  obtain ⟨v, hv_mem, hv_tendsto⟩ :=
    MemWkp.exists_limit_of_wkpNorm_cauchy (d := d) hΩ k p hp_one
      hψ_comp_mem h_cauchy
  have h_v_sub_tendsto :
      Filter.Tendsto
        (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω)
        atTop (𝓝 0) := by
    have h_eq : ∀ n, (fun x => v x - ψ n (Φ.toFun x)) =
        (fun x => -(ψ n (Φ.toFun x) - v x)) := by
      intro n; funext x; ring
    have h_norm_eq : ∀ n,
        iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω =
          iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n (Φ.toFun x) - v x) Ω := by
      intro n
      rw [h_eq n]
      have hf_mem : MemWkp (d := d) k p
          (fun x => ψ n (Φ.toFun x) - v x) Ω :=
        MemWkp.sub (d := d) hp_one hΩ (hψ_comp_mem n) hv_mem
      rw [show (fun x => -(ψ n (Φ.toFun x) - v x)) =
          (fun x => (-1 : ℝ) * (ψ n (Φ.toFun x) - v x)) from by
        funext x; ring]
      rw [wkpNorm_const_smul (d := d) hp_one hΩ hf_mem (-1)]
      simp
    rw [show (fun n => iteratedWeakSobolevNorm (d := d) k p
          (fun x => v x - ψ n (Φ.toFun x)) Ω) =
        (fun n => iteratedWeakSobolevNorm (d := d) k p
          (fun x => ψ n (Φ.toFun x) - v x) Ω) from funext h_norm_eq]
    exact hv_tendsto
  have h_Lp_close : ∀ n,
      eLpNorm (fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) p
        (volume.restrict Ω) ≤
        ENNReal.ofReal
            ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
          ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
    intro n
    have h_chg := Φ.eLpNorm_comp_toFun_le_const hp_one hp_top hΩ
      (fun x => u x - ψ n x)
    have h_eLp_le_wkp :
        eLpNorm (fun x => u x - ψ n x) p (volume.restrict Ω') ≤
          iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' := by
      simpa only [wkpNorm_zero] using
        (wkpNorm_mono_order (d := d) (p := p) (Nat.zero_le k) (fun x => u x - ψ n x) Ω')
    have h_arg_eq : (fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) =
        (fun x => (fun y => u y - ψ n y) (Φ.toFun x)) := by funext x; rfl
    rw [h_arg_eq]
    refine h_chg.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    exact h_eLp_le_wkp.trans (hψ_close n)
  have h_v_eq_uΦ : v =ᵐ[volume.restrict Ω] (fun x => u (Φ.toFun x)) := by
    have hp_zero_ne : p ≠ 0 := by
      intro hpz; rw [hpz] at hp_one
      exact absurd hp_one (by norm_num)
    have h_zero :
        eLpNorm (fun x => v x - u (Φ.toFun x)) p (volume.restrict Ω) = 0 := by
      have h_bound : ∀ n,
          eLpNorm (fun x => v x - u (Φ.toFun x)) p (volume.restrict Ω) ≤
            iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω +
            ENNReal.ofReal
                ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
              ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
        intro n
        have h_decomp :
            (fun x => v x - u (Φ.toFun x)) = (fun x =>
              (v x - ψ n (Φ.toFun x)) + (ψ n (Φ.toFun x) - u (Φ.toFun x))) := by
          funext x; ring
        rw [h_decomp]
        refine (eLpNorm_add_le hp_one).trans ?_
        have h_first :
            eLpNorm (fun x => v x - ψ n (Φ.toFun x)) p (volume.restrict Ω) ≤
              iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω := by
          simpa only [wkpNorm_zero] using
            (wkpNorm_mono_order (d := d) (p := p) (Nat.zero_le k)
              (fun x => v x - ψ n (Φ.toFun x)) Ω)
        have h_second :
            eLpNorm (fun x => ψ n (Φ.toFun x) - u (Φ.toFun x)) p
                (volume.restrict Ω) ≤
              ENNReal.ofReal
                  ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
                ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
          rw [show eLpNorm (fun x => ψ n (Φ.toFun x) - u (Φ.toFun x)) p
              (volume.restrict Ω) =
            eLpNorm (fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) p
              (volume.restrict Ω) from
            eLpNorm_sub_comm (fun x => ψ n (Φ.toFun x)) (fun x => u (Φ.toFun x))
              p (volume.restrict Ω)]
          exact h_Lp_close n
        exact add_le_add h_first h_second
      apply le_antisymm _ (zero_le)
      have h_tendsto_second :
          Filter.Tendsto
            (fun n : ℕ => ENNReal.ofReal
                ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
              ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
            atTop (𝓝 0) := by
        have h_inner_tendsto :
            Filter.Tendsto
              (fun n : ℕ => ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
              atTop (𝓝 0) := by
          have h_real : Filter.Tendsto
              (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          have h_ofReal := (ENNReal.continuous_ofReal.tendsto 0).comp h_real
          change Filter.Tendsto
            (ENNReal.ofReal ∘ fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0)
          simpa [ENNReal.ofReal_zero] using h_ofReal
        set C : ℝ≥0∞ := ENNReal.ofReal
            ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) with hC_def
        have hC_ne_top : C ≠ ⊤ := by rw [hC_def]; exact ENNReal.ofReal_ne_top
        have h_const_mul := ENNReal.Tendsto.const_mul (a := C) (b := 0)
          h_inner_tendsto (Or.inr hC_ne_top)
        simpa using h_const_mul
      have h_tendsto_sum :
          Filter.Tendsto
            (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω +
              ENNReal.ofReal
                  ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
                ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
            atTop (𝓝 0) := by
        have := h_v_sub_tendsto.add h_tendsto_second
        simpa using this
      exact ge_of_tendsto h_tendsto_sum (Filter.Eventually.of_forall h_bound)
    have h_diff_zero : (fun x => v x - u (Φ.toFun x)) =ᵐ[volume.restrict Ω]
        0 := by
      exact (eLpNorm_eq_zero_iff hp_zero_ne).mp h_zero
    filter_upwards [h_diff_zero] with x hx
    have : v x - u (Φ.toFun x) = 0 := hx
    linarith
  exact ⟨v, hv_mem, h_v_sub_tendsto, h_v_eq_uΦ⟩

theorem MemWkp.comp_smoothDiffeoBoundedAtOrder
    {kmax : ℕ} (k : ℕ) (hk : k ≤ kmax)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω Ω' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω')
    (hu_compactSupport : HasCompactSupport u)
    (hu_support : tsupport u ⊆ Ω') :
    MemWkp (d := d) k p (fun x => u (Φ.toFun x)) Ω := by
  classical
  have h_approx : ∀ n : ℕ, ∃ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω' ∧
      iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ x) Ω' ≤
        ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
    intro n
    have h_pos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
    exact MemWkp.exists_smooth_compactSupport_approx
      (d := d) hΩ' k p hp_one hp_top hu hu_compactSupport hu_support _ h_pos
  let ψ : ℕ → E → ℝ := fun n => (h_approx n).choose
  have hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n =>
    (h_approx n).choose_spec.1
  have hψ_compact : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (h_approx n).choose_spec.2.1
  have hψ_support : ∀ n, tsupport (ψ n) ⊆ Ω' := fun n =>
    (h_approx n).choose_spec.2.2.1
  have hψ_close : ∀ n,
      iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' ≤
        ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := fun n =>
    (h_approx n).choose_spec.2.2.2
  obtain ⟨v, hv_mem, _, h_v_eq_uΦ⟩ :=
    Φ.exists_limit_comp_of_smooth_approximation hp_one hp_top hΩ hΩ' k hk hu
      ψ hψ_smooth hψ_compact hψ_support hψ_close
  exact (MemWkp_congr_ae (d := d) hp_one hΩ h_v_eq_uΦ).mp hv_mem


theorem SmoothDiffeoBoundedAtOrder.wkpNorm_comp_le
    {kmax : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω Ω' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    (k : ℕ) (hk : k ≤ kmax)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω')
    (hu_compactSupport : HasCompactSupport u)
    (hu_support : tsupport u ⊆ Ω') :
    iteratedWeakSobolevNorm (d := d) k p (fun x => u (Φ.toFun x)) Ω ≤
      ENNReal.ofReal (Φ.wkpCompositionConstant k p) *
        iteratedWeakSobolevNorm (d := d) k p u Ω' := by
  classical
  set K_const : ℝ := Φ.wkpCompositionConstant k p with hK_def
  have h_approx : ∀ n : ℕ, ∃ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω' ∧
      iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ x) Ω' ≤
        ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
    intro n
    have h_pos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
    exact MemWkp.exists_smooth_compactSupport_approx
      (d := d) hΩ' k p hp_one hp_top hu hu_compactSupport hu_support _ h_pos
  let ψ : ℕ → E → ℝ := fun n => (h_approx n).choose
  have hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n =>
    (h_approx n).choose_spec.1
  have hψ_compact : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (h_approx n).choose_spec.2.1
  have hψ_support : ∀ n, tsupport (ψ n) ⊆ Ω' := fun n =>
    (h_approx n).choose_spec.2.2.1
  have hψ_close : ∀ n,
      iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' ≤
        ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := fun n =>
    (h_approx n).choose_spec.2.2.2
  have hψ_mem : ∀ n, MemWkp (d := d) k p (ψ n) Ω' := fun n =>
    MemWkp_of_smooth_compactSupport (d := d) hΩ' (hψ_smooth n) (hψ_compact n)
      (hψ_support n) hp_one k
  have hψ_comp_mem : ∀ n, MemWkp (d := d) k p (fun x => ψ n (Φ.toFun x)) Ω :=
    fun n => Φ.comp_smooth_compactSupport_memWkp hΩ
      (hψ_smooth n) (hψ_compact n) (hψ_support n) hp_one k
  obtain ⟨vΦ, hvΦ_mem, hvΦ_tendsto, h_vΦ_eq_uΦ⟩ :=
    Φ.exists_limit_comp_of_smooth_approximation hp_one hp_top hΩ hΩ' k hk hu
      ψ hψ_smooth hψ_compact hψ_support hψ_close
  have h_uΦ_eq_vΦ : (fun x => u (Φ.toFun x)) =ᵐ[volume.restrict Ω] vΦ :=
    h_vΦ_eq_uΦ.symm
  have h_norm_eq :
      iteratedWeakSobolevNorm (d := d) k p (fun x => u (Φ.toFun x)) Ω =
        iteratedWeakSobolevNorm (d := d) k p vΦ Ω :=
    wkpNorm_congr_ae (d := d) hp_one hΩ h_uΦ_eq_vΦ
  rw [h_norm_eq]
  set RHS : ℝ≥0∞ := ENNReal.ofReal K_const * iteratedWeakSobolevNorm (d := d) k p u Ω' with hRHS_def
  have h_bound2 : ∀ n,
      iteratedWeakSobolevNorm (d := d) k p vΦ Ω ≤
        iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
        ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) +
        RHS := by
    intro n
    have h_decomp : (fun x => vΦ x) =
        (fun x => (vΦ x - ψ n (Φ.toFun x)) + ψ n (Φ.toFun x)) := by
      funext x; ring
    have h_ψcomp_mem : MemWkp (d := d) k p (fun x => ψ n (Φ.toFun x)) Ω :=
      hψ_comp_mem n
    have h_diff_mem : MemWkp (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω :=
      MemWkp.sub (d := d) hp_one hΩ hvΦ_mem h_ψcomp_mem
    have h_fun_eq : vΦ = fun x => (vΦ x - ψ n (Φ.toFun x)) + ψ n (Φ.toFun x) := by
      funext x; ring
    conv_lhs => rw [h_fun_eq]
    have h_tri := wkpNorm_add_le (d := d) hp_one hΩ h_diff_mem h_ψcomp_mem
    refine h_tri.trans ?_
    have h_smooth_bound := Φ.wkpNorm_comp_smooth_le hp_one hp_top hΩ hΩ' k hk
      (hψ_smooth n) (hψ_compact n) (hψ_support n)
    have h_ψn_le_u : iteratedWeakSobolevNorm (d := d) k p (ψ n) Ω' ≤
        iteratedWeakSobolevNorm (d := d) k p u Ω' + ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
      have h_neg_uψn_mem : MemWkp (d := d) k p (fun x => ψ n x - u x) Ω' := by
        have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
          MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem n)
        have h_neg : MemWkp (d := d) k p (fun x => -(u x - ψ n x)) Ω' :=
          MemWkp.neg (d := d) hp_one hΩ' h_uψn_mem
        have h_eq : (fun x => -(u x - ψ n x)) = (fun x => ψ n x - u x) := by
          funext x; ring
        rw [h_eq] at h_neg; exact h_neg
      have h_eq_norm' : iteratedWeakSobolevNorm (d := d) k p (ψ n) Ω' =
          iteratedWeakSobolevNorm (d := d) k p (fun x => u x + (ψ n x - u x)) Ω' := by
        congr 1
        funext x; ring
      rw [h_eq_norm']
      have h_tri' := wkpNorm_add_le (d := d) hp_one hΩ' hu h_neg_uψn_mem
      refine h_tri'.trans ?_
      have h_diff_norm_eq :
          iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n x - u x) Ω' =
            iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' := by
        have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
          MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem n)
        have h_eq : (fun x => ψ n x - u x) =
            (fun x => (-1 : ℝ) * (u x - ψ n x)) := by funext x; ring
        rw [h_eq, wkpNorm_const_smul (d := d) hp_one hΩ' h_uψn_mem (-1)]
        simp
      rw [h_diff_norm_eq]
      exact add_le_add (le_refl _) (hψ_close n)
    have h_bound_ψn :
        iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n (Φ.toFun x)) Ω ≤
          ENNReal.ofReal K_const *
            (iteratedWeakSobolevNorm (d := d) k p u Ω' + ENNReal.ofReal
              ((1 : ℝ) / (n + 1 : ℝ))) := by
      refine h_smooth_bound.trans ?_
      exact mul_le_mul_of_nonneg_left h_ψn_le_u (zero_le)
    refine le_trans (add_le_add (le_refl _) h_bound_ψn) ?_
    rw [mul_add]
    have h_eq_RHS : ENNReal.ofReal K_const * iteratedWeakSobolevNorm (d := d) k p u Ω' = RHS := rfl
    rw [h_eq_RHS]
    have h_rearr :
        iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
            (RHS + ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ))) =
          iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
            ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) +
            RHS := by ring
    rw [h_rearr]
  have h_tendsto_first :
      Filter.Tendsto
        (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω)
        atTop (𝓝 0) :=
    hvΦ_tendsto
  have h_tendsto_second :
      Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal K_const *
          ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
        atTop (𝓝 0) := by
    have h_inner_tendsto :
        Filter.Tendsto
          (fun n : ℕ => ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
          atTop (𝓝 0) := by
      have h_real : Filter.Tendsto
          (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h_ofReal := (ENNReal.continuous_ofReal.tendsto 0).comp h_real
      rw [ENNReal.ofReal_zero] at h_ofReal
      exact h_ofReal
    set C : ℝ≥0∞ := ENNReal.ofReal K_const with hC_def
    have hC_ne_top : C ≠ ⊤ := by rw [hC_def]; exact ENNReal.ofReal_ne_top
    have h_const_mul := ENNReal.Tendsto.const_mul (a := C) (b := 0)
      h_inner_tendsto (Or.inr hC_ne_top)
    simpa using h_const_mul
  have h_tendsto_zero :
      Filter.Tendsto
        (fun n =>
          iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
          ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
        atTop (𝓝 0) := by
    have := h_tendsto_first.add h_tendsto_second
    simpa using this
  have h_tendsto_rhs :
      Filter.Tendsto
        (fun n =>
          (iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
           ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ))) +
          RHS)
        atTop (𝓝 (0 + RHS)) :=
    h_tendsto_zero.add tendsto_const_nhds
  rw [zero_add] at h_tendsto_rhs
  exact ge_of_tendsto h_tendsto_rhs (Filter.Eventually.of_forall h_bound2)


omit [NeZero d] in
theorem eLpNorm_comp_toFun_le_const
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBounded d Ω Ω')
    (f : E → ℝ) :
    eLpNorm (fun x => f (Φ.toFun x)) p (volume.restrict Ω) ≤
      ENNReal.ofReal
          ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
        eLpNorm f p (volume.restrict Ω') := by
  exact (Φ.toAtOrder (kmax := 0)).eLpNorm_comp_toFun_le_const
    hp_one hp_top hΩ f

noncomputable def wkpCompConst
    {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') (k : ℕ) (p : ℝ≥0∞) : ℝ :=
  ((Finset.range (k + 1)).sum (fun j => (Fintype.card (Fin j → Fin d) : ℝ))) *
    ((k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k) *
    ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
    ((k + 1 : ℕ) : ℝ)


theorem wkpNorm_comp_smooth_le
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω Ω' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBounded d Ω Ω') (k : ℕ)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω') :
    iteratedWeakSobolevNorm (d := d) k p (fun x => ψ (Φ.toFun x)) Ω ≤
      ENNReal.ofReal (wkpCompConst (d := d) Φ k p) *
        iteratedWeakSobolevNorm (d := d) k p ψ Ω' := by
  exact (Φ.toAtOrder (kmax := k)).wkpNorm_comp_smooth_le
    hp_one hp_top hΩ hΩ' k (le_refl k) hψ_smooth hψ_compact hψ_support

theorem MemWkp.comp_smoothDiffeoBounded
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω Ω' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω')
    (hu_compactSupport : HasCompactSupport u)
    (hu_support : tsupport u ⊆ Ω') :
    MemWkp (d := d) k p (fun x => u (Φ.toFun x)) Ω := by
  exact MemWkp.comp_smoothDiffeoBoundedAtOrder k (le_refl k)
    hp_one hp_top hΩ hΩ' (Φ.toAtOrder (kmax := k))
    hu hu_compactSupport hu_support

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
