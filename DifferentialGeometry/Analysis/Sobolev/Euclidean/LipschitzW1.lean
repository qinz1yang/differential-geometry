import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Lipschitz functions in first-order Sobolev spaces

This file supplies the Euclidean weak-derivative entrance used by nonsmooth
cutoff constructions.  The weak partial derivative is the line derivative in
the corresponding coordinate direction.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A locally Lipschitz Euclidean function with compact support and a global
amplitude bound is globally Lipschitz. -/
theorem lip_of_local_comp
    {f : E → ℝ} {B : ℝ≥0}
    (hf : LocallyLipschitz f) (hf_supp : HasCompactSupport f)
    (hB : ∀ x, edist (f x) 0 ≤ B) :
    ∃ C : ℝ≥0, LipschitzWith C f := by
  let K : Set E := tsupport f
  let U : Set E := Metric.cthickening 1 K
  have hU_compact : IsCompact U := by
    exact hf_supp.cthickening
  obtain ⟨C, hC⟩ :=
    hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hU_compact
  refine ⟨max C B, ?_⟩
  intro x y
  have hK_sub : K ⊆ U := by
    exact Metric.self_subset_cthickening K
  have hzero {z : E} (hz : z ∉ K) : f z = 0 := by
    by_contra hne
    exact hz (subset_tsupport f hne)
  by_cases hxU : x ∈ U
  · by_cases hyU : y ∈ U
    · refine (hC hxU hyU).trans ?_
      gcongr
      exact le_max_left C B
    · by_cases hxK : x ∈ K
      · have hyK : y ∉ K := fun hyK ↦ hyU (hK_sub hyK)
        have hxy : (1 : ℝ≥0∞) ≤ edist x y := by
          have hInf : (1 : ℝ≥0∞) < Metric.infEDist y K := by
            simpa only [U, Metric.mem_cthickening_iff, ENNReal.ofReal_one,
              not_le] using hyU
          exact (le_of_lt hInf).trans
            (by simpa only [edist_comm] using Metric.infEDist_le_edist_of_mem hxK)
        rw [hzero hyK]
        exact (hB x).trans <| by
          simpa only [mul_one] using
            mul_le_mul (show (B : ℝ≥0∞) ≤ max C B by exact_mod_cast le_max_right C B)
              hxy (by positivity) (by positivity)
      · rw [hzero hxK, hzero (fun hyK ↦ hyU (hK_sub hyK)), edist_self]
        exact bot_le
  · have hxK : x ∉ K := fun hxK ↦ hxU (hK_sub hxK)
    by_cases hyU : y ∈ U
    · by_cases hyK : y ∈ K
      · have hyx : (1 : ℝ≥0∞) ≤ edist x y := by
          have hInf : (1 : ℝ≥0∞) < Metric.infEDist x K := by
            simpa only [U, Metric.mem_cthickening_iff, ENNReal.ofReal_one,
              not_le] using hxU
          exact (le_of_lt hInf).trans (Metric.infEDist_le_edist_of_mem hyK)
        rw [hzero hxK, edist_comm]
        exact (hB y).trans <| by
          simpa only [mul_one] using
            mul_le_mul (show (B : ℝ≥0∞) ≤ max C B by exact_mod_cast le_max_right C B)
              hyx (by positivity) (by positivity)
      · rw [hzero hxK, hzero hyK, edist_self]
        exact bot_le
    · rw [hzero hxK, hzero (fun hyK ↦ hyU (hK_sub hyK)), edist_self]
      exact bot_le

/-- A coordinate line derivative of a Lipschitz function is its weak partial
derivative on every set. -/
theorem hasWeakPart_of_lip
    {C : ℝ≥0} {f : E → ℝ} {Omega : Set E}
    (hf : LipschitzWith C f) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) f Omega := by
  intro phi hphi hphi_supp hphi_sub
  obtain ⟨D, hphi_lip⟩ : ∃ D, LipschitzWith D phi :=
    ContDiff.lipschitzWith_of_hasCompactSupport hphi_supp hphi (by simp)
  let ei : E := EuclideanSpace.single i 1
  have hline_phi : ∀ x, lineDeriv ℝ phi x (-ei) = -fderiv ℝ phi x ei := by
    intro x
    rw [(hphi.differentiable (by simp) x).lineDeriv_eq_fderiv]
    simp only [map_neg]
  have hderiv_sub : tsupport (fun x => fderiv ℝ phi x ei) ⊆ Omega :=
    (tsupport_fderiv_apply_subset ℝ ei).trans hphi_sub
  have hibp :=
    LipschitzWith.integral_lineDeriv_mul_eq
      (μ := volume) hf hphi_lip hphi_supp ei
  simp_rw [hline_phi] at hibp
  have hleft_zero :
      ∀ x, x ∉ Omega → lineDeriv ℝ f x ei * phi x = 0 := by
    intro x hx
    have hphi_x : phi x = 0 := by
      by_contra hne
      exact hx (hphi_sub (subset_tsupport _ hne))
    simp only [hphi_x, mul_zero]
  have hright_zero :
      ∀ x, x ∉ Omega → (-fderiv ℝ phi x ei) * f x = 0 := by
    intro x hx
    have hderiv_x : fderiv ℝ phi x ei = 0 := by
      by_contra hne
      exact hx (hderiv_sub (subset_tsupport _ hne))
    simp only [hderiv_x, neg_zero, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero] at hibp
  have hibp' :
      ∫ x in Omega, lineDeriv ℝ f x ei * phi x =
        -∫ x in Omega, f x * fderiv ℝ phi x ei := by
    rw [show (∫ x in Omega, (-fderiv ℝ phi x ei) * f x) =
        -∫ x in Omega, f x * fderiv ℝ phi x ei by
      simp_rw [neg_mul, mul_comm]
      rw [integral_neg]] at hibp
    exact hibp
  have hneg := congrArg Neg.neg hibp'
  simpa only [ei, neg_neg] using hneg.symm

/-- A globally Lipschitz, compactly supported function belongs to
`W^{1,p}` on every set. -/
theorem memW1p_of_lip
    {p : ℝ≥0∞} {C : ℝ≥0} {f : E → ℝ} {Omega : Set E}
    (hf : LipschitzWith C f) (hf_supp : HasCompactSupport f) :
    DeGiorgi.MemW1p p f Omega := by
  refine ⟨(hf.continuous.memLp_of_hasCompactSupport hf_supp).restrict Omega, ?_⟩
  intro i
  let ei : E := EuclideanSpace.single i 1
  let gi : E → ℝ := fun x => lineDeriv ℝ f x ei
  have hgi_top : MemLp gi ∞ volume := by
    simpa only [gi] using hf.memLp_lineDeriv (μ := volume) ei
  have hgi_zero : ∀ x, x ∉ tsupport f → gi x = 0 := by
    intro x hx
    have hline :=
      ((HasFDerivAt.of_notMem_tsupport ℝ hx).hasLineDerivAt ei).lineDeriv
    simpa only [gi, ContinuousLinearMap.zero_apply] using hline
  have hgi_mem : MemLp gi p volume :=
    hgi_top.mono_exponent_of_measure_support_ne_top
      hgi_zero hf_supp.measure_lt_top.ne le_top
  refine ⟨gi, hgi_mem.restrict Omega, ?_⟩
  simpa only [gi, ei] using hasWeakPart_of_lip (Omega := Omega) hf i

/-- At almost every point of an open set, the classical coordinate partial of
a globally Lipschitz compactly supported function agrees with its chosen weak
partial. -/
theorem fderiv_ae_chosen
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E} (hOmega : IsOpen Omega)
    {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) (hf_supp : HasCompactSupport f) (i : Fin d) :
    (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict Omega]
      chosenWeakPartial' p i f Omega := by
  have hf_mem : DeGiorgi.MemW1p p f Omega :=
    memW1p_of_lip hf hf_supp
  have hline : DeGiorgi.HasWeakPartialDeriv i
      (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) f Omega :=
    hasWeakPart_of_lip hf i
  have hchosen : DeGiorgi.HasWeakPartialDeriv i
      (chosenWeakPartial' p i f Omega) f Omega :=
    chosenWeakPartial'_isWeakPartial_of_mem hf_mem i
  have hline_loc : LocallyIntegrable
      (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1))
      (volume.restrict Omega) :=
    (hf.locallyIntegrable_lineDeriv (EuclideanSpace.single i 1)).mono_measure
      Measure.restrict_le_self
  have hchosen_loc : LocallyIntegrable
      (chosenWeakPartial' p i f Omega) (volume.restrict Omega) :=
    (chosenWeakPartial'_memLp_of_mem hf_mem i).locallyIntegrable hp
  have hline_eq :
      (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict Omega]
        chosenWeakPartial' p i f Omega :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hOmega
      hline hchosen hline_loc hchosen_loc
  have hfderiv_eq :
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict Omega]
        (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) := by
    filter_upwards [ae_mono Measure.restrict_le_self hf.ae_differentiableAt] with x hx
    exact hx.lineDeriv_eq_fderiv.symm
  exact hfderiv_eq.trans hline_eq

/-- The `L²` norm of the Euclidean length of the classical coordinate partials
of a globally Lipschitz, compactly supported function is controlled by its
first-order Sobolev norm on any open set. -/
theorem partials_l2_le_wkp
    {Omega : Set E} (hOmega : IsOpen Omega) {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) (hf_supp : HasCompactSupport f) :
    eLpNorm (fun x : E => Real.sqrt (∑ i : Fin d,
        ((fderiv ℝ f x) (EuclideanSpace.single i 1)) ^ 2)) 2
        (volume.restrict Omega) ≤
      wkpNorm (d := d) 1 2 f Omega := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hcomp : ∀ i : Fin d,
      AEStronglyMeasurable
        (fun x : E => (fderiv ℝ f x) (EuclideanSpace.single i 1))
        (volume.restrict Omega) := by
    intro i
    exact ((measurable_fderiv_apply_const ℝ f
      (EuclideanSpace.single i 1)).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
  have hpoint (x : E) :
      Real.sqrt (∑ i : Fin d,
          ((fderiv ℝ f x) (EuclideanSpace.single i 1)) ^ 2) ≤
        ∑ i : Fin d,
        ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖ := by
    have hsquares :
        (∑ i : Fin d,
            ((fderiv ℝ f x) (EuclideanSpace.single i 1)) ^ 2) ≤
          (∑ i : Fin d,
            ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖) ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (Finset.sum_sq_le_sq_sum_of_nonneg
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
            abs_nonneg ((fderiv ℝ f x) (EuclideanSpace.single i 1))))
    refine (Real.sqrt_le_sqrt hsquares).trans_eq ?_
    rw [Real.sqrt_sq]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hmono :
      eLpNorm (fun x : E => Real.sqrt (∑ i : Fin d,
          ((fderiv ℝ f x) (EuclideanSpace.single i 1)) ^ 2)) 2
          (volume.restrict Omega) ≤
        eLpNorm (fun x : E => ∑ i : Fin d,
          ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖) 2
          (volume.restrict Omega) := by
    apply eLpNorm_mono_real
    intro x
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hpoint x
  refine hmono.trans ?_
  have hsum := eLpNorm_sum_le (μ := volume.restrict Omega) (p := (2 : ℝ≥0∞))
    (s := (Finset.univ : Finset (Fin d)))
    (f := fun i x => ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖)
    (fun i _ => (hcomp i).norm) hp
  have hfun : (fun x : E => ∑ i : Fin d,
      ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖) =
      ∑ i : Fin d, fun x : E =>
        ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖ := by
    funext x
    simp only [Finset.sum_apply]
  rw [hfun]
  refine hsum.trans ?_
  have heach (i : Fin d) :
      eLpNorm (fun x : E =>
          ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖) 2
          (volume.restrict Omega) =
        eLpNorm (chosenWeakPartial' (d := d) (2 : ℝ≥0∞) i f Omega) 2
          (volume.restrict Omega) := by
    rw [eLpNorm_norm]
    exact eLpNorm_congr_ae (fderiv_ae_chosen hp hOmega hf hf_supp i)
  calc
    (∑ i : Fin d, eLpNorm (fun x : E =>
        ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖) 2
        (volume.restrict Omega)) =
      ∑ i : Fin d,
        eLpNorm (chosenWeakPartial' (d := d) (2 : ℝ≥0∞) i f Omega) 2
          (volume.restrict Omega) :=
        Finset.sum_congr rfl (fun i _ => heach i)
    _ ≤ wkpNorm (d := d) 1 2 f Omega := by
      have hblock :
          (∑ β : Fin 1 → Fin d,
              eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 1 β f Omega) 2
                (volume.restrict Omega)) =
            ∑ i : Fin d,
              eLpNorm (chosenWeakPartial' (d := d) (2 : ℝ≥0∞) i f Omega) 2
                (volume.restrict Omega) := by
        let e : (Fin 1 → Fin d) ≃ Fin d :=
          { toFun := fun β => β 0
            invFun := fun i _ => i
            left_inv := fun β => by
              funext j
              rw [Subsingleton.elim j 0]
            right_inv := fun _ => rfl }
        exact Fintype.sum_equiv e _ _ fun β => by
          rw [iterWeakPartial_succ]
          simp only [iterWeakPartial_zero]
          rfl
      rw [wkpNorm_eq_sum, Finset.sum_range_succ, Finset.sum_range_one, hblock]
      exact le_add_of_nonneg_left (zero_le _)

/-- A globally Lipschitz, compactly supported function belongs to the
first-order iterated Sobolev space on every set. -/
theorem memWkp_one_of_lip
    {p : ℝ≥0∞} {C : ℝ≥0} {f : E → ℝ} {Omega : Set E}
    (hf : LipschitzWith C f) (hf_supp : HasCompactSupport f) :
    MemWkp (d := d) 1 p f Omega :=
  MemWkp.one_iff_memW1p.mpr (memW1p_of_lip hf hf_supp)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
