import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.WeakDerivativeBound
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density

noncomputable section

open MeasureTheory Metric Filter Set Function
open scoped ENNReal Topology ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_mul_cutoff
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω) :
    MemLp (fun x => η x * u x) 2 volume := by
  have hm : MemLp (fun x => η x * u x) 2 (volume.restrict Ω) :=
    ((hη.memLp_of_hasCompactSupport hηc : MemLp η ∞ volume).restrict Ω).fun_mul hu
  have hi := (memLp_indicator_iff_restrict hΩ).mpr hm
  have heq : Ω.indicator (fun x => η x * u x) = fun x => η x * u x := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h)), zero_mul]
  rwa [heq] at hi

theorem hasWeakPartialDeriv_mul_cutoff_univ
    {Ω : Set E} (hΩ : IsOpen Ω) {u g η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    DeGiorgi.HasWeakPartialDeriv k
      (fun x => η x * g x + fderiv ℝ η x (EuclideanSpace.single k 1) * u x)
      (fun x => η x * u x) univ := by
  let e : E := EuclideanSpace.single k 1
  let Dη : E → ℝ := fun x => fderiv ℝ η x e
  have hDη : Continuous Dη :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDηc : HasCompactSupport Dη := hηc.fderiv_apply (𝕜 := ℝ) e
  have hDηs : tsupport Dη ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ e).trans hηs
  have hηu := memLp_mul_cutoff hΩ.measurableSet hu hη.continuous hηc hηs
  have hηg := memLp_mul_cutoff hΩ.measurableSet hg hη.continuous hηc hηs
  have hDηu := memLp_mul_cutoff hΩ.measurableSet hu hDη hDηc hDηs
  intro φ hφ hφc _
  have hηφ : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * φ x) := hη.mul hφ
  have hηφc : HasCompactSupport (fun x => η x * φ x) := hηc.mul_right
  have hηφs : tsupport (fun x => η x * φ x) ⊆ Ω :=
    (tsupport_smul_subset_left η φ).trans hηs
  have hw := hweak (fun x => η x * φ x) hηφ hηφc hηφs
  have hfd (x : E) : fderiv ℝ (fun y => η y * φ y) x e =
      η x * fderiv ℝ φ x e + Dη x * φ x := by
    rw [fderiv_fun_mul (hη.differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul, Dη]
    ring
  have hL : Integrable (fun x => η x * u x * fderiv ℝ φ x e) volume :=
    hηu.integrable_mul ((hφ.continuous_fderiv (by simp)).clm_apply
      continuous_const |>.memLp_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) e) :
        MemLp (fun x => fderiv ℝ φ x e) 2 volume)
  have hC : Integrable (fun x => Dη x * u x * φ x) volume :=
    hDηu.integrable_mul (hφ.continuous.memLp_of_hasCompactSupport hφc : MemLp φ 2 volume)
  have hR : Integrable (fun x => η x * g x * φ x) volume :=
    hηg.integrable_mul (hφ.continuous.memLp_of_hasCompactSupport hφc : MemLp φ 2 volume)
  have hzero (x : E) (hx : x ∉ Ω) : η x = 0 ∧ Dη x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h)),
      image_eq_zero_of_notMem_tsupport (fun h => hx (hDηs h))⟩
  have hleft : (∫ x in Ω, u x * fderiv ℝ (fun y => η y * φ y) x e) =
      (∫ x, η x * u x * fderiv ℝ φ x e) + ∫ x, Dη x * u x * φ x := by
    calc
      _ = ∫ x in Ω, (η x * u x * fderiv ℝ φ x e + Dη x * u x * φ x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hfd]
        ring
      _ = ∫ x, (η x * u x * fderiv ℝ φ x e + Dη x * u x * φ x) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rcases hzero x hx with ⟨h1, h2⟩
          simp only [h1, h2, zero_mul, zero_add]
      _ = _ := integral_add hL hC
  have hright : (∫ x in Ω, g x * (η x * φ x)) = ∫ x, η x * g x * φ x := by
    calc
      _ = ∫ x in Ω, η x * g x * φ x := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp only [(hzero x hx).1, zero_mul]
  rw [hleft, hright] at hw
  simp only [Measure.restrict_univ]
  change (∫ x, η x * u x * fderiv ℝ φ x e) =
    -∫ x, (η x * g x + Dη x * u x) * φ x
  simp_rw [add_mul]
  rw [integral_add hR hC]
  linarith

theorem eLpNorm_diffQuot_le_eLpNorm_weakPartial_local
    {Ω Ω' Ω'' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {u g : E → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    {h0 : ℝ} (hh0 : 0 < h0) (hthick : cthickening h0 (closure Ω'') ⊆ Ω')
    {h : ℝ} (hh : |h| ≤ h0) :
    eLpNorm (diffQuot k h u) 2 (volume.restrict Ω'') ≤
      eLpNorm g 2 (volume.restrict Ω') := by
  by_cases hhzero : h = 0
  · simp only [hhzero, diffQuot_zero_h, eLpNorm_zero, zero_le]
  obtain ⟨δ, η, hδ, _, hη, hηc, _, hηone, hηs⟩ :=
    Euclidean.exists_smooth_cutoff_with_neighborhood hΩ'c hΩ hΩ'Ω
  let v : E → ℝ := fun x => η x * u x
  let w : E → ℝ := fun x => η x * g x +
    fderiv ℝ η x (EuclideanSpace.single k 1) * u x
  have hv : MemLp v 2 volume := memLp_mul_cutoff hΩ.measurableSet hu hη.continuous hηc hηs
  have hDη : Continuous (fun x => fderiv ℝ η x (EuclideanSpace.single k 1)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDηc := hηc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)
  have hDηs : tsupport (fun x => fderiv ℝ η x (EuclideanSpace.single k 1)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single k 1)).trans hηs
  have hw : MemLp w 2 volume :=
    (memLp_mul_cutoff hΩ.measurableSet hg hη.continuous hηc hηs).add
      (memLp_mul_cutoff hΩ.measurableSet hu hDη hDηc hDηs)
  have hwp : DeGiorgi.HasWeakPartialDeriv k w v univ :=
    hasWeakPartialDeriv_mul_cutoff_univ hΩ hu hg k hweak hη hηc hηs
  have hηeq (x : E) (hx : x ∈ Ω') : η x = 1 :=
    hηone x (self_subset_cthickening (closure Ω') (subset_closure hx))
  have hweq (x : E) (hx : x ∈ Ω') : w x = g x := by
    dsimp only [w]
    rw [hηeq x hx,
      Euclidean.fderiv_cutoff_apply_zero_on_cthickening hδ hηone (subset_closure hx) k]
    ring
  have hveq (x : E) (hx : x ∈ Ω') : v x = u x := by
    dsimp only [v]
    rw [hηeq x hx, one_mul]
  have hdq (x : E) (hx : x ∈ Ω'') : diffQuot k h v x = diffQuot k h u x := by
    have hx' : x ∈ Ω' := hthick (self_subset_cthickening (closure Ω'') (subset_closure hx))
    have hxshift : x + h • EuclideanSpace.single k 1 ∈ Ω' := by
      apply hthick
      apply closedBall_subset_cthickening (subset_closure hx) h0
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      simpa only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] using hh
    simp only [diffQuot_apply_of_ne k hhzero, hveq x hx', hveq _ hxshift]
  calc
    eLpNorm (diffQuot k h u) 2 (volume.restrict Ω'') =
        eLpNorm (diffQuot k h v) 2 (volume.restrict Ω'') :=
      eLpNorm_congr_ae ((ae_restrict_mem hΩ''.measurableSet).mono fun x hx => (hdq x hx).symm)
    _ ≤ eLpNorm w 2 (volume.restrict Ω') :=
      eLpNorm_diffQuot_le_eLpNorm_weakPartial hv hw k hwp hΩ' hΩ'' hΩ''c hh0 hthick hhzero hh
    _ = eLpNorm g 2 (volume.restrict Ω') :=
      eLpNorm_congr_ae ((ae_restrict_mem hΩ'.measurableSet).mono hweq)

end DifferentialGeometry.Analysis.Sobolev
