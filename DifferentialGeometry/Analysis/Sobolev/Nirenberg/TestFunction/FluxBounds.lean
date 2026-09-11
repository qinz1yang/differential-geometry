import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Integration
import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn


noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

private theorem abs_mul_le_young (p q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |p * q| ≤ ε * p^2 + (4 * ε)⁻¹ * q^2 := by
  have h := two_mul_le_add_mul_sq (a := |p|) (b := |q|) (by linarith : 0 < 2 * ε)
  rw [sq_abs, sq_abs] at h
  rw [abs_mul]
  have heq : (2 * ε)⁻¹ = 2 * (4 * ε)⁻¹ := by
    field_simp
    norm_num
  rw [heq] at h
  linarith

private theorem abs_two_mul_le_young (c p q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |2 * c * p * q| ≤ ε * p^2 + ε⁻¹ * c^2 * q^2 := by
  have hy := abs_mul_le_young p (2 * c * q) hε
  have hsq : (4 * ε)⁻¹ * (2 * c * q)^2 = ε⁻¹ * c^2 * q^2 := by
    field_simp
    ring_nf
  rw [hsq] at hy
  convert hy using 1
  ring_nf

private theorem nirenberg_principal_flux_remainder_le
    (a b e t p q z w : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |(a * p + b * e * z) * (q + 2 * t * w) - a * p * q| ≤
      ε * p^2 + ε * q^2 + ((4 * ε)⁻¹ * (b * e)^2 + (b * e * t)^2) * z^2 +
        (ε⁻¹ * (a * t)^2 + 1) * w^2 := by
  have h1 := abs_two_mul_le_young (a * t) p w hε
  have h2 := abs_mul_le_young q (b * e * z) hε
  have h3 : |2 * (b * e * t) * z * w| ≤ (b * e * t)^2 * z^2 + w^2 := by
    have h := two_mul_le_add_sq (|(b * e * t) * z|) (|w|)
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), sq_abs, mul_pow, mul_assoc] using h
  have halg : (a * p + b * e * z) * (q + 2 * t * w) - a * p * q =
      2 * (a * t) * p * w + q * (b * e * z) + 2 * (b * e * t) * z * w := by ring_nf
  rw [halg]
  have ht := (abs_add_le (2 * (a * t) * p * w + q * (b * e * z))
    (2 * (b * e * t) * z * w)).trans
      (add_le_add (abs_add_le (2 * (a * t) * p * w) (q * (b * e * z))) (le_refl _))
  have h := ht.trans (add_le_add (add_le_add h1 h2) h3)
  nlinarith [h]

private theorem square_mul_le (c C z : ℝ) (hc : |c| ≤ C) : (c * z)^2 ≤ C^2 * z^2 := by
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [← sq_abs c]
  exact (sq_le_sq₀ (abs_nonneg c) ((abs_nonneg c).trans hc)).mpr hc

private theorem nirenberg_principal_flux_remainder_le_of_bounds
    (a b e t p q z w L : ℝ) {ε : ℝ} (hε : 0 < ε)
    (ha : |a| ≤ L) (hb : |b| ≤ L) (he : |e| ≤ 1) (ht : |t| ≤ L) :
    |(a * p + b * e * z) * (q + 2 * t * w) - a * p * q| ≤
      ε * p^2 + ε * q^2 + ((4 * ε)⁻¹ * L^2 + L^4) * z^2 +
        (ε⁻¹ * L^4 + 1) * w^2 := by
  have hbe : |b * e| ≤ L := by
    calc
      _ = |b| * |e| := abs_mul _ _
      _ ≤ L * 1 := mul_le_mul hb he (abs_nonneg _) ((abs_nonneg a).trans ha)
      _ = L := mul_one _
  have hbet : |b * e * t| ≤ L^2 := by
    rw [abs_mul]
    exact (mul_le_mul hbe ht (abs_nonneg _) ((abs_nonneg a).trans ha)).trans_eq (pow_two L).symm
  have hat : |a * t| ≤ L^2 := by
    rw [abs_mul]
    exact (mul_le_mul ha ht (abs_nonneg _) ((abs_nonneg a).trans ha)).trans_eq (pow_two L).symm
  have h1 := square_mul_le (b * e) L z hbe
  have h2 := square_mul_le (b * e * t) (L^2) z hbet
  have h3 := square_mul_le (a * t) (L^2) w hat
  have hε1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (by positivity : 0 ≤ 4 * ε))
  have hε3 := mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hε.le)
  have hbase := nirenberg_principal_flux_remainder_le a b e t p q z w hε
  nlinarith [hbase]

private theorem nirenberg_lower_order_flux_le_of_bounds
    (a b e p z w L : ℝ) {ε : ℝ} (hε : 0 < ε)
    (ha : |a| ≤ L) (hb : |b| ≤ L) (he : |e| ≤ 1) :
    |(a * p + b * e * z) * (e * w)| ≤
      ε * p^2 + L^2 / 2 * z^2 + ((4 * ε)⁻¹ * L^2 + 1 / 2) * w^2 := by
  have he0 := (abs_nonneg a).trans ha
  have hae : |a * e| ≤ L := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul ha he (abs_nonneg _) he0
  have he2 : |e * e| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul he he (abs_nonneg _) zero_le_one
  have hbee : |b * (e * e)| ≤ L := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hb he2 (abs_nonneg _) he0
  have h1 := abs_mul_le_young p (a * e * w) hε
  have hsq1 := square_mul_le (a * e) L w hae
  have hsq1' := mul_le_mul_of_nonneg_left hsq1 (inv_nonneg.mpr (by positivity : 0 ≤ 4 * ε))
  have h2 : |b * (e * e) * z * w| ≤ L^2 / 2 * z^2 + 1 / 2 * w^2 := by
    have h := two_mul_le_add_sq (|b * (e * e) * z|) (|w|)
    rw [sq_abs, sq_abs] at h
    have hs := square_mul_le (b * (e * e)) L z hbee
    rw [abs_mul]
    nlinarith
  have heq : (a * p + b * e * z) * (e * w) = p * (a * e * w) + b * (e * e) * z * w := by ring_nf
  rw [heq]
  have ht := abs_add_le (p * (a * e * w)) (b * (e * e) * z * w)
  nlinarith


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem memLp_flux_factor
    {a b e p z : α → ℝ}
    (ha : MemLp a ∞ μ) (hb : MemLp b ∞ μ) (he : MemLp e ∞ μ)
    (hp : MemLp p 2 μ) (hz : MemLp z 2 μ) :
    MemLp (fun x => a x * p x + b x * e x * z x) 2 μ :=
  (hp.mul' (r := 2) ha).add (hz.mul' (r := 2) (he.mul' (r := ∞) hb))

theorem abs_integral_flux_sub_integral_principal_le
    {a b e t p q z w : α → ℝ} {L ε : ℝ}
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (he : AEStronglyMeasurable e μ) (ht : AEStronglyMeasurable t μ)
    (hp : MemLp p 2 μ) (hq : MemLp q 2 μ) (hz : MemLp z 2 μ) (hw : MemLp w 2 μ)
    (haL : ∀ᵐ x ∂μ, |a x| ≤ L) (hbL : ∀ᵐ x ∂μ, |b x| ≤ L)
    (heL : ∀ᵐ x ∂μ, |e x| ≤ 1) (htL : ∀ᵐ x ∂μ, |t x| ≤ L)
    (hε : 0 < ε) :
    |(∫ x, (a x * p x + b x * e x * z x) * (q x + 2 * t x * w x) ∂μ) -
      ∫ x, a x * p x * q x ∂μ| ≤
      ε * (∫ x, p x ^ 2 ∂μ) + ε * (∫ x, q x ^ 2 ∂μ) +
        ((4 * ε)⁻¹ * L ^ 2 + L ^ 4) * (∫ x, z x ^ 2 ∂μ) +
        (ε⁻¹ * L ^ 4 + 1) * (∫ x, w x ^ 2 ∂μ) := by
  have haLp : MemLp a ∞ μ := memLp_top_of_bound ha L (by simpa only [Real.norm_eq_abs] using haL)
  have hbLp : MemLp b ∞ μ := memLp_top_of_bound hb L (by simpa only [Real.norm_eq_abs] using hbL)
  have heLp : MemLp e ∞ μ := memLp_top_of_bound he 1 (by simpa only [Real.norm_eq_abs] using heL)
  have htLp : MemLp t ∞ μ := memLp_top_of_bound ht L (by simpa only [Real.norm_eq_abs] using htL)
  have hf1 := memLp_flux_factor haLp hbLp heLp hp hz
  have hf2 : MemLp (fun x => q x + 2 * t x * w x) 2 μ :=
    hq.add (hw.mul' (r := 2) (htLp.const_mul 2))
  have hflux : Integrable
      (fun x => (a x * p x + b x * e x * z x) * (q x + 2 * t x * w x)) μ :=
    hf1.integrable_mul hf2
  have hprin : Integrable (fun x => a x * p x * q x) μ :=
    (hp.mul' (r := 2) haLp).integrable_mul hq
  rw [← integral_sub hflux hprin]
  refine abs_integral_le_integral_abs.trans ?_
  calc
    _ ≤ ∫ x, ε * p x ^ 2 + ε * q x ^ 2 +
        ((4 * ε)⁻¹ * L ^ 2 + L ^ 4) * z x ^ 2 +
        (ε⁻¹ * L ^ 4 + 1) * w x ^ 2 ∂μ := by
      apply integral_mono_ae (hflux.sub hprin).abs
        (((hp.integrable_sq.const_mul ε).add (hq.integrable_sq.const_mul ε)).add
          (hz.integrable_sq.const_mul _ ) |>.add (hw.integrable_sq.const_mul _))
      filter_upwards [haL, hbL, heL, htL] with x hax hbx hex htx
      exact nirenberg_principal_flux_remainder_le_of_bounds
        (a x) (b x) (e x) (t x) (p x) (q x) (z x) (w x) L hε hax hbx hex htx
    _ = _ := by
      have hpq : Integrable (fun x => ε * p x ^ 2 + ε * q x ^ 2) μ :=
        (hp.integrable_sq.const_mul ε).add (hq.integrable_sq.const_mul ε)
      have hpqz : Integrable (fun x => ε * p x ^ 2 + ε * q x ^ 2 +
          ((4 * ε)⁻¹ * L ^ 2 + L ^ 4) * z x ^ 2) μ :=
        hpq.add (hz.integrable_sq.const_mul _)
      rw [integral_add hpqz (hw.integrable_sq.const_mul (ε⁻¹ * L ^ 4 + 1))]
      rw [integral_add hpq (hz.integrable_sq.const_mul ((4 * ε)⁻¹ * L ^ 2 + L ^ 4))]
      rw [integral_add (hp.integrable_sq.const_mul ε) (hq.integrable_sq.const_mul ε)]
      simp only [integral_const_mul]

theorem abs_integral_lower_order_flux_le
    {a b e p z w : α → ℝ} {L ε : ℝ}
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (he : AEStronglyMeasurable e μ)
    (hp : MemLp p 2 μ) (hz : MemLp z 2 μ) (hw : MemLp w 2 μ)
    (haL : ∀ᵐ x ∂μ, |a x| ≤ L) (hbL : ∀ᵐ x ∂μ, |b x| ≤ L)
    (heL : ∀ᵐ x ∂μ, |e x| ≤ 1) (hε : 0 < ε) :
    |∫ x, (a x * p x + b x * e x * z x) * (e x * w x) ∂μ| ≤
      ε * (∫ x, p x ^ 2 ∂μ) + L ^ 2 / 2 * (∫ x, z x ^ 2 ∂μ) +
        ((4 * ε)⁻¹ * L ^ 2 + 1 / 2) * (∫ x, w x ^ 2 ∂μ) := by
  have haLp : MemLp a ∞ μ := memLp_top_of_bound ha L (by simpa only [Real.norm_eq_abs] using haL)
  have hbLp : MemLp b ∞ μ := memLp_top_of_bound hb L (by simpa only [Real.norm_eq_abs] using hbL)
  have heLp : MemLp e ∞ μ := memLp_top_of_bound he 1 (by simpa only [Real.norm_eq_abs] using heL)
  have hf1 := memLp_flux_factor haLp hbLp heLp hp hz
  have hflux := hf1.integrable_mul (hw.mul' (r := 2) heLp)
  refine abs_integral_le_integral_abs.trans ?_
  calc
    _ ≤ ∫ x, ε * p x ^ 2 + L ^ 2 / 2 * z x ^ 2 +
        ((4 * ε)⁻¹ * L ^ 2 + 1 / 2) * w x ^ 2 ∂μ := by
      apply integral_mono_ae hflux.abs
        (((hp.integrable_sq.const_mul ε).add (hz.integrable_sq.const_mul _)).add
          (hw.integrable_sq.const_mul _))
      filter_upwards [haL, hbL, heL] with x hax hbx hex
      exact nirenberg_lower_order_flux_le_of_bounds
        (a x) (b x) (e x) (p x) (z x) (w x) L hε hax hbx hex
    _ = _ := by
      have hpz : Integrable (fun x => ε * p x ^ 2 + L ^ 2 / 2 * z x ^ 2) μ :=
        (hp.integrable_sq.const_mul ε).add (hz.integrable_sq.const_mul _)
      rw [integral_add hpz (hw.integrable_sq.const_mul ((4 * ε)⁻¹ * L ^ 2 + 1 / 2))]
      rw [integral_add (hp.integrable_sq.const_mul ε) (hz.integrable_sq.const_mul (L ^ 2 / 2))]
      simp only [integral_const_mul]

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

noncomputable section

open Metric Set

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem translate_mem_of_support
    {Ω : Set E} {η : E → ℝ} (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) {x : E} (hx : x ∈ tsupport η) :
    x + h • EuclideanSpace.single k (1 : ℝ) ∈ Ω := by
  apply hηs
  apply closedBall_subset_cthickening hx |h|
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
  simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]

private theorem memLp_indicator_translate_coeff
    {Ω : Set E} {η c : E → ℝ} (hηc : HasCompactSupport η)
    (hc : ContinuousOn c Ω) (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    MemLp ((tsupport η).indicator (translate k h c)) ∞ volume := by
  have hcont : ContinuousOn (translate k h c) (tsupport η) := by
    let shift : E → E := fun x => x + h • EuclideanSpace.single k 1
    have hs : Continuous shift := continuous_id.add continuous_const
    exact hc.comp hs.continuousOn (fun x hx => translate_mem_of_support k h hηs hx)
  exact (memLp_indicator_iff_restrict (isClosed_tsupport η).measurableSet).mpr
    (hcont.memLp_top_of_isCompact hηc (isClosed_tsupport η).measurableSet)

private theorem integral_sum_quadratic_ge
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {ι : Type*} [Fintype ι]
    (A : ι → ι → α → ℝ) (v : ι → α → ℝ) {lam : ℝ}
    (hv : ∀ i, MemLp (v i) 2 μ) (hA : ∀ i j, MemLp (A i j) ∞ μ)
    (hc : ∀ x, lam * ∑ i, (v i x) ^ 2 ≤ ∑ i, ∑ j, A i j x * v i x * v j x) :
    lam * (∫ x, ∑ i, (v i x) ^ 2 ∂μ) ≤
      ∑ i, ∑ j, ∫ x, A i j x * v i x * v j x ∂μ := by
  have hint (i j) : Integrable (fun x => A i j x * v i x * v j x) μ :=
    ((hv i).mul' (r := 2) (hA i j)).integrable_mul (hv j)
  rw [← integral_const_mul]
  simp_rw [← integral_finsetSum _ (fun j _ => hint _ j)]
  rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  exact integral_mono ((integrable_finsetSum _ (fun i _ => (hv i).integrable_sq)).const_mul lam)
    (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))) hc

theorem integral_shifted_principal_ge_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {g : Fin d → E → ℝ} {η : E → ℝ}
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η)
    {A : Fin d → Fin d → E → ℝ} (hA : ∀ i j, ContinuousOn (A i j) Ω)
    {lam : ℝ} (hcoer : ∀ y ∈ Ω, ∀ ξ : Fin d → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, A i j y * ξ i * ξ j)
    (k : Fin d) (h : ℝ) (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    lam * (∫ x, (η x)^2 * ∑ i, (diffQuot k h (g i) x)^2) ≤
      ∑ i, ∑ j, ∫ x, translate k h (A i j) x * (η x)^2 *
        diffQuot k h (g i) x * diffQuot k h (g j) x := by
  let v := fun i x => η x * diffQuot k h (g i) x
  let C := fun i j => (tsupport η).indicator (translate k h (A i j))
  have hv (i) : MemLp (v i) 2 volume := memLp_cutoff_mul_diffQuot_local hΩ (hg i) hη hηc k h hηs
  have hC (i j) : MemLp (C i j) ∞ volume := memLp_indicator_translate_coeff hηc (hA i j) k h hηs
  have hpoint (x : E) : lam * ∑ i, (v i x) ^ 2 ≤ ∑ i, ∑ j, C i j x * v i x * v j x := by
    by_cases hx : η x = 0
    · simp [v, hx]
    have hxs : x ∈ tsupport η := subset_tsupport η hx
    have hshift : x + h • EuclideanSpace.single k (1 : ℝ) ∈ Ω := by
      apply hηs
      apply closedBall_subset_cthickening hxs |h|
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]
    simpa only [C, indicator_of_mem hxs, translate] using hcoer _ hshift (fun i => v i x)
  have heq1 : (fun x => ∑ i, (v i x) ^ 2) = fun x => (η x)^2 * ∑ i, (diffQuot k h (g i) x)^2 := by
    funext x
    simp only [v, mul_pow, Finset.mul_sum]
  have heq2 (i j) : (fun x => C i j x * v i x * v j x) =
      fun x => translate k h (A i j) x * (η x)^2 * diffQuot k h (g i) x * diffQuot k h (g j) x := by
    funext x
    by_cases hx : η x = 0
    · simp [v, hx]
    · simp only [C, indicator_of_mem (subset_tsupport η hx), v]
      ring
  simpa only [heq1, heq2] using integral_sum_quadratic_ge volume C v hv hC hpoint

private theorem continuousOn_translate_diffQuot
    {Ω K : Set E} {c : E → ℝ} (hc : ContinuousOn c Ω)
    (k : Fin d) (s : ℝ) (hKΩ : cthickening |s| K ⊆ Ω) :
    ContinuousOn (translate k s c) K ∧ ContinuousOn (diffQuot k s c) K := by
  have hshift : MapsTo (fun x => x + s • EuclideanSpace.single k (1 : ℝ)) K Ω := by
    intro x hx
    apply hKΩ
    apply closedBall_subset_cthickening hx |s|
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]
  have hτ : ContinuousOn (translate k s c) K :=
    hc.comp (continuous_id.add continuous_const).continuousOn hshift
  refine ⟨hτ, ?_⟩
  by_cases hs : s = 0
  · subst s
    rw [diffQuot_zero_h]
    exact continuousOn_const
  have hbase : K ⊆ Ω := (self_subset_cthickening _).trans hKΩ
  apply ((hτ.sub (hc.mono hbase)).div_const s).congr
  intro x _
  simp only [diffQuot_apply_of_ne k hs, translate, Pi.sub_apply]

theorem integral_sq_cutoff_diffQuot_eq_restrict
    {η u : E → ℝ} (k : Fin d) (s : ℝ) :
    (∫ x in tsupport η, (η x * diffQuot k s u x)^2) =
      ∫ x, (η x * diffQuot k s u x)^2 := by
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_pow (by norm_num)]

theorem abs_integral_nirenberg_flux_sub_principal_le_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u g v c η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hv : MemLp v 2 (volume.restrict Ω)) (hc : ContinuousOn c Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin d) (s : ℝ) (hηs : cthickening |s| (tsupport η) ⊆ Ω)
    {L ε : ℝ} (hε : 0 < ε)
    (hτ : ∀ x ∈ tsupport η, |translate k s c x| ≤ L)
    (hδ : ∀ x ∈ tsupport η, |diffQuot k s c x| ≤ L)
    (hηb : ∀ x, |η x| ≤ 1)
    (hηd : ∀ x ∈ tsupport η, |fderiv ℝ η x (EuclideanSpace.single j 1)| ≤ L) :
    |(∫ x, (translate k s c x * diffQuot k s g x + diffQuot k s c x * g x) *
        ((η x)^2 * diffQuot k s v x +
          2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k s u x)) -
      ∫ x, translate k s c x * (η x)^2 * diffQuot k s g x * diffQuot k s v x| ≤
      ε * (∫ x, (η x * diffQuot k s g x)^2) + ε * (∫ x, (η x * diffQuot k s v x)^2) +
        ((4 * ε)⁻¹ * L^2 + L^4) * (∫ x in tsupport η, (g x)^2) +
        (ε⁻¹ * L^4 + 1) * (∫ x in tsupport η, (diffQuot k s u x)^2) := by
  let K := tsupport η
  have hK : MeasurableSet K := (isClosed_tsupport η).measurableSet
  have hKΩ : K ⊆ Ω := (self_subset_cthickening _).trans hηs
  have hcont := continuousOn_translate_diffQuot hc k s hηs
  have hDη : Continuous (fun x => fderiv ℝ η x (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hp := (memLp_cutoff_mul_diffQuot_local hΩ hg hη.continuous hηc k s hηs).restrict K
  have hq := (memLp_cutoff_mul_diffQuot_local hΩ hv hη.continuous hηc k s hηs).restrict K
  have hz := hg.mono_measure (Measure.restrict_mono_set _ hKΩ)
  have hw := memLp_diffQuot_restrict hΩ hK hu k s hηs
  have hi := abs_integral_flux_sub_integral_principal_le
    (hcont.1.aestronglyMeasurable hK) (hcont.2.aestronglyMeasurable hK)
    (hη.continuous.aestronglyMeasurable) (hDη.aestronglyMeasurable)
    hp hq hz hw
    ((ae_restrict_mem hK).mono fun x hx => hτ x hx)
    ((ae_restrict_mem hK).mono fun x hx => hδ x hx)
    (Filter.Eventually.of_forall hηb)
    ((ae_restrict_mem hK).mono fun x hx => hηd x hx) hε
  have hleft : (∫ x in K, (translate k s c x * (η x * diffQuot k s g x) +
      diffQuot k s c x * η x * g x) *
        (η x * diffQuot k s v x + 2 * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k s u x)) =
      ∫ x, (translate k s c x * diffQuot k s g x + diffQuot k s c x * g x) *
        ((η x)^2 * diffQuot k s v x +
          2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k s u x) := by
    calc
      _ = ∫ x in K, (translate k s c x * diffQuot k s g x + diffQuot k s c x * g x) *
          ((η x)^2 * diffQuot k s v x +
            2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k s u x) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx]
  have hright : (∫ x in K, translate k s c x * (η x * diffQuot k s g x) *
      (η x * diffQuot k s v x)) =
      ∫ x, translate k s c x * (η x)^2 * diffQuot k s g x * diffQuot k s v x := by
    calc
      _ = ∫ x in K, translate k s c x * (η x)^2 * diffQuot k s g x * diffQuot k s v x := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx]
  rw [hleft, hright, integral_sq_cutoff_diffQuot_eq_restrict,
    integral_sq_cutoff_diffQuot_eq_restrict] at hi
  exact hi

theorem abs_integral_nirenberg_lower_order_flux_le_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u g c η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hc : ContinuousOn c Ω) (hη : Continuous η) (hηc : HasCompactSupport η)
    (k : Fin d) (s : ℝ) (hηs : cthickening |s| (tsupport η) ⊆ Ω)
    {L ε : ℝ} (hε : 0 < ε)
    (hτ : ∀ x ∈ tsupport η, |translate k s c x| ≤ L)
    (hδ : ∀ x ∈ tsupport η, |diffQuot k s c x| ≤ L)
    (hηb : ∀ x, |η x| ≤ 1) :
    |∫ x, (translate k s c x * diffQuot k s g x + diffQuot k s c x * g x) *
        ((η x)^2 * diffQuot k s u x)| ≤
      ε * (∫ x, (η x * diffQuot k s g x)^2) + L^2 / 2 * (∫ x in tsupport η, (g x)^2) +
        ((4 * ε)⁻¹ * L^2 + 1 / 2) * (∫ x in tsupport η, (diffQuot k s u x)^2) := by
  let K := tsupport η
  have hK : MeasurableSet K := (isClosed_tsupport η).measurableSet
  have hKΩ : K ⊆ Ω := (self_subset_cthickening _).trans hηs
  have hcont := continuousOn_translate_diffQuot hc k s hηs
  have hp := (memLp_cutoff_mul_diffQuot_local hΩ hg hη hηc k s hηs).restrict K
  have hz := hg.mono_measure (Measure.restrict_mono_set _ hKΩ)
  have hw := memLp_diffQuot_restrict hΩ hK hu k s hηs
  have hi := abs_integral_lower_order_flux_le
    (hcont.1.aestronglyMeasurable hK) (hcont.2.aestronglyMeasurable hK) hη.aestronglyMeasurable
    hp hz hw
    ((ae_restrict_mem hK).mono fun x hx => hτ x hx)
    ((ae_restrict_mem hK).mono fun x hx => hδ x hx)
    (Filter.Eventually.of_forall hηb) hε
  have heq : (∫ x in K, (translate k s c x * (η x * diffQuot k s g x) +
      diffQuot k s c x * η x * g x) * (η x * diffQuot k s u x)) =
      ∫ x, (translate k s c x * diffQuot k s g x + diffQuot k s c x * g x) *
        ((η x)^2 * diffQuot k s u x) := by
    calc
      _ = ∫ x in K, (translate k s c x * diffQuot k s g x + diffQuot k s c x * g x) *
          ((η x)^2 * diffQuot k s u x) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx]
  rw [heq, integral_sq_cutoff_diffQuot_eq_restrict] at hi
  exact hi

private theorem integral_cutoff_diffQuot_sq_le_restrict
    {Ω : Set E} (hΩ : MeasurableSet Ω) {η u : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin d) (s : ℝ)
    (hηs : cthickening |s| (tsupport η) ⊆ Ω) :
    0 ≤ (∫ x, diffQuot k s u x * ((η x)^2 * diffQuot k s u x)) ∧
      (∫ x, diffQuot k s u x * ((η x)^2 * diffQuot k s u x)) ≤
        ∫ x in tsupport η, (diffQuot k s u x)^2 := by
  have heq : (∫ x, diffQuot k s u x * ((η x)^2 * diffQuot k s u x)) =
      ∫ x, (η x * diffQuot k s u x)^2 := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [heq]
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  rw [← integral_sq_cutoff_diffQuot_eq_restrict]
  have hm := memLp_diffQuot_restrict hΩ (isClosed_tsupport η).measurableSet hu k s hηs
  apply integral_mono ((memLp_cutoff_mul_diffQuot_local hΩ hu hη hηc k s hηs).restrict _).integrable_sq
    hm.integrable_sq
  intro x
  dsimp only
  rw [mul_pow]
  exact (mul_le_mul_of_nonneg_right
    (by simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hηb x)) (sq_nonneg _)).trans_eq (by simp)


variable {ι : Type*} [Fintype ι]

private theorem finite_flux_energy_le
    (P F Q : ι → ι → ℝ) (B En G : ι → ℝ)
    (r W lam ε C_R_G C_R_W C_Q_G C_Q_W C_B_G C_B_W C_A : ℝ)
    (hP : lam * ∑ i, En i ≤ ∑ i, ∑ j, P i j)
    (hF : ∀ i j, |F i j - P i j| ≤ ε * (En i + En j) + C_R_G * G i + C_R_W * W)
    (hQ : ∀ i j, |Q i j| ≤ ε * En i + C_Q_G * G i + C_Q_W * W)
    (hB : ∀ i, |B i| ≤ ε * En i + C_B_G * G i + C_B_W * W)
    (hr : -C_A * W ≤ r) :
    let d : ℝ := Fintype.card ι
    lam * (∑ i, En i) ≤ (∑ i, ∑ j, F i j) + (∑ i, ∑ j, Q i j) - (∑ i, B i) + r +
      ((3 * d + 1) * ε) * (∑ i, En i) +
      (d * C_R_G + d * C_Q_G + C_B_G) * (∑ i, G i) +
      (d ^ 2 * C_R_W + d ^ 2 * C_Q_W + d * C_B_W + C_A) * W := by
  intro d
  have hFP : (∑ i, ∑ j, P i j) ≤ (∑ i, ∑ j, F i j) +
      ∑ i, ∑ j, (ε * (En i + En j) + C_R_G * G i + C_R_W * W) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hij := (abs_le.mp (hF i j)).1
    linarith
  have hQsum : -(∑ i, ∑ j, Q i j) ≤
      ∑ i, ∑ _j : ι, (ε * En i + C_Q_G * G i + C_Q_W * W) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    exact (neg_le_abs _).trans (hQ i j)
  have hBsum : (∑ i, B i) ≤ ∑ i, (ε * En i + C_B_G * G i + C_B_W * W) :=
    Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hB i)
  have hRtotal : (∑ i, ∑ j, (ε * (En i + En j) + C_R_G * G i + C_R_W * W)) =
      (2 * d * ε) * (∑ i, En i) + d * C_R_G * (∑ i, G i) + d ^ 2 * C_R_W * W := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    dsimp only [d]
    ring
  have hQtotal : (∑ i, ∑ _j : ι, (ε * En i + C_Q_G * G i + C_Q_W * W)) =
      (d * ε) * (∑ i, En i) + d * C_Q_G * (∑ i, G i) + d ^ 2 * C_Q_W * W := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    dsimp only [d]
    ring
  have hBtotal : (∑ i, (ε * En i + C_B_G * G i + C_B_W * W)) =
      ε * (∑ i, En i) + C_B_G * (∑ i, G i) + d * C_B_W * W := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    dsimp only [d]
    ring
  rw [hRtotal] at hFP
  rw [hQtotal] at hQsum
  rw [hBtotal] at hBsum
  nlinarith

private theorem finite_flux_absorption
    (P F Q : ι → ι → ℝ) (B En G : ι → ℝ)
    (r W lam C_R_G C_R_W C_Q_G C_Q_W C_B_G C_B_W C_A : ℝ)
    (hlam : 0 < lam) (hG : ∀ i, 0 ≤ G i) (hW : 0 ≤ W) :
    let d : ℝ := Fintype.card ι
    let ε := lam / (2 * (3 * d + 1))
    let Cg := d * C_R_G + d * C_Q_G + C_B_G
    let Cw := d ^ 2 * C_R_W + d ^ 2 * C_Q_W + d * C_B_W + C_A
    lam * (∑ i, En i) ≤ (∑ i, ∑ j, P i j) →
    (∀ i j, |F i j - P i j| ≤ ε * (En i + En j) + C_R_G * G i + C_R_W * W) →
    (∀ i j, |Q i j| ≤ ε * En i + C_Q_G * G i + C_Q_W * W) →
    (∀ i, |B i| ≤ ε * En i + C_B_G * G i + C_B_W * W) →
    -C_A * W ≤ r →
    0 < ε ∧ 0 ≤ max 0 (max Cg Cw) ∧ lam / 2 * (∑ i, En i) ≤
      (∑ i, ∑ j, F i j) + (∑ i, ∑ j, Q i j) - (∑ i, B i) + r +
        max 0 (max Cg Cw) * ((∑ i, G i) + W) := by
  intro d ε Cg Cw hP hF hQ hB hr
  have hd : 0 < 3 * d + 1 := by dsimp only [d]; positivity
  have hε : 0 < ε := div_pos hlam (mul_pos (by norm_num) hd)
  refine ⟨hε, le_max_left _ _, ?_⟩
  have hmain := finite_flux_energy_le P F Q B En G r W lam ε
    C_R_G C_R_W C_Q_G C_Q_W C_B_G C_B_W C_A hP hF hQ hB hr
  change lam * (∑ i, En i) ≤ (∑ i, ∑ j, F i j) + (∑ i, ∑ j, Q i j) - (∑ i, B i) + r +
    ((3 * d + 1) * ε) * (∑ i, En i) + Cg * (∑ i, G i) + Cw * W at hmain
  have hbalance : (3 * d + 1) * ε = lam / 2 := by
    dsimp only [ε]
    field_simp
  rw [hbalance] at hmain
  have hGsum : 0 ≤ ∑ i, G i := Finset.sum_nonneg fun i _ => hG i
  have hg := mul_le_mul_of_nonneg_right ((le_max_left Cg Cw).trans (le_max_right 0 (max Cg Cw))) hGsum
  have hw := mul_le_mul_of_nonneg_right ((le_max_right Cg Cw).trans (le_max_right 0 (max Cg Cw))) hW
  nlinarith


theorem integral_nirenberg_flux_lower_bound_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u : E → ℝ} {g : Fin d → E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : ∀ i, MemLp (g i) 2 (volume.restrict Ω))
    {A R : Fin d → Fin d → E → ℝ} {B : Fin d → E → ℝ}
    (hA : ∀ i j, ContinuousOn (A i j) Ω)
    (hR : ∀ i j, ContinuousOn (R i j) Ω) (hB : ∀ i, ContinuousOn (B i) Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) {lam L : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ y ∈ Ω, ∀ ξ : Fin d → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, A i j y * ξ i * ξ j)
    (k : Fin d) (s a : ℝ) (hηs : cthickening |s| (tsupport η) ⊆ Ω)
    (hAL : ∀ i j x, x ∈ tsupport η →
      |translate k s (A i j) x| ≤ L ∧ |diffQuot k s (A i j) x| ≤ L)
    (hRL : ∀ i j x, x ∈ tsupport η →
      |translate k s (R i j) x| ≤ L ∧ |diffQuot k s (R i j) x| ≤ L)
    (hBL : ∀ i x, x ∈ tsupport η →
      |translate k s (B i) x| ≤ L ∧ |diffQuot k s (B i) x| ≤ L)
    (hηd : ∀ j x, x ∈ tsupport η → |fderiv ℝ η x (EuclideanSpace.single j 1)| ≤ L) :
    let ε := lam / (2 * (3 * (d : ℝ) + 1))
    let Cg := (d : ℝ) * ((4 * ε)⁻¹ * L^2 + L^4) + (d : ℝ) * (L^2 / 2) + L^2 / 2
    let Cw := (d : ℝ)^2 * (ε⁻¹ * L^4 + 1) + (d : ℝ)^2 * ((4 * ε)⁻¹ * L^2 + 1/2) +
      (d : ℝ) * ((4 * ε)⁻¹ * L^2 + 1/2) + |a|
    let C := max 0 (max Cg Cw)
    0 ≤ C ∧ lam / 2 * (∑ i, ∫ x, (η x * diffQuot k s (g i) x)^2) ≤
      (∑ i, ∑ j, ((∫ x, (translate k s (A i j) x * diffQuot k s (g i) x +
        diffQuot k s (A i j) x * g i x) *
          ((η x)^2 * diffQuot k s (g j) x +
            2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k s u x)) +
        ∫ x, (translate k s (R i j) x * diffQuot k s (g i) x +
          diffQuot k s (R i j) x * g i x) * ((η x)^2 * diffQuot k s u x))) -
      (∑ i, ∫ x, (translate k s (B i) x * diffQuot k s (g i) x +
        diffQuot k s (B i) x * g i x) * ((η x)^2 * diffQuot k s u x)) +
      a * (∫ x, diffQuot k s u x * ((η x)^2 * diffQuot k s u x)) +
      C * ((∑ i, ∫ x in tsupport η, (g i x)^2) + ∫ x in tsupport η, (diffQuot k s u x)^2) := by
  intro ε Cg Cw C
  have hε : 0 < ε := div_pos hlam (by positivity)
  let En₀ := fun i => ∫ x, (η x * diffQuot k s (g i) x)^2
  let G₀ := fun i => ∫ x in tsupport η, (g i x)^2
  let W := ∫ x in tsupport η, (diffQuot k s u x)^2
  let P₀ := fun i j => ∫ x, translate k s (A i j) x * (η x)^2 * diffQuot k s (g i) x * diffQuot k s (g j) x
  let F₀ := fun i j => ∫ x, (translate k s (A i j) x * diffQuot k s (g i) x + diffQuot k s (A i j) x * g i x) *
    ((η x)^2 * diffQuot k s (g j) x + 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k s u x)
  let Q₀ := fun i j => ∫ x, (translate k s (R i j) x * diffQuot k s (g i) x + diffQuot k s (R i j) x * g i x) *
    ((η x)^2 * diffQuot k s u x)
  let B₀ := fun i => ∫ x, (translate k s (B i) x * diffQuot k s (g i) x + diffQuot k s (B i) x * g i x) *
    ((η x)^2 * diffQuot k s u x)
  let r := a * (∫ x, diffQuot k s u x * ((η x)^2 * diffQuot k s u x))
  have hE : (∫ x, (η x)^2 * ∑ i, (diffQuot k s (g i) x)^2) = ∑ i, En₀ i := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl; intro i _
      apply integral_congr_ae; filter_upwards with x; ring
    · intro i _
      exact ((memLp_cutoff_mul_diffQuot_local hΩ (hg i) hη.continuous hηc k s hηs).integrable_sq).congr
        (Filter.Eventually.of_forall fun x => by dsimp [En₀]; ring)
  have hP : lam * ∑ i, En₀ i ≤ ∑ i, ∑ j, P₀ i j := by
    have hi := integral_shifted_principal_ge_local hΩ hg hη.continuous hηc hA hcoer k s hηs
    rwa [hE] at hi
  have hF (i j') : |F₀ i j' - P₀ i j'| ≤
      ε * (En₀ i + En₀ j') + ((4 * ε)⁻¹ * L^2 + L^4) * G₀ i + (ε⁻¹ * L^4 + 1) * W := by
    have hi := abs_integral_nirenberg_flux_sub_principal_le_local hΩ hu (hg i) (hg j')
      (hA i j') hη hηc k j' s hηs hε
      (fun x hx => (hAL i j' x hx).1) (fun x hx => (hAL i j' x hx).2) hηb (hηd j')
    simpa [F₀, P₀, En₀, G₀, W, mul_add, add_mul] using hi
  have hQ (i j') : |Q₀ i j'| ≤ ε * En₀ i + L^2/2 * G₀ i + ((4 * ε)⁻¹ * L^2 + 1/2) * W := by
    have hi := abs_integral_nirenberg_lower_order_flux_le_local hΩ hu (hg i) (hR i j') hη.continuous hηc k s hηs hε
      (fun x hx => (hRL i j' x hx).1) (fun x hx => (hRL i j' x hx).2) hηb
    simpa [Q₀, En₀, G₀, W] using hi
  have hB' (i) : |B₀ i| ≤ ε * En₀ i + L^2/2 * G₀ i + ((4 * ε)⁻¹ * L^2 + 1/2) * W := by
    have hi := abs_integral_nirenberg_lower_order_flux_le_local hΩ hu (hg i) (hB i) hη.continuous hηc k s hηs hε
      (fun x hx => (hBL i x hx).1) (fun x hx => (hBL i x hx).2) hηb
    simpa [B₀, En₀, G₀, W] using hi
  have hr : -|a| * W ≤ r := by
    have hi := integral_cutoff_diffQuot_sq_le_restrict hΩ hu hη.continuous hηc hηb k s hηs
    have h1 := mul_le_mul_of_nonneg_right (neg_abs_le a) hi.1
    have h2 := mul_le_mul_of_nonpos_left hi.2 (neg_nonpos.mpr (abs_nonneg a))
    exact h2.trans h1
  have hi := finite_flux_absorption P₀ F₀ Q₀ B₀ En₀ G₀ r W lam
    ((4 * ε)⁻¹ * L^2 + L^4) (ε⁻¹ * L^4 + 1) (L^2/2) ((4 * ε)⁻¹ * L^2 + 1/2)
    (L^2/2) ((4 * ε)⁻¹ * L^2 + 1/2) |a| hlam
    (fun i => integral_nonneg (fun x => sq_nonneg _)) (integral_nonneg (fun x => sq_nonneg _))
  simp only [Fintype.card_fin] at hi
  have hbound := (hi hP hF hQ hB' hr).2
  simpa only [En₀, G₀, W, P₀, F₀, Q₀, B₀, r, Cg, Cw, ε, C, Finset.sum_add_distrib] using hbound

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction




namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_mul_diffQuot_eq_neg_integral_diffQuot_mul_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {F G η : E → ℝ}
    (hF : MemLp F 2 (volume.restrict Ω)) (hG : MemLp G 2 volume)
    (hGs : Function.support G ⊆ tsupport η)
    (k : Fin d) (h : ℝ) (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x in Ω, F x * diffQuot k (-h) G x) = -∫ x, diffQuot k h F x * G x := by
  by_cases hh : h = 0
  · simp [hh]
  have hF0 : MemLp (Ω.indicator F) 2 volume := (memLp_indicator_iff_restrict hΩ).mpr hF
  have hi := integral_diffQuot_mul_eq_neg_integral_mul_diffQuot k hh hF0 hG
  have hleft : (∫ x, Ω.indicator F x * diffQuot k (-h) G x) =
      ∫ x in Ω, F x * diffQuot k (-h) G x := by
    rw [← integral_indicator hΩ]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  have hright : (∫ x, diffQuot k h (Ω.indicator F) x * G x) =
      ∫ x, diffQuot k h F x * G x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : G x = 0
    · simp [hx]
    have hxs := hGs hx
    have hbase := hηs (self_subset_cthickening _ hxs)
    have hshift := translate_mem_of_support k h hηs hxs
    simp only [diffQuot_apply_of_ne k hh, indicator_of_mem hbase, indicator_of_mem hshift]
  rw [hleft, hright] at hi
  linarith

private theorem memLp_nirenberg_flux_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u g η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin d) (h : ℝ) (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    MemLp (fun x => (η x)^2 * diffQuot k h g x +
      2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x) 2 volume := by
  have hηlp : MemLp η ∞ volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have hfirst : MemLp (fun x => η x * (η x * diffQuot k h g x)) 2 volume :=
    (memLp_cutoff_mul_diffQuot_local hΩ hg hη.continuous hηc k h hηs).mul' hηlp
  let χ := fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1)
  have hχ : Continuous χ := (continuous_const.mul hη.continuous).mul
    ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hχc : HasCompactSupport χ := hηc.mul_left.mul_right
  have hχs : tsupport χ ⊆ tsupport η := tsupport_mul_subset_left.trans tsupport_mul_subset_right
  have hsecond := memLp_cutoff_mul_diffQuot_local hΩ hu hχ hχc k h
    ((cthickening_subset_of_subset _ hχs).trans hηs)
  apply (hfirst.add hsecond).ae_eq
  filter_upwards with x
  dsimp only [Pi.add_apply, χ]
  ring

theorem integral_coefficient_mul_nirenberg_flux_eq_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u g v a η : E → ℝ}
    (hau : MemLp (fun x => a x * g x) 2 (volume.restrict Ω))
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin d) (h : ℝ) (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    -(∫ x in Ω, a x * g x * diffQuot k (-h) (fun y => (η y)^2 * diffQuot k h v y +
      2 * η y * fderiv ℝ η y (EuclideanSpace.single j 1) * diffQuot k h u y) x) =
    ∫ x, (translate k h a x * diffQuot k h g x + diffQuot k h a x * g x) *
      ((η x)^2 * diffQuot k h v x +
        2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x) := by
  let G := fun x => (η x)^2 * diffQuot k h v x +
    2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x
  have hGs : Function.support G ⊆ tsupport η := by
    intro x hx
    by_contra hxs
    exact hx (by simp [G, image_eq_zero_of_notMem_tsupport hxs])
  rw [integral_mul_diffQuot_eq_neg_integral_diffQuot_mul_local hΩ hau
    (memLp_nirenberg_flux_local hΩ hu hv hη hηc k j h hηs) hGs k h hηs, neg_neg]
  simp only [NirenbergEuclidean.diffQuot_mul]


end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction


namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth (memLp_diffQuot_two)

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_normalized_multiplier_nirenberg_flux_eq_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u g v A C P Q η : E → ℝ}
    (hPg : MemLp (fun x => A x * g x) 2 (volume.restrict Ω))
    (hCP : EqOn (fun x => C x * P x) A Ω)
    (hQg : MemLp (fun x => (C x * Q x) * g x) 2 (volume.restrict Ω))
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin d) (h : ℝ) (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    -(∫ x in Ω, g x * C x * (P x * diffQuot k (-h) (fun y => (η y)^2 * diffQuot k h v y +
      2 * η y * fderiv ℝ η y (EuclideanSpace.single j 1) * diffQuot k h u y) x +
        Q x * nirenbergTestFunction k h η u x)) =
      (∫ x, (translate k h A x * diffQuot k h g x +
        diffQuot k h A x * g x) *
          ((η x)^2 * diffQuot k h v x +
            2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x)) +
      ∫ x, (translate k h (fun y => C y * Q y) x * diffQuot k h g x +
        diffQuot k h (fun y => C y * Q y) x * g x) * ((η x)^2 * diffQuot k h u x) := by
  let G := fun y => (η y)^2 * diffQuot k h v y +
    2 * η y * fderiv ℝ η y (EuclideanSpace.single j 1) * diffQuot k h u y
  have hDG : MemLp (diffQuot k (-h) G) 2 (volume.restrict Ω) :=
    (memLp_diffQuot_two k (-h) (memLp_nirenberg_flux_local hΩ hu hv hη hηc k j h hηs)).restrict Ω
  have hηdu := memLp_cutoff_mul_diffQuot_local hΩ hu hη.continuous hηc k h hηs
  have hN : MemLp (nirenbergTestFunction k h η u) 2 (volume.restrict Ω) := by
    have hηsq : MemLp (fun x => (η x)^2 * diffQuot k h u x) 2 volume := by
      convert hηdu.mul' (r := 2) (hη.continuous.memLp_of_hasCompactSupport hηc : MemLp η ∞ volume) using 1
      ext x
      ring
    exact (memLp_diffQuot_two k (-h) hηsq).restrict Ω
  have hsplit : (∫ x in Ω, g x * C x * (P x * diffQuot k (-h) G x +
      Q x * nirenbergTestFunction k h η u x)) =
      (∫ x in Ω, A x * g x * diffQuot k (-h) G x) +
        ∫ x in Ω, (C x * Q x) * g x * nirenbergTestFunction k h η u x := by
    calc
      _ = ∫ x in Ω, (A x * g x * diffQuot k (-h) G x +
          (C x * Q x) * g x * nirenbergTestFunction k h η u x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hΩ] with x hx
        rw [← hCP hx]
        ring
      _ = _ := integral_add (hPg.integrable_mul hDG) (hQg.integrable_mul hN)
  rw [hsplit, neg_add_rev]
  have h1 := integral_coefficient_mul_nirenberg_flux_eq_local hΩ hPg hu hv hη hηc k j h hηs
  have h2 := integral_weight_mul_nirenbergTestFunction_eq_local hΩ hQg hu hη.continuous hηc k h hηs
  rw [h2, neg_neg, h1, add_comm]

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
