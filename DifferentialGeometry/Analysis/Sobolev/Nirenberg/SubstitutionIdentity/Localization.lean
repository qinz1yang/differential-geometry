import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Defs
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.IntegrationByParts
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.SmoothRegularity
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses

noncomputable section

open MeasureTheory Metric Set
open DifferentialGeometry.Analysis.Sobolev
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem memLp_mul_cpt
    {f g : E → ℝ} (hf : Continuous f) (hf_cpt : HasCompactSupport f)
    (hg : MemLp g 2 (volume : Measure E)) :
    MemLp (fun x => f x * g x) 2 (volume : Measure E) := by
  exact hg.mul' (r := 2) (hf.memLp_top_of_hasCompactSupport hf_cpt volume)

omit [NeZero d] in
private theorem integrable_cpt_mul_two
    {a f g : E → ℝ} (ha : Continuous a) (ha_cpt : HasCompactSupport a)
    (hf : MemLp f 2 (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E)) :
    Integrable (fun x => a x * f x * g x) (volume : Measure E) :=
  MemLp.integrable_mul (memLp_mul_cpt ha ha_cpt hf) hg


omit [NeZero d] in
private theorem ibp_pair
    {Omega K : Set E} {a g F : E → ℝ} (k : Fin d) (h : ℝ)
    (hag : MemLp (fun x => a x * g x) 2 (volume : Measure E))
    (hF : MemLp F 2 (volume : Measure E))
    (hF_supp : tsupport F ⊆ K)
    (hroom : Metric.cthickening |h| K ⊆ Omega) :
    ∫ x in Omega, a x * g x * diffQuot k (-h) F x ∂(volume : Measure E) =
      -∫ x in Omega,
        (translate k h a x * diffQuot k h g x + diffQuot k h a x * g x) * F x
          ∂(volume : Measure E) := by
  have hibp := setIntegral_mul_diffQuot_eq_neg_setIntegral_diffQuot_mul_of_cthickening_subset
    (Ω := Omega) (f := fun x => a x * g x) (g := F) k h hag hF
    ((Metric.cthickening_subset_of_subset |h| ((subset_tsupport F).trans hF_supp)).trans
      hroom)
  rw [diffQuot_mul] at hibp
  exact hibp

omit [NeZero d] in
private theorem inner_tsupport
    (eta u g : E → ℝ) (i k : Fin d) (h : ℝ) :
    tsupport (fun x =>
        eta x ^ 2 * diffQuot k h g x +
          2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single i 1) *
            diffQuot k h u x) ⊆ tsupport eta := by
  rw [tsupport]
  apply closure_minimal _ (isClosed_tsupport eta)
  intro x hx
  by_contra hx_eta
  apply hx
  have heta : eta x = 0 := image_eq_zero_of_notMem_tsupport hx_eta
  simp [heta]

omit [NeZero d] in
private theorem inner_memLp
    {eta u g : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (hu : MemLp u 2 (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E))
    (i k : Fin d) (h : ℝ) :
    MemLp (fun x =>
        eta x ^ 2 * diffQuot k h g x +
          2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single i 1) *
            diffQuot k h u x) 2 (volume : Measure E) := by
  have hdq_u : MemLp (diffQuot k h u) 2 (volume : Measure E) :=
    memLp_diffQuot k h hu
  have hdq_g : MemLp (diffQuot k h g) 2 (volume : Measure E) :=
    memLp_diffQuot k h hg
  have heta_sq_cont : Continuous (fun x : E => eta x ^ 2) :=
    heta.continuous.pow 2
  have heta_sq_cpt : HasCompactSupport (fun x : E => eta x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using heta_cpt.mul_right (f' := eta)
  have hterm1 : MemLp (fun x => eta x ^ 2 * diffQuot k h g x) 2
      (volume : Measure E) :=
    memLp_mul_cpt heta_sq_cont heta_sq_cpt hdq_g
  let coeff : E → ℝ := fun x =>
    2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single i 1)
  have hcoeff_cont : Continuous coeff := by
    exact (continuous_const.mul heta.continuous).mul
      ((heta.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hcoeff_cpt : HasCompactSupport coeff := by
    apply HasCompactSupport.intro'
      (K := tsupport eta) heta_cpt.isCompact (isClosed_tsupport eta)
    intro x hx
    have hetax : eta x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [coeff, hetax]
  have hterm2 : MemLp (fun x => coeff x * diffQuot k h u x) 2
      (volume : Measure E) :=
    memLp_mul_cpt hcoeff_cont hcoeff_cpt hdq_u
  simpa only [Pi.add_apply, coeff] using! hterm1.add hterm2

private theorem coeff_mul_memLp
    {Omega K : Set E} (B : SmoothEllipticBilinearForm d Omega)
    (hK : IsCompact K) {g : E → ℝ} (hg : MemLp g 2 (volume : Measure E))
    (i j : Fin d) :
    MemLp (fun x => K.indicator (fun y => B.a y i j) x * g x) 2
      (volume : Measure E) := by
  obtain ⟨M, hM, hM_bound⟩ := B.bounded_a_on_compact hK
  have ha_meas : AEStronglyMeasurable
      (K.indicator (fun y => B.a y i j)) (volume : Measure E) :=
    (B.continuous_a i j).aestronglyMeasurable.indicator hK.measurableSet
  apply hg.mul' (p := ⊤) (r := 2)
  apply memLp_top_of_bound ha_meas M
  filter_upwards with x
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    exact hM_bound i j x hx
  · rw [Set.indicator_of_notMem hx, abs_zero]
    exact hM

omit [NeZero d] in
private theorem inner_eq_of_eqOn
    {K : Set E} {eta u U g G : E → ℝ}
    (hu : ∀ x ∈ K, U x = u x)
    (hg : ∀ x ∈ K, G x = g x)
    (i k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ K) :
    (fun x =>
        eta x ^ 2 * diffQuot k h G x +
          2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single i 1) *
            diffQuot k h U x) =
      fun x =>
        eta x ^ 2 * diffQuot k h g x +
          2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single i 1) *
            diffQuot k h u x := by
  funext x
  by_cases hx : x ∈ tsupport eta
  · have hxK : x ∈ K := by
      apply hroom
      refine Metric.mem_cthickening_of_dist_le x x |h| (tsupport eta) hx ?_
      simp
    have hx_shiftK : x + h • EuclideanSpace.single k 1 ∈ K := by
      apply hroom
      refine Metric.mem_cthickening_of_dist_le _ x |h| (tsupport eta) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp
    rw [diffQuot_apply_of_ne (d := d) k hh G x,
      diffQuot_apply_of_ne (d := d) k hh g x,
      diffQuot_apply_of_ne (d := d) k hh U x,
      diffQuot_apply_of_ne (d := d) k hh u x,
      hg x hxK, hg _ hx_shiftK, hu x hxK, hu _ hx_shiftK]
  · have heta : eta x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [heta]

omit [NeZero d] in
private theorem outer_zero_off
    {K : Set E} {eta u g : E → ℝ} (i k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ K)
    {x : E} (hx : x ∉ K) :
    diffQuot k (-h) (fun y =>
        eta y ^ 2 * diffQuot k h g y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h u y) x = 0 := by
  let F : E → ℝ := fun y =>
    eta y ^ 2 * diffQuot k h g y +
      2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
        diffQuot k h u y
  have hF_supp : tsupport F ⊆ tsupport eta :=
    inner_tsupport eta u g i k h
  have hFx : F x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hxt => hx (hroom
      ((Metric.self_subset_cthickening (tsupport eta)) (hF_supp hxt)))
  have hFshift : F (x + (-h) • EuclideanSpace.single k 1) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have hxt_eta : x + (-h) • EuclideanSpace.single k 1 ∈ tsupport eta :=
      hF_supp hxt
    apply hx
    apply hroom
    refine Metric.mem_cthickening_of_dist_le x
      (x + (-h) • EuclideanSpace.single k 1) |h| (tsupport eta) hxt_eta ?_
    rw [dist_eq_norm]
    have heq : x - (x + (-h) • EuclideanSpace.single k 1) =
        h • EuclideanSpace.single k 1 := by
      rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← neg_smul, neg_neg]
    rw [heq, norm_smul]
    simp
  change diffQuot k (-h) F x = 0
  rw [diffQuot_apply_of_ne (d := d) k (neg_ne_zero.mpr hh), hFshift, hFx]
  ring


theorem nirenberg_substitution_identity_of_eqOn
    {Omega K : Set E}
    {A : DeGiorgi.EllipticCoeff d Omega} {u U : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hU : DeGiorgi.MemW1pWitness 2 U Set.univ)
    (hK_compact : IsCompact K) (hK_Omega : K ⊆ Omega)
    (hU_eq : ∀ x ∈ K, U x = u x)
    (hgrad_eq : ∀ x ∈ K, ∀ i : Fin d,
      hU.weakGrad x i = hu.weakGrad x i)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    (hcoeff : ∀ x ∈ K, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (k : Fin d) (h : ℝ)
    (hroom_K : Metric.cthickening |h| (tsupport eta) ⊆ K) :
    ∫ x, (∑ i : Fin d, ∑ j : Fin d,
        translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
          diffQuot k h (fun y => hU.weakGrad y i) x *
          diffQuot k h (fun y => hU.weakGrad y j) x) ∂(volume : Measure E) +
      ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        2 * translate k h (fun y : E => B.a y i j) x * eta x *
          (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
          diffQuot k h (fun y => hU.weakGrad y i) x * diffQuot k h U x
        ∂(volume : Measure E) +
      ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
          hU.weakGrad x i * diffQuot k h (fun y => hU.weakGrad y j) x
        ∂(volume : Measure E) +
      ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
          (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
          hU.weakGrad x i * diffQuot k h U x
        ∂(volume : Measure E) = -(rho⁻¹ * (∫ x in Omega, ∑ i : Fin d,
          (∑ j : Fin d, A.a x i j * hu.weakGrad x j) *
            diffQuot k (-h) (fun y =>
              eta y ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
                2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
                  diffQuot k h u y) x
        ∂(volume : Measure E))) := by
  classical
  by_cases hh : h = 0
  · subst h
    simp
  let r : ℝ := ∫ x in Omega, ∑ i : Fin d,
          (∑ j : Fin d, A.a x i j * hu.weakGrad x j) *
            diffQuot k (-h) (fun y =>
              eta y ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
                2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
                  diffQuot k h u y) x
        ∂(volume : Measure E)
  have hlocal : ∫ x in Omega, ∑ i : Fin d,
          (∑ j : Fin d, A.a x i j * hu.weakGrad x j) *
            diffQuot k (-h) (fun y =>
              eta y ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
                2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
                  diffQuot k h u y) x
        ∂(volume : Measure E) = r := rfl
  let g : Fin d → E → ℝ := fun i x => hU.weakGrad x i
  let gLocal : Fin d → E → ℝ := fun i x => hu.weakGrad x i
  let F : Fin d → E → ℝ := fun i x =>
    eta x ^ 2 * diffQuot k h (g i) x +
      2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single i 1) *
        diffQuot k h U x
  let FLocal : Fin d → E → ℝ := fun i x =>
    eta x ^ 2 * diffQuot k h (gLocal i) x +
      2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single i 1) *
        diffQuot k h u x
  let aK : Fin d → Fin d → E → ℝ := fun i j =>
    K.indicator (fun x => B.a x i j)
  have hF_eq : ∀ i : Fin d, F i = FLocal i := by
    intro i
    exact inner_eq_of_eqOn (d := d) hU_eq
      (fun x hx => hgrad_eq x hx i) i k hh hroom_K
  change ∫ x in Omega, ∑ i : Fin d,
      (∑ j : Fin d, A.a x i j * gLocal j x) *
        diffQuot k (-h) (FLocal i) x ∂(volume : Measure E) = r at hlocal
  have houter_local : ∀ i : Fin d, ∀ {x : E}, x ∉ K →
      diffQuot k (-h) (FLocal i) x = 0 := by
    intro i x hx
    exact outer_zero_off (d := d) i k hh hroom_K hx
  have hpre_zero_outside : ∀ x ∉ Omega,
      (∑ i : Fin d, ∑ j : Fin d,
        aK i j x * g i x * diffQuot k (-h) (F j) x) = 0 := by
    intro x hx
    have hxK : x ∉ K := fun hx' => hx (hK_Omega hx')
    simp [aK, Set.indicator_of_notMem hxK]
  have hpoint : ∀ x : E,
      (∑ i : Fin d,
        (∑ j : Fin d, A.a x i j * gLocal j x) *
          diffQuot k (-h) (FLocal i) x) =
      rho * (∑ i : Fin d, ∑ j : Fin d,
        aK i j x * g i x * diffQuot k (-h) (F j) x) := by
    intro x
    by_cases hxK : x ∈ K
    · have hswap :
          (∑ i : Fin d, ∑ j : Fin d,
            B.a x i j * g j x * diffQuot k (-h) (F i) x) =
          ∑ i : Fin d, ∑ j : Fin d,
            B.a x i j * g i x * diffQuot k (-h) (F j) x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [B.symm]
      calc
        (∑ i : Fin d,
            (∑ j : Fin d, A.a x i j * gLocal j x) *
              diffQuot k (-h) (FLocal i) x) =
            rho * (∑ i : Fin d, ∑ j : Fin d,
              B.a x i j * g j x * diffQuot k (-h) (F i) x) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.sum_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [hcoeff x hxK i j, ← hF_eq i]
              simp only [g, gLocal]
              rw [← hgrad_eq x hxK j]
              ring
        _ = rho * (∑ i : Fin d, ∑ j : Fin d,
              B.a x i j * g i x * diffQuot k (-h) (F j) x) := by
              rw [hswap]
        _ = rho * (∑ i : Fin d, ∑ j : Fin d,
              aK i j x * g i x * diffQuot k (-h) (F j) x) := by
              simp only [aK, Set.indicator_of_mem hxK]
    · have hzero : ∀ i : Fin d, diffQuot k (-h) (FLocal i) x = 0 :=
        fun i => houter_local i hxK
      simp [hzero, aK, Set.indicator_of_notMem hxK]
  have hlocal_scaled :
      ∫ x in Omega, ∑ i : Fin d,
          (∑ j : Fin d, A.a x i j * gLocal j x) *
            diffQuot k (-h) (FLocal i) x ∂(volume : Measure E) =
        rho * ∫ x, ∑ i : Fin d, ∑ j : Fin d,
          aK i j x * g i x * diffQuot k (-h) (F j) x
          ∂(volume : Measure E) := by
    calc
      _ = ∫ x in Omega, rho * (∑ i : Fin d, ∑ j : Fin d,
            aK i j x * g i x * diffQuot k (-h) (F j) x)
            ∂(volume : Measure E) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpoint x
      _ = rho * ∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
            aK i j x * g i x * diffQuot k (-h) (F j) x
            ∂(volume : Measure E) := by
          exact integral_const_mul rho (fun x => ∑ i : Fin d, ∑ j : Fin d,
            aK i j x * g i x * diffQuot k (-h) (F j) x)
      _ = rho * ∫ x, ∑ i : Fin d, ∑ j : Fin d,
            aK i j x * g i x * diffQuot k (-h) (F j) x
            ∂(volume : Measure E) := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero hpre_zero_outside]
  have hpre_eq : ∫ x, ∑ i : Fin d, ∑ j : Fin d,
      aK i j x * g i x * diffQuot k (-h) (F j) x
      ∂(volume : Measure E) = rho⁻¹ * r := by
    have hscaled : rho * ∫ x, ∑ i : Fin d, ∑ j : Fin d,
        aK i j x * g i x * diffQuot k (-h) (F j) x
        ∂(volume : Measure E) = r := hlocal_scaled ▸ hlocal
    calc
      _ = (rho⁻¹ * rho) * ∫ x, ∑ i : Fin d, ∑ j : Fin d,
          aK i j x * g i x * diffQuot k (-h) (F j) x
          ∂(volume : Measure E) := by rw [inv_mul_cancel₀ hrho, one_mul]
      _ = rho⁻¹ * (rho * ∫ x, ∑ i : Fin d, ∑ j : Fin d,
          aK i j x * g i x * diffQuot k (-h) (F j) x
          ∂(volume : Measure E)) := by ring
      _ = rho⁻¹ * r := by rw [hscaled]
  have hg_l2 : ∀ i : Fin d, MemLp (g i) 2 (volume : Measure E) := by
    intro i
    simpa only [g, Measure.restrict_univ] using hU.weakGrad_component_memLp i
  have hU_l2 : MemLp U 2 (volume : Measure E) := by
    simpa only [Measure.restrict_univ] using hU.memLp
  have hdq_g_l2 : ∀ i : Fin d,
      MemLp (diffQuot k h (g i)) 2 (volume : Measure E) :=
    fun i => memLp_diffQuot k h (hg_l2 i)
  have hdq_U_l2 : MemLp (diffQuot k h U) 2 (volume : Measure E) :=
    memLp_diffQuot k h hU_l2
  have hF_l2 : ∀ i : Fin d, MemLp (F i) 2 (volume : Measure E) := by
    intro i
    exact inner_memLp heta heta_cpt hU_l2 (hg_l2 i) i k h
  have hpre_int : ∀ i j : Fin d, Integrable (fun x =>
      aK i j x * g i x * diffQuot k (-h) (F j) x)
      (volume : Measure E) := by
    intro i j
    exact MemLp.integrable_mul
      (coeff_mul_memLp B hK_compact (hg_l2 i) i j)
      (memLp_diffQuot k (-h) (hF_l2 j))
  have hpre_sum_eq : ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      aK i j x * g i x * diffQuot k (-h) (F j) x
      ∂(volume : Measure E) = rho⁻¹ * r := by
    have hinner : ∀ i : Fin d, Integrable (fun x => ∑ j : Fin d,
        aK i j x * g i x * diffQuot k (-h) (F j) x)
        (volume : Measure E) := fun i =>
      integrable_finsetSum _ (fun j _ => hpre_int i j)
    rw [integral_finsetSum _ (fun i _ => hinner i)] at hpre_eq
    simp_rw [integral_finsetSum _ (fun j _ => hpre_int _ j)] at hpre_eq
    exact hpre_eq
  have htrans_cont : ∀ i j : Fin d,
      Continuous (translate k h (fun x : E => B.a x i j)) := by
    intro i j
    exact (B.continuous_a i j).comp (continuous_id.add continuous_const)
  have hdq_B_cont : ∀ i j : Fin d,
      Continuous (diffQuot k h (fun x : E => B.a x i j)) := by
    intro i j
    exact (contDiff_diffQuot_of_contDiff (d := d) (B.contDiff_a i j) k hh).continuous
  have heta_sq_cpt : HasCompactSupport (fun x : E => eta x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using heta_cpt.mul_right (f' := eta)
  have hP_int : ∀ i j : Fin d, Integrable (fun x =>
      translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
        diffQuot k h (g i) x * diffQuot k h (g j) x)
      (volume : Measure E) := by
    intro i j
    apply integrable_cpt_mul_two
      ((htrans_cont i j).mul (heta.continuous.pow 2))
      (heta_sq_cpt.mul_left) (hdq_g_l2 i) (hdq_g_l2 j)
  have hC1_int : ∀ i j : Fin d, Integrable (fun x =>
      2 * translate k h (fun y : E => B.a y i j) x * eta x *
        (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
        diffQuot k h (g i) x * diffQuot k h U x)
      (volume : Measure E) := by
    intro i j
    have hc : Continuous (fun x : E =>
        2 * translate k h (fun y : E => B.a y i j) x * eta x *
          (fderiv ℝ eta x) (EuclideanSpace.single j 1)) :=
      (((continuous_const.mul (htrans_cont i j)).mul heta.continuous).mul
        ((heta.continuous_fderiv (by simp)).clm_apply continuous_const))
    have hs : HasCompactSupport (fun x : E =>
        2 * translate k h (fun y : E => B.a y i j) x * eta x *
          (fderiv ℝ eta x) (EuclideanSpace.single j 1)) := by
      apply HasCompactSupport.intro' (K := tsupport eta) heta_cpt.isCompact
        (isClosed_tsupport eta)
      intro x hx
      have hetax : eta x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hetax]
    exact integrable_cpt_mul_two hc hs (hdq_g_l2 i) hdq_U_l2
  have hC2_int : ∀ i j : Fin d, Integrable (fun x =>
      diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
        g i x * diffQuot k h (g j) x) (volume : Measure E) := by
    intro i j
    exact integrable_cpt_mul_two ((hdq_B_cont i j).mul (heta.continuous.pow 2))
      heta_sq_cpt.mul_left (hg_l2 i) (hdq_g_l2 j)
  have hC3_int : ∀ i j : Fin d, Integrable (fun x =>
      2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
        (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
        g i x * diffQuot k h U x) (volume : Measure E) := by
    intro i j
    have hc : Continuous (fun x : E =>
        2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
          (fderiv ℝ eta x) (EuclideanSpace.single j 1)) :=
      (((continuous_const.mul (hdq_B_cont i j)).mul heta.continuous).mul
        ((heta.continuous_fderiv (by simp)).clm_apply continuous_const))
    have hs : HasCompactSupport (fun x : E =>
        2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
          (fderiv ℝ eta x) (EuclideanSpace.single j 1)) := by
      apply HasCompactSupport.intro' (K := tsupport eta) heta_cpt.isCompact
        (isClosed_tsupport eta)
      intro x hx
      have hetax : eta x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hetax]
    exact integrable_cpt_mul_two hc hs (hg_l2 i) hdq_U_l2
  have hibp_expanded : ∀ i j : Fin d,
      (∫ x, aK i j x * g i x * diffQuot k (-h) (F j) x
        ∂(volume : Measure E)) =
      -((∫ x, translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
            diffQuot k h (g i) x * diffQuot k h (g j) x
          ∂(volume : Measure E)) +
        (∫ x, 2 * translate k h (fun y : E => B.a y i j) x * eta x *
            (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
            diffQuot k h (g i) x * diffQuot k h U x
          ∂(volume : Measure E)) +
        (∫ x, diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
            g i x * diffQuot k h (g j) x ∂(volume : Measure E)) +
        ∫ x, 2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
            (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
            g i x * diffQuot k h U x ∂(volume : Measure E)) := by
    intro i j
    have hibp := ibp_pair (d := d) (Omega := Set.univ) (K := tsupport eta)
      (a := aK i j) (g := g i) (F := F j) k h
      (coeff_mul_memLp B hK_compact (hg_l2 i) i j) (hF_l2 j)
      (inner_tsupport eta U (g j) j k h) (fun _ _ => trivial)
    simp only [setIntegral_univ] at hibp
    have hfun : (fun x =>
        (translate k h (aK i j) x * diffQuot k h (g i) x +
          diffQuot k h (aK i j) x * g i x) * F j x) =
      fun x =>
        translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
            diffQuot k h (g i) x * diffQuot k h (g j) x +
          (2 * translate k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              diffQuot k h (g i) x * diffQuot k h U x +
            (diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
                g i x * diffQuot k h (g j) x +
              2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
                (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
                g i x * diffQuot k h U x)) := by
      funext x
      by_cases hx : x ∈ tsupport eta
      · have hxK : x ∈ K :=
          hroom_K ((Metric.self_subset_cthickening (tsupport eta)) hx)
        have hx_shiftK : x + h • EuclideanSpace.single k 1 ∈ K := by
          apply hroom_K
          refine Metric.mem_cthickening_of_dist_le _ x |h| (tsupport eta) hx ?_
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
          simp
        have htrans : translate k h (aK i j) x =
            translate k h (fun y : E => B.a y i j) x := by
          change aK i j (x + h • EuclideanSpace.single k 1) =
            B.a (x + h • EuclideanSpace.single k 1) i j
          simp [aK, hx_shiftK]
        have hdq : diffQuot k h (aK i j) x =
            diffQuot k h (fun y : E => B.a y i j) x := by
          rw [diffQuot_apply_of_ne (d := d) k hh,
            diffQuot_apply_of_ne (d := d) k hh]
          simp [aK, hxK, hx_shiftK]
        rw [htrans, hdq]
        simp only [F]
        ring
      · have hetax : eta x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [F, hetax]
    rw [hfun] at hibp
    have hsplit₁ := integral_add (hP_int i j)
      ((hC1_int i j).add ((hC2_int i j).add (hC3_int i j)))
    have hsplit₂ := integral_add (hC1_int i j)
      ((hC2_int i j).add (hC3_int i j))
    have hsplit₃ := integral_add (hC2_int i j) (hC3_int i j)
    simp only [Pi.add_apply] at hsplit₁ hsplit₂ hsplit₃
    rw [hsplit₁, hsplit₂, hsplit₃] at hibp
    simpa [add_assoc] using hibp
  have hsum_ibp :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
        aK i j x * g i x * diffQuot k (-h) (F j) x
        ∂(volume : Measure E)) =
      -((∑ i : Fin d, ∑ j : Fin d, ∫ x,
          translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
            diffQuot k h (g i) x * diffQuot k h (g j) x
          ∂(volume : Measure E)) +
        (∑ i : Fin d, ∑ j : Fin d, ∫ x,
            2 * translate k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              diffQuot k h (g i) x * diffQuot k h U x
            ∂(volume : Measure E)) +
        (∑ i : Fin d, ∑ j : Fin d, ∫ x,
            diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
              g i x * diffQuot k h (g j) x ∂(volume : Measure E)) +
        (∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
            (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
            g i x * diffQuot k h U x ∂(volume : Measure E))) := by
    calc
      _ = ∑ i : Fin d, ∑ j : Fin d,
          -((∫ x, translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
                diffQuot k h (g i) x * diffQuot k h (g j) x
              ∂(volume : Measure E)) +
            (∫ x, 2 * translate k h (fun y : E => B.a y i j) x * eta x *
                (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
                diffQuot k h (g i) x * diffQuot k h U x
              ∂(volume : Measure E)) +
            (∫ x, diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
                g i x * diffQuot k h (g j) x ∂(volume : Measure E)) +
            (∫ x, 2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
                (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
                g i x * diffQuot k h U x ∂(volume : Measure E))) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            exact hibp_expanded i j
      _ = _ := by
        simp_rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hP_sum :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
        translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
          diffQuot k h (g i) x * diffQuot k h (g j) x
        ∂(volume : Measure E)) =
      ∫ x, (∑ i : Fin d, ∑ j : Fin d,
        translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
          diffQuot k h (g i) x * diffQuot k h (g j) x)
        ∂(volume : Measure E) := by
    have hinner : ∀ i : Fin d, Integrable (fun x => ∑ j : Fin d,
        translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
          diffQuot k h (g i) x * diffQuot k h (g j) x)
        (volume : Measure E) := fun i =>
      integrable_finsetSum _ (fun j _ => hP_int i j)
    rw [integral_finsetSum _ (fun i _ => hinner i)]
    simp_rw [integral_finsetSum _ (fun j _ => hP_int _ j)]
  rw [hsum_ibp] at hpre_sum_eq
  have hterms_eq :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
        translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
          diffQuot k h (g i) x * diffQuot k h (g j) x
        ∂(volume : Measure E)) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
        2 * translate k h (fun y : E => B.a y i j) x * eta x *
          (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
          diffQuot k h (g i) x * diffQuot k h U x
        ∂(volume : Measure E)) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
        diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
          g i x * diffQuot k h (g j) x ∂(volume : Measure E)) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
        2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
          (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
          g i x * diffQuot k h U x ∂(volume : Measure E)) = -(rho⁻¹ * r) := by
    linarith
  rw [hP_sum] at hterms_eq
  simpa [g] using hterms_eq

end DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
