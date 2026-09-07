import DifferentialGeometry.Analysis.Sobolev.Nirenberg.MasterInequality.WeakSolution
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.IntegralBound
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.LocalWeakLimit
import DifferentialGeometry.Analysis.Integration.LpNorm

noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open scoped ENNReal BigOperators

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem nirenbergTestFunction_eq_of_eqOn
    {K : Set E} {eta u U : E → ℝ}
    (hU_eq : ∀ x ∈ K, U x = u x)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ K) :
    nirenbergTestFunction k h eta U = nirenbergTestFunction k h eta u := by
  unfold nirenbergTestFunction
  apply congrArg (diffQuot k (-h))
  funext x
  by_cases hx : x ∈ tsupport eta
  · have hxK : x ∈ K :=
      hroom ((Metric.self_subset_cthickening (tsupport eta)) hx)
    have hx_shiftK : x + h • EuclideanSpace.single k 1 ∈ K := by
      apply hroom
      refine Metric.mem_cthickening_of_dist_le _ x |h| (tsupport eta) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp
    rw [diffQuot_apply_of_ne (d := d) k hh,
      diffQuot_apply_of_ne (d := d) k hh,
      hU_eq x hxK, hU_eq _ hx_shiftK]
  · have hetax : eta x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hetax]

omit [NeZero d] in
private theorem subset_tsupport_of_eq_one
    {V : Set E} {eta : E → ℝ}
    (heta_one : ∀ x ∈ V, eta x = 1) :
    V ⊆ tsupport eta := by
  intro x hx
  apply subset_tsupport eta
  intro hzero
  have hone := heta_one x hx
  rw [hzero] at hone
  norm_num at hone

omit [NeZero d] in
private theorem diffQuot_eqOn_of_cthickening_eqOn
    {eta : E → ℝ} {R₀ h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    {V : Set E} (hV_tsupp : V ⊆ tsupport eta)
    {g G : E → ℝ}
    (hgrad_eq : ∀ x ∈ Metric.cthickening R₀ (tsupport eta), G x = g x)
    (k : Fin d) :
    ∀ x ∈ V, diffQuot k h G x = diffQuot k h g x := by
  intro x hxV
  have hx_tsupp : x ∈ tsupport eta := hV_tsupp hxV
  have hxK : x ∈ Metric.cthickening R₀ (tsupport eta) :=
    (Metric.self_subset_cthickening (tsupport eta)) hx_tsupp
  have hx_shiftK : x + h • EuclideanSpace.single k 1 ∈
      Metric.cthickening R₀ (tsupport eta) := by
    refine Metric.mem_cthickening_of_dist_le _ x R₀ (tsupport eta) hx_tsupp ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    simpa using hh_le
  rw [diffQuot_apply_of_ne (d := d) k hh,
    diffQuot_apply_of_ne (d := d) k hh,
    hgrad_eq _ hx_shiftK, hgrad_eq x hxK]

theorem exists_eLpNorm_diffQuot_weakGrad_le
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega))
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (heta_range : Set.range eta ⊆ Set.Icc (0 : ℝ) 1)
    {R₀ : ℝ}
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    (hcoeff : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j)
    {V : Set E} (hV_meas : MeasurableSet V)
    (heta_one : ∀ x ∈ V, eta x = 1)
    (i k : Fin d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℝ, |h| ≤ R₀ →
      eLpNorm (diffQuot k h (fun x => hu.weakGrad x i)) 2
        ((volume : Measure E).restrict V) ≤ ENNReal.ofReal M := by
  classical
  by_cases hR₀ : 0 < R₀
  swap
  · refine ⟨0, le_rfl, ?_⟩
    intro h hh
    have hz : h = 0 := abs_nonpos_iff.mp (hh.trans (le_of_not_gt hR₀))
    simp [hz]
  obtain ⟨N, hderiv⟩ := (heta.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (heta_cpt.fderiv (𝕜 := ℝ))
  have hN : 0 ≤ N :=
    (norm_nonneg (fderiv ℝ eta (0 : E))).trans (hderiv 0)
  obtain ⟨U, hU, hU_eq, hgrad_eq, hmaster⟩ :=
    exists_extension_nirenberg_master_inequality hOmega hu hweak B hrho heta heta_cpt
      hK_Omega hcoeff k
  let g : Fin d → E → ℝ := fun j x => hU.weakGrad x j
  have hU_l2 : MemLp U 2 (volume : Measure E) := by
    simpa only [Measure.restrict_univ] using hU.memLp
  have hg_l2 : ∀ j : Fin d, MemLp (g j) 2 (volume : Measure E) := by
    intro j
    simpa only [g, Measure.restrict_univ] using hU.weakGrad_component_memLp j
  let fGlobal : E → ℝ := Omega.indicator (fun x => rho⁻¹ * f x)
  have hfGlobal : MemLp fGlobal 2 (volume : Measure E) := by
    change MemLp (Omega.indicator (fun x => rho⁻¹ * f x)) 2 (volume : Measure E)
    rw [MeasureTheory.memLp_indicator_iff_restrict hOmega.measurableSet]
    simpa only [smul_eq_mul] using hf.const_mul (rho⁻¹)
  have hfGlobal_loc : ∀ {W : Set E}, IsCompact (closure W) →
      MemLp fGlobal 2 ((volume : Measure E).restrict W) := by
    intro W _
    exact hfGlobal.restrict W
  let Omega' : Set E := Metric.thickening (R₀ + 1) (tsupport eta)
  have hOmega'_open : IsOpen Omega' := Metric.isOpen_thickening
  have hOmega'_compact : IsCompact (closure Omega') := by
    have hsub : closure Omega' ⊆
        Metric.cthickening (R₀ + 1) (tsupport eta) :=
      Metric.closure_thickening_subset_cthickening _ _
    exact heta_cpt.cthickening.of_isClosed_subset isClosed_closure hsub
  have hroom_Omega' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport eta) ⊆ Omega' := by
    intro h hh_le
    exact Metric.cthickening_subset_thickening' (by linarith) (by linarith) _
  have hFK : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport eta, (diffQuot k h U x) ^ 2
          ∂(volume : Measure E) ≤
        ∫ x in Omega', ∑ j : Fin d, (g j x) ^ 2
          ∂(volume : Measure E) := by
    intro h hh hh_le
    have htsupp_compact : IsCompact (closure (tsupport eta)) := by
      simpa only [(isClosed_tsupport eta).closure_eq] using heta_cpt.isCompact
    have hthick : Metric.cthickening R₀ (closure (tsupport eta)) ⊆ Omega' := by
      simpa only [(isClosed_tsupport eta).closure_eq] using
        (Metric.cthickening_subset_thickening' (by linarith : 0 < R₀ + 1)
          (by linarith : R₀ < R₀ + 1) (tsupport eta))
    have hsingle :=
      integral_sq_diffQuot_le_integral_sq_weakPartial_meas
        (d := d) hU_l2 (hg_l2 k) k (hU.isWeakGrad k)
        hOmega'_open.measurableSet (isClosed_tsupport eta).measurableSet
        htsupp_compact hR₀ hthick hh hh_le
    have hk_int : Integrable (fun x => (g k x) ^ 2)
        ((volume : Measure E).restrict Omega') :=
      ((hg_l2 k).mono_measure Measure.restrict_le_self).integrable_sq
    have hsum_int : Integrable (fun x => ∑ j : Fin d, (g j x) ^ 2)
        ((volume : Measure E).restrict Omega') :=
      integrable_finsetSum Finset.univ fun j _ =>
        ((hg_l2 j).mono_measure Measure.restrict_le_self).integrable_sq
    exact hsingle.trans (integral_mono hk_int hsum_int fun x =>
      Finset.single_le_sum (fun j _ => sq_nonneg (g j x)) (Finset.mem_univ k))
  have htest : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (nirenbergTestFunction k h eta U x) ^ 2 ∂(volume : Measure E) ≤
        8 * N ^ 2 *
          ∫ x in tsupport eta, (diffQuot k h U x) ^ 2
            ∂(volume : Measure E) +
        2 * ∫ x, eta x ^ 2 * (diffQuot k h (g k) x) ^ 2
          ∂(volume : Measure E) := by
    intro h _ _
    refine integral_sq_nirenbergTestFunction_le hU_l2 (hg_l2 k) k (hU.isWeakGrad k)
      heta heta_cpt (fun x => ?_) (fun x => ?_) h
    · have hx := heta_range (Set.mem_range_self x)
      exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    · have hpartial := (fderiv ℝ eta x).le_opNorm (EuclideanSpace.single k 1)
      simpa [Real.norm_eq_abs] using hpartial.trans
        (mul_le_mul_of_nonneg_right (hderiv x) (norm_nonneg _))
  have hsource_eq {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀) :
      ∫ x in (Set.univ : Set E),
          fGlobal x * nirenbergTestFunction k h eta U x
            ∂(volume : Measure E) =
        rho⁻¹ * ∫ x in Omega,
          f x * nirenbergTestFunction k h eta u x
            ∂(volume : Measure E) := by
    have hroom : Metric.cthickening |h| (tsupport eta) ⊆
        Metric.cthickening R₀ (tsupport eta) :=
      Metric.cthickening_mono hh_le _
    have htest_eq : nirenbergTestFunction k h eta U =
        nirenbergTestFunction k h eta u :=
      nirenbergTestFunction_eq_of_eqOn (d := d) hU_eq k hh hroom
    rw [setIntegral_univ]
    calc
      _ = ∫ x, Omega.indicator (fun y =>
          rho⁻¹ * (f y * nirenbergTestFunction k h eta u y)) x
            ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Omega
        · rw [congrFun htest_eq x]
          simp only [fGlobal, Set.indicator_of_mem hx]
          ring
        · simp only [fGlobal, Set.indicator_of_notMem hx, zero_mul]
      _ = ∫ x in Omega,
          rho⁻¹ * (f x * nirenbergTestFunction k h eta u x)
            ∂(volume : Measure E) :=
        MeasureTheory.integral_indicator hOmega.measurableSet
      _ = _ := integral_const_mul _ _
  let C : ℝ := nirenbergMasterYoungConstant (d := d) B N hOmega'_compact k
  let energy : ℝ :=
    (∫ x in Omega', ∑ j : Fin d, (g j x) ^ 2 ∂(volume : Measure E)) +
      ∫ x in Omega', U x ^ 2 ∂(volume : Measure E) +
      ∫ x in Omega', fGlobal x ^ 2 ∂(volume : Measure E)
  let S : ℝ := C * energy / (B.lam / 2)
  have hlam_half : 0 < B.lam / 2 := half_pos B.ellipticity_pos
  refine ⟨Real.sqrt S, Real.sqrt_nonneg S, ?_⟩
  intro h hh_le
  by_cases hh : h = 0
  · simp [hh]
  have hquant_h :=
    nirenberg_diffQuot_g_localL2_bound_quantitative
      (d := d) (Ω := Set.univ) (u := U) (f := fGlobal) (g := g)
      B hU_l2 hfGlobal_loc hg_l2
      heta heta_cpt heta_range hN hderiv hOmega'_open (subset_univ _)
      hOmega'_compact hroom_Omega'
      heta_one hV_meas k
      hFK htest (fun {h} hh hh_le => by
        rw [hsource_eq hh hh_le]
        exact (hmaster hh_le).trans (le_add_of_nonneg_right (abs_nonneg _))) hh hh_le
  have hsum_le :
      ∫ x in V, ∑ j : Fin d, (diffQuot k h (g j) x) ^ 2
          ∂(volume : Measure E) ≤ S := by
    apply (le_div_iff₀ hlam_half).2
    calc
      (∫ x in V, ∑ j : Fin d, (diffQuot k h (g j) x) ^ 2
          ∂(volume : Measure E)) * (B.lam / 2) =
          (B.lam / 2) * ∫ x in V,
            ∑ j : Fin d, (diffQuot k h (g j) x) ^ 2
              ∂(volume : Measure E) := mul_comm _ _
      _ ≤ C * energy := by
        simpa [C, energy] using hquant_h
  have hU_bound : eLpNorm (diffQuot k h (g i)) 2 (volume.restrict V) ≤
      ENNReal.ofReal (Real.sqrt S) :=
    DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_sum_norm_sq_le
      (s := Finset.univ) (fun j _ => (memLp_diffQuot k h (hg_l2 j)).restrict V)
      (Finset.mem_univ i) (by simpa only [Real.norm_eq_abs, sq_abs] using hsum_le)
  have hV_tsupp : V ⊆ tsupport eta :=
    subset_tsupport_of_eq_one heta_one
  have hdq_eq : diffQuot k h (g i) =ᵐ[(volume : Measure E).restrict V]
      diffQuot k h (fun x => hu.weakGrad x i) := by
    filter_upwards [ae_restrict_mem hV_meas] with x hx
    exact diffQuot_eqOn_of_cthickening_eqOn (d := d) hh hh_le hV_tsupp
      (fun y hy => hgrad_eq y hy i) k x hx
  rw [← eLpNorm_congr_ae hdq_eq]
  exact hU_bound

end DeGiorgi
