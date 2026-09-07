import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.WeakRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.External.DeGiorgi.Localization

noncomputable section

open MeasureTheory Filter Set
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open scoped ENNReal

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_mul_compact
    {f g : E → ℝ} (hf : Continuous f) (hf_cpt : HasCompactSupport f)
    (hg : MemLp g 2 (volume : Measure E)) :
    MemLp (fun x => f x * g x) 2 (volume : Measure E) := by
  exact hg.mul' (r := 2) (hf.memLp_top_of_hasCompactSupport hf_cpt volume)

private noncomputable def nirenbergTestWitnessUniv
    {u : E → ℝ} (hu : MemW1pWitness 2 u Set.univ)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ) :
    MemW1pWitness 2 (NirenbergTestFunction.nirenbergTestFunction k h eta u) Set.univ := by
  classical
  let grad : Fin d → E → ℝ := fun j =>
    diffQuot k (-h) (fun y =>
      (eta y) ^ 2 * diffQuot k h (fun x => hu.weakGrad x j) y +
        2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
  let G : E → E := fun x => WithLp.toLp 2 fun j => grad j x
  have hu_l2 : MemLp u 2 (volume : Measure E) := by
    simpa using hu.memLp
  have hgrad_l2 : ∀ j : Fin d,
      MemLp (fun x => hu.weakGrad x j) 2 (volume : Measure E) := by
    intro j
    simpa using hu.weakGrad_component_memLp j
  have hdq_u : MemLp (diffQuot k h u) 2 (volume : Measure E) :=
    memLp_diffQuot k h hu_l2
  have heta_sq_cont : Continuous (fun x : E => (eta x) ^ 2) :=
    heta.continuous.pow 2
  have heta_sq_cpt : HasCompactSupport (fun x : E => (eta x) ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using heta_cpt.mul_right (f' := eta)
  have hF_l2 : MemLp (fun x => (eta x) ^ 2 * diffQuot k h u x) 2
      (volume : Measure E) :=
    memLp_mul_compact heta_sq_cont heta_sq_cpt hdq_u
  have htest_l2 : MemLp (NirenbergTestFunction.nirenbergTestFunction k h eta u) 2
      (volume : Measure E) := by
    change MemLp (diffQuot k (-h) (fun x => (eta x) ^ 2 * diffQuot k h u x)) 2
      (volume : Measure E)
    exact memLp_diffQuot k (-h) hF_l2
  have hgrad_component_l2 : ∀ j : Fin d,
      MemLp (grad j) 2 (volume : Measure E) := by
    intro j
    have hdq_g : MemLp (diffQuot k h (fun x => hu.weakGrad x j)) 2
        (volume : Measure E) :=
      memLp_diffQuot k h (hgrad_l2 j)
    have hterm1 : MemLp
        (fun x => (eta x) ^ 2 * diffQuot k h (fun y => hu.weakGrad y j) x) 2
        (volume : Measure E) :=
      memLp_mul_compact heta_sq_cont heta_sq_cpt hdq_g
    let coeff : E → ℝ := fun x =>
      2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single j 1)
    have hcoeff_cont : Continuous coeff := by
      exact (continuous_const.mul heta.continuous).mul
        ((heta.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hcoeff_cpt : HasCompactSupport coeff := by
      apply HasCompactSupport.intro'
        (K := tsupport eta) heta_cpt.isCompact (isClosed_tsupport eta)
      intro x hx
      have hetax : eta x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [coeff, hetax]
    have hterm2 : MemLp
        (fun x => coeff x * diffQuot k h u x) 2 (volume : Measure E) :=
      memLp_mul_compact hcoeff_cont hcoeff_cpt hdq_u
    have hsum : MemLp
        (fun x =>
          (eta x) ^ 2 * diffQuot k h (fun y => hu.weakGrad y j) x +
            coeff x * diffQuot k h u x) 2 (volume : Measure E) :=
      hterm1.add hterm2
    change MemLp (diffQuot k (-h) (fun x =>
      (eta x) ^ 2 * diffQuot k h (fun y => hu.weakGrad y j) x +
        2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
          diffQuot k h u x)) 2 (volume : Measure E)
    simpa [coeff, mul_assoc] using memLp_diffQuot k (-h) hsum
  refine
    { memLp := by simpa using htest_l2
      weakGrad := G
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · intro j
    simpa [G, PiLp.toLp_apply] using hgrad_component_l2 j
  · intro j
    simpa [G, grad, PiLp.toLp_apply] using
      (hasWeakPartialDeriv_nirenbergTestFunction (d := d) k j h heta
        (by simpa using hu_l2.locallyIntegrable (by norm_num))
        (by simpa using (hgrad_l2 j).locallyIntegrable (by norm_num))
        (hu.isWeakGrad j))

private theorem fderiv_cutoff_zero
    {K : Set E} {delta : ℝ} (hdelta : 0 < delta)
    {chi : E → ℝ}
    (hchi_one : ∀ x ∈ Metric.cthickening delta K, chi x = 1)
    {x : E} (hx : x ∈ K) (i : Fin d) :
    (fderiv ℝ chi x) (EuclideanSpace.single i 1) = 0 := by
  have hchi_eq : chi =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    refine Filter.mem_of_superset
      (Metric.ball_mem_nhds x (by linarith : 0 < delta / 2)) ?_
    intro y hy
    rw [Metric.mem_ball] at hy
    have hy_closed : y ∈ Metric.closedBall x (delta / 2) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt hy
    have hy_thick_half : y ∈ Metric.cthickening (delta / 2) K :=
      Metric.closedBall_subset_cthickening hx (delta / 2) hy_closed
    exact hchi_one y
      (Metric.cthickening_mono (by linarith : delta / 2 ≤ delta) K hy_thick_half)
  rw [Filter.EventuallyEq.fderiv_eq hchi_eq]
  simp

noncomputable def MemW1pWitness.nirenbergTestFunction
    {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : MemW1pWitness 2 u Omega)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega) :
    MemW1pWitness 2 (NirenbergTestFunction.nirenbergTestFunction k h eta u) Omega := by
  classical
  letI : NeZero d := ⟨Nat.ne_zero_of_lt k.isLt⟩
  let K : Set E := Metric.cthickening |h| (tsupport eta)
  have hK_cpt : IsCompact K := heta_cpt.isCompact.cthickening
  let hcutoff :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := d) hK_cpt hOmega hroom
  let delta := Classical.choose hcutoff
  let chi := Classical.choose (Classical.choose_spec hcutoff)
  have hspec := Classical.choose_spec (Classical.choose_spec hcutoff)
  have hdelta : 0 < delta := hspec.1
  have hchi : ContDiff ℝ (⊤ : ℕ∞) chi := hspec.2.2.1
  have hchi_cpt : HasCompactSupport chi := hspec.2.2.2.1
  have hchi_range : Set.range chi ⊆ Set.Icc (0 : ℝ) 1 := hspec.2.2.2.2.1
  have hchi_one : ∀ x ∈ Metric.cthickening delta K, chi x = 1 := hspec.2.2.2.2.2.1
  have hchi_sub : tsupport chi ⊆ Omega := hspec.2.2.2.2.2.2
  have hchi_bound : ∀ x, |chi x| ≤ 1 := by
    intro x
    rcases hchi_range ⟨x, rfl⟩ with ⟨hx0, hx1⟩
    simpa [abs_of_nonneg hx0] using hx1
  have hchi_deriv_cpt : HasCompactSupport (fderiv ℝ chi) :=
    hchi_cpt.fderiv (𝕜 := ℝ)
  have hC_exists := hchi_deriv_cpt.isCompact.exists_bound_of_continuousOn
    ((hchi.continuous_fderiv (by simp)).continuousOn)
  let C : ℝ := Classical.choose hC_exists
  have hC := Classical.choose_spec hC_exists
  let C1 : ℝ := max C 0
  have hC1 : 0 ≤ C1 := le_max_right _ _
  have hchi_deriv_bound : ∀ x, ‖fderiv ℝ chi x‖ ≤ C1 := by
    intro x
    by_cases hx : x ∈ tsupport (fderiv ℝ chi)
    · exact (hC x hx).trans (le_max_left _ _)
    · have hz : fderiv ℝ chi x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [C1, hz]
  let huv : MemW1pWitness 2 (fun x => chi x * u x) Omega :=
    hu.mulSmoothBoundedP (d := d) (by norm_num) hOmega hchi
      zero_le_one hC1 hchi_bound hchi_deriv_bound
  have hv_cpt : HasCompactSupport (fun x => chi x * u x) := hchi_cpt.mul_right
  have hv_sub : tsupport (fun x => chi x * u x) ⊆ Omega :=
    (tsupport_smul_subset_left chi u).trans hchi_sub
  have hv0 : MemW01p (ENNReal.ofReal (2 : ℝ))
      (fun x => chi x * u x) Omega := by
    have hvW : MemW1p (ENNReal.ofReal (2 : ℝ))
        (fun x => chi x * u x) Omega := by
      simpa [huv] using huv.memW1p
    exact memW01p_of_memW1p_of_tsupport_subset
      (d := d) hOmega (p := (2 : ℝ)) (by norm_num) hvW hv_cpt hv_sub
  let huv_real : MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (fun x => chi x * u x) Omega :=
    { memLp := by simpa using huv.memLp
      weakGrad := huv.weakGrad
      weakGrad_component_memLp := by
        intro i
        simpa using huv.weakGrad_component_memLp i
      isWeakGrad := huv.isWeakGrad }
  let huvExtRaw : MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (Omega.indicator (fun x => chi x * u x)) Set.univ :=
    zeroExtendMemW1pWitnessP (d := d) hOmega
      (p := 2) (by norm_num : (1 : ℝ) < 2) hv0 huv_real
  have hindicator : Omega.indicator (fun x => chi x * u x) =
      (fun x => chi x * u x) := by
    funext x
    by_cases hx : x ∈ Omega
    · simp [hx]
    · have hchix : chi x = 0 := by
        apply zero_outside_of_tsupport_subset hchi_sub hx
      simp [hx, hchix]
  let huvExtRaw2 : MemW1pWitness 2
      (Omega.indicator (fun x => chi x * u x)) Set.univ :=
    { memLp := by simpa using huvExtRaw.memLp
      weakGrad := huvExtRaw.weakGrad
      weakGrad_component_memLp := by
        intro i
        simpa using huvExtRaw.weakGrad_component_memLp i
      isWeakGrad := huvExtRaw.isWeakGrad }
  let huvExt : MemW1pWitness 2
      (fun x => chi x * u x) Set.univ :=
    MemW1pWitness.ofAeEq
      (Filter.Eventually.of_forall fun x => congrFun hindicator x) huvExtRaw2
  let hwExt := nirenbergTestWitnessUniv (d := d) huvExt heta heta_cpt k h
  have hchi_one_K : ∀ x ∈ K, chi x = 1 := by
    intro x hx
    exact hchi_one x (Metric.self_subset_cthickening K hx)
  have hinner : (fun y => (eta y) ^ 2 *
        diffQuot k h (fun x => chi x * u x) y) =
      (fun y => (eta y) ^ 2 * diffQuot k h u y) := by
    funext y
    by_cases hy : y ∈ tsupport eta
    · have hyK : y ∈ K := Metric.self_subset_cthickening (tsupport eta) hy
      have hyhK : y + h • EuclideanSpace.single k 1 ∈ K := by
        refine Metric.mem_cthickening_of_dist_le _ y |h| (tsupport eta) hy ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
        simp
      have hchiy : chi y = 1 := hchi_one_K y hyK
      have hchiyh : chi (y + h • EuclideanSpace.single k 1) = 1 :=
        hchi_one_K _ hyhK
      by_cases hh : h = 0
      · subst hh
        simp
      · rw [diffQuot_apply_of_ne (d := d) k hh,
          diffQuot_apply_of_ne (d := d) k hh]
        simp [hchiy, hchiyh]
    · have hetay : eta y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hetay]
  have hgrad_K : ∀ x ∈ K, ∀ i : Fin d,
      huvExt.weakGrad x i = hu.weakGrad x i := by
    intro x hx i
    have hxOmega : x ∈ Omega := hroom hx
    have hchi_x : chi x = 1 := hchi_one_K x hx
    have hfd_x : (fderiv ℝ chi x) (EuclideanSpace.single i 1) = 0 := by
      exact fderiv_cutoff_zero (K := K) (delta := delta) hdelta
        (chi := chi) hchi_one hx i
    simp [huvExt, huvExtRaw2, huvExtRaw, huv_real, huv,
      MemW1pWitness.ofAeEq,
      zeroExtendMemW1pWitnessP,
      MemW1pWitness.mulSmoothBoundedP,
      PiLp.toLp_apply, hxOmega, hchi_x, hfd_x]
  have hinner_grad : ∀ i : Fin d,
      (fun y =>
        (eta y) ^ 2 * diffQuot k h (fun x => huvExt.weakGrad x i) y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h (fun x => chi x * u x) y) =
      (fun y =>
        (eta y) ^ 2 * diffQuot k h (fun x => hu.weakGrad x i) y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h u y) := by
    intro i
    funext y
    by_cases hy : y ∈ tsupport eta
    · have hyK : y ∈ K := Metric.self_subset_cthickening (tsupport eta) hy
      have hyhK : y + h • EuclideanSpace.single k 1 ∈ K := by
        refine Metric.mem_cthickening_of_dist_le _ y |h| (tsupport eta) hy ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
        simp
      have hgrad_y := hgrad_K y hyK i
      have hgrad_yh := hgrad_K _ hyhK i
      have hchi_y : chi y = 1 := hchi_one_K y hyK
      have hchi_yh : chi (y + h • EuclideanSpace.single k 1) = 1 :=
        hchi_one_K _ hyhK
      by_cases hh : h = 0
      · subst hh
        simp
      · rw [diffQuot_apply_of_ne (d := d) k hh,
          diffQuot_apply_of_ne (d := d) k hh,
          diffQuot_apply_of_ne (d := d) k hh,
          diffQuot_apply_of_ne (d := d) k hh]
        simp [hgrad_y, hgrad_yh, hchi_y, hchi_yh]
    · have heta_y : eta y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [heta_y]
  have htest_eq : NirenbergTestFunction.nirenbergTestFunction k h eta (fun x => chi x * u x) =
      NirenbergTestFunction.nirenbergTestFunction k h eta u := by
    unfold NirenbergTestFunction.nirenbergTestFunction
    rw [hinner]
  let htestRestrict := hwExt.restrict hOmega (subset_univ Omega)
  let hwRaw := MemW1pWitness.ofAeEq
    (Filter.Eventually.of_forall fun x => congrFun htest_eq x) htestRestrict
  let explicitGrad : E → E := fun x => WithLp.toLp 2 fun i =>
    diffQuot k (-h) (fun y =>
      (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
        2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
          diffQuot k h u y) x
  have hraw_grad : ∀ x i, hwRaw.weakGrad x i = explicitGrad x i := by
    intro x i
    change diffQuot k (-h) (fun y =>
      (eta y) ^ 2 * diffQuot k h (fun z => huvExt.weakGrad z i) y +
        2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
          diffQuot k h (fun z => chi z * u z) y) x = _
    rw [hinner_grad i]
  refine
    { memLp := hwRaw.memLp
      weakGrad := explicitGrad
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · intro i
    have heq : (fun x => explicitGrad x i) = (fun x => hwRaw.weakGrad x i) := by
      funext x
      exact (hraw_grad x i).symm
    rw [heq]
    exact hwRaw.weakGrad_component_memLp i
  · intro i
    have heq : (fun x => explicitGrad x i) = (fun x => hwRaw.weakGrad x i) := by
      funext x
      exact (hraw_grad x i).symm
    rw [heq]
    exact hwRaw.isWeakGrad i

@[simp] theorem MemW1pWitness.nirenbergTestFunction_weakGrad_apply
    {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : MemW1pWitness 2 u Omega)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega)
    (x : E) (i : Fin d) :
    (MemW1pWitness.nirenbergTestFunction (d := d) hOmega hu heta heta_cpt k h hroom).weakGrad x i =
      diffQuot k (-h) (fun y =>
        (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h u y) x := by
  rfl

theorem memH01_nirenbergTestFunction
    {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : MemW1pWitness 2 u Omega)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega) :
    MemH01 (NirenbergTestFunction.nirenbergTestFunction k h eta u) Omega := by
  let : NeZero d := ⟨Nat.ne_zero_of_lt k.isLt⟩
  have hw := MemW1pWitness.nirenbergTestFunction (d := d) hOmega hu heta heta_cpt k h hroom
  have htest_sub : tsupport (NirenbergTestFunction.nirenbergTestFunction k h eta u) ⊆ Omega :=
    (tsupport_nirenbergTestFunction_subset eta u k h).trans hroom
  have hw' : MemW1p (ENNReal.ofReal (2 : ℝ))
      (NirenbergTestFunction.nirenbergTestFunction k h eta u) Omega := by
    simpa using hw.memW1p
  simpa using memW01p_of_memW1p_of_tsupport_subset
    (d := d) hOmega (p := (2 : ℝ)) (by norm_num) hw'
    (hasCompactSupport_nirenbergTestFunction heta_cpt k h) htest_sub

end DeGiorgi
