import DifferentialGeometry.Analysis.Sobolev.Euclidean.Approximation.ContinuousTests
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.FirstVariation
import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Composition

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

private theorem aestronglyMeasurable_clm_apply_variable
    {P X Y : Type*} [MeasurableSpace P] {μ : Measure P}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {B : P → X →L[ℝ] Y} {v : P → X}
    (hB : AEStronglyMeasurable B μ) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => B x (v x)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hB.prodMk hv)

private theorem tendsto_integral_bilinear_of_tendsto_eLpNorm
    {P F : Type*} [MeasurableSpace P] {μ : Measure P}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : P → F →L[ℝ] F →L[ℝ] ℝ) (hB : AEStronglyMeasurable B μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖B x‖ ≤ C)
    {v : P → F} (hv : MemLp v 2 μ) {w : ℕ → P → F} {w₀ : P → F}
    (hw : ∀ n, MemLp (w n) 2 μ) (hw₀ : MemLp w₀ 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => w n x - w₀ x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, B x (v x) (w n x) ∂μ) atTop
      (𝓝 (∫ x, B x (v x) (w₀ x) ∂μ)) := by
  let V := hv.toLp v
  let W (n : ℕ) := (hw n).toLp (w n)
  let W₀ := hw₀.toLp w₀
  have hW : Tendsto W atTop (𝓝 W₀) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' w hw w₀ hw₀).mpr hlim
  have hcont := continuous_integral_bilinear_lp_right B
    (fun a b => (hB.apply_continuousLinearMap a).apply_continuousLinearMap b) hC V
  have hn (n : ℕ) : (∫ x, B x (V x) (W n x) ∂μ) = ∫ x, B x (v x) (w n x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp, (hw n).coeFn_toLp] with x hx hy
    rw [show V x = v x from hx, show W n x = w n x from hy]
  have h₀ : (∫ x, B x (V x) (W₀ x) ∂μ) = ∫ x, B x (v x) (w₀ x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp, hw₀.coeFn_toLp] with x hx hy
    rw [show V x = v x from hx, show W₀ x = w₀ x from hy]
  simpa only [Function.comp_def, hn, h₀] using (hcont.tendsto W₀).comp hW

variable {d n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin n)

theorem integral_metric_energy_variation_eq_zero_of_continuous_test
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → F}
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    {A : F → F →L[ℝ] F →L[ℝ] ℝ} {U K : Set F}
    (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) (hK : IsCompact K) (hKU : K ⊆ U)
    (huK : ∀ᵐ x ∂volume.restrict Ω, u x ∈ K)
    (hEL : ∀ ψ : E → F, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x in Ω, ∑ j : Fin d,
        ((fderiv ℝ A (u x) (ψ x))
          (DeGiorgi.weakGradientColumn hu x j) (DeGiorgi.weakGradientColumn hu x j) +
        2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
          (fderiv ℝ ψ x (EuclideanSpace.single j 1)))) = 0)
    {φ : E → F} (hφ : Continuous φ) (hφs : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω)
    (hφw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => φ x i) Ω) :
    (∫ x in Ω, ∑ j : Fin d,
      ((fderiv ℝ A (u x) (φ x))
        (DeGiorgi.weakGradientColumn hu x j) (DeGiorgi.weakGradientColumn hu x j) +
      2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
        (DeGiorgi.weakGradientColumn hφw x j))) = 0 := by
  classical
  let _ : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let _ : NormedAddCommGroup (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ)) := ContinuousLinearMap.toNormedSpace
  let μ : Measure E := volume.restrict Ω
  let G (j : Fin d) (x : E) := DeGiorgi.weakGradientColumn hu x j
  let H (j : Fin d) (x : E) := DeGiorgi.weakGradientColumn hφw x j
  have hG (j : Fin d) : MemLp (G j) 2 μ := DeGiorgi.weakGrad_column_memLp hu j
  have hH (j : Fin d) : MemLp (H j) 2 μ := DeGiorgi.weakGrad_column_memLp hφw j
  have hum : MemLp u 2 μ := MemLp.of_eval_piLp fun i => (hu i).memLp
  have hAc : ContinuousOn A K := hA.continuousOn.mono hKU
  have hDAc : ContinuousOn (fderiv ℝ A) K :=
    (hA.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU
  have hAm : AEStronglyMeasurable (fun x => A (u x)) μ := by
    have hm : Measurable (K.piecewise A 0) :=
      hAc.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
    apply (hm.comp_aemeasurable hum.aemeasurable).aestronglyMeasurable.congr
    filter_upwards [huK] with x hx
    exact Set.piecewise_eq_of_mem K A 0 hx
  have hDAm : AEStronglyMeasurable (fun x => fderiv ℝ A (u x)) μ := by
    have hm : Measurable (K.piecewise (fderiv ℝ A) 0) :=
      hDAc.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
    apply (hm.comp_aemeasurable hum.aemeasurable).aestronglyMeasurable.congr
    filter_upwards [huK] with x hx
    exact Set.piecewise_eq_of_mem K (fderiv ℝ A) 0 hx
  obtain ⟨δ, hδ, C, hC, hbound⟩ := exists_compact_metric_range_bounds hU hA hK hKU 0 le_rfl
  have hbound₀ : ∀ᵐ x ∂μ, ‖A (u x)‖ ≤ C ∧ ‖fderiv ℝ A (u x)‖ ≤ C := by
    filter_upwards [huK] with x hx
    simpa only [zero_smul, add_zero] using
      (hbound (u x) hx 0 (by simp) 0 (by simpa using hδ)).2
  have hAb : ∀ᵐ x ∂μ, ‖A (u x)‖ ≤ C := hbound₀.mono fun _ hx => hx.1
  have hDAb : ∀ᵐ x ∂μ, ‖fderiv ℝ A (u x)‖ ≤ C := hbound₀.mono fun _ hx => hx.2
  obtain ⟨S, ψ, _, hSΩ, _, hψ, hψs, hψS, hunif, hder⟩ :=
    Euclidean.exists_contDiff_compactSupport_tendstoUniformly_weakGrad hΩ hφ hφs hφΩ hφw
  let D (k : ℕ) (j : Fin d) (x : E) := fderiv ℝ (ψ k) x (EuclideanSpace.single j 1)
  have hD (k : ℕ) (j : Fin d) : MemLp (D k j) 2 μ :=
    ((((hψ k).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hψs k).fderiv_apply ℝ (EuclideanSpace.single j 1))).restrict Ω
  have hsourceI {v : E → F} (hv : Continuous v) (hvs : HasCompactSupport v) (j : Fin d) :
      Integrable (fun x => (fderiv ℝ A (u x) (v x)) (G j x) (G j x)) μ := by
    obtain ⟨P, hP⟩ := hvs.exists_bound_of_continuous hv
    have hm := aestronglyMeasurable_clm_apply_variable hDAm hv.aestronglyMeasurable
    have hb : ∀ᵐ x ∂μ, ‖fderiv ℝ A (u x) (v x)‖ ≤ C * P := by
      filter_upwards [hDAb] with x hx
      exact ((fderiv ℝ A (u x)).le_opNorm (v x)).trans
        (mul_le_mul hx (hP x) (norm_nonneg _) hC)
    exact integrable_bilinear_of_apply_aestronglyMeasurable
      (fun x => fderiv ℝ A (u x) (v x))
      (fun a b => (hm.apply_continuousLinearMap a).apply_continuousLinearMap b) hb (hG j) (hG j)
  have hprincipalI {v : E → F} (hv : MemLp v 2 μ) (j : Fin d) :
      Integrable (fun x => A (u x) (G j x) (v x)) μ :=
    integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (u x))
      (fun a b => (hAm.apply_continuousLinearMap a).apply_continuousLinearMap b) hAb (hG j) hv
  obtain ⟨P₀, hP₀⟩ := hφs.exists_bound_of_continuous hφ
  let P : ℝ := max P₀ 0
  have hφb (x : E) : ‖φ x‖ ≤ P := (hP₀ x).trans (le_max_left _ _)
  have hψb : ∀ᶠ k in atTop, ∀ x, ‖ψ k x‖ ≤ P + 1 := by
    filter_upwards [Metric.tendstoUniformly_iff.mp hunif 1 zero_lt_one] with k hk
    intro x
    have hx : ‖ψ k x - φ x‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hk x
    calc
      ‖ψ k x‖ ≤ ‖ψ k x - φ x‖ + ‖φ x‖ := by
        simpa only [sub_add_cancel] using norm_add_le (ψ k x - φ x) (φ x)
      _ ≤ P + 1 := by linarith [hφb x]
  have hsourceLim (j : Fin d) : Tendsto (fun k =>
      ∫ x, (fderiv ℝ A (u x) (ψ k x)) (G j x) (G j x) ∂μ) atTop
      (𝓝 (∫ x, (fderiv ℝ A (u x) (φ x)) (G j x) (G j x) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => (C * (P + 1)) * ‖G j x‖ ^ 2)
    · exact Eventually.of_forall fun k =>
        (hsourceI (hψ k).continuous (hψs k) j).aestronglyMeasurable
    · filter_upwards [hψb] with k hk
      filter_upwards [hDAb] with x hx
      calc
        ‖(fderiv ℝ A (u x) (ψ k x)) (G j x) (G j x)‖ ≤
            ‖fderiv ℝ A (u x) (ψ k x)‖ * ‖G j x‖ * ‖G j x‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ (C * (P + 1)) * ‖G j x‖ ^ 2 := by
          have hb := ((fderiv ℝ A (u x)).le_opNorm (ψ k x)).trans
            (mul_le_mul hx (hk x) (norm_nonneg _) hC)
          calc
            _ ≤ (C * (P + 1)) * ‖G j x‖ * ‖G j x‖ := by gcongr
            _ = _ := by ring
    · exact ((hG j).norm.integrable_sq).const_mul (C * (P + 1))
    · exact Eventually.of_forall fun x =>
        (((fderiv ℝ A (u x)).continuous.clm_apply continuous_const).clm_apply
          continuous_const).tendsto (φ x) |>.comp (hunif.tendsto_at x)
  have hprincipalLim (j : Fin d) : Tendsto (fun k =>
      ∫ x, A (u x) (G j x) (D k j x) ∂μ) atTop
      (𝓝 (∫ x, A (u x) (G j x) (H j x) ∂μ)) :=
    tendsto_integral_bilinear_of_tendsto_eLpNorm (fun x => A (u x)) hAm hAb
      (hG j) (fun k => hD k j) (hH j) (hder j)
  let J (k : ℕ) := ∫ x, ∑ j : Fin d,
    ((fderiv ℝ A (u x) (ψ k x)) (G j x) (G j x) +
      2 * A (u x) (G j x) (D k j x)) ∂μ
  let J₀ := ∫ x, ∑ j : Fin d,
    ((fderiv ℝ A (u x) (φ x)) (G j x) (G j x) +
      2 * A (u x) (G j x) (H j x)) ∂μ
  have hJn (k : ℕ) : J k = ∑ j : Fin d,
      ((∫ x, (fderiv ℝ A (u x) (ψ k x)) (G j x) (G j x) ∂μ) +
        2 * ∫ x, A (u x) (G j x) (D k j x) ∂μ) := by
    dsimp only [J]
    have hi (j : Fin d) : Integrable (fun x =>
        (fderiv ℝ A (u x) (ψ k x)) (G j x) (G j x) +
          2 * A (u x) (G j x) (D k j x)) μ :=
      (hsourceI (hψ k).continuous (hψs k) j).add ((hprincipalI (hD k j) j).const_mul 2)
    rw [integral_finsetSum _ (fun j _ => hi j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_add (hsourceI (hψ k).continuous (hψs k) j)
      ((hprincipalI (hD k j) j).const_mul 2), integral_const_mul]
  have hJ₀ : J₀ = ∑ j : Fin d,
      ((∫ x, (fderiv ℝ A (u x) (φ x)) (G j x) (G j x) ∂μ) +
        2 * ∫ x, A (u x) (G j x) (H j x) ∂μ) := by
    dsimp only [J₀]
    have hi (j : Fin d) : Integrable (fun x =>
        (fderiv ℝ A (u x) (φ x)) (G j x) (G j x) +
          2 * A (u x) (G j x) (H j x)) μ :=
      (hsourceI hφ hφs j).add ((hprincipalI (hH j) j).const_mul 2)
    rw [integral_finsetSum _ (fun j _ => hi j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_add (hsourceI hφ hφs j) ((hprincipalI (hH j) j).const_mul 2), integral_const_mul]
  have hlim : Tendsto J atTop (𝓝 J₀) := by
    have heq : J = fun k => ∑ j : Fin d,
        ((∫ x, (fderiv ℝ A (u x) (ψ k x)) (G j x) (G j x) ∂μ) +
          2 * ∫ x, A (u x) (G j x) (D k j x) ∂μ) := funext hJn
    rw [heq, hJ₀]
    exact tendsto_finsetSum Finset.univ fun j _ =>
      (hsourceLim j).add ((hprincipalLim j).const_mul 2)
  have hzero (k : ℕ) : J k = 0 := hEL (ψ k) (hψ k) (hψs k) ((hψS k).trans hSΩ)
  have hz : Tendsto J atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr (fun k => (hzero k).symm)
  exact tendsto_nhds_unique hlim hz

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

private theorem metric_inverse_column_derivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : F → F →L[ℝ] F →L[ℝ] ℝ} {L : F → F} {U : Set F}
    (hU : IsOpen U) {y : F} (hy : y ∈ U)
    (hB : DifferentiableAt ℝ B y) (hL : DifferentiableAt ℝ L y)
    (ℓ : F →L[ℝ] ℝ) (hpair : ∀ x ∈ U, ∀ v, B x v (L x) = ℓ v) (v h : F) :
    (fderiv ℝ B y h) v (L y) + B y v (fderiv ℝ L y h) = 0 := by
  have hd := ((hB.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) v y)).clm_apply
    hL.hasFDerivAt).fderiv
  have heq : (fun x => B x v (L x)) =ᶠ[𝓝 y] (fun _ => ℓ v) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    exact hpair x hx v
  have hzero : fderiv ℝ (fun x => B x v (L x)) y = 0 := by
    rw [heq.fderiv_eq]
    exact fderiv_const_apply (ℓ v)
  have he := congrArg (fun D : F →L[ℝ] ℝ => D h) hzero
  rw [hd] at he
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, zero_add, add_zero,
    map_zero, add_comm] using he

end DifferentialGeometry.Analysis.Sobolev

namespace DifferentialGeometry.Analysis.Sobolev

variable {d n : ℕ}
local notation "P" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin n)

theorem integral_weakGradientColumn_test_deriv_eq_metric_connection
    {Ω : Set P} (hΩ : IsOpen Ω) {z : P → F} (hzc : ContinuousOn z Ω)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) Ω)
    {B : F → F →L[ℝ] F →L[ℝ] ℝ} {U K : Set F}
    (hU : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hzK : ∀ᵐ x ∂volume.restrict Ω, z x ∈ K)
    (hEL : ∀ ψ : P → F, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x in Ω, ∑ j : Fin d,
        ((fderiv ℝ B (z x) (ψ x))
          (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j) +
        2 * B (z x) (DeGiorgi.weakGradientColumn hz x j)
          (fderiv ℝ ψ x (EuclideanSpace.single j 1)))) = 0)
    (L : F → F) (hL : ContDiff ℝ 1 L) {C : ℝ} (hC : ∀ y, ‖fderiv ℝ L y‖ ≤ C)
    (ℓ : F →L[ℝ] ℝ) (hpair : ∀ y ∈ U, ∀ v, B y v (L y) = ℓ v)
    {x₀ : P} {ρ : ℝ} (hball : Metric.closedBall x₀ ρ ⊆ Ω)
    {ζ : P → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζball : tsupport ζ ⊆ Metric.ball x₀ ρ) :
    (∫ x in Metric.ball x₀ ρ, ∑ j : Fin d,
      (2 * (fderiv ℝ ζ x (EuclideanSpace.single j 1)) *
          ℓ (DeGiorgi.weakGradientColumn hz x j) -
        ζ x * (2 * (fderiv ℝ B (z x) (DeGiorgi.weakGradientColumn hz x j))
            (DeGiorgi.weakGradientColumn hz x j) (L (z x)) -
          (fderiv ℝ B (z x) (L (z x)))
            (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j)))) = 0 := by
  classical
  let S := Metric.ball x₀ ρ
  have hSΩ : S ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  let hzs (i : Fin n) := DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hSΩ (hz i)
  have hzKs : ∀ᵐ x ∂volume.restrict S, z x ∈ K :=
    ae_mono (Measure.restrict_mono_set volume hSΩ) hzK
  have hELs : ∀ ψ : P → F, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
      (∫ x in S, ∑ j : Fin d,
        ((fderiv ℝ B (z x) (ψ x))
          (DeGiorgi.weakGradientColumn hzs x j) (DeGiorgi.weakGradientColumn hzs x j) +
        2 * B (z x) (DeGiorgi.weakGradientColumn hzs x j)
          (fderiv ℝ ψ x (EuclideanSpace.single j 1)))) = 0 := by
    intro ψ hψ hψc hψS
    have h := hEL ψ hψ hψc (hψS.trans hSΩ)
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hSΩ] at h
    · exact h
    · intro x hx
      have hxψ : x ∉ tsupport ψ := fun hx' => hx.2 (hψS hx')
      rw [image_eq_zero_of_notMem_tsupport hxψ, fderiv_of_notMem_tsupport ℝ hxψ]
      simp
  obtain ⟨hφc, hφs, hφsupp, hφ, hφgrad⟩ :=
    Euclidean.exists_memW1pWitnesses_smul_comp_contDiff_on_ball hΩ hzc hz L hL hC hball hζ hζball
  have hzero := integral_metric_energy_variation_eq_zero_of_continuous_test
    Metric.isOpen_ball hzs hU hB hK hKU hzKs hELs hφc hφs (hφsupp.trans hζball) hφ
  rw [← hzero]
  apply integral_congr_ae
  filter_upwards [hzKs] with x hx
  apply Finset.sum_congr rfl
  intro j _
  have hφg : DeGiorgi.weakGradientColumn hφ x j =
      ζ x • fderiv ℝ L (z x) (DeGiorgi.weakGradientColumn hz x j) +
        (fderiv ℝ ζ x (EuclideanSpace.single j 1)) • L (z x) := hφgrad x j
  rw [hφg]
  have hD := metric_inverse_column_derivative hU (hKU hx)
    ((hB.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt one_ne_zero)
    (hL.differentiable one_ne_zero (z x)) ℓ hpair
    (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j)
  change (2 * _ * _ - ζ x * (2 * _ - _)) =
    (fderiv ℝ B (z x) (ζ x • L (z x)))
      (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j) +
      2 * B (z x) (DeGiorgi.weakGradientColumn hz x j)
        (ζ x • fderiv ℝ L (z x) (DeGiorgi.weakGradientColumn hz x j) +
          (fderiv ℝ ζ x (EuclideanSpace.single j 1)) • L (z x))
  rw [map_smul, smul_apply, smul_apply,
    map_add, map_smul, map_smul, hpair _ (hKU hx)]
  simp only [smul_eq_mul]
  have hDz := congrArg (fun q : ℝ => ζ x * q) hD
  nlinarith [hDz]

end DifferentialGeometry.Analysis.Sobolev

end
