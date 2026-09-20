import DifferentialGeometry.Analysis.Calculus.Taylor
import DifferentialGeometry.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Viscosity

private theorem exists_smooth_upper_test_near_differentiable_point_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : UpperSemicontinuousOn u Ω)
    {x : E} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ Metric.ball x r ∩ Ω, ∃ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      IsLocalMax (fun z => u z - φ z) y ∧ ‖fderiv ℝ φ y - fderiv ℝ u x‖ < r := by
  let ε := r / 8
  have hε : 0 < ε := div_pos hr (by norm_num)
  have he := hd.hasFDerivAt.isLittleO.def hε
  have hn : ∀ᶠ y in 𝓝 x, y ∈ Ω ∧ y ∈ Metric.ball x r ∧
      ‖u y - u x - fderiv ℝ u x (y - x)‖ ≤ ε * ‖y - x‖ := by
    filter_upwards [hΩ.mem_nhds hx, Metric.ball_mem_nhds x hr, he] with y hyΩ hyr hye
    exact ⟨hyΩ, hyr, hye⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  let D := fderiv ℝ u x
  let c := 2 * ε / δ
  have hc : 0 ≤ c := by positivity
  let φ : E → ℝ := fun y => u x + D (y - x) + c * ‖y - x‖ ^ 2
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (contDiff_const.add (D.contDiff.comp (contDiff_id.sub contDiff_const))).add
      (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))
  have hφx : u x - φ x = 0 := by simp [φ]
  have hKc : UpperSemicontinuousOn (fun y => u y - φ y) (Metric.closedBall x δ) := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      (hu.mono (fun y hy => (hδsub hy).1)).add
        hφ.continuous.neg.continuousOn.upperSemicontinuousOn
  obtain ⟨y, hy, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    ⟨x, Metric.mem_closedBall_self hδ.le⟩ (isCompact_closedBall x δ) hKc
  have hnonneg : 0 ≤ u y - φ y := by
    simpa only [Set.mem_ofPred_eq, hφx] using hmax (Metric.mem_closedBall_self hδ.le)
  have hyδ : ‖y - x‖ ≤ δ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
  have hyball : y ∈ Metric.ball x δ := by
    by_contra hnot
    have hnorm : ‖y - x‖ = δ := le_antisymm hyδ (by
      simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hnot)
    have hrem : u y - u x - D (y - x) ≤ ε * δ :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, hnorm] using (hδsub hy).2.2)
    have hquad : c * δ ^ 2 = 2 * ε * δ := by dsimp [c]; field_simp
    have heq : u y - φ y = (u y - u x - D (y - x)) - c * δ ^ 2 := by
      dsimp only [φ]
      rw [hnorm]
      ring
    rw [heq, hquad] at hnonneg
    nlinarith
  refine ⟨y, ⟨(hδsub hy).2.1, (hδsub hy).1⟩, φ, hφ, ?_, ?_⟩
  · filter_upwards [Metric.closedBall_mem_nhds_of_mem hyball] with z hz
    exact hmax hz
  · have hshift := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
    have hlinear : HasFDerivAt (fun z => u x + D (z - x)) D y := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_apply, id_eq] using (D.hasFDerivAt.comp y hshift).const_add (u x)
    have hquad : HasFDerivAt (fun z => c * ‖z - x‖ ^ 2)
        (c • ((2 : ℝ) • innerSL ℝ (y - x))) y := by
      simpa only [Function.comp_apply, ContinuousLinearMap.comp_id, id_eq, two_smul ℝ, two_nsmul] using
        (((hasStrictFDerivAt_norm_sq (y - x)).hasFDerivAt.comp y hshift).const_mul c)
    have hφD : HasFDerivAt φ (D + c • ((2 : ℝ) • innerSL ℝ (y - x))) y := hlinear.fun_add hquad
    change ‖fderiv ℝ φ y - D‖ < r
    rw [hφD.fderiv, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hc, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      innerSL_apply_norm]
    calc
      c * (2 * ‖y - x‖) ≤ c * (2 * δ) := by gcongr
      _ = 4 * ε := by dsimp [c]; field_simp; norm_num
      _ < r := by dsimp [ε]; linarith

theorem exists_smooth_upper_test_near_differentiable_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : UpperSemicontinuousOn u Ω)
    {x : E} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ Metric.ball x r ∩ Ω, ∃ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      IsLocalMax (fun z => u z - φ z) y ∧ ‖fderiv ℝ φ y - fderiv ℝ u x‖ < r := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFunL.trans
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))).symm
  let v := u ∘ e.symm
  let A := ‖e.toContinuousLinearMap‖ + ‖e.symm.toContinuousLinearMap‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : ‖e.toContinuousLinearMap‖ < A := by dsimp [A]; linarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hA2 : ‖e.symm.toContinuousLinearMap‖ < A := by dsimp [A]; linarith [norm_nonneg e.toContinuousLinearMap]
  have hΩ' : IsOpen (e.symm ⁻¹' Ω) := hΩ.preimage e.symm.continuous
  have hv : UpperSemicontinuousOn v (e.symm ⁻¹' Ω) :=
    hu.comp e.symm.continuous.continuousOn (mapsTo_preimage _ _)
  have hdv : HasFDerivAt v ((fderiv ℝ u x).comp e.symm.toContinuousLinearMap) (e x) := by
    have hd' : HasFDerivAt u (fderiv ℝ u x) (e.symm (e x)) := by
      simpa only [e.symm_apply_apply] using hd.hasFDerivAt
    exact hd'.comp (e x) e.symm.hasFDerivAt
  obtain ⟨y, hy, ψ, hψ, hm, hp⟩ :=
    exists_smooth_upper_test_near_differentiable_point_inner hΩ' hv
      (by simpa only [mem_preimage, e.symm_apply_apply] using hx)
      hdv.differentiableAt (div_pos hr hA)
  have hy' : ‖y - e x‖ < r / A := by simpa only [Metric.mem_ball, dist_eq_norm] using hy.1
  have hdist : e.symm y ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖e.symm y - x‖ = ‖e.symm (y - e x)‖ := by rw [map_sub, e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖y - e x‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * (r / A) := by gcongr
      _ < A * (r / A) := mul_lt_mul_of_pos_right hA2 (div_pos hr hA)
      _ = r := by field_simp
  refine ⟨e.symm y, ⟨hdist, hy.2⟩, ψ ∘ e, hψ.comp e.contDiff, ?_, ?_⟩
  · have hm' : IsLocalMax (fun z => v z - ψ z) (e (e.symm y)) := by
      simpa only [e.apply_symm_apply] using hm
    simpa only [Function.comp_def, v, e.symm_apply_apply] using
      hm'.comp_continuous e.continuous.continuousAt
  · have hD : fderiv ℝ u x = (fderiv ℝ v (e x)).comp e.toContinuousLinearMap := by
      have h := (hdv.comp x e.hasFDerivAt).fderiv
      rw [← hdv.fderiv] at h
      simpa only [v, Function.comp_def, e.symm_apply_apply] using h
    have hψD : fderiv ℝ (ψ ∘ e) (e.symm y) =
        (fderiv ℝ ψ y).comp e.toContinuousLinearMap := by
      simpa only [e.apply_symm_apply] using
        ((hψ.differentiable (by simp) (e (e.symm y))).hasFDerivAt.comp
          (e.symm y) e.hasFDerivAt).fderiv
    rw [hψD, hD, ← ContinuousLinearMap.sub_comp]
    calc
      ‖(fderiv ℝ ψ y - fderiv ℝ v (e x)).comp e.toContinuousLinearMap‖ ≤
          ‖fderiv ℝ ψ y - fderiv ℝ v (e x)‖ * ‖e.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (r / A) * ‖e.toContinuousLinearMap‖ := by gcongr
      _ < (r / A) * A := mul_lt_mul_of_pos_left hA1 (div_pos hr hA)
      _ = r := by field_simp

theorem exists_smooth_lower_test_near_differentiable_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : LowerSemicontinuousOn u Ω)
    {x : E} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ Metric.ball x r ∩ Ω, ∃ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      IsLocalMin (fun z => u z - φ z) y ∧ ‖fderiv ℝ φ y - fderiv ℝ u x‖ < r := by
  have hu' : UpperSemicontinuousOn (-u) Ω := by
    intro z hz a ha
    filter_upwards [hu z hz (-a) (by dsimp at ha; linarith)] with w hw
    change -u w < a
    linarith
  obtain ⟨y, hy, φ, hφ, hm, hp⟩ :=
    exists_smooth_upper_test_near_differentiable_point hΩ hu' hx hd.neg hr
  refine ⟨y, hy, -φ, hφ.neg, ?_, ?_⟩
  · filter_upwards [hm] with z hz
    dsimp only [Pi.neg_apply] at *
    linarith
  · rw [fderiv_neg]
    rw [fderiv_neg, sub_neg_eq_add] at hp
    have heq : -fderiv ℝ φ y - fderiv ℝ u x = -(fderiv ℝ φ y + fderiv ℝ u x) := by abel
    simpa only [heq, norm_neg] using hp

theorem second_order_le_zero_of_upper_tests_of_isLittleO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} {x : E}
    {p : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B.flip = B)
    (htaylor : (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x))
      =o[𝓝 x] (fun y => ‖y - x‖ ^ 2))
    {H : (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ}
    (hsub : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMax (fun z => u z - φ z) x → H (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0)
    (hH : LowerSemicontinuousAt (fun z : (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) => H z.1 z.2)
      (p, B)) :
    H p B ≤ 0 := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFunL.trans
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))).symm
  let Q : E →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.precomp ℝ e.toContinuousLinearMap).comp
      ((innerSL ℝ).comp e.toContinuousLinearMap)
  have hQ : Q.flip = Q := by
    ext v w
    change inner ℝ (e w) (e v) = inner ℝ (e v) (e w)
    exact real_inner_comm (e v) (e w)
  have hQdiag (v : E) : Q v v = ‖e v‖ ^ 2 := by
    change inner ℝ (e v) (e v) = ‖e v‖ ^ 2
    exact real_inner_self_eq_norm_sq _
  let C := (‖e.symm.toContinuousLinearMap‖ + 1) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (v : E) : ‖v‖ ^ 2 ≤ C * Q v v := by
    rw [hQdiag]
    have hn : ‖v‖ ≤ (‖e.symm.toContinuousLinearMap‖ + 1) * ‖e v‖ := by
      calc
        ‖v‖ = ‖e.symm (e v)‖ := by rw [e.symm_apply_apply]
        _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e v‖ := e.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ (‖e.symm.toContinuousLinearMap‖ + 1) * ‖e v‖ := by gcongr; linarith
    have hs := pow_le_pow_left₀ (norm_nonneg v) hn 2
    simpa only [mul_pow, C] using hs
  have htest (ε : ℝ) (hε : 0 < ε) : H p (B + (2 * ε) • Q) ≤ 0 := by
    let φ := fun y => u x + p (y - x) + (1 / 2 : ℝ) * (B + (2 * ε) • Q) (y - x) (y - x)
    have hsym : (B + (2 * ε) • Q).flip = B + (2 * ε) • Q := by
      ext v w
      simp only [ContinuousLinearMap.flip_apply, add_apply, smul_apply, smul_eq_mul]
      rw [show B w v = B v w from congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) hB,
        show Q w v = Q v w from congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) hQ]
    obtain ⟨hφ, hφx, hφd⟩ := DifferentialGeometry.Analysis.second_order_polynomial_derivatives
      x (u x) p (B + (2 * ε) • Q) hsym
    simp only [smul_eq_mul] at hφ hφx hφd
    have hφD := (hφd x).1
    have hφDD := (hφd x).2
    simp only [sub_self, map_zero, add_zero] at hφD
    change ContDiff ℝ (⊤ : ℕ∞) φ at hφ
    change φ x = u x at hφx
    change fderiv ℝ φ x = p at hφD
    change fderiv ℝ (fderiv ℝ φ) x = B + (2 * ε) • Q at hφDD
    have hm : IsLocalMax (fun z => u z - φ z) x := by
      have he := htaylor.def (div_pos hε hC)
      filter_upwards [he] with y hy
      change u y - φ y ≤ u x - φ x
      rw [hφx, sub_self]
      have hrem : u y - u x - p (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x) ≤
          (ε / C) * ‖y - x‖ ^ 2 := by
        apply (le_abs_self _).trans
        simpa only [Real.norm_eq_abs, norm_pow, norm_norm, abs_norm] using hy
      have hquad : (ε / C) * ‖y - x‖ ^ 2 ≤ ε * Q (y - x) (y - x) := by
        calc
          (ε / C) * ‖y - x‖ ^ 2 ≤ (ε / C) * (C * Q (y - x) (y - x)) :=
            mul_le_mul_of_nonneg_left (hbound _) (div_pos hε hC).le
          _ = ε * Q (y - x) (y - x) := by field_simp
      simp only [φ, add_apply, smul_apply, smul_eq_mul]
      linarith
    simpa only [hφD, hφDD] using hsub φ hφ hm
  by_contra hn
  have hp : 0 < H p B := lt_of_not_ge hn
  have hJ : ContinuousAt (fun ε : ℝ => (p, B + (2 * ε) • Q)) 0 := by fun_prop
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0, 0 < H p (B + (2 * ε) • Q) := by
    have hh : ∀ᶠ z in 𝓝 (p, B), 0 < H z.1 z.2 := hH 0 hp
    have hJ' : Filter.Tendsto (fun ε : ℝ => (p, B + (2 * ε) • Q)) (𝓝 0) (𝓝 (p, B)) := by
      simpa only [ContinuousAt, mul_zero, zero_smul, add_zero] using hJ
    exact hJ' hh
  obtain ⟨ε, hε, hpos⟩ := ((show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin).and
    (nhdsWithin_le_nhds hnear)).exists
  exact (not_lt_of_ge (htest ε hε)) hpos

theorem second_order_le_zero_of_upper_tests_of_differentiableAt_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} {x : E}
    (hu : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y)
    (hdu : DifferentiableAt ℝ (fderiv ℝ u) x)
    {H : (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ}
    (hsub : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMax (fun z => u z - φ z) x → H (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0)
    (hH : LowerSemicontinuousAt (fun z : (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) => H z.1 z.2)
      (fderiv ℝ u x, fderiv ℝ (fderiv ℝ u) x)) :
    H (fderiv ℝ u x) (fderiv ℝ (fderiv ℝ u) x) ≤ 0 := by
  have hu' : ∀ᶠ y in 𝓝 x, HasFDerivAt u (fderiv ℝ u y) y := hu.mono (fun _ h => h.hasFDerivAt)
  have hB : (fderiv ℝ (fderiv ℝ u) x).flip = fderiv ℝ (fderiv ℝ u) x := by
    ext v w
    exact (second_derivative_symmetric_of_eventually_of_real hu' hdu.hasFDerivAt v w).symm
  apply second_order_le_zero_of_upper_tests_of_isLittleO hB ?_ hsub hH
  simpa only [smul_eq_mul] using
    DifferentialGeometry.Analysis.second_order_taylor_isLittleO hu' hdu.hasFDerivAt

theorem ae_second_order_le_zero_of_upper_tests_of_locallyLipschitzOn_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E} [μ.IsAddHaarMeasure]
    {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : DifferentiableOn ℝ u Ω)
    (hdu : LocallyLipschitzOn Ω (fderiv ℝ u))
    {H : E → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ}
    (hsub : ∀ x ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMax (fun z => u z - φ z) x → H x (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0)
    (hH : ∀ x ∈ Ω, LowerSemicontinuous
      (fun z : (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) => H x z.1 z.2)) :
    ∀ᵐ x ∂μ.restrict Ω, H x (fderiv ℝ u x) (fderiv ℝ (fderiv ℝ u) x) ≤ 0 := by
  filter_upwards [hdu.ae_differentiableAt hΩ, MeasureTheory.ae_restrict_mem hΩ.measurableSet]
    with x hx hxΩ
  apply second_order_le_zero_of_upper_tests_of_differentiableAt_fderiv ?_ hx (hsub x hxΩ)
    (hH x hxΩ _)
  filter_upwards [hΩ.mem_nhds hxΩ] with y hy
  exact (hu y hy).differentiableAt (hΩ.mem_nhds hy)

end DifferentialGeometry.Analysis.Viscosity
