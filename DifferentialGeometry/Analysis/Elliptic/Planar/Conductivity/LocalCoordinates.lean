import DifferentialGeometry.Analysis.Elliptic.Euclidean.ScalarOperator.Bernstein
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Dirichlet.SmoothSolution
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Barrier.AffineDirichlet
import DifferentialGeometry.Analysis.Elliptic.Euclidean.ScalarOperator.CoefficientBounds
import DifferentialGeometry.Analysis.Elliptic.Euclidean.DivergenceOperator
import DifferentialGeometry.Analysis.Elliptic.Coefficients.Extension
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.LocalDiffeomorphism
import DifferentialGeometry.Analysis.Elliptic.Planar.StreamFunction
import DifferentialGeometry.Analysis.Complex.Beltrami.AnalyticCoordinates
import DifferentialGeometry.Analysis.Calculus.Inverse.Univalent

section

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "e" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)

theorem exists_smooth_conductivity_harmonic_function_fderiv_ne_zero
    (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hpos : ∀ x, (B.a x).PosDef) :
    ∃ R : ℝ, 0 < R ∧ ∃ v : V → ℝ, ContDiffOn ℝ ∞ v (Metric.ball (0 : V) R) ∧
      DeGiorgi.HasWeakDiv 0 (fun x => DeGiorgi.matMulE (B.a x)
        (DeGiorgi.smoothGradField v x)) (Metric.ball (0 : V) R) ∧
      DeGiorgi.smoothGradField v 0 ≠ 0 := by
  let b : V → Fin 2 → ℝ := fun x j => ∑ i,
    fderiv ℝ (fun y => B.a y i j) x (e i)
  obtain ⟨hb, C, hC, hbounds⟩ := exists_smooth_elliptic_coefficient_drift_bounds_on_compact
    B (isCompact_closedBall (0 : V) 1)
  change (∀ j, ContDiff ℝ ∞ (fun x => b x j)) at hb
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  let lam := B.lam
  let K := ((16 * C ^ 2 / lam + 4 * C + 1) + 8 * C + 8 * C +
    1024 * C ^ 2 / lam + 1) / (2 * lam)
  have hlam : 0 < lam := B.ellipticity_pos
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨k, Cb, hk, hCb, hbar⟩ := DeGiorgi.exists_affine_dirichlet_barrier_bound_on_subballs
    (by norm_num : 2 ≤ 2) B 1 (0 : Fin 2)
  let M₀ := 4 * Cb * k * Real.exp k
  let H := K * M₀ ^ 2 + 2 * K * M₀ * C + (2 * C) ^ 2
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let R := min (1 / 4) (1 / (4 * (H + 1)))
  have hR : 0 < R := lt_min (by norm_num) (by positivity)
  have hRquarter : R ≤ 1 / 4 := min_le_left _ _
  have hsmall : H * R ^ 2 < 1 / 4 := by
    have hden : 0 < 4 * (H + 1) := by positivity
    have hprod : R * (4 * (H + 1)) ≤ 1 :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith [mul_nonneg hH hR.le]
  obtain ⟨A, u, v, hAB, hlamEq, hu, hzero, hv, huv, hdiv, hdivClassical⟩ :=
    DeGiorgi.exists_smooth_dirichlet_solution_of_posDef (by norm_num : 2 ≤ 2) B hpos
      (0 : V) (2 * R) (e 0) 0
  have hz : DeGiorgi.MemH01 (fun x => u x - x 0) (Metric.ball (0 : V) (2 * R)) := by
    simpa [PiLp.inner_apply, PiLp.single_apply] using hzero
  have hbar' := hbar (2 * R) (by positivity) (by linarith) A u v
    (DeGiorgi.isHomogeneousWeakSolution_isSolution hu) (fun x _ => congrFun hAB x)
    hz hv.continuousOn huv
  let w : V → ℝ := fun x => v x - x 0
  have hw : ContDiffOn ℝ ∞ w (Metric.ball (0 : V) (2 * R)) :=
    hv.sub ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))).contDiffOn)
  have hball : Metric.closedBall (0 : V) R ⊆ Metric.ball 0 (2 * R) :=
    Metric.closedBall_subset_ball (by linarith)
  have hOne : Metric.closedBall (0 : V) R ⊆ Metric.closedBall 0 1 :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hum : ∀ x ∈ Metric.closedBall (0 : V) R, |w x| ≤ M₀ * R ^ 2 := by
    intro x hx
    have h := (hbar' x (hball hx)).1.trans (hbar' x (hball hx)).2
    change |v x - x 0| ≤ _
    calc
      _ ≤ Cb * k * Real.exp (k * 1 ^ 2) * (2 * R) ^ 2 := h
      _ = _ := by dsimp only [M₀]; norm_num; ring
  have hLv (x : V) (hx : x ∈ Metric.ball (0 : V) (2 * R)) :
      scalarEllipticOperator B.a b v x = 0 := by
    rw [← divergence_matMulE_smoothGradField_eq_scalarEllipticOperator B.a
      (fun i j => (B.smooth_a i j).differentiable (by simp) x)
      ((hv.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).of_le (by decide))]
    exact hdivClassical x hx
  have hLw (x : V) (hx : x ∈ Metric.ball (0 : V) (2 * R)) :
      scalarEllipticOperator B.a b w x = -b x 0 := by
    have hv2 := (hv.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).of_le
      (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by decide)
    have hi2 : ContDiffAt ℝ 2 (fun y : V => y 0) x := contDiffAt_piLp_apply 2
    have he : scalarEllipticOperator B.a b (fun y : V => y 0) x = b x 0 := by
      have hdi : fderiv ℝ (fun y : V => y 0) = fun _ => (EuclideanSpace.proj 0 : V →L[ℝ] ℝ) := by
        funext y
        exact (EuclideanSpace.proj 0 : V →L[ℝ] ℝ).fderiv
      simp only [scalarEllipticOperator, hdi]
      simp
    have hweq : w = fun y => v y + (-1 : ℝ) * y 0 := by funext y; dsimp only [w]; ring
    rw [hweq]
    rw [scalarEllipticOperator_add B.a b hv2 (contDiffAt_const.mul hi2),
      scalarEllipticOperator_const_mul B.a b hi2, hLv x hx, he]
    ring
  have hforce (x : V) (hx : x ∈ Metric.ball (0 : V) R) :
      ∑ j, (fderiv ℝ (scalarEllipticOperator B.a b w) x (e j)) ^ 2 ≤ (2 * C) ^ 2 := by
    have hxe := hball (Metric.ball_subset_closedBall hx)
    have heq : scalarEllipticOperator B.a b w =ᶠ[𝓝 x] fun y => -b y 0 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxe] with y hy
      exact hLw y hy
    rw [heq.fderiv_eq]
    simp only [fderiv_fun_neg, neg_apply, neg_sq]
    have hb0 := (hb 0).differentiable (by simp) x
    have hdata := hbounds x (hOne (Metric.ball_subset_closedBall hx))
    have h0 := (sq_le_sq₀ (abs_nonneg _) hC0).mpr (hdata.2.2.2 0 0)
    have h1 := (sq_le_sq₀ (abs_nonneg _) hC0).mpr (hdata.2.2.2 1 0)
    simp only [Fin.sum_univ_two]
    simp only [sq_abs] at h0 h1
    nlinarith
  have hcoer (x : V) (hx : x ∈ Metric.ball (0 : V) R) (ξ : Fin 2 → ℝ) :
      lam * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, B.a x i j * ξ i * ξ j := by
    have h := B.coercive x (mem_univ _) (WithLp.toLp 2 ξ)
    simp only [lam, EuclideanSpace.norm_sq_eq, PiLp.inner_apply, DeGiorgi.matMulE_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, RCLike.inner_apply,
      conj_trivial, Real.norm_eq_abs, sq_abs] at h ⊢
    nlinarith only [h]
  have hbound := sum_sq_fderiv_le_of_scalar_elliptic_bounds B.a b Metric.isOpen_ball
    (hw.of_le (by decide))
    hR (show R ≤ 1 by linarith) hlam hC0 hC0 hC0 (mul_nonneg hM₀ (sq_nonneg R)) hC0 hball
    (fun x _ => hpos x) (fun x _ i j => (B.smooth_a i j).differentiable (by simp) x)
    (fun x _ j => (hb j).differentiable (by simp) x) hcoer
    (fun x hx => (hbounds x (hOne (Metric.ball_subset_closedBall hx))).1)
    (fun x hx => (hbounds x (hOne (Metric.ball_subset_closedBall hx))).2.1)
    (fun x hx => (hbounds x (hOne (Metric.ball_subset_closedBall hx))).2.2.2)
    (fun x hx => (hbounds x (hOne (Metric.ball_subset_closedBall hx))).2.2.1)
    hforce hum (fun x hx => by
      rw [hLw x (hball (Metric.ball_subset_closedBall hx)), abs_neg]
      exact (hbounds x (hOne (Metric.ball_subset_closedBall hx))).2.2.1 0)
  have hgradBound : (∑ j, (fderiv ℝ w 0 (e j)) ^ 2) < 1 / 4 := by
    have he : K * (M₀ * R ^ 2) ^ 2 / R ^ 2 +
        2 * K * (M₀ * R ^ 2) * C + R ^ 2 * (2 * C) ^ 2 = H * R ^ 2 := by
      dsimp only [H]
      field_simp [hR.ne']
    change (∑ j, (fderiv ℝ w 0 (e j)) ^ 2) ≤ _ at hbound
    have hbound' : (∑ j, (fderiv ℝ w 0 (e j)) ^ 2) ≤
        K * (M₀ * R ^ 2) ^ 2 / R ^ 2 + 2 * K * (M₀ * R ^ 2) * C + R ^ 2 * (2 * C) ^ 2 := by
      simpa only [one_pow, mul_one, K, lam] using hbound
    rw [he] at hbound'
    exact hbound'.trans_lt hsmall
  refine ⟨2 * R, by positivity, v, hv, hdiv, ?_⟩
  intro hvzero
  have hd0 : fderiv ℝ v 0 (e 0) = 0 := by
    have h := congrArg (fun z : V => z 0) hvzero
    exact h
  have hw0 : fderiv ℝ w 0 (e 0) = -1 := by
    rw [show w = fun y => v y - (EuclideanSpace.proj 0 : V →L[ℝ] ℝ) y from rfl,
      fderiv_fun_sub ((hv.contDiffAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by positivity)))).differentiableAt
          (by simp))
        (EuclideanSpace.proj 0).differentiableAt]
    simp only [sub_apply, hd0, zero_sub]
    congr 1
    rw [(EuclideanSpace.proj 0 : V →L[ℝ] ℝ).fderiv]
    simp
  have hsingle := Finset.single_le_sum
    (f := fun j : Fin 2 => (fderiv ℝ w 0 (e j)) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ (0 : Fin 2))
  rw [hw0] at hsingle
  nlinarith

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

private theorem exists_local_beltrami_coordinate_at_zero
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hzero : (0 : ℂ) ∈ Ω)
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) Ω)
    (hpos : ∀ z ∈ Ω, (A z).PosDef) (hdet : ∀ z ∈ Ω, (A z).det = 1) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, 0 ∈ e.source ∧ e.source ⊆ Ω ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      0 < (fderiv ℝ e 0).toLinearMap.det ∧
      ∀ z ∈ e.source, complexAntilinearPart (fderiv ℝ e z) =
        beltramiCoefficient (A z 1 1) (A z 0 0) (-A z 0 1) *
          complexLinearPart (fderiv ℝ e z) := by
  let L := Complex.orthonormalBasisOneI.repr
  let U := L.symm ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage L.symm.continuous
  have h0U : (0 : V) ∈ U := by simpa [U] using hzero
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hU 0 h0U
  have hsmall : Metric.closedBall (0 : V) (ρ / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρsub
  obtain ⟨B, hB, hBp, hBc⟩ := exists_smoothEllipticBilinearForm_extension hU
    (isCompact_closedBall (0 : V) (ρ / 2)) hsmall (fun x => A (L.symm x))
    (fun i j => (hA i j).comp L.symm.contDiff.contDiffOn (fun x hx => hx))
    (fun x hx => hpos (L.symm x) hx)
  obtain ⟨R, hR, v, hv, hdiv, hgrad⟩ :=
    exists_smooth_conductivity_harmonic_function_fderiv_ne_zero B hBp
  let r := min R (ρ / 2)
  have hr : 0 < r := lt_min hR (half_pos hρ)
  have hrR : r ≤ R := min_le_left _ _
  have hrρ : r ≤ ρ / 2 := min_le_right _ _
  let D := Metric.ball (0 : V) r
  have hDR : D ⊆ Metric.ball (0 : V) R := Metric.ball_subset_ball hrR
  have hDU : D ⊆ U := (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall hrρ)).trans hsmall
  have hBsame (x : V) (hx : x ∈ D) : B.a x = A (L.symm x) :=
    hB x (Metric.closedBall_subset_closedBall hrρ (Metric.ball_subset_closedBall hx))
  have hflux : ContDiffOn ℝ ∞ (fun x => DeGiorgi.matMulE (B.a x)
      (DeGiorgi.smoothGradField v x)) (Metric.ball (0 : V) R) := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    change ContDiffOn ℝ ∞ (fun x => ∑ j, B.a x i j *
      fderiv ℝ v x (EuclideanSpace.single j 1)) (Metric.ball (0 : V) R)
    apply ContDiffOn.sum
    intro j _
    exact (B.smooth_a i j).contDiffOn.mul
      ((hv.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const)
  obtain ⟨s, hs, hds⟩ := exists_stream_function_of_hasWeakDiv_zero
    Metric.isOpen_ball (convex_ball (0 : V) R) hflux hdiv
  have hvD := hv.mono hDR
  have hsD := hs.mono hDR
  have h0D : L (0 : ℂ) ∈ D := by
    simpa [D] using (Metric.mem_ball_self hr : (0 : V) ∈ Metric.ball (0 : V) r)
  obtain ⟨e, he0, heD, he, hei, heq⟩ := exists_localInverse_of_conductivity_stream
    (by simp : (∞ : ℕ∞ω) ≠ 0) Metric.isOpen_ball hvD hsD h0D
    (hBp _) (hds _ (hDR h0D)) (by simpa using hgrad)
  have heΩ : e.source ⊆ Ω := by
    intro z hz
    have hh := hDU (heD hz)
    simpa only [U, L, mem_preimage, LinearIsometryEquiv.symm_apply_apply] using hh
  have hmap : (e : ℂ → ℂ) = fun z => (v (L z) : ℂ) + (s (L z) : ℂ) * Complex.I :=
    funext heq
  refine ⟨e, he0, heΩ, he, hei, ?_, ?_⟩
  · rw [hmap]
    exact det_fderiv_pos_of_conductivity_stream (hBp _)
      ((hv.differentiableOn (by simp)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (hDR h0D)))
      (hds _ (hDR h0D)) (by simpa using hgrad)
  · intro z hz
    rw [hmap]
    have hzD := heD hz
    have hzR := hDR hzD
    have hd := hds (L z) hzR
    have hBA := hBsame (L z) hzD
    rw [LinearIsometryEquiv.symm_apply_apply] at hBA
    have hdsA : HasFDerivAt s
        (planarFluxForm (fun x => DeGiorgi.matMulE (A z) (DeGiorgi.smoothGradField v x)) (L z))
        (L z) := by simpa only [planarFluxForm, hBA] using hd
    exact beltrami_fderiv_of_unit_determinant_conductivity_stream (A := fun _ => A z)
      (hpos z (heΩ hz)) (hdet z (heΩ hz))
      ((hv.differentiableOn (by simp)).differentiableAt (Metric.isOpen_ball.mem_nhds hzR)) hdsA

private theorem exists_local_isothermal_coordinates_at_point
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) Ω)
    (hpos : ∀ z ∈ Ω, (A z).PosDef) (hdet : ∀ z ∈ Ω, (A z).det = 1)
    {p : ℂ} (hp : p ∈ Ω) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e.source ⊆ Ω ∧ e p = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      0 < (fderiv ℝ e p).toLinearMap.det ∧
      ∀ z ∈ e.source, complexAntilinearPart (fderiv ℝ e z) =
        beltramiCoefficient (A z 1 1) (A z 0 0) (-A z 0 1) *
          complexLinearPart (fderiv ℝ e z) := by
  let U := (fun z : ℂ => p + z) ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage (continuous_const.add continuous_id)
  have h0 : (0 : ℂ) ∈ U := by simpa only [U, mem_preimage, add_zero] using hp
  have hshift (i j : Fin 2) : ContDiffOn ℝ ∞ (fun z => A (p + z) i j) U :=
    (hA i j).comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hz => hz)
  obtain ⟨e, he0, heU, he, hei, hedet, heB⟩ := exists_local_beltrami_coordinate_at_zero
    hU h0 (fun z => A (p + z)) hshift (fun z hz => hpos (p + z) hz)
    (fun z hz => hdet (p + z) hz)
  obtain ⟨f, hfp, hfΩ, hf0, hf, hfi, _, _, hfB, hfdet⟩ :=
    exists_normalized_translate_beltrami (μ := fun z =>
      beltramiCoefficient (A z 1 1) (A z 0 0) (-A z 0 1)) e p he0 heU he hei heB hedet
  exact ⟨f, hfp, hfΩ, hf0, hf, hfi, hfdet, hfB⟩

theorem exists_local_isothermal_coordinates
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) Ω)
    (hpos : ∀ z ∈ Ω, (A z).PosDef) (hdet : ∀ z ∈ Ω, (A z).det = 1)
    {p : ℂ} (hp : p ∈ Ω) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e.source ⊆ Ω ∧ e p = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ z ∈ e.source, 0 < (fderiv ℝ e z).toLinearMap.det) ∧
      ∀ z ∈ e.source, complexAntilinearPart (fderiv ℝ e z) =
        beltramiCoefficient (A z 1 1) (A z 0 0) (-A z 0 1) *
          complexLinearPart (fderiv ℝ e z) := by
  obtain ⟨e, hep, heΩ, he0, he, hei, hedet, heB⟩ :=
    exists_local_isothermal_coordinates_at_point hΩ A hA hpos hdet hp
  obtain ⟨U, hU, hpU, hUe, hUdet⟩ := exists_open_det_fderiv_pos
    ((he.contDiffAt (e.open_source.mem_nhds hep)).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by decide))
    (e.open_source.mem_nhds hep) hedet
  let f := e.restrOpen U hU
  have hfsource : f.source = e.source ∩ U := rfl
  have hftarget : f.target ⊆ e.target := fun _ hy => hy.1
  refine ⟨f, ⟨hep, hpU⟩, fun z hz => heΩ hz.1, he0,
    he.mono (fun z hz => hz.1), hei.mono hftarget, ?_, ?_⟩
  · intro z hz
    exact hUdet z hz.2
  · intro z hz
    exact heB z hz.1

end DifferentialGeometry.Analysis

end

end
