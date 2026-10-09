import DifferentialGeometry.Analysis.Elliptic.Planar.ContinuousStreamFunction
import DifferentialGeometry.Analysis.Elliptic.Planar.IsothermalPrincipal

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

/-- For determinant-one conductivity, the principal contraction factor is the
actual real determinant of the same Beltrami differential. -/
theorem planarIsothermalFactor_eq_det_of_beltrami
    {A : Matrix (Fin 2) (Fin 2) ℝ} {L : ℂ →L[ℝ] ℂ}
    (hA : A.PosDef) (hdet : A.det = 1)
    (hBel : complexAntilinearPart L =
      beltramiCoefficient (A 1 1) (A 0 0) (-A 0 1) * complexLinearPart L) :
    planarIsothermalFactor A L = L.det := by
  have hcross : A 1 0 = A 0 1 :=
    (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).apply 0 1
  have hb : 0 < A 1 1 := hA.diag_pos
  have hd : A 1 1 * A 0 0 - (-A 0 1) ^ 2 = 1 := by
    rw [Matrix.det_fin_two, hcross] at hdet
    nlinarith only [hdet]
  have hcols : L 1 + Complex.I * L Complex.I =
      beltramiCoefficient (A 1 1) (A 0 0) (-A 0 1) *
        (L 1 - Complex.I * L Complex.I) := by
    rw [complexAntilinearPart, complexLinearPart, ← mul_div_assoc] at hBel
    exact (div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)).mp hBel
  have hLI : L Complex.I = (((-A 0 1 : ℝ) : ℂ) + Complex.I) / (A 1 1 : ℝ) * L 1 := by
    have hh := (beltrami_eq_iff_metric_columns hb (by rw [hd]; norm_num)
      (L 1) (L Complex.I)).mp hcols
    simpa only [hd, Real.sqrt_one, Complex.ofReal_one, one_mul] using hh
  change planarIsothermalFactor A L = L.toLinearMap.det
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr,
    Complex.coe_basisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  change planarIsothermalFactor A L =
    (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im
  rw [hLI]
  simp only [planarIsothermalFactor, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, add_zero, zero_add]
  ring

/-- A noncritical `C¹` weak conductivity solution supplies a centered,
orientation-positive `C¹` chart with the exact determinant principal identity.
The stream is constructed for the literal original flux. -/
theorem exists_c1_principal_chart_of_noncritical_weak_conductivity_solution
    {R : ℝ} (hR : 0 < R) (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, ContinuousOn (fun z => A z i j) (ball 0 R))
    (hpos : ∀ z ∈ ball 0 R, (A z).PosDef)
    (hdet : ∀ z ∈ ball 0 R, (A z).det = 1)
    (v : V → ℝ) (hv : ContDiffOn ℝ 1 v (ball 0 R))
    (hdiv : DeGiorgi.HasWeakDiv 0
      (fun x => DeGiorgi.matMulE (A (Complex.orthonormalBasisOneI.repr.symm x))
        (DeGiorgi.smoothGradField v x)) (ball 0 R))
    (hgrad : DeGiorgi.smoothGradField v 0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      0 ∈ e.source ∧ e.source ⊆ ball 0 R ∧ e 0 = 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ z ∈ e.source, 0 < (fderiv ℝ e z).det) ∧
      ∀ z ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
        (∑ i : Fin 2, ∑ j : Fin 2, A z i j *
          H (fderiv ℝ e z ((![1, Complex.I] : Fin 2 → ℂ) i))
            (fderiv ℝ e z ((![1, Complex.I] : Fin 2 → ℂ) j))) =
          (fderiv ℝ e z).det * (H 1 1 + H Complex.I Complex.I) := by
  let L := Complex.orthonormalBasisOneI.repr
  let K : V → Matrix (Fin 2) (Fin 2) ℝ := fun x => A (L.symm x)
  let F : V → V := fun x => DeGiorgi.matMulE (K x) (DeGiorgi.smoothGradField v x)
  have hLball {x : V} (hx : x ∈ ball 0 R) : L.symm x ∈ ball 0 R := by
    simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have hflux : ContinuousOn F (ball 0 R) := by
    change ContinuousOn (fun x => WithLp.toLp 2 (fun i : Fin 2 =>
      ∑ j : Fin 2, K x i j * fderiv ℝ v x (EuclideanSpace.single j 1))) (ball 0 R)
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_finsetSum
    intro j _
    exact ((hA i j).comp L.symm.continuous.continuousOn (fun x hx => hLball hx)).mul
      ((hv.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const)
  obtain ⟨s, hs, _, hds⟩ :=
    exists_contDiff_one_stream_function_of_continuousOn_hasWeakDiv_zero 0 R hR hflux hdiv
  have hhalf : ball (0 : V) (R / 2) ⊆ ball 0 R := ball_subset_ball (by linarith)
  have h0 : L (0 : ℂ) ∈ ball (0 : V) (R / 2) := by
    simpa only [map_zero] using mem_ball_self (half_pos hR)
  obtain ⟨e, he0, hehalf, he, hei, heq⟩ := exists_localInverse_of_conductivity_stream
    one_ne_zero isOpen_ball (hv.mono hhalf) hs h0
    (by simpa only [K, L, map_zero] using hpos 0 (mem_ball_self hR))
    (hds _ h0) (by simpa only [L, map_zero] using hgrad)
  have heR : e.source ⊆ ball 0 R := by
    intro z hz
    have hh := hhalf (hehalf hz)
    simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hh
  have hmap : (e : ℂ → ℂ) = fun z => (v (L z) : ℂ) + (s (L z) : ℂ) * Complex.I :=
    funext heq
  have hedet : 0 < (fderiv ℝ e 0).toLinearMap.det := by
    rw [hmap]
    apply det_fderiv_pos_of_conductivity_stream
      (by simpa only [K, L, map_zero] using hpos 0 (mem_ball_self hR))
      ((hv.differentiableOn one_ne_zero).differentiableAt
        (isOpen_ball.mem_nhds (hhalf h0))) (hds _ h0)
    simpa only [L, map_zero] using hgrad
  have heBel : ∀ z ∈ e.source, complexAntilinearPart (fderiv ℝ e z) =
      beltramiCoefficient (A z 1 1) (A z 0 0) (-A z 0 1) *
        complexLinearPart (fderiv ℝ e z) := by
    intro z hz
    rw [hmap]
    have hd := hds (L z) (hehalf hz)
    have hh := beltrami_fderiv_of_unit_determinant_conductivity_stream (A := K)
      (by simpa only [K, L, LinearIsometryEquiv.symm_apply_apply] using hpos z (heR hz))
      (by simpa only [K, L, LinearIsometryEquiv.symm_apply_apply] using hdet z (heR hz))
      ((hv.differentiableOn one_ne_zero).differentiableAt
        (isOpen_ball.mem_nhds (hhalf (hehalf hz)))) hd
    simpa only [K, L, LinearIsometryEquiv.symm_apply_apply] using hh
  obtain ⟨f, hf0, hfR, hfzero, hf, hfi, _, _, hfBel, hfdet⟩ :=
    exists_normalized_translate_beltrami (U := ball (0 : ℂ) R) (μ := fun z =>
      beltramiCoefficient (A z 1 1) (A z 0 0) (-A z 0 1)) e 0 he0
      (by
        intro z hz
        change (0 : ℂ) + z ∈ ball 0 R
        simpa only [zero_add] using heR hz) he hei
      (by simpa only [zero_add] using heBel) hedet
  obtain ⟨U, hU, h0U, _, hUdet⟩ := exists_open_det_fderiv_pos
    (hf.contDiffAt (f.open_source.mem_nhds hf0)) (f.open_source.mem_nhds hf0) hfdet
  let g := f.restrOpen U hU
  refine ⟨g, ⟨hf0, h0U⟩, fun z hz => hfR hz.1, hfzero,
    hf.mono (fun z hz => hz.1), hfi.mono (fun z hz => hz.1), ?_, ?_⟩
  · intro z hz
    exact hUdet z hz.2
  · intro z hz H
    have hB := hfBel z hz.1
    have hp := hpos z (hfR hz.1)
    have hd := hdet z (hfR hz.1)
    change (∑ i : Fin 2, ∑ j : Fin 2, A z i j *
      H (fderiv ℝ f z ((![1, Complex.I] : Fin 2 → ℂ) i))
        (fderiv ℝ f z ((![1, Complex.I] : Fin 2 → ℂ) j))) =
      (fderiv ℝ f z).det * (H 1 1 + H Complex.I Complex.I)
    rw [← planarIsothermalFactor_eq_det_of_beltrami hp hd hB]
    exact planar_principal_contraction_of_beltrami (A z) (fderiv ℝ f z) hp hd hB H

end DifferentialGeometry.Analysis
