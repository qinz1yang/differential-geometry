import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.C1PrincipalChart
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.NoncriticalSolution
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.RescaledPrincipalChart

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

/-- A locally `C¹`, positive, determinant-one conductivity has a centered,
orientation-positive `C¹` principal chart. The identity uses the original
coefficient field and the actual determinant of this chart. No solution,
noncriticality, or coordinate map is assumed. -/
theorem exists_c1_isothermal_principal_chart
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (h0 : (0 : ℂ) ∈ Ω)
    (K : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j, ContDiffOn ℝ 1 (fun z => K z i j) Ω)
    (hpos : ∀ z ∈ Ω, (K z).PosDef)
    (hdet : ∀ z ∈ Ω, (K z).det = 1) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      0 ∈ e.source ∧ e.source ⊆ Ω ∧ e 0 = 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ z ∈ e.source, 0 < (fderiv ℝ e z).det) ∧
      ∀ z ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
        (∑ i : Fin 2, ∑ j : Fin 2, K z i j *
          H (fderiv ℝ e z ((![1, Complex.I] : Fin 2 → ℂ) i))
            (fderiv ℝ e z ((![1, Complex.I] : Fin 2 → ℂ) j))) =
          (fderiv ℝ e z).det * (H 1 1 + H Complex.I Complex.I) := by
  let L := Complex.orthonormalBasisOneI.repr
  let ΩE : Set V := L.symm ⁻¹' Ω
  let KE : V → Matrix (Fin 2) (Fin 2) ℝ := fun x => K (L.symm x)
  have hΩE : IsOpen ΩE := hΩ.preimage L.symm.continuous
  have h0E : (0 : V) ∈ ΩE := by
    simpa only [ΩE, mem_preimage, map_zero] using h0
  have hKE : ∀ i j, ContDiffOn ℝ 1 (fun x => KE x i j) ΩE := by
    intro i j
    exact (hK i j).comp L.symm.contDiff.contDiffOn (fun x hx => hx)
  obtain ⟨ρ, hρ, hball, v, hv, hdiv, hgrad⟩ :=
    exists_noncritical_rescaled_c1_weak_conductivity_solution hΩE h0E KE hKE
      (fun x hx => hpos _ hx) (fun x hx => hdet _ hx)
  have hR : (0 : ℝ) < 1 / 8 := by norm_num
  have hinside {z : ℂ} (hz : z ∈ ball 0 (1 / 8 : ℝ)) : ρ • z ∈ Ω := by
    have hn : ‖z‖ ≤ 1 := by
      have hh := Metric.mem_ball.mp hz
      rw [dist_zero_right] at hh
      linarith
    have hh : L (ρ • z) ∈ closedBall (0 : V) ρ := by
      rw [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map,
        norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hρ.le
    have hm := hball hh
    simpa only [ΩE, mem_preimage, LinearIsometryEquiv.symm_apply_apply] using hm
  have hscaled : ∀ i j, ContinuousOn (fun z => K (ρ • z) i j)
      (ball 0 (1 / 8 : ℝ)) := by
    intro i j
    exact (hK i j).continuousOn.comp (continuous_id.const_smul ρ).continuousOn
      (fun z hz => hinside hz)
  have hdiv' : DeGiorgi.HasWeakDiv 0
      (fun x => DeGiorgi.matMulE
        (K (ρ • Complex.orthonormalBasisOneI.repr.symm x))
        (DeGiorgi.smoothGradField v x)) (ball 0 (1 / 8 : ℝ)) := by
    simpa only [KE, L, map_smul] using hdiv
  obtain ⟨e, he0, heR, hezero, he, hei, hedet, heprincipal⟩ :=
    exists_c1_principal_chart_of_noncritical_weak_conductivity_solution hR
      (fun z => K (ρ • z)) hscaled (fun z hz => hpos _ (hinside hz))
      (fun z hz => hdet _ (hinside hz)) v hv hdiv' hgrad
  let f : OpenPartialHomeomorph ℂ ℂ :=
    (Homeomorph.smulOfNeZero ρ⁻¹ (inv_ne_zero hρ.ne')).toOpenPartialHomeomorph.trans e
  obtain ⟨_, _, hfs, _, _, hf0, _, hfzero, hf, hfi, _, _, hfdet, hfprincipal⟩ :=
    rescale_principal_chart K hρ hR e he0 heR hezero he hei hedet heprincipal
  refine ⟨f, hf0, ?_, hfzero, hf, hfi, hfdet, hfprincipal⟩
  intro z hz
  have hh : ρ⁻¹ • z ∈ e.source := by
    change z ∈ f.source at hz
    rw [hfs] at hz
    exact hz
  have hm := hinside (heR hh)
  simpa only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] using hm

end DifferentialGeometry.Analysis
