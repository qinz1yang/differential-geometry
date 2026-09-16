import DifferentialGeometry.External.DeGiorgi.WeakFormulation.CoefficientOperator

noncomputable section

open MeasureTheory Filter Set DeGiorgi
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_poincare_constant
    {Ω : Set E} (hd : 2 ≤ d) (hΩ : IsOpen Ω)
    (hΩ_bdd : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : E → ℝ}, MemW01p 2 f Ω →
      ∀ hw : MemW1pWitness 2 f Ω,
        ‖hw.memLp.toLp f‖ ≤ C * ‖gradLpOfWitness hw‖ := by
  let _ : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hP⟩ := smoothCompactSupport_L2_bound_on_bounded_ge_two hd hΩ_bdd
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f hf hw
  obtain ⟨_, hw₀, φ, hφs, hφc, hφΩ, hφf, hφg⟩ := hf
  let ht (n : ℕ) : IsSmoothTestOn Ω (φ n) := ⟨hφs n, hφc n, hφΩ n⟩
  let hφw (n : ℕ) := smoothTestWitness hΩ (ht n)
  have hF : Tendsto (fun n => smoothFunToLp hΩ (ht n)) atTop
      (𝓝 (hw.memLp.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n => (hφw n).memLp)
      (f_lim_ℒp := hw.memLp)).mpr hφf
  have hG : Tendsto (fun n => gradLpOfWitness (hφw n)) atTop
      (𝓝 (gradLpOfWitness hw₀)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n =>
      (hφw n).weakGrad_memLp) (f_lim_ℒp := hw₀.weakGrad_memLp)).mpr
    exact tendsto_eLpNorm_vector_of_componentwise
      (fun n i => ((hφw n).weakGrad_component_memLp i).sub
        (hw₀.weakGrad_component_memLp i))
      (fun i => by simpa only [hφw, smoothTestWitness, smoothGradField,
        PiLp.toLp_apply] using hφg i)
  have hGeq : gradLpOfWitness hw₀ = gradLpOfWitness hw :=
    MemLp.toLp_congr hw₀.weakGrad_memLp hw.weakGrad_memLp
      (MemW1pWitness.ae_eq hΩ hw₀ hw)
  have hbound (n : ℕ) :
      ‖smoothFunToLp hΩ (ht n)‖ ≤ C.toReal * ‖gradLpOfWitness (hφw n)‖ := by
    have hgrad : MemLp (smoothGradNorm (φ n)) 2 (volume.restrict Ω) := by
      exact MemLp.ae_eq (Eventually.of_forall fun x => by
        change ‖smoothGradField (φ n) x‖ = smoothGradNorm (φ n) x
        exact norm_smoothGradField_eq_smoothGradNorm) (hφw n).weakGrad_memLp.norm
    have hPn := hP (hφs n) (hφc n) (hφΩ n)
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hC.ne hgrad.eLpNorm_lt_top.ne) hPn
    have hnorm : eLpNorm (smoothGradNorm (φ n)) 2 (volume.restrict Ω) =
        eLpNorm (hφw n).weakGrad 2 (volume.restrict Ω) := by
      change eLpNorm (fun x => ‖(hφw n).weakGrad x‖) 2 (volume.restrict Ω) = _
      exact eLpNorm_norm _
    rw [hnorm, ENNReal.toReal_mul] at hreal
    simpa only [smoothFunToLp, gradLpOfWitness, Lp.norm_toLp] using hreal
  rw [hGeq] at hG
  exact le_of_tendsto_of_tendsto' hF.norm (hG.norm.const_mul C.toReal) hbound

end DifferentialGeometry.Analysis.Sobolev.Euclidean
