import DifferentialGeometry.Analysis.Calculus.Derivative.RankOneDivergence
import DifferentialGeometry.Analysis.Calculus.Derivative.RankOneContraction
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.DirectionalDrift

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem integral_add_matrix_spatial_derivative_mul_nonneg_of_ae_approximate_upper_contacts
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype κ]
    {ν : Measure ℝ} {μ : Measure E} [IsFiniteMeasureOnCompacts ν] [Measure.IsAddHaarMeasure μ]
    {f : ℝ × E → ℝ} {J : Set ℝ} {V : Set E}
    (hlip : LocallyLipschitzOn (J ×ˢ V) f) (hJ : IsOpen J) (hV : IsOpen V)
    (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hconc : ∀ s ∈ J, ConcaveOn ℝ V (fun z => f (s, z) - A z z / 2))
    (e : Module.Basis ι ℝ E) (v : κ → E) (w : κ → ℝ × E → ℝ)
    (hw : ∀ j, ContDiffOn ℝ 2 (w j) (J ×ˢ V))
    (hwn : ∀ j, ∀ p ∈ J ×ˢ V, 0 ≤ w j p)
    (C : ι → ι → ℝ × E → ℝ)
    (hC : ∀ p ∈ J ×ˢ V, ∀ i j,
      C i j p = ∑ m, w m p * e.repr (v m) i * e.repr (v m) j)
    (B : ℝ × E → ℝ) (hB : LocallyIntegrableOn B (J ×ˢ V) (ν.prod μ))
    (hcontact : ∀ᵐ p ∂ν.prod μ, p ∈ J ×ˢ V → ∀ ε : ℝ, 0 < ε →
      ∃ ψ : κ → ℝ → ℝ, (∀ j, ContDiffAt ℝ 2 (ψ j) 0) ∧
        (∀ j, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v j) ≤ ψ j t) ∧
        (∀ j, f p = ψ j 0) ∧
        (∑ j, w j p * deriv (deriv (ψ j)) 0) ≤ B p -
          (∑ ij : ι × ι, fderiv ℝ (fun z => C ij.1 ij.2 (p.1, z)) p.2 (e ij.1) *
            fderiv ℝ (fun z => f (p.1, z)) p.2 (e ij.2)) + ε)
    (φ : ℝ × E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφV : tsupport φ ⊆ J ×ˢ V) (hφn : ∀ p, 0 ≤ φ p) :
    0 ≤ ∫ p, B p * φ p + ∑ ij : ι × ι, C ij.1 ij.2 p *
      fderiv ℝ (fun z => f (p.1, z)) p.2 (e ij.1) *
        fderiv ℝ φ p (0, e ij.2) ∂ν.prod μ := by
  classical
  have hcontact' : ∀ᵐ p ∂ν.prod μ, p ∈ J ×ˢ V → ∀ ε : ℝ, 0 < ε →
      ∃ ψ : κ → ℝ → ℝ, (∀ j, ContDiffAt ℝ 2 (ψ j) 0) ∧
        (∀ j, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v j) ≤ ψ j t) ∧
        (∀ j, f p = ψ j 0) ∧
        (∑ j, w j p * deriv (deriv (ψ j)) 0) ≤ B p -
          (∑ j, fderiv ℝ (w j) p (0, v j) *
            fderiv ℝ (fun z => f (p.1, z)) p.2 (v j)) + ε := by
    filter_upwards [hcontact] with p hp hpJV ε hε
    obtain ⟨ψ, hψ, hu, heq, hb⟩ := hp hpJV ε hε
    have hslice : DifferentiableAt ℝ (fun z : E => (p.1, z)) p.2 :=
      (differentiableAt_const p.1).prodMk differentiableAt_id
    have hwd (j : κ) : DifferentiableAt ℝ (w j) p :=
      ((hw j p hpJV).contDiffAt ((hJ.prod hV).mem_nhds hpJV)).differentiableAt
        (by norm_num)
    have hws (j : κ) : DifferentiableAt ℝ (fun z => w j (p.1, z)) p.2 := by
      simpa only [Function.comp_def] using
        DifferentiableAt.comp (𝕜 := ℝ) (g := w j) (f := fun z : E => (p.1, z))
          p.2 (hwd j) hslice
    have hwder (j : κ) (z : E) :
        fderiv ℝ (fun u => w j (p.1, u)) p.2 z = fderiv ℝ (w j) p (0, z) := by
      have hcomp := HasFDerivAt.comp (𝕜 := ℝ)
        (g := w j) (f := fun z : E => (p.1, z)) p.2 (hwd j).hasFDerivAt
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))
      exact congrArg (fun D => D z) hcomp.fderiv
    have hdiv := sum_fderiv_mul_eq_of_rank_one_coefficients
      e Finset.univ (fun j z => w j (p.1, z)) v (fun i j z => C i j (p.1, z))
      p.2 (fderiv ℝ (fun z => f (p.1, z)) p.2)
      (fun j _ => hws j) (fun i j => by
        filter_upwards [hV.mem_nhds hpJV.2] with z hz
        exact hC (p.1, z) ⟨hpJV.1, hz⟩ i j)
    simp only [hwder] at hdiv
    refine ⟨ψ, hψ, hu, heq, ?_⟩
    simpa only [Fintype.sum_prod_type, hdiv] using hb
  have hweak :=
    integral_add_sum_spatial_derivative_mul_nonneg_of_ae_approximate_upper_contacts
      hlip hJ hV A hconc v w hw hwn B hB hcontact' φ hφ hφc hφV hφn
  convert hweak using 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  apply congrArg (fun z : ℝ => B p * φ p + z)
  by_cases hp : p ∈ tsupport φ
  · let df := fderiv ℝ (fun z => f (p.1, z)) p.2
    let dt : E →L[ℝ] ℝ := (fderiv ℝ φ p).comp (ContinuousLinearMap.inr ℝ ℝ E)
    have hsum := ContinuousLinearMap.sum_mul_apply_diagonal_eq_sum_coordinates
      (df.smulRight dt) e Finset.univ (fun j => w j p) v (fun i j => C i j p)
      (fun i j => hC p (hφV hp) i j)
    simpa only [Fintype.sum_prod_type, ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      df, dt, mul_assoc] using hsum.symm
  · rw [fderiv_of_notMem_tsupport ℝ hp]
    simp only [zero_apply, mul_zero, Finset.sum_const_zero]

end DifferentialGeometry.Analysis.Calculus
