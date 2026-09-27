import DifferentialGeometry.Analysis.Parabolic.WeakEquation.AffineTransport
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Affine
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_lp_weighted_weak_equation_comp_add_smul
    (μ : Measure ℝ) [SFinite μ] (J : Set ℝ) (Ω : Set V)
    (ρ : ℝ × V → ℝ) (A : Fin n → Fin n → ℝ × V → ℝ)
    {p : ℝ≥0∞} (U F : Lp ℝ p (μ.prod (volume.restrict Ω)))
    (K : Fin n → Lp ℝ p (μ.prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hweak : ∀ φ : ℝ × V → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ J ×ˢ Ω →
      (∫ q, ρ q * U q * fderiv ℝ φ q (1, 0) ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ q, (∑ i, A i j q * K i q) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) -
        ∫ q, F q * φ q ∂μ.prod (volume.restrict Ω))
    (b : V) {r : ℝ} (hr : r ≠ 0) :
    let ν := μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω))
    let S : ℝ × V → ℝ × V := fun q => (q.1, b + r • q.2)
    let δ := |r ^ n|
    ∃ Uh Fh : Lp ℝ p ν, ∃ Kh : Fin n → Lp ℝ p ν,
      (Uh =ᵐ[ν] fun q => U (S q)) ∧
      (Fh =ᵐ[ν] fun q => δ * F (S q)) ∧
      (∀ i, Kh i =ᵐ[ν] fun q => r * K i (S q)) ∧
      (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => Kh k (t, x)) (fun x => Uh (t, x))
        ((fun x => b + r • x) ⁻¹' Ω)) ∧
      ∀ φ : ℝ × V → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ J ×ˢ ((fun x => b + r • x) ⁻¹' Ω) →
        (∫ q, (δ * ρ (S q)) * Uh q * fderiv ℝ φ q (1, 0) ∂ν) =
          (∑ j, ∫ q, (∑ i, (δ / r ^ 2 * A i j (S q)) * Kh i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ q, Fh q * φ q ∂ν := by
  intro ν S δ
  have hU : MemLp (fun q => U (S q)) p ν :=
    (Lp.memLp U).comp_prod_add_smul μ volume b hr
  have hF : MemLp (fun q => δ * F (S q)) p ν :=
    ((Lp.memLp F).comp_prod_add_smul μ volume b hr).const_mul δ
  have hK (i : Fin n) : MemLp (fun q => r * K i (S q)) p ν :=
    ((Lp.memLp (K i)).comp_prod_add_smul μ volume b hr).const_mul r
  let Uh := hU.toLp (fun q => U (S q))
  let Fh := hF.toLp (fun q => δ * F (S q))
  let Kh := fun i => (hK i).toLp (fun q => r * K i (S q))
  have hUh : Uh =ᵐ[ν] fun q => U (S q) := hU.coeFn_toLp
  have hFh : Fh =ᵐ[ν] fun q => δ * F (S q) := hF.coeFn_toLp
  have hKh (i : Fin n) : Kh i =ᵐ[ν] fun q => r * K i (S q) := (hK i).coeFn_toLp
  refine ⟨Uh, Fh, Kh, hUh, hFh, hKh, ?_, ?_⟩
  · intro k
    filter_upwards [hspatial k, Measure.ae_ae_of_ae_prod hUh,
      Measure.ae_ae_of_ae_prod (hKh k)] with t ht hUt hKt
    exact (ht.comp_add_smul b hr).congr_ae
      (Filter.EventuallyEq.symm hUt) (Filter.EventuallyEq.symm hKt)
  · intro φ hφ hφc hφs
    have hraw := weighted_weak_equation_comp_add_smul μ J Ω ρ U F A
      (fun i => K i) hweak b hr φ hφ hφc hφs
    calc
      _ = ∫ q, (δ * ρ (S q)) * U (S q) * fderiv ℝ φ q (1, 0) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hUh] with q hq
        rw [hq]
      _ = (∑ j, ∫ q, (∑ i, (δ / r ^ 2 * A i j (S q)) * (r * K i (S q))) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ q, (δ * F (S q)) * φ q ∂ν := hraw
      _ = _ := by
        apply congrArg₂ (fun x y : ℝ => x - y)
        · apply Finset.sum_congr rfl
          intro j _
          apply integral_congr_ae
          filter_upwards [ae_all_iff.mpr hKh] with q hq
          simp only [hq]
        · apply integral_congr_ae
          filter_upwards [hFh] with q hq
          rw [hq]

end DifferentialGeometry.Analysis.Parabolic
