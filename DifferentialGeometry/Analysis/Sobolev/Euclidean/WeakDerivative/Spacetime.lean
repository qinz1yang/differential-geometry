import DifferentialGeometry.Analysis.Integration.Measure.EuclideanCoordinates
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.LinearEquiv
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "E₁" => EuclideanSpace ℝ (Fin (d + 1))

theorem exists_lp_spacetime_weak_partial_tree
    {p : ℝ≥0∞} {a b : ℝ} {Ω : Set E} (K : ℕ)
    (Y : ∀ n : ℕ, (Fin n → Fin (d + 1)) →
      Lp ℝ p ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hweak : ∀ n < K, ∀ α i (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ q, Y n α q * fderiv ℝ φ q
        (Fin.cases (1, 0) (fun l => (0, EuclideanSpace.single l 1)) i)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, Y (n + 1) (Fin.cons i α) q * φ q
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) :
    let e := EuclideanSpace.finSuccEquivProd d
    let Ω₁ := e ⁻¹' (Ioo a b ×ˢ Ω)
    ∃ Z : ∀ n : ℕ, (Fin n → Fin (d + 1)) → Lp ℝ p (volume.restrict Ω₁),
      (∀ n α, Z n α =ᵐ[volume.restrict Ω₁] (Y n α) ∘ e) ∧
      ∀ n < K, ∀ α i, DeGiorgi.HasWeakPartialDeriv i
        (Z (n + 1) (Fin.cons i α)) (Z n α) Ω₁ := by
  intro e Ω₁
  let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
  have hν : (volume : Measure (ℝ × E)).restrict (Ioo a b ×ˢ Ω) = ν := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_congr_set Ioo_ae_eq_Icc]
  have he : MeasurePreserving e (volume.restrict Ω₁) ν := by
    have h := (EuclideanSpace.measurePreserving_finSuccEquivProd d).restrict_preimage_emb
      e.toHomeomorph.measurableEmbedding (Ioo a b ×ˢ Ω)
    simpa only [hν] using h
  let Z : ∀ n : ℕ, (Fin n → Fin (d + 1)) → Lp ℝ p (volume.restrict Ω₁) :=
    fun n α => Lp.compMeasurePreserving e he (Y n α)
  have hZ (n : ℕ) (α : Fin n → Fin (d + 1)) :
      Z n α =ᵐ[volume.restrict Ω₁] (Y n α) ∘ e :=
    Lp.coeFn_compMeasurePreserving (Y n α) he
  refine ⟨Z, hZ, ?_⟩
  intro n hn α i
  have hdir : e (EuclideanSpace.single i 1) =
      Fin.cases (1, 0) (fun l => (0, EuclideanSpace.single l 1)) i := by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact EuclideanSpace.finSuccEquivProd_single_zero d
    · exact EuclideanSpace.finSuccEquivProd_single_succ d i
  have h := hasWeakPartialDeriv_comp_continuousLinearEquiv e
    (EuclideanSpace.measurePreserving_finSuccEquivProd d) i
    (u := Y n α) (v := Y (n + 1) (Fin.cons i α)) (by
      intro φ hφ hφc hφs
      change (∫ q, Y n α q * fderiv ℝ φ q (e (EuclideanSpace.single i 1))
        ∂(volume : Measure (ℝ × E)).restrict (Ioo a b ×ˢ Ω)) =
          -∫ q, Y (n + 1) (Fin.cons i α) q * φ q
            ∂(volume : Measure (ℝ × E)).restrict (Ioo a b ×ˢ Ω)
      rw [hν, hdir]
      exact hweak n hn α i φ hφ hφc hφs)
  exact h.congr_ae (hZ n α).symm (hZ (n + 1) (Fin.cons i α)).symm

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
