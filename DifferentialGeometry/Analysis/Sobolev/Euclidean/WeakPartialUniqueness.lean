import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import DifferentialGeometry.Analysis.Integration.Lp.Product

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

theorem lp_eq_of_ae_hasWeakPartialDeriv
    {Z : Type*} [MeasurableSpace Z] {d : ℕ} {μ : Measure Z}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (i : Fin d) (P : Z → EuclideanSpace ℝ (Fin d) → ℝ)
    (H H' : Lp ℝ p (μ.prod (volume.restrict Ω)))
    (hH : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => H (t, x)) (P t) Ω)
    (hH' : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => H' (t, x)) (P t) Ω) :
    H = H' := by
  apply Lp.ext_curry
  have hslice (G : Lp ℝ p (μ.prod (volume.restrict Ω))) :
      ∀ᵐ t ∂μ, MemLp (fun x => G (t, x)) p (volume.restrict Ω) := by
    by_cases hpt : p = ⊤
    · subst p
      exact (Lp.memLp G).prodMk_left_top
    · exact (Lp.memLp G).prodMk_left hpt
  filter_upwards [hH, hH', hslice H, hslice H'] with t ht ht' hHt hHt'
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ ht ht'
    (hHt.locallyIntegrable hp) (hHt'.locallyIntegrable hp)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
