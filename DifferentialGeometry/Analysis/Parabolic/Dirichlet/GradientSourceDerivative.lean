import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientSourceExpansion
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialSource

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet
open DifferentialGeometry.Analysis.Sobolev.Euclidean
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
abbrev SourceIndex (d : ℕ) := ((Fin d × Fin d) × Bool) ⊕ (Fin d × Bool) ⊕ (Bool × Bool)

theorem exists_lp_gradient_source_spatial_derivative
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {Ω : Set E}
    (hΩ : IsOpen Ω) (F : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (Y : Fin d → SourceIndex d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (DY : Fin d → SourceIndex d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (A : Fin d → SourceIndex d → Z × E → ℝ)
    (hA : ∀ k s, MemLp (A k s) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ k s j, MemLp (fun p => fderiv ℝ (fun x => A k s (p.1, x)) p.2
      (EuclideanSpace.single j 1)) ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ k s, ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A k s (t, x)) Ω)
    (hYweak : ∀ k s j, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv j (fun x => DY k s j (t, x))
        (fun x => Y k s (t, x)) Ω)
    (hF : ∀ k, F k =ᵐ[μ.prod (volume.restrict Ω)]
      fun p => ∑ s, A k s p * Y k s p) :
    ∃ DF : Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (∀ k j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun x => DF k j (t, x)) (fun x => F k (t, x)) Ω) ∧
      (∀ k j, DF k j =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ s,
        (A k s p * DY k s j p +
          fderiv ℝ (fun x => A k s (p.1, x)) p.2
            (EuclideanSpace.single j 1) * Y k s p)) := by
  obtain ⟨DF, hweak, hformula, _⟩ :=
    exists_lp_gradient_source_spatial_derivative_step hΩ F Y DY A hA hDA hAsmooth hYweak hF
  exact ⟨DF, hweak, hformula⟩
end DifferentialGeometry.Analysis.Parabolic.Dirichlet
