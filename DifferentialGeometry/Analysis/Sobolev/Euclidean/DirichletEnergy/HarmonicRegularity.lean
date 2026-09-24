import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.HarmonicMinimizer
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.Harmonic

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω V : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_weakly_harmonic_dirichlet_minimizer_with_component_representatives
    (hd : 2 ≤ d) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {ι : Type*} [Fintype ι]
    {b : E → EuclideanSpace ℝ ι}
    (hb : ∀ i, DeGiorgi.MemW1p 2 (fun x => b x i) Ω)
    (hV : IsOpen V) (hV_compact : IsCompact (closure V))
    (hV_sub : closure V ⊆ Ω) :
    ∃ (u : E → EuclideanSpace ℝ ι),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      ∃ hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω,
        (∀ (v : E → EuclideanSpace ℝ ι),
          (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) →
          ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
            (∑ i, ∫ x in Ω, ‖(hu i).weakGrad x‖ ^ 2) ≤
              ∑ i, ∫ x in Ω, ‖(hv i).weakGrad x‖ ^ 2) ∧
        (∀ i (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
          (∫ x in Ω, inner ℝ ((hu i).weakGrad x)
            (DeGiorgi.smoothGradField φ x)) = 0) ∧
        (∀ i, ∃ v : E → ℝ,
          ContDiffOn ℝ (∞ : WithTop ℕ∞) v V ∧
          (fun x => u x i) =ᵐ[volume.restrict V] v) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨u, hu0, hu, hmin, hEuler⟩ :=
    exists_weakly_harmonic_dirichlet_minimizer hd hΩ hΩb hb
  refine ⟨u, hu0, hu, hmin, hEuler, fun i => ?_⟩
  exact exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero
    hΩ hV hV_compact hV_sub (hu i) (hEuler i)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
