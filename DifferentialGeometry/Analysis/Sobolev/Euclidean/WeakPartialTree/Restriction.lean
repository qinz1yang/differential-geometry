import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_weak_partial_tree_restrict
    {Z : Type*} [MeasurableSpace Z] {μ μ' : Measure Z} (hμ : μ' ≤ μ)
    {p : ℝ≥0∞} {Ω Ω' : Set E} (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) (K : ℕ)
    (V : ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω)))
    (hV : ∀ n, n < K → ∀ α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => V (n + 1) (Fin.cons i α) (t, x)) (fun x => V n α (t, x)) Ω) :
    ∃ W : ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p (μ'.prod (volume.restrict Ω')),
      (∀ n α, W n α =ᵐ[μ'.prod (volume.restrict Ω')] V n α) ∧
        ∀ n, n < K → ∀ α i, ∀ᵐ t ∂μ',
          DeGiorgi.HasWeakPartialDeriv i
            (fun x => W (n + 1) (Fin.cons i α) (t, x)) (fun x => W n α (t, x)) Ω' := by
  have hν : μ'.prod (volume.restrict Ω') ≤ μ.prod (volume.restrict Ω) :=
    Measure.prod_mono hμ (Measure.restrict_mono hsub le_rfl)
  have hmem (n : ℕ) (α : Fin n → Fin d) :
      MemLp (V n α) p (μ'.prod (volume.restrict Ω')) := (Lp.memLp (V n α)).mono_measure hν
  let W := fun n α => (hmem n α).toLp (V n α)
  have hW (n : ℕ) (α : Fin n → Fin d) :
      W n α =ᵐ[μ'.prod (volume.restrict Ω')] V n α := (hmem n α).coeFn_toLp
  refine ⟨W, hW, ?_⟩
  intro n hn α i
  filter_upwards [(hV n hn α i).filter_mono (ae_mono hμ),
    Measure.ae_ae_of_ae_prod (hW n α),
    Measure.ae_ae_of_ae_prod (hW (n + 1) (Fin.cons i α))] with t ht hroot hchild
  exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ' hsub ht).congr_ae
    (Filter.EventuallyEq.symm hroot) (Filter.EventuallyEq.symm hchild)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
