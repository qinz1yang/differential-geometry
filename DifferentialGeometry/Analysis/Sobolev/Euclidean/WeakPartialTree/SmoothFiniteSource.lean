import DifferentialGeometry.Analysis.Calculus.SpatialDerivativeTree
import DifferentialGeometry.Analysis.Sobolev.Euclidean.FiniteWeakPartialSource

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_weak_partial_tree_of_smooth_finite_sum
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {I T : Set ℝ} (hI : UniqueDiffOn ℝ I) (hT : IsCompact T) (hTI : T ⊆ I)
    {O Ω : Set E} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O) (K : ℕ)
    (f : Lp ℝ p ((volume.restrict T).prod (volume.restrict Ω)))
    (A : ι → ℝ × E → ℝ)
    (Y : ι → ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict T).prod (volume.restrict Ω)))
    (hAsmooth : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (A j) (I ×ˢ O))
    (hYweak : ∀ j n, n < K → ∀ α i, ∀ᵐ t ∂volume.restrict T,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Y j (n + 1) (Fin.cons i α) (t, x))
        (fun x => Y j n α (t, x)) Ω)
    (hf : f =ᵐ[(volume.restrict T).prod (volume.restrict Ω)] fun q =>
      ∑ j, A j q * Y j 0 (fun i => Fin.elim0 i) q) :
    ∃ F : ∀ n : ℕ, (Fin n → Fin d) →
        Lp ℝ p ((volume.restrict T).prod (volume.restrict Ω)),
      F 0 (fun i => Fin.elim0 i) = f ∧
        ∀ n, n < K → ∀ α i, ∀ᵐ t ∂volume.restrict T,
          DeGiorgi.HasWeakPartialDeriv i
            (fun x => F (n + 1) (Fin.cons i α) (t, x))
            (fun x => F n α (t, x)) Ω := by
  classical
  choose B hBroot hBsmooth hBLp hBD using fun j =>
    DifferentialGeometry.Analysis.exists_spatial_derivative_tree_of_contDiffOn
      hI hO (hAsmooth j) (hT.prod hΩc) (prod_mono hTI hΩO)
      ((volume : Measure ℝ).prod volume) (fun i : Fin d => EuclideanSpace.single i 1)
  have hB (j : ι) (n : ℕ) (α : Fin n → Fin d) :
      MemLp (B j n α) ∞ ((volume.restrict T).prod (volume.restrict Ω)) := by
    rw [Measure.prod_restrict]
    exact (hBLp j n α).mono_measure
      (Measure.restrict_mono_set _ (prod_mono Subset.rfl subset_closure))
  have hBslice (j : ι) (n : ℕ) (α : Fin n → Fin d) :
      ∀ᵐ t ∂volume.restrict T, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => B j n α (t, x)) Ω := by
    filter_upwards [ae_restrict_mem hT.measurableSet] with t ht
    exact (hBsmooth j n α).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => ⟨hTI ht, hΩO (subset_closure hx)⟩)
  apply exists_lp_weak_partial_tree_of_finite_sum hp hΩ K f B
    (fun j n α q => Y j n α q) (fun j n _ α => hB j n α)
    (fun j n _ α => Lp.memLp (Y j n α)) (fun j n _ α => hBslice j n α)
    (fun j n _ α i => Filter.EventuallyEq.of_eq (hBD j n α i)) hYweak
  simpa only [hBroot] using hf

end DifferentialGeometry.Analysis.Sobolev.Euclidean
