import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Integration.Lp.Product

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkp_two_of_hasWeakPartialDeriv
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemLp u p (volume.restrict Ω))
    {g : Fin d → E → ℝ} (hg : ∀ i, DeGiorgi.MemW1p p (g i) Ω)
    (hweak : ∀ i, DeGiorgi.HasWeakPartialDeriv i (g i) u Ω) :
    MemWkp 2 p u Ω := by
  have huW : DeGiorgi.MemW1p p u Ω := ⟨hu, fun i => ⟨g i, (hg i).1, hweak i⟩⟩
  refine ⟨huW, ?_⟩
  intro i
  apply MemWkp.one_iff_memW1p.mpr
  have heq := DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
    (chosenWeakPartial'_isWeakPartial_of_mem huW i) (hweak i)
    ((chosenWeakPartial'_memLp_of_mem huW i).locallyIntegrable hp)
    ((hg i).1.locallyIntegrable hp)
  exact (MemW1p_congr_ae hΩ heq.symm).mp (hg i)

theorem ae_memWkp_two_of_hasWeakPartialDeriv
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : Z × E → ℝ} (hu : MemLp u p (μ.prod (volume.restrict Ω)))
    {g : Fin d → Z × E → ℝ} (hg : ∀ i, MemLp (g i) p (μ.prod (volume.restrict Ω)))
    {v : Fin d → Fin d → Z × E → ℝ}
    (hv : ∀ i k, MemLp (v i k) p (μ.prod (volume.restrict Ω)))
    (hfirst : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => g i (t, x)) (fun x => u (t, x)) Ω)
    (hsecond : ∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v i k (t, x)) (fun x => g i (t, x)) Ω) :
    ∀ᵐ t ∂μ, MemWkp 2 p (fun x => u (t, x)) Ω := by
  have hgLp := ae_all_iff.mpr (fun i => (hg i).prodMk_left hptop)
  have hvLp := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k => (hv i k).prodMk_left hptop))
  have hfirst' := ae_all_iff.mpr hfirst
  have hsecond' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hsecond i))
  filter_upwards [hu.prodMk_left hptop, hgLp, hvLp, hfirst', hsecond']
    with t hut hgt hvt hft hst
  apply memWkp_two_of_hasWeakPartialDeriv hp hΩ hut (g := fun i x => g i (t, x))
  · intro i
    exact ⟨hgt i, fun k => ⟨fun x => v i k (t, x), hvt i k, hst i k⟩⟩
  · exact hft

end DifferentialGeometry.Analysis.Sobolev.Euclidean
