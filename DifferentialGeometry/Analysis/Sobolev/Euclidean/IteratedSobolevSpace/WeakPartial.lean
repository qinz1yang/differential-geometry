import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation
import DifferentialGeometry.Analysis.Integration.Lp.Product

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem MemWkp.iterWeakPartial_mem
    {k j : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (hu : MemWkp (k + j) p u Ω) (α : Fin j → Fin d) :
    MemWkp k p (iterWeakPartial p j α u Ω) Ω := by
  induction j generalizing u with
  | zero => simpa only [Nat.add_zero, iterWeakPartial_zero] using hu
  | succ j ih =>
    rw [iterWeakPartial_succ]
    exact ih (hu.chosenWeakPartial_mem (α 0)) (fun i => α i.succ)

theorem MemWkp.mem_of_hasWeakPartialDeriv
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u g : E → ℝ} (hu : MemWkp (k + 1) p u Ω)
    {i : Fin d} (hg : LocallyIntegrable g (volume.restrict Ω))
    (hweak : DeGiorgi.HasWeakPartialDeriv i g u Ω) :
    MemWkp k p g Ω := by
  have hchosen := chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i
  have hchosenLp := chosenWeakPartial'_memLp_of_mem hu.memW1p i
  have hae := DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hchosen hweak
    (hchosenLp.locallyIntegrable hp) hg
  exact (MemWkp_congr_ae hp hΩ hae).mp (hu.chosenWeakPartial_mem i)

theorem chosenWeakPartial'_comm_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemWkp 2 p u Ω) (i j : Fin d) :
    chosenWeakPartial' p j (chosenWeakPartial' p i u Ω) Ω =ᵐ[volume.restrict Ω]
      chosenWeakPartial' p i (chosenWeakPartial' p j u Ω) Ω := by
  have hi := (hu.chosenWeakPartial_mem i).memW1p
  have hj := (hu.chosenWeakPartial_mem j).memW1p
  exact Sobolev.ae_eq_of_weak_second_deriv_comm hΩ
    (ae_restrict_mem hΩ.measurableSet) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
    (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)
    (chosenWeakPartial'_isWeakPartial_of_mem hi j)
    (chosenWeakPartial'_isWeakPartial_of_mem hj i)
    ((chosenWeakPartial'_memLp_of_mem hi j).locallyIntegrable hp)
    ((chosenWeakPartial'_memLp_of_mem hj i).locallyIntegrable hp)

theorem memWkp_succ_of_hasWeakPartialDeriv
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemLp u p (volume.restrict Ω))
    {g : Fin d → E → ℝ} (hg : ∀ i, MemWkp k p (g i) Ω)
    (hweak : ∀ i, DeGiorgi.HasWeakPartialDeriv i (g i) u Ω) :
    MemWkp (k + 1) p u Ω := by
  have hmem : DeGiorgi.MemW1p p u Ω :=
    ⟨hu, fun i => ⟨g i, (hg i).memLp, hweak i⟩⟩
  refine ⟨hmem, ?_⟩
  intro i
  have hchosen := chosenWeakPartial'_isWeakPartial_of_mem hmem i
  have hchosenLp := chosenWeakPartial'_memLp_of_mem hmem i
  have hae := DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hchosen (hweak i)
    (hchosenLp.locallyIntegrable hp) ((hg i).memLp.locallyIntegrable hp)
  exact (MemWkp_congr_ae hp hΩ hae.symm).mp (hg i)

theorem memWkp_two_of_hasWeakPartialDeriv
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemLp u p (volume.restrict Ω))
    {g : Fin d → E → ℝ} (hg : ∀ i, DeGiorgi.MemW1p p (g i) Ω)
    (hweak : ∀ i, DeGiorgi.HasWeakPartialDeriv i (g i) u Ω) :
    MemWkp 2 p u Ω := by
  exact memWkp_succ_of_hasWeakPartialDeriv hp hΩ hu
    (fun i => MemWkp.one_iff_memW1p.mpr (hg i)) hweak

theorem ae_memWkp_two_of_hasWeakPartialDeriv
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p)
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
  have hslices {f : Z × E → ℝ} (hf : MemLp f p (μ.prod (volume.restrict Ω))) :
      ∀ᵐ t ∂μ, MemLp (fun x => f (t, x)) p (volume.restrict Ω) := by
    by_cases hptop : p = ⊤
    · subst p
      exact hf.prodMk_left_top
    · exact hf.prodMk_left hptop
  have hgLp := ae_all_iff.mpr (fun i => hslices (hg i))
  have hvLp := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k => hslices (hv i k)))
  have hfirst' := ae_all_iff.mpr hfirst
  have hsecond' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hsecond i))
  filter_upwards [hslices hu, hgLp, hvLp, hfirst', hsecond']
    with t hut hgt hvt hft hst
  apply memWkp_two_of_hasWeakPartialDeriv hp hΩ hut (g := fun i x => g i (t, x))
  · intro i
    exact ⟨hgt i, fun k => ⟨fun x => v i k (t, x), hvt i k, hst i k⟩⟩
  · exact hft

end DifferentialGeometry.Analysis.Sobolev.Euclidean
