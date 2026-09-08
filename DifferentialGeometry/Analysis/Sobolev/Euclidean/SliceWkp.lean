import DifferentialGeometry.Analysis.Integration.Lp.Product
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem wkpNorm_one_eq
    {d : ℕ} {p : ℝ≥0∞} (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    iteratedWeakSobolevNorm 1 p u Ω = eLpNorm u p (volume.restrict Ω) +
      ∑ a : Fin 1 → Fin d, eLpNorm (chosenWeakPartial' p (a 0) u Ω) p (volume.restrict Ω) := by
  classical
  unfold iteratedWeakSobolevNorm
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h0_unique : ∀ a : Fin 0 → Fin d, a = (fun i : Fin 0 => i.elim0) :=
    fun a => by funext i; exact i.elim0
  have : Unique (Fin 0 → Fin d) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun a => (h0_unique a).symm ▸ rfl }
  rw [Fintype.sum_unique
    (f := fun a : Fin 0 → Fin d => eLpNorm (iterWeakPartial p 0 a u Ω) p
      (volume.restrict Ω))]
  simp only [iterWeakPartial_zero, iterWeakPartial_succ]

theorem ae_memWkp_one_and_memLp_wkpNorm_of_weak_partials
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {V : Z × EuclideanSpace ℝ (Fin d) → ℝ}
    {W : Fin d → Z × EuclideanSpace ℝ (Fin d) → ℝ}
    (hV : MemLp V p (μ.prod (volume.restrict Ω)))
    (hW : ∀ i, MemLp (W i) p (μ.prod (volume.restrict Ω)))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => W i (t, z)) (fun z => V (t, z)) Ω) :
    (∀ᵐ t ∂μ, MemWkp 1 p (fun z => V (t, z)) Ω) ∧
    MemLp (fun t => (iteratedWeakSobolevNorm 1 p (fun z => V (t,z)) Ω).toReal) p μ := by
  classical
  have hslice : ∀ᵐ t ∂μ, MemLp (fun z => V (t,z)) p (volume.restrict Ω) ∧
      ∀ i, MemLp (fun z => W i (t,z)) p (volume.restrict Ω) ∧
        DeGiorgi.HasWeakPartialDeriv i (fun z => W i (t,z)) (fun z => V (t,z)) Ω := by
    filter_upwards [hV.prodMk_left hpt,
      ae_all_iff.mpr (fun i => (hW i).prodMk_left hpt), ae_all_iff.mpr hweak] with t ht hwt hweak
    exact ⟨ht, fun i => ⟨hwt i, hweak i⟩⟩
  have hmem : ∀ᵐ t ∂μ, MemWkp 1 p (fun z => V (t,z)) Ω := by
    filter_upwards [hslice] with t ht
    apply MemWkp.one_iff_memW1p.mpr
    exact ⟨ht.1, fun i => ⟨fun z => W i (t,z), (ht.2 i).1, (ht.2 i).2⟩⟩
  refine ⟨hmem, ?_⟩
  have heq : (fun t => (iteratedWeakSobolevNorm 1 p (fun z => V (t,z)) Ω).toReal) =ᵐ[μ]
      fun t => (eLpNorm (fun z => V (t,z)) p (volume.restrict Ω)).toReal +
        ∑ a : Fin 1 → Fin d,
          (eLpNorm (fun z => W (a 0) (t,z)) p (volume.restrict Ω)).toReal := by
    filter_upwards [hslice, hmem] with t ht hmt
    have he (i : Fin d) : chosenWeakPartial' p i (fun z => V (t,z)) Ω =ᵐ[volume.restrict Ω]
        fun z => W i (t,z) :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
        (chosenWeakPartial'_isWeakPartial_of_mem hmt.memW1p i) (ht.2 i).2
        ((chosenWeakPartial'_memLp_of_mem hmt.memW1p i).locallyIntegrable hp)
        ((ht.2 i).1.locallyIntegrable hp)
    rw [wkpNorm_one_eq]
    simp_rw [eLpNorm_congr_ae (he _)]
    rw [ENNReal.toReal_add ht.1.2.ne (ENNReal.sum_ne_top.mpr fun a _ => (ht.2 (a 0)).1.2.ne),
      ENNReal.toReal_sum (fun a _ => (ht.2 (a 0)).1.2.ne)]
  have hb : MemLp (fun t => (eLpNorm (fun z => V (t,z)) p (volume.restrict Ω)).toReal +
        ∑ a : Fin 1 → Fin d,
          (eLpNorm (fun z => W (a 0) (t,z)) p (volume.restrict Ω)).toReal) p μ :=
    (hV.eLpNorm_toReal hpt).add
      (memLp_finsetSum _ fun a _ => (hW (a 0)).eLpNorm_toReal hpt)
  have hmL : AEStronglyMeasurable (fun t => (iteratedWeakSobolevNorm 1 p (fun z => V (t,z)) Ω).toReal) μ :=
    hb.1.congr heq.symm
  apply hb.of_le hmL
  filter_upwards [heq] with t ht
  rw [ht]

end DifferentialGeometry.Analysis.Sobolev.Euclidean
