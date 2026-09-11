import DifferentialGeometry.Analysis.Integration.Lp.Product
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.WeakPartial
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem wkpNorm_one_eq
    {d : ℕ} {p : ℝ≥0∞} (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    iteratedWeakSobolevNorm 1 p u Ω = eLpNorm u p (volume.restrict Ω) +
      ∑ a : Fin 1 → Fin d, eLpNorm (chosenWeakPartialOrZero p (a 0) u Ω) p (volume.restrict Ω) := by
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
    MemLp (fun t => (iteratedWeakSobolevNorm 1 p (fun z => V (t, z)) Ω).toReal) p μ := by
  classical
  have hslice : ∀ᵐ t ∂μ, MemLp (fun z => V (t, z)) p (volume.restrict Ω) ∧
      ∀ i, MemLp (fun z => W i (t, z)) p (volume.restrict Ω) ∧
        DeGiorgi.HasWeakPartialDeriv i (fun z => W i (t, z)) (fun z => V (t, z)) Ω := by
    filter_upwards [hV.prodMk_left hpt,
      ae_all_iff.mpr (fun i => (hW i).prodMk_left hpt), ae_all_iff.mpr hweak] with t ht hwt hweak
    exact ⟨ht, fun i => ⟨hwt i, hweak i⟩⟩
  have hmem : ∀ᵐ t ∂μ, MemWkp 1 p (fun z => V (t, z)) Ω := by
    filter_upwards [hslice] with t ht
    apply MemWkp.one_iff_memW1p.mpr
    exact ⟨ht.1, fun i => ⟨fun z => W i (t, z), (ht.2 i).1, (ht.2 i).2⟩⟩
  refine ⟨hmem, ?_⟩
  have heq : (fun t => (iteratedWeakSobolevNorm 1 p (fun z => V (t, z)) Ω).toReal) =ᵐ[μ]
      fun t => (eLpNorm (fun z => V (t, z)) p (volume.restrict Ω)).toReal +
        ∑ a : Fin 1 → Fin d,
          (eLpNorm (fun z => W (a 0) (t, z)) p (volume.restrict Ω)).toReal := by
    filter_upwards [hslice, hmem] with t ht hmt
    have he (i : Fin d) : chosenWeakPartialOrZero p i (fun z => V (t, z)) Ω =ᵐ[volume.restrict Ω]
        fun z => W i (t, z) :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
        (chosenWeakPartialOrZero_isWeakPartial_of_mem hmt.memW1p i) (ht.2 i).2
        ((chosenWeakPartialOrZero_memLp_of_mem hmt.memW1p i).locallyIntegrable hp)
        ((ht.2 i).1.locallyIntegrable hp)
    rw [wkpNorm_one_eq]
    simp_rw [eLpNorm_congr_ae (he _)]
    rw [ENNReal.toReal_add ht.1.2.ne (ENNReal.sum_ne_top.mpr fun a _ => (ht.2 (a 0)).1.2.ne),
      ENNReal.toReal_sum (fun a _ => (ht.2 (a 0)).1.2.ne)]
  have hb : MemLp (fun t => (eLpNorm (fun z => V (t, z)) p (volume.restrict Ω)).toReal +
        ∑ a : Fin 1 → Fin d,
          (eLpNorm (fun z => W (a 0) (t, z)) p (volume.restrict Ω)).toReal) p μ :=
    (hV.eLpNorm_toReal hpt).add
      (memLp_finsetSum _ fun a _ => (hW (a 0)).eLpNorm_toReal hpt)
  have hmL : AEStronglyMeasurable (fun t => (iteratedWeakSobolevNorm 1 p (fun z => V (t, z)) Ω).toReal) μ :=
    hb.1.congr heq.symm
  apply hb.of_le hmL
  filter_upwards [heq] with t ht
  rw [ht]

theorem ae_memWkp_one_and_memLp_wkpNorm_of_lp_weak_partials
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (P : Lp (Lp ℝ 2 (volume.restrict Ω)) 2 μ)
    (W : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => W i (t, z)) (P t : EuclideanSpace ℝ (Fin d) → ℝ) Ω) :
    (∀ᵐ t ∂μ, MemWkp 1 2 (P t) Ω) ∧
      MemLp (fun t => (iteratedWeakSobolevNorm 1 2 (P t) Ω).toReal) 2 μ := by
  let U := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P
  have hUeq : ∀ᵐ t ∂μ, (fun z => U (t, z)) =ᵐ[volume.restrict Ω] (P t : EuclideanSpace ℝ (Fin d) → ℝ) :=
    Lp.uncurry_coeFn (by norm_num) P
  have hweakU : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => W i (t, z)) (fun z => U (t, z)) Ω := by
    intro i
    filter_upwards [hweak i, hUeq] with t ht he
    intro ψ hψ hψc hψs
    have htest := ht ψ hψ hψc hψs
    have heint : (∫ z in Ω, U (t, z) * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        ∫ z in Ω, P t z * fderiv ℝ ψ z (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      rw [hz]
    exact heint.trans htest
  obtain ⟨hmU, hnU⟩ := ae_memWkp_one_and_memLp_wkpNorm_of_weak_partials
    hΩ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) (Lp.memLp U)
    (fun i => Lp.memLp (W i)) hweakU
  have hmP : ∀ᵐ t ∂μ, MemWkp 1 2 (P t) Ω := by
    filter_upwards [hmU, hUeq] with t ht he
    exact (MemWkp_congr_ae (by norm_num) hΩ he).mp ht
  have hnP : MemLp (fun t => (iteratedWeakSobolevNorm 1 2 (P t) Ω).toReal) 2 μ := by
    have he : (fun t => (iteratedWeakSobolevNorm 1 2 (fun z => U (t, z)) Ω).toReal) =ᵐ[μ]
        fun t => (iteratedWeakSobolevNorm 1 2 (P t) Ω).toReal := by
      filter_upwards [hUeq] with t ht
      apply congrArg ENNReal.toReal
      exact wkpNorm_congr_ae (by norm_num) hΩ ht
    exact ⟨hnU.1.congr he, (eLpNorm_congr_ae he).symm.trans_lt hnU.2⟩
  exact ⟨hmP, hnP⟩

theorem ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {V : Z × EuclideanSpace ℝ (Fin d) → ℝ}
    {W : Fin d → Z × EuclideanSpace ℝ (Fin d) → ℝ}
    (hV : MemLp V p (μ.prod (volume.restrict Ω)))
    (hW : ∀ i, ∀ᵐ t ∂μ, MemWkp m p (fun z => W i (t, z)) Ω)
    (hWnorm : ∀ i, MemLp
      (fun t => (iteratedWeakSobolevNorm m p (fun z => W i (t, z)) Ω).toReal) p μ)
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => W i (t, z)) (fun z => V (t, z)) Ω) :
    (∀ᵐ t ∂μ, MemWkp (m + 1) p (fun z => V (t, z)) Ω) ∧
      MemLp (fun t => (iteratedWeakSobolevNorm (m + 1) p
        (fun z => V (t, z)) Ω).toReal) p μ := by
  classical
  have hslice := hV.prodMk_left hpt
  have hWall := ae_all_iff.mpr hW
  have hweakall := ae_all_iff.mpr hweak
  have hmem : ∀ᵐ t ∂μ, MemWkp (m + 1) p (fun z => V (t, z)) Ω := by
    filter_upwards [hslice, hWall, hweakall] with t ht hwt hweak
    exact memWkp_succ_of_hasWeakPartialDeriv hp hΩ ht hwt hweak
  refine ⟨hmem, ?_⟩
  have heq : (fun t => (iteratedWeakSobolevNorm (m + 1) p
      (fun z => V (t, z)) Ω).toReal) =ᵐ[μ]
      fun t => (eLpNorm (fun z => V (t, z)) p (volume.restrict Ω)).toReal +
        ∑ i : Fin d, (iteratedWeakSobolevNorm m p (fun z => W i (t, z)) Ω).toReal := by
    filter_upwards [hslice, hWall, hweakall, hmem] with t ht hwt hweak hmt
    have he (i : Fin d) : chosenWeakPartialOrZero p i (fun z => V (t, z)) Ω =ᵐ[volume.restrict Ω]
        fun z => W i (t, z) :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
        (chosenWeakPartialOrZero_isWeakPartial_of_mem hmt.memW1p i) (hweak i)
        ((chosenWeakPartialOrZero_memLp_of_mem hmt.memW1p i).locallyIntegrable hp)
        ((hwt i).memLp.locallyIntegrable hp)
    rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial]
    simp_rw [wkpNorm_congr_ae hp hΩ (he _)]
    rw [ENNReal.toReal_add ht.2.ne
      (ENNReal.sum_ne_top.mpr fun i _ => (wkpNorm_lt_top_of_memWkp (hwt i)).ne),
      ENNReal.toReal_sum (fun i _ => (wkpNorm_lt_top_of_memWkp (hwt i)).ne)]
  have hb := (hV.eLpNorm_toReal hpt).add
    (memLp_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hWnorm i)
  exact ⟨hb.1.congr heq.symm, (eLpNorm_congr_ae heq).trans_lt hb.2⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean
