import DifferentialGeometry.Analysis.Calculus.Sard
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.Algebra.Support

noncomputable section

open Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem ContMDiff.sard_of_isCompact {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) {K : Set M} (hK : IsCompact K)
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (f '' {x | x ∈ K ∧ ¬ Function.Surjective (mfderiv I 𝓘(ℝ, F) f x)}) = 0 := by
  classical
  let c (p : M) := extChartAt I p
  let bad (p : M) : Set F := (f ∘ (c p).symm) ''
    {z | z ∈ (c p).target ∧ ¬ Function.Surjective (fderiv ℝ (f ∘ (c p).symm) z)}
  have hbad (p : M) : μ (bad p) = 0 := by
    have hlocal : ContDiffOn ℝ ∞ (f ∘ (c p).symm) (c p).target :=
      contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm p))
    exact hlocal.sard (isOpen_extChartAt_target p) μ
  have hcover : K ⊆ ⋃ p : M, (c p).source := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun p => (c p).source)
    (fun p => isOpen_extChartAt_source p) hcover
  have hnull : μ (⋃ p ∈ s, bad p) = 0 :=
    measure_biUnion_null_iff s.finite_toSet.countable |>.mpr (fun p _ => hbad p)
  apply measure_mono_null _ hnull
  rintro y ⟨x, ⟨hxK, hxcrit⟩, rfl⟩
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hxK)
  apply mem_iUnion₂.mpr
  refine ⟨p, hp, (c p) x, ⟨(c p).map_source hxp, ?_⟩, ?_⟩
  · intro hsurj
    have hinv : MDifferentiableAt 𝓘(ℝ, E) I (c p).symm ((c p) x) :=
      (mdifferentiableOn_extChartAt_symm (I := I) (x := p) _
        ((c p).map_source hxp)).mdifferentiableAt
          ((isOpen_extChartAt_target p).mem_nhds ((c p).map_source hxp))
    have hf' : MDifferentiableAt I 𝓘(ℝ, F) f ((c p).symm ((c p) x)) := by
      rw [(c p).left_inv hxp]
      exact hf.mdifferentiableAt (by simp)
    have heq := mfderiv_comp ((c p) x) hf' hinv
    rw [mfderiv_eq_fderiv, (c p).left_inv hxp] at heq
    rw [heq] at hsurj
    apply hxcrit
    intro v
    obtain ⟨w, hw⟩ := hsurj v
    exact ⟨mfderiv 𝓘(ℝ, E) I (c p).symm ((c p) x) w, hw⟩
  · exact congrArg f ((c p).left_inv hxp)

theorem ContMDiff.exists_regular_value_of_hasCompactSupport {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hc : HasCompactSupport f)
    {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, ∀ x : M, f x = r → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := by
  let bad : Set ℝ := f '' {x | x ∈ tsupport f ∧
    ¬ Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) f x)}
  have hnull : volume bad = 0 := hf.sard_of_isCompact hc volume
  have hnull' : volume (bad ∪ {0}) = 0 := measure_union_null hnull (measure_singleton 0)
  have hgood : ∀ᵐ r ∂volume, r ∉ bad ∪ {0} := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull'
  obtain ⟨r, hr, hreg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo a b) ≠ 0 by
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne') (ae_restrict_of_ae hgood)
  refine ⟨r, hr, ?_⟩
  intro x hxr hzero
  apply hreg
  apply Or.inl
  refine ⟨x, ⟨?_, ?_⟩, hxr⟩
  · apply subset_tsupport f
    change f x ≠ 0
    intro hx
    exact hreg (Or.inr (hxr.symm.trans hx))
  · rw [hzero]
    change ¬ Function.Surjective (0 : E →L[ℝ] ℝ)
    intro hsurj
    obtain ⟨v, hv⟩ := hsurj 1
    simp only [zero_apply, zero_ne_one] at hv
