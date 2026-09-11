import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory Set

namespace OpenPartialHomeomorph

variable {M N : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]

theorem map_symm_restrict_compl_le
    (e : OpenPartialHomeomorph M N) (mu : Measure N)
    {K : Set M} (hK : MeasurableSet K) (hKsrc : K ⊆ e.source)
    {B : Set N} (hcap : B ⊆ e '' K) :
    Measure.map e.symm (mu.restrict e.target) Kᶜ ≤ mu Bᶜ := by
  have htarget : MeasurableSet e.target := e.open_target.measurableSet
  have hinv : AEMeasurable e.symm (mu.restrict e.target) :=
    e.continuousOn_symm.aemeasurable htarget
  rw [Measure.map_apply_of_aemeasurable hinv hK.compl,
    Measure.restrict_apply' htarget]
  apply measure_mono
  rintro y ⟨hyK, _hyt⟩ hyB
  obtain ⟨x, hxK, hxy⟩ := hcap hyB
  apply hyK
  have hback : e.symm y = x := by
    rw [← hxy]
    exact e.left_inv (hKsrc hxK)
  rw [hback]
  exact hxK

theorem lintegral_map_symm_restrict_eq_sum
    {A : Type*} (e : OpenPartialHomeomorph M N) (mu : Measure N)
    (s : Finset A) (F : M → ENNReal) (G : A → M → ENNReal)
    (K : A → Set M)
    (hG : ∀ a ∈ s, Measurable (G a))
    (hsum : ∀ x, F x = ∑ a ∈ s, G a x)
    (hKsrc : ∀ a ∈ s, K a ⊆ e.source)
    (hSupp : ∀ a ∈ s, Function.support (G a) ⊆ K a)
    (hKimg : ∀ a ∈ s, MeasurableSet (e '' K a)) :
    ∫⁻ x, F x ∂Measure.map e.symm (mu.restrict e.target) =
      ∑ a ∈ s, ∫⁻ y in e '' K a, G a (e.symm y) ∂mu := by
  classical
  have hF : Measurable F := by
    have hfun : F = fun x => ∑ a ∈ s, G a x := funext hsum
    rw [hfun]
    exact Finset.measurable_sum s hG
  have htarget : MeasurableSet e.target := e.open_target.measurableSet
  have hinv : AEMeasurable e.symm (mu.restrict e.target) :=
    e.continuousOn_symm.aemeasurable htarget
  rw [MeasureTheory.lintegral_map' hF.aemeasurable hinv]
  calc
    ∫⁻ y in e.target, F (e.symm y) ∂mu =
        ∫⁻ y in e.target, ∑ a ∈ s, G a (e.symm y) ∂mu := by
      apply MeasureTheory.lintegral_congr
      intro y
      exact hsum (e.symm y)
    _ = ∑ a ∈ s, ∫⁻ y in e.target, G a (e.symm y) ∂mu := by
      rw [MeasureTheory.lintegral_finsetSum']
      intro a ha
      exact (hG a ha).aemeasurable.comp_aemeasurable hinv
    _ = ∑ a ∈ s, ∫⁻ y in e '' K a, G a (e.symm y) ∂mu := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← MeasureTheory.lintegral_indicator htarget,
        ← MeasureTheory.lintegral_indicator (hKimg a ha)]
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hyK : y ∈ e '' K a
      · have hyt : y ∈ e.target := by
          rcases hyK with ⟨x, hxK, rfl⟩
          exact e.map_source (hKsrc a ha hxK)
        simp only [Set.indicator_of_mem hyK, Set.indicator_of_mem hyt]
      · rw [Set.indicator_of_notMem hyK]
        by_cases hyt : y ∈ e.target
        · rw [Set.indicator_of_mem hyt]
          have hzero : G a (e.symm y) = 0 := by
            by_contra hne
            have hxK : e.symm y ∈ K a := hSupp a ha hne
            exact hyK ⟨e.symm y, hxK, e.right_inv hyt⟩
          exact hzero
        · rw [Set.indicator_of_notMem hyt]

end OpenPartialHomeomorph
