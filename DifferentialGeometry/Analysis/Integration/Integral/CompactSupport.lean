import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

open Set

namespace MeasureTheory

variable {X E 𝕜 : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {μ : Measure X} {Ω : Set X}

theorem LocallyIntegrableOn.integrable_smul_left_of_hasCompactSupport
    {f : X → E} (hf : LocallyIntegrableOn f Ω μ) {g : X → 𝕜}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    Integrable (fun x => g x • f x) μ := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((subset_tsupport (fun x => g x • f x)).trans (tsupport_smul_subset_left g f))).mp
  exact (hf.integrableOn_compact_subset hgs hgc).smul_of_top_right
    (hg.memLp_top_of_hasCompactSupport hgc (μ.restrict (tsupport g)))

theorem LocallyIntegrableOn.integrable_smul_right_of_hasCompactSupport
    {f : X → 𝕜} (hf : LocallyIntegrableOn f Ω μ) {g : X → E}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    Integrable (fun x => f x • g x) μ := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((subset_tsupport (fun x => f x • g x)).trans (tsupport_smul_subset_right f g))).mp
  exact (hf.integrableOn_compact_subset hgs hgc).smul_of_top_left
    (hg.memLp_top_of_hasCompactSupport hgc (μ.restrict (tsupport g)))

end MeasureTheory
