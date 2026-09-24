import DifferentialGeometry.Topology.LocalLipschitzVariation
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option autoImplicit false
open Set
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

theorem lipschitzOnWith_comp_of_locally_lipschitzOn
    {f : X → Y} {gamma : ℝ → X} {a b : ℝ} {C L : ℝ≥0}
    (hgamma : LipschitzOnWith C gamma (Icc a b))
    (hf : ∀ x ∈ gamma '' Icc a b, ∃ s ∈ 𝓝 x, LipschitzOnWith L f s) :
    LipschitzOnWith (L * C) (f ∘ gamma) (Icc a b) := by
  have hbound (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b)
      (hst : s ≤ t) : edist (f (gamma s)) (f (gamma t)) ≤
        ((L * C : ℝ≥0) : ℝ≥0∞) * edist s t := by
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hvar := eVariationOn_comp_le_of_locally_lipschitzOn
      (hgamma.continuousOn.mono hsub)
      (fun x hx => hf x ((image_mono hsub) hx))
    have hgammaVar : eVariationOn gamma (Icc s t) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (t - s) := by
      simpa only [Function.comp_id, eVariationOn_id_Icc] using
        (hgamma.mono hsub).comp_eVariationOn_le (mapsTo_id (Icc s t))
    have hdist : edist s t = ENNReal.ofReal (t - s) := by
      rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    calc
      edist (f (gamma s)) (f (gamma t)) ≤ eVariationOn (f ∘ gamma) (Icc s t) :=
        eVariationOn.edist_le _ ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩
      _ ≤ (L : ℝ≥0∞) * eVariationOn gamma (Icc s t) := hvar
      _ ≤ (L : ℝ≥0∞) * ((C : ℝ≥0∞) * ENNReal.ofReal (t - s)) :=
        mul_le_mul_right hgammaVar _
      _ = ((L * C : ℝ≥0) : ℝ≥0∞) * edist s t := by
        rw [ENNReal.coe_mul, hdist, mul_assoc]
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hbound s hs t ht hst
  · simpa only [edist_comm, Function.comp_apply] using hbound t ht s hs hts

end DifferentialGeometry.Topology
