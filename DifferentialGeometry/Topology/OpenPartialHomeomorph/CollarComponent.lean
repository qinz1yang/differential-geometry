import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace Y]

theorem image_closed_slab_subset_connectedComponentIn_closed_exterior
    (A : OpenPartialHomeomorph (X × ℝ) Y) {a b : ℝ} (hab : a < b)
    (hsource : univ ×ˢ Icc a b ⊆ A.source) {W₀ W : Set Y}
    (hW : W₀ ⊆ W)
    (hinter : (A '' (univ ×ˢ Icc a b)) ∩ W ⊆ A '' (univ ×ˢ ({a} : Set ℝ)))
    {x : Y}
    (hmeet : (A '' (univ ×ˢ ({a} : Set ℝ)) ∩
      connectedComponentIn (interior W₀)ᶜ x).Nonempty) :
    A '' (univ ×ˢ Icc a b) ⊆ connectedComponentIn (interior W₀)ᶜ x := by
  let B := A '' (univ ×ˢ Icc a b)
  have hBinterior : interior B = A '' (univ ×ˢ Ioo a b) := by
    rw [← A.image_interior_of_subset_source hsource, interior_prod_eq,
      interior_univ, interior_Icc]
  have hdense : B ⊆ closure (interior B) := by
    rw [hBinterior]
    have hclosure : closure (univ ×ˢ Ioo a b : Set (X × ℝ)) = univ ×ˢ Icc a b := by
      rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
    have hc : ContinuousOn A (closure (univ ×ˢ Ioo a b)) := by
      rw [hclosure]
      exact A.continuousOn.mono hsource
    simpa only [hclosure] using hc.image_closure
  have hdisj : Disjoint (interior B) (interior W) := by
    refine disjoint_left.mpr ?_
    intro y hyB hyW
    have hyface := hinter ⟨interior_subset hyB, interior_subset hyW⟩
    rw [hBinterior] at hyB
    obtain ⟨⟨q, t⟩, hqt, hqy⟩ := hyB
    obtain ⟨⟨r, s⟩, hrs, hry⟩ := hyface
    have hs : s = a := hrs.2
    have heq := A.injOn (hsource ⟨hqt.1, hqt.2.1.le, hqt.2.2.le⟩)
      (hsource ⟨hrs.1, by rw [hs]; exact ⟨le_rfl, hab.le⟩⟩) (hqy.trans hry.symm)
    have hts : t = s := congrArg Prod.snd heq
    exact (ne_of_gt hqt.2.1) (hts.trans hs)
  have hBexterior : B ⊆ (interior W₀)ᶜ :=
    hdense.trans ((hdisj.closure_left isOpen_interior).subset_compl_right.trans
      (compl_subset_compl.mpr (interior_mono hW)))
  have hBconnected : IsPreconnected B :=
    (isPreconnected_univ.prod isPreconnected_Icc).image A (A.continuousOn.mono hsource)
  obtain ⟨y, hyface, hycomponent⟩ := hmeet
  have hyB : y ∈ B := by
    apply image_mono (prod_mono Subset.rfl (show ({a} : Set ℝ) ⊆ Icc a b from ?_)) hyface
    exact singleton_subset_iff.mpr ⟨le_rfl, hab.le⟩
  rw [connectedComponentIn_eq hycomponent]
  exact hBconnected.subset_connectedComponentIn hyB hBexterior

end OpenPartialHomeomorph
