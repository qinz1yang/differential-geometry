import Mathlib.Topology.Connected.Basic
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas

open Set

namespace DifferentialGeometry.Topology

theorem isConnected_interior_union {X : Type*} [TopologicalSpace X] {S T : Set X}
    (hS : S ⊆ closure (interior S)) (hT : T ⊆ closure (interior T))
    (hconnS : IsPreconnected (interior S)) (hconnT : IsPreconnected (interior T))
    (hmeet : (closure (interior S) ∩ closure (interior T) ∩ interior (S ∪ T)).Nonempty) :
    IsConnected (interior (S ∪ T)) := by
  obtain ⟨p, ⟨hpS, hpT⟩, hp⟩ := hmeet
  have hSp : IsPreconnected (insert p (interior S)) :=
    hconnS.subset_closure (subset_insert p _) (insert_subset hpS subset_closure)
  have hTp : IsPreconnected (insert p (interior T)) :=
    hconnT.subset_closure (subset_insert p _) (insert_subset hpT subset_closure)
  have hconn : IsPreconnected (insert p (interior S) ∪ insert p (interior T)) :=
    hSp.union p (mem_insert p _) (mem_insert p _) hTp
  refine ⟨⟨p, hp⟩, hconn.subset_closure ?_ ?_⟩
  · apply union_subset
    · exact insert_subset hp (interior_mono subset_union_left)
    · exact insert_subset hp (interior_mono subset_union_right)
  · apply interior_subset.trans
    apply union_subset
    · exact hS.trans (closure_mono ((subset_insert p _).trans subset_union_left))
    · exact hT.trans (closure_mono ((subset_insert p _).trans subset_union_right))

variable {N M : Type*} [TopologicalSpace N] [ConnectedSpace N]
  [TopologicalSpace M]

theorem isConnected_interior_union_of_collar
    (A : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a < b)
    (hsource : univ ×ˢ Icc a b ⊆ A.source) {W : Set M}
    (hW : W ⊆ closure (interior W))
    (hWconn : IsPreconnected (interior W))
    (hfill : A '' (univ ×ˢ ({a} : Set ℝ)) ⊆
      interior (W ∪ A '' (univ ×ˢ Icc a b))) :
    IsConnected (interior (W ∪ A '' (univ ×ˢ Icc a b))) := by
  let B := A '' (univ ×ˢ Icc a b)
  have hBint : interior B = A '' (univ ×ˢ Ioo a b) := by
    rw [← A.image_interior_of_subset_source hsource, interior_prod_eq,
      interior_univ, interior_Icc]
  have hBreg : B ⊆ closure (interior B) := by
    have hclosure : closure (univ ×ˢ Ioo a b : Set (N × ℝ)) = univ ×ˢ Icc a b := by
      rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
    have hc : ContinuousOn A (closure (univ ×ˢ Ioo a b)) := by
      rw [hclosure]
      exact A.continuousOn.mono hsource
    simpa only [hclosure, ← hBint] using hc.image_closure
  have hBconn : IsPreconnected (interior B) := by
    rw [hBint]
    exact (isPreconnected_univ.prod isPreconnected_Ioo).image _
      (A.continuousOn.mono ((prod_mono Subset.rfl Ioo_subset_Icc_self).trans hsource))
  obtain ⟨q⟩ := (inferInstance : Nonempty N)
  have hp : A (q, a) ∈ A '' (univ ×ˢ ({a} : Set ℝ)) :=
    ⟨(q, a), ⟨mem_univ _, rfl⟩, rfl⟩
  let p := A (q, a)
  have hpnotint : p ∉ interior B := by
    rw [hBint]
    rintro ⟨⟨r, t⟩, ⟨_, ht⟩, he⟩
    have hqa := hsource (show (q, a) ∈ univ ×ˢ Icc a b from ⟨mem_univ _, le_rfl, hab.le⟩)
    have hrt := hsource (show (r, t) ∈ univ ×ˢ Icc a b from
      ⟨mem_univ _, ht.1.le, ht.2.le⟩)
    have hta : t = a := congrArg Prod.snd (A.injOn hrt hqa he)
    exact ht.1.ne hta.symm
  have hpS : p ∈ closure (interior W) := by
    have hpclosure : p ∈ closure W := by
      by_contra hpW
      exact hpnotint (interior_union_inter_interior_compl_left_subset
        ⟨hfill hp, (show p ∈ interior Wᶜ by simpa only [interior_compl, mem_compl_iff] using hpW)⟩)
    simpa only [closure_closure] using closure_mono hW hpclosure
  have hpT : p ∈ B := by
    rcases hp with ⟨q, hq, hqp⟩
    exact ⟨q, (prod_mono Subset.rfl (by
      intro t ht
      have ht' : t = a := ht
      subst ht'
      exact ⟨le_rfl, hab.le⟩)) hq, hqp⟩
  exact isConnected_interior_union hW hBreg hWconn hBconn ⟨p, ⟨hpS, hBreg hpT⟩, hfill hp⟩

end DifferentialGeometry.Topology
