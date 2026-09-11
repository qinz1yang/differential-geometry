import DifferentialGeometry.Topology.Compactness.ProductChartThickening
import DifferentialGeometry.Topology.Connected.FiniteChain
import DifferentialGeometry.Topology.VanKampen.DisjointSimplyConnectedCover
import Mathlib.Topology.Connected.LocallyPathConnected

noncomputable section

open Set

namespace DifferentialGeometry.Topology.VanKampen

theorem exists_open_torsionFree_neighborhood_of_cylindrical_chain
    {S M : Type*} [TopologicalSpace S] [CompactSpace S] [SimplyConnectedSpace S]
    [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M] {n : ℕ}
    (e : Fin (n + 1) → OpenPartialHomeomorph (S × ℝ) M)
    (a b : Fin (n + 1) → ℝ) (hab : ∀ i, a i ≤ b i)
    (hsource : ∀ i, (univ : Set S) ×ˢ Icc (a i) (b i) ⊆ (e i).source)
    (hmeet : ∀ i : Fin n,
      (e i.castSucc '' ((univ : Set S) ×ˢ Icc (a i.castSucc) (b i.castSucc)) ∩
        e i.succ '' ((univ : Set S) ×ˢ Icc (a i.succ) (b i.succ))).Nonempty)
    (hd : ∀ i j, i.val + 1 < j.val → Disjoint
      (e i '' ((univ : Set S) ×ˢ Icc (a i) (b i)))
      (e j '' ((univ : Set S) ×ˢ Icc (a j) (b j)))) :
    ∃ U : Set M, IsOpen U ∧
      (⋃ i, e i '' ((univ : Set S) ×ˢ Icc (a i) (b i))) ⊆ U ∧
      PathConnectedSpace U ∧ ∀ x₀ : U, IsMulTorsionFree (FundamentalGroup U x₀) := by
  obtain ⟨a', b', hends, hsrc, hdisj⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_bands_preserving_disjointness
      e a b hab hsource (fun i j ↦ i.val + 1 < j.val) hd
  let V (i : Fin (n + 1)) := e i '' ((univ : Set S) ×ˢ Ioo (a' i) (b' i))
  have hV (i : Fin (n + 1)) : IsOpen (V i) :=
    (e i).isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) (hsrc i)
  have hsmall (i : Fin (n + 1)) :
      e i '' ((univ : Set S) ×ˢ Icc (a i) (b i)) ⊆ V i := by
    apply image_mono
    intro x hx
    exact ⟨hx.1, (hends i).1.trans_le hx.2.1, hx.2.2.trans_lt (hends i).2⟩
  have hsc (i : Fin (n + 1)) : SimplyConnectedSpace (V i) :=
    DifferentialGeometry.Topology.Compactness.simplyConnectedSpace_product_chart_band
      (e i) ((hends i).1.trans_le ((hab i).trans (hends i).2.le)) (hsrc i)
  have hconn (i : Fin (n + 1)) : IsConnected (V i) := by
    let _ := hsc i
    exact isConnected_iff_connectedSpace.mpr inferInstance
  have hopen : IsOpen (⋃ i, V i) := isOpen_iUnion hV
  have hconnected : IsConnected (⋃ i, V i) :=
    DifferentialGeometry.Topology.isConnected_iUnion_of_finite_chain V hconn
      (fun i ↦ (hmeet i).mono (inter_subset_inter (hsmall i.castSucc) (hsmall i.succ)))
  let _ : PathConnectedSpace (↑(⋃ i, V i)) :=
    isPathConnected_iff_pathConnectedSpace.mp (hopen.isConnected_iff_isPathConnected.mp hconnected)
  refine ⟨⋃ i, V i, hopen, iUnion_mono hsmall, inferInstance, fun x₀ ↦ ?_⟩
  exact isMulTorsionFree_fundamentalGroup_iUnion_of_open_chain V hV hsc hdisj x₀

end DifferentialGeometry.Topology.VanKampen
