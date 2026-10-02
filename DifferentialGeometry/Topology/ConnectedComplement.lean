import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology

universe u v

theorem isPreconnected_compl_iUnion_of_collar {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {ι : Type*} [Finite ι] (K V : ι → Set X)
    (hKcl : ∀ i, IsClosed (K i)) (hVop : ∀ i, IsOpen (V i)) (hKV : ∀ i, K i ⊆ V i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (K j))
    (hconn : ∀ i, IsConnected (V i \ K i)) :
    IsPreconnected ((⋃ i, K i)ᶜ : Set X) := by
  classical
  have hKcl' : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hKcl
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hsub (i : ι) : V i \ K i ⊆ (⋃ j, K j)ᶜ := by
    intro z hz
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro j hj
    by_cases hji : j = i
    · exact hz.2 (hji ▸ hj)
    · exact (Set.disjoint_left.mp (hdisj i j (fun hij => hji hij.symm)) hz.1) hj
  have hconst (i : ι) : ∃ c : Bool, ∀ z ∈ V i \ K i, f z = c := by
    obtain ⟨z0, hz0⟩ := (hconn i).nonempty
    exact ⟨f z0, fun z hz => (hconn i).isPreconnected.constant
      (hf.mono (hsub i)) hz hz0⟩
  choose c hc using hconst
  have hKdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j) := fun i j hij =>
    (hdisj i j hij).mono_left (hKV i)
  let g : X → Bool := fun z =>
    if hz : z ∈ ⋃ i, K i then c (Classical.choose (mem_iUnion.mp hz)) else f z
  have hgK : ∀ i, ∀ z ∈ K i, g z = c i := by
    intro i z hz
    have hzU : z ∈ ⋃ i, K i := mem_iUnion.mpr ⟨i, hz⟩
    have hspec : z ∈ K (Classical.choose (mem_iUnion.mp hzU)) :=
      Classical.choose_spec (mem_iUnion.mp hzU)
    have hidx : Classical.choose (mem_iUnion.mp hzU) = i := by
      by_contra hne
      exact (Set.disjoint_left.mp (hKdisj _ i hne) hspec) hz
    simp only [g, dite_eq_left hzU, hidx]
  have hgCompl : ∀ z, z ∉ ⋃ i, K i → g z = f z := by
    intro z hz
    simp only [g, dite_eq_right hz]
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ ⋃ i, K i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      refine (continuousAt_const (y := c i)).congr ?_
      filter_upwards [hVop i |>.mem_nhds (hKV i hi)] with w hw
      by_cases hwU : w ∈ ⋃ j, K j
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hwU
        by_cases hji : j = i
        · rw [hji] at hj
          rw [hgK i w hj]
        · exact absurd hj (Set.disjoint_left.mp (hdisj i j (fun hij => hji hij.symm)) hw)
      · rw [hgCompl w hwU]
        exact (hc i w ⟨hw, fun hwk => hwU (mem_iUnion.mpr ⟨i, hwk⟩)⟩).symm
    · refine ((hf z hz).continuousAt (hKcl'.isOpen_compl.mem_nhds hz)).congr ?_
      filter_upwards [hKcl'.isOpen_compl.mem_nhds hz] with w hw
      exact (hgCompl w hw).symm
  have hxy := IsPreconnected.constant isPreconnected_univ hgcont.continuousOn
    (mem_univ x) (mem_univ y)
  rw [hgCompl x hx, hgCompl y hy] at hxy
  exact hxy

end DifferentialGeometry.Topology
