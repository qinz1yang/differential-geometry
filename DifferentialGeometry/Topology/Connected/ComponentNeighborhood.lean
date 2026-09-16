import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.NhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem local_component_closure_neighborhood {N S C : Set X} {a b p x y : X}
    (hN : IsClosed N) (hCN : C ⊆ N) (hC : C ∈ 𝓝[N] p) (hp : p ∈ S)
    (hdis : Disjoint (connectedComponentIn (N \ S) a) (connectedComponentIn (N \ S) b))
    (hmeet : closure (connectedComponentIn (N \ S) a) ∩
      closure (connectedComponentIn (N \ S) b) = S)
    (hcover : connectedComponentIn (C \ S) x ∪ connectedComponentIn (C \ S) y = C \ S)
    (hlocal : closure (connectedComponentIn (C \ S) x) ∩
      closure (connectedComponentIn (C \ S) y) = C ∩ S) :
    (closure (connectedComponentIn (C \ S) x) ⊆ closure (connectedComponentIn (N \ S) a) ∧
      closure (connectedComponentIn (C \ S) x) ∈ 𝓝[closure (connectedComponentIn (N \ S) a)] p) ∨
    (closure (connectedComponentIn (C \ S) y) ⊆ closure (connectedComponentIn (N \ S) a) ∧
      closure (connectedComponentIn (C \ S) y) ∈ 𝓝[closure (connectedComponentIn (N \ S) a)] p) := by
  let A := connectedComponentIn (N \ S) a
  let B := connectedComponentIn (N \ S) b
  let D := connectedComponentIn (C \ S) x
  let F := connectedComponentIn (C \ S) y
  have hAN : A ⊆ N := (connectedComponentIn_subset (N \ S) a).trans sdiff_subset
  have hBN : B ⊆ N := (connectedComponentIn_subset (N \ S) b).trans sdiff_subset
  have hpA : p ∈ closure A := (hmeet.symm.subset hp).1
  have hpB : p ∈ closure B := (hmeet.symm.subset hp).2
  obtain ⟨O, hO, hpO, hOC⟩ := mem_nhdsWithin.mp hC
  obtain ⟨u, huO, huA⟩ := mem_closure_iff.mp hpA O hO hpO
  obtain ⟨v, hvO, hvB⟩ := mem_closure_iff.mp hpB O hO hpO
  have hu : u ∈ D ∪ F := hcover.symm.subset
    ⟨hOC ⟨huO, hAN huA⟩, (connectedComponentIn_subset (N \ S) a huA).2⟩
  have hv : v ∈ D ∪ F := hcover.symm.subset
    ⟨hOC ⟨hvO, hBN hvB⟩, (connectedComponentIn_subset (N \ S) b hvB).2⟩
  have hsub (i j z : X) (hz : z ∈ connectedComponentIn (C \ S) i)
      (hz' : z ∈ connectedComponentIn (N \ S) j) :
      connectedComponentIn (C \ S) i ⊆ connectedComponentIn (N \ S) j := by
    have h : connectedComponentIn (C \ S) i ⊆ connectedComponentIn (N \ S) z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hz
        ((connectedComponentIn_subset (C \ S) i).trans (fun _ hw => ⟨hCN hw.1, hw.2⟩))
    rwa [← connectedComponentIn_eq hz'] at h
  have hfinish (P Q : Set X) (hPQ : P ∪ Q = C \ S)
      (hPQcl : closure P ∩ closure Q = C ∩ S) (hPA : P ⊆ A) (hQB : Q ⊆ B) :
      closure P ⊆ closure A ∧ closure P ∈ 𝓝[closure A] p := by
    refine ⟨closure_mono hPA, ?_⟩
    have hCrel : C ∈ 𝓝[closure A] p := nhdsWithin_mono p (closure_minimal hAN hN) hC
    apply Filter.mem_of_superset (Filter.inter_mem hCrel self_mem_nhdsWithin)
    rintro z ⟨hzC, hzA⟩
    by_cases hzS : z ∈ S
    · exact (hPQcl.symm.subset ⟨hzC, hzS⟩).1
    · rcases hPQ.symm.subset ⟨hzC, hzS⟩ with hzP | hzQ
      · exact subset_closure hzP
      · exact (hzS (hmeet.subset ⟨hzA, subset_closure (hQB hzQ)⟩)).elim
  rcases hu with huD | huF
  · have hDA : D ⊆ A := hsub x a u huD huA
    have hvF : v ∈ F := hv.resolve_left fun hvD => disjoint_left.mp hdis (hDA hvD) hvB
    exact Or.inl (hfinish D F hcover hlocal hDA (hsub y b v hvF hvB))
  · have hFA : F ⊆ A := hsub y a u huF huA
    have hvD : v ∈ D := hv.resolve_right fun hvF => disjoint_left.mp hdis (hFA hvF) hvB
    exact Or.inr (hfinish F D (by rwa [union_comm]) (by rwa [inter_comm]) hFA
      (hsub x b v hvD hvB))

end DifferentialGeometry.Topology
