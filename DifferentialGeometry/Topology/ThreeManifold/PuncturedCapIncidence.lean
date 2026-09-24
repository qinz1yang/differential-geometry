import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCapCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandFrontier
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.LocallyFinite.Frontier

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]
  (T : TubeSystem M)

private theorem frontier_punctured_subset {Ω : Set M}
    (s : Finset T.Boundary) (B : T.Boundary → PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M ∞)
    (hB : ∀ b ∈ s, closedBall (0 : ThreeSpace) 1 ⊆ (B b).source) :
    frontier (Ω \ ⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1) ⊆
      frontier Ω ∪ ⋃ b ∈ s, B b '' sphere (0 : ThreeSpace) 1 := by
  have hfr : frontier (⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1) ⊆
      ⋃ b ∈ s, B b '' sphere (0 : ThreeSpace) 1 := by
    have hh := (locallyFinite_of_finite
      (fun b : {b // b ∈ s} => B b.val '' ball (0 : ThreeSpace) 1)).frontier_iUnion_subset
    intro y hy
    have hy' : y ∈ frontier (⋃ b : {b // b ∈ s}, B b.val '' ball (0 : ThreeSpace) 1) := by
      simpa only [iUnion_subtype] using hy
    obtain ⟨b,hb⟩ := mem_iUnion.mp (hh hy')
    refine mem_iUnion₂.mpr ⟨b.val,b.property,?_⟩
    rw [DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph
      (B b.val) (hB b.val b.property)] at hb
    exact hb
  intro x hx
  have hh := frontier_inter_subset Ω (⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1)ᶜ hx
  exact hh.elim (fun h => Or.inl h.1) (fun h => Or.inr (hfr ((frontier_compl (⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1)) ▸ h.2)))

theorem boundary_incidence_of_finite_ball_complement_component
    {Ω : Set M} (hΩ : IsClosed Ω) (outer : T.Boundary)
    (hfront : frontier Ω = range (T.boundarySphere outer))
    (s : Finset T.Boundary) (B : T.Boundary → PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M ∞)
    (hB : ∀ b ∈ s, closedBall (0 : ThreeSpace) 1 ⊆ (B b).source)
    (hinside : ∀ b ∈ s, B b '' closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hdis : (s : Set T.Boundary).Pairwise (fun b c =>
      Disjoint (B b '' closedBall (0 : ThreeSpace) 1) (B c '' closedBall (0 : ThreeSpace) 1)))
    (hsphere : ∀ b ∈ s, B b '' sphere (0 : ThreeSpace) 1 = range (T.boundarySphere b))
    (x : T.core)
    (hcomponent : Ω \ ⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1 =
      (Subtype.val : T.core → M) '' connectedComponent x) :
    (∀ b : T.Boundary, b = outer ∨ b ∈ s →
      ∀ q : Sphere 2, T.coreBoundarySphere b q ∈ connectedComponent x) ∧
    (∀ b : T.Boundary, (∃ q : Sphere 2, T.coreBoundarySphere b q ∈ connectedComponent x) →
      b = outer ∨ b ∈ s) := by
  classical
  let K := Ω \ ⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1
  have hcomp : K = (Subtype.val : T.core → M) '' connectedComponent x := hcomponent
  have hKcore : K ⊆ T.core := by
    intro y hy
    obtain ⟨z,_,hz⟩ := hcomp ▸ hy
    exact hz ▸ z.property
  have hKmem {y : T.core} (hy : y.val ∈ K) : y ∈ connectedComponent x := by
    obtain ⟨z,hz,hzy⟩ := hcomp ▸ hy
    exact (Subtype.ext hzy : z = y) ▸ hz
  constructor
  · intro b hb q
    apply hKmem
    rcases hb with hbo | hb
    · subst b
      have hqf : T.boundarySphere outer q ∈ frontier Ω := hfront.symm ▸ mem_range_self q
      refine ⟨hΩ.frontier_subset hqf,?_⟩
      intro hyU
      obtain ⟨c,hc,hy⟩ := mem_iUnion₂.mp hyU
      exact hqf.2 (hinside c hc (image_mono ball_subset_closedBall hy))
    · have hqs : T.boundarySphere b q ∈ B b '' sphere (0 : ThreeSpace) 1 :=
        (hsphere b hb).symm ▸ mem_range_self q
      refine ⟨interior_subset (hinside b hb (image_mono sphere_subset_closedBall hqs)),?_⟩
      intro hqU
      obtain ⟨c,hc,z,hz,hzq⟩ := mem_iUnion₂.mp hqU
      by_cases hbc : b = c
      · subst c
        obtain ⟨w,hw,hwq⟩ := hqs
        have he := (B b).injOn (hB b hb (ball_subset_closedBall hz))
          (hB b hb (sphere_subset_closedBall hw)) (hzq.trans hwq.symm)
        exact (mem_ball_zero_iff.mp (he ▸ hz)).ne (mem_sphere_zero_iff_norm.mp hw)
      · exact disjoint_left.mp (hdis hb hc hbc) (image_mono sphere_subset_closedBall hqs)
          ⟨z,ball_subset_closedBall hz,hzq⟩
  · intro b hb
    obtain ⟨q,hq⟩ := hb
    have hqK : T.boundarySphere b q ∈ K := hcomp.symm ▸ mem_image_of_mem Subtype.val hq
    have hn : T.boundarySphere b q ∉ interior K := by
      intro hi
      have hm := (mem_closure_iff_nhds.mp (T.boundarySphere_mem_closure_removedBand b q))
        (interior K) (isOpen_interior.mem_nhds hi)
      obtain ⟨y,hy,hyband⟩ := hm
      exact hKcore (interior_subset hy) (mem_iUnion.mpr ⟨b.1,hyband⟩)
    have hf : T.boundarySphere b q ∈ frontier K := (mem_frontier_iff_notMem_interior hqK).mpr hn
    rcases frontier_punctured_subset T s B hB hf with ho | hi
    · obtain ⟨z,hz⟩ := hfront ▸ ho
      exact Or.inl ((T.boundarySphere_eq_iff b outer q z).mp hz.symm).1
    · obtain ⟨c,hc,hq'⟩ := mem_iUnion₂.mp hi
      obtain ⟨z,hz⟩ := hsphere c hc ▸ hq'
      have he : b = c := ((T.boundarySphere_eq_iff b c q z).mp hz.symm).1
      exact Or.inr (he.symm ▸ hc)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem
