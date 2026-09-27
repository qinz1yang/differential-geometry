import DifferentialGeometry.Topology.Order.DisjointGraphs
import DifferentialGeometry.Topology.Manifold.GraphBand

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {E F H G X Y ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] [PreconnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace G Y] [T2Space Y]
  {n : ℕ∞ω}

theorem exists_first_graph_band_of_finite_boundary_family
    (T : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (X × ℝ) Y n)
    (f : X → ℝ) (hf : ContMDiff I 𝓘(ℝ) n f)
    (S : ι → Set Y) {s : Set ι} (hs : s.Finite)
    (g : ι → X → ℝ) (hg : ∀ i ∈ s, ContMDiff I 𝓘(ℝ) n (g i))
    (hsource : ∀ i ∈ s,
      {z : X × ℝ | z.2 ∈ uIcc (f z.1) (g i z.1)} ⊆ T.source)
    (hgraph : ∀ i ∈ s, range (fun q => T (q, g i q)) = S i)
    (hdisjoint : s.Pairwise (fun i j => Disjoint (S i) (S j)))
    (havoid : ∀ i ∈ s, Disjoint (range (fun q => T (q, f q))) (S i))
    (hmeet : ∃ i ∈ s, ∃ q, f q < g i q) :
    ∃ i ∈ s, ∃ A : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (X × ℝ) Y n,
      (∀ q, f q < g i q) ∧
      univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
      (∀ q t, A (q, t) = T (q, f q + (g i q - f q) * t)) ∧
      (∀ q, A (q, 0) = T (q, f q)) ∧
      (∀ q, A (q, 1) = T (q, g i q)) ∧
      IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
      frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun q => T (q, f q)) ∪ S i ∧
      ∀ j ∈ s, j ≠ i → Disjoint (S j) (A '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
  have hne (i j : ι) (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) (q : X) :
      g i q ≠ g j q := by
    intro heq
    apply Set.disjoint_left.mp (hdisjoint hi hj hij)
      ((hgraph i hi) ▸ mem_range_self q)
    exact (hgraph j hj) ▸ ⟨q, congrArg T (Prod.ext rfl heq.symm)⟩
  have hlow (i : ι) (hi : i ∈ s) (q : X) : f q ≠ g i q := by
    intro heq
    exact Set.disjoint_left.mp (havoid i hi) (mem_range_self q)
      ((hgraph i hi) ▸ ⟨q, congrArg T (Prod.ext rfl heq.symm)⟩)
  obtain ⟨i, hi, hfi, hmin⟩ := exists_least_graph_above hs f g hf.continuous
    (fun i hi => (hg i hi).continuous) (fun i hi j hj hij => hne i j hi hj hij) hlow hmeet
  obtain ⟨A, hA, hformula, hrange, hcompact, hfront⟩ :=
    exists_graphBand_partialDiffeomorph T f (g i) hf (hg i hi) (fun q => (hfi q).ne)
      (hsource i hi)
  refine ⟨i, hi, A, hfi, hA, fun q t => hformula (q, t), ?_, ?_, hcompact, ?_, ?_⟩
  · intro q
    rw [hformula]
    simp
  · intro q
    rw [hformula]
    simp
  · exact hfront.trans (congrArg (fun U => range (fun q => T (q, f q)) ∪ U) (hgraph i hi))
  · intro j hj hji
    rw [hrange, Set.disjoint_left]
    rintro y hyS ⟨z, hz, hzy⟩
    have hygraph : y ∈ range (fun q => T (q, g j q)) := (hgraph j hj).symm ▸ hyS
    obtain ⟨q, hq⟩ := hygraph
    have hqsource : (q, g j q) ∈ T.source :=
      hsource j hj (right_mem_uIcc : g j q ∈ uIcc (f q) (g j q))
    have hzeq := T.injOn hqsource (hsource i hi hz) (hq.trans hzy.symm)
    have hqz : q = z.1 := congrArg Prod.fst hzeq
    have hgz : g j q = z.2 := congrArg Prod.snd hzeq
    have hz' : f z.1 ≤ z.2 ∧ z.2 ≤ g i z.1 := by
      change z.2 ∈ uIcc (f z.1) (g i z.1) at hz
      simpa only [uIcc_of_le (hfi z.1).le, mem_Icc] using hz
    have hfj : f q < g j q := lt_of_le_of_ne
      (by rw [hgz, hqz]; exact hz'.1) (hlow j hj q)
    have hle := hmin j hj ⟨q, hfj⟩ q
    have heq : g i q = g j q := le_antisymm hle (by rw [hgz, hqz]; exact hz'.2)
    exact hne i j hi hj (Ne.symm hji) q heq

end DifferentialGeometry.Topology
