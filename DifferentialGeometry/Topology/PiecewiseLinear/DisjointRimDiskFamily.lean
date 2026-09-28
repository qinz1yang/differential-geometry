/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskComplementConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.exists_disjoint_disk_subfamily_of_disjoint_boundaries
    {ι : Type*} [Finite ι] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hKc : IsConnected K.space)
    {D : ι → Set E} {r : ι → (Fin 3 → ℝ) → E}
    (hr : ∀ i, IsPLHomeomorphOn (r i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDK : ∀ i, D i ⊆ K.space)
    (hdis : Pairwise fun i j => Disjoint (r i '' stdSimplexBoundary 2)
      (r j '' stdSimplexBoundary 2))
    (hpair : ∀ i j, (K.space \ (D i ∪ D j)).Nonempty) :
    ∃ (κ : Type) (_ : Finite κ) (B : κ → Set E), (∀ b, ∃ i, D i = B b) ∧
      (Pairwise fun b c => Disjoint (B b) (B c)) ∧ (⋃ b, B b) = ⋃ i, D i := by
  classical
  let C := fun i => r i '' stdSimplexBoundary 2
  have hC : ∀ i, IsPLSphere 1 (C i) := fun i => (hr i).isPLSphere_image_stdSimplexBoundary
  have hDc : ∀ i, IsClosed (D i) := fun i => (IsPLBall.isPolyhedron ⟨r i, hr i⟩).isClosed
  have hfr : ∀ i, D i ∩ closure (K.space \ D i) = C i := fun i =>
    hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K (hr i) (hDK i)
  have hin : ∀ i, ∀ x ∈ K.space, x ∉ closure (K.space \ D i) → x ∈ D i := by
    intro i x hx hxc
    by_contra hxD
    exact hxc (subset_closure ⟨hx, hxD⟩)
  have hside : ∀ i (Z : Set E), Z ⊆ K.space → IsPreconnected Z → Disjoint Z (C i) →
      Z ⊆ (closure (K.space \ D i))ᶜ ∨ Disjoint Z (D i) := by
    intro i Z hZK hZ hZC
    have hcov : Z ⊆ (closure (K.space \ D i))ᶜ ∪ (D i)ᶜ := by
      intro z hz
      by_cases hzD : z ∈ D i
      · refine Or.inl fun hcl => disjoint_left.mp hZC hz ?_
        rw [← hfr i]
        exact ⟨hzD, hcl⟩
      · exact Or.inr hzD
    have hemp : Z ∩ ((closure (K.space \ D i))ᶜ ∩ (D i)ᶜ) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun z hz => hz.2.1 (subset_closure ⟨hZK hz.1, hz.2.2⟩)
    rcases isPreconnected_iff_subset_of_disjoint.mp hZ _ _ isClosed_closure.isOpen_compl
      (hDc i).isOpen_compl hcov hemp with hsub | hsub
    · exact Or.inl hsub
    · exact Or.inr (disjoint_left.mpr fun z hz hzD => hsub hz hzD)
  have hCconn : ∀ i, IsPreconnected (C i) :=
    fun i => (isConnected_stdSimplexBoundary 0).isPreconnected.image (r i)
      ((hr i).isPiecewiseAffineOn.continuousOn.mono fun x hx => hx.1)
  have hDconn : ∀ i, IsPreconnected (D i) :=
    fun i => (IsPLBall.isConnected ⟨r i, hr i⟩).isPreconnected
  have hCD : ∀ i, C i ⊆ D i := fun i => by
    rw [← (hr i).image_eq]
    exact image_mono fun x hx => hx.1
  have hCd : ∀ i j, i ≠ j → Disjoint (C i) (C j) := fun _ _ hij => hdis hij
  have hnest : ∀ i j, D i ⊆ D j ∨ D j ⊆ D i ∨ Disjoint (D i) (D j) := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · exact Or.inl Subset.rfl
    have hCC := hCd i j hij
    rcases hside i _ ((hCD j).trans (hDK j)) (hCconn j) hCC.symm with hα | hβ
    · rcases hside j _ ((hCD i).trans (hDK i)) (hCconn i) hCC with hγ | hδ
      · exfalso
        have hZ := (hK.isConnected_sdiff_of_isPLBall_two hKc ⟨r i, hr i⟩ (hDK i)).isPreconnected
        have hZC : Disjoint (K.space \ D i)
            (C j) :=
          disjoint_left.mpr fun z hz hzC =>
            hz.2 (hin i z ((hCD j).trans (hDK j) hzC) (hα hzC))
        rcases hside j _ sdiff_subset hZ hZC with h1 | h1
        · obtain ⟨p, hpK, hpD⟩ := hpair i j
          exact hpD (Or.inr (hin j p hpK (h1 ⟨hpK, fun h => hpD (Or.inl h)⟩)))
        · obtain ⟨x, hx⟩ := (hC i).nonempty
          have hx' := hx
          rw [← hfr i] at hx'
          obtain ⟨z, hzu, hzZ⟩ :=
            mem_closure_iff.mp hx'.2 _ isClosed_closure.isOpen_compl (hγ hx)
          exact disjoint_left.mp h1 hzZ (hin j z hzZ.1 hzu)
      · rcases hside i _ (hDK j) (hDconn j) hδ.symm with h2 | h2
        · exact Or.inr (Or.inl fun x hx => hin i x (hDK j hx) (h2 hx))
        · exfalso
          obtain ⟨x, hx⟩ := (hC j).nonempty
          exact disjoint_left.mp h2 (hCD j hx)
            (hin i x ((hCD j).trans (hDK j) hx) (hα hx))
    · rcases hside j _ ((hCD i).trans (hDK i)) (hCconn i) hCC with hγ | hδ
      · rcases hside j _ (hDK i) (hDconn i) hβ.symm with h2 | h2
        · exact Or.inl fun x hx => hin j x (hDK i hx) (h2 hx)
        · exfalso
          obtain ⟨x, hx⟩ := (hC i).nonempty
          exact disjoint_left.mp h2 (hCD i hx)
            (hin j x ((hCD i).trans (hDK i) hx) (hγ hx))
      · rcases hside j _ (hDK i) (hDconn i) hβ.symm with h2 | h2
        · exfalso
          obtain ⟨x, hx⟩ := (hC i).nonempty
          exact disjoint_left.mp hδ hx
            (hin j x ((hCD i).trans (hDK i) hx) (h2 (hCD i hx)))
        · exact Or.inr (Or.inr h2)
  have hfinD : (range D).Finite := finite_range D
  obtain ⟨M, hMdef⟩ : ∃ M : Set (Set E),
      M = {b | Maximal (· ∈ range D) b} := ⟨_, rfl⟩
  have hMmax : ∀ b ∈ M, Maximal (· ∈ range D) b := by
    rw [hMdef]
    exact fun b hb => hb
  have hMmem : ∀ b, Maximal (· ∈ range D) b → b ∈ M := by
    rw [hMdef]
    exact fun b hb => hb
  have hMfin : M.Finite := hfinD.subset fun b hb => (hMmax b hb).1
  have hMdisj : ∀ b₁ ∈ M, ∀ b₂ ∈ M, b₁ ≠ b₂ → Disjoint b₁ b₂ := by
    intro b₁ hb₁ b₂ hb₂ hne
    obtain ⟨i, rfl⟩ := (hMmax b₁ hb₁).1
    obtain ⟨j, rfl⟩ := (hMmax b₂ hb₂).1
    rcases hnest i j with h1 | h1 | h1
    · exact absurd (Subset.antisymm h1 ((hMmax _ hb₁).2 (hMmax _ hb₂).1 h1)) hne
    · exact absurd (Subset.antisymm ((hMmax _ hb₂).2 (hMmax _ hb₁).1 h1) h1) hne
    · exact h1
  have hMD : ∀ b : M, ∃ i, D i = (b : Set E) := fun b => (hMmax b b.2).1
  have : Finite M := hMfin.to_subtype
  refine ⟨M, inferInstance, Subtype.val, hMD, ?_, ?_⟩
  · intro b₁ b₂ hne
    exact hMdisj _ b₁.2 _ b₂.2 (Subtype.coe_injective.ne hne)
  · ext x
    constructor
    · intro hx
      obtain ⟨b, hxb⟩ := mem_iUnion.mp hx
      obtain ⟨i, hi⟩ := hMD b
      exact mem_iUnion.mpr ⟨i, hi ▸ hxb⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨b, hib, hb⟩ := hfinD.exists_le_maximal (mem_range_self i)
      exact mem_iUnion.mpr ⟨⟨b, hMmem b hb⟩, (show D i ⊆ b from hib) hi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
