import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Coordinates.BarycentricChain
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Coordinates.BarycentricWeights
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Coordinates.BarycentricChainWeights
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Fintype.Powerset

namespace DifferentialGeometry.Topology.Engulfing

set_option linter.unusedSectionVars false

open Set
open scoped BigOperators

variable {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

noncomputable def chainCentroids (v : ι → E) (C : Finset (Finset ι)) : Finset E := by
  classical
  exact C.image (fun s => s.centroid ℝ v)

omit [DecidableEq ι] in
theorem mem_chainCentroids {v : ι → E} {C : Finset (Finset ι)} {x : E} :
    x ∈ chainCentroids v C ↔ ∃ s ∈ C, s.centroid ℝ v = x := by
  classical
  exact Finset.mem_image

omit [DecidableEq ι] in
theorem isFaceChain.centroids_injective {v : ι → E} (hv : AffineIndependent ℝ v)
    {C : Finset (Finset ι)} (hC : isFaceChain C) :
    Set.InjOn (fun s : Finset ι => s.centroid ℝ v) (C : Set (Finset ι)) := by
  classical
  exact fun _ hs _ ht h => centroid_injective_of_affineIndependent hv (hC.1 _ hs) (hC.1 _ ht) h

omit [DecidableEq ι] in
theorem isFaceChain.mem_convexHull_chainCentroids_iff {v : ι → E}
    (hv : AffineIndependent ℝ v) {C : Finset (Finset ι)} (hC : isFaceChain C) {x : E} :
    x ∈ convexHull ℝ (chainCentroids v C : Set E) ↔
      ∃ a : Finset ι → ℝ, (∀ s ∈ C, 0 ≤ a s) ∧ ∑ s ∈ C, a s = 1 ∧
        ∑ s ∈ C, a s • s.centroid ℝ v = x := by
  classical
  constructor
  · intro hx
    obtain ⟨a, ha, hsum, hpoint⟩ := Finset.mem_convexHull'.mp hx
    refine ⟨fun s => a (s.centroid ℝ v), ?_, ?_, ?_⟩
    · intro s hs
      exact ha _ (mem_chainCentroids.mpr ⟨s, hs, rfl⟩)
    · simpa only [chainCentroids, Finset.sum_image (hC.centroids_injective hv)] using hsum
    · simpa only [chainCentroids, Finset.sum_image (hC.centroids_injective hv)] using hpoint
  · rintro ⟨a, ha, hsum, rfl⟩
    have h := C.centerMass_mem_convexHull ha (by rw [hsum]; exact zero_lt_one)
      (fun s hs => (show s.centroid ℝ v ∈ (chainCentroids v C : Set E) from
        mem_chainCentroids.mpr ⟨s, hs, rfl⟩))
    simpa only [Finset.centerMass_eq_of_sum_1 _ _ hsum] using h

omit [DecidableEq ι] in
theorem isFaceChain.affineIndependent_chainCentroids {v : ι → E}
    (hv : AffineIndependent ℝ v) {C : Finset (Finset ι)} (hC : isFaceChain C) :
    AffineIndependent ℝ ((↑) : chainCentroids v C → E) := by
  classical
  have h := (hC.affineIndependent_centroids hv).range
  have heq : range (fun s : C => s.1.centroid ℝ v) = (chainCentroids v C : Set E) := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact mem_chainCentroids.mpr ⟨s, s.2, rfl⟩
    · intro hx
      obtain ⟨s, hs, rfl⟩ := mem_chainCentroids.mp hx
      exact ⟨⟨s, hs⟩, rfl⟩
  rw [heq] at h
  exact h

omit [DecidableEq ι] in
theorem chainCentroids_mono (v : ι → E) {C D : Finset (Finset ι)} (hCD : C ⊆ D) :
    chainCentroids v C ⊆ chainCentroids v D := by
  classical
  exact Finset.image_subset_image hCD

theorem chainCentroids_inter [DecidableEq E] {v : ι → E} (hv : AffineIndependent ℝ v)
    {C D : Finset (Finset ι)} (hC : isFaceChain C) (hD : isFaceChain D) :
    chainCentroids v (C ∩ D) = chainCentroids v C ∩ chainCentroids v D := by
  classical
  ext x
  simp only [Finset.mem_inter, mem_chainCentroids]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs.1, rfl⟩, ⟨s, hs.2, rfl⟩⟩
  · rintro ⟨⟨s, hs, hsx⟩, ⟨t, ht, htx⟩⟩
    have hst := centroid_injective_of_affineIndependent hv (hC.1 s hs) (hD.1 t ht)
      (hsx.trans htx.symm)
    exact ⟨s, ⟨hs, hst ▸ ht⟩, hsx⟩

omit [DecidableEq ι] in
theorem isFaceChain.exists_subchain {v : ι → E} {C : Finset (Finset ι)}
    (hC : isFaceChain C) {b : Finset E} (hb : b ⊆ chainCentroids v C) (hbne : b.Nonempty) :
    ∃ D : Finset (Finset ι), D.Nonempty ∧ isFaceChain D ∧ chainCentroids v D = b := by
  classical
  let D := C.filter (fun s => s.centroid ℝ v ∈ b)
  have hD : isFaceChain D := hC.mono (Finset.filter_subset _ C)
  have himage : chainCentroids v D = b := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := mem_chainCentroids.mp hx
      exact (Finset.mem_filter.mp hs).2
    · intro hx
      obtain ⟨s, hs, heq⟩ := mem_chainCentroids.mp (hb hx)
      exact mem_chainCentroids.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, heq ▸ hx⟩, heq⟩
  have hDne : D.Nonempty := by
    obtain ⟨x, hx⟩ := hbne
    rw [← himage] at hx
    obtain ⟨s, hs, -⟩ := mem_chainCentroids.mp hx
    exact ⟨s, hs⟩
  exact ⟨D, hDne, hD, himage⟩

theorem isFaceChain.convexHull_chainCentroids_inter {v : ι → E}
    (hv : AffineIndependent ℝ v) {C D : Finset (Finset ι)}
    (hC : isFaceChain C) (hD : isFaceChain D) :
    convexHull ℝ (chainCentroids v C : Set E) ∩ convexHull ℝ (chainCentroids v D : Set E) =
      convexHull ℝ (chainCentroids v (C ∩ D) : Set E) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, hasum, hax⟩ := (hC.mem_convexHull_chainCentroids_iff hv).mp hx.1
    obtain ⟨b, hb, hbsum, hbx⟩ := (hD.mem_convexHull_chainCentroids_iff hv).mp hx.2
    have hcoord := faceWeightCoord_eq_of_sum_eq hv C D a b hC.1 hD.1
      (hasum.trans hbsum.symm) (hax.trans hbx.symm)
    have hzero (s : Finset ι) (hs : s ∈ C) (hsD : s ∉ D) : a s = 0 := by
      apply le_antisymm _ (ha s hs)
      exact le_of_not_gt (fun hpos => hsD (hC.mem_of_faceWeightCoord_eq hD a b ha hb
        hcoord hs hpos))
    apply ((hC.mono Finset.inter_subset_left).mem_convexHull_chainCentroids_iff hv).mpr
    refine ⟨a, fun s hs => ha s (Finset.mem_inter.mp hs).1, ?_, ?_⟩
    · calc
        ∑ s ∈ C ∩ D, a s = ∑ s ∈ C, a s := Finset.sum_subset Finset.inter_subset_left
          (fun s hs hsn => hzero s hs (fun hd => hsn (Finset.mem_inter.mpr ⟨hs, hd⟩)))
        _ = 1 := hasum
    · calc
        ∑ s ∈ C ∩ D, a s • s.centroid ℝ v = ∑ s ∈ C, a s • s.centroid ℝ v :=
          Finset.sum_subset Finset.inter_subset_left (fun s hs hsn => by
            rw [hzero s hs (fun hd => hsn (Finset.mem_inter.mpr ⟨hs, hd⟩)), zero_smul])
        _ = x := hax
  · intro x hx
    exact ⟨convexHull_mono (chainCentroids_mono v Finset.inter_subset_left) hx,
      convexHull_mono (chainCentroids_mono v Finset.inter_subset_right) hx⟩

noncomputable def barycentricComplex (v : ι → E) (hv : AffineIndependent ℝ v) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | ∃ C : Finset (Finset ι), C.Nonempty ∧ isFaceChain C ∧ chainCentroids v C = s}
  isRelLowerSet_faces := by
    rintro s ⟨C, hCne, hC, rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨t, ht⟩ := hCne
      exact ⟨t.centroid ℝ v, mem_chainCentroids.mpr ⟨t, ht, rfl⟩⟩
    · intro b hb hbne
      exact hC.exists_subchain hb hbne
  indep := by
    rintro s ⟨C, -, hC, rfl⟩
    exact hC.affineIndependent_chainCentroids hv
  inter_subset_convexHull := by
    classical
    rintro s t ⟨C, -, hC, rfl⟩ ⟨D, -, hD, rfl⟩
    have heq := hC.convexHull_chainCentroids_inter hv hD
    rw [chainCentroids_inter hv hC hD] at heq
    simpa only [Finset.coe_inter] using heq.le

theorem barycentricComplex_finite_faces [Finite ι] (v : ι → E)
    (hv : AffineIndependent ℝ v) : (barycentricComplex v hv).faces.Finite := by
  let := Fintype.ofFinite ι
  apply (Set.finite_range (chainCentroids v)).subset
  rintro s ⟨C, -, -, rfl⟩
  exact mem_range_self C

theorem barycentricComplex_space_subset (v : ι → E) (hv : AffineIndependent ℝ v) :
    (barycentricComplex v hv).space ⊆ convexHull ℝ (range v) := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨C, -, hC, rfl⟩ := hs
  apply (convexHull_min ?_ (convex_convexHull ℝ (range v))) hxs
  intro y hy
  obtain ⟨t, ht, rfl⟩ := mem_chainCentroids.mp hy
  exact affineCombination_mem_convexHull
    (fun i _ => by simp only [Finset.centroidWeights_apply]; positivity)
    (t.sum_centroidWeights_eq_one_of_nonempty ℝ (hC.1 t ht))

noncomputable def barycentricSimplex (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) : Geometry.SimplicialComplex ℝ E := by
  classical
  exact barycentricComplex (Subtype.val : V → E) hV

theorem barycentricSimplex_finite_faces (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) : (barycentricSimplex V hV).faces.Finite := by
  classical
  exact barycentricComplex_finite_faces _ _

theorem barycentricSimplex_space_subset (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) :
    (barycentricSimplex V hV).space ⊆ convexHull ℝ (V : Set E) := by
  classical
  have hr : range (Subtype.val : V → E) = (V : Set E) := by
    ext x
    exact ⟨fun ⟨i, hi⟩ => hi ▸ i.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  change (barycentricComplex (Subtype.val : V → E) hV).space ⊆ _
  rw [← hr]
  exact barycentricComplex_space_subset _ _

end DifferentialGeometry.Topology.Engulfing
