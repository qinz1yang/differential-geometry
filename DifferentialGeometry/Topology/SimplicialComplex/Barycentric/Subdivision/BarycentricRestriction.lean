import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricSubdivision

namespace DifferentialGeometry.Topology.Engulfing

open Set
open scoped BigOperators

variable {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

theorem isFaceChain.convexHull_chainCentroids_inter_affineSpan {v : ι → E}
    (hv : AffineIndependent ℝ v) {C : Finset (Finset ι)} (hC : isFaceChain C)
    (T : Finset ι) :
    convexHull ℝ (chainCentroids v C : Set E) ∩
      (affineSpan ℝ (v '' (T : Set ι)) : Set E) =
      convexHull ℝ (chainCentroids v (C.filter (fun s => s ⊆ T)) : Set E) := by
  classical
  let D := C.filter (fun s => s ⊆ T)
  have hDC : D ⊆ C := Finset.filter_subset _ _
  have hD : isFaceChain D := hC.mono hDC
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, hasum, hax⟩ := (hC.mem_convexHull_chainCentroids_iff hv).mp hx.1
    let U := C.biUnion id
    have hU : ∀ s ∈ C, s ⊆ U := fun s hs i hi => Finset.mem_biUnion.mpr ⟨s, hs, hi⟩
    have hsum : ∑ i ∈ U, faceWeightCoord C a i = 1 :=
      (sum_faceWeightCoord C a U hC.1 hU).trans hasum
    have hpoint : U.affineCombination ℝ v (faceWeightCoord C a) ∈
        affineSpan ℝ (v '' (T : Set ι)) := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
        sum_faceWeightCoord_smul C a U v hC.1 hU, hax]
      exact hx.2
    have hzero (s : Finset ι) (hs : s ∈ C) (hsT : ¬ s ⊆ T) : a s = 0 := by
      apply le_antisymm _ (ha s hs)
      apply le_of_not_gt
      intro hpos
      obtain ⟨i, his, hiT⟩ := Finset.not_subset.mp hsT
      have hiU : i ∈ U := hU s hs his
      have hcoord := hv.eq_zero_of_affineCombination_mem_affineSpan hsum hpoint hiU hiT
      have hnonneg (t : Finset ι) (ht : t ∈ C) :
          0 ≤ (if i ∈ t then a t / (t.card : ℝ) else 0) := by
        split_ifs
        · exact div_nonneg (ha t ht) (Nat.cast_nonneg _)
        · exact le_rfl
      have hle := Finset.single_le_sum hnonneg hs
      change (if i ∈ s then a s / (s.card : ℝ) else 0) ≤ faceWeightCoord C a i at hle
      rw [ite_eq_left his, hcoord] at hle
      exact (not_le_of_gt (div_pos hpos (by exact_mod_cast Finset.card_pos.mpr (hC.1 s hs)))) hle
    apply (hD.mem_convexHull_chainCentroids_iff hv).mpr
    refine ⟨a, fun s hs => ha s (hDC hs), ?_, ?_⟩
    · calc
        ∑ s ∈ D, a s = ∑ s ∈ C, a s := Finset.sum_subset hDC (fun s hs hsD =>
          hzero s hs (fun hsT => hsD (Finset.mem_filter.mpr ⟨hs, hsT⟩)))
        _ = 1 := hasum
    · calc
        ∑ s ∈ D, a s • s.centroid ℝ v = ∑ s ∈ C, a s • s.centroid ℝ v :=
          Finset.sum_subset hDC (fun s hs hsD => by
            rw [hzero s hs (fun hsT => hsD (Finset.mem_filter.mpr ⟨hs, hsT⟩)), zero_smul])
        _ = x := hax
  · intro x hx
    refine ⟨convexHull_mono (chainCentroids_mono v hDC) hx, ?_⟩
    apply (convexHull_min ?_ (AffineSubspace.convex _)) hx
    intro y hy
    obtain ⟨s, hs, rfl⟩ := mem_chainCentroids.mp hy
    have hsT : s ⊆ T := (Finset.mem_filter.mp hs).2
    exact affineSpan_mono ℝ (image_mono hsT)
      (affineCombination_mem_affineSpan_image
        (s.sum_centroidWeights_eq_one_of_nonempty ℝ (hD.1 s hs))
        (fun _ hi hn => (hn hi).elim) v)

end DifferentialGeometry.Topology.Engulfing
