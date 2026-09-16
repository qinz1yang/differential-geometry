import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplementLink
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem inter_closure_sdiff_space_subset_boundaryComplex {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.faces ⊆ K.faces) :
    A.space ∩ closure (K.space \ A.space) ⊆ (boundaryComplex (n + 1) A).space := by
  classical
  rintro x ⟨hxA, hxR⟩
  obtain ⟨T, hT, hTfin, hxT⟩ := exists_isSubdivision_singleton_mem K
    (space_mono_of_faces_subset hAK hxA)
  let _ : Finite T.faces := hTfin.to_subtype
  let B := restrict T A.space
  let _ : Finite B.faces := (restrict_faces_finite T A.space).to_subtype
  have hB : IsSubdivision B A := hT.restrict A hAK
  have hBT : B.faces ⊆ T.faces := restrict_faces_subset T A.space
  have hxB : {x} ∈ B.faces := mem_faces_of_mem_openSimplex_of_mem_space hBT hxT
    (mem_openSimplex_singleton x) (hB.space_eq.symm ▸ hxA)
  have hxC : x ∈ (subcomplexGeneratedBy T B.facesᶜ).space := by
    rw [← closure_space_sdiff_space_eq_subcomplexGeneratedBy T T B Subset.rfl hBT,
      hT.space_eq, hB.space_eq]
    exact hxR
  have hxC' := mem_faces_of_mem_openSimplex_of_mem_space
    (subcomplexGeneratedBy_faces_subset T B.facesᶜ) hxT (mem_openSimplex_singleton x) hxC
  have hnot := not_geometricLink_space_subset_of_mem_subcomplexGeneratedBy_compl T B hBT hxB hxC'
  have hsub : (SimplicialComplex.geometricLink B {x}).space ⊆
      (SimplicialComplex.geometricLink T {x}).space :=
    space_mono_of_faces_subset (fun _ ht => ⟨ht.1, ht.2.1, hBT ht.2.2⟩)
  have hball : IsPLBall n (SimplicialComplex.geometricLink B {x}).space := by
    rcases (hA.of_isSubdivision hB) x hxB with hs | hb
    · rcases (hK.of_isSubdivision hT) x hxT with hsT | hbT
      · have heq : (SimplicialComplex.geometricLink B {x}).space =
            (SimplicialComplex.geometricLink T {x}).space := by
          cases n with
          | zero =>
            obtain ⟨a, b, hab, ha⟩ := isPLSphere_zero_iff.mp hs
            obtain ⟨c, d, hcd, hc⟩ := isPLSphere_zero_iff.mp hsT
            exact eq_of_subset_of_ncard_le hsub
              (by rw [ha, hc, ncard_pair hab, ncard_pair hcd]) hsT.finite_of_zero
          | succ n => exact eq_of_subset_of_isPLSphere hs hsT hsub
        exact (hnot heq.symm.subset).elim
      · exact (hs.not_subset_of_isPLBall hbT hsub).elim
    · exact hb
  have hxbd : {x} ∈ (boundaryComplex (n + 1) B).faces := by
    apply ((hA.of_isSubdivision hB).mem_boundaryComplex_faces_iff B).mpr
    refine ⟨hxB, by simp, ?_⟩
    simpa only [Finset.card_singleton, Nat.add_sub_cancel] using hball
  have hx := (boundaryComplex (n + 1) B).subset_space hxbd (Finset.mem_singleton_self x)
  rwa [boundaryComplex_space_of_isSubdivision A B hA hB] at hx

open Classical in
theorem boundaryComplex_space_subset_closure_sdiff_of_isCombinatorialManifold {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifold (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.faces ⊆ K.faces) :
    (boundaryComplex (n + 1) A).space ⊆ closure (K.space \ A.space) := by
  classical
  let B := boundaryComplex (n + 1) A
  let _ : Finite B.faces := (boundaryComplex_faces_finite (n + 1) A).to_subtype
  have hB := isCombinatorialManifold_boundaryComplex A hA
  rw [closure_space_sdiff_space_eq_subcomplexGeneratedBy K K A Subset.rfl hAK]
  intro x hx
  obtain ⟨s, hs, hxs⟩ := B.mem_space_iff.mp hx
  obtain ⟨t, ht, hst, htc⟩ := hB.exists_face_superset_card_eq B hs
  have htA := boundaryComplex_faces_subset (n + 1) A ht
  obtain ⟨a, ha⟩ := (hA.mem_boundaryComplex_iff_unique_coface A htc).mp ht
  have htKbd : t ∉ (boundaryComplex (n + 1) K).faces := by
    rw [hK.boundaryComplex_faces_eq_empty K]
    exact notMem_empty t
  obtain ⟨b, c, hbc, hbcV⟩ :=
    hK.isCombinatorialManifoldWithBoundary.codimension_one_cofaces_of_notMem_boundary K
      (hAK htA) htc htKbd
  have hVfin : {w | w ∉ t ∧ insert w t ∈ A.faces}.Finite := ha ▸ finite_singleton a
  have hcard : {w | w ∉ t ∧ insert w t ∈ A.faces}.ncard <
      {w | w ∉ t ∧ insert w t ∈ K.faces}.ncard := by
    rw [ha, hbcV, ncard_singleton, ncard_pair hbc]
    decide
  obtain ⟨w, hwK, hwA⟩ := sdiff_nonempty_of_ncard_lt_ncard hcard hVfin
  have hiA : insert w t ∉ A.faces := fun hi => hwA ⟨hwK.1, hi⟩
  exact (subcomplexGeneratedBy K A.facesᶜ).convexHull_subset_space
    ⟨insert w t, ⟨hwK.2, hiA⟩, Finset.subset_insert w t, A.nonempty_of_mem_faces htA⟩
    (convexHull_mono (Finset.coe_subset.mpr hst) hxs)

open Classical in
theorem inter_closure_sdiff_space_eq_boundaryComplex_of_isCombinatorialManifold {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifold (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.faces ⊆ K.faces) :
    A.space ∩ closure (K.space \ A.space) = (boundaryComplex (n + 1) A).space :=
  Subset.antisymm
    (inter_closure_sdiff_space_subset_boundaryComplex K A hK.isCombinatorialManifoldWithBoundary hA hAK)
    (subset_inter (boundaryComplex_space_subset (n + 1) A)
      (boundaryComplex_space_subset_closure_sdiff_of_isCombinatorialManifold K A hK hA hAK))

open Classical in
theorem IsCombinatorialManifold.inter_closure_sdiff_eq_image_stdSimplexBoundary {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) {D : Set E} {r : (Fin (n + 2) → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin (n + 2))) D) (hDK : D ⊆ K.space) :
    D ∩ closure (K.space \ D) = r '' stdSimplexBoundary (n + 1) := by
  classical
  have hD : IsPLBall (n + 1) D := ⟨r, hr⟩
  obtain ⟨T, hT, hTfin, hTD⟩ := exists_isSubdivision_restrict_space K hD.isPolyhedron hDK
  let _ : Finite T.faces := hTfin.to_subtype
  let A := restrict T D
  let _ : Finite A.faces := (restrict_faces_finite T D).to_subtype
  have hrA : IsPLHomeomorphOn r (stdSimplex ℝ (Fin (n + 2))) A.space := hTD.symm ▸ hr
  have hA : IsPLBall (n + 1) A.space := ⟨r, hrA⟩
  have heq := inter_closure_sdiff_space_eq_boundaryComplex_of_isCombinatorialManifold T A
    (hK.of_isSubdivision hT) hA.isCombinatorialManifoldWithBoundary (restrict_faces_subset T D)
  rw [hTD, hT.space_eq, boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex A hrA,
    simplexBoundary_stdVertices_space] at heq
  exact heq

end DifferentialGeometry.Topology.PiecewiseLinear
