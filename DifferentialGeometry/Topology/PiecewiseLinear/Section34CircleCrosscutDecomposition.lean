import DifferentialGeometry.Topology.PiecewiseLinear.ArcDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCellComplement
import Mathlib.Topology.Perfect

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsPolyhedron.exists_finite_connected_partition {U : Set E} (hU : IsPolyhedron U) :
    ∃ C : Set (Set E), C.Finite ∧ C.PairwiseDisjoint id ∧
      (∀ A ∈ C, IsCompact A ∧ IsConnected A) ∧ ⋃₀ C = U := by
  classical
  obtain ⟨ι, hι, P, hP, rfl⟩ := hU
  let _ : Fintype ι := Fintype.ofFinite ι
  let d : Finset ι := Finset.univ.filter fun i => (P i).Nonempty
  obtain ⟨C, hCfin, hCdis, hC, hcover⟩ :=
    Topology.exists_finite_isConnected_partition d P
      (fun i _ => (hP i).isCompact)
      (fun i hi => ⟨(Finset.mem_filter.mp hi).2, (hP i).convex.isPreconnected⟩)
  refine ⟨C, hCfin, hCdis, fun A hA => ⟨(hC A hA).1, (hC A hA).2.1⟩, ?_⟩
  rw [hcover]
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨i, hx⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hi⟩⟩, hi⟩

theorem inter_closure_sdiff_of_finite_closed_partition {X : Type*} [TopologicalSpace X]
    {S U : Set X} {C : Set (Set X)} (hCfin : C.Finite)
    (hCdis : C.PairwiseDisjoint id) (hCclosed : ∀ A ∈ C, IsClosed A)
    (hcover : ⋃₀ C = U) {A : Set X} (hA : A ∈ C) :
    A ∩ closure (S \ A) = A ∩ closure (S \ U) := by
  have hAU : A ⊆ U := fun x hx => hcover.subset (mem_sUnion.mpr ⟨A, hA, hx⟩)
  have hclosed : IsClosed (U \ A) := by
    have heq : U \ A = ⋃ B ∈ C \ {A}, B := by
      ext x
      constructor
      · rintro ⟨hx, hxn⟩
        obtain ⟨B, hB, hxB⟩ := mem_sUnion.mp (hcover.symm.subset hx)
        exact mem_iUnion₂.mpr ⟨B, ⟨hB, fun h => hxn (h ▸ hxB)⟩, hxB⟩
      · intro hx
        obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp hx
        exact ⟨hcover.subset (mem_sUnion.mpr ⟨B, hB.1, hxB⟩),
          fun hxA => Set.disjoint_left.mp (hCdis hB.1 hA hB.2) hxB hxA⟩
    rw [heq]
    exact (hCfin.subset sdiff_subset).isClosed_biUnion fun B hB => hCclosed B hB.1
  apply Subset.antisymm
  · rintro x ⟨hxA, hx⟩
    have hsub : S \ A ⊆ (S \ U) ∪ (U \ A) := by
      rintro y ⟨hyS, hyA⟩
      by_cases hyU : y ∈ U
      · exact Or.inr ⟨hyU, hyA⟩
      · exact Or.inl ⟨hyS, hyU⟩
    have hy := closure_mono hsub hx
    rw [closure_union, hclosed.closure_eq] at hy
    exact ⟨hxA, hy.resolve_right fun h => h.2 hxA⟩
  · exact inter_subset_inter_right _ (closure_mono (sdiff_subset_sdiff_right hAU))

variable [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_finite_disjoint_arc_partition {S U : Set E}
    (hS : IsPLSphere 1 S) (hU : IsPolyhedron U) (hUS : U ⊂ S) (hacc : Preperfect U) :
    ∃ C : Set (Set E), C.Finite ∧ C.PairwiseDisjoint id ∧ ⋃₀ C = U ∧
      ∀ A ∈ C, ∃ q : (Fin 2 → ℝ) → E,
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
        q '' stdSimplexBoundary 1 = A ∩ closure (S \ U) := by
  obtain ⟨D, hD, hUD, -⟩ := hS.exists_isPLBall_one_superset_of_ssubset hU.isClosed hUS
  obtain ⟨C, hCfin, hCdis, hC, hcover⟩ := hU.exists_finite_connected_partition
  have hAU : ∀ A ∈ C, A ⊆ U := fun A hA x hx =>
    hcover.subset (mem_sUnion.mpr ⟨A, hA, hx⟩)
  refine ⟨C, hCfin, hCdis, hcover, ?_⟩
  intro A hA
  have hnontrivial : A.Nontrivial := by
    obtain ⟨x, hx⟩ := (hC A hA).2.nonempty
    let R : Set E := ⋃ B ∈ C \ {A}, B
    have hR : IsClosed R :=
      (hCfin.subset sdiff_subset).isClosed_biUnion fun B hB => (hC B hB.1).1.isClosed
    have hxR : x ∉ R := by
      intro hxR
      obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp hxR
      exact Set.disjoint_left.mp (hCdis hB.1 hA hB.2) hxB hx
    obtain ⟨y, ⟨hyR, hyU⟩, hyx⟩ := preperfect_iff_nhds.mp hacc x (hAU A hA hx)
      Rᶜ (hR.isOpen_compl.mem_nhds hxR)
    obtain ⟨B, hB, hyB⟩ := mem_sUnion.mp (hcover.symm.subset hyU)
    have hBA : B = A := by
      by_contra h
      exact hyR (mem_iUnion₂.mpr ⟨B, ⟨hB, h⟩, hyB⟩)
    exact ⟨y, hBA ▸ hyB, x, hx, hyx⟩
  obtain ⟨q, hq⟩ := hD.isPLBall_one_of_isCompact_of_isConnected (hC A hA).1
    (hC A hA).2 hnontrivial ((hAU A hA).trans hUD)
  refine ⟨q, hq, ?_⟩
  rw [← hS.inter_closure_sdiff_eq_image_stdSimplexBoundary_one hq
    ((hAU A hA).trans hUS.subset)]
  exact inter_closure_sdiff_of_finite_closed_partition hCfin hCdis
    (fun B hB => (hC B hB).1.isClosed) hcover hA

theorem IsPLSphere.preperfect_one {S : Set E} (hS : IsPLSphere 1 S) : Preperfect S := by
  obtain ⟨A, hA, -, hAS⟩ := hS.exists_isPLBall_one_superset_of_ssubset isClosed_empty
    (empty_ssubset.mpr hS.isConnected.nonempty)
  exact hS.isConnected.isPreconnected.preperfect_of_nontrivial (hA.nontrivial.mono hAS)

theorem IsPLSphere.exists_finite_crosscut_partition_of_relative_boundary {S U W : Set E}
    (hS : IsPLSphere 1 S) (hU : IsPolyhedron U) (hproper : U ⊂ S)
    (hboundary : U ∩ closure (S \ U) = U ∩ W) (hdense : U ⊆ closure (U \ W)) :
    ∃ C : Set (Set E), C.Finite ∧ C.PairwiseDisjoint id ∧ ⋃₀ C = U ∧
      ∀ A ∈ C, ∃ q : (Fin 2 → ℝ) → E,
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
        q '' stdSimplexBoundary 1 = A ∩ W := by
  let V : Set E := (closure (S \ U))ᶜ
  have hVU : V ∩ S ⊆ U := by
    rintro x ⟨hxV, hxS⟩
    by_contra hxU
    exact hxV (subset_closure ⟨hxS, hxU⟩)
  have hUV : U \ W ⊆ V ∩ S := by
    rintro x ⟨hxU, hxW⟩
    refine ⟨?_, hproper.subset hxU⟩
    intro hx
    exact hxW (hboundary.subset ⟨hxU, hx⟩).2
  have hclosure : closure (V ∩ S) = U :=
    Subset.antisymm (closure_minimal hVU hU.isClosed) (hdense.trans (closure_mono hUV))
  have hacc : Preperfect U := by
    rw [← hclosure]
    exact (hS.preperfect_one.open_inter isClosed_closure.isOpen_compl).perfect_closure.acc
  obtain ⟨C, hCfin, hCdis, hcover, hC⟩ :=
    hS.exists_finite_disjoint_arc_partition hU hproper hacc
  refine ⟨C, hCfin, hCdis, hcover, ?_⟩
  intro A hA
  obtain ⟨q, hq, hqb⟩ := hC A hA
  have hAU : A ⊆ U := fun x hx => hcover.subset (mem_sUnion.mpr ⟨A, hA, hx⟩)
  refine ⟨q, hq, hqb.trans ?_⟩
  ext x
  constructor
  · rintro ⟨hxA, hx⟩
    exact ⟨hxA, (hboundary.subset ⟨hAU hxA, hx⟩).2⟩
  · rintro ⟨hxA, hxW⟩
    exact ⟨hxA, (hboundary.symm.subset ⟨hAU hxA, hxW⟩).2⟩

theorem IsPLSphere.exists_finite_crosscut_partition {S D : Set E}
    (hS : IsPLSphere 1 S) (hD : IsPolyhedron D) (hproper : S ∩ D ⊂ S)
    (hin : S ∩ frontier D ⊆ closure (S ∩ interior D))
    (hout : S ∩ frontier D ⊆ closure (S \ D)) :
    ∃ C : Set (Set E), C.Finite ∧ C.PairwiseDisjoint id ∧ ⋃₀ C = S ∩ D ∧
      ∀ A ∈ C, ∃ q : (Fin 2 → ℝ) → E,
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
        q '' stdSimplexBoundary 1 = A ∩ frontier D := by
  have hclosure : closure (S ∩ interior D) = S ∩ D := by
    apply Subset.antisymm
    · exact closure_minimal (inter_subset_inter_right _ interior_subset)
        (hS.isPolyhedron.isClosed.inter hD.isClosed)
    · rintro x ⟨hxS, hxD⟩
      by_cases hxint : x ∈ interior D
      · exact subset_closure ⟨hxS, hxint⟩
      · exact hin ⟨hxS, ⟨subset_closure hxD, hxint⟩⟩
  have hacc : Preperfect (S ∩ D) := by
    rw [← hclosure]
    have h : Preperfect (interior D ∩ S) := hS.preperfect_one.open_inter isOpen_interior
    rw [inter_comm] at h
    exact h.perfect_closure.acc
  obtain ⟨C, hCfin, hCdis, hcover, hC⟩ :=
    hS.exists_finite_disjoint_arc_partition (hS.isPolyhedron.inter hD) hproper hacc
  have hboundary : (S ∩ D) ∩ closure (S \ (S ∩ D)) = S ∩ frontier D := by
    have hdiff : S \ (S ∩ D) = S \ D := by ext x; simp
    rw [hdiff]
    apply Subset.antisymm
    · rintro x ⟨⟨hxS, hxD⟩, hxcl⟩
      refine ⟨hxS, subset_closure hxD, ?_⟩
      have hx := closure_mono (show S \ D ⊆ Dᶜ from fun _ h => h.2) hxcl
      rw [closure_compl] at hx
      exact hx
    · rintro x ⟨hxS, hxfront⟩
      exact ⟨⟨hxS, hD.isClosed.closure_eq.subset hxfront.1⟩, hout ⟨hxS, hxfront⟩⟩
  refine ⟨C, hCfin, hCdis, hcover, ?_⟩
  intro A hA
  obtain ⟨q, hq, hqb⟩ := hC A hA
  have hASD : A ⊆ S ∩ D := fun x hx => hcover.subset (mem_sUnion.mpr ⟨A, hA, hx⟩)
  refine ⟨q, hq, hqb.trans ?_⟩
  calc
    A ∩ closure (S \ (S ∩ D)) = A ∩ ((S ∩ D) ∩ closure (S \ (S ∩ D))) := by
      ext x
      exact ⟨fun h => ⟨h.1, hASD h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    _ = A ∩ (S ∩ frontier D) := by rw [hboundary]
    _ = A ∩ frontier D := by
      ext x
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (hASD h.1).1, h.2⟩⟩

theorem IsPLSphere.exists_finite_crosscut_partition_in_region {S K D W : Set E}
    (hS : IsPLSphere 1 S) (hSK : S ⊆ K) (hD : IsPolyhedron D)
    (hboundary : D ∩ closure (K \ D) ⊆ W)
    (hproper : S ∩ D ⊂ S) (hin : S ∩ W ⊆ closure (S ∩ (D \ W)))
    (hout : S ∩ W ⊆ closure (S \ D)) :
    ∃ C : Set (Set E), C.Finite ∧ C.PairwiseDisjoint id ∧ ⋃₀ C = S ∩ D ∧
      ∀ A ∈ C, ∃ q : (Fin 2 → ℝ) → E,
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
        q '' stdSimplexBoundary 1 = A ∩ W := by
  have hdiff : S \ (S ∩ D) = S \ D := by ext x; simp
  have hrel : (S ∩ D) ∩ closure (S \ (S ∩ D)) = (S ∩ D) ∩ W := by
    rw [hdiff]
    apply Subset.antisymm
    · rintro x ⟨hx, hxcl⟩
      exact ⟨hx, hboundary ⟨hx.2,
        closure_mono (sdiff_subset_sdiff_left hSK) hxcl⟩⟩
    · rintro x ⟨hx, hxW⟩
      exact ⟨hx, hout ⟨hx.1, hxW⟩⟩
  have hdense : S ∩ D ⊆ closure ((S ∩ D) \ W) := by
    rintro x ⟨hxS, hxD⟩
    by_cases hxW : x ∈ W
    · have hx := hin ⟨hxS, hxW⟩
      exact closure_mono (by intro y hy; exact ⟨⟨hy.1, hy.2.1⟩, hy.2.2⟩) hx
    · exact subset_closure ⟨⟨hxS, hxD⟩, hxW⟩
  exact hS.exists_finite_crosscut_partition_of_relative_boundary (hS.isPolyhedron.inter hD)
    hproper hrel hdense

end DifferentialGeometry.Topology.PiecewiseLinear
