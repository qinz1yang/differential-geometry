/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.LocalSurfaceLink
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurface

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section SurfacePieces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff {ι : Type*}
    (s : Finset ι) {M Cc : ι → Set E} {P : ι → E}
    (hM : ∀ i ∈ s, IsOpenTopologicalCell 2 (M i))
    (hloc : ∀ i ∈ s, IsLocallyPolyhedral (M i \ {P i}))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (M i) (M j))
    (hC : ∀ i ∈ s, IsCompact (Cc i)) (hCM : ∀ i ∈ s, Cc i ⊆ M i \ {P i}) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 L ∧
        ∀ i ∈ s, ∀ x ∈ Cc i, ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ y ∈ M i := by
  classical
  have hQ : ∀ i, ∃ Q : Set E, IsPolyhedron Q ∧ (i ∈ s → Cc i ⊆ Q ∧ Q ⊆ M i \ {P i} ∧
      ∀ x ∈ Cc i, Q ∈ 𝓝[M i \ {P i}] x) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨Q, hQ, hCQ, hQS, hnhds⟩ :=
        (hloc i hi).exists_isPolyhedron_neighborhood_of_isCompact (hC i hi) (hCM i hi)
      exact ⟨Q, hQ, fun _ => ⟨hCQ, hQS, hnhds⟩⟩
    · exact ⟨∅, IsPolyhedron.empty, fun h => (hi h).elim⟩
  choose Q hQpoly hQprop using hQ
  obtain ⟨T, hTfin, hT⟩ := (IsPolyhedron.finsetBiUnion s hQpoly).exists_simplicialComplex
  have : Finite T.faces := hTfin.to_subtype
  have hagree : ∀ i ∈ s, ∀ x ∈ Cc i, ∀ᶠ y in 𝓝 x, y ∈ T.space ↔ y ∈ M i := by
    intro i hi x hx
    obtain ⟨-, -, hnhds⟩ := hQprop i hi
    have hxS := hCM i hi hx
    obtain ⟨V, hV, hVQ⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hnhds x hx)
    have hfar : ∀ᶠ y in 𝓝 x, ∀ j ∈ s, j ≠ i → y ∉ Q j := by
      rw [Filter.eventually_all_finset]
      intro j hj
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall fun _ h => (h hji).elim
      · have hxQ : x ∉ Q j := fun hxQ => Set.disjoint_left.mp (hdisj i hi j hj (Ne.symm hji))
          hxS.1 ((hQprop j hj).2.1 hxQ).1
        filter_upwards [(hQpoly j).isClosed.isOpen_compl.mem_nhds hxQ] with y hy _ using hy
    have hP : ∀ᶠ y in 𝓝 x, y ∈ ({P i} : Set E)ᶜ := isOpen_compl_singleton.mem_nhds hxS.2
    filter_upwards [hV, hfar, hP] with y hyV hyfar hyP
    rw [hT]
    constructor
    · intro hyQ
      obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hyQ
      by_cases hji : j = i
      · rw [hji] at hyj
        exact ((hQprop i hi).2.1 hyj).1
      · exact (hyfar j hj hji hyj).elim
    · intro hyM
      exact mem_iUnion₂.mpr ⟨i, hi, hVQ ⟨hyV, hyM, hyP⟩⟩
  have hCc : IsCompact (⋃ i ∈ s, Cc i) := s.isCompact_biUnion hC
  have hCT : (⋃ i ∈ s, Cc i) ⊆ T.space := by
    rw [hT]
    exact iUnion₂_mono fun i hi => (hQprop i hi).1
  have hO : IsOpen (⋃ i ∈ s, {x | ∀ᶠ y in 𝓝 x, y ∈ T.space ↔ y ∈ M i}) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => isOpen_setOfPred_eventually_nhds
  have hCO : (⋃ i ∈ s, Cc i) ⊆ ⋃ i ∈ s, {x | ∀ᶠ y in 𝓝 x, y ∈ T.space ↔ y ∈ M i} :=
    iUnion₂_mono fun i hi x hx => hagree i hi x hx
  have hlink : ∀ J : Geometry.SimplicialComplex ℝ E, IsSubdivision J T → J.faces.Finite →
      ∀ v ∈ ⋃ i ∈ s, {x | ∀ᶠ y in 𝓝 x, y ∈ T.space ↔ y ∈ M i},
        ({v} : Finset E) ∈ J.faces →
          IsPLSphere 1 (SimplicialComplex.geometricLink J {v}).space ∨
            IsPLBall 1 (SimplicialComplex.geometricLink J {v}).space := by
    intro J hJ hJfin v hv hvJ
    have : Finite J.faces := hJfin.to_subtype
    obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.mp hv
    obtain ⟨ψ⟩ := hM i hi
    refine Or.inl (isPLSphere_one_geometricLink_of_homeomorph J Metric.isOpen_ball ψ hvJ ?_)
    rw [hJ.space_eq]
    exact hvi
  obtain ⟨T', L, hT', hT'fin, hLT', hL, -, hLnhds⟩ :=
    exists_isSubdivision_neighborhood_of_forall_geometricLink hCc hCT hO hCO hlink
  refine ⟨L, hT'fin.subset hLT', hL, fun i hi x hx => ?_⟩
  obtain ⟨V, hV, hVL⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (hLnhds x (mem_iUnion₂.mpr ⟨i, hi, hx⟩))
  have hLT : L.space ⊆ T.space := by
    intro y hy
    obtain ⟨σ, hσ, hyσ⟩ := L.mem_space_iff.mp hy
    rw [← hT'.space_eq]
    exact T'.convexHull_subset_space (hLT' hσ) hyσ
  filter_upwards [hagree i hi x hx, hV] with y hyT hyV
  rw [← hyT]
  exact ⟨fun hy => hLT hy, fun hy => hVL ⟨hyV, hy⟩⟩

end SurfacePieces

section TubeTopology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.isClosed {Ec Eint Ebd : Set E3} {P : E3} (hpc : IsPseudoCell Ec Eint Ebd P) :
    IsClosed Ec := by
  rw [hpc.carrierEq, ← hpc.closureEq]
  exact isClosed_closure

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3}

theorem IsTube.isCompact (ht : IsTube K N C D Dbd h N') : IsCompact N := by
  rw [ht.unionEq]
  exact ht.finite_vertices.isCompact_biUnion fun v hv =>
    (ht.dualBall v hv).isPolyhedron.isCompact

theorem IsTube.interior_eq_image_interior (ht : IsTube K N C D Dbd h N') :
    interior N' = h '' interior N := by
  rw [ht.imageEq]
  exact interior_image_eq_image_interior_of_isCompact ht.isCompact ht.continuousOn ht.injOn

theorem IsTube.image_space_subset_interior (ht : IsTube K N C D Dbd h N') :
    h '' K.space ⊆ interior N' := by
  rw [ht.interior_eq_image_interior]
  exact image_mono (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood)

theorem IsTube.isCompact_image_space (ht : IsTube K N C D Dbd h N') :
    IsCompact (h '' K.space) := by
  have : Finite K.faces := ht.facesFinite.to_subtype
  exact (isPolyhedron_space K).isCompact.image_of_continuousOn (ht.continuousOn.mono
    ((subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood).trans interior_subset))

theorem IsTube.disjoint_image_rim_interior (ht : IsTube K N C D Dbd h N')
    {e : Finset E3} (he : e ∈ K.faces) (hcard : e.card = 2) :
    Disjoint (h '' Dbd e) (interior N') := by
  rw [Set.disjoint_left, ht.interior_eq_image_interior]
  rintro _ ⟨x, hxD, rfl⟩ ⟨z, hz, hzx⟩
  have hxFr : x ∈ frontier N := by
    rw [← ht.splitProper e he hcard] at hxD
    exact hxD.2
  have hzx' : z = x := ht.injOn (interior_subset hz) (ht.isClosed.frontier_subset hxFr) hzx
  exact hxFr.2 (hzx' ▸ hz)

variable {Ec Eint Ebd : Finset E3 → Set E3} {Cpp : E3 → Set E3}

theorem IsHandleDecompositionOfTube.disjoint_rim_interior
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    {e : Finset E3} (he : e ∈ K.faces) (hcard : e.card = 2) : Disjoint (Ebd e) (interior N') := by
  rw [hd.rimEq e he hcard]
  exact hd.tube.disjoint_image_rim_interior he hcard

end TubeTopology

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem exists_isPolyhedralTubeNeighborhood
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) :
    ∃ XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK := by
  classical
  have ht := hd.tube
  have hKc := ht.isCompact_image_space
  obtain ⟨X₀, hX₀fin, hX₀, hKX₀, hX₀N'⟩ :=
    exists_isCombinatorialManifoldWithBoundary_neighborhood (n := 2) finrank_euclideanSpace_fin
      hKc isOpen_interior ht.image_space_subset_interior
  have : Finite X₀.faces := hX₀fin.to_subtype
  obtain ⟨B, hBfin, hB, hBspace⟩ :=
    hX₀.exists_isCombinatorialManifold_space_eq_frontier (n := 2) (by simp)
  have : Finite B.faces := hBfin.to_subtype
  have hX₀poly := isPolyhedron_space X₀
  have hX₀c : IsCompact X₀.space := hX₀poly.isCompact
  have hFrc : IsCompact (frontier X₀.space) :=
    hX₀c.of_isClosed_subset isClosed_frontier hX₀c.isClosed.frontier_subset
  have hUo : IsOpen (interior N' \ h '' K.space) := isOpen_interior.sdiff hKc.isClosed
  have hFrUo : frontier X₀.space ⊆ interior N' \ h '' K.space := fun x hx =>
    ⟨hX₀N' (hX₀c.isClosed.frontier_subset hx), fun hxK => hx.2 (hKX₀ hxK)⟩
  obtain ⟨δ, hδ, hδU⟩ := hFrc.exists_cthickening_subset_open hUo hFrUo
  let edges : Finset (Finset (EuclideanSpace ℝ (Fin 3))) :=
    ht.facesFinite.toFinset.filter fun e => e.card = 2
  have hedges : ∀ e, e ∈ edges ↔ e ∈ K.faces ∧ e.card = 2 := fun e => by simp [edges]
  have hCe : ∀ e ∈ edges, Ec e ∩ Metric.cthickening δ (frontier X₀.space) ⊆
      Eint e \ {h (e.centroid ℝ id)} := by
    rintro e he x ⟨hxE, hxδ⟩
    obtain ⟨he₁, he₂⟩ := (hedges e).mp he
    have hpc := hd.pseudoCell e he₁ he₂
    have hxU := hδU hxδ
    rw [hpc.carrierEq] at hxE
    rcases hxE with hxI | hxB
    · refine ⟨hxI, fun hxP => hxU.2 ?_⟩
      rw [mem_singleton_iff.mp hxP]
      exact ⟨_, K.convexHull_subset_space he₁
        (e.centroid_mem_convexHull (K.nonempty_of_mem_faces he₁)), rfl⟩
    · exact (Set.disjoint_left.mp (hd.disjoint_rim_interior he₁ he₂) hxB hxU.1).elim
  obtain ⟨L, hLfin, hL, hLagree⟩ :=
    exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff edges (M := Eint)
    (P := fun e => h (e.centroid ℝ id))
    (Cc := fun e => Ec e ∩ Metric.cthickening δ (frontier X₀.space))
    (fun e he => (hd.pseudoCell e ((hedges e).mp he).1 ((hedges e).mp he).2).isOpenCell)
    (fun e he => (hd.pseudoCell e ((hedges e).mp he).1 ((hedges e).mp he).2).regular)
    (fun e he g hg heg => by
      obtain ⟨he₁, he₂⟩ := (hedges e).mp he
      obtain ⟨hg₁, hg₂⟩ := (hedges g).mp hg
      have hdisj := hd.pseudoCellDisjoint e he₁ he₂ g hg₁ hg₂ heg
      rw [(hd.pseudoCell e he₁ he₂).carrierEq, (hd.pseudoCell g hg₁ hg₂).carrierEq] at hdisj
      exact hdisj.mono subset_union_left subset_union_left)
    (fun e he => hFrc.cthickening.inter_left
      (hd.pseudoCell e ((hedges e).mp he).1 ((hedges e).mp he).2).isClosed)
    hCe
  have : Finite L.faces := hLfin.to_subtype
  obtain ⟨f, -, hf, hfδ, hfix, -, -, -, hcross⟩ :=
    exists_small_homeomorph_generalPosition B L hB.isCombinatorialManifoldWithBoundary hL
      finrank_euclideanSpace_fin hUo (by rw [hBspace]; exact hFrUo) hδ
  have hfX : IsPLHomeomorphOn f X₀.space (f '' X₀.space) := hf.restrict hX₀poly (subset_univ _)
  obtain ⟨XK, hXKfin, hXK⟩ :=
    (hX₀poly.image_of_isPiecewiseAffineOn hfX.isPiecewiseAffineOn
      hfX.bijOn.injOn).exists_simplicialComplex
  have : Finite XK.faces := hXKfin.to_subtype
  have hint : f '' interior X₀.space = interior XK.space := by
    rw [hXK]
    exact hfX.image_interior rfl
  have hfr : f '' frontier X₀.space = frontier XK.space := by
    rw [hXK]
    exact hfX.image_frontier rfl hX₀c.isClosed
      (hX₀c.image_of_continuousOn hfX.isPiecewiseAffineOn.continuousOn).isClosed
  have hsubN' : XK.space ⊆ interior N' := by
    rw [hXK]
    rintro _ ⟨y, hy, rfl⟩
    by_cases hyU : y ∈ interior N' \ h '' K.space
    · by_contra hfy
      have hfyU : f y ∉ interior N' \ h '' K.space := fun hfy' => hfy hfy'.1
      have hff : f (f y) = f y := hfix hfyU
      have hyy : f y = y := hf.bijOn.injOn (mem_univ _) (mem_univ _) hff
      exact hfyU (by rw [hyy]; exact hyU)
    · rw [show f y = y from hfix hyU]
      exact hX₀N' hy
  refine ⟨XK, hXKfin, ?_, ?_, hsubN',
    fun e he hcard => (hd.disjoint_rim_interior he hcard).mono_right hsubN', ?_⟩
  · have hfX' : IsPLHomeomorphOn f X₀.space XK.space := by
      rw [hXK]
      exact hfX
    exact hX₀.of_isPLHomeomorphOn hfX'
  · rw [← subset_interior_iff_mem_nhdsSet, ← hint]
    intro x hx
    exact ⟨x, hKX₀ hx, hfix fun hxU => hxU.2 hx⟩
  · rintro e he hcard x ⟨hxE, hxF⟩
    have he' : e ∈ edges := (hedges e).mpr ⟨he, hcard⟩
    rw [← hfr] at hxF
    obtain ⟨y, hyFr, rfl⟩ := hxF
    have hxC : f y ∈ Ec e ∩ Metric.cthickening δ (frontier X₀.space) :=
      ⟨hxE, Metric.mem_cthickening_of_dist_le (f y) y δ _ hyFr (hfδ y).le⟩
    have hagree := hLagree e he' (f y) hxC
    have hxL : f y ∈ L.space := hagree.self_of_nhds.mpr (hCe e he' hxC).1
    have hyB : y ∈ B.space := by
      rw [hBspace]
      exact hyFr
    refine ((hcross (f y) ⟨⟨y, hyB, rfl⟩, hxL⟩).congr ?_ hagree).symm
    exact Filter.Eventually.of_forall fun z => by rw [hBspace, hfr]

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
