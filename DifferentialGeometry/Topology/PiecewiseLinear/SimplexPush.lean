/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage
import DifferentialGeometry.Topology.PiecewiseLinear.PushProperty

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem coneComplex_simplexBoundary_space {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card) {p : E}
    (hp : p ∈ openSimplex T) :
    (coneComplex (isConeBase_simplexBoundary hT hcard hp)).space = convexHull ℝ (T : Set E) := by
  ext x
  rw [mem_coneComplex_space_iff]
  constructor
  · rintro (hxp | ⟨z, hz, s, hs, hs', rfl⟩)
    · rw [hxp]
      exact openSimplex_subset_convexHull _ hp
    · have hzT : z ∈ convexHull ℝ (T : Set E) :=
        simplexComplex_space_subset T hT
          (space_mono_of_faces_subset (simplexBoundary_faces_subset_simplexComplex T hT) hz)
      rw [add_smul_sub_eq_combo]
      exact (convex_convexHull ℝ _) (openSimplex_subset_convexHull _ hp) hzT
        (by linarith) hs.le (by ring)
  · intro hx
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase hT hp hx
    rcases exists_combo_of_mem_convexHull_insert (notMem_erase_of_mem_openSimplex hT hp hv) hxv with
      hxp | ⟨z, hz, s, hs, hs', rfl⟩
    · exact Or.inl hxp
    · exact Or.inr ⟨z, (simplexBoundary T hT).convexHull_subset_space
        (erase_mem_simplexBoundary_faces hT hcard hv) hz, s, hs, hs', rfl⟩

open Classical in
theorem exists_isPLHomeomorphOn_push_simplex [FiniteDimensional ℝ E] [dE : DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∉ T) (hTa : AffineIndependent ℝ ((↑) : ↥(insert a T : Finset E) → E))
    {N : Set E} (hN : IsPolyhedron N)
    (hTN : convexHull ℝ ((insert a T : Finset E) : Set E) \ (simplexBoundary T hT).space ⊆ interior
        N) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h id Nᶜ ∧
      EqOn h id (simplexBoundary T hT).space ∧
      h '' convexHull ℝ (T : Set E) =
        ⋃ v ∈ T, convexHull ℝ ((insert a (T.erase v) : Finset E) : Set E) := by
  cases Subsingleton.elim dE (Classical.decEq E)
  let p := T.centroid ℝ id
  have hp : p ∈ openSimplex T := centroid_mem_openSimplex (Finset.card_pos.mp (by omega))
  let L := simplexBoundary T hT
  have : Finite L.faces := (simplexBoundary_faces_finite T hT).to_subtype
  let γ : unitInterval → E := fun t => p + (t : ℝ) • (a - p)
  have hγ0 : γ 0 = p := by simp [γ]
  have hγ1 : γ 1 = a := by simp [γ]
  have hγcont : Continuous γ := continuous_const.add (continuous_subtype_val.smul continuous_const)
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull _ hp
  have hpSpan : p ∈ affineSpan ℝ (T : Set E) := convexHull_subset_affineSpan _ hpT
  have haSpan : a ∉ affineSpan ℝ (T : Set E) := notMem_affineSpan_of_affineIndependent_insert ha hTa
  have hbase : ∀ t, IsConeBase (γ t) L := by
    intro t
    by_cases ht : (t : ℝ) = 0
    · have hγt : γ t = p := by simp [γ, ht]
      rw [hγt]
      exact isConeBase_simplexBoundary hT hcard hp
    · have hγSpan : γ t ∉ affineSpan ℝ (T : Set E) := by
        intro hmem
        apply haSpan
        have h := (affineSpan ℝ (T : Set E)).smul_vsub_vadd_mem ((t : ℝ)⁻¹) hmem hpSpan hpSpan
        change (t : ℝ)⁻¹ • (γ t - p) + p ∈ affineSpan ℝ (T : Set E) at h
        simpa only [γ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul,
          sub_add_cancel] using h
      exact (isConeBase_simplexComplex T hT
        (fun h => hγSpan (subset_affineSpan ℝ _ h))
        (affineIndependent_insert_of_notMem_affineSpan hT hγSpan)).of_faces_subset
        (simplexBoundary_faces_subset_simplexComplex T hT)
  have hγT : ∀ t, γ t ∈ convexHull ℝ ((insert a T : Finset E) : Set E) := by
    intro t
    change p + (t : ℝ) • (a - p) ∈ _
    rw [add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _)
      (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert a T)) hpT)
      (subset_convexHull ℝ _ (Finset.mem_insert_self a T))
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  have hLN : ∀ t, (coneComplex (hbase t)).space \ L.space ⊆ interior N := by
    intro t x hx
    apply hTN
    refine ⟨?_, hx.2⟩
    rcases (mem_coneComplex_space_iff (hbase t)).mp hx.1 with rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · exact hγT t
    · have hzT : z ∈ convexHull ℝ (T : Set E) :=
        simplexComplex_space_subset T hT
          (space_mono_of_faces_subset (simplexBoundary_faces_subset_simplexComplex T hT) hz)
      rw [add_smul_sub_eq_combo]
      exact (convex_convexHull ℝ _) (hγT t)
        (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert a T)) hzT)
        (by linarith) hs.le (by ring)
  obtain ⟨h, hh, hfix, hpoint, hrad⟩ :=
    exists_isPLHomeomorphOn_coneComplex_of_continuous γ hγcont L hbase hN hLN 0 1
  rw [hγ0, hγ1] at hpoint hrad
  refine ⟨h, hh, hfix, ?_, ?_⟩
  · intro z hz
    have h := hrad z hz 1 zero_le_one le_rfl
    simpa only [one_smul, add_sub_cancel, id_eq] using h
  · have hCa : IsConeBase a L := by simpa only [hγ1] using hbase 1
    have hCp : IsConeBase p L := isConeBase_simplexBoundary hT hcard hp
    have hsource : (coneComplex hCp).space = convexHull ℝ (T : Set E) :=
      coneComplex_simplexBoundary_space hT hcard hp
    have himage : h '' (coneComplex hCp).space = (coneComplex hCa).space := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases (mem_coneComplex_space_iff hCp).mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
        · rw [hpoint]
          exact apex_mem_coneComplex_space hCa
        · rw [hrad z hz s hs.le hs']
          exact (mem_coneComplex_space_iff hCa).mpr (Or.inr ⟨z, hz, s, hs, hs', rfl⟩)
      · intro hy
        rcases (mem_coneComplex_space_iff hCa).mp hy with rfl | ⟨z, hz, s, hs, hs', rfl⟩
        · exact ⟨p, apex_mem_coneComplex_space hCp, hpoint⟩
        · exact ⟨p + s • (z - p),
            (mem_coneComplex_space_iff hCp).mpr (Or.inr ⟨z, hz, s, hs, hs', rfl⟩),
            hrad z hz s hs.le hs'⟩
    rw [← hsource, himage]
    ext x
    constructor
    · intro hx
      rcases (mem_coneComplex_space_iff hCa).mp hx with hxa | ⟨z, hz, s, hs, hs', rfl⟩
      · rw [hxa]
        obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
        exact mem_iUnion₂.mpr ⟨v, hv, subset_convexHull ℝ _ (Finset.mem_insert_self a _)⟩
      · rw [show L.space = ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E) from
          simplexBoundary_space T hT hcard] at hz
        obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hz
        exact mem_iUnion₂.mpr ⟨v, hv, mem_convexHull_insert_of_combo hzv hs.le hs'⟩
    · intro hx
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      exact (coneComplex hCa).convexHull_subset_space
        (Or.inr (Or.inr ⟨T.erase v, erase_mem_simplexBoundary_faces hT hcard hv, rfl⟩)) hxv

open Classical in
theorem closure_frontier_convexHull_sdiff_face [DecidableEq E] (T : Finset E) {a : E} (ha : a ∉ T)
    (hTa : AffineIndependent ℝ ((↑) : ↥(insert a T : Finset E) → E))
    (hspan : affineSpan ℝ ((insert a T : Finset E) : Set E) = ⊤) :
    closure (frontier (convexHull ℝ ((insert a T : Finset E) : Set E)) \ convexHull ℝ (T : Set E)) =
      ⋃ v ∈ T, convexHull ℝ ((insert a (T.erase v) : Finset E) : Set E) := by
  let R : Set E := ⋃ v ∈ T, convexHull ℝ ((insert a (T.erase v) : Finset E) : Set E)
  have hfront : frontier (convexHull ℝ ((insert a T : Finset E) : Set E)) =
      convexHull ℝ (T : Set E) ∪ R := by
    rw [frontier_convexHull_eq_biUnion_erase _ hTa hspan]
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hx⟩ := mem_iUnion₂.mp hx
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Or.inl (by simpa only [Finset.erase_insert ha] using hx)
      · exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, by
          simpa only [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hv ha).symm] using hx⟩)
    · rintro (hx | hx)
      · exact mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a T, by
          simpa only [Finset.erase_insert ha] using hx⟩
      · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨v, Finset.mem_insert_of_mem hv, by
          simpa only [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hv ha).symm] using hxv⟩
  have hRclosed : IsClosed R := T.finite_toSet.isClosed_biUnion fun v _ =>
    ((insert a (T.erase v) : Finset E).finite_toSet.isCompact_convexHull ℝ).isClosed
  apply Subset.antisymm
  · apply closure_minimal _ hRclosed
    intro x hx
    rw [hfront] at hx
    exact hx.1.resolve_left hx.2
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    apply (convexHull_subset_closure_openSimplex (Finset.insert_nonempty a (T.erase v))).trans _ hxv
    apply closure_mono
    intro y hy
    refine ⟨?_, fun hyT => ?_⟩
    · rw [hfront]
      exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, openSimplex_subset_convexHull _ hy⟩)
    · have hsub := subset_of_mem_openSimplex_of_mem_convexHull hTa
        (Finset.insert_subset_insert a (Finset.erase_subset v T))
        (Finset.subset_insert a T) hy hyT
      exact ha (hsub (Finset.mem_insert_self a _))

open Classical in
theorem hasPushPropertyAt_convexHull_simplex_face
    (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 3))) (hcard : T.card = 3)
    {a : EuclideanSpace ℝ (Fin 3)} (ha : a ∉ T)
    (hTa : AffineIndependent ℝ ((↑) : ↥(insert a T : Finset _) → EuclideanSpace ℝ (Fin 3))) :
    HasPushPropertyAt (convexHull ℝ ((insert a T : Finset _) : Set _)) (convexHull ℝ (T : Set _)) :=
        by
  have hTaCard : (insert a T).card = 4 := by rw [Finset.card_insert_of_notMem ha, hcard]
  have hspan : affineSpan ℝ ((insert a T : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) = ⊤ := by
    have h := hTa.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa only [Fintype.card_coe, finrank_euclideanSpace, Fintype.card_fin] using hTaCard)
    have hrange : range ((↑) : ↥(insert a T : Finset _) → EuclideanSpace ℝ (Fin 3)) =
        ((insert a T : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) := Subtype.range_coe
    exact (congrArg (affineSpan ℝ) hrange).symm.trans h
  refine ⟨isPLBall_convexHull_of_affineIndependent _ hTa hTaCard,
    isPLBall_convexHull_of_affineIndependent _ hT hcard, ?_, ?_⟩
  · intro x hx
    rw [frontier_convexHull_eq_biUnion_erase _ hTa hspan]
    exact mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a T, by
      simpa only [Finset.erase_insert ha] using hx⟩
  · intro f hf N hN hCN
    rw [image_stdSimplexBoundary_of_isPLHomeomorphOn_convexHull hT hcard hf] at hCN
    obtain ⟨h, hh, hfix, -, himage⟩ := exists_isPLHomeomorphOn_push_simplex T hT (by omega) ha hTa
        hN hCN
    refine ⟨h, hh, ?_, hfix⟩
    rw [closure_frontier_convexHull_sdiff_face T ha hTa hspan]
    exact himage

end DifferentialGeometry.Topology.PiecewiseLinear
