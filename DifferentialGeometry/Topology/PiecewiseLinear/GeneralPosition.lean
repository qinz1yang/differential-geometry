import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import Mathlib.Topology.Algebra.AffineSubspace

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem interior_eq_empty_of_affineSubspace_ne_top (s : AffineSubspace ℝ E) (hs : s ≠ ⊤) :
    interior (s : Set E) = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hxs : x ∈ s := interior_subset hx
  have hcont : ContinuousAt (fun v : E => v + x) (0 : E) := by fun_prop
  have hpre : (fun v : E => v + x) ⁻¹' (s : Set E) ∈ 𝓝 (0 : E) :=
    hcont.preimage_mem_nhds
      (by simpa only [zero_add] using mem_interior_iff_mem_nhds.mp hx)
  have hdir : (s.direction : Set E) ∈ 𝓝 (0 : E) := by
    apply Filter.mem_of_superset hpre
    intro v hv
    change v ∈ s.direction
    have hmem := AffineSubspace.vsub_mem_direction hv hxs
    simpa only [vsub_eq_sub, add_sub_cancel_right] using hmem
  exact hs ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x, hxs⟩).mp
    (s.direction.eq_top_of_nonempty_interior' ⟨0, mem_interior_iff_mem_nhds.mpr hdir⟩))

theorem exists_mem_ball_notMem_affineSubspaces [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]
    (s : ι → AffineSubspace ℝ E) (hs : ∀ i, s i ≠ ⊤) {x : E} {ε : ℝ} (hε : 0 < ε) :
    ∃ y : E, dist y x < ε ∧ ∀ i, y ∉ s i := by
  classical
  have hclosed : ∀ i, IsClosed (s i : Set E) := fun i =>
    ((s i).isClosed_direction_iff).mp ((s i).direction.closed_of_finiteDimensional)
  have hint : interior (⋃ i, (s i : Set E)) = ∅ :=
    interior_iUnion_eq_empty_of_finite hclosed fun i =>
      interior_eq_empty_of_affineSubspace_ne_top (s i) (hs i)
  by_contra h
  have hsub : ball x ε ⊆ ⋃ i, (s i : Set E) := by
    intro y hy
    by_contra hyS
    apply h
    exact ⟨y, hy, fun i hi => hyS (mem_iUnion.mpr ⟨i, hi⟩)⟩
  have hx : x ∈ interior (⋃ i, (s i : Set E)) :=
    interior_maximal hsub isOpen_ball (mem_ball_self hε)
  rw [hint] at hx
  exact hx

theorem isPLHomeomorphOn_add_const [FiniteDimensional ℝ E] (a : E) :
    IsPLHomeomorphOn (fun x => x + a) univ univ := by
  have hbij : BijOn (fun x : E => x + a) univ univ :=
    ⟨mapsTo_univ _ _, fun _ _ _ _ h => add_right_cancel h,
      fun y _ => ⟨y - a, mem_univ _, sub_add_cancel _ _⟩⟩
  refine ⟨hbij, ?_, ?_⟩
  · exact isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E + AffineMap.const ℝ E a) isOpen_univ
  · have hpl : IsPiecewiseAffineOn (fun y : E => y - a) univ :=
      isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E - AffineMap.const ℝ E a) isOpen_univ
    refine hpl.congr fun y hy => ?_
    exact eq_sub_iff_add_eq.mpr (hbij.invOn_invFunOn.2 hy)

open Classical in
theorem exists_small_translation_transverse_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E, ‖a‖ < ε ∧ IsPLHomeomorphOn (fun x => x + a) univ univ ∧
      ∀ s ∈ K.faces, ∀ t ∈ L.faces,
        ((fun x => x + a) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
          vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
  let I := {p : K.faces × L.faces //
    vectorSpan ℝ (p.1.val : Set E) ⊔ vectorSpan ℝ (p.2.val : Set E) ≠ ⊤}
  let B : I → AffineSubspace ℝ E := fun p =>
    AffineSubspace.mk' (p.val.2.val.centroid ℝ id - p.val.1.val.centroid ℝ id)
      (vectorSpan ℝ (p.val.1.val : Set E) ⊔ vectorSpan ℝ (p.val.2.val : Set E))
  have hB : ∀ p, B p ≠ ⊤ := by
    intro p h
    apply p.property
    have hdir := congrArg AffineSubspace.direction h
    simpa only [B, AffineSubspace.direction_mk', AffineSubspace.direction_top] using hdir
  obtain ⟨a, ha, havoid⟩ := exists_mem_ball_notMem_affineSubspaces B hB (x := 0) hε
  refine ⟨a, by simpa only [dist_zero_right] using ha, isPLHomeomorphOn_add_const a, ?_⟩
  intro s hs t ht hinter
  by_contra hdir
  let p : I := ⟨(⟨s, hs⟩, ⟨t, ht⟩), hdir⟩
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hinter
  have hsC : s.centroid ℝ id ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan _ (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs))
  have htC : t.centroid ℝ id ∈ affineSpan ℝ (t : Set E) :=
    convexHull_subset_affineSpan _ (t.centroid_mem_convexHull (L.nonempty_of_mem_faces ht))
  have hxdir : x - s.centroid ℝ id ∈ vectorSpan ℝ (s : Set E) := by
    simpa only [vsub_eq_sub, direction_affineSpan] using
      AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hx) hsC
  have hydir : x + a - t.centroid ℝ id ∈ vectorSpan ℝ (t : Set E) := by
    simpa only [vsub_eq_sub, direction_affineSpan] using
      AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hy) htC
  apply havoid p
  change a ∈ AffineSubspace.mk' (t.centroid ℝ id - s.centroid ℝ id)
    (vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E))
  rw [AffineSubspace.mem_mk', vsub_eq_sub]
  have heq : a - (t.centroid ℝ id - s.centroid ℝ id) =
      (x + a - t.centroid ℝ id) - (x - s.centroid ℝ id) := by abel
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right hydir) (Submodule.mem_sup_left hxdir)

end DifferentialGeometry.Topology.PiecewiseLinear
