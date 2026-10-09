import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyLevel

/-!
# FC42 packet T4a §2: how the final pieces meet

For a certificate with `μ(D) = 0` (no sphere seam, no bad vertex) and a complete cycle partition
`P` (ASM-CYC3), the final pieces of review 40 §3.6 are the cycle unions `P.roundedUnion j`, the
non-ball vertices, the edge-circle pieces and the rounded circle-region pieces. This file proves the
intersection laws among the first three (the "positive side" family):

* `handleEnd_ne_of_not_isBall`: with `μ = 0` every handle end is a ball;
* `disjoint_roundedUnion_vertex`, `disjoint_roundedUnion_edgeCircle`: a cycle union meets no
  non-ball vertex and no edge circle (balls: ASM-CYC2's H1 with the partitioned face of the ball;
  handles: the handle–vertex incidence; fillets: the full rim chart excludes other pieces, G2);
* `false_of_mem_vertex_region_piece` (no third piece at a region point of a vertex, G2) and
  `disjoint_vertex_edgeCircle`: a non-ball vertex meets no edge circle;
* `vertex_inter_vertex_subset_seamTorus`: two different vertices meet only along vertex–vertex seam
  tori (V4 `face_disjoint`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- With no bad vertex, every handle end is a ball, so no handle ends on a non-ball vertex. -/
theorem handleEnd_ne_of_not_isBall (hbad : D.badVertexCount = 0) {k : Fin D.vertexCount}
    (hk : ¬ (D.vertex k).IsBall) (h : Fin D.handleCount) (b : Bool) : D.handleEnd h b ≠ k :=
  fun heq => hk (heq ▸ D.isBall_handleEnd
    (fun f hf hS => D.partitionedSphereFace_ball_of_badVertexCount_eq_zero hbad f hf hS) h b)

/-- **A cycle union meets no non-ball vertex.** -/
theorem disjoint_roundedUnion_vertex (hbad : D.badVertexCount = 0) (P : D.CyclePartition)
    (j : Fin P.cnt) (k : Fin D.vertexCount) (hk : ¬ (D.vertex k).IsBall) :
    Disjoint (range (P.roundedUnion j).map) (D.vertex k).image := by
  rw [P.range_roundedUnion, Set.disjoint_left]
  intro x hxU hxk
  rcases P.unionSet_subset_coreSet_union_rimTargets j hxU with hc | hr
  · rcases hc with hb | hh
    · obtain ⟨k', hk'⟩ := mem_iUnion.mp hb
      rw [P.range_ballPiece] at hk'
      have hne : P.ball j k' ≠ k := fun h => hk (h ▸ P.ball_isBall j k')
      exact Set.disjoint_left.mp (D.ball_image_disjoint_vertex_image (P.ball_isBall j k')
        (P.exists_partitioned_face j k') hne) hk' hxk
    · obtain ⟨k', hk'⟩ := mem_iUnion.mp hh
      rw [P.range_cycleHandle] at hk'
      have h := (D.handle_inter_vertex_image (P.handle j k') k).subset ⟨hk', hxk⟩
      obtain ⟨b, hb, -⟩ := mem_iUnion₂.mp h
      exact D.handleEnd_ne_of_not_isBall hbad hk _ b hb
  · obtain ⟨k', b, hT⟩ := mem_iUnion₂.mp hr
    exact Set.disjoint_left.mp (D.disjoint_vertex_rimChart_target _ _ k
      (D.handleEnd_ne_of_not_isBall hbad hk _ _).symm) hxk hT

/-- **A cycle union meets no edge circle.** -/
theorem disjoint_roundedUnion_edgeCircle (P : D.CyclePartition) (j : Fin P.cnt)
    (e : Fin D.edgeCircleCount) :
    Disjoint (range (P.roundedUnion j).map) (range (D.edgeCircle e).piece.map) := by
  rw [P.range_roundedUnion, Set.disjoint_left]
  intro x hxU hxe
  rcases P.unionSet_subset_coreSet_union_rimTargets j hxU with hc | hr
  · rcases hc with hb | hh
    · obtain ⟨k', hk'⟩ := mem_iUnion.mp hb
      rw [P.range_ballPiece] at hk'
      exact Set.disjoint_left.mp (D.ball_image_disjoint_edgeCircle (P.ball_isBall j k')
        (P.exists_partitioned_face j k') e) hk' hxe
    · obtain ⟨k', hk'⟩ := mem_iUnion.mp hh
      rw [P.range_cycleHandle] at hk'
      exact Set.disjoint_left.mp (D.handle_image_disjoint_edgeCircle _ e) hk' hxe
  · obtain ⟨k', b, hT⟩ := mem_iUnion₂.mp hr
    exact Set.disjoint_left.mp (D.disjoint_edgeCircle_rimChart_target _ _ e) hxe hT

/-- **No third piece at a region point of a vertex.** At a point of a vertex (not a handle end)
lying in the circle region, the region and the vertex enter along half-spaces, so no full-rank
image with interior disjoint from both can pass through the point. -/
theorem false_of_mem_vertex_region_piece (k : Fin D.vertexCount)
    (hk : ∀ h b, D.handleEnd h b ≠ k) {x : W.Carrier} (hxk : x ∈ (D.vertex k).image)
    (hxR : x ∈ D.circ.region)
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H' M] [IsManifold I ∞ M] (hdim : Module.finrank ℝ E' = 3) {F : M → W.Carrier}
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q)) {q : M}
    (hq : F q = x) (hFR : Disjoint (interior D.circ.region) (interior (range F)))
    (hFk : Disjoint (interior (D.vertex k).image) (interior (range F))) : False := by
  subst hq
  have hxZ := D.mem_roundedLevel_of_mem_vertex_of_mem_region k hk hxk hxR
  have hxd : F q ∈ D.circ.domain := D.circ.region_subset_domain hxR
  have hxW : F q ∈ W.interior := D.circ.domain_interior hxd
  have hxc := D.not_mem_rimCore_of_mem_vertex k hk hxk
  obtain ⟨z, hz, hzx⟩ := hxR
  have hzx' : z = ⟨F q, hxd⟩ := Subtype.ext hzx
  have hb : D.circ.proj ⟨F q, hxd⟩ ∈ D.circ.cornerBase := hzx' ▸ hz
  have hA : ∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 (extChartAt W.model (F q) (F q)),
        ε * ‖y - extChartAt W.model (F q) (F q)‖ < κ (y - extChartAt W.model (F q) (F q)) →
          (extChartAt W.model (F q)).symm y ∈ interior D.circ.region := by
    rcases D.circ.depth_cases hb with h0 | ⟨l, hl, hother⟩ | ⟨k0, hk0⟩
    · exact absurd (D.circ.mem_interior_region_of_defining_neg hxd h0)
        (D.not_mem_interior_region_of_mem_roundedLevel hxZ hxc)
    · exact D.circ.exists_entering hxd hl hother
    · obtain ⟨h, b, -, -, hT⟩ := D.exists_rimCircle_of_proj_eq_corner hxd hk0
      exact absurd hT (Set.disjoint_left.mp
        (D.disjoint_vertex_rimChart_target h b k (hk h b).symm) hxk)
  have hxb : F q ∈ (D.vertex k).boundaryImage :=
    mem_boundaryImage_of_not_mem_interior hxk (D.not_mem_interior_vertex_of_mem_roundedLevel k hxZ)
  exact false_of_two_entering_and_piece hdim hF hbij q hA (Vertex.exists_entering hxb)
    (D.circ_vertex_disjoint k) hFR hFk

/-- **A non-ball vertex meets no edge circle.** -/
theorem disjoint_vertex_edgeCircle (hbad : D.badVertexCount = 0) (k : Fin D.vertexCount)
    (hk : ¬ (D.vertex k).IsBall) (e : Fin D.edgeCircleCount) :
    Disjoint (D.vertex k).image (range (D.edgeCircle e).piece.map) := by
  rw [Set.disjoint_left]
  rintro x hxk ⟨q, rfl⟩
  by_cases hq : (𝓡∂ 3).IsInteriorPoint q
  · have hxi := (D.edgeCircle e).piece.toPieceFold.map_mem_interior_range hq
    rw [Vertex.image_eq_range_piece] at hxk
    obtain ⟨w, hw1, hw2⟩ := inter_interior_range_nonempty finrank_euclideanSpace_fin
      (D.vertex k).piece.smooth (D.vertex k).piece.mfderiv_bijective isOpen_interior ⟨_, hxi, hxk⟩
    rw [← Vertex.image_eq_range_piece] at hw2
    exact Set.disjoint_left.mp (D.edgeCircle_vertex_disjoint e k) hw1 hw2
  · have hqb : (𝓡∂ 3).IsBoundaryPoint q :=
      ((𝓡∂ 3).isBoundaryPoint_iff_not_isInteriorPoint q).mpr hq
    have hxR : (D.edgeCircle e).piece.map q ∈ D.circ.region := D.edgeCircle_vertical e ⟨q, hqb, rfl⟩
    exact D.false_of_mem_vertex_region_piece k (D.handleEnd_ne_of_not_isBall hbad hk) hxk hxR
      finrank_euclideanSpace_fin (D.edgeCircle e).piece.smooth
      (D.edgeCircle e).piece.mfderiv_bijective rfl (D.circ_edgeCircle_disjoint e)
      (D.edgeCircle_vertex_disjoint e k).symm

/-- **Two vertices meet only along vertex–vertex seam tori.** -/
theorem vertex_inter_vertex_subset_seamTorus (hsph : D.sphereSeamCount = 0)
    {k k' : Fin D.vertexCount} (hkk' : k ≠ k') :
    (D.vertex k).image ∩ (D.vertex k').image ⊆
      ⋃ (c : Fin D.torusSeamCount) (_ : D.IsVertexSeam c), D.seamTorus c := by
  rintro x ⟨hxk, hxk'⟩
  have hb : x ∈ (D.vertex k).boundaryImage :=
    mem_boundaryImage_of_not_mem_interior hxk (D.not_mem_interior_of_mem_two hkk' hxk')
  have hb' : x ∈ (D.vertex k').boundaryImage :=
    mem_boundaryImage_of_not_mem_interior hxk' (D.not_mem_interior_of_mem_two hkk'.symm hxk)
  rw [← D.face_exhausted] at hb hb'
  obtain ⟨f, hfo, hxf⟩ := mem_iUnion₂.mp hb
  obtain ⟨f', hfo', hxf'⟩ := mem_iUnion₂.mp hb'
  have hff : f ≠ f' := fun h => hkk' (hfo.symm.trans (h ▸ hfo'))
  by_contra hnot
  refine Set.disjoint_left.mp (D.face_disjoint f f' hff
    (fun c => absurd c.2 (by omega)) ?_) hxf hxf'
  rintro c b ⟨hc, hc'⟩
  apply hnot
  obtain ⟨hface, hside⟩ := D.face_torusSeam f c b hc
  obtain ⟨-, hside'⟩ := D.face_torusSeam f' c (!b) hc'
  have h1 : (D.torusSide c b).isSome := by rw [hside]; rfl
  have h2 : (D.torusSide c (!b)).isSome := by rw [hside']; rfl
  have hxS : x ∈ D.seamTorus c := by
    rw [seamTorus, ← hface]
    exact hxf
  refine mem_iUnion₂.mpr ⟨c, ?_, hxS⟩
  cases b
  · exact ⟨h2, h1⟩
  · exact ⟨h1, h2⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
