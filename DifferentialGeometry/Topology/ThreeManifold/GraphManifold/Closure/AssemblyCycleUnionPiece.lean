import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleUnionSetApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleIncidence

/-!
# FC42 packet H3a, part 3: the rounded union of a cycle is one B1 piece

`unionSet j` (part 2) is relatively OPEN in the closed complement `S = roundedComplement` of the
open rounded circle region (`exists_isOpen_inter_roundedComplement_eq`): in the cycle's rim charts
`S` is the `ψ_std ≤ 0` side; elsewhere the other closed pieces (other vertices, other handles, edge
circles, the closed rim boxes — lane ASM-CYC2's packet H1) avoid a neighbourhood, so `S` is locally
the cycle's balls and handles plus circle-region points with `ρ = 0`, and the latter are excluded by
regularity (`ρ > 0` occurs near every zero, and off the boxes `ρ ≤ 0` on the circle region). With
closedness and connectedness (part 2), `unionSet j` is a component of `S`; the B1-complement
`exists_pieces_of_interior_superlevel` (defining function on the open domain only) gives the piece
`roundedUnion j` with range `unionSet j` (`exists_pieceEmbedding_unionSet`), in `W.interior`, whose
model boundary is the zero level of the COMMON `ρ` (`image_boundary_roundedUnion`, review 42 §3.2).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsP_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothP_ASMCYC3 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskChartsP_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothP_ASMCYC3 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

namespace DecompositionCertificate

namespace CyclePartition

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {D : DecompositionCertificate W E}
  (P : D.CyclePartition)

/-- The closed pieces that cycle `j` must avoid: the other vertices, the other handles, the edge
circle pieces and the closed unit boxes of all rim charts. -/
def awaySet (j : Fin P.cnt) : Set W.Carrier :=
  ((⋃ (v : Fin D.vertexCount) (_ : ∀ k, P.ball j k ≠ v), (D.vertex v).image) ∪
    ⋃ (h : Fin D.handleCount) (_ : ∀ k, P.handle j k ≠ h), range (D.handle h).map) ∪
  ((⋃ e, range (D.edgeCircle e).piece.map) ∪ D.rimCore)

theorem isClosed_awaySet (j : Fin P.cnt) : IsClosed (P.awaySet j) := by
  refine ((isClosed_iUnion_of_finite fun v => isClosed_iUnion_of_finite fun _ => ?_).union
    (isClosed_iUnion_of_finite fun h => isClosed_iUnion_of_finite fun _ =>
      (isCompact_range (D.handle h).smooth.continuous).isClosed)).union
    ((isClosed_iUnion_of_finite fun e => (D.edgeCircle e).piece.isClosed_range).union
      D.isClosed_rimCore)
  rw [Vertex.image_eq_range_piece]
  exact (D.vertex v).piece.isClosed_range

theorem not_mem_awaySet (j : Fin P.cnt) {x : W.Carrier} (hx : x ∈ P.coreSet j)
    (hT : x ∉ P.rimTargets j) : x ∉ P.awaySet j := by
  -- the two kinds of points of the core
  have hcases : (∃ k, x ∈ (D.vertex (P.ball j k)).image) ∨
      ∃ k, x ∈ range (D.handle (P.handle j k)).map := by
    rcases hx with hx | hx
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact Or.inl ⟨k, P.ball_mem_vertex_image hk⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      rw [P.range_cycleHandle] at hk
      exact Or.inr ⟨k, hk⟩
  rintro (((hV | hH)) | (hE | hC))
  · obtain ⟨v, hv⟩ := mem_iUnion.mp hV
    obtain ⟨hv', hxv⟩ := mem_iUnion.mp hv
    rcases hcases with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Set.disjoint_left.mp (D.ball_image_disjoint_vertex_image (P.ball_isBall j k)
        (P.exists_partitioned_face j k) (hv' k)) hk hxv
    · have hmem := (D.handle_inter_vertex_image (P.handle j k) v).subset ⟨hk, hxv⟩
      obtain ⟨b, hb⟩ := mem_iUnion.mp hmem
      obtain ⟨hbv, -⟩ := mem_iUnion.mp hb
      rw [P.handleEnd_handle_eq] at hbv
      exact hv' _ hbv
  · obtain ⟨h, hh⟩ := mem_iUnion.mp hH
    obtain ⟨hh', hxh⟩ := mem_iUnion.mp hh
    rcases hcases with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hmem := (D.handle_inter_vertex_image h (P.ball j k)).subset ⟨hxh, hk⟩
      obtain ⟨b, hb⟩ := mem_iUnion.mp hmem
      obtain ⟨hbv, -⟩ := mem_iUnion.mp hb
      obtain ⟨k', hk'⟩ := P.exists_handle_eq_of_handleEnd_eq j k hbv
      exact hh' k' hk'
    · exact Set.disjoint_left.mp (D.handle_images_disjoint (hh' k)) hk hxh
  · obtain ⟨e, he⟩ := mem_iUnion.mp hE
    rcases hcases with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Set.disjoint_left.mp (D.ball_image_disjoint_edgeCircle (P.ball_isBall j k)
        (P.exists_partitioned_face j k) e) hk he
    · exact Set.disjoint_left.mp (D.handle_image_disjoint_edgeCircle _ e) hk he
  · obtain ⟨h, b, hhb⟩ := D.rimCore_subset_target hC
    by_cases hcyc : ∃ k, P.handle j k = h
    · obtain ⟨k, rfl⟩ := hcyc
      apply hT
      rw [P.rimChart_handle_eq] at hhb
      exact mem_iUnion₂.mpr ⟨k, _, hhb⟩
    · push Not at hcyc
      rcases hcases with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hne : P.ball j k ≠ D.handleEnd h b := fun he =>
          let ⟨k', hk'⟩ := P.exists_handle_eq_of_handleEnd_eq j k he.symm
          hcyc k' hk'
        exact Set.disjoint_left.mp (D.disjoint_vertex_rimChart_target h b _ hne) hk hhb
      · exact Set.disjoint_left.mp (D.disjoint_handle_rimChart_target h b _ (hcyc k)) hk hhb

/-- Off the pieces to avoid and off the core, a point lies in the circle region, off the boxes. -/
theorem mem_region_of_not_mem_awaySet (j : Fin P.cnt) {y : W.Carrier} (hy : y ∉ P.awaySet j)
    (hyc : y ∉ P.coreSet j) : y ∈ D.circ.region ∧ y ∉ D.rimCore := by
  refine ⟨?_, fun h => hy (Or.inr (Or.inr h))⟩
  have hcov : y ∈ (⋃ k, (D.vertex k).image) ∪ (⋃ h, range (D.handle h).map) ∪
      (⋃ e, range (D.edgeCircle e).piece.map) ∪ D.circ.region := by
    rw [D.cover]
    trivial
  rcases hcov with ((hV | hH) | hE) | hR
  · obtain ⟨v, hv⟩ := mem_iUnion.mp hV
    by_cases hcyc : ∃ k, P.ball j k = v
    · obtain ⟨k, rfl⟩ := hcyc
      exact (hyc (P.ball_subset_coreSet j k hv)).elim
    · push Not at hcyc
      exact (hy (Or.inl (Or.inl (mem_iUnion₂.mpr ⟨v, hcyc, hv⟩)))).elim
  · obtain ⟨h, hh⟩ := mem_iUnion.mp hH
    by_cases hcyc : ∃ k, P.handle j k = h
    · obtain ⟨k, rfl⟩ := hcyc
      exact (hyc (P.handle_subset_coreSet j k hh)).elim
    · push Not at hcyc
      exact (hy (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨h, hcyc, hh⟩)))).elim
  · exact (hy (Or.inr (Or.inl hE))).elim
  · exact hR

/-- **Pointwise relative openness of the rounded union in the closed complement.** -/
theorem eventually_mem_unionSet (j : Fin P.cnt) {x : W.Carrier} (hx : x ∈ P.unionSet j) :
    ∀ᶠ y in 𝓝 x, y ∈ D.roundedComplement → y ∈ P.unionSet j := by
  by_cases hT : x ∈ P.rimTargets j
  · obtain ⟨k, b, hxT⟩ := mem_iUnion₂.mp hT
    filter_upwards [(P.cycleRimChart j k b).open_target.mem_nhds hxT] with y hyT hyS
    obtain ⟨p, hp, rfl⟩ : ∃ p, p ∈ (P.cycleRimChart j k b).source ∧ P.cycleRimChart j k b p = y :=
      ⟨(P.cycleRimChart j k b).symm y, (P.cycleRimChart j k b).map_target hyT,
        (P.cycleRimChart j k b).right_inv hyT⟩
    rcases hyS with hyd | hρ
    · exact (hyd (D.mem_domain_of_mem_rimChart_target ((P.cycleRimChart j k b).map_source hp))).elim
    · apply (P.mem_unionSet_rim_iff j k b hp).mpr
      change 0 ≤ D.circ.roundedFunction (D.rimChart (P.handle j k) (xor b (P.orientation j k)) p)
        at hρ
      rw [D.roundedFunction_rimChart _ _ hp] at hρ
      have hc := D.circ.cornerScale_pos (D.handleCorner (P.handle j k) (xor b (P.orientation j k)))
      by_contra hψ
      have : 0 < D.circ.cornerScale (D.handleCorner (P.handle j k) (xor b (P.orientation j k))) *
          standardRimRounding p.2 := mul_pos hc (not_le.mp hψ)
      linarith
  · have hxc : x ∈ P.coreSet j := by
      have h1 : x ∈ P.unionSet j \ P.rimTargets j := ⟨hx, hT⟩
      rw [P.unionSet_diff_rimTargets] at h1
      exact h1.1
    have hN : (P.awaySet j)ᶜ ∈ 𝓝 x :=
      (P.isClosed_awaySet j).isOpen_compl.mem_nhds (P.not_mem_awaySet j hxc hT)
    filter_upwards [hN] with y hy hyS
    apply P.coreSet_subset_unionSet j
    by_contra hyc
    obtain ⟨hyR, hyC⟩ := P.mem_region_of_not_mem_awaySet j hy hyc
    have hyd : y ∈ D.circ.domain := D.circ.region_subset_domain hyR
    have hle : D.circ.roundedFunction y ≤ 0 := by
      rw [D.circ.roundedFunction_apply ⟨y, hyd⟩]
      exact (rounding_le_zero_iff_of_not_mem_rimCore (y := ⟨y, hyd⟩) hyC).mpr hyR
    have hge : 0 ≤ D.circ.roundedFunction y := hyS.resolve_left (not_not.mpr hyd)
    have hN2 : (P.awaySet j)ᶜ ∩ (P.coreSet j)ᶜ ∈ 𝓝 y :=
      ((P.isClosed_awaySet j).isOpen_compl.inter (P.isClosed_coreSet j).isOpen_compl).mem_nhds
        ⟨hy, hyc⟩
    obtain ⟨z, ⟨hz1, hz2⟩, hzd, hzpos⟩ :=
      D.exists_pos_roundedFunction_of_mem_nhds hyd (le_antisymm hle hge) hN2
    obtain ⟨hzR, hzC⟩ := P.mem_region_of_not_mem_awaySet j hz1 hz2
    have hzle : D.circ.roundedFunction z ≤ 0 := by
      rw [D.circ.roundedFunction_apply ⟨z, hzd⟩]
      exact (rounding_le_zero_iff_of_not_mem_rimCore (y := ⟨z, hzd⟩) hzC).mpr hzR
    linarith

/-- **The rounded union is relatively open in the closed complement.** -/
theorem exists_isOpen_inter_roundedComplement_eq (j : Fin P.cnt) :
    ∃ O : Set W.Carrier, IsOpen O ∧ O ∩ D.roundedComplement = P.unionSet j := by
  refine ⟨{x | ∀ᶠ y in 𝓝 x, y ∈ D.roundedComplement → y ∈ P.unionSet j},
    isOpen_setOfPred_eventually_nhds, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hx, hxS⟩
    exact hx.self_of_nhds hxS
  · intro x hx
    exact ⟨P.eventually_mem_unionSet j hx, P.unionSet_subset_roundedComplement j hx⟩

/-- **H3a.** The rounded union of cycle `j` is one B1 piece of the closed complement of the open
rounded circle region: a `PieceEmbedding` with range exactly `unionSet j`, whose model boundary is
the zero level of the COMMON defining function `ρ = rounding ∘ proj`. -/
theorem exists_pieceEmbedding_unionSet (j : Fin P.cnt) :
    ∃ U : PieceEmbedding W, range U.map = P.unionSet j ∧
      ∀ q, (𝓡∂ 3).IsBoundaryPoint q ↔
        (U.map q ∈ D.circ.domain ∧ D.circ.roundedFunction (U.map q) = 0) := by
  obtain ⟨m, Q, hcov, hdisj, hbd⟩ := exists_pieces_of_interior_superlevel W D.circ.domain
    D.circ.domain_interior D.circ.roundedFunction 0 D.circ.contMDiffOn_roundedFunction
    (fun x hx h0 => D.circ.roundedFunction_regular x hx h0)
    (by rw [← D.circ.rounded_eq_sublevel]; exact D.circ.isCompact_rounded)
  have hS : (⋃ i, range (Q i).map) = D.roundedComplement := hcov
  obtain ⟨x₀, hx₀⟩ := (P.isConnected_unionSet j).nonempty
  have hx₀S : x₀ ∈ ⋃ i, range (Q i).map := hS ▸ P.unionSet_subset_roundedComplement j hx₀
  obtain ⟨i, hx₀i⟩ := mem_iUnion.mp hx₀S
  have hsub1 : P.unionSet j ⊆ range (Q i).map := by
    have hpre := (P.isConnected_unionSet j).isPreconnected
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hpre
    let V : Set W.Carrier := ⋃ (i' : Fin m) (_ : i' ≠ i), range (Q i').map
    have hV : IsClosed V := isClosed_iUnion_of_finite fun i' => isClosed_iUnion_of_finite fun _ =>
      (Q i').isClosed_range
    have hcover : P.unionSet j ⊆ range (Q i).map ∪ V := by
      intro y hy
      have hyS : y ∈ ⋃ i, range (Q i).map := hS ▸ P.unionSet_subset_roundedComplement j hy
      obtain ⟨i', hi'⟩ := mem_iUnion.mp hyS
      by_cases hii : i' = i
      · exact Or.inl (hii ▸ hi')
      · exact Or.inr (mem_iUnion₂.mpr ⟨i', hii, hi'⟩)
    have hempty : P.unionSet j ∩ (range (Q i).map ∩ V) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro _ hyi hyV
      obtain ⟨i', hii, hyi'⟩ := mem_iUnion₂.mp hyV
      exact Set.disjoint_left.mp (hdisj hii) hyi' hyi
    rcases hpre _ _ (Q i).isClosed_range hV hcover hempty with h | h
    · exact h
    · obtain ⟨i', hii, hx'⟩ := mem_iUnion₂.mp (h hx₀)
      exact (Set.disjoint_left.mp (hdisj hii) hx' hx₀i).elim
  obtain ⟨O, hO, hOS⟩ := P.exists_isOpen_inter_roundedComplement_eq j
  have hQS : range (Q i).map ⊆ D.roundedComplement := fun y hy => hS ▸ mem_iUnion.mpr ⟨i, hy⟩
  have hsub2 : range (Q i).map ⊆ P.unionSet j := by
    have hpre := (Q i).isConnected_range.isPreconnected
    rw [isPreconnected_iff_subset_of_disjoint] at hpre
    have hcover : range (Q i).map ⊆ O ∪ (P.unionSet j)ᶜ := by
      intro y hy
      by_cases hyU : y ∈ P.unionSet j
      · rw [← hOS] at hyU
        exact Or.inl hyU.1
      · exact Or.inr hyU
    have hempty : range (Q i).map ∩ (O ∩ (P.unionSet j)ᶜ) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hy hyO hyU
      exact hyU (hOS ▸ ⟨hyO, hQS hy⟩)
    rcases hpre _ _ hO (P.isClosed_unionSet j).isOpen_compl hcover hempty with h | h
    · intro y hy
      exact hOS ▸ ⟨h hy, hQS hy⟩
    · exact ((h (hsub1 hx₀)) hx₀).elim
  refine ⟨Q i, Subset.antisymm hsub2 hsub1, fun q => ?_⟩
  rw [hbd i q]
  have hint : (Q i).map q ∈ W.interior := P.unionSet_subset_interior j (hsub2 ⟨q, rfl⟩)
  constructor
  · rintro (hb | hc)
    · exact absurd hb ((W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hint)
    · exact hc
  · exact Or.inr

/-- The rounded union of cycle `j` as a piece (H3a). -/
def roundedUnion (j : Fin P.cnt) : PieceEmbedding W :=
  (P.exists_pieceEmbedding_unionSet j).choose

theorem range_roundedUnion (j : Fin P.cnt) : range (P.roundedUnion j).map = P.unionSet j :=
  (P.exists_pieceEmbedding_unionSet j).choose_spec.1

variable {P} in
theorem roundedUnion_isBoundaryPoint_iff {j : Fin P.cnt} {q : (P.roundedUnion j).Piece} :
    (𝓡∂ 3).IsBoundaryPoint q ↔ ((P.roundedUnion j).map q ∈ D.circ.domain ∧
      D.circ.roundedFunction ((P.roundedUnion j).map q) = 0) :=
  (P.exists_pieceEmbedding_unionSet j).choose_spec.2 q

/-- **(H3-boundary)** The boundary of the rounded union is its part of the zero level of the
common defining function `ρ`. -/
theorem image_boundary_roundedUnion (j : Fin P.cnt) :
    (P.roundedUnion j).map '' (𝓡∂ 3).boundary (P.roundedUnion j).Piece =
      P.unionSet j ∩ {x | x ∈ D.circ.domain ∧ D.circ.roundedFunction x = 0} := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨P.range_roundedUnion j ▸ ⟨q, rfl⟩, roundedUnion_isBoundaryPoint_iff.mp hq⟩
  · rintro ⟨hx, hx0⟩
    rw [← P.range_roundedUnion j] at hx
    obtain ⟨q, rfl⟩ := hx
    exact ⟨q, roundedUnion_isBoundaryPoint_iff.mpr hx0, rfl⟩

theorem range_roundedUnion_subset_interior (j : Fin P.cnt) :
    range (P.roundedUnion j).map ⊆ W.interior := by
  rw [P.range_roundedUnion]
  exact P.unionSet_subset_interior j

end CyclePartition

end DecompositionCertificate

end GC.GraphManifold.Assembly
