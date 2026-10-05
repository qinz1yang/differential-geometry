import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyApplications

/-!
# FC42 packet T4a §3: the final pieces cover `W`; the positive family

The final pieces of review 40 §3.6 split into the POSITIVE family (`posPiece`: the cycle unions,
the non-ball vertices and the edge circles, all on the closed side `ρ ≥ 0` of the common defining
function) and the rounded circle-region pieces (the sublevel `ρ ≤ 0`, T2).

* `cover_finalPieces`: the positive set and the rounded circle region cover `W`;
* `mem_positiveSet_of_nonneg`, `roundedLevel_subset_positiveSet`: every point with `ρ ≥ 0`, in
  particular the new zero level `Z_R`, is in the positive set;
* `range_posPiece_subset_roundedComplement`: the positive pieces lie on `ρ ≥ 0`;
* `posPiece_inter_subset_vertexSeamSet`: two different positive pieces meet only along the
  vertex–vertex seam tori (`vertexSeamSet`), which avoid `Z_R` (`disjoint_vertexSeamSet_roundedLevel`).
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

/-- The positive final pieces: cycle unions, non-ball vertices, edge circles. -/
abbrev PosIdx (P : D.CyclePartition) : Type :=
  Fin P.cnt ⊕ {k : Fin D.vertexCount // ¬ (D.vertex k).IsBall} ⊕ Fin D.edgeCircleCount

/-- The positive final piece of an index. -/
def posPiece (P : D.CyclePartition) : D.PosIdx P → PieceEmbedding W
  | .inl j => P.roundedUnion j
  | .inr (.inl k) => (D.vertex k.1).piece
  | .inr (.inr e) => (D.edgeCircle e).piece

/-- The union of the positive final pieces. -/
def positiveSet (P : D.CyclePartition) : Set W.Carrier :=
  (⋃ j, range (P.roundedUnion j).map) ∪
    (⋃ (k : Fin D.vertexCount) (_ : ¬ (D.vertex k).IsBall), (D.vertex k).image) ∪
    ⋃ e, range (D.edgeCircle e).piece.map

/-- The vertex–vertex seam tori. -/
def vertexSeamSet : Set W.Carrier :=
  ⋃ (c : Fin D.torusSeamCount) (_ : D.IsVertexSeam c), D.seamTorus c

theorem isClosed_vertexSeamSet : IsClosed D.vertexSeamSet :=
  isClosed_iUnion_of_finite fun c => isClosed_iUnion_of_finite fun _ =>
    (D.isCompact_seamTorus c).isClosed

theorem disjoint_vertexSeamSet_roundedLevel : Disjoint D.vertexSeamSet D.circ.roundedLevel :=
  disjoint_iUnion₂_left.mpr fun c hc => D.disjoint_seamTorus_roundedLevel c hc

theorem iUnion_range_posPiece (P : D.CyclePartition) :
    ⋃ a, range (D.posPiece P a).map = D.positiveSet P := by
  ext x
  simp only [mem_iUnion, positiveSet, mem_union]
  constructor
  · rintro ⟨a | ⟨k⟩ | e, ha⟩
    · exact Or.inl (Or.inl ⟨a, ha⟩)
    · change x ∈ range (D.vertex k.1).piece.map at ha
      rw [← Vertex.image_eq_range_piece] at ha
      exact Or.inl (Or.inr ⟨k.1, k.2, ha⟩)
    · exact Or.inr ⟨e, ha⟩
  · rintro ((⟨j, hj⟩ | ⟨k, hk, hx⟩) | ⟨e, he⟩)
    · exact ⟨.inl j, hj⟩
    · rw [Vertex.image_eq_range_piece] at hx
      exact ⟨.inr (.inl ⟨k, hk⟩), hx⟩
    · exact ⟨.inr (.inr e), he⟩

theorem isClosed_positiveSet (P : D.CyclePartition) : IsClosed (D.positiveSet P) := by
  rw [← D.iUnion_range_posPiece P]
  exact isClosed_iUnion_of_finite fun a => (D.posPiece P a).isClosed_range

/-- **The positive pieces lie on the closed side `ρ ≥ 0`.** -/
theorem range_posPiece_subset_roundedComplement (P : D.CyclePartition) (a : D.PosIdx P) :
    range (D.posPiece P a).map ⊆ D.roundedComplement := by
  intro x hx
  by_cases hxd : x ∈ D.circ.domain
  · refine Or.inr ?_
    rcases a with j | ⟨k⟩ | e
    · change x ∈ range (P.roundedUnion j).map at hx
      rw [P.range_roundedUnion] at hx
      exact (P.unionSet_subset_roundedComplement j hx).resolve_left (not_not.mpr hxd)
    · change x ∈ range (D.vertex k.1).piece.map at hx
      rw [← Vertex.image_eq_range_piece] at hx
      exact D.nonneg_roundedFunction_of_mem_vertex_image k.1 hx hxd
    · exact D.nonneg_roundedFunction_of_mem_edgeCircle e hx hxd
  · exact Or.inl hxd

theorem positiveSet_subset_roundedComplement (P : D.CyclePartition) :
    D.positiveSet P ⊆ D.roundedComplement := by
  rw [← D.iUnion_range_posPiece P]
  exact iUnion_subset fun a => D.range_posPiece_subset_roundedComplement P a

/-- **T4a §3: the final pieces cover `W`.** -/
theorem cover_finalPieces (P : D.CyclePartition) : D.positiveSet P ∪ D.circ.rounded = univ := by
  refine eq_univ_of_forall fun x => ?_
  have hx : x ∈ (⋃ k, (D.vertex k).image) ∪ (⋃ h, range (D.handle h).map) ∪
      (⋃ e, range (D.edgeCircle e).piece.map) ∪ D.circ.region := D.cover ▸ mem_univ x
  rcases hx with ((hv | hh) | he) | hR
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hv
    by_cases hb : (D.vertex k).IsBall
    · refine Or.inl (Or.inl (Or.inl (mem_iUnion.mpr ⟨(P.ballIdx.symm ⟨k, hb⟩).1, ?_⟩)))
      rw [P.range_roundedUnion]
      exact P.vertex_image_subset_unionSet k hb hk
    · exact Or.inl (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨k, hb, hk⟩)))
  · obtain ⟨h, hh⟩ := mem_iUnion.mp hh
    refine Or.inl (Or.inl (Or.inl (mem_iUnion.mpr ⟨(P.handleIdx.symm h).1, ?_⟩)))
    rw [P.range_roundedUnion]
    exact P.handle_range_subset_unionSet h hh
  · exact Or.inl (Or.inr he)
  · have hxd := D.circ.region_subset_domain hR
    by_cases hρ : D.circ.roundedFunction x ≤ 0
    · right
      rw [D.circ.rounded_eq_sublevel]
      exact ⟨hxd, hρ⟩
    · left
      have hc : x ∈ D.rimCore := by
        by_contra hc
        have h1 := (rounding_le_zero_iff_of_not_mem_rimCore (D := D) (y := ⟨x, hxd⟩) hc).mpr hR
        rw [← D.circ.roundedFunction_apply ⟨x, hxd⟩] at h1
        exact hρ h1
      obtain ⟨h, b, hT⟩ := D.rimCore_subset_target hc
      have hp : (D.rimChart h b).symm x ∈ (D.rimChart h b).source := (D.rimChart h b).map_target hT
      have hxp : D.rimChart h b ((D.rimChart h b).symm x) = x := (D.rimChart h b).right_inv hT
      have hψ : standardRimRounding ((D.rimChart h b).symm x).2 ≤ 0 := by
        have h1 := D.roundedFunction_rimChart h b hp
        rw [hxp] at h1
        have hsc := D.circ.cornerScale_pos (D.handleCorner h b)
        have hpos : 0 < D.circ.roundedFunction x := not_le.mp hρ
        by_contra hψ
        have hm : 0 < D.circ.cornerScale (D.handleCorner h b) *
            standardRimRounding ((D.rimChart h b).symm x).2 := mul_pos hsc (not_le.mp hψ)
        linarith
      have hjk := P.handle_handleIdx_symm h
      have hp' : (D.rimChart h b).symm x ∈
          (D.rimChart (P.handle (P.handleIdx.symm h).1 (P.handleIdx.symm h).2) b).source := by
        rw [hjk]
        exact hp
      have hU := P.mem_unionSet_of_rim _ _ b hp' hψ
      rw [hjk, hxp] at hU
      refine Or.inl (Or.inl (mem_iUnion.mpr ⟨(P.handleIdx.symm h).1, ?_⟩))
      rw [P.range_roundedUnion]
      exact hU

/-- A point with `ρ > 0` lies in the positive set. -/
theorem mem_positiveSet_of_pos (P : D.CyclePartition) {x : W.Carrier}
    (hpos : 0 < D.circ.roundedFunction x) : x ∈ D.positiveSet P := by
  have hx : x ∈ D.positiveSet P ∪ D.circ.rounded := (D.cover_finalPieces P).symm ▸ mem_univ x
  rcases hx with hx | hx
  · exact hx
  · rw [D.circ.rounded_eq_sublevel] at hx
    exact absurd hx.2 (not_le.mpr hpos)

/-- **The new zero level lies in the positive set.** -/
theorem roundedLevel_subset_positiveSet (P : D.CyclePartition) :
    D.circ.roundedLevel ⊆ D.positiveSet P := by
  intro x hx
  rw [D.circ.roundedLevel_eq] at hx
  refine (D.isClosed_positiveSet P).closure_subset (mem_closure_iff_nhds.mpr fun N hN => ?_)
  obtain ⟨z, hzN, -, hz⟩ := D.exists_pos_roundedFunction_of_mem_nhds hx.1 hx.2 hN
  exact ⟨z, hzN, D.mem_positiveSet_of_pos P hz⟩

/-- **Every point with `ρ ≥ 0` lies in the positive set.** -/
theorem mem_positiveSet_of_nonneg (P : D.CyclePartition) {x : W.Carrier}
    (hxd : x ∈ D.circ.domain) (hρ : 0 ≤ D.circ.roundedFunction x) : x ∈ D.positiveSet P := by
  rcases hρ.lt_or_eq with h | h
  · exact D.mem_positiveSet_of_pos P h
  · refine D.roundedLevel_subset_positiveSet P ?_
    rw [D.circ.roundedLevel_eq]
    exact ⟨hxd, h.symm⟩

/-- **Two different positive pieces meet only along vertex–vertex seam tori** (`μ = 0`). -/
theorem posPiece_inter_subset_vertexSeamSet (hsph : D.sphereSeamCount = 0)
    (hbad : D.badVertexCount = 0) (P : D.CyclePartition) {a a' : D.PosIdx P} (haa' : a ≠ a') :
    range (D.posPiece P a).map ∩ range (D.posPiece P a').map ⊆ D.vertexSeamSet := by
  have hcv : ∀ j (k : {k : Fin D.vertexCount // ¬ (D.vertex k).IsBall}),
      Disjoint (range (P.roundedUnion j).map) (range (D.vertex k.1).piece.map) := fun j k => by
    rw [← Vertex.image_eq_range_piece]
    exact D.disjoint_roundedUnion_vertex hbad P j k.1 k.2
  have hve : ∀ (k : {k : Fin D.vertexCount // ¬ (D.vertex k).IsBall}) e,
      Disjoint (range (D.vertex k.1).piece.map) (range (D.edgeCircle e).piece.map) := fun k e => by
    rw [← Vertex.image_eq_range_piece]
    exact D.disjoint_vertex_edgeCircle hbad k.1 k.2 e
  have hempty : ∀ {s t : Set W.Carrier}, Disjoint s t → s ∩ t ⊆ D.vertexSeamSet :=
    fun h => by rw [h.inter_eq]; exact empty_subset _
  rcases a with j | k | e <;> rcases a' with j' | k' | e'
  · have hjj : j ≠ j' := fun h => haa' (congrArg Sum.inl h)
    change range (P.roundedUnion j).map ∩ range (P.roundedUnion j').map ⊆ _
    rw [P.range_roundedUnion, P.range_roundedUnion]
    exact hempty (P.pairwise_disjoint_unionSet hjj)
  · exact hempty (hcv j k')
  · exact hempty (D.disjoint_roundedUnion_edgeCircle P j e')
  · exact hempty (hcv j' k).symm
  · have hkk : k.1 ≠ k'.1 := fun h => haa' (congrArg (fun k => Sum.inr (Sum.inl k)) (Subtype.ext h))
    change range (D.vertex k.1).piece.map ∩ range (D.vertex k'.1).piece.map ⊆ _
    rw [← Vertex.image_eq_range_piece, ← Vertex.image_eq_range_piece]
    exact D.vertex_inter_vertex_subset_seamTorus hsph hkk
  · exact hempty (hve k e')
  · exact hempty (D.disjoint_roundedUnion_edgeCircle P j' e).symm
  · exact hempty (hve k' e).symm
  · have hee : e ≠ e' := fun h => haa' (congrArg (fun e => Sum.inr (Sum.inr e)) h)
    exact hempty (D.edgeCircle_disjoint hee)

end DecompositionCertificate

end GC.GraphManifold.Assembly
