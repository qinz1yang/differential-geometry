import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleThirdPieceApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleSeamSides
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# FC42 packet H1 (part a): handle points, the rim sectors, vertical propagation

Lane ASM-CYC2, review 40 §4.2. For a certificate handle `H = D.handle h`:

* rim circles: `handle_rim_mem_target`, `handle_rim_mem_region`; every point of the handle image
  lies in the domain of the circle region along the vertical face (`handle_vertical_mem_domain`);
* **the rim sector `{y = 0, x ≤ 0}` is face** (`rimChart_mem_face`): the chart image of that
  closed half-plane is connected, lies in the model-boundary image of the rim's vertex (the open
  handle sector sits above it) and contains the rim circle, so by ASM-CYC3's
  `subset_face_of_isPreconnected` it lies in the face `handleFace h b`; off the circle region such a
  point lies on an end disk of `H` itself (`exists_endDisk_of_rimChart`: face partition + the full
  rim chart);
* **no third piece at a vertical point in the region** (`false_of_vertical_mem_region_of_piece`) and
  at an end-disk point (`false_of_endDisk_of_piece`): the half-space normal forms of G1 for the
  handle, the vertex and (depth one) the circle region, the corner germ of G2 for the third piece;
  depth zero and corner fibres by density and the full rim chart;
* **vertical propagation** `handle_vertical_subset_region` (review 40 §4.2): the vertical face lies
  in the circle region. Along each vertical segment `t ↦ H (x, t)` the set of times in the region is
  closed (the region is closed in the domain), contains `0` and `1` (rim circles), is open at `0`,
  `1` (rim chart sectors: a vertical point on `{y = 0, x < 0}` would be an end-disk point) and at
  interior times (the boundary criterion of G1, the cover, and no third piece), hence everything.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsH1_ASMCYC2 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothH1_ASMCYC2 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-! ## Rim circles -/

theorem rimChart_zero_mem_source (h : Fin D.handleCount) (b : Bool) (c : Circle) :
    ((c, ((0 : ℝ), (0 : ℝ))) : Circle × (ℝ × ℝ)) ∈ (D.rimChart h b).source :=
  (D.rim_source h b).mpr (by simp [rimBox])

/-- A rim point of a handle is the chart image of a centre point. -/
theorem exists_rimChart_eq_handle_rim (h : Fin D.handleCount) (b : Bool) {x : ClosedCell 2}
    (hx : x ∈ diskRim) :
    ∃ c : Circle, D.rimChart h b (c, ((0 : ℝ), (0 : ℝ))) = (D.handle h).map (x, iccEnd b) := by
  have hmem : (D.handle h).map (x, iccEnd b) ∈
      (fun z : ClosedCell 2 => (D.handle h).map (z, iccEnd b)) '' diskRim := ⟨x, hx, rfl⟩
  rw [← D.rim_label h b] at hmem
  obtain ⟨p, hp, hpx⟩ := hmem
  refine ⟨p.1, ?_⟩
  rw [← hpx]
  congr 1
  exact Prod.ext rfl hp.symm

theorem handle_rim_mem_target (h : Fin D.handleCount) (b : Bool) {x : ClosedCell 2}
    (hx : x ∈ diskRim) : (D.handle h).map (x, iccEnd b) ∈ (D.rimChart h b).target := by
  obtain ⟨c, hc⟩ := D.exists_rimChart_eq_handle_rim h b hx
  rw [← hc]
  exact (D.rimChart h b).map_source (D.rimChart_zero_mem_source h b c)

theorem handle_rim_mem_region (h : Fin D.handleCount) (b : Bool) {x : ClosedCell 2}
    (hx : x ∈ diskRim) : (D.handle h).map (x, iccEnd b) ∈ D.circ.region := by
  obtain ⟨c, hc⟩ := D.exists_rimChart_eq_handle_rim h b hx
  rw [← hc]
  exact (D.rim_region h b (D.rimChart_zero_mem_source h b c)).mpr ⟨le_rfl, le_rfl⟩

/-- The vertical segments lie in the domain of the circle region (whole fibres). -/
theorem handle_vertical_mem_domain (h : Fin D.handleCount) {x : ClosedCell 2} (hx : x ∈ diskRim)
    (t : Icc (0 : ℝ) 1) : (D.handle h).map (x, t) ∈ D.circ.domain := by
  obtain ⟨b, hb⟩ := D.vertical_fibre h t
  have hmem : (D.handle h).map (x, t) ∈
      (fun z : ClosedCell 2 => (D.handle h).map (z, t)) '' diskRim := ⟨x, hx, rfl⟩
  rw [hb] at hmem
  obtain ⟨w, -, hw⟩ := hmem
  rw [← hw]
  exact w.2

/-- Two points of a handle with different times are different. -/
theorem handle_map_ne_of_time_ne (h : Fin D.handleCount) {p q : ClosedCell 2 × Icc (0 : ℝ) 1}
    (hpq : (p.2 : ℝ) ≠ q.2) : (D.handle h).map p ≠ (D.handle h).map q := fun he =>
  hpq (congrArg (fun r : ClosedCell 2 × Icc (0 : ℝ) 1 => (r.2 : ℝ)) ((D.handle h).injective he))

theorem iccEnd_val_mem (b : Bool) : ((iccEnd b : Icc (0 : ℝ) 1) : ℝ) = 0 ∨
    ((iccEnd b : Icc (0 : ℝ) 1) : ℝ) = 1 := by
  cases b <;> simp [iccEnd]

/-- An end-disk point is not a point of interior time. -/
theorem handle_endDisk_ne_interior_time (h : Fin D.handleCount) (b : Bool) {x : ClosedCell 2}
    {t : Icc (0 : ℝ) 1} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (D.handle h).map (x, t) ∉ (D.handle h).endDisk b := by
  rintro ⟨x', hx'⟩
  refine D.handle_map_ne_of_time_ne h (p := (x', iccEnd b)) (q := (x, t)) ?_ hx'
  rcases iccEnd_val_mem b with h0 | h1
  · rw [h0]
    exact ht0.ne
  · rw [h1]
    exact ht1.ne'

/-! ## The sector `{y = 0, x ≤ 0}` of a rim chart -/

/-- **The lower sector boundary of a rim chart is face.** -/
theorem rimChart_mem_face (h : Fin D.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (D.rimChart h b).source) (hy : p.2.2 = 0) (hx : p.2.1 ≤ 0) :
    D.rimChart h b p ∈ D.face (D.handleFace h b) := by
  set f₀ := D.handleFace h b with hf₀
  have hown : D.faceOwner f₀ = D.handleEnd h b := D.handleFace_owner h b
  set Q : Set (Circle × (ℝ × ℝ)) :=
    {q | q ∈ (D.rimChart h b).source ∧ q.2.2 = 0 ∧ q.2.1 ≤ 0} with hQdef
  have hQ : Q = (univ : Set Circle) ×ˢ (Ioc (-2 : ℝ) 0 ×ˢ ({0} : Set ℝ)) := by
    ext q
    simp only [hQdef, mem_ofPred_eq, D.rim_source h b, rimBox, mem_prod, mem_univ, true_and,
      mem_Ioc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, -⟩, h2, h3⟩
      exact ⟨⟨by linarith [(abs_lt.mp h1).1], h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      refine ⟨⟨abs_lt.mpr ⟨h1, by linarith⟩, by rw [h2]; norm_num⟩, h2, h3⟩
  have hQc : IsPreconnected Q := by
    rw [hQ]
    exact isPreconnected_univ.prod (isPreconnected_Ioc.prod isPreconnected_singleton)
  have hSigc : IsPreconnected (D.rimChart h b '' Q) :=
    hQc.image _ ((D.rimChart h b).toOpenPartialHomeomorph.continuousOn.mono fun q hq => hq.1)
  -- the sector lies in the model-boundary image of the vertex
  have hSigB : D.rimChart h b '' Q ⊆ (D.vertex (D.faceOwner f₀)).boundaryImage := by
    rintro _ ⟨q, ⟨hq, hq2, hq1⟩, rfl⟩
    rw [hown]
    have hV : D.rimChart h b q ∈ (D.vertex (D.handleEnd h b)).image :=
      (D.rim_vertex h b hq).mpr hq2.le
    rw [Vertex.image_eq_range_piece] at hV
    obtain ⟨m, hm⟩ := hV
    by_cases hmint : (𝓡∂ 3).IsInteriorPoint m
    · exfalso
      have hI := (D.vertex (D.handleEnd h b)).piece.toPieceFold.map_mem_interior_range hmint
      change (D.vertex (D.handleEnd h b)).piece.map m ∈ _ at hI
      rw [hm] at hI
      -- points just above `q`, in the open handle sector, are still in the vertex interior
      set U := (D.rimChart h b).source ∩
        (D.rimChart h b) ⁻¹' interior (range (D.vertex (D.handleEnd h b)).piece.map) with hU
      have hUo : IsOpen U :=
        (D.rimChart h b).toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage
          (D.rimChart h b).open_source isOpen_interior
      have hc : Continuous fun δ : ℝ => ((q.1, (q.2.1 - δ, δ)) : Circle × (ℝ × ℝ)) := by
        fun_prop
      have hc0 : ((q.1, (q.2.1 - 0, (0 : ℝ))) : Circle × (ℝ × ℝ)) = q := by
        ext <;> simp [hq2]
      have hT : Tendsto (fun δ : ℝ => ((q.1, (q.2.1 - δ, δ)) : Circle × (ℝ × ℝ))) (𝓝[>] 0)
          (𝓝 q) := by
        have := hc.tendsto 0
        rw [hc0] at this
        exact this.mono_left nhdsWithin_le_nhds
      obtain ⟨δ, hδU, hδ⟩ := ((hT.eventually (hUo.mem_nhds ⟨hq, hI⟩)).and
        self_mem_nhdsWithin).exists
      have hδ0 : (0 : ℝ) < δ := hδ
      have hHint := D.rimChart_mem_interior (T := range (D.handle h).map)
        (O := {v | 0 < v.2 ∧ v.1 < 0})
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_fst continuous_const))
        (fun q' hq' hqO => (D.rim_handle h b hq').mpr ⟨hqO.1.le, hqO.2.le⟩) hδU.1
        ⟨hδ0, by simp only; linarith⟩
      have hd := D.vertex_handle_disjoint (D.handleEnd h b) h
      rw [Vertex.image_eq_range_piece] at hd
      exact Set.disjoint_left.mp hd hδU.2 hHint
    · exact ⟨m, ((𝓡∂ 3).isBoundaryPoint_iff_not_isInteriorPoint m).mpr hmint, hm⟩
  -- the rim circle point of the sector is in the face
  have hz₀Q : ((p.1, ((0 : ℝ), (0 : ℝ))) : Circle × (ℝ × ℝ)) ∈ Q :=
    ⟨D.rimChart_zero_mem_source h b p.1, rfl, le_rfl⟩
  have hz₀f : D.rimChart h b (p.1, ((0 : ℝ), (0 : ℝ))) ∈ D.face f₀ := by
    have hmem : D.rimChart h b (p.1, ((0 : ℝ), (0 : ℝ))) ∈
        (fun z : ClosedCell 2 => (D.handle h).map (z, iccEnd b)) '' diskRim := by
      rw [← D.rim_label h b]
      exact ⟨_, rfl, rfl⟩
    obtain ⟨z, -, hz⟩ := hmem
    rw [← hz]
    exact D.handleEnd_face h b ⟨z, rfl⟩
  exact D.subset_face_of_isPreconnected f₀ hSigc hSigB ⟨_, hz₀Q, rfl⟩ hz₀f ⟨p, ⟨hp, hy, hx⟩, rfl⟩

/-- **Off the region, the lower sector boundary is an end disk of the rim's own handle.** -/
theorem exists_endDisk_of_rimChart (h : Fin D.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (D.rimChart h b).source) (hy : p.2.2 = 0) (hx : p.2.1 < 0) :
    ∃ b', D.rimChart h b p ∈ (D.handle h).endDisk b' := by
  have hf := D.rimChart_mem_face h b hp hy hx.le
  have hnR : D.rimChart h b p ∉ D.circ.region := fun hR =>
    absurd ((D.rim_region h b hp).mp hR).1 (not_le.mpr hx)
  have hT : D.rimChart h b p ∈ (D.rimChart h b).target := (D.rimChart h b).map_source hp
  have hreg := D.face_region_inter (D.handleFace h b) (D.handleFace_kind h b)
  rw [← D.face_partition (D.handleFace h b) (D.handleFace_kind h b)] at hf
  rcases hf with (hd | ha) | hl
  · obtain ⟨h', hd⟩ := mem_iUnion.mp hd
    obtain ⟨b', hd⟩ := mem_iUnion.mp hd
    obtain ⟨-, hd⟩ := mem_iUnion.mp hd
    by_cases hh : h' = h
    · subst hh
      exact ⟨b', hd⟩
    · obtain ⟨z, hz⟩ := hd
      exact (Set.disjoint_left.mp (D.disjoint_handle_rimChart_target h b h' hh) ⟨_, hz⟩ hT).elim
  · have : D.rimChart h b p ∈ D.face (D.handleFace h b) ∩ D.circ.region := by
      rw [hreg]
      exact Or.inl ha
    exact (hnR this.2).elim
  · have : D.rimChart h b p ∈ D.face (D.handleFace h b) ∩ D.circ.region := by
      rw [hreg]
      exact Or.inr hl
    exact (hnR this.2).elim

/-! ## No third piece at vertical and end-disk points -/

section ThirdPiece

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I ∞ M'] {F : M' → W.Carrier}

/-- **No third piece at a vertical point in the circle region.** -/
theorem false_of_vertical_mem_region_of_piece (hdim : Module.finrank ℝ E' = 3)
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q))
    (h : Fin D.handleCount) {x : ClosedCell 2} (hx : x ∈ diskRim) {t : Icc (0 : ℝ) 1}
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) (hR : (D.handle h).map (x, t) ∈ D.circ.region)
    (hmem : (D.handle h).map (x, t) ∈ range F)
    (hHF : Disjoint (interior (range (D.handle h).map)) (interior (range F)))
    (hRF : Disjoint (interior D.circ.region) (interior (range F))) : False := by
  rcases D.region_trichotomy hR with hint | hent | ⟨h'', b'', hrim, hT⟩
  · obtain ⟨w, hw1, hw2⟩ := inter_interior_range_nonempty finrank_handleModel
      (D.handle h).smooth (D.handle h).mfderiv_bijective isOpen_interior ⟨_, hint, ⟨(x, t), rfl⟩⟩
    exact Set.disjoint_left.mp (D.circ_handle_disjoint h) hw1 hw2
  · obtain ⟨q, hq⟩ := hmem
    have hA := (D.handle h).exists_entering_vertical hx ht0 ht1
    rw [← hq] at hA hent
    exact false_of_two_entering_and_piece hdim hF hbij q hA hent (D.circ_handle_disjoint h).symm
      hHF hRF
  · by_cases hh : h'' = h
    · subst hh
      obtain ⟨x', -, hxx'⟩ := hrim
      exact D.handle_endDisk_ne_interior_time h'' b'' ht0 ht1 ⟨x', hxx'⟩
    · exact Set.disjoint_left.mp (D.disjoint_handle_rimChart_target h'' b'' h (Ne.symm hh))
        ⟨(x, t), rfl⟩ hT

/-- **No third piece at an end-disk point** (interior of the disk). -/
theorem false_of_endDisk_of_piece (hdim : Module.finrank ℝ E' = 3)
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q))
    (h : Fin D.handleCount) {x : ClosedCell 2} (hx : x ∉ diskRim) (b : Bool)
    (hmem : (D.handle h).map (x, iccEnd b) ∈ range F)
    (hHF : Disjoint (interior (range (D.handle h).map)) (interior (range F)))
    (hVF : Disjoint (interior (D.vertex (D.handleEnd h b)).image) (interior (range F))) :
    False := by
  have hzB : (D.handle h).map (x, iccEnd b) ∈ (D.vertex (D.handleEnd h b)).boundaryImage := by
    have h1 := D.face_subset_boundaryImage (D.handleFace h b) (D.handleEnd_face h b ⟨x, rfl⟩)
    rwa [D.handleFace_owner] at h1
  obtain ⟨q, hq⟩ := hmem
  have hA := (D.handle h).exists_entering_endDisk hx b
  have hB := Vertex.exists_entering hzB
  rw [← hq] at hA hB
  exact false_of_two_entering_and_piece hdim hF hbij q hA hB
    (D.vertex_handle_disjoint (D.handleEnd h b) h).symm hHF hVF

end ThirdPiece

/-! ## Vertical propagation -/

/-- The union of all pieces other than the handle `h` and the circle region. -/
def otherPieces (h : Fin D.handleCount) : Set W.Carrier :=
  (⋃ k, (D.vertex k).image) ∪ (⋃ (h' : Fin D.handleCount) (_ : h' ≠ h), range (D.handle h').map) ∪
    ⋃ e, range (D.edgeCircle e).piece.map

theorem isClosed_otherPieces (h : Fin D.handleCount) : IsClosed (D.otherPieces h) := by
  refine ((isClosed_iUnion_of_finite fun k => ?_).union
    (isClosed_iUnion_of_finite fun h' => isClosed_iUnion_of_finite fun _ =>
      (isCompact_range (D.handle h').smooth.continuous).isClosed)).union
    (isClosed_iUnion_of_finite fun e => (D.edgeCircle e).piece.isClosed_range)
  rw [Vertex.image_eq_range_piece]
  exact (D.vertex k).piece.isClosed_range

/-- A vertical point off the region (inside the domain) is a point of another piece. -/
theorem vertical_mem_otherPieces (h : Fin D.handleCount) {x : ClosedCell 2} (hx : x ∈ diskRim)
    (t : Icc (0 : ℝ) 1) (hR : (D.handle h).map (x, t) ∉ D.circ.region) :
    (D.handle h).map (x, t) ∈ D.otherPieces h := by
  by_contra hC
  have hdom := D.handle_vertical_mem_domain h hx t
  set N : Set W.Carrier := Subtype.val '' (D.circ.proj ⁻¹' D.circ.cornerBaseᶜ) with hN
  have hNo : IsOpen N :=
    D.circ.domain.isOpen.isOpenMap_subtype_val _ (D.circ.proj.continuous.isOpen_preimage _
      D.circ.cornerBase_compact.isClosed.isOpen_compl)
  have hzN : (D.handle h).map (x, t) ∈ N :=
    ⟨⟨_, hdom⟩, fun hc => hR ⟨⟨_, hdom⟩, hc, rfl⟩, rfl⟩
  have hNR : Disjoint N D.circ.region := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
    rw [Subtype.val_injective hzz'] at hz'
    exact hz hz'
  have hsub : N ∩ (D.otherPieces h)ᶜ ⊆ range (D.handle h).map := by
    rintro w ⟨hwN, hwC⟩
    have hcov : w ∈ (⋃ k, (D.vertex k).image) ∪ (⋃ h, range (D.handle h).map) ∪
        (⋃ e, range (D.edgeCircle e).piece.map) ∪ D.circ.region := by
      rw [D.cover]
      exact mem_univ w
    rcases hcov with ((hv | hh) | he) | hr
    · exact (hwC (Or.inl (Or.inl hv))).elim
    · obtain ⟨h', hh'⟩ := mem_iUnion.mp hh
      by_cases he' : h' = h
      · rw [← he']
        exact hh'
      · exact (hwC (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨h', he', hh'⟩)))).elim
    · exact (hwC (Or.inr he)).elim
    · exact (Set.disjoint_left.mp hNR hwN hr).elim
  have hint : (D.handle h).map (x, t) ∈ interior (range (D.handle h).map) :=
    interior_maximal hsub (hNo.inter (D.isClosed_otherPieces h).isOpen_compl) ⟨hzN, hC⟩
  have hb : ((𝓡∂ 2).prod (𝓡∂ 1)).IsBoundaryPoint (x, t) :=
    handle_isBoundaryPoint_iff.mpr (Or.inl hx)
  exact (D.handle h).map_not_mem_interior_range hb hint

/-- No third piece at a vertical point in the region: the other pieces avoid it. -/
theorem false_of_vertical_mem_otherPieces (h : Fin D.handleCount) {x : ClosedCell 2}
    (hx : x ∈ diskRim) {t : Icc (0 : ℝ) 1} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hR : (D.handle h).map (x, t) ∈ D.circ.region)
    (hC : (D.handle h).map (x, t) ∈ D.otherPieces h) : False := by
  rcases hC with (hv | hh) | he
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hv
    rw [Vertex.image_eq_range_piece] at hk
    have hHF : Disjoint (interior (range (D.handle h).map))
        (interior (range (D.vertex k).piece.map)) := by
      rw [← Vertex.image_eq_range_piece]
      exact (D.vertex_handle_disjoint k h).symm
    have hRF : Disjoint (interior D.circ.region) (interior (range (D.vertex k).piece.map)) := by
      rw [← Vertex.image_eq_range_piece]
      exact D.circ_vertex_disjoint k
    exact D.false_of_vertical_mem_region_of_piece finrank_euclideanSpace_fin
      (D.vertex k).piece.smooth (D.vertex k).piece.mfderiv_bijective h hx ht0 ht1 hR hk hHF hRF
  · obtain ⟨h', hne, hh'⟩ := mem_iUnion₂.mp hh
    exact D.false_of_vertical_mem_region_of_piece finrank_handleModel (D.handle h').smooth
      (D.handle h').mfderiv_bijective h hx ht0 ht1 hR hh' (D.handle_disjoint (Ne.symm hne))
      (D.circ_handle_disjoint h')
  · obtain ⟨e, he⟩ := mem_iUnion.mp he
    exact D.false_of_vertical_mem_region_of_piece finrank_euclideanSpace_fin
      (D.edgeCircle e).piece.smooth (D.edgeCircle e).piece.mfderiv_bijective h hx ht0 ht1 hR he
      (D.edgeCircle_handle_disjoint e h).symm (D.circ_edgeCircle_disjoint e)

/-- Near a rim, the vertical segment stays in the circle region (the sectors of the rim chart). -/
theorem mem_nhds_of_rim_vertical (h : Fin D.handleCount) (b : Bool) {x₀ : ClosedCell 2}
    (hx₀ : x₀ ∈ diskRim) :
    {t : Icc (0 : ℝ) 1 | (D.handle h).map (x₀, t) ∈ D.circ.region} ∈ 𝓝 (iccEnd b) := by
  have hγc : Continuous fun t : Icc (0 : ℝ) 1 => (D.handle h).map (x₀, t) :=
    (D.handle h).smooth.continuous.comp (continuous_const.prodMk continuous_id)
  have hT := (hγc.continuousAt (x := iccEnd b)).preimage_mem_nhds
    ((D.rimChart h b).open_target.mem_nhds (D.handle_rim_mem_target h b hx₀))
  filter_upwards [hT] with t' ht'
  by_cases hend : (t' : ℝ) = 0 ∨ (t' : ℝ) = 1
  · rcases hend with h0 | h1
    · have he : t' = iccEnd false := Subtype.ext (by simp [iccEnd, h0])
      rw [he]
      exact D.handle_rim_mem_region h false hx₀
    · have he : t' = iccEnd true := Subtype.ext (by simp [iccEnd, h1])
      rw [he]
      exact D.handle_rim_mem_region h true hx₀
  · have ht0 : 0 < (t' : ℝ) := lt_of_le_of_ne t'.2.1 (fun h0 => hend (Or.inl h0.symm))
    have ht1 : (t' : ℝ) < 1 := lt_of_le_of_ne t'.2.2 (fun h1 => hend (Or.inr h1))
    have ht'' : (D.handle h).map (x₀, t') ∈ (D.rimChart h b).target := ht'
    obtain ⟨p, hp, hpz⟩ : ∃ p, p ∈ (D.rimChart h b).source ∧
        D.rimChart h b p = (D.handle h).map (x₀, t') :=
      ⟨_, (D.rimChart h b).map_target ht'', (D.rimChart h b).right_inv ht''⟩
    have hH : D.rimChart h b p ∈ range (D.handle h).map := by
      rw [hpz]
      exact ⟨_, rfl⟩
    obtain ⟨hy0, hx0⟩ := (D.rim_handle h b hp).mp hH
    rcases hx0.lt_or_eq with hxn | hxz
    · exfalso
      rcases hy0.lt_or_eq with hyp | hyz
      · have hint := D.rimChart_mem_interior (T := range (D.handle h).map)
          (O := {v | 0 < v.2 ∧ v.1 < 0})
          ((isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt continuous_fst continuous_const))
          (fun q hq hqO => (D.rim_handle h b hq).mpr ⟨hqO.1.le, hqO.2.le⟩) hp ⟨hyp, hxn⟩
        rw [hpz] at hint
        have hb : ((𝓡∂ 2).prod (𝓡∂ 1)).IsBoundaryPoint (x₀, t') :=
          handle_isBoundaryPoint_iff.mpr (Or.inl hx₀)
        exact (D.handle h).map_not_mem_interior_range hb hint
      · obtain ⟨b', hb'⟩ := D.exists_endDisk_of_rimChart h b hp hyz.symm hxn
        rw [hpz] at hb'
        exact D.handle_endDisk_ne_interior_time h b' ht0 ht1 hb'
    · rw [← hpz]
      exact (D.rim_region h b hp).mpr ⟨hxz.ge, hy0⟩

/-- **H1, vertical propagation** (review 40 §4.2). -/
theorem handle_vertical_subset_region (h : Fin D.handleCount) :
    (D.handle h).vertical ⊆ D.circ.region := by
  rintro _ ⟨⟨x₀, t₀⟩, ⟨hx₀, -⟩, rfl⟩
  set γ : Icc (0 : ℝ) 1 → W.Carrier := fun t => (D.handle h).map (x₀, t) with hγ
  have hγc : Continuous γ :=
    (D.handle h).smooth.continuous.comp (continuous_const.prodMk continuous_id)
  set S : Set (Icc (0 : ℝ) 1) := {t | γ t ∈ D.circ.region} with hS
  -- closed
  have hSc : IsClosed S := by
    set γ' : Icc (0 : ℝ) 1 → D.circ.domain := fun t => ⟨γ t, D.handle_vertical_mem_domain h hx₀ t⟩
    have hγ'c : Continuous γ' := hγc.subtype_mk _
    have hS' : S = (fun t => D.circ.proj (γ' t)) ⁻¹' D.circ.cornerBase := by
      ext t
      constructor
      · rintro ⟨z, hz, hzt⟩
        have : z = γ' t := Subtype.ext hzt
        change D.circ.proj (γ' t) ∈ D.circ.cornerBase
        rw [← this]
        exact hz
      · intro ht
        exact ⟨γ' t, ht, rfl⟩
    rw [hS']
    exact D.circ.cornerBase_compact.isClosed.preimage (D.circ.proj.continuous.comp hγ'c)
  -- open
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.2 with h0 | h1 | hmid
    · -- the start: the rim chart `(h, false)`
      have ht' : t = iccEnd false := Subtype.ext (by simp [iccEnd, h0])
      exact ht' ▸ D.mem_nhds_of_rim_vertical h false hx₀
    · have ht' : t = iccEnd true := Subtype.ext (by simp [iccEnd, h1])
      exact ht' ▸ D.mem_nhds_of_rim_vertical h true hx₀
    · by_contra hn
      have hfr : ∃ᶠ t' in 𝓝 t, t' ∉ S := by
        rw [Filter.not_eventually.symm]
        exact hn
      have hev : ∀ᶠ t' : Icc (0 : ℝ) 1 in 𝓝 t, 0 < (t' : ℝ) ∧ (t' : ℝ) < 1 :=
        ((isOpen_lt continuous_const continuous_subtype_val).inter
          (isOpen_lt continuous_subtype_val continuous_const)).mem_nhds ⟨hmid.1, hmid.2⟩
      have hfr' : ∃ᶠ t' in 𝓝 t, γ t' ∈ D.otherPieces h :=
        (hfr.and_eventually hev).mono fun t' ht' => D.vertical_mem_otherPieces h hx₀ t' ht'.1
      have hC : γ t ∈ D.otherPieces h :=
        (D.isClosed_otherPieces h).mem_of_frequently_of_tendsto hfr' (hγc.tendsto t)
      exact D.false_of_vertical_mem_otherPieces h hx₀ hmid.1 hmid.2 ht hC
  have hSne : S.Nonempty := ⟨iccEnd false, D.handle_rim_mem_region h false hx₀⟩
  have : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hSu := (IsClopen.eq_univ ⟨hSc, hSo⟩ hSne)
  have : t₀ ∈ S := hSu ▸ mem_univ t₀
  exact this

end DecompositionCertificate

end GC.GraphManifold.Assembly
