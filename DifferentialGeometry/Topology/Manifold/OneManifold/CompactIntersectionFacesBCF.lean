import DifferentialGeometry.Topology.Manifold.OneManifold.CompactOneManifoldChoiceBCF

/-!
# The shared `K₃` kernel, package K1: `D₃ = K₃ ∩ C₃` and its faces (review 74, D74-9; lane B-BCF134)

D74-9: with `∂K₃ ∩ ∂C₃ = ∅` (the avoidance condition excludes two opposite half-intervals pinching an
isolated point),
`∂D₃ = (∂K₃ ∩ int C₃) ⊔ (int K₃ ∩ ∂C₃)`, and `D₃` has finitely many interval / circle components.
All interiors and frontiers are RELATIVE to the base `Bs` (`∂X := X \ int_{Bs} X`).

* `relInterior_inter_BCF`: `int_{Bs}(K ∩ C) = int_{Bs} K ∩ int_{Bs} C`;
* `relFrontier_inter_BCF`: the frontier identity and the disjointness of its two parts (pure set
  theory, from `∂K ∩ ∂C = ∅`);
* `HalfChart_BCF.restrict_BCF`: a half chart of `T` cut down by an open `G` is a half chart of any `T'`
  agreeing with `T` on `O ∩ G`;
* `HalfChart_BCF.mem_closure_relInterior_BCF`: chart points are limits of relative interior points
  (half charts make a set regular);
* `GraphAtlas1_BCF.exists_compact_intersection_faces_BCF` (K1): for a compact `Kset ⊆ Bs` and a
  relatively closed `C ⊆ Bs` with finite relative frontier `∂C ⊆ Kset` and half charts of `C` at the
  points of `∂C`, smooth compact one-dimensional domains `K₃` and `D₃` (arcs AND loops) with
  `D₃ = K₃ ∩ C`, `Kset ⊆ int K₃`, `∂K₃ ∩ ∂C = ∅`, the frontier identity for `∂D₃`, and `K₃ ∩ C`
  regular.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- The relative interior of an intersection is the intersection of the relative interiors. -/
theorem relInterior_inter_BCF {X : Type*} [TopologicalSpace X] {Bs K C : Set X} :
    Subtype.val '' interior (Subtype.val ⁻¹' (K ∩ C) : Set Bs) =
      Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs) ∩
        Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs) := by
  rw [preimage_inter, interior_inter, image_inter Subtype.val_injective]

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- **The faces of `K ∩ C`** (D74-9): when the relative frontiers of `K` and `C` are disjoint,
`∂(K ∩ C) = (∂K ∩ int C) ∪ (int K ∩ ∂C)`, and the two parts are disjoint. -/
theorem relFrontier_inter_BCF {X : Type*} [TopologicalSpace X] {Bs K C : Set X}
    (hdisj : Disjoint (K \ Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs))
      (C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs))) :
    (K ∩ C) \ Subtype.val '' interior (Subtype.val ⁻¹' (K ∩ C) : Set Bs) =
        ((K \ Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs) ∩
          (C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs))) ∧
      Disjoint ((K \ Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs))
        (Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs) ∩
          (C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs))) := by
  have hIK : Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs) ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact (interior_subset hy : y ∈ Subtype.val ⁻¹' K)
  have hIC : Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs) ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    exact (interior_subset hy : y ∈ Subtype.val ⁻¹' C)
  rw [relInterior_inter_BCF]
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨⟨hxK, hxC⟩, hxI⟩
      by_cases hk : x ∈ Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs)
      · refine Or.inr ⟨hk, hxC, fun hc => hxI ⟨hk, hc⟩⟩
      · refine Or.inl ⟨⟨hxK, hk⟩, ?_⟩
        by_contra hc
        exact hdisj.ne_of_mem ⟨hxK, hk⟩ ⟨hxC, hc⟩ rfl
    · rintro (⟨⟨hxK, hk⟩, hc⟩ | ⟨hk, hxC, hc⟩)
      · exact ⟨⟨hxK, hIC hc⟩, fun h => hk h.1⟩
      · exact ⟨⟨hIK hk, hxC⟩, fun h => hc h.2⟩
  · rw [Set.disjoint_left]
    rintro x ⟨⟨-, hk⟩, -⟩ ⟨hk', -⟩
    exact hk hk'

namespace HalfChart_BCF

variable {Bs T : Set H} (d : HalfChart_BCF Bs T)

/-- **Restriction of a half chart** to `O ∩ G` for an open `G`: a half chart of every `T'` that agrees
with `T` on `O ∩ G`. -/
def restrict_BCF {T' : Set H} (G : Set H) (hG : IsOpen G) (hTT' : T' ∩ (d.O ∩ G) = T ∩ (d.O ∩ G)) :
    HalfChart_BCF Bs T' where
  L := d.L
  κ := d.κ
  π := d.π
  W := d.W
  V := d.V ∩ (d.W ∩ d.π ⁻¹' G)
  O := d.O ∩ G
  isOpen_W := d.isOpen_W
  isOpen_V := d.isOpen_V.inter (d.continuousOn_π_BCF.isOpen_inter_preimage d.isOpen_W hG)
  V_subset := fun _ ht => d.V_subset ht.1
  smooth := d.smooth
  coord := d.coord
  mem := d.mem
  relOpen := d.relOpen
  isOpen_O := d.isOpen_O.inter hG
  inter_eq := by
    rw [hTT', ← inter_assoc, d.inter_eq]
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hzG⟩
      exact ⟨t, ⟨⟨ht.1, d.V_subset ht.1, hzG⟩, ht.2⟩, rfl⟩
    · rintro ⟨t, ⟨⟨htV, -, htG⟩, ht0⟩, rfl⟩
      exact ⟨⟨t, ⟨htV, ht0⟩, rfl⟩, htG⟩

theorem restrict_O_BCF {T' : Set H} (G : Set H) (hG : IsOpen G)
    (hTT' : T' ∩ (d.O ∩ G) = T ∩ (d.O ∩ G)) : (d.restrict_BCF G hG hTT').O = d.O ∩ G := rfl

/-- **Half charts make a set regular**: a chart point is a limit of relative interior points. -/
theorem mem_closure_relInterior_BCF {z : H} (hzT : z ∈ T) (hzO : z ∈ d.O) :
    z ∈ closure (Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs)) := by
  obtain ⟨ht, hz⟩ := d.exists_param_BCF hzT hzO
  set t₀ := d.L z + d.κ with ht₀
  have hcont : ContinuousWithinAt d.π (Ioi t₀) t₀ :=
    (d.continuousOn_π_BCF.continuousAt (d.isOpen_W.mem_nhds (d.V_subset ht.1))).continuousWithinAt
  have hev : ∀ᶠ t in 𝓝[>] t₀,
      d.π t ∈ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs) := by
    filter_upwards [nhdsWithin_le_nhds (d.isOpen_V.mem_nhds ht.1), self_mem_nhdsWithin]
      with t htV htlt
    have hpos : 0 < t := lt_of_le_of_lt (mem_Ici.mp ht.2) htlt
    have hπT : d.π t ∈ T ∩ d.O := d.inter_eq ▸ ⟨t, ⟨htV, mem_Ici.mpr hpos.le⟩, rfl⟩
    refine d.mem_relInterior_of_pos_BCF hπT.1 hπT.2 ?_
    rw [d.coord t (d.V_subset htV)]
    exact hpos
  have hlim : Tendsto d.π (𝓝[>] t₀) (𝓝 z) := hz ▸ hcont.tendsto
  exact mem_closure_of_tendsto hlim hev

end HalfChart_BCF

namespace GraphAtlas1_BCF

variable {ι : Type*} {Bs : Set H} (At : GraphAtlas1_BCF ι Bs)

include At in
/-- **K1 (D74-9): `K₃`, `D₃ = K₃ ∩ C₃` and the faces of `D₃`.** For a compact `Kset ⊆ Bs` and a
relatively closed `C ⊆ Bs` whose relative frontier `∂C` is finite, lies in `Kset`, and carries half
charts of `C`, there are compact smooth one-dimensional domains `K` and `D` of `Bs` (arcs AND loops)
with `D = K ∩ C`, `Kset ⊆ int K`, `∂K ∩ ∂C = ∅`, `∂D = (∂K ∩ int C) ⊔ (int K ∩ ∂C)`, and `D`
regular in `Bs`. -/
theorem exists_compact_intersection_faces_BCF {Kset C : Set H} (hK : IsCompact Kset)
    (hKB : Kset ⊆ Bs) (hCcl : ∃ F : Set H, IsClosed F ∧ C = F ∩ Bs)
    (hCfin : (C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)).Finite)
    (hCch : ∀ y ∈ C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs),
      ∃ d : HalfChart_BCF Bs C, y ∈ d.O)
    (hfront : C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs) ⊆ Kset) :
    ∃ K D : SmoothCompactOneDomain_BCF Bs,
      D.carrier = K.carrier ∩ C ∧
      Kset ⊆ Subtype.val '' interior (Subtype.val ⁻¹' K.carrier : Set Bs) ∧
      Disjoint (K.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' K.carrier : Set Bs))
        (C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)) ∧
      D.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set Bs) =
        ((K.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' K.carrier : Set Bs)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K.carrier : Set Bs) ∩
          (C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs))) ∧
      Disjoint ((K.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' K.carrier : Set Bs)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs))
        (Subtype.val '' interior (Subtype.val ⁻¹' K.carrier : Set Bs) ∩
          (C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs))) ∧
      D.carrier ⊆ closure (Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set Bs)) := by
  obtain ⟨F, hF, hCF⟩ := hCcl
  have hCB : C ⊆ Bs := hCF ▸ inter_subset_right
  have hDreg : C ⊆ closure (Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)) := by
    intro y hy
    by_cases hyI : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)
    · exact subset_closure hyI
    · obtain ⟨d, hyd⟩ := hCch y ⟨hy, hyI⟩
      exact d.mem_closure_relInterior_BCF hy hyd
  obtain ⟨n, c, a, b, hab, hgen, hcpt, hsub, hcov, hreg⟩ :=
    At.exists_cover_union_generic_BCF hK hKB hCfin hDreg hfront
  set T := ⋃ r, At.param (c r) '' Icc (a r) (b r) with hT
  have hch : ∀ y : T, ∃ d : HalfChart_BCF Bs T, (y : H) ∈ d.O := fun y =>
    At.exists_halfChart_of_cover_BCF (fun r => ⟨(hab r).1, (hab r).2.1⟩) hgen y.2
  have hdisj : Disjoint (T \ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs))
      (C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)) := by
    rw [Set.disjoint_left]
    rintro y ⟨hyT, hyI⟩ hyF
    obtain ⟨r, t, ht, rfl⟩ := mem_iUnion.mp hyT
    by_cases hto : t ∈ Ioo (a r) (b r)
    · exact hyI (At.image_Ioo_subset_relInterior_BCF (hab r).2.1
        (subset_iUnion (fun r => At.param (c r) '' Icc (a r) (b r)) r) ⟨t, hto, rfl⟩)
    · have hend : t = a r ∨ t = b r := by
        by_contra h
        push Not at h
        exact hto ⟨lt_of_le_of_ne ht.1 (Ne.symm h.1), lt_of_le_of_ne ht.2 h.2⟩
      rcases hend with rfl | rfl
      · exact (hab r).2.2.1 hyF
      · exact (hab r).2.2.2 hyF
  have hchD : ∀ y : ↥(T ∩ C), ∃ d : HalfChart_BCF Bs (T ∩ C), (y : H) ∈ d.O := by
    rintro ⟨y, hyT, hyC⟩
    by_cases hyI : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)
    · obtain ⟨-, G, hG, hyG, hGC⟩ := mem_image_interior_preimage_val_iff.mp hyI
      obtain ⟨d, hyd⟩ := hch ⟨y, hyT⟩
      have hTT' : (T ∩ C) ∩ (d.O ∩ G) = T ∩ (d.O ∩ G) := by
        ext z
        constructor
        · rintro ⟨⟨hzT, -⟩, hz⟩
          exact ⟨hzT, hz⟩
        · rintro ⟨hzT, hzO, hzG⟩
          exact ⟨⟨hzT, hGC ⟨hzG, hsub hzT⟩⟩, hzO, hzG⟩
      exact ⟨d.restrict_BCF G hG hTT', hyd, hyG⟩
    · have hyK : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs) := by
        by_contra h
        exact hdisj.ne_of_mem ⟨hyT, h⟩ ⟨hyC, hyI⟩ rfl
      obtain ⟨-, G, hG, hyG, hGT⟩ := mem_image_interior_preimage_val_iff.mp hyK
      obtain ⟨d, hyd⟩ := hCch y ⟨hyC, hyI⟩
      have hTT' : (T ∩ C) ∩ (d.O ∩ G) = C ∩ (d.O ∩ G) := by
        ext z
        constructor
        · rintro ⟨⟨-, hzC⟩, hz⟩
          exact ⟨hzC, hz⟩
        · rintro ⟨hzC, hzO, hzG⟩
          exact ⟨⟨hGT ⟨hzG, hCB hzC⟩, hzC⟩, hzO, hzG⟩
      exact ⟨d.restrict_BCF G hG hTT', hyd, hyG⟩
  choose chT hchT using hch
  choose chD hchD using hchD
  obtain ⟨K, hKT⟩ := exists_smoothCompactOneDomain_BCF ⟨chT, hchT⟩ hcpt
  have hTC : T ∩ C = T ∩ F := by
    rw [hCF]
    ext z
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hsub h.1⟩⟩
  have hTCcpt : IsCompact (T ∩ C) := hTC ▸ hcpt.inter_right hF
  obtain ⟨D, hDT⟩ := exists_smoothCompactOneDomain_BCF ⟨chD, hchD⟩ hTCcpt
  have hfaces := relFrontier_inter_BCF hdisj
  refine ⟨K, D, by rw [hDT, hKT], hKT ▸ hcov, hKT ▸ hdisj, ?_, hKT ▸ hfaces.2, hDT ▸ hreg⟩
  rw [hDT, hKT]
  exact hfaces.1

end GraphAtlas1_BCF

end DifferentialGeometry.Topology
