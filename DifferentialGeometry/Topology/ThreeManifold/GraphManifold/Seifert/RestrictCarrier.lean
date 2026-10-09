import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Restrict
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

/-!
# The carrier of a restricted torus presentation

Chapter 6, K22b. For a torus presentation `T` of `W` and a finset `S` of pieces owning no
external torus of `W` (`hext`; automatic when `W` is closed, `externalPiece_not_mem_of_closed`),
the region `Set.range (T.restrictMap S)` of K22a (the image of the pieces of `S`) is given the
structure of a compact carrier with boundary, `restrictCarrier S hext`, as a `SmoothBoundaryAtlas`
inside `W`, and `T.restrict S hS hext` is a torus presentation of it whose cut carrier, pieces,
pairing and cut boundary tori are those of K22a and whose reconstruction is `restrictHomeomorph`.

A seam is crossing (`IsCrossing`) when exactly one of its sides lies in `S`; the image meets the
image of the other pieces only along the crossing seam tori (`crossingSurface`,
`range_inter_complImage_subset_crossing`), and inside the collar of a crossing seam it is the half
`s ≤ 0` or `s ≥ 0` on the side of `S` (`seam_mem_range_iff_of_left`, `_of_right`). Every point of
the region is an interior point of `W` (`isInteriorPoint_of_mem_range`). The ambient charts
(`exists_restrict_chart`) are, on the crossing tori, the regular-sublevel charts of the collar
coordinate `∓ s` pulled back along the seam (`exists_seam_chart`, from
`SmoothBoundaryAtlas.exists_partialDiffeomorph_coord_eq_sub`), and elsewhere interior charts of
`W` shifted into `{x₀ > 0}` and shrunk into the open set `range \ crossingSurface`. So the
boundary of the carrier is the union of the crossing seam tori
(`restrictCarrier_isBoundaryPoint_iff`), and the orientation is restricted from `W`.

The external tori of the restriction are the half collars of the crossing seams on the side of
`S` (`leftCrossCollar`, `rightCrossCollar`, `crossCollar`, `restrictExternal`), written in seam
coordinates; they exhaust the boundary (`restrictExternal_exhausted`). The kept seams are those of
`T`, corestricted through `SmoothBoundaryAtlas.interiorPartialDiffeomorph` (`restrictSeam`). The
interior diffeomorphism is that of `T` restricted to the pieces of `S`
(`restrictInteriorDiffeomorph`), and `quotient_oriented` follows from that of `T` and the bijective
differential of the inclusion (`restrictQuotientMap_oriented`). Counts: `restrict_components_count`,
`restrict_pairing_count`, `restrict_externalCount` (the crossing seams); the reconstructed region is
the image of the pieces of `S` (`restrict_reconstruction_range`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace TorusPresentation
variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count))

def IsCrossing (k : Fin T.pairing.count) : Prop :=
  (T.leftPiece k ∈ S ∧ T.rightPiece k ∉ S) ∨ (T.rightPiece k ∈ S ∧ T.leftPiece k ∉ S)

def crossingSurface : Set W.Carrier := ⋃ k, ⋃ (_ : T.IsCrossing S k), T.seamSurface k

theorem isClosed_crossingSurface : IsClosed (T.crossingSurface S) :=
  isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => T.isClosed_seamSurface k

private theorem cutMap_mem_seamSurface_of_block (k : Fin T.pairing.count)
    {x : T.cutCarrier.Carrier} (hx : x ∈ T.pairing.gluing.block k) :
    T.cutMap x ∈ T.seamSurface k := by
  rcases hx with hx | hx
  · refine ⟨(T.pairing.leftParam k).symm ⟨x, hx⟩, ?_⟩
    rw [seamTorus_eq_cutMap, Homeomorph.apply_symm_apply]
  · refine ⟨(T.pairing.matching k).symm ((T.pairing.rightParam k).symm ⟨x, hx⟩), ?_⟩
    rw [seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem range_inter_complImage_subset_crossing :
    Set.range (T.restrictMap S) ∩ T.complImage S ⊆ T.crossingSurface S := by
  rw [range_restrictMap]
  rintro w ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  rcases Quotient.exact (T.reconstruction.injective hxy) with h | ⟨k, hk, hxk⟩
  · exact (hy (h ▸ hx)).elim
  have hmem : T.cutMap x ∈ T.seamSurface k := by
    rw [← hxy]
    exact T.cutMap_mem_seamSurface_of_block k hk
  refine Set.mem_iUnion₂.mpr ⟨k, ?_, hmem⟩
  rcases hk with hl | hr
  · have hxr : x ∈ T.pairing.gluing.right k := by
      rw [hxk, T.pairing.gluing.flip_of_mem_left hl]
      exact (T.pairing.gluing.attaching k ⟨y, hl⟩).property
    exact Or.inr ⟨T.mem_of_mem_subPiece S hx (T.right_owned k hxr),
      fun h => hy (T.piece_subset_subPiece S h (T.left_owned k hl))⟩
  · have hxl : x ∈ T.pairing.gluing.left k := by
      rw [hxk, T.pairing.gluing.flip_of_mem_right hr]
      exact ((T.pairing.gluing.attaching k).symm ⟨y, hr⟩).property
    exact Or.inl ⟨T.mem_of_mem_subPiece S hx (T.left_owned k hxl),
      fun h => hy (T.piece_subset_subPiece S h (T.right_owned k hr))⟩

theorem range_diff_crossingSurface_eq :
    Set.range (T.restrictMap S) \ T.crossingSurface S =
      (T.complImage S ∪ T.crossingSurface S)ᶜ := by
  ext x
  constructor
  · rintro ⟨hx, hs⟩ (hc | hc)
    · exact hs (T.range_inter_complImage_subset_crossing S ⟨hx, hc⟩)
    · exact hs hc
  · intro hx
    have hx' : x ∈ Set.range (T.restrictMap S) ∪ T.complImage S := by
      rw [T.range_union_complImage S]
      exact Set.mem_univ x
    rcases hx' with h | h
    · exact ⟨h, fun hs => hx (Or.inr hs)⟩
    · exact (hx (Or.inl h)).elim

theorem isOpen_range_diff_crossingSurface :
    IsOpen (Set.range (T.restrictMap S) \ T.crossingSurface S) := by
  rw [T.range_diff_crossingSurface_eq S]
  exact ((T.isClosed_complImage S).union (T.isClosed_crossingSurface S)).isOpen_compl

private theorem snd_eq_zero_of_mem_seamSurface'' (k : Fin T.pairing.count) {p : Torus × ℝ}
    (hp : p ∈ signedCollarSource) (h : T.seam k p ∈ T.seamSurface k) : p.2 = 0 := by
  obtain ⟨t, ht⟩ := h
  rw [← (T.seam k).toPartialEquiv.injOn
    (T.mem_seam_source k ⟨by norm_num, by norm_num⟩) (T.mem_seam_source k hp) ht]

theorem snd_eq_zero_of_seam_mem_crossingSurface (k : Fin T.pairing.count) {p : Torus × ℝ}
    (hp : p ∈ signedCollarSource) (h : T.seam k p ∈ T.crossingSurface S) : p.2 = 0 := by
  obtain ⟨k', -, hk'⟩ := Set.mem_iUnion₂.mp h
  by_cases hkk : k' = k
  · subst hkk
    exact T.snd_eq_zero_of_mem_seamSurface'' k' hp hk'
  · exact ((T.seam_disjoint hkk).le_bot ⟨T.seamSurface_subset_seamCollar k' hk',
      (T.seam k).map_source' (T.mem_seam_source k hp)⟩).elim

theorem seam_mem_range_of_nonpos (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ S)
    {p : Torus × ℝ} (hp : p ∈ signedCollarSource) (h : p.2 ≤ 0) :
    T.seam k p ∈ Set.range (T.restrictMap S) := by
  rw [range_restrictMap]
  have hq : (p.1, halfPoint (-p.2) (neg_nonneg.mpr h)) ∈ halfCollarSource := by
    change -p.2 < 1
    linarith [hp.1]
  refine ⟨T.pairing.leftCollar k (p.1, halfPoint (-p.2) (neg_nonneg.mpr h)),
    T.sideCollar_target_subset_subPiece S (s := .inl k) hl
      ((T.pairing.leftCollar k).map_source (by rw [T.pairing.left_source]; exact hq)), ?_⟩
  rw [T.cutMap_leftCollar k hq]
  change T.seam k (p.1, -(-p.2)) = T.seam k p
  rw [neg_neg]

theorem seam_mem_range_of_nonneg (k : Fin T.pairing.count) (hr : T.rightPiece k ∈ S)
    {p : Torus × ℝ} (hp : p ∈ signedCollarSource) (h : 0 ≤ p.2) :
    T.seam k p ∈ Set.range (T.restrictMap S) := by
  rw [range_restrictMap]
  have hq : (T.pairing.matching k p.1, halfPoint p.2 h) ∈ halfCollarSource := hp.2
  refine ⟨T.pairing.rightCollar k (T.pairing.matching k p.1, halfPoint p.2 h),
    T.sideCollar_target_subset_subPiece S (s := .inr (.inl k)) hr
      ((T.pairing.rightCollar k).map_source (by rw [T.pairing.right_source]; exact hq)), ?_⟩
  rw [T.cutMap_rightCollar k hq, Diffeomorph.symm_apply_apply]
  rfl

theorem seam_mem_complImage_of_nonpos (k : Fin T.pairing.count) (hl : T.leftPiece k ∉ S)
    {p : Torus × ℝ} (hp : p ∈ signedCollarSource) (h : p.2 ≤ 0) :
    T.seam k p ∈ T.complImage S := by
  have hq : (p.1, halfPoint (-p.2) (neg_nonneg.mpr h)) ∈ halfCollarSource := by
    change -p.2 < 1
    linarith [hp.1]
  refine ⟨T.pairing.leftCollar k (p.1, halfPoint (-p.2) (neg_nonneg.mpr h)), fun hmem =>
    hl (T.mem_of_mem_subPiece S hmem (T.sideCollar_target_subset (.inl k)
      ((T.pairing.leftCollar k).map_source (by rw [T.pairing.left_source]; exact hq)))), ?_⟩
  rw [T.cutMap_leftCollar k hq]
  change T.seam k (p.1, -(-p.2)) = T.seam k p
  rw [neg_neg]

theorem seam_mem_range_iff_of_left (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ S)
    (hr : T.rightPiece k ∉ S) {p : Torus × ℝ} (hp : p ∈ signedCollarSource) :
    T.seam k p ∈ Set.range (T.restrictMap S) ↔ p.2 ≤ 0 := by
  refine ⟨fun h => ?_, T.seam_mem_range_of_nonpos S k hl hp⟩
  by_contra hpos
  have hc := T.seam_mem_complImage S k hr p.1 (le_of_lt (not_le.mp hpos)) hp.2
  have h0 := T.snd_eq_zero_of_seam_mem_crossingSurface S k hp
    (T.range_inter_complImage_subset_crossing S ⟨h, hc⟩)
  exact hpos h0.le

theorem seam_mem_range_iff_of_right (k : Fin T.pairing.count) (hr : T.rightPiece k ∈ S)
    (hl : T.leftPiece k ∉ S) {p : Torus × ℝ} (hp : p ∈ signedCollarSource) :
    T.seam k p ∈ Set.range (T.restrictMap S) ↔ 0 ≤ p.2 := by
  refine ⟨fun h => ?_, T.seam_mem_range_of_nonneg S k hr hp⟩
  by_contra hneg
  have hc := T.seam_mem_complImage_of_nonpos S k hl hp (le_of_lt (not_le.mp hneg))
  have h0 := T.snd_eq_zero_of_seam_mem_crossingSurface S k hp
    (T.range_inter_complImage_subset_crossing S ⟨h, hc⟩)
  exact hneg h0.ge

theorem isInteriorPoint_of_mem_range (hext : ∀ i, T.externalPiece i ∉ S) {x : W.Carrier}
    (hx : x ∈ Set.range (T.restrictMap S)) : W.model.IsInteriorPoint x := by
  rcases W.model.isInteriorPoint_or_isBoundaryPoint x with h | h
  · exact h
  exfalso
  have hb : x ∈ W.model.boundary W.Carrier := h
  rw [T.external_exhausted] at hb
  obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hb
  have hc : T.external.torusMap i t ∈ T.complImage S :=
    ⟨T.cutExternal.collar i (t, halfZero), fun hmem =>
      hext i (T.mem_of_mem_subPiece S hmem (T.external_owned i ⟨t, rfl⟩)),
      T.marked_collar i _ (zero_mem_halfCollarSource t)⟩
  obtain ⟨k, -, hk⟩ := Set.mem_iUnion₂.mp
    (T.range_inter_complImage_subset_crossing S ⟨hx, hc⟩)
  have hxt : T.external.torusMap i t ∈ (T.external.collar i).target :=
    (T.external.collar i).map_source' ((T.external.source_eq i).symm ▸
      zero_mem_halfCollarSource t)
  exact (T.external_seam_disjoint i k).le_bot ⟨hxt, T.seamSurface_subset_seamCollar k hk⟩

private theorem exists_positive_chart {x : W.Carrier} (hx : W.model.IsInteriorPoint x)
    {U : Set W.Carrier} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ φ : PartialDiffeomorph W.model (𝓡 3) W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
      x ∈ φ.source ∧ φ.source ⊆ U ∧ ∀ y ∈ φ.source, 0 < φ y 0 := by
  let c := DifferentialGeometry.Manifold.interiorChart W.model ∞ x
  let D := SmoothBoundaryAtlas.affineDiffeomorph
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)))
    ((1 - c x 0) • EuclideanSpace.single 0 1)
  let ψ := c.trans D.toPartialDiffeomorph
  have hψx : ψ x 0 = 1 := by
    change (c x + (1 - c x 0) • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 3)) 0 = 1
    simp
  have hxc : x ∈ c.source := ⟨mem_chart_source _ x, (W.model.isInteriorPoint_iff).mp hx⟩
  have hxψ : x ∈ ψ.source := ⟨hxc, Set.mem_univ _⟩
  let V := (ψ.source ∩ ψ ⁻¹' {v : EuclideanSpace ℝ (Fin 3) | 0 < v 0}) ∩ U
  have hV : IsOpen V :=
    (ψ.contMDiffOn.continuousOn.isOpen_inter_preimage ψ.open_source
      (isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous))).inter hU
  let φ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict ψ V hV
  exact ⟨φ, ⟨hxψ, ⟨hxψ, by simp [hψx]⟩, hxU⟩, fun y hy => hy.2.2, fun y hy => hy.2.1.2⟩

private theorem finrank_signedCollar :
    Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) = 2 + 1 := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]

private theorem mfderiv_snd_ne_zero (p : Torus × ℝ) :
    mfderiv signedCollarModel 𝓘(ℝ, ℝ) (Prod.snd : Torus × ℝ → ℝ) p ≠ 0 := by
  rw [mfderiv_snd]
  intro h
  have := congrArg (fun L => L ((0 : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)),
    (1 : ℝ))) h
  change (1 : ℝ) = 0 at this
  exact one_ne_zero this

private theorem exists_seam_chart (k : Fin T.pairing.count) {f : Torus × ℝ → ℝ}
    (hf : ContMDiff signedCollarModel 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ p, mfderiv signedCollarModel 𝓘(ℝ, ℝ) f p ≠ 0)
    {x : W.Carrier} (hx : x ∈ (T.seam k).target) :
    ∃ φ : PartialDiffeomorph W.model (𝓡 3) W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
      x ∈ φ.source ∧ φ.source ⊆ (T.seam k).target ∧
        ∀ y ∈ φ.source, φ y 0 = -f ((T.seam k).symm y) := by
  obtain ⟨ψ, hψ, hψf⟩ := SmoothBoundaryAtlas.exists_partialDiffeomorph_coord_eq_sub
    signedCollarModel finrank_signedCollar hf (hreg ((T.seam k).symm x)) 0
  refine ⟨(T.seam k).symm.trans ψ, ⟨hx, hψ⟩, fun y hy => hy.1, fun y hy => ?_⟩
  have h := hψf ((T.seam k).symm y) hy.2
  rw [zero_sub] at h
  exact h

theorem exists_restrict_chart (hext : ∀ i, T.externalPiece i ∉ S) {x : W.Carrier}
    (hx : x ∈ Set.range (T.restrictMap S)) :
    ∃ φ : PartialDiffeomorph W.model (𝓡 3) W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
      x ∈ φ.source ∧ (∀ y ∈ φ.source, y ∈ Set.range (T.restrictMap S) ↔ 0 ≤ φ y 0) ∧
        (φ x 0 = 0 ↔ x ∈ T.crossingSurface S) := by
  by_cases hcx : x ∈ T.crossingSurface S
  · obtain ⟨k, hk, t, rfl⟩ := Set.mem_iUnion₂.mp hcx
    have hx0 : T.seamTorus k t ∈ (T.seam k).target := T.seamTorus_mem_seamCollar k t
    have hsymm : (T.seam k).symm (T.seamTorus k t) = (t, 0) :=
      (T.seam k).left_inv (T.mem_seam_source k ⟨by norm_num, by norm_num⟩)
    rcases hk with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · obtain ⟨φ, hφx, hφs, hφ⟩ := T.exists_seam_chart k contMDiff_snd mfderiv_snd_ne_zero hx0
      refine ⟨φ, hφx, fun y hy => ?_, ?_⟩
      · have hyt := hφs hy
        have hsrc : (T.seam k).symm y ∈ signedCollarSource :=
          T.seam_source k ▸ (T.seam k).map_target' hyt
        have key := T.seam_mem_range_iff_of_left S k hl hr hsrc
        have hy' : T.seam k ((T.seam k).symm y) = y := (T.seam k).right_inv' hyt
        rw [hy'] at key
        rw [hφ y hy, key]
        constructor <;> intro h <;> linarith
      · rw [hφ _ hφx, hsymm]
        simp only [neg_zero, true_iff]
        exact hcx
    · obtain ⟨φ, hφx, hφs, hφ⟩ := T.exists_seam_chart k (f := -Prod.snd)
        contMDiff_snd.neg (fun p => by
          rw [mfderiv_neg]
          exact neg_ne_zero.mpr (mfderiv_snd_ne_zero p)) hx0
      refine ⟨φ, hφx, fun y hy => ?_, ?_⟩
      · have hyt := hφs hy
        have hsrc : (T.seam k).symm y ∈ signedCollarSource :=
          T.seam_source k ▸ (T.seam k).map_target' hyt
        have key := T.seam_mem_range_iff_of_right S k hr hl hsrc
        have hy' : T.seam k ((T.seam k).symm y) = y := (T.seam k).right_inv' hyt
        rw [hy'] at key
        rw [hφ y hy, key, Pi.neg_apply, neg_neg]
      · rw [hφ _ hφx, hsymm, Pi.neg_apply, neg_neg]
        exact iff_of_true rfl hcx
  · obtain ⟨φ, hφx, hφU, hφ⟩ := exists_positive_chart (W := W)
      (T.isInteriorPoint_of_mem_range S hext hx) (T.isOpen_range_diff_crossingSurface S)
      ⟨hx, hcx⟩
    refine ⟨φ, hφx, fun y hy => iff_of_true (hφU hy).1 (hφ y hy).le, ?_⟩
    exact iff_of_false (hφ x hφx).ne' hcx

def restrictAtlas (hext : ∀ i, T.externalPiece i ∉ S) :
    SmoothBoundaryAtlas W.model 3 (Set.range (T.restrictMap S)) where
  ambientChart x := Classical.choose (T.exists_restrict_chart S hext x.property)
  mem_source x := (Classical.choose_spec (T.exists_restrict_chart S hext x.property)).1
  mem_iff x := (Classical.choose_spec (T.exists_restrict_chart S hext x.property)).2.1

theorem restrictAtlas_isBoundaryPoint_iff (hext : ∀ i, T.externalPiece i ∉ S)
    (x : Set.range (T.restrictMap S)) :
    letI := (T.restrictAtlas S hext).toChartedSpace
    (𝓡∂ 3).IsBoundaryPoint x ↔ x.val ∈ T.crossingSurface S :=
  ((T.restrictAtlas S hext).isBoundaryPoint_iff x).trans
    (Classical.choose_spec (T.exists_restrict_chart S hext x.property)).2.2

def restrictCarrier (hext : ∀ i, T.externalPiece i ∉ S) : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := Set.range (T.restrictMap S)
  charts := (T.restrictAtlas S hext).toChartedSpace
  smooth := (T.restrictAtlas S hext).isManifold
  compact := isCompact_iff_compactSpace.mp (T.isClosed_range_restrictMap S).isCompact
  orientation := (T.restrictAtlas S hext).orientation W.orientation

theorem restrictCarrier_carrier (hext : ∀ i, T.externalPiece i ∉ S) :
    (T.restrictCarrier S hext).Carrier = Set.range (T.restrictMap S) := rfl

theorem restrictCarrier_isBoundaryPoint_iff (hext : ∀ i, T.externalPiece i ∉ S)
    (x : (T.restrictCarrier S hext).Carrier) :
    (T.restrictCarrier S hext).model.IsBoundaryPoint x ↔ x.val ∈ T.crossingSurface S :=
  T.restrictAtlas_isBoundaryPoint_iff S hext x

theorem contMDiff_restrictCarrier_val (hext : ∀ i, T.externalPiece i ∉ S) :
    ContMDiff (T.restrictCarrier S hext).model W.model ∞
      (fun x : (T.restrictCarrier S hext).Carrier => x.val) :=
  (T.restrictAtlas S hext).contMDiff_subtype_val

theorem contMDiffOn_restrictCarrier_iff (hext : ∀ i, T.externalPiece i ∉ S)
    {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    (f : X → (T.restrictCarrier S hext).Carrier) (s : Set X) :
    ContMDiffOn J (T.restrictCarrier S hext).model ∞ f s ↔
      ContMDiffOn J W.model ∞ (fun x => (f x).val) s :=
  (T.restrictAtlas S hext).contMDiffOn_iff_subtype_val f s

theorem contMDiff_restrictCarrier_iff (hext : ∀ i, T.externalPiece i ∉ S)
    {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    (f : X → (T.restrictCarrier S hext).Carrier) :
    ContMDiff J (T.restrictCarrier S hext).model ∞ f ↔
      ContMDiff J W.model ∞ (fun x => (f x).val) :=
  (T.restrictAtlas S hext).contMDiff_iff_subtype_val f

private theorem halfSpaceOneLift_coord (h : EuclideanHalfSpace 1) :
    Manifold.halfSpaceOneLift (h.val 0) = h := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  change max (h.val 0) 0 = h.val 0
  exact max_eq_left h.2

private theorem halfSpaceOneLift_val (a : ℝ) : (Manifold.halfSpaceOneLift a).val 0 = max a 0 :=
  rfl

private theorem isOpen_halfCollarSource : IsOpen halfCollarSource :=
  isOpen_lt ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const

private theorem neg_mem_signedCollarSource' {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) : (p.1, -(p.2.val 0)) ∈ signedCollarSource := by
  have h1 : p.2.val 0 < 1 := hp
  have h0 : 0 ≤ p.2.val 0 := p.2.2
  exact ⟨by simp only; linarith, by simp only; linarith⟩

private theorem contMDiff_halfCollar_neg :
    ContMDiff halfCollarModel signedCollarModel ∞
      (fun q : Torus × EuclideanHalfSpace 1 => (q.1, -q.2.val 0)) :=
  contMDiff_fst.prodMk (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).neg

theorem restrictMap_subCollar_left (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ S)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.restrictMap S ((T.restrictPairing S).quotientMap (T.subCollar S (.inl k) hl p)) =
      T.seam k (p.1, -(p.2.val 0)) := by
  rw [restrictMap_quotientMap, T.subCollar_apply S (.inl k) hl hp]
  exact T.cutMap_leftCollar k hp

theorem restrictMap_subCollar_right (k : Fin T.pairing.count) (hr : T.rightPiece k ∈ S)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.restrictMap S ((T.restrictPairing S).quotientMap (T.subCollar S (.inr (.inl k)) hr p)) =
      T.seam k ((T.pairing.matching k).symm p.1, p.2.val 0) := by
  rw [restrictMap_quotientMap, T.subCollar_apply S (.inr (.inl k)) hr hp]
  exact T.cutMap_rightCollar k hp

def crossMap (hext : ∀ i, T.externalPiece i ∉ S) (s : T.Side) (hs : T.sidePiece s ∈ S)
    (p : Torus × EuclideanHalfSpace 1) : (T.restrictCarrier S hext).Carrier :=
  ⟨T.restrictMap S ((T.restrictPairing S).quotientMap (T.subCollar S s hs p)),
    Set.mem_range_self _⟩

theorem crossMap_val (hext : ∀ i, T.externalPiece i ∉ S) (s : T.Side) (hs : T.sidePiece s ∈ S)
    (p : Torus × EuclideanHalfSpace 1) :
    (T.crossMap S hext s hs p).val =
      T.restrictMap S ((T.restrictPairing S).quotientMap (T.subCollar S s hs p)) := rfl

def leftCrossInv (k : Fin T.pairing.count) (y : W.Carrier) : Torus × EuclideanHalfSpace 1 :=
  (((T.seam k).symm y).1, Manifold.halfSpaceOneLift (-((T.seam k).symm y).2))

theorem seam_symm_mem (k : Fin T.pairing.count) {y : W.Carrier} (hy : y ∈ (T.seam k).target) :
    (T.seam k).symm y ∈ signedCollarSource :=
  T.seam_source k ▸ (T.seam k).map_target' hy

theorem seam_symm_snd_nonpos (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ S)
    (hr : T.rightPiece k ∉ S) {y : W.Carrier} (hy : y ∈ (T.seam k).target)
    (hyR : y ∈ Set.range (T.restrictMap S)) : ((T.seam k).symm y).2 ≤ 0 := by
  have key := T.seam_mem_range_iff_of_left S k hl hr (T.seam_symm_mem k hy)
  have hy' : T.seam k ((T.seam k).symm y) = y := (T.seam k).right_inv' hy
  rw [hy'] at key
  exact key.mp hyR

theorem seam_symm_snd_nonneg (k : Fin T.pairing.count) (hr : T.rightPiece k ∈ S)
    (hl : T.leftPiece k ∉ S) {y : W.Carrier} (hy : y ∈ (T.seam k).target)
    (hyR : y ∈ Set.range (T.restrictMap S)) : 0 ≤ ((T.seam k).symm y).2 := by
  have key := T.seam_mem_range_iff_of_right S k hr hl (T.seam_symm_mem k hy)
  have hy' : T.seam k ((T.seam k).symm y) = y := (T.seam k).right_inv' hy
  rw [hy'] at key
  exact key.mp hyR

theorem leftCrossInv_mem (k : Fin T.pairing.count) {y : W.Carrier}
    (hy : y ∈ (T.seam k).target) : T.leftCrossInv k y ∈ halfCollarSource := by
  have hs := T.seam_symm_mem k hy
  change max (-((T.seam k).symm y).2) 0 < 1
  exact max_lt (by linarith [hs.1]) one_pos

def leftCrossCollar (hext : ∀ i, T.externalPiece i ∉ S) (k : Fin T.pairing.count)
    (hl : T.leftPiece k ∈ S) (hr : T.rightPiece k ∉ S) :
    PartialDiffeomorph halfCollarModel (T.restrictCarrier S hext).model
      (Torus × EuclideanHalfSpace 1) (T.restrictCarrier S hext).Carrier ∞ where
  toFun := T.crossMap S hext (.inl k) hl
  invFun y := T.leftCrossInv k y.val
  source := halfCollarSource
  target := Subtype.val ⁻¹' (T.seam k).target
  map_source' p hp := by
    have hv : (T.crossMap S hext (.inl k) hl p).val = T.seam k (p.1, -(p.2.val 0)) :=
      T.restrictMap_subCollar_left S k hl hp
    change (T.crossMap S hext (.inl k) hl p).val ∈ (T.seam k).target
    rw [hv]
    exact (T.seam k).map_source' (T.mem_seam_source k (neg_mem_signedCollarSource' hp))
  map_target' y hy := T.leftCrossInv_mem k hy
  left_inv' p hp := by
    have hv := T.restrictMap_subCollar_left S k hl hp
    have hinv : (T.seam k).symm (T.seam k (p.1, -(p.2.val 0))) = (p.1, -(p.2.val 0)) :=
      (T.seam k).left_inv (T.mem_seam_source k (neg_mem_signedCollarSource' hp))
    have h : T.leftCrossInv k (T.seam k (p.1, -(p.2.val 0))) = p := by
      rw [leftCrossInv, hinv]
      simp only [neg_neg]
      rw [halfSpaceOneLift_coord]
    exact (congrArg (T.leftCrossInv k) hv).trans h
  right_inv' y hy := by
    have hy' : T.seam k ((T.seam k).symm y.val) = y.val := (T.seam k).right_inv' hy
    have hnp := T.seam_symm_snd_nonpos S k hl hr hy y.property
    have hv := T.restrictMap_subCollar_left S k hl (T.leftCrossInv_mem k hy)
    have h : T.seam k ((T.leftCrossInv k y.val).1, -((T.leftCrossInv k y.val).2.val 0)) =
        y.val := by
      rw [leftCrossInv, halfSpaceOneLift_val, max_eq_left (by linarith), neg_neg]
      exact hy'
    exact Subtype.ext (hv.trans h)
  open_source := isOpen_halfCollarSource
  open_target := (T.seam k).open_target.preimage continuous_subtype_val
  contMDiffOn_toFun := by
    refine (T.contMDiffOn_restrictCarrier_iff S hext _ _).mpr ?_
    have h := (T.seam k).contMDiffOn.comp contMDiff_halfCollar_neg.contMDiffOn
      (fun q hq => T.mem_seam_source k (neg_mem_signedCollarSource' hq))
    exact h.congr fun q hq => T.restrictMap_subCollar_left S k hl hq
  contMDiffOn_invFun := by
    have hsymm : ContMDiffOn (T.restrictCarrier S hext).model signedCollarModel ∞
        (fun y : (T.restrictCarrier S hext).Carrier => (T.seam k).symm y.val)
        (Subtype.val ⁻¹' (T.seam k).target) :=
      (T.seam k).contMDiffOn_invFun.comp
        (T.contMDiff_restrictCarrier_val S hext).contMDiffOn (fun y hy => hy)
    have hnn : Set.MapsTo (fun y : (T.restrictCarrier S hext).Carrier =>
        -((T.seam k).symm y.val).2) (Subtype.val ⁻¹' (T.seam k).target) (Set.Ici 0) :=
      fun y hy => neg_nonneg.mpr (T.seam_symm_snd_nonpos S k hl hr hy y.property)
    exact (contMDiff_fst.comp_contMDiffOn hsymm).prodMk
      (Manifold.contMDiffOn_halfSpaceOneLift.comp (contMDiff_snd.comp_contMDiffOn hsymm).neg hnn)


private theorem pos_mem_signedCollarSource' (m : Torus → Torus)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (m p.1, p.2.val 0) ∈ signedCollarSource := by
  have h1 : p.2.val 0 < 1 := hp
  have h0 : 0 ≤ p.2.val 0 := p.2.2
  exact ⟨by simp only; linarith, by simp only; linarith⟩

def rightCrossInv (k : Fin T.pairing.count) (y : W.Carrier) : Torus × EuclideanHalfSpace 1 :=
  (T.pairing.matching k ((T.seam k).symm y).1, Manifold.halfSpaceOneLift ((T.seam k).symm y).2)

theorem rightCrossInv_mem (k : Fin T.pairing.count) {y : W.Carrier}
    (hy : y ∈ (T.seam k).target) : T.rightCrossInv k y ∈ halfCollarSource := by
  have hs := T.seam_symm_mem k hy
  change max ((T.seam k).symm y).2 0 < 1
  exact max_lt hs.2 one_pos

def rightCrossCollar (hext : ∀ i, T.externalPiece i ∉ S) (k : Fin T.pairing.count)
    (hr : T.rightPiece k ∈ S) (hl : T.leftPiece k ∉ S) :
    PartialDiffeomorph halfCollarModel (T.restrictCarrier S hext).model
      (Torus × EuclideanHalfSpace 1) (T.restrictCarrier S hext).Carrier ∞ where
  toFun := T.crossMap S hext (.inr (.inl k)) hr
  invFun y := T.rightCrossInv k y.val
  source := halfCollarSource
  target := Subtype.val ⁻¹' (T.seam k).target
  map_source' p hp := by
    have hv : (T.crossMap S hext (.inr (.inl k)) hr p).val =
        T.seam k ((T.pairing.matching k).symm p.1, p.2.val 0) :=
      T.restrictMap_subCollar_right S k hr hp
    change (T.crossMap S hext (.inr (.inl k)) hr p).val ∈ (T.seam k).target
    rw [hv]
    exact (T.seam k).map_source' (T.mem_seam_source k (pos_mem_signedCollarSource' _ hp))
  map_target' y hy := T.rightCrossInv_mem k hy
  left_inv' p hp := by
    have hv := T.restrictMap_subCollar_right S k hr hp
    have hinv : (T.seam k).symm (T.seam k ((T.pairing.matching k).symm p.1, p.2.val 0)) =
        ((T.pairing.matching k).symm p.1, p.2.val 0) :=
      (T.seam k).left_inv (T.mem_seam_source k (pos_mem_signedCollarSource' _ hp))
    have h : T.rightCrossInv k (T.seam k ((T.pairing.matching k).symm p.1, p.2.val 0)) = p := by
      rw [rightCrossInv, hinv]
      simp only [Diffeomorph.apply_symm_apply]
      rw [halfSpaceOneLift_coord]
    exact (congrArg (T.rightCrossInv k) hv).trans h
  right_inv' y hy := by
    have hy' : T.seam k ((T.seam k).symm y.val) = y.val := (T.seam k).right_inv' hy
    have hnn := T.seam_symm_snd_nonneg S k hr hl hy y.property
    have hv := T.restrictMap_subCollar_right S k hr (T.rightCrossInv_mem k hy)
    have h : T.seam k ((T.pairing.matching k).symm (T.rightCrossInv k y.val).1,
        (T.rightCrossInv k y.val).2.val 0) = y.val := by
      rw [rightCrossInv]
      simp only [Diffeomorph.symm_apply_apply]
      rw [halfSpaceOneLift_val, max_eq_left hnn]
      exact hy'
    exact Subtype.ext (hv.trans h)
  open_source := isOpen_halfCollarSource
  open_target := (T.seam k).open_target.preimage continuous_subtype_val
  contMDiffOn_toFun := by
    refine (T.contMDiffOn_restrictCarrier_iff S hext _ _).mpr ?_
    have hmap : ContMDiff halfCollarModel signedCollarModel ∞
        (fun q : Torus × EuclideanHalfSpace 1 => ((T.pairing.matching k).symm q.1, q.2.val 0)) :=
      ((T.pairing.matching k).symm.contMDiff.comp contMDiff_fst).prodMk
        (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
    have h := (T.seam k).contMDiffOn.comp hmap.contMDiffOn
      (fun q hq => T.mem_seam_source k (pos_mem_signedCollarSource' _ hq))
    exact h.congr fun q hq => T.restrictMap_subCollar_right S k hr hq
  contMDiffOn_invFun := by
    have hsymm : ContMDiffOn (T.restrictCarrier S hext).model signedCollarModel ∞
        (fun y : (T.restrictCarrier S hext).Carrier => (T.seam k).symm y.val)
        (Subtype.val ⁻¹' (T.seam k).target) :=
      (T.seam k).contMDiffOn_invFun.comp
        (T.contMDiff_restrictCarrier_val S hext).contMDiffOn (fun y hy => hy)
    have hnn : Set.MapsTo (fun y : (T.restrictCarrier S hext).Carrier =>
        ((T.seam k).symm y.val).2) (Subtype.val ⁻¹' (T.seam k).target) (Set.Ici 0) :=
      fun y hy => T.seam_symm_snd_nonneg S k hr hl hy y.property
    exact ((T.pairing.matching k).contMDiff.comp_contMDiffOn
      (contMDiff_fst.comp_contMDiffOn hsymm)).prodMk
      (Manifold.contMDiffOn_halfSpaceOneLift.comp (contMDiff_snd.comp_contMDiffOn hsymm) hnn)

def crossCollar (hext : ∀ i, T.externalPiece i ∉ S) (a : T.RestrictSide S) :
    PartialDiffeomorph halfCollarModel (T.restrictCarrier S hext).model
      (Torus × EuclideanHalfSpace 1) (T.restrictCarrier S hext).Carrier ∞ :=
  match a with
  | ⟨.inl k, hs, hk⟩ => T.leftCrossCollar S hext k hs fun hr => hk ⟨hs, hr⟩
  | ⟨.inr (.inl k), hs, hk⟩ => T.rightCrossCollar S hext k hs fun hl => hk ⟨hl, hs⟩
  | ⟨.inr (.inr i), hs, _⟩ => (hext i hs).elim

theorem crossCollar_source (hext : ∀ i, T.externalPiece i ∉ S) (a : T.RestrictSide S) :
    (T.crossCollar S hext a).source = halfCollarSource := by
  rcases a with ⟨k | k | i, hs, hk⟩
  · rfl
  · rfl
  · exact (hext i hs).elim

theorem crossCollar_apply (hext : ∀ i, T.externalPiece i ∉ S) (a : T.RestrictSide S)
    (p : Torus × EuclideanHalfSpace 1) :
    T.crossCollar S hext a p = T.crossMap S hext a.val a.property.1 p := by
  rcases a with ⟨k | k | i, hs, hk⟩
  · rfl
  · rfl
  · exact (hext i hs).elim

theorem crossCollar_target (hext : ∀ i, T.externalPiece i ∉ S) (a : T.RestrictSide S) :
    (T.crossCollar S hext a).target = Subtype.val ⁻¹' T.sideRegion (T.sideIndex a.val) := by
  rcases a with ⟨k | k | i, hs, hk⟩
  · rfl
  · rfl
  · exact (hext i hs).elim

theorem crossCollar_val (hext : ∀ i, T.externalPiece i ∉ S) (a : T.RestrictSide S)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (T.crossCollar S hext a p).val = T.cutMap (T.sideCollar a.val p) := by
  rw [crossCollar_apply]
  exact congrArg T.cutMap (T.subCollar_apply S a.val a.property.1 hp)

theorem crossCollar_zero_mem (hext : ∀ i, T.externalPiece i ∉ S) (a : T.RestrictSide S)
    (t : Torus) : (T.crossCollar S hext a (t, halfZero)).val ∈ T.crossingSurface S := by
  rw [T.crossCollar_val S hext a (zero_mem_halfCollarSource t)]
  rcases a with ⟨k | k | i, hs, hk⟩
  · refine Set.mem_iUnion₂.mpr ⟨k, Or.inl ⟨hs, fun hr => hk ⟨hs, hr⟩⟩, ?_⟩
    change T.cutMap (T.pairing.leftCollar k (t, halfZero)) ∈ _
    rw [T.pairing.left_zero]
    exact T.cutMap_mem_seamSurface_of_block k (Or.inl (T.pairing.leftParam k t).property)
  · refine Set.mem_iUnion₂.mpr ⟨k, Or.inr ⟨hs, fun hl => hk ⟨hl, hs⟩⟩, ?_⟩
    change T.cutMap (T.pairing.rightCollar k (t, halfZero)) ∈ _
    rw [T.pairing.right_zero]
    exact T.cutMap_mem_seamSurface_of_block k (Or.inr (T.pairing.rightParam k t).property)
  · exact (hext i hs).elim

theorem restrictSide_eq_of_sideIndex_eq (a b : T.RestrictSide S)
    (h : T.sideIndex a.val = T.sideIndex b.val) : a = b := by
  obtain ⟨s, hs, hks⟩ := a
  obtain ⟨s', hs', hks'⟩ := b
  rcases s with k | k | k <;> rcases s' with k' | k' | k' <;>
    simp only [sideIndex, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · subst h
    rfl
  · subst h
    exact (hks ⟨hs, hs'⟩).elim
  · subst h
    exact (hks ⟨hs', hs⟩).elim
  · subst h
    rfl
  · subst h
    rfl

def restrictExternal (hext : ∀ i, T.externalPiece i ∉ S) :
    BoundaryTori (T.restrictCarrier S hext) (Fintype.card (T.RestrictSide S)) where
  collar j := T.crossCollar S hext (T.restrictSide S j)
  source_eq j := T.crossCollar_source S hext _
  boundary_zero j t := (T.restrictCarrier_isBoundaryPoint_iff S hext _).mpr
    (T.crossCollar_zero_mem S hext _ t)
  disjoint j j' h := by
    change Disjoint (T.crossCollar S hext _).target (T.crossCollar S hext _).target
    rw [T.crossCollar_target, T.crossCollar_target]
    exact (T.pairwise_disjoint_sideRegion fun e => h ((Fintype.equivFin _).symm.injective
      (T.restrictSide_eq_of_sideIndex_eq S _ _ e))).preimage _

theorem seam_target_subset_interior_range (j : Fin (T.restrictPairing S).count) :
    (T.seam (T.keptSeam S j).val).target ⊆ interior (Set.range (T.restrictMap S)) :=
  interior_maximal (T.seam_target_subset_range_restrictMap S j) (T.seam _).open_target

def restrictBasePoint (hext : ∀ i, T.externalPiece i ∉ S) (j : Fin (T.restrictPairing S).count) :
    (T.restrictCarrier S hext).Carrier :=
  ⟨_, T.seam_target_subset_range_restrictMap S j (T.seamTorus_mem_seamCollar _ 1)⟩

def restrictSeam (hext : ∀ i, T.externalPiece i ∉ S) (j : Fin (T.restrictPairing S).count) :
    PartialDiffeomorph signedCollarModel (T.restrictCarrier S hext).model (Torus × ℝ)
      (T.restrictCarrier S hext).Carrier ∞ :=
  letI := (T.restrictAtlas S hext).toChartedSpace
  (T.seam (T.keptSeam S j).val).trans
    ((T.restrictAtlas S hext).interiorPartialDiffeomorph (T.restrictBasePoint S hext j)).symm

theorem restrictSeam_val (hext : ∀ i, T.externalPiece i ∉ S) (j : Fin (T.restrictPairing S).count)
    {p : Torus × ℝ} (hp : p ∈ signedCollarSource) :
    (T.restrictSeam S hext j p).val = T.seam (T.keptSeam S j).val p :=
  ((T.restrictAtlas S hext).interiorPartialDiffeomorph (T.restrictBasePoint S hext j)).right_inv
    (T.seam_target_subset_interior_range S j ((T.seam _).map_source' (T.mem_seam_source _ hp)))

theorem restrictSeam_source (hext : ∀ i, T.externalPiece i ∉ S)
    (j : Fin (T.restrictPairing S).count) :
    (T.restrictSeam S hext j).source = signedCollarSource := by
  ext p
  constructor
  · intro hp
    exact T.seam_source _ ▸ hp.1
  · intro hp
    exact ⟨T.mem_seam_source _ hp,
      T.seam_target_subset_interior_range S j ((T.seam _).map_source' (T.mem_seam_source _ hp))⟩

theorem restrictSeam_target_subset (hext : ∀ i, T.externalPiece i ∉ S)
    (j : Fin (T.restrictPairing S).count) :
    (T.restrictSeam S hext j).target ⊆ Subtype.val ⁻¹' (T.seam (T.keptSeam S j).val).target :=
  fun _ hy => hy.2

def restrictInteriorImage (hext : ∀ i, T.externalPiece i ∉ S) :
    TopologicalSpace.Opens (T.restrictCarrier S hext).Carrier :=
  ⟨{y | y.val ∈ T.interiorImage},
    T.interiorImage.isOpen.preimage (T.contMDiff_restrictCarrier_val S hext).continuous⟩

private theorem subInterior_val (x : (T.subCarrier S).interior) :
    x.val.val ∈ T.cutCarrier.interior :=
  (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val (I := T.cutCarrier.model)
    (u := T.subPiece S) (x := x.val)).mp x.property

private theorem cutMap_mem_interiorImage (x : (T.subCarrier S).interior) :
    T.cutMap x.val.val ∈ T.interiorImage := by
  have h := (T.interiorDiffeomorph ⟨x.val.val, T.subInterior_val S x⟩).property
  rw [T.interior_map] at h
  exact h

private theorem eq_of_cutMap_eq_of_isInteriorPoint {y x : T.cutCarrier.Carrier}
    (hy : T.cutCarrier.model.IsInteriorPoint y) (h : T.cutMap y = T.cutMap x) : y = x := by
  refine T.pairing.gluing.eq_of_rel_of_notMem (fun i hi => ?_)
    (Quotient.exact (T.reconstruction.injective h))
  have hb : y ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier := by
    rw [T.cut_boundary_exhausted]
    exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
  exact (T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint y).mp hy hb

private theorem interiorInv_mem (hext : ∀ i, T.externalPiece i ∉ S)
    (z : T.restrictInteriorImage S hext) :
    (T.interiorDiffeomorph.symm ⟨z.val.val, z.property⟩).val ∈ T.subPiece S := by
  obtain ⟨q, hq⟩ := z.val.property
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hxz : T.cutMap x.val = z.val.val := hq
  have h1 := T.interior_map (T.interiorDiffeomorph.symm ⟨z.val.val, z.property⟩)
  rw [Diffeomorph.apply_symm_apply] at h1
  have heq := T.eq_of_cutMap_eq_of_isInteriorPoint
    (T.interiorDiffeomorph.symm ⟨z.val.val, z.property⟩).property (h1.symm.trans hxz.symm)
  rw [heq]
  exact x.property

def restrictInteriorDiffeomorph (hext : ∀ i, T.externalPiece i ∉ S) :
    (T.subCarrier S).interior ≃ₘ⟮(T.subCarrier S).model, (T.restrictCarrier S hext).model⟯
      T.restrictInteriorImage S hext where
  toFun x := ⟨⟨T.cutMap x.val.val, (T.restrictPairing S).quotientMap x.val, rfl⟩,
    T.cutMap_mem_interiorImage S x⟩
  invFun z := ⟨⟨(T.interiorDiffeomorph.symm ⟨z.val.val, z.property⟩).val,
    T.interiorInv_mem S hext z⟩,
    (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val (I := T.cutCarrier.model)
      (u := T.subPiece S) (x := ⟨_, T.interiorInv_mem S hext z⟩)).mpr
      (T.interiorDiffeomorph.symm ⟨z.val.val, z.property⟩).property⟩
  left_inv x := by
    have e : T.interiorDiffeomorph ⟨x.val.val, T.subInterior_val S x⟩ =
        ⟨T.cutMap x.val.val, T.cutMap_mem_interiorImage S x⟩ :=
      Subtype.ext (T.interior_map _)
    have h : (T.interiorDiffeomorph.symm ⟨T.cutMap x.val.val,
        T.cutMap_mem_interiorImage S x⟩).val = x.val.val := by
      rw [← e, Diffeomorph.symm_apply_apply]
    apply Subtype.ext
    apply Subtype.ext
    exact h
  right_inv z := by
    have h1 := T.interior_map (T.interiorDiffeomorph.symm ⟨z.val.val, z.property⟩)
    rw [Diffeomorph.apply_symm_apply] at h1
    apply Subtype.ext
    apply Subtype.ext
    exact h1.symm
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    refine (T.contMDiff_restrictCarrier_iff S hext _).mpr ?_
    have h1 : ContMDiff (T.subCarrier S).model T.cutCarrier.model ∞
        (fun x : (T.subCarrier S).interior => x.val.val) :=
      (contMDiff_subtype_val (I := T.cutCarrier.model) (U := T.subPiece S)).comp
        (contMDiff_subtype_val (I := (T.subCarrier S).model) (U := (T.subCarrier S).interior))
    exact T.quotient_smooth.comp h1
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    have hg : ContMDiff (T.restrictCarrier S hext).model W.model ∞
        (fun z : T.restrictInteriorImage S hext => z.val.val) :=
      (T.contMDiff_restrictCarrier_val S hext).comp contMDiff_subtype_val
    have hg' : ContMDiff (T.restrictCarrier S hext).model W.model ∞
        (fun z : T.restrictInteriorImage S hext =>
          (⟨z.val.val, z.property⟩ : T.interiorImage)) :=
      (ContMDiff.subtypeVal_comp_iff _ _).mp hg
    have hc : ContMDiff (T.restrictCarrier S hext).model T.cutCarrier.model ∞
        (fun z : T.restrictInteriorImage S hext =>
          (T.interiorDiffeomorph.symm ⟨z.val.val, z.property⟩).val) :=
      contMDiff_subtype_val.comp (T.interiorDiffeomorph.symm.contMDiff.comp hg')
    have hd : ContMDiff (T.restrictCarrier S hext).model T.cutCarrier.model ∞
        (fun z : T.restrictInteriorImage S hext =>
          (⟨(T.interiorDiffeomorph.symm ⟨z.val.val, z.property⟩).val,
            T.interiorInv_mem S hext z⟩ : T.subPiece S)) :=
      (ContMDiff.subtypeVal_comp_iff (T.subPiece S) _).mp hc
    exact hd

def restrictQuotientMap (hext : ∀ i, T.externalPiece i ∉ S) (x : (T.subCarrier S).Carrier) :
    (T.restrictCarrier S hext).Carrier :=
  ⟨T.cutMap x.val, (T.restrictPairing S).quotientMap x, rfl⟩

theorem contMDiff_restrictQuotientMap (hext : ∀ i, T.externalPiece i ∉ S) :
    ContMDiff (T.subCarrier S).model (T.restrictCarrier S hext).model ∞
      (T.restrictQuotientMap S hext) := by
  refine (T.contMDiff_restrictCarrier_iff S hext _).mpr ?_
  exact T.quotient_smooth.comp (contMDiff_subtype_val (I := T.cutCarrier.model) (U := T.subPiece S))

theorem restrictQuotientMap_oriented (hext : ∀ i, T.externalPiece i ∉ S)
    (x : (T.subCarrier S).Carrier) :
    ∃ L : TangentSpace (T.subCarrier S).model x ≃ₗ[ℝ]
        TangentSpace (T.restrictCarrier S hext).model (T.restrictQuotientMap S hext x),
      (∀ v, L v = mfderiv (T.subCarrier S).model (T.restrictCarrier S hext).model
        (T.restrictQuotientMap S hext) x v) ∧
      Orientation.map (Fin 3) L ((T.subCarrier S).orientation.orientation x) =
        (T.restrictCarrier S hext).orientation.orientation (T.restrictQuotientMap S hext x) := by
  obtain ⟨L₀, hL₀, ho₀⟩ := T.quotient_oriented x.val
  let C := T.restrictAtlas S hext
  let y := T.restrictQuotientMap S hext x
  let i := C.inclusionDifferentialEquiv y
  have hoi := C.orientation_map_inclusion W.orientation y
  have hval : MDifferentiableAt (T.restrictCarrier S hext).model W.model
      (fun z : (T.restrictCarrier S hext).Carrier => z.val) y :=
    (T.contMDiff_restrictCarrier_val S hext).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (T.subCarrier S).model (T.restrictCarrier S hext).model
      (T.restrictQuotientMap S hext) x :=
    (T.contMDiff_restrictQuotientMap S hext).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x hval hg
  have hres := DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open
    T.cutCarrier.model W.model (T.subPiece S) (T.reconstruction ∘ T.pairing.quotientMap)
    T.quotient_smooth x
  have key : ∀ v, i (mfderiv (T.subCarrier S).model (T.restrictCarrier S hext).model
      (T.restrictQuotientMap S hext) x v) = L₀ v := by
    intro v
    have e1 : i (mfderiv (T.subCarrier S).model (T.restrictCarrier S hext).model
        (T.restrictQuotientMap S hext) x v) =
        ((mfderiv (T.restrictCarrier S hext).model W.model
          (fun z : (T.restrictCarrier S hext).Carrier => z.val) y).comp
          (mfderiv (T.subCarrier S).model (T.restrictCarrier S hext).model
            (T.restrictQuotientMap S hext) x)) v := rfl
    have e2 : mfderiv (T.subCarrier S).model W.model
        ((fun z : (T.restrictCarrier S hext).Carrier => z.val) ∘ T.restrictQuotientMap S hext) x =
        mfderiv T.cutCarrier.model W.model ((T.reconstruction ∘ T.pairing.quotientMap) ∘
          (Subtype.val : T.subPiece S → T.cutCarrier.Carrier)) x := rfl
    rw [e1, ← hcomp, e2, hres]
    exact (hL₀ v).symm
  refine ⟨L₀.trans i.symm.toLinearEquiv, fun v => ?_, ?_⟩
  · change i.symm (L₀ v) = _
    rw [← key v]
    exact i.symm_apply_apply _
  · have hmap : ∀ o, Orientation.map (Fin 3) (L₀.trans i.symm.toLinearEquiv) o =
        Orientation.map (Fin 3) i.symm.toLinearEquiv (Orientation.map (Fin 3) L₀ o) := by
      intro o
      induction o using Module.Ray.ind with
      | h v hv => rfl
    have hsymm : Orientation.map (Fin 3) i.symm.toLinearEquiv =
        (Orientation.map (Fin 3) i.toLinearEquiv).symm :=
      (Orientation.map_symm (ι := Fin 3) _).symm
    refine (hmap _).trans ?_
    change Orientation.map (Fin 3) i.symm.toLinearEquiv
      (Orientation.map (Fin 3) L₀ (T.cutCarrier.orientation.orientation x.val)) = _
    rw [ho₀]
    have h1 := congrArg (Orientation.map (Fin 3) i.symm.toLinearEquiv) hoi
    rw [hsymm] at h1
    rw [hsymm]
    exact h1.symm.trans (Equiv.symm_apply_apply (Orientation.map (Fin 3) i.toLinearEquiv) _)

theorem not_mem_crossingSurface_of_kept (j : Fin (T.restrictPairing S).count) {y : W.Carrier}
    (hy : y ∈ (T.seam (T.keptSeam S j).val).target) : y ∉ T.crossingSurface S := by
  intro h
  obtain ⟨k, hk, hs⟩ := Set.mem_iUnion₂.mp h
  have hkept := (T.keptSeam S j).property
  by_cases e : k = (T.keptSeam S j).val
  · subst e
    rcases hk with ⟨-, hr⟩ | ⟨-, hl⟩
    · exact hr hkept.2
    · exact hl hkept.1
  · exact (T.seam_disjoint e).le_bot ⟨T.seamSurface_subset_seamCollar k hs, hy⟩

theorem sideIndex_ne_of_kept (a : T.RestrictSide S) (k : T.KeptSeam S) :
    T.sideIndex a.val ≠ .inl k.val := by
  obtain ⟨s, hs, hks⟩ := a
  rcases s with k' | k' | k' <;> intro h <;>
    simp only [sideIndex, Sum.inl.injEq, reduceCtorEq] at h
  · subst h
    exact hks k.property
  · subst h
    exact hks k.property

theorem restrictExternal_exhausted (hext : ∀ i, T.externalPiece i ∉ S) :
    (T.restrictCarrier S hext).model.boundary (T.restrictCarrier S hext).Carrier =
      (T.restrictExternal S hext).image := by
  ext y
  constructor
  · intro hy
    have hc := (T.restrictCarrier_isBoundaryPoint_iff S hext y).mp hy
    obtain ⟨k, hk, t, ht⟩ := Set.mem_iUnion₂.mp hc
    rcases hk with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · let a : T.RestrictSide S := ⟨.inl k, hl, fun h => hr h.2⟩
      refine Set.mem_iUnion.mpr ⟨Fintype.equivFin _ a, t, Subtype.ext ?_⟩
      change (T.crossCollar S hext (T.restrictSide S (Fintype.equivFin _ a))
        (t, halfZero)).val = y.val
      rw [restrictSide_equivFin, T.crossCollar_val S hext a (zero_mem_halfCollarSource t), ← ht]
      change T.cutMap (T.pairing.leftCollar k (t, halfZero)) = T.seamTorus k t
      rw [T.pairing.left_zero, seamTorus_eq_cutMap]
    · let a : T.RestrictSide S := ⟨.inr (.inl k), hr, fun h => hl h.1⟩
      refine Set.mem_iUnion.mpr ⟨Fintype.equivFin _ a, T.pairing.matching k t, Subtype.ext ?_⟩
      change (T.crossCollar S hext (T.restrictSide S (Fintype.equivFin _ a))
        (T.pairing.matching k t, halfZero)).val = y.val
      rw [restrictSide_equivFin, T.crossCollar_val S hext a (zero_mem_halfCollarSource _), ← ht]
      change T.cutMap (T.pairing.rightCollar k (T.pairing.matching k t, halfZero)) =
        T.seamTorus k t
      rw [T.pairing.right_zero, seamTorus_eq_cutMap_right]
  · intro hy
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hy
    exact (T.restrictExternal S hext).boundary_zero j t

def restrict (hS : S.Nonempty) (hext : ∀ i, T.externalPiece i ∉ S) :
    TorusPresentation (T.restrictCarrier S hext) where
  cutCarrier := T.subCarrier S
  components := T.subComponents S hS
  pairing := T.restrictPairing S
  externalCount := Fintype.card (T.RestrictSide S)
  external := T.restrictExternal S hext
  cutExternal := T.restrictBoundaryTori S
  external_exhausted := T.restrictExternal_exhausted S hext
  cut_boundary_exhausted := T.subCarrier_boundary S
  external_disjoint := T.restrict_external_disjoint S
  reconstruction := T.restrictHomeomorph S
  quotient_smooth := T.contMDiff_restrictQuotientMap S hext
  quotient_oriented := T.restrictQuotientMap_oriented S hext
  interiorImage := T.restrictInteriorImage S hext
  interiorDiffeomorph := T.restrictInteriorDiffeomorph S hext
  interior_map _ := rfl
  seam := T.restrictSeam S hext
  seam_source := T.restrictSeam_source S hext
  seam_zero j t := Subtype.ext ((T.restrictSeam_val S hext j ⟨by norm_num, by norm_num⟩).trans
    (T.restrictMap_leftParam S j t).symm)
  seam_positive j t s hs h := Subtype.ext ((T.restrictSeam_val S hext j ⟨by linarith, h⟩).trans
    ((T.seam_positive _ t s hs h).trans (congrArg T.cutMap
      (T.restrictPairing_rightCollar_apply S j
        (show (T.pairing.matching _ t, halfPoint s hs) ∈ halfCollarSource from h))).symm))
  seam_negative j t s hs h := Subtype.ext ((T.restrictSeam_val S hext j ⟨h, by linarith⟩).trans
    ((T.seam_negative _ t s hs h).trans (congrArg T.cutMap
      (T.restrictPairing_leftCollar_apply S j
        (show (t, halfPoint (-s) (neg_nonneg.mpr hs)) ∈ halfCollarSource from
          show -s < 1 by linarith))).symm))
  seam_interior j y hy := by
    change (T.restrictCarrier S hext).model.IsInteriorPoint y
    refine (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint y).mpr fun hb => ?_
    exact T.not_mem_crossingSurface_of_kept S j (T.restrictSeam_target_subset S hext j hy)
      ((T.restrictCarrier_isBoundaryPoint_iff S hext y).mp hb)
  seam_disjoint i j h := ((T.seam_disjoint fun e => h ((Fintype.equivFin _).symm.injective
    (Subtype.ext e))).preimage Subtype.val).mono (T.restrictSeam_target_subset S hext i)
      (T.restrictSeam_target_subset S hext j)
  marked_collar i p _ := (T.crossCollar_apply S hext _ p).symm
  external_seam_disjoint i j := by
    change Disjoint (T.crossCollar S hext (T.restrictSide S i)).target
      (T.restrictSeam S hext j).target
    rw [T.crossCollar_target]
    exact ((T.pairwise_disjoint_sideRegion
      (T.sideIndex_ne_of_kept S (T.restrictSide S i) (T.keptSeam S j))).preimage
        Subtype.val).mono_right (T.restrictSeam_target_subset S hext j)
  leftPiece := T.restrictLeftPiece S
  rightPiece := T.restrictRightPiece S
  left_owned := T.restrict_left_owned S hS
  right_owned := T.restrict_right_owned S hS
  externalPiece := T.restrictExternalPiece S
  external_owned := T.restrict_external_owned S hS

section Restrict
variable (hS : S.Nonempty) (hext : ∀ i, T.externalPiece i ∉ S)

@[simp]
theorem restrict_components_count : (T.restrict S hS hext).components.count = S.card := rfl

theorem restrict_pairing_count :
    (T.restrict S hS hext).pairing.count =
      (Finset.univ.filter fun k => T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S).card :=
  T.restrictPairing_count_eq_card_filter S

include hext in
theorem restrict_externalCount :
    (T.restrict S hS hext).externalCount =
      (Finset.univ.filter fun k => (T.leftPiece k ∈ S ∧ T.rightPiece k ∉ S) ∨
        (T.rightPiece k ∈ S ∧ T.leftPiece k ∉ S)).card := by
  change Fintype.card (T.RestrictSide S) = _
  rw [T.card_restrictSide S, Finset.filter_false_of_mem fun k _ => hext k, Finset.card_empty,
    zero_add]

theorem restrict_reconstruction_val (q : (T.restrictPairing S).QuotientSpace) :
    ((T.restrict S hS hext).reconstruction q).val = T.restrictMap S q := rfl

theorem restrict_reconstruction_range :
    Set.range (fun q => ((T.restrict S hS hext).reconstruction q).val) =
      T.cutMap '' (T.subPiece S : Set T.cutCarrier.Carrier) :=
  T.range_restrictMap S

theorem restrict_seam_val (j : Fin (T.restrictPairing S).count) {p : Torus × ℝ}
    (hp : p ∈ signedCollarSource) :
    ((T.restrict S hS hext).seam j p).val = T.seam (T.keptSeam S j).val p :=
  T.restrictSeam_val S hext j hp

theorem restrict_external_collar_val (j : Fin (Fintype.card (T.RestrictSide S)))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((T.restrict S hS hext).external.collar j p).val =
      T.cutMap (T.sideCollar (T.restrictSide S j).val p) :=
  T.crossCollar_val S hext _ hp

theorem restrict_boundary_iff (y : (T.restrictCarrier S hext).Carrier) :
    (T.restrictCarrier S hext).model.IsBoundaryPoint y ↔ y.val ∈ T.crossingSurface S :=
  T.restrictCarrier_isBoundaryPoint_iff S hext y

end Restrict

theorem externalPiece_not_mem_of_closed {P : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier P)) (S : Finset (Fin T.components.count)) :
    ∀ i, T.externalPiece i ∉ S :=
  fun i => (Fin.cast T.externalCount_eq_zero i).elim0

end TorusPresentation

end GC.Seifert
