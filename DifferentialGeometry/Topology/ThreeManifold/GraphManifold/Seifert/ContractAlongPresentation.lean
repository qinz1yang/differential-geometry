import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ContractAlongAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import DifferentialGeometry.Topology.Manifold.ConnectedInterior
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpace.Instances
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps

/-!
# Smooth selected contraction

The carrier is the quotient gluing only K. Ambient collar coordinates give its half-space
atlas, smooth fold with bijective differential, retained boundary, and descended half collars.
Hausdorffness comes from the closed selected relation; compactness and the actual local charts
provide second countability. The boundary is exactly the quotient image of the original
boundary minus the selected blocks. Charts keep the source intersections inside the quotient.

Finite pieces consist of this quotient and the original components outside S. Their collars,
side bijection, ambient cover, and exact selected-versus-retained overlaps feed EmbeddedCutSystem.
The resulting contractAlong keeps every omitted seam, including the two ports of a new self-seam.
Its connectedness input concerns the quotient's own intrinsic interior. The five count and
reconstruction APIs compare the actual reconstructed presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))

def restrictAlongSeamPatch
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    {k : Fin T.pairing.count} (hk : k ∈ K) :
    OpenPartialHomeomorph (T.restrictAlongPairing S K hK).QuotientSpace W.Carrier := by
  let f := T.restrictAlongMap S K hK
  let V : TopologicalSpace.Opens W.Carrier := ⟨(T.seam k).target, (T.seam k).open_target⟩
  let U : TopologicalSpace.Opens (T.restrictAlongPairing S K hK).QuotientSpace :=
    ⟨f ⁻¹' V, V.isOpen.preimage (T.continuous_restrictAlongMap S K hK)⟩
  let e : U ≃ₜ V := T.restrictAlongSeamHomeomorph S K hK hk
  have hv : Nonempty V := ⟨⟨T.seamTorus k 1, T.seamTorus_mem_seamCollar k 1⟩⟩
  have hu : Nonempty U := hv.map e.symm
  exact (U.openPartialHomeomorphSubtypeCoe hu).symm.trans
    (e.toOpenPartialHomeomorph.trans (V.openPartialHomeomorphSubtypeCoe hv))

theorem restrictAlongSeamPatch_source
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    {k : Fin T.pairing.count} (hk : k ∈ K) :
    (T.restrictAlongSeamPatch S K hK hk).source =
      (T.restrictAlongMap S K hK) ⁻¹' (T.seam k).target := by
  simp [restrictAlongSeamPatch]

theorem restrictAlongSeamPatch_target
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    {k : Fin T.pairing.count} (hk : k ∈ K) :
    (T.restrictAlongSeamPatch S K hK hk).target = (T.seam k).target := by
  simp [restrictAlongSeamPatch]

def restrictAlongBoundaryPatch
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (a : T.AlongBoundarySide S K) :
    OpenPartialHomeomorph (T.subCarrier S).Carrier
      (T.restrictAlongPairing S K hK).QuotientSpace := by
  let d := T.subCollar S a.val a.property.1
  let U : TopologicalSpace.Opens (T.subCarrier S).Carrier := ⟨d.target, d.open_target⟩
  have hu : Nonempty U := ⟨⟨d (1, halfZero), d.map_source (by
    rw [T.subCollar_source]
    exact zero_mem_halfCollarSource 1)⟩⟩
  letI := hu
  let q : U → (T.restrictAlongPairing S K hK).QuotientSpace :=
    fun x => (T.restrictAlongPairing S K hK).quotientMap x.val
  exact (U.openPartialHomeomorphSubtypeCoe hu).symm.trans
    ((T.isOpenEmbedding_alongBoundaryCollar S K hK a).toOpenPartialHomeomorph q)

theorem restrictAlongBoundaryPatch_source
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (a : T.AlongBoundarySide S K) :
    (T.restrictAlongBoundaryPatch S K hK a).source =
      (T.subCollar S a.val a.property.1).target := by
  simp [restrictAlongBoundaryPatch]

def restrictAlongHalfCollar
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (a : T.AlongBoundarySide S K) :
    OpenPartialHomeomorph (Torus × EuclideanHalfSpace 1)
      (T.restrictAlongPairing S K hK).QuotientSpace :=
  (T.subCollar S a.val a.property.1).toOpenPartialHomeomorph.trans
    (T.restrictAlongBoundaryPatch S K hK a)

theorem restrictAlongHalfCollar_source
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (a : T.AlongBoundarySide S K) :
    (T.restrictAlongHalfCollar S K hK a).source = halfCollarSource := by
  rw [restrictAlongHalfCollar, OpenPartialHomeomorph.trans_source,
    restrictAlongBoundaryPatch_source]
  ext p
  constructor
  · intro hp
    exact (T.subCollar_source S a.val a.property.1) ▸ hp.1
  · intro hp
    have hs : p ∈ (T.subCollar S a.val a.property.1).source :=
      (T.subCollar_source S a.val a.property.1).symm ▸ hp
    exact ⟨hs, (T.subCollar S a.val a.property.1).map_source hs⟩

theorem restrictAlongHalfCollar_apply
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (a : T.AlongBoundarySide S K) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    T.restrictAlongHalfCollar S K hK a p =
      (T.restrictAlongPairing S K hK).quotientMap (T.subCollar S a.val a.property.1 p) := by
  let d := T.subCollar S a.val a.property.1
  let U : TopologicalSpace.Opens (T.subCarrier S).Carrier := ⟨d.target, d.open_target⟩
  have hu : Nonempty U := ⟨⟨d (1, halfZero), d.map_source (by
    rw [T.subCollar_source]
    exact zero_mem_halfCollarSource 1)⟩⟩
  have hs : p ∈ d.source := (T.subCollar_source S a.val a.property.1).symm ▸ hp
  change (T.restrictAlongPairing S K hK).quotientMap
    (((U.openPartialHomeomorphSubtypeCoe hu).symm (d p)).val) =
      (T.restrictAlongPairing S K hK).quotientMap (d p)
  apply congrArg (T.restrictAlongPairing S K hK).quotientMap
  apply (U.openPartialHomeomorphSubtypeCoe hu).right_inv
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  exact d.map_source hs

def alongBoundaryLeftHomeomorph
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ S) (hk : k ∉ K) :
    (T.restrictAlongHalfCollar S K hK ⟨.inl k, hl, hk⟩).target ≃ₜ
      T.alongSeamHalfRange k false := by
  let e := T.restrictAlongHalfCollar S K hK ⟨.inl k, hl, hk⟩
  have hs := T.restrictAlongHalfCollar_source S K hK ⟨.inl k, hl, hk⟩
  exact ((Homeomorph.setCongr hs.symm).trans e.toHomeomorphSourceTarget).symm.trans
    (T.alongLeftAmbientHomeomorph k)

def alongBoundaryRightHomeomorph
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (k : Fin T.pairing.count) (hr : T.rightPiece k ∈ S) (hk : k ∉ K) :
    (T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hr, hk⟩).target ≃ₜ
      T.alongSeamHalfRange k true := by
  let e := T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hr, hk⟩
  have hs := T.restrictAlongHalfCollar_source S K hK ⟨.inr (.inl k), hr, hk⟩
  exact ((Homeomorph.setCongr hs.symm).trans e.toHomeomorphSourceTarget).symm.trans
    (T.alongRightAmbientHomeomorph k)

theorem alongBoundaryLeftHomeomorph_val
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ S) (hk : k ∉ K)
    (q : (T.restrictAlongHalfCollar S K hK ⟨.inl k, hl, hk⟩).target) :
    (T.alongBoundaryLeftHomeomorph S K hK k hl hk q).val =
      T.restrictAlongMap S K hK q.val := by
  let a : T.AlongBoundarySide S K := ⟨.inl k, hl, hk⟩
  let e := T.restrictAlongHalfCollar S K hK a
  let p := e.symm q.val
  have hp : p ∈ halfCollarSource :=
    (T.restrictAlongHalfCollar_source S K hK a) ▸ e.map_target q.property
  change T.seam k (p.1, -(p.2.val 0)) = T.restrictAlongMap S K hK q.val
  have hh : T.restrictAlongMap S K hK (e p) = T.seam k (p.1, -(p.2.val 0)) := by
    rw [T.restrictAlongHalfCollar_apply S K hK a hp,
      T.restrictAlongMap_quotientMap S K hK, T.subCollar_apply S a.val a.property.1 hp]
    exact T.cutMap_leftCollar k hp
  rw [e.right_inv q.property] at hh
  exact hh.symm

theorem alongBoundaryRightHomeomorph_val
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (k : Fin T.pairing.count) (hr : T.rightPiece k ∈ S) (hk : k ∉ K)
    (q : (T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hr, hk⟩).target) :
    (T.alongBoundaryRightHomeomorph S K hK k hr hk q).val =
      T.restrictAlongMap S K hK q.val := by
  let a : T.AlongBoundarySide S K := ⟨.inr (.inl k), hr, hk⟩
  let e := T.restrictAlongHalfCollar S K hK a
  let p := e.symm q.val
  have hp : p ∈ halfCollarSource :=
    (T.restrictAlongHalfCollar_source S K hK a) ▸ e.map_target q.property
  change T.seam k ((T.pairing.matching k).symm p.1, p.2.val 0) =
    T.restrictAlongMap S K hK q.val
  have hh : T.restrictAlongMap S K hK (e p) =
      T.seam k ((T.pairing.matching k).symm p.1, p.2.val 0) := by
    rw [T.restrictAlongHalfCollar_apply S K hK a hp,
      T.restrictAlongMap_quotientMap S K hK, T.subCollar_apply S a.val a.property.1 hp]
    exact T.cutMap_rightCollar k hp
  rw [e.right_inv q.property] at hh
  exact hh.symm

theorem exists_alongLeftChart
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ S) (hk : k ∉ K)
    (q : (T.restrictAlongHalfCollar S K hK ⟨.inl k, hl, hk⟩).target) :
    ∃ c : OpenPartialHomeomorph (T.restrictAlongPairing S K hK).QuotientSpace
        (EuclideanHalfSpace 3),
      ∃ φ : PartialDiffeomorph W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
        q.val ∈ c.source ∧
          (∀ x ∈ c.source, T.restrictAlongMap S K hK x ∈ φ.source) ∧
          ∀ x ∈ c.source, (c x).val = φ (T.restrictAlongMap S K hK x) := by
  let U : TopologicalSpace.Opens (T.restrictAlongPairing S K hK).QuotientSpace :=
    ⟨(T.restrictAlongHalfCollar S K hK ⟨.inl k, hl, hk⟩).target,
      (T.restrictAlongHalfCollar S K hK ⟨.inl k, hl, hk⟩).open_target⟩
  let L := T.alongSeamHalfRange k false
  let h := T.alongBoundaryLeftHomeomorph S K hK k hl hk
  let C := T.alongSeamHalfAtlas k false
  have hf := T.alongBoundaryLeftHomeomorph_val S K hK k hl hk
  refine ⟨alongLiftedChart U L h C q, C.ambientChart (h q),
    alongLiftedChart_mem U L h C q, ?_, ?_⟩
  · exact alongLiftedChart_source U L h C q (T.restrictAlongMap S K hK) hf
  · exact alongLiftedChart_forward U L h C q (T.restrictAlongMap S K hK) hf

theorem exists_alongRightChart
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (k : Fin T.pairing.count) (hr : T.rightPiece k ∈ S) (hk : k ∉ K)
    (q : (T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hr, hk⟩).target) :
    ∃ c : OpenPartialHomeomorph (T.restrictAlongPairing S K hK).QuotientSpace
        (EuclideanHalfSpace 3),
      ∃ φ : PartialDiffeomorph W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
        q.val ∈ c.source ∧
          (∀ x ∈ c.source, T.restrictAlongMap S K hK x ∈ φ.source) ∧
          ∀ x ∈ c.source, (c x).val = φ (T.restrictAlongMap S K hK x) := by
  let U : TopologicalSpace.Opens (T.restrictAlongPairing S K hK).QuotientSpace :=
    ⟨(T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hr, hk⟩).target,
      (T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hr, hk⟩).open_target⟩
  let L := T.alongSeamHalfRange k true
  let h := T.alongBoundaryRightHomeomorph S K hK k hr hk
  let C := T.alongSeamHalfAtlas k true
  have hf := T.alongBoundaryRightHomeomorph_val S K hK k hr hk
  refine ⟨alongLiftedChart U L h C q, C.ambientChart (h q),
    alongLiftedChart_mem U L h C q, ?_, ?_⟩
  · exact alongLiftedChart_source U L h C q (T.restrictAlongMap S K hK) hf
  · exact alongLiftedChart_forward U L h C q (T.restrictAlongMap S K hK) hf

theorem alongChartPatch_cover
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (q : (T.restrictAlongPairing S K hK).QuotientSpace) :
    T.restrictAlongMap S K hK q ∈ T.alongInteriorRange S K ∨
      ∃ a : T.AlongBoundarySide S K, q ∈ (T.restrictAlongHalfCollar S K hK a).target := by
  classical
  by_cases hi : T.restrictAlongMap S K hK q ∈ T.alongInteriorRange S K
  · exact Or.inl hi
  right
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hR : T.cutMap x.val ∈ Set.range (T.restrictMap S) := by
    rw [← T.range_restrictAlongMap S K hK]
    exact ⟨(T.restrictAlongPairing S K hK).quotientMap x, rfl⟩
  have hO : T.cutMap x.val ∈ T.alongOmittedSurface K := by
    by_contra hn
    apply hi
    exact ⟨⟨hR, fun hc => hn (T.crossingSurface_subset_alongOmittedSurface S K hK hc)⟩, hn⟩
  obtain ⟨k, hk, hs⟩ := Set.mem_iUnion₂.mp hO
  have hnot : k ∉ K := Finset.mem_compl.mp hk
  have hb := T.alongMem_block_of_cutMap_mem_seamSurface hs
  rcases hb with hl | hr
  · have hlS : T.leftPiece k ∈ S :=
      T.mem_of_mem_subPiece S x.property (T.left_owned k hl)
    let a : T.AlongBoundarySide S K := ⟨.inl k, hlS, hnot⟩
    let t := (T.pairing.leftParam k).symm ⟨x.val, hl⟩
    have hc : T.subCollar S a.val a.property.1 (t, halfZero) = x := by
      apply Subtype.ext
      rw [T.subCollar_apply S a.val a.property.1 (zero_mem_halfCollarSource t)]
      change T.pairing.leftCollar k (t, halfZero) = x.val
      rw [T.pairing.left_zero]
      exact congrArg Subtype.val ((T.pairing.leftParam k).apply_symm_apply ⟨x.val, hl⟩)
    have he := T.restrictAlongHalfCollar_apply S K hK a (zero_mem_halfCollarSource t)
    rw [hc] at he
    refine ⟨a, ?_⟩
    change (T.restrictAlongPairing S K hK).quotientMap x ∈
      (T.restrictAlongHalfCollar S K hK a).target
    rw [← he]
    apply (T.restrictAlongHalfCollar S K hK a).map_source
    rw [T.restrictAlongHalfCollar_source S K hK a]
    exact zero_mem_halfCollarSource t
  · have hrS : T.rightPiece k ∈ S :=
      T.mem_of_mem_subPiece S x.property (T.right_owned k hr)
    let a : T.AlongBoundarySide S K := ⟨.inr (.inl k), hrS, hnot⟩
    let t := (T.pairing.rightParam k).symm ⟨x.val, hr⟩
    have hc : T.subCollar S a.val a.property.1 (t, halfZero) = x := by
      apply Subtype.ext
      rw [T.subCollar_apply S a.val a.property.1 (zero_mem_halfCollarSource t)]
      change T.pairing.rightCollar k (t, halfZero) = x.val
      rw [T.pairing.right_zero]
      exact congrArg Subtype.val ((T.pairing.rightParam k).apply_symm_apply ⟨x.val, hr⟩)
    have he := T.restrictAlongHalfCollar_apply S K hK a (zero_mem_halfCollarSource t)
    rw [hc] at he
    refine ⟨a, ?_⟩
    change (T.restrictAlongPairing S K hK).quotientMap x ∈
      (T.restrictAlongHalfCollar S K hK a).target
    rw [← he]
    apply (T.restrictAlongHalfCollar S K hK a).map_source
    rw [T.restrictAlongHalfCollar_source S K hK a]
    exact zero_mem_halfCollarSource t

theorem exists_alongInteriorChart
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S)
    (q : (T.restrictAlongMap S K hK) ⁻¹' T.alongInteriorRange S K) :
    ∃ c : OpenPartialHomeomorph (T.restrictAlongPairing S K hK).QuotientSpace
        (EuclideanHalfSpace 3),
      ∃ φ : PartialDiffeomorph W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
        q.val ∈ c.source ∧
          (∀ x ∈ c.source, T.restrictAlongMap S K hK x ∈ φ.source) ∧
          ∀ x ∈ c.source, (c x).val = φ (T.restrictAlongMap S K hK x) := by
  let U : TopologicalSpace.Opens (T.restrictAlongPairing S K hK).QuotientSpace :=
    ⟨(T.restrictAlongMap S K hK) ⁻¹' T.alongInteriorRange S K,
      (T.isOpen_alongInteriorRange S K).preimage (T.continuous_restrictAlongMap S K hK)⟩
  let L := T.alongInteriorRange S K
  let h := T.restrictAlongInteriorHomeomorph S K hK
  let C := T.alongInteriorAtlas S K hext
  have hf : ∀ z : U, (h z).val = T.restrictAlongMap S K hK z.val := fun z => rfl
  refine ⟨alongLiftedChart U L h C q, C.ambientChart (h q),
    alongLiftedChart_mem U L h C q, ?_, ?_⟩
  · exact alongLiftedChart_source U L h C q (T.restrictAlongMap S K hK) hf
  · exact alongLiftedChart_forward U L h C q (T.restrictAlongMap S K hK) hf

theorem exists_alongChart
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S)
    (q : (T.restrictAlongPairing S K hK).QuotientSpace) :
    ∃ c : OpenPartialHomeomorph (T.restrictAlongPairing S K hK).QuotientSpace
        (EuclideanHalfSpace 3),
      ∃ φ : PartialDiffeomorph W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
        q ∈ c.source ∧
          (∀ x ∈ c.source, T.restrictAlongMap S K hK x ∈ φ.source) ∧
          ∀ x ∈ c.source, (c x).val = φ (T.restrictAlongMap S K hK x) := by
  rcases T.alongChartPatch_cover S K hK q with hi | ⟨a, ha⟩
  · exact T.exists_alongInteriorChart S K hK hext ⟨q, hi⟩
  · rcases a with ⟨s, hs, hn⟩
    rcases s with k | k | i
    · exact T.exists_alongLeftChart S K hK k hs hn ⟨q, ha⟩
    · exact T.exists_alongRightChart S K hK k hs hn ⟨q, ha⟩
    · exact (hext i hs).elim

structure AlongChartData
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) where
  chart : (T.restrictAlongPairing S K hK).QuotientSpace →
    OpenPartialHomeomorph (T.restrictAlongPairing S K hK).QuotientSpace (EuclideanHalfSpace 3)
  ambient : (T.restrictAlongPairing S K hK).QuotientSpace →
    PartialDiffeomorph W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞
  mem : ∀ q, q ∈ (chart q).source
  source : ∀ q x, x ∈ (chart q).source → T.restrictAlongMap S K hK x ∈ (ambient q).source
  forward : ∀ q x, x ∈ (chart q).source →
    (chart q x).val = ambient q (T.restrictAlongMap S K hK x)

def alongChartData
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) : T.AlongChartData S K hK := by
  choose c a hm hs hf using T.exists_alongChart S K hK hext
  exact ⟨c, a, hm, hs, hf⟩

@[reducible]
def restrictAlongChartedSpace
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) :
    ChartedSpace (EuclideanHalfSpace 3) (T.restrictAlongPairing S K hK).QuotientSpace :=
  let d := T.alongChartData S K hK hext
  alongPullbackChartedSpace d.chart (fun q => ⟨q, d.mem q⟩)

theorem restrictAlong_isManifold
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) :
    letI := T.restrictAlongChartedSpace S K hK hext
    IsManifold (modelWithCornersEuclideanHalfSpace 3) ∞
      (T.restrictAlongPairing S K hK).QuotientSpace := by
  let d := T.alongChartData S K hK hext
  exact alongPullback_isManifold W.model d.chart (fun q => ⟨q, d.mem q⟩)
    d.ambient (T.restrictAlongMap S K hK) d.source d.forward
    (alongPullback_target_of_forward W.model d.chart d.ambient
      (T.restrictAlongMap S K hK) d.source d.forward)
    (alongPullback_back_of_forward W.model d.chart d.ambient
      (T.restrictAlongMap S K hK) d.source d.forward)

theorem contMDiff_restrictAlongMap
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) :
    letI := T.restrictAlongChartedSpace S K hK hext
    ContMDiff (modelWithCornersEuclideanHalfSpace 3) W.model ∞ (T.restrictAlongMap S K hK) := by
  let d := T.alongChartData S K hK hext
  exact alongPullback_contMDiff W.model d.chart (fun q => ⟨q, d.mem q⟩)
    d.ambient (T.restrictAlongMap S K hK) d.source d.forward
    (alongPullback_target_of_forward W.model d.chart d.ambient
      (T.restrictAlongMap S K hK) d.source d.forward)
    (alongPullback_back_of_forward W.model d.chart d.ambient
      (T.restrictAlongMap S K hK) d.source d.forward)

theorem mfderiv_restrictAlongMap_bijective
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S)
    (q : (T.restrictAlongPairing S K hK).QuotientSpace) :
    letI := T.restrictAlongChartedSpace S K hK hext
    Function.Bijective
      (mfderiv (modelWithCornersEuclideanHalfSpace 3) W.model (T.restrictAlongMap S K hK) q) := by
  let d := T.alongChartData S K hK hext
  exact alongPullback_mfderiv_bijective W.model d.chart (fun x => ⟨x, d.mem x⟩)
    d.ambient (T.restrictAlongMap S K hK) d.source d.forward
    (alongPullback_target_of_forward W.model d.chart d.ambient
      (T.restrictAlongMap S K hK) d.source d.forward)
    (alongPullback_back_of_forward W.model d.chart d.ambient
      (T.restrictAlongMap S K hK) d.source d.forward) q

theorem contMDiffOn_restrictAlong_of_comp
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S)
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
    [TopologicalSpace N] [ChartedSpace G N]
    (g : N → (T.restrictAlongPairing S K hK).QuotientSpace) (U : Set N)
    (hcont : ContinuousOn g U)
    (hsmooth : ContMDiffOn J W.model ∞ (T.restrictAlongMap S K hK ∘ g) U) :
    letI := T.restrictAlongChartedSpace S K hK hext
    ContMDiffOn J (modelWithCornersEuclideanHalfSpace 3) ∞ g U := by
  let d := T.alongChartData S K hK hext
  exact alongPullback_contMDiffOn_of_comp W.model d.chart (fun q => ⟨q, d.mem q⟩)
    d.ambient (T.restrictAlongMap S K hK) d.source d.forward g U hcont hsmooth

theorem contMDiffOn_restrictAlongHalfCollar
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) (a : T.AlongBoundarySide S K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    ContMDiffOn halfCollarModel (modelWithCornersEuclideanHalfSpace 3) ∞
      (T.restrictAlongHalfCollar S K hK a) halfCollarSource := by
  let := T.restrictAlongChartedSpace S K hK hext
  apply T.contMDiffOn_restrictAlong_of_comp S K hK hext halfCollarModel
    (T.restrictAlongHalfCollar S K hK a) halfCollarSource
  · exact (T.restrictAlongHalfCollar S K hK a).continuousOn.mono
      (le_of_eq (T.restrictAlongHalfCollar_source S K hK a).symm)
  · have hc := T.quotient_smooth.comp_contMDiffOn (T.sideCollar a.val).contMDiffOn
    apply (hc.mono (le_of_eq (T.sideCollar_source a.val).symm)).congr
    intro p hp
    change T.restrictAlongMap S K hK (T.restrictAlongHalfCollar S K hK a p) =
      T.cutMap (T.sideCollar a.val p)
    rw [T.restrictAlongHalfCollar_apply S K hK a hp,
      T.restrictAlongMap_quotientMap S K hK, T.subCollar_apply S a.val a.property.1 hp]

theorem restrictAlongHalfCollar_left_symm
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ S) (hk : k ∉ K)
    {q : (T.restrictAlongPairing S K hK).QuotientSpace}
    (hq : q ∈ (T.restrictAlongHalfCollar S K hK ⟨.inl k, hl, hk⟩).target) :
    (T.restrictAlongHalfCollar S K hK ⟨.inl k, hl, hk⟩).symm q =
      T.leftCrossInv k (T.restrictAlongMap S K hK q) := by
  let e := T.restrictAlongHalfCollar S K hK ⟨.inl k, hl, hk⟩
  have hp : e.symm q ∈ halfCollarSource :=
    (T.restrictAlongHalfCollar_source S K hK ⟨.inl k, hl, hk⟩) ▸ e.map_target hq
  have hi := congrArg Subtype.val ((T.alongLeftAmbientHomeomorph k).left_inv ⟨e.symm q, hp⟩)
  have hf := T.alongBoundaryLeftHomeomorph_val S K hK k hl hk ⟨q, hq⟩
  exact hi.symm.trans (congrArg (T.leftCrossInv k) hf)

theorem restrictAlongHalfCollar_right_symm
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (k : Fin T.pairing.count) (hr : T.rightPiece k ∈ S) (hk : k ∉ K)
    {q : (T.restrictAlongPairing S K hK).QuotientSpace}
    (hq : q ∈ (T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hr, hk⟩).target) :
    (T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hr, hk⟩).symm q =
      T.rightCrossInv k (T.restrictAlongMap S K hK q) := by
  let e := T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hr, hk⟩
  have hp : e.symm q ∈ halfCollarSource :=
    (T.restrictAlongHalfCollar_source S K hK ⟨.inr (.inl k), hr, hk⟩) ▸ e.map_target hq
  have hi := congrArg Subtype.val ((T.alongRightAmbientHomeomorph k).left_inv ⟨e.symm q, hp⟩)
  have hf := T.alongBoundaryRightHomeomorph_val S K hK k hr hk ⟨q, hq⟩
  exact hi.symm.trans (congrArg (T.rightCrossInv k) hf)

theorem contMDiffOn_restrictAlongHalfCollar_symm
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) (a : T.AlongBoundarySide S K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    ContMDiffOn (modelWithCornersEuclideanHalfSpace 3) halfCollarModel ∞
      (T.restrictAlongHalfCollar S K hK a).symm
      (T.restrictAlongHalfCollar S K hK a).target := by
  let := T.restrictAlongChartedSpace S K hK hext
  rcases a with ⟨s, hs, hn⟩
  rcases s with k | k | i
  · let e := T.restrictAlongHalfCollar S K hK ⟨.inl k, hs, hn⟩
    have hmaps : Set.MapsTo (T.restrictAlongMap S K hK) e.target (T.seam k).target := by
      intro q hq
      have hm := (T.alongBoundaryLeftHomeomorph S K hK k hs hn ⟨q, hq⟩).property.1
      rwa [T.alongBoundaryLeftHomeomorph_val S K hK k hs hn] at hm
    have hsymm := (T.seam k).contMDiffOn_invFun.comp
      (T.contMDiff_restrictAlongMap S K hK hext).contMDiffOn hmaps
    have hnn : Set.MapsTo (fun q => -((T.seam k).symm (T.restrictAlongMap S K hK q)).2)
        e.target (Set.Ici 0) := by
      intro q hq
      have hm := (T.alongBoundaryLeftHomeomorph S K hK k hs hn ⟨q, hq⟩).property.2
      rwa [T.alongBoundaryLeftHomeomorph_val S K hK k hs hn] at hm
    have hh := (contMDiff_fst.comp_contMDiffOn hsymm).prodMk
      (Manifold.contMDiffOn_halfSpaceOneLift.comp
        (contMDiff_snd.comp_contMDiffOn hsymm).neg hnn)
    exact hh.congr (fun q hq => T.restrictAlongHalfCollar_left_symm S K hK k hs hn hq)
  · let e := T.restrictAlongHalfCollar S K hK ⟨.inr (.inl k), hs, hn⟩
    have hmaps : Set.MapsTo (T.restrictAlongMap S K hK) e.target (T.seam k).target := by
      intro q hq
      have hm := (T.alongBoundaryRightHomeomorph S K hK k hs hn ⟨q, hq⟩).property.1
      rwa [T.alongBoundaryRightHomeomorph_val S K hK k hs hn] at hm
    have hsymm := (T.seam k).contMDiffOn_invFun.comp
      (T.contMDiff_restrictAlongMap S K hK hext).contMDiffOn hmaps
    have hnn : Set.MapsTo (fun q => ((T.seam k).symm (T.restrictAlongMap S K hK q)).2)
        e.target (Set.Ici 0) := by
      intro q hq
      have hm := (T.alongBoundaryRightHomeomorph S K hK k hs hn ⟨q, hq⟩).property.2
      rwa [T.alongBoundaryRightHomeomorph_val S K hK k hs hn] at hm
    have hh := ((T.pairing.matching k).contMDiff.comp_contMDiffOn
      (contMDiff_fst.comp_contMDiffOn hsymm)).prodMk
      (Manifold.contMDiffOn_halfSpaceOneLift.comp
        (contMDiff_snd.comp_contMDiffOn hsymm) hnn)
    exact hh.congr (fun q hq => T.restrictAlongHalfCollar_right_symm S K hK k hs hn hq)
  · exact (hext i hs).elim

def restrictAlongBoundaryCollar
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) (a : T.AlongBoundarySide S K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    PartialDiffeomorph halfCollarModel (modelWithCornersEuclideanHalfSpace 3)
      (Torus × EuclideanHalfSpace 1) (T.restrictAlongPairing S K hK).QuotientSpace ∞ := by
  let := T.restrictAlongChartedSpace S K hK hext
  let e := T.restrictAlongHalfCollar S K hK a
  refine { e.toPartialEquiv with
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := T.contMDiffOn_restrictAlongHalfCollar_symm S K hK hext a }
  exact (T.contMDiffOn_restrictAlongHalfCollar S K hK hext a).mono
    (le_of_eq (T.restrictAlongHalfCollar_source S K hK a))

private theorem alongHalfCollar_isBoundaryPoint_iff (p : Torus × EuclideanHalfSpace 1) :
    halfCollarModel.IsBoundaryPoint p ↔ p.2.val 0 = 0 := by
  have hi : halfCollarModel.IsInteriorPoint p ↔ 0 < p.2.val 0 := by
    change p ∈ halfCollarModel.interior (Torus × EuclideanHalfSpace 1) ↔ 0 < p.2.val 0
    rw [ModelWithCorners.interior_prod]
    constructor
    · intro hp
      have hh := hp.2
      change (modelWithCornersEuclideanHalfSpace 1).IsInteriorPoint p.2 at hh
      rw [ModelWithCorners.IsInteriorPoint,
        interior_range_modelWithCornersEuclideanHalfSpace] at hh
      exact hh
    · intro hp
      refine ⟨BoundarylessManifold.isInteriorPoint, ?_⟩
      change (modelWithCornersEuclideanHalfSpace 1).IsInteriorPoint p.2
      rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace]
      exact hp
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, hi, not_lt]
  exact ⟨fun hp => le_antisymm hp p.2.property, fun hp => hp.le⟩

theorem restrictAlongHalfCollar_isBoundaryPoint_iff
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) (a : T.AlongBoundarySide S K)
    (q : (T.restrictAlongPairing S K hK).QuotientSpace)
    (hq : q ∈ (T.restrictAlongHalfCollar S K hK a).target) :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    (modelWithCornersEuclideanHalfSpace 3).IsBoundaryPoint q ↔
      ((T.restrictAlongHalfCollar S K hK a).symm q).2.val 0 = 0 := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  let e := T.restrictAlongHalfCollar S K hK a
  have hp : e.symm q ∈ (T.restrictAlongBoundaryCollar S K hK hext a).source := e.map_target hq
  have hloc := (T.restrictAlongBoundaryCollar S K hK hext a).isLocalDiffeomorphAt
    halfCollarModel (modelWithCornersEuclideanHalfSpace 3) ∞ hp
  have hh := hloc.isBoundaryPoint_iff (by simp)
  change halfCollarModel.IsBoundaryPoint (e.symm q) ↔
    (modelWithCornersEuclideanHalfSpace 3).IsBoundaryPoint (e (e.symm q)) at hh
  rw [e.right_inv hq] at hh
  exact hh.symm.trans (alongHalfCollar_isBoundaryPoint_iff (e.symm q))

theorem restrictAlong_secondCountable
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) :
    SecondCountableTopology (T.restrictAlongPairing S K hK).QuotientSpace := by
  let := T.restrictAlongChartedSpace S K hK hext
  exact ChartedSpace.secondCountable_of_sigmaCompact (EuclideanHalfSpace 3)
    (T.restrictAlongPairing S K hK).QuotientSpace

@[reducible]
def restrictAlongCarrier
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) : CompactCarrier.{u} := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  let := T.restrictAlong_secondCountable S K hK hext
  exact
    { kind := .withBoundary
      Carrier := (T.restrictAlongPairing S K hK).QuotientSpace
      charts := T.restrictAlongChartedSpace S K hK hext
      smooth := T.restrictAlong_isManifold S K hK hext
      orientation := Manifold.manifoldOrientationPullback
        (modelWithCornersEuclideanHalfSpace 3) W.model finrank_euclideanSpace_fin
        (T.restrictAlongMap S K hK) (T.contMDiff_restrictAlongMap S K hK hext)
        (T.mfderiv_restrictAlongMap_bijective S K hK hext) W.orientation }

theorem restrictAlongCarrier_carrier
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) :
    (T.restrictAlongCarrier S K hK hext).Carrier =
      (T.restrictAlongPairing S K hK).QuotientSpace := rfl

def restrictAlongInteriorPatch
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (v : T.alongInteriorRange S K) :
    OpenPartialHomeomorph (T.restrictAlongPairing S K hK).QuotientSpace
      (T.alongInteriorRange S K) := by
  letI : Nonempty (T.alongInteriorRange S K) := ⟨v⟩
  exact (T.restrictAlongInteriorHomeomorph S K hK).toOpenPartialHomeomorph.lift_openEmbedding
    ((T.isOpen_alongInteriorRange S K).preimage
      (T.continuous_restrictAlongMap S K hK)).isOpenEmbedding_subtypeVal

theorem restrictAlongInteriorPatch_source
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (v : T.alongInteriorRange S K) :
    (T.restrictAlongInteriorPatch S K hK v).source =
      (T.restrictAlongMap S K hK) ⁻¹' T.alongInteriorRange S K := by
  simp only [restrictAlongInteriorPatch, OpenPartialHomeomorph.lift_openEmbedding_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.image_univ]
  ext q
  simp

theorem restrictAlongInteriorPatch_val
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (v : T.alongInteriorRange S K) {q : (T.restrictAlongPairing S K hK).QuotientSpace}
    (hq : q ∈ (T.restrictAlongInteriorPatch S K hK v).source) :
    (T.restrictAlongInteriorPatch S K hK v q).val = T.restrictAlongMap S K hK q := by
  let : Nonempty (T.alongInteriorRange S K) := ⟨v⟩
  obtain ⟨z, hz, rfl⟩ := hq
  rw [restrictAlongInteriorPatch, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

theorem restrictAlongInteriorPatch_symm_val
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (v : T.alongInteriorRange S K) (y : T.alongInteriorRange S K) :
    T.restrictAlongMap S K hK ((T.restrictAlongInteriorPatch S K hK v).symm y) = y.val := by
  change T.restrictAlongMap S K hK ((T.restrictAlongInteriorHomeomorph S K hK).symm y).val = _
  exact congrArg Subtype.val ((T.restrictAlongInteriorHomeomorph S K hK).apply_symm_apply y)

def restrictAlongInteriorDiffeomorph
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) (v : T.alongInteriorRange S K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := (T.alongInteriorAtlas S K hext).toChartedSpace
    PartialDiffeomorph (modelWithCornersEuclideanHalfSpace 3)
      (modelWithCornersEuclideanHalfSpace 3) (T.restrictAlongPairing S K hK).QuotientSpace
      (T.alongInteriorRange S K) ∞ := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := (T.alongInteriorAtlas S K hext).toChartedSpace
  let e := T.restrictAlongInteriorPatch S K hK v
  refine { e.toPartialEquiv with
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }
  · apply ((T.alongInteriorAtlas S K hext).contMDiffOn_iff_subtype_val e e.source).mpr
    exact (T.contMDiff_restrictAlongMap S K hK hext).contMDiffOn.congr
      (fun q hq => T.restrictAlongInteriorPatch_val S K hK v hq)
  · apply T.contMDiffOn_restrictAlong_of_comp S K hK hext
      (modelWithCornersEuclideanHalfSpace 3) e.symm e.target e.continuousOn_invFun
    exact (T.alongInteriorAtlas S K hext).contMDiff_subtype_val.contMDiffOn.congr
      (fun y hy => T.restrictAlongInteriorPatch_symm_val S K hK v y)

theorem isInteriorPoint_restrictAlong_of_mem
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S)
    (q : (T.restrictAlongPairing S K hK).QuotientSpace)
    (hq : T.restrictAlongMap S K hK q ∈ T.alongInteriorRange S K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    (modelWithCornersEuclideanHalfSpace 3).IsInteriorPoint q := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  let := (T.alongInteriorAtlas S K hext).toChartedSpace
  let := (T.alongInteriorAtlas S K hext).isManifold
  let v : T.alongInteriorRange S K := ⟨T.restrictAlongMap S K hK q, hq⟩
  have hs : q ∈ (T.restrictAlongInteriorDiffeomorph S K hK hext v).source := by
    change q ∈ (T.restrictAlongInteriorPatch S K hK v).source
    rw [T.restrictAlongInteriorPatch_source S K hK v]
    exact hq
  have hloc := (T.restrictAlongInteriorDiffeomorph S K hK hext v).isLocalDiffeomorphAt
    (modelWithCornersEuclideanHalfSpace 3) (modelWithCornersEuclideanHalfSpace 3) ∞ hs
  exact (hloc.isInteriorPoint_iff (by simp)).mpr
    (T.alongInteriorAtlas_isInteriorPoint S K hext
      (T.restrictAlongInteriorDiffeomorph S K hK hext v q))

theorem alongBoundaryImage_mem_iff
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (q : (T.restrictAlongPairing S K hK).QuotientSpace) :
    q ∈ (T.restrictAlongPairing S K hK).quotientMap ''
        (T.restrictAlongBoundaryTori S K).image ↔
      ∃ a : T.AlongBoundarySide S K, ∃ t : Torus,
        q = T.restrictAlongHalfCollar S K hK a (t, halfZero) := by
  constructor
  · rintro ⟨x, hx, hq⟩
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hx
    let a := T.alongBoundarySide S K j
    refine ⟨a, t, ?_⟩
    have he := T.restrictAlongHalfCollar_apply S K hK a (zero_mem_halfCollarSource t)
    exact hq.symm.trans he.symm
  · rintro ⟨a, t, rfl⟩
    let x := T.subCollar S a.val a.property.1 (t, halfZero)
    refine ⟨x, ?_, (T.restrictAlongHalfCollar_apply S K hK a
      (zero_mem_halfCollarSource t)).symm⟩
    refine Set.mem_iUnion.mpr ⟨Fintype.equivFin (T.AlongBoundarySide S K) a, t, ?_⟩
    change T.subCollar S
      (T.alongBoundarySide S K (Fintype.equivFin (T.AlongBoundarySide S K) a)).val
      (T.alongBoundarySide S K (Fintype.equivFin (T.AlongBoundarySide S K) a)).property.1
      (t, halfZero) = x
    rw [T.alongBoundarySide_equivFin S K a]

theorem restrictAlongHalfCollar_zero_boundary
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) (a : T.AlongBoundarySide S K) (t : Torus) :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    (modelWithCornersEuclideanHalfSpace 3).IsBoundaryPoint
      (T.restrictAlongHalfCollar S K hK a (t, halfZero)) := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  have hs : (t, halfZero) ∈ (T.restrictAlongBoundaryCollar S K hK hext a).source := by
    change (t, halfZero) ∈ (T.restrictAlongHalfCollar S K hK a).source
    rw [T.restrictAlongHalfCollar_source S K hK a]
    exact zero_mem_halfCollarSource t
  have hloc := (T.restrictAlongBoundaryCollar S K hK hext a).isLocalDiffeomorphAt
    halfCollarModel (modelWithCornersEuclideanHalfSpace 3) ∞ hs
  exact (hloc.isBoundaryPoint_iff (by simp)).mp
    ((alongHalfCollar_isBoundaryPoint_iff (t, halfZero)).mpr rfl)

theorem restrictAlong_isBoundaryPoint_iff
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S)
    (q : (T.restrictAlongPairing S K hK).QuotientSpace) :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    (modelWithCornersEuclideanHalfSpace 3).IsBoundaryPoint q ↔
      q ∈ (T.restrictAlongPairing S K hK).quotientMap ''
        (T.restrictAlongBoundaryTori S K).image := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  rw [T.alongBoundaryImage_mem_iff S K hK q]
  constructor
  · intro hb
    rcases T.alongChartPatch_cover S K hK q with hi | ⟨a, hq⟩
    · exact ((ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint q).mp
        (T.isInteriorPoint_restrictAlong_of_mem S K hK hext q hi) hb).elim
    · let e := T.restrictAlongHalfCollar S K hK a
      have hz := (T.restrictAlongHalfCollar_isBoundaryPoint_iff S K hK hext a q hq).mp hb
      have hzero : (e.symm q).2 = halfZero := by
        apply Subtype.ext
        ext i
        rw [Subsingleton.elim i 0]
        exact hz
      refine ⟨a, (e.symm q).1, ?_⟩
      exact (e.right_inv hq).symm.trans (congrArg e (Prod.ext rfl hzero))
  · rintro ⟨a, t, rfl⟩
    exact T.restrictAlongHalfCollar_zero_boundary S K hK hext a t

theorem restrictAlongHalfCollar_disjoint
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    Pairwise fun a b : T.AlongBoundarySide S K =>
      Disjoint (T.restrictAlongHalfCollar S K hK a).target
        (T.restrictAlongHalfCollar S K hK b).target := by
  intro a b hab
  rw [Set.disjoint_left]
  intro q ha hb
  let ea := T.restrictAlongHalfCollar S K hK a
  let eb := T.restrictAlongHalfCollar S K hK b
  have hpa : ea.symm q ∈ halfCollarSource :=
    (T.restrictAlongHalfCollar_source S K hK a) ▸ ea.map_target ha
  have hpb : eb.symm q ∈ halfCollarSource :=
    (T.restrictAlongHalfCollar_source S K hK b) ▸ eb.map_target hb
  let x := T.subCollar S a.val a.property.1 (ea.symm q)
  let y := T.subCollar S b.val b.property.1 (eb.symm q)
  have hxa : x ∈ (T.subCollar S a.val a.property.1).target :=
    (T.subCollar S a.val a.property.1).map_source
      ((T.subCollar_source S a.val a.property.1).symm ▸ hpa)
  have hyb : y ∈ (T.subCollar S b.val b.property.1).target :=
    (T.subCollar S b.val b.property.1).map_source
      ((T.subCollar_source S b.val b.property.1).symm ▸ hpb)
  have he : (T.restrictAlongPairing S K hK).quotientMap x =
      (T.restrictAlongPairing S K hK).quotientMap y := by
    rw [← T.restrictAlongHalfCollar_apply S K hK a hpa,
      ← T.restrictAlongHalfCollar_apply S K hK b hpb]
    exact (ea.right_inv ha).trans (eb.right_inv hb).symm
  have ha' : x.val ∈ (T.sideCollar a.val).target := by
    change x ∈ Subtype.val ⁻¹' (T.sideCollar a.val).target
    rw [← T.subCollar_target S a.val a.property.1]
    exact hxa
  have hxy : x = y := (T.restrictAlongGluing S K hK).eq_of_rel_of_notMem
    (fun j hj => T.alongBoundaryCollar_avoids_selected S K hK a ha' j hj)
      (Quotient.exact he)
  have hb' : x.val ∈ (T.sideCollar b.val).target := by
    change x ∈ Subtype.val ⁻¹' (T.sideCollar b.val).target
    rw [← T.subCollar_target S b.val b.property.1, hxy]
    exact hyb
  exact (T.sideCollar_disjoint (fun heq => hab (Subtype.ext heq))).le_bot ⟨ha', hb'⟩

def restrictAlongBoundaryToriDescended
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) :
    BoundaryTori (T.restrictAlongCarrier S K hK hext)
      (Fintype.card (T.AlongBoundarySide S K)) where
  collar j := T.restrictAlongBoundaryCollar S K hK hext (T.alongBoundarySide S K j)
  source_eq j := T.restrictAlongHalfCollar_source S K hK (T.alongBoundarySide S K j)
  boundary_zero j t := T.restrictAlongHalfCollar_zero_boundary S K hK hext
    (T.alongBoundarySide S K j) t
  disjoint i j hij := T.restrictAlongHalfCollar_disjoint S K hK
    (show T.alongBoundarySide S K i ≠ T.alongBoundarySide S K j from
      fun heq => hij ((Fintype.equivFin (T.AlongBoundarySide S K)).symm.injective heq))

theorem restrictAlongBoundaryToriDescended_image
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) :
    (T.restrictAlongBoundaryToriDescended S K hK hext).image =
      (T.restrictAlongPairing S K hK).quotientMap ''
        (T.restrictAlongBoundaryTori S K).image := by
  ext q
  rw [T.alongBoundaryImage_mem_iff S K hK q]
  constructor
  · intro hq
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hq
    exact ⟨T.alongBoundarySide S K j, t, rfl⟩
  · rintro ⟨a, t, rfl⟩
    refine Set.mem_iUnion.mpr
      ⟨Fintype.equivFin (T.AlongBoundarySide S K) a, t, ?_⟩
    change T.restrictAlongHalfCollar S K hK
      (T.alongBoundarySide S K (Fintype.equivFin (T.AlongBoundarySide S K) a))
      (t, halfZero) = _
    rw [T.alongBoundarySide_equivFin S K a]

theorem restrictAlongCarrier_interior_eq
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) :
    ((T.restrictAlongCarrier S K hK hext).interior : Set _) =
      (Set.univ : Set (T.restrictAlongPairing S K hK).QuotientSpace) \
        ((T.restrictAlongPairing S K hK).quotientMap ''
          (T.restrictAlongBoundaryTori S K).image) := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  ext q
  change (modelWithCornersEuclideanHalfSpace 3).IsInteriorPoint q ↔ _
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
    T.restrictAlong_isBoundaryPoint_iff S K hK hext q]
  simp

theorem connectedSpace_restrictAlong
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S)
    (hconn : IsConnected ((Set.univ :
      Set (T.restrictAlongPairing S K hK).QuotientSpace) \
        ((T.restrictAlongPairing S K hK).quotientMap ''
          (T.restrictAlongBoundaryTori S K).image))) :
    ConnectedSpace (T.restrictAlongPairing S K hK).QuotientSpace := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  have hc : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
      Set (T.restrictAlongPairing S K hK).QuotientSpace) := by
    rwa [T.restrictAlongCarrier_interior_eq S K hK hext]
  have hd : Dense ((T.restrictAlongCarrier S K hK hext).interior :
      Set (T.restrictAlongPairing S K hK).QuotientSpace) :=
    DifferentialGeometry.Topology.Manifold.dense_manifold_interior
  exact connectedSpace_iff_univ.mpr (hd.closure_eq ▸ hc.closure)

theorem restrictAlongBoundaryTori_image_eq_boundary_sdiff
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    (T.restrictAlongBoundaryTori S K).image =
      (T.subCarrier S).model.boundary (T.subCarrier S).Carrier \
        ⋃ j, (T.restrictAlongGluing S K hK).block j := by
  rw [T.subCarrier_boundary_along S K hK]
  ext x
  constructor
  · intro hx
    refine ⟨Or.inr hx, ?_⟩
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hx
    intro hs
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hs
    apply T.alongBoundaryCollar_avoids_selected S K hK (T.alongBoundarySide S K i)
      (x := (T.restrictAlongBoundaryTori S K).torusMap i t) ?_ j hj
    change ((T.restrictAlongBoundaryTori S K).collar i (t, halfZero)).val ∈ _
    rw [T.restrictAlongBoundaryTori_collar_apply S K i (zero_mem_halfCollarSource t)]
    apply (T.sideCollar (T.alongBoundarySide S K i).val).map_source
    rw [T.sideCollar_source]
    exact zero_mem_halfCollarSource t
  · rintro ⟨hx | hx, hn⟩
    · exact (hn hx).elim
    · exact hx

theorem restrictAlong_boundary_formula
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    (modelWithCornersEuclideanHalfSpace 3).boundary
        (T.restrictAlongPairing S K hK).QuotientSpace =
      (T.restrictAlongPairing S K hK).quotientMap ''
        ((T.subCarrier S).model.boundary (T.subCarrier S).Carrier \
          ⋃ j, (T.restrictAlongGluing S K hK).block j) := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  rw [← T.restrictAlongBoundaryTori_image_eq_boundary_sdiff S K hK]
  ext q
  change (modelWithCornersEuclideanHalfSpace 3).IsBoundaryPoint q ↔ _
  exact T.restrictAlong_isBoundaryPoint_iff S K hK hext q

structure AlongPieceGeometry (W : CompactCarrier.{u}) where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace (EuclideanHalfSpace 3) Carrier]
  [manifold : IsManifold (modelWithCornersEuclideanHalfSpace 3) ∞ Carrier]
  [compact : CompactSpace Carrier]
  [hausdorff : T2Space Carrier]
  [secondCountable : SecondCountableTopology Carrier]
  [connected : ConnectedSpace Carrier]
  map : Carrier → W.Carrier
  smooth : ContMDiff (modelWithCornersEuclideanHalfSpace 3) W.model ∞ map
  mfderiv_bijective : ∀ q,
    Function.Bijective (mfderiv (modelWithCornersEuclideanHalfSpace 3) W.model map q)
  torusCount : ℕ
  collar : Fin torusCount → PartialDiffeomorph halfCollarModel
    (modelWithCornersEuclideanHalfSpace 3) (Torus × EuclideanHalfSpace 1) Carrier ∞
  collar_source : ∀ j, (collar j).source = halfCollarSource
  collar_disjoint : Pairwise fun i j => Disjoint (collar i).target (collar j).target
  boundary_exhausted : (modelWithCornersEuclideanHalfSpace 3).boundary Carrier =
    ⋃ j, Set.range fun t => collar j (t, halfZero)

attribute [instance] AlongPieceGeometry.topology AlongPieceGeometry.charts
  AlongPieceGeometry.manifold AlongPieceGeometry.compact AlongPieceGeometry.hausdorff
  AlongPieceGeometry.secondCountable AlongPieceGeometry.connected

def alongRegionGeometry
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S)
    (hconn : IsConnected ((Set.univ :
      Set (T.restrictAlongPairing S K hK).QuotientSpace) \
        ((T.restrictAlongPairing S K hK).quotientMap ''
          (T.restrictAlongBoundaryTori S K).image))) : AlongPieceGeometry W := by
  let C := T.restrictAlongCarrier S K hK hext
  let : ChartedSpace (EuclideanHalfSpace 3) C.Carrier := C.charts
  let : IsManifold (modelWithCornersEuclideanHalfSpace 3) ∞ C.Carrier := C.smooth
  let := T.connectedSpace_restrictAlong S K hK hext hconn
  refine {
    Carrier := C.Carrier
    topology := C.topology
    compact := C.compact
    hausdorff := C.hausdorff
    secondCountable := C.secondCountable
    connected := T.connectedSpace_restrictAlong S K hK hext hconn
    charts := C.charts
    manifold := C.smooth
    map := T.restrictAlongMap S K hK
    smooth := T.contMDiff_restrictAlongMap S K hK hext
    mfderiv_bijective := T.mfderiv_restrictAlongMap_bijective S K hK hext
    torusCount := Fintype.card (T.AlongBoundarySide S K)
    collar := (T.restrictAlongBoundaryToriDescended S K hK hext).collar
    collar_source := (T.restrictAlongBoundaryToriDescended S K hK hext).source_eq
    collar_disjoint := (T.restrictAlongBoundaryToriDescended S K hK hext).disjoint
    boundary_exhausted := ?_ }
  ext q
  change (modelWithCornersEuclideanHalfSpace 3).IsBoundaryPoint q ↔ _
  rw [T.restrictAlong_isBoundaryPoint_iff S K hK hext q]
  exact Iff.of_eq (congrArg (fun A : Set C.Carrier => q ∈ A)
    (T.restrictAlongBoundaryToriDescended_image S K hK hext).symm)

def alongOldGeometry (hk : T.cutCarrier.kind = .withBoundary)
    (i : Fin T.components.count) : AlongPieceGeometry W := by
  let C := GC.Topology.componentCarrier T.cutCarrier T.components i
  let D := recastCarrier C .withBoundary hk
  let : ChartedSpace (EuclideanHalfSpace 3) D.Carrier := D.charts
  let : IsManifold (modelWithCornersEuclideanHalfSpace 3) ∞ D.Carrier := D.smooth
  refine {
    Carrier := D.Carrier
    topology := D.topology
    compact := D.compact
    hausdorff := D.hausdorff
    secondCountable := D.secondCountable
    charts := D.charts
    manifold := D.smooth
    connected := T.components.connected i
    map := fun q => T.cutMap q.val
    smooth := (recast_contMDiff_iff_left C .withBoundary hk _).mpr
      (T.quotient_smooth.comp (contMDiff_subtype_val
        (I := T.cutCarrier.model) (U := T.components.piece i)))
    mfderiv_bijective := ?_
    torusCount := Fintype.card (T.OwnedSide i)
    collar := fun j => recastPD C .withBoundary hk ((T.pieceBoundaryTori i).collar j)
    collar_source := fun j => (recastPD_source C .withBoundary hk _).trans
      ((T.pieceBoundaryTori i).source_eq j)
    collar_disjoint := ?_
    boundary_exhausted := ?_ }
  · intro q
    have he := recast_mfderiv_left C .withBoundary hk (J := W.model)
      (fun q : D.Carrier => T.cutMap q.val) q
    exact he ▸ T.bijective_mfderiv_cutMap_val i q
  · intro a b hab
    rw [recastPD_target, recastPD_target]
    exact (T.pieceBoundaryTori i).disjoint hab
  · ext q
    change D.model.IsBoundaryPoint q ↔ _
    rw [recast_isBoundaryPoint_iff C .withBoundary hk]
    have hb := congrArg (fun A : Set C.Carrier => q ∈ A) (T.pieceBoundaryTori_image i)
    dsimp only [BoundaryTori.image, BoundaryTori.torusMap] at hb
    have he : (⋃ j, Set.range fun t =>
        recastPD C .withBoundary hk ((T.pieceBoundaryTori i).collar j) (t, halfZero)) =
        (T.pieceBoundaryTori i).image := by
      apply Set.iUnion_congr
      intro j
      apply congrArg Set.range
      funext t
      exact recastPD_apply C .withBoundary hk _ _
    rw [he]
    exact Iff.of_eq hb

def alongPieceGeometry
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected ((Set.univ :
      Set (T.restrictAlongPairing S K hK).QuotientSpace) \
        ((T.restrictAlongPairing S K hK).quotientMap ''
          (T.restrictAlongBoundaryTori S K).image))) :
    (Fin Sᶜ.card ⊕ Unit) → AlongPieceGeometry W :=
  Sum.elim (fun j => T.alongOldGeometry hk (T.subIndex Sᶜ j))
    (fun stub => by clear stub; exact T.alongRegionGeometry S K hK hext hconn)

abbrev AlongLedgerRetainedSide :=
  {s : T.Side // ∀ k ∈ K, s ≠ .inl k ∧ s ≠ .inr (.inl k)}

instance alongLedgerRetainedSide_fintype : Fintype (T.AlongLedgerRetainedSide K) := by
  classical
  exact Fintype.ofFinite _

def alongLedgerSideSum : (T.AlongUnpairedSeam K × Bool) ⊕ Fin T.externalCount →
    T.AlongLedgerRetainedSide K
  | .inl (c, true) => ⟨.inl c.val, by
      intro k hk
      constructor
      · intro he
        exact c.property ((Sum.inl.inj he) ▸ hk)
      · intro he
        cases he⟩
  | .inl (c, false) => ⟨.inr (.inl c.val), by
      intro k hk
      constructor
      · intro he
        cases he
      · intro he
        exact c.property ((Sum.inl.inj (Sum.inr.inj he)) ▸ hk)⟩
  | .inr i => ⟨.inr (.inr i), by
      intro k hk
      constructor
      · intro he
        cases he
      · intro he
        cases he⟩

def alongLedgerSideSumInv : T.AlongLedgerRetainedSide K →
    (T.AlongUnpairedSeam K × Bool) ⊕ Fin T.externalCount
  | ⟨.inl k, h⟩ => .inl (⟨k, fun hk => (h k hk).1 rfl⟩, true)
  | ⟨.inr (.inl k), h⟩ => .inl (⟨k, fun hk => (h k hk).2 rfl⟩, false)
  | ⟨.inr (.inr i), h⟩ => by
      clear h
      exact .inr i

def alongLedgerSideSumEquiv :
    (T.AlongUnpairedSeam K × Bool) ⊕ Fin T.externalCount ≃ T.AlongLedgerRetainedSide K where
  toFun := T.alongLedgerSideSum K
  invFun := T.alongLedgerSideSumInv K
  left_inv x := by
    rcases x with ⟨c, b⟩ | i
    · cases b <;> rfl
    · rfl
  right_inv x := by
    rcases x with ⟨s, h⟩
    rcases s with k | k | i <;> rfl

def alongLedgerOwner (s : T.AlongLedgerRetainedSide K) : Fin (Sᶜ.card + 1) :=
  T.alongPieceIndex S (T.sidePiece s.val)

abbrev AlongLedgerOwnedSide (j : Fin (Sᶜ.card + 1)) :=
  {s : T.AlongLedgerRetainedSide K // T.alongLedgerOwner S K s = j}

instance alongLedgerOwnedSide_fintype (j : Fin (Sᶜ.card + 1)) :
    Fintype (T.AlongLedgerOwnedSide S K j) := by
  classical
  exact Fintype.ofFinite _

def alongLedgerOwnerEquiv : T.AlongLedgerRetainedSide K ≃
    Σ j, T.AlongLedgerOwnedSide S K j :=
  (Equiv.sigmaFiberEquiv (T.alongLedgerOwner S K)).symm

def alongLedgerOwnerFinEquiv : T.AlongLedgerRetainedSide K ≃
    Σ j, Fin (Fintype.card (T.AlongLedgerOwnedSide S K j)) :=
  (T.alongLedgerOwnerEquiv S K).trans
    (Equiv.sigmaCongrRight fun j => Fintype.equivFin (T.AlongLedgerOwnedSide S K j))

theorem alongLedgerOwnerFinEquiv_apply (s : T.AlongLedgerRetainedSide K) :
    T.alongLedgerOwnerFinEquiv S K s =
      ⟨T.alongLedgerOwner S K s, Fintype.equivFin _ ⟨s, rfl⟩⟩ := rfl

def alongLedgerSeamSide (c : T.AlongUnpairedSeam K) (b : Bool) :
    Σ j, Fin (Fintype.card (T.AlongLedgerOwnedSide S K j)) :=
  T.alongLedgerOwnerFinEquiv S K (T.alongLedgerSideSum K (.inl (c, b)))

def alongLedgerExternalSide (i : Fin T.externalCount) :
    Σ j, Fin (Fintype.card (T.AlongLedgerOwnedSide S K j)) :=
  T.alongLedgerOwnerFinEquiv S K (T.alongLedgerSideSum K (.inr i))

theorem alongLedgerSides_bijective : Function.Bijective (Sum.elim
    (Function.uncurry (T.alongLedgerSeamSide S K)) (T.alongLedgerExternalSide S K)) := by
  have h : Sum.elim (Function.uncurry (T.alongLedgerSeamSide S K))
      (T.alongLedgerExternalSide S K) =
        T.alongLedgerOwnerFinEquiv S K ∘ T.alongLedgerSideSum K := by
    funext x
    rcases x with ⟨c, b⟩ | i <;> rfl
  rw [h]
  exact (T.alongLedgerOwnerFinEquiv S K).bijective.comp
    (T.alongLedgerSideSumEquiv K).bijective

def alongLedgerIndexedDomainEquiv :
    (Fin (Fintype.card (T.AlongUnpairedSeam K)) × Bool) ⊕ Fin T.externalCount ≃
      (T.AlongUnpairedSeam K × Bool) ⊕ Fin T.externalCount :=
  Equiv.sumCongr
    (Equiv.prodCongr (Fintype.equivFin (T.AlongUnpairedSeam K)).symm (Equiv.refl Bool))
    (Equiv.refl (Fin T.externalCount))

def alongLedgerIndexedSeamSide (c : Fin (Fintype.card (T.AlongUnpairedSeam K))) (b : Bool) :
    Σ j, Fin (Fintype.card (T.AlongLedgerOwnedSide S K j)) :=
  T.alongLedgerSeamSide S K ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c) b

theorem alongLedgerIndexedSides_bijective : Function.Bijective (Sum.elim
    (Function.uncurry (T.alongLedgerIndexedSeamSide S K)) (T.alongLedgerExternalSide S K)) := by
  have h : Sum.elim (Function.uncurry (T.alongLedgerIndexedSeamSide S K))
      (T.alongLedgerExternalSide S K) =
      Sum.elim (Function.uncurry (T.alongLedgerSeamSide S K)) (T.alongLedgerExternalSide S K) ∘
        T.alongLedgerIndexedDomainEquiv K := by
    funext x
    rcases x with ⟨c, b⟩ | i <;> rfl
  rw [h]
  exact (T.alongLedgerSides_bijective S K).comp (T.alongLedgerIndexedDomainEquiv K).bijective

theorem alongLedgerRetained_iff (s : T.Side) :
    (∀ k ∈ K, s ≠ .inl k ∧ s ≠ .inr (.inl k)) ↔
      match s with
      | .inl k => k ∉ K
      | .inr (.inl k) => k ∉ K
      | .inr (.inr i) => i ∈ Finset.univ := by
  rcases s with c | c | i <;> simp

theorem alongLedgerPieceIndex_last_iff (i : Fin T.components.count) :
    T.alongPieceIndex S i = Fin.last Sᶜ.card ↔ i ∈ S := by
  classical
  by_cases hi : i ∈ S <;> simp [alongPieceIndex, hi]

theorem alongLedgerPieceIndex_castSucc_iff (i : Fin T.components.count) (j : Fin Sᶜ.card) :
    T.alongPieceIndex S i = j.castSucc ↔ i = T.subIndex Sᶜ j := by
  classical
  by_cases hi : i ∈ S
  · have hne : i ≠ T.subIndex Sᶜ j := by
      intro he
      exact (Finset.mem_compl.mp (T.subIndex_mem Sᶜ j)) (he ▸ hi)
    simp only [alongPieceIndex, hi, dite_true, hne, iff_false]
    exact (Fin.castSucc_ne_last j).symm
  · rw [alongPieceIndex, dite_eq_right hi, Fin.castSucc_inj]
    constructor
    · intro h
      exact (T.subIndex_subIndexOf Sᶜ (Finset.mem_compl.mpr hi)).symm.trans
        (congrArg (T.subIndex Sᶜ) h)
    · intro h
      subst i
      exact T.subIndexOf_subIndex Sᶜ j

def alongLedgerLastOwnedEquiv :
    T.AlongLedgerOwnedSide S K (Fin.last Sᶜ.card) ≃ T.AlongBoundarySide S K where
  toFun a := ⟨a.val.val,
    (T.alongLedgerPieceIndex_last_iff S (T.sidePiece a.val.val)).mp a.property,
    (T.alongLedgerRetained_iff K a.val.val).mp a.val.property⟩
  invFun a := ⟨⟨a.val, (T.alongLedgerRetained_iff K a.val).mpr a.property.2⟩,
    (T.alongLedgerPieceIndex_last_iff S (T.sidePiece a.val)).mpr a.property.1⟩
  left_inv a := Subtype.ext (Subtype.ext (Eq.refl a.val.val))
  right_inv a := Subtype.ext (Eq.refl a.val)

theorem alongLedgerRetained_of_ownedOutside
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (j : Fin Sᶜ.card) (a : T.OwnedSide (T.subIndex Sᶜ j)) :
    ∀ k ∈ K, a.val ≠ .inl k ∧ a.val ≠ .inr (.inl k) := by
  intro k hk
  have hout : T.sidePiece a.val ∉ S := by
    rw [a.property]
    exact Finset.mem_compl.mp (T.subIndex_mem Sᶜ j)
  constructor
  · intro he
    apply hout
    rw [he]
    exact (hK k hk).1
  · intro he
    apply hout
    rw [he]
    exact (hK k hk).2

def alongLedgerCastOwnedEquiv
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) (j : Fin Sᶜ.card) :
    T.AlongLedgerOwnedSide S K j.castSucc ≃ T.OwnedSide (T.subIndex Sᶜ j) where
  toFun a := ⟨a.val.val,
    (T.alongLedgerPieceIndex_castSucc_iff S (T.sidePiece a.val.val) j).mp a.property⟩
  invFun a := ⟨⟨a.val, T.alongLedgerRetained_of_ownedOutside S K hK j a⟩,
    (T.alongLedgerPieceIndex_castSucc_iff S (T.sidePiece a.val) j).mpr a.property⟩
  left_inv a := Subtype.ext (Subtype.ext (Eq.refl a.val.val))
  right_inv a := Subtype.ext (Eq.refl a.val)

section AlongAssembly

variable (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((Set.univ :
    Set (T.restrictAlongPairing S K hK).QuotientSpace) \
      ((T.restrictAlongPairing S K hK).quotientMap ''
        (T.restrictAlongBoundaryTori S K).image)))

def alongGeometryIndexEquiv : (Fin Sᶜ.card ⊕ Unit) ≃ Fin (Sᶜ.card + 1) where
  toFun := Sum.elim Fin.castSucc (fun stub => by clear stub; exact Fin.last Sᶜ.card)
  invFun := Fin.lastCases (.inr ()) Sum.inl
  left_inv j := by cases j with
    | inl j => simp
    | inr j => cases j; simp
  right_inv j := by induction j using Fin.lastCases <;> simp

def alongGeometryOwner (s : T.AlongLedgerRetainedSide K) : Fin Sᶜ.card ⊕ Unit :=
  (T.alongGeometryIndexEquiv S).symm (T.alongLedgerOwner S K s)

abbrev AlongGeometryOwned (j : Fin Sᶜ.card ⊕ Unit) :=
  {s : T.AlongLedgerRetainedSide K // T.alongGeometryOwner S K s = j}

def alongGeometryOwnedEquiv (j : Fin Sᶜ.card ⊕ Unit) :
    T.AlongGeometryOwned S K j ≃
      T.AlongLedgerOwnedSide S K (T.alongGeometryIndexEquiv S j) where
  toFun a := ⟨a.val, by
    have h := congrArg (T.alongGeometryIndexEquiv S) a.property
    exact ((T.alongGeometryIndexEquiv S).apply_symm_apply _).symm.trans h⟩
  invFun a := ⟨a.val, by
    change (T.alongGeometryIndexEquiv S).symm (T.alongLedgerOwner S K a.val) = j
    rw [a.property]
    exact (T.alongGeometryIndexEquiv S).symm_apply_apply j⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

def alongGeometryFiberEquiv (j : Fin Sᶜ.card ⊕ Unit) :
    T.AlongGeometryOwned S K j ≃
      Fin ((T.alongPieceGeometry S K hK hext hk hconn j).torusCount) := by
  cases j with
  | inr stub =>
    cases stub
    exact (T.alongGeometryOwnedEquiv S K (.inr ())).trans
      ((T.alongLedgerLastOwnedEquiv S K).trans
        (Fintype.equivFin (T.AlongBoundarySide S K)))
  | inl j =>
    exact (T.alongGeometryOwnedEquiv S K (.inl j)).trans
      ((T.alongLedgerCastOwnedEquiv S K hK j).trans
        (Fintype.equivFin (T.OwnedSide (T.subIndex Sᶜ j))))

def alongGeometrySideEquiv : T.AlongLedgerRetainedSide K ≃
    Σ j, Fin ((T.alongPieceGeometry S K hK hext hk hconn j).torusCount) :=
  (Equiv.sigmaFiberEquiv (T.alongGeometryOwner S K)).symm.trans
    (Equiv.sigmaCongrRight (T.alongGeometryFiberEquiv S K hK hext hk hconn))

theorem alongGeometry_map_collar (j : Fin Sᶜ.card ⊕ Unit)
    (a : T.AlongGeometryOwned S K j) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    (T.alongPieceGeometry S K hK hext hk hconn j).map
      ((T.alongPieceGeometry S K hK hext hk hconn j).collar
        (T.alongGeometryFiberEquiv S K hK hext hk hconn j a) p) =
      T.cutMap (T.sideCollar a.val.val p) := by
  cases j with
  | inr stub =>
    cases stub
    let a' := T.alongGeometryOwnedEquiv S K (.inr ()) a
    change T.restrictAlongMap S K hK
      (T.restrictAlongHalfCollar S K hK
        (T.alongBoundarySide S K (Fintype.equivFin (T.AlongBoundarySide S K)
          (T.alongLedgerLastOwnedEquiv S K a'))) p) = _
    rw [T.alongBoundarySide_equivFin S K]
    rw [T.restrictAlongHalfCollar_apply S K hK _ hp,
      T.restrictAlongMap_quotientMap S K hK, T.subCollar_apply S _ _ hp]
    rfl
  | inl j =>
    let a' := T.alongGeometryOwnedEquiv S K (.inl j) a
    change T.cutMap (Subtype.val
      (recastPD (GC.Topology.componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j))
        .withBoundary hk ((T.pieceBoundaryTori (T.subIndex Sᶜ j)).collar
          (Fintype.equivFin (T.OwnedSide (T.subIndex Sᶜ j))
            (T.alongLedgerCastOwnedEquiv S K hK j a'))) p)) = _
    rw [recastPD_apply]
    change T.cutMap (Subtype.val (T.pieceCollar (T.subIndex Sᶜ j)
      ((Fintype.equivFin (T.OwnedSide (T.subIndex Sᶜ j))).symm
        (Fintype.equivFin (T.OwnedSide (T.subIndex Sᶜ j))
          (T.alongLedgerCastOwnedEquiv S K hK j a'))) p)) = _
    rw [Equiv.symm_apply_apply, T.pieceCollar_apply _ _ hp]
    rfl

theorem restrictAlongGluing_rel_of_selected_flip
    {k : Fin T.pairing.count} (hkK : k ∈ K)
    {x y : (T.subCarrier S).Carrier} (hx : x.val ∈ T.pairing.gluing.block k)
    (hy : y.val = T.pairing.gluing.flip k x.val) :
    (T.restrictAlongGluing S K hK).rel x y := by
  obtain ⟨n, hn⟩ := T.alongSeam_surjective K ⟨k, hkK⟩
  have hnv : (T.alongSeam K n).val = k := congrArg Subtype.val hn
  refine Or.inr ⟨n, ?_, Subtype.ext ?_⟩
  · rw [T.restrictAlongGluing_block_val S K hK, hnv]
    exact hx
  · rw [T.restrictAlongGluing_flip S K hK, T.restrictGluing_flip_val S,
      T.keptSeam_alongKeptIndex S K hK, hnv]
    exact hy

def alongGeometryRep (j : Fin Sᶜ.card ⊕ Unit) :
    (T.alongPieceGeometry S K hK hext hk hconn j).Carrier → T.cutCarrier.Carrier := by
  cases j with
  | inl j => exact fun q => q.val
  | inr stub => cases stub; exact fun q => (Quotient.out q).val

theorem alongGeometry_map_rep (j : Fin Sᶜ.card ⊕ Unit)
    (q : (T.alongPieceGeometry S K hK hext hk hconn j).Carrier) :
    (T.alongPieceGeometry S K hK hext hk hconn j).map q =
      T.cutMap (T.alongGeometryRep S K hK hext hk hconn j q) := by
  cases j with
  | inl j => rfl
  | inr stub =>
    cases stub
    exact (congrArg (T.restrictAlongMap S K hK) (Quotient.out_eq q)).symm

theorem alongGeometry_eq_of_rep_eq (j j' : Fin Sᶜ.card ⊕ Unit)
    (q : (T.alongPieceGeometry S K hK hext hk hconn j).Carrier)
    (q' : (T.alongPieceGeometry S K hK hext hk hconn j').Carrier)
    (he : T.alongGeometryRep S K hK hext hk hconn j q =
      T.alongGeometryRep S K hK hext hk hconn j' q') :
    (⟨j, q⟩ : Σ j, (T.alongPieceGeometry S K hK hext hk hconn j).Carrier) = ⟨j', q'⟩ := by
  cases j with
  | inl i =>
    cases j' with
    | inl i' =>
      change q.val = q'.val at he
      have hii : i = i' := by
        apply T.subIndex_injective Sᶜ
        by_contra hne
        exact (T.components.disjoint hne).le_bot ⟨q.property, he ▸ q'.property⟩
      subst i'
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext he))
    | inr stub =>
      cases stub
      change q.val = (Quotient.out q').val at he
      have hm : q.val ∈ T.subPiece S := he.symm ▸ (Quotient.out q').property
      exact ((Finset.mem_compl.mp (T.subIndex_mem Sᶜ i))
        (T.mem_of_mem_subPiece S hm q.property)).elim
  | inr stub =>
    cases stub
    cases j' with
    | inl i' =>
      change (Quotient.out q).val = q'.val at he
      have hm : q'.val ∈ T.subPiece S := he ▸ (Quotient.out q).property
      exact ((Finset.mem_compl.mp (T.subIndex_mem Sᶜ i'))
        (T.mem_of_mem_subPiece S hm q'.property)).elim
    | inr stub' =>
      cases stub'
      have hout : Quotient.out q = Quotient.out q' := Subtype.ext he
      exact Sigma.ext rfl (heq_of_eq (Quotient.out_injective hout))

theorem alongGeometry_eq_of_selected_flip (j j' : Fin Sᶜ.card ⊕ Unit)
    (q : (T.alongPieceGeometry S K hK hext hk hconn j).Carrier)
    (q' : (T.alongPieceGeometry S K hK hext hk hconn j').Carrier)
    {k : Fin T.pairing.count} (hkK : k ∈ K)
    (hx : T.alongGeometryRep S K hK hext hk hconn j q ∈ T.pairing.gluing.block k)
    (hy : T.alongGeometryRep S K hK hext hk hconn j' q' = T.pairing.gluing.flip k
      (T.alongGeometryRep S K hK hext hk hconn j q)) :
    (⟨j, q⟩ : Σ j, (T.alongPieceGeometry S K hK hext hk hconn j).Carrier) = ⟨j', q'⟩ := by
  have hsub {x : T.cutCarrier.Carrier} (hb : x ∈ T.pairing.gluing.block k) :
      x ∈ T.subPiece S := by
    rcases hb with hl | hr
    · exact T.piece_subset_subPiece S (hK k hkK).1 (T.left_owned k hl)
    · exact T.piece_subset_subPiece S (hK k hkK).2 (T.right_owned k hr)
  have hindex (i : Fin Sᶜ.card ⊕ Unit)
      (r : (T.alongPieceGeometry S K hK hext hk hconn i).Carrier)
      (hb : T.alongGeometryRep S K hK hext hk hconn i r ∈ T.pairing.gluing.block k) :
      i = .inr () := by
    cases i with
    | inr stub => cases stub; rfl
    | inl i =>
      exact ((Finset.mem_compl.mp (T.subIndex_mem Sᶜ i))
        (T.mem_of_mem_subPiece S (hsub hb) r.property)).elim
  have hj := hindex j q hx
  have hj' := hindex j' q' (hy.symm ▸ T.pairing.gluing.flip_mem_block hx)
  subst j
  subst j'
  have hrel := T.restrictAlongGluing_rel_of_selected_flip S K hK hkK
    (x := Quotient.out q) (y := Quotient.out q') hx hy
  have heq : q = q' := Quotient.out_equiv_out.mp hrel
  exact Sigma.ext rfl (heq_of_eq heq)

theorem alongGeometry_overlap (j j' : Fin Sᶜ.card ⊕ Unit)
    (q : (T.alongPieceGeometry S K hK hext hk hconn j).Carrier)
    (q' : (T.alongPieceGeometry S K hK hext hk hconn j').Carrier)
    (he : (T.alongPieceGeometry S K hK hext hk hconn j).map q =
      (T.alongPieceGeometry S K hK hext hk hconn j').map q') :
    (⟨j, q⟩ : Σ j, (T.alongPieceGeometry S K hK hext hk hconn j).Carrier) = ⟨j', q'⟩ ∨
      ∃ c : T.AlongUnpairedSeam K, ∃ t,
        (T.alongPieceGeometry S K hK hext hk hconn j).map q = T.seam c.val (t, 0) := by
  have hmap := he
  rw [T.alongGeometry_map_rep S K hK hext hk hconn j q,
    T.alongGeometry_map_rep S K hK hext hk hconn j' q'] at hmap
  have hquot := T.reconstruction.injective hmap
  rcases (Quotient.exact hquot : T.pairing.gluing.rel
    (T.alongGeometryRep S K hK hext hk hconn j q)
    (T.alongGeometryRep S K hK hext hk hconn j' q')) with hr | ⟨k, hx, hy⟩
  · exact Or.inl (T.alongGeometry_eq_of_rep_eq S K hK hext hk hconn j j' q q' hr)
  · by_cases hkK : k ∈ K
    · exact Or.inl (T.alongGeometry_eq_of_selected_flip S K hK hext hk hconn
        j j' q q' hkK hx hy)
    · right
      rw [T.alongGeometry_map_rep S K hK hext hk hconn j q]
      let x := T.alongGeometryRep S K hK hext hk hconn j q
      rcases hx with hl | hr
      · refine ⟨⟨k, hkK⟩, (T.pairing.leftParam k).symm ⟨x, hl⟩, ?_⟩
        rw [T.seam_zero, Homeomorph.apply_symm_apply]
        rfl
      · refine ⟨⟨k, hkK⟩,
          (T.pairing.matching k).symm ((T.pairing.rightParam k).symm ⟨x, hr⟩), ?_⟩
        rw [T.seam_zero]
        change T.reconstruction (T.pairing.quotientMap x) = _
        rw [T.quotientMap_leftParam_eq_rightParam_matching, Diffeomorph.apply_symm_apply,
          Homeomorph.apply_symm_apply]

theorem alongGeometry_covers :
    (⋃ j, Set.range ((T.alongPieceGeometry S K hK hext hk hconn j).map)) = Set.univ := by
  refine Set.eq_univ_of_forall fun w => ?_
  obtain ⟨q, rfl⟩ := T.reconstruction.surjective w
  induction q using Quotient.inductionOn with
  | h x =>
    have hx : x ∈ ⋃ i, (T.components.piece i : Set T.cutCarrier.Carrier) :=
      T.components.covers ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    by_cases hiS : i ∈ S
    · refine Set.mem_iUnion.mpr ⟨.inr (), ?_⟩
      exact ⟨(T.restrictAlongPairing S K hK).quotientMap
        ⟨x, T.piece_subset_subPiece S hiS hi⟩, rfl⟩
    · let j := T.subIndexOf Sᶜ (Finset.mem_compl.mpr hiS)
      refine Set.mem_iUnion.mpr ⟨.inl j, ?_⟩
      have hj : x ∈ T.components.piece (T.subIndex Sᶜ j) := by
        rw [T.subIndex_subIndexOf Sᶜ]
        exact hi
      exact ⟨⟨x, hj⟩, rfl⟩

def alongGeometryFiniteSideEquiv : T.AlongLedgerRetainedSide K ≃
    Σ j : Fin (Sᶜ.card + 1),
      Fin ((T.alongPieceGeometry S K hK hext hk hconn
        ((T.alongGeometryIndexEquiv S).symm j)).torusCount) :=
  (T.alongGeometrySideEquiv S K hK hext hk hconn).trans
    (Equiv.sigmaCongrLeft' (T.alongGeometryIndexEquiv S))

def alongGeometrySeamSide (c : Fin (Fintype.card (T.AlongUnpairedSeam K))) (b : Bool) :
    Σ j : Fin (Sᶜ.card + 1),
      Fin ((T.alongPieceGeometry S K hK hext hk hconn
        ((T.alongGeometryIndexEquiv S).symm j)).torusCount) :=
  T.alongGeometryFiniteSideEquiv S K hK hext hk hconn
    (T.alongLedgerSideSum K (.inl ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c, b)))

def alongGeometryExternalSide (i : Fin T.externalCount) :
    Σ j : Fin (Sᶜ.card + 1),
      Fin ((T.alongPieceGeometry S K hK hext hk hconn
        ((T.alongGeometryIndexEquiv S).symm j)).torusCount) :=
  T.alongGeometryFiniteSideEquiv S K hK hext hk hconn (T.alongLedgerSideSum K (.inr i))

theorem alongGeometrySides_bijective : Function.Bijective (Sum.elim
    (Function.uncurry (T.alongGeometrySeamSide S K hK hext hk hconn))
      (T.alongGeometryExternalSide S K hK hext hk hconn)) := by
  have he : Sum.elim (Function.uncurry (T.alongGeometrySeamSide S K hK hext hk hconn))
      (T.alongGeometryExternalSide S K hK hext hk hconn) =
        T.alongGeometryFiniteSideEquiv S K hK hext hk hconn ∘
          T.alongLedgerSideSum K ∘ T.alongLedgerIndexedDomainEquiv K := by
    funext z
    rcases z with ⟨c, b⟩ | i <;> rfl
  rw [he]
  exact (T.alongGeometryFiniteSideEquiv S K hK hext hk hconn).bijective.comp
    ((T.alongLedgerSideSumEquiv K).bijective.comp
      (T.alongLedgerIndexedDomainEquiv K).bijective)

theorem alongGeometryFinite_map_collar (a : T.AlongLedgerRetainedSide K)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (T.alongPieceGeometry S K hK hext hk hconn ((T.alongGeometryIndexEquiv S).symm
      (T.alongGeometryFiniteSideEquiv S K hK hext hk hconn a).1)).map
      ((T.alongPieceGeometry S K hK hext hk hconn ((T.alongGeometryIndexEquiv S).symm
        (T.alongGeometryFiniteSideEquiv S K hK hext hk hconn a).1)).collar
          (T.alongGeometryFiniteSideEquiv S K hK hext hk hconn a).2 p) =
      T.cutMap (T.sideCollar a.val p) := by
  let Y := Σ j, Fin ((T.alongPieceGeometry S K hK hext hk hconn j).torusCount)
  let f : Y → W.Carrier := fun b =>
    (T.alongPieceGeometry S K hK hext hk hconn b.1).map
      ((T.alongPieceGeometry S K hK hext hk hconn b.1).collar b.2 p)
  let e := Equiv.sigmaCongrLeft' (β := fun j =>
    Fin ((T.alongPieceGeometry S K hK hext hk hconn j).torusCount))
      (T.alongGeometryIndexEquiv S)
  change f (e.symm (e (T.alongGeometrySideEquiv S K hK hext hk hconn a))) = _
  rw [e.symm_apply_apply]
  exact T.alongGeometry_map_collar S K hK hext hk hconn
    (T.alongGeometryOwner S K a) ⟨a, rfl⟩ hp

theorem alongGeometryFinite_covers :
    (⋃ j : Fin (Sᶜ.card + 1), Set.range
      ((T.alongPieceGeometry S K hK hext hk hconn
        ((T.alongGeometryIndexEquiv S).symm j)).map)) = Set.univ := by
  exact (Function.Surjective.iUnion_comp (T.alongGeometryIndexEquiv S).symm.surjective
    (fun j => Set.range (T.alongPieceGeometry S K hK hext hk hconn j).map)).trans
      (T.alongGeometry_covers S K hK hext hk hconn)

theorem alongGeometryExternal_local (i : Fin T.externalCount) (t : Torus) :
    IsLocalDiffeomorphAt (modelWithCornersEuclideanHalfSpace 3) W.model ∞
      (T.alongPieceGeometry S K hK hext hk hconn ((T.alongGeometryIndexEquiv S).symm
        (T.alongGeometryExternalSide S K hK hext hk hconn i).1)).map
      ((T.alongPieceGeometry S K hK hext hk hconn ((T.alongGeometryIndexEquiv S).symm
        (T.alongGeometryExternalSide S K hK hext hk hconn i).1)).collar
          (T.alongGeometryExternalSide S K hK hext hk hconn i).2 (t, halfZero)) := by
  let a := T.alongLedgerSideSum K (.inr i)
  let s := T.alongGeometryFiniteSideEquiv S K hK hext hk hconn a
  let G := T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm s.1)
  let d := G.collar s.2
  have hp : (t, halfZero) ∈ d.source :=
    (G.collar_source s.2).symm ▸ zero_mem_halfCollarSource t
  have ht := d.map_source hp
  have hinv := d.symm.isLocalDiffeomorphAt (modelWithCornersEuclideanHalfSpace 3)
    halfCollarModel ∞ ht
  have hextlocal : IsLocalDiffeomorphAt halfCollarModel W.model ∞ (T.external.collar i)
      (d.symm (d (t, halfZero))) := by
    have h0 : (t, halfZero) ∈ (T.external.collar i).source := by
      rw [T.external.source_eq]
      exact zero_mem_halfCollarSource t
    convert (T.external.collar i).isLocalDiffeomorphAt halfCollarModel W.model ∞ h0 using 1
    exact d.toPartialEquiv.left_inv hp
  refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
    (hinv.comp W.model W.Carrier hextlocal)
  filter_upwards [d.open_target.mem_nhds ht] with y hy
  have hsource : d.symm y ∈ halfCollarSource := (G.collar_source s.2) ▸ d.map_target hy
  have hfold := T.alongGeometryFinite_map_collar S K hK hext hk hconn a hsource
  change G.map (d (d.symm y)) = T.cutMap (T.sideCollar (.inr (.inr i)) (d.symm y)) at hfold
  have hright := congrArg G.map (d.toPartialEquiv.right_inv hy)
  exact hright.symm.trans (hfold.trans (T.marked_collar i (d.symm y) hsource))

theorem alongGeometryFinite_overlap (j j' : Fin (Sᶜ.card + 1))
    (q : (T.alongPieceGeometry S K hK hext hk hconn
      ((T.alongGeometryIndexEquiv S).symm j)).Carrier)
    (q' : (T.alongPieceGeometry S K hK hext hk hconn
      ((T.alongGeometryIndexEquiv S).symm j')).Carrier)
    (he : (T.alongPieceGeometry S K hK hext hk hconn
      ((T.alongGeometryIndexEquiv S).symm j)).map q =
      (T.alongPieceGeometry S K hK hext hk hconn
        ((T.alongGeometryIndexEquiv S).symm j')).map q') :
    (⟨j, q⟩ : Σ j, (T.alongPieceGeometry S K hK hext hk hconn
      ((T.alongGeometryIndexEquiv S).symm j)).Carrier) = ⟨j', q'⟩ ∨
      ∃ c : Fin (Fintype.card (T.AlongUnpairedSeam K)), ∃ t,
        (T.alongPieceGeometry S K hK hext hk hconn
          ((T.alongGeometryIndexEquiv S).symm j)).map q =
          T.seam ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val (t, 0) := by
  rcases T.alongGeometry_overlap S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j) ((T.alongGeometryIndexEquiv S).symm j')
      q q' he with hs | ⟨c, t, hc⟩
  · exact Or.inl ((Equiv.sigmaCongrLeft (β := fun i =>
      (T.alongPieceGeometry S K hK hext hk hconn i).Carrier)
        (T.alongGeometryIndexEquiv S).symm).injective hs)
  · right
    refine ⟨Fintype.equivFin (T.AlongUnpairedSeam K) c, t, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hc

def alongCutSystem : EmbeddedCutSystem W .withBoundary where
  count := Sᶜ.card + 1
  count_pos := Nat.succ_pos _
  Piece j := (T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j)).Carrier
  map j := (T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j)).map
  smooth j := (T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j)).smooth
  mfderiv_bijective j := (T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j)).mfderiv_bijective
  covers := T.alongGeometryFinite_covers S K hK hext hk hconn
  torusCount j := (T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j)).torusCount
  collar j := (T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j)).collar
  collar_source j := (T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j)).collar_source
  collar_disjoint j := (T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j)).collar_disjoint
  boundary_exhausted j := (T.alongPieceGeometry S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm j)).boundary_exhausted
  seamCount := Fintype.card (T.AlongUnpairedSeam K)
  side := T.alongGeometrySeamSide S K hK hext hk hconn
  externalCount := T.externalCount
  externalSide := T.alongGeometryExternalSide S K hK hext hk hconn
  sides_bijective := T.alongGeometrySides_bijective S K hK hext hk hconn
  matching c := T.pairing.matching ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val
  seam c := T.seam ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val
  seam_source c := T.seam_source ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val
  seam_neg c t s hs h1 := by
    have hp : (t, halfPoint (-s) (neg_nonneg.2 hs)) ∈ halfCollarSource := by
      change -s < 1
      linarith
    exact (T.seam_negative _ t s hs h1).trans
      (T.alongGeometryFinite_map_collar S K hK hext hk hconn
        (T.alongLedgerSideSum K (.inl
          ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c, true))) hp).symm
  seam_pos c t s hs h1 := by
    have hp : (T.pairing.matching
        ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val t, halfPoint s hs)
        ∈ halfCollarSource := h1
    exact (T.seam_positive _ t s hs h1).trans
      (T.alongGeometryFinite_map_collar S K hK hext hk hconn
        (T.alongLedgerSideSum K (.inl
          ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c, false))) hp).symm
  seam_interior c := T.seam_interior ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val
  external_local := T.alongGeometryExternal_local S K hK hext hk hconn
  overlap := T.alongGeometryFinite_overlap S K hK hext hk hconn

def alongGeometryOriginalPoint (x : T.cutCarrier.Carrier) :
    Σ j, (T.alongPieceGeometry S K hK hext hk hconn j).Carrier := by
  have hx : ∃ i, x ∈ T.components.piece i := by
    exact Set.mem_iUnion.mp (T.components.covers ▸ Set.mem_univ x)
  let i := Classical.choose hx
  have hi : x ∈ T.components.piece i := Classical.choose_spec hx
  by_cases hiS : i ∈ S
  · exact ⟨.inr (), (T.restrictAlongPairing S K hK).quotientMap
      ⟨x, T.piece_subset_subPiece S hiS hi⟩⟩
  · let j := T.subIndexOf Sᶜ (Finset.mem_compl.mpr hiS)
    have hj : x ∈ T.components.piece (T.subIndex Sᶜ j) := by
      rw [T.subIndex_subIndexOf Sᶜ]
      exact hi
    exact ⟨.inl j, ⟨x, hj⟩⟩

theorem alongGeometry_map_originalPoint (x : T.cutCarrier.Carrier) :
    (T.alongPieceGeometry S K hK hext hk hconn
      (T.alongGeometryOriginalPoint S K hK hext hk hconn x).1).map
        (T.alongGeometryOriginalPoint S K hK hext hk hconn x).2 = T.cutMap x := by
  let f : (Σ j, (T.alongPieceGeometry S K hK hext hk hconn j).Carrier) → W.Carrier :=
    fun b => (T.alongPieceGeometry S K hK hext hk hconn b.1).map b.2
  change f (T.alongGeometryOriginalPoint S K hK hext hk hconn x) = T.cutMap x
  simp only [alongGeometryOriginalPoint]
  split <;> rfl

def alongOriginalPoint (x : T.cutCarrier.Carrier) : (T.alongCutSystem S K hK hext hk hconn).Cut :=
  Equiv.sigmaCongrLeft' (β := fun j =>
    (T.alongPieceGeometry S K hK hext hk hconn j).Carrier) (T.alongGeometryIndexEquiv S)
      (T.alongGeometryOriginalPoint S K hK hext hk hconn x)

theorem alongOriginalPoint_fold (x : T.cutCarrier.Carrier) :
    (T.alongCutSystem S K hK hext hk hconn).fold
      (T.alongOriginalPoint S K hK hext hk hconn x) = T.cutMap x := by
  let Y := Σ j, (T.alongPieceGeometry S K hK hext hk hconn j).Carrier
  let f : Y → W.Carrier := fun q =>
    (T.alongPieceGeometry S K hK hext hk hconn q.1).map q.2
  let e := Equiv.sigmaCongrLeft' (β := fun j =>
    (T.alongPieceGeometry S K hK hext hk hconn j).Carrier) (T.alongGeometryIndexEquiv S)
  change f (e.symm (e (T.alongGeometryOriginalPoint S K hK hext hk hconn x))) = _
  rw [e.symm_apply_apply]
  exact T.alongGeometry_map_originalPoint S K hK hext hk hconn x

end AlongAssembly

theorem restrictAlong_hconn_complement
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S)
    (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
      Set (T.restrictAlongPairing S K hK).QuotientSpace)) :
    IsConnected ((Set.univ : Set (T.restrictAlongPairing S K hK).QuotientSpace) \
      ((T.restrictAlongPairing S K hK).quotientMap ''
        (T.restrictAlongBoundaryTori S K).image)) := by
  rwa [T.restrictAlongCarrier_interior_eq S K hK hext] at hconn

def contractAlong
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
      Set (T.restrictAlongPairing S K hK).QuotientSpace)) : TorusPresentation W :=
  (T.alongCutSystem S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)).toTorusPresentation

def contractAlongMap
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
      Set (T.restrictAlongPairing S K hK).QuotientSpace)) (x : T.cutCarrier.Carrier) :
    (T.contractAlong S K hK hext hk hconn).cutCarrier.Carrier :=
  T.alongOriginalPoint S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn) x

section ContractAlong

variable (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
    Set (T.restrictAlongPairing S K hK).QuotientSpace))

theorem contractAlong_components_count :
    (T.contractAlong S K hK hext hk hconn).components.count =
      T.components.count - S.card + 1 := T.alongPieceIndex_count S

theorem contractAlong_pairing_count :
    (T.contractAlong S K hK hext hk hconn).pairing.count =
      T.pairing.count - K.card := T.alongUnpairedSeam_card K

theorem contractAlong_externalCount :
    (T.contractAlong S K hK hext hk hconn).externalCount = T.externalCount := rfl

theorem contractAlong_reconstruction_eq (x : T.cutCarrier.Carrier) :
    (T.contractAlong S K hK hext hk hconn).reconstruction
      ((T.contractAlong S K hK hext hk hconn).pairing.quotientMap
        (T.contractAlongMap S K hK hext hk hconn x)) =
      T.reconstruction (T.pairing.quotientMap x) :=
  T.alongOriginalPoint_fold S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn) x

theorem contractAlong_eq_contract_of_all
    (hAll : K = Finset.univ.filter fun k => T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hconn' : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S)) :
    (T.contractAlong S K hK hext hk hconn).components.count =
        (T.contract S hext hk hconn').components.count ∧
      (T.contractAlong S K hK hext hk hconn).pairing.count =
        (T.contract S hext hk hconn').pairing.count ∧
      (T.contractAlong S K hK hext hk hconn).externalCount =
        (T.contract S hext hk hconn').externalCount := by
  constructor
  · rw [T.contractAlong_components_count S K hK hext hk hconn,
      T.contract_components_count S hext hk hconn']
  · constructor
    · rw [T.contractAlong_pairing_count S K hK hext hk hconn,
        T.contract_pairing_count S hext hk hconn', hAll]
    · rfl

end ContractAlong

end GC.Seifert.TorusPresentation
