import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclidean
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBlockGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeProduct
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierClassification

/-!
# Shape dispatch for good unions of Seifert blocks

The ten positive-port shapes consume whole interior geometries. Zero-port blocks are handled
on their whole compact carrier before the componentwise open assembly. Closed blocks with at
most two cones contract to an actual two-solid-torus presentation; the final dispatch consumes
only the existing torus mapping-class, filled-pants and closed-triangle geometry inputs.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open GC.Geometry
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace SeifertData

def openGeometryModel (d : SeifertData) : ThurstonModel := by
  classical
  exact if d.IsSolidTorus ∨ d.orbChi = 0 then .euclidean else .hyperbolicProduct

theorem openGeometryModel_of_solid (d : SeifertData) (h : d.IsSolidTorus) :
    d.openGeometryModel = .euclidean := by
  simp only [openGeometryModel, h, true_or, ite_true]

theorem openGeometryModel_of_not_solid (d : SeifertData) (hopen : 0 < d.ports)
    (h : ¬ d.IsSolidTorus) : d.openGeometryModel = d.openModelOf hopen h := by
  simp only [openGeometryModel, h, false_or, openModelOf, openTable]

theorem open_shapes (d : SeifertData) (hopen : 0 < d.ports) :
    (d.k = 2 ∧ d.ports = 2 ∧ d.cones.length = 0 ∧ d.normals.length = 0) ∨
    (d.k = 3 ∧ d.ports = 3 ∧ d.cones.length = 0 ∧ d.normals.length = 0) ∨
    (d.k = 3 ∧ d.ports = 2 ∧ d.cones.length = 1 ∧ d.normals.length = 0) ∨
    (d.k = 3 ∧ d.ports = 1 ∧ d.cones.length = 2 ∧ d.normals.length = 0) ∨
    (d.k = 3 ∧ d.ports = 2 ∧ d.cones.length = 0 ∧ d.normals.length = 1) ∨
    (d.k = 1 ∧ d.ports = 1 ∧ d.cones.length = 0 ∧ d.normals.length = 0) ∨
    (d.k = 2 ∧ d.ports = 1 ∧ d.cones.length = 1 ∧ d.normals.length = 0) ∨
    (d.k = 2 ∧ d.ports = 1 ∧ d.cones.length = 0 ∧ d.normals.length = 1) ∨
    (d.k = 3 ∧ d.ports = 1 ∧ d.cones.length = 1 ∧ d.normals.length = 1) ∨
    (d.k = 3 ∧ d.ports = 1 ∧ d.cones.length = 0 ∧ d.normals.length = 2) := by
  have hk := d.k_le_three
  have hsum := d.ports_add_length_add_length
  have hp : d.ports = 1 ∨ d.ports = 2 ∨ d.ports = 3 := by omega
  rcases hp with hp | hp | hp
  · have hc : d.cones.length = 0 ∨ d.cones.length = 1 ∨ d.cones.length = 2 := by omega
    rcases hc with hc | hc | hc
    · have hn : d.normals.length = 0 ∨ d.normals.length = 1 ∨ d.normals.length = 2 := by omega
      rcases hn with hn | hn | hn
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hp, hc, hn⟩)))))
      · right
        right
        right
        right
        right
        right
        right
        left
        exact ⟨by omega, hp, hc, hn⟩
      · right
        right
        right
        right
        right
        right
        right
        right
        right
        exact ⟨by omega, hp, hc, hn⟩
    · have hn : d.normals.length = 0 ∨ d.normals.length = 1 := by omega
      rcases hn with hn | hn
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hp, hc, hn⟩))))))
      · right
        right
        right
        right
        right
        right
        right
        right
        left
        exact ⟨by omega, hp, hc, hn⟩
    · have hn : d.normals.length = 0 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hp, hc, hn⟩)))
  · have hc : d.cones.length = 0 ∨ d.cones.length = 1 := by omega
    rcases hc with hc | hc
    · have hn : d.normals.length = 0 ∨ d.normals.length = 1 := by omega
      rcases hn with hn | hn
      · exact Or.inl ⟨by omega, hp, hc, hn⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hp, hc, hn⟩))))
    · have hn : d.normals.length = 0 := by omega
      exact Or.inr (Or.inr (Or.inl ⟨by omega, hp, hc, hn⟩))
  · have hc : d.cones.length = 0 := by omega
    have hn : d.normals.length = 0 := by omega
    exact Or.inr (Or.inl ⟨by omega, hp, hc, hn⟩)

theorem cones_eq_two_two_of_map (d : SeifertData) (h : d.cones.map Prod.fst = [2, 2]) :
    ∃ q₁ q₂ : ℤ, d.cones = [(2, q₁), (2, q₂)] := by
  rcases d with ⟨k, ports, cones, normals, hk, hk3, hc, hg, hs⟩
  cases cones with
  | nil => simp at h
  | cons c cs =>
    cases cs with
    | nil => simp at h
    | cons e es =>
      have hh : c.1 = 2 ∧ e.1 = 2 ∧ es = [] := by simpa using h
      refine ⟨c.2, e.2, ?_⟩
      have hce : c = (2, c.2) := Prod.ext hh.1 rfl
      have hee : e = (2, e.2) := Prod.ext hh.2.1 rfl
      change c :: e :: es = [(2, c.2), (2, e.2)]
      rw [hh.2.2]
      exact congrArg₂ List.cons hce (congrArg₂ List.cons hee rfl)

end SeifertData

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem exists_unfilledOpenInteriorGeometry_model (B : SeifertBlock W d)
    (h0 : d.fillingCount = 0) (hopen : 0 < d.ports) :
    ∃ G : W.InteriorGeometry ⊤,
      let := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
      let := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
      G.model = d.openGeometryModel := by
  classical
  let := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  let := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
  by_cases hs : d.IsSolidTorus
  · refine ⟨solidTorusShapeGeometry (B.unfilledCharts h0) hs, ?_⟩
    rw [solidTorusShapeGeometry_model]
    simp only [SeifertData.openGeometryModel, hs, true_or, ite_true]
  have hsum := d.ports_add_fillingCount
  have hk3 := d.k_le_three
  have hc : d.cones = [] := List.length_eq_zero_iff.mp (by
    change d.cones.length + d.normals.length = 0 at h0
    omega)
  have hk : d.k = 2 ∨ d.k = 3 := by
    have hl : d.cones.length = 0 := by rw [hc]; rfl
    simp only [SeifertData.IsSolidTorus] at hs
    omega
  refine ⟨B.unfilledBlockGeometry h0 hk, ?_⟩
  rw [B.unfilledBlockGeometry_model]
  have hp : d.ports = d.k := by omega
  rcases hk with hk | hk
  · have he : d.orbChi = 0 := by norm_num [SeifertData.orbChi, hc, hp, hk]
    simp only [hk, SeifertData.openGeometryModel, he, or_true, ite_true]
  · have he : d.orbChi ≠ 0 := by norm_num [SeifertData.orbChi, hc, hp, hk]
    simp only [hk, SeifertData.openGeometryModel, hs, he, or_self, ite_false]
    decide

theorem exists_openInteriorGeometry_model (B : SeifertBlock W d) (hB : B.IsGoodBlock)
    (hopen : 0 < d.ports) (hT : TorusMappingClassLinear)
    (hA : FilledPantsBlockGeometry.{u}) :
    ∃ G : W.InteriorGeometry ⊤,
      let := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
      let := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
      G.model = d.openGeometryModel := by
  classical
  let := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  let := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
  by_cases h0 : d.fillingCount = 0
  · exact B.exists_unfilledOpenInteriorGeometry_model h0 hopen
  by_cases hs : d.IsSolidTorus
  · refine ⟨solidTorusShapeGeometry (Classical.choice (B.exists_charts hT)) hs, ?_⟩
    rw [solidTorusShapeGeometry_model]
    simp only [SeifertData.openGeometryModel, hs, true_or, ite_true]
  by_cases hn : d.ports = 2 ∧ d.cones = []
  · refine ⟨normalT2IntervalGeometry (Classical.choice (B.exists_charts hT)) hn, ?_⟩
    rw [normalT2IntervalGeometry_model]
    have he : d.orbChi = 0 := by simp [SeifertData.orbChi, hn.1, hn.2]
    simp only [SeifertData.openGeometryModel, he, or_true, ite_true]
  by_cases he : d.orbChi = 0
  · rcases (d.orbChi_eq_zero_iff_of_open hopen hs).mp he with hn' | ht
    · exact False.elim (hn hn')
    obtain ⟨q₁, q₂, hq⟩ := d.cones_eq_two_two_of_map ht.2
    refine ⟨B.twistedIBundleInteriorGeometry hT q₁ q₂ ht.1 hq, ?_⟩
    rw [B.twistedIBundleInteriorGeometry_model]
    simp only [SeifertData.openGeometryModel, he, or_true, ite_true]
  have hk : d.k = 3 := by
    have hsum := d.ports_add_length_add_length
    have hk3 := d.k_le_three
    simp only [SeifertData.IsSolidTorus] at hs
    have hc : d.cones ≠ [] := by
      intro hc
      have hl : d.cones.length = 0 := by rw [hc]; rfl
      have hn' : d.ports ≠ 2 := fun hp => hn ⟨hp, hc⟩
      have hf : 0 < d.cones.length + d.normals.length := Nat.pos_of_ne_zero h0
      omega
    have hl : 0 < d.cones.length := List.length_pos_iff.mpr hc
    omega
  have hm : d.openModelOf hopen hs = .hyperbolicProduct := by
    simp only [SeifertData.openModelOf, openTable, ite_eq_right he]
  obtain ⟨G, hG⟩ := hA W d B hk (Nat.pos_of_ne_zero h0) hopen hs hB hm
  refine ⟨G, ?_⟩
  rw [hG]
  simp only [SeifertData.openGeometryModel, hs, he, or_self, ite_false]

theorem exists_openInteriorGeometry (B : SeifertBlock W d) (hB : B.IsGoodBlock)
    (hopen : 0 < d.ports) (hT : TorusMappingClassLinear)
    (hA : FilledPantsBlockGeometry.{u}) : Nonempty (W.InteriorGeometry ⊤) := by
  obtain ⟨G, hG⟩ := B.exists_openInteriorGeometry_model hB hopen hT hA
  exact ⟨G⟩

def openInteriorGeometry (B : SeifertBlock W d) (hB : B.IsGoodBlock)
    (hopen : 0 < d.ports) (hT : TorusMappingClassLinear)
    (hA : FilledPantsBlockGeometry.{u}) : W.InteriorGeometry ⊤ :=
  Classical.choice (B.exists_openInteriorGeometry hB hopen hT hA)

end SeifertBlock

private def dispatchOpenDiffeomorph {M : Type u} [TopologicalSpace M]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
    [ChartedSpace H M] (U : TopologicalSpace.Opens M) (h : ∀ x : M, x ∈ U) :
    U ≃ₘ⟮I, I⟯ M where
  toFun := Subtype.val
  invFun x := ⟨x, h x⟩
  left_inv x := Subtype.ext (Eq.refl x.val)
  right_inv x := Eq.refl x
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_id

namespace BlockedPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem piece_eq_top_of_zeroPort (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0) :
    B.base.components.piece i = ⊤ := by
  have hn := (B.unique_block_of_ports_eq_zero i h).1
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ j, (B.base.components.piece j : Set B.base.cutCarrier.Carrier) := by
    rw [B.base.components.covers]
    trivial
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  have he : j = i := Fin.ext (by have hj := j.isLt; have hi := i.isLt; omega)
  rwa [he] at hj

theorem cutInterior_eq_univ_of_zeroPort (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0) :
    (B.base.cutCarrier.interior : Set B.base.cutCarrier.Carrier) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hp : x ∈ B.base.components.piece i := by rw [B.piece_eq_top_of_zeroPort i h]; trivial
  let y : (componentCarrier B.base.cutCarrier B.base.components i).Carrier := ⟨x, hp⟩
  have hy : (componentCarrier B.base.cutCarrier B.base.components i).model.IsInteriorPoint y := by
    change y ∈ ((componentCarrier B.base.cutCarrier B.base.components i).interior : Set _)
    rw [(B.block i).interior_eq_univ_of_ports_zero h]
    trivial
  change B.base.cutCarrier.model.IsInteriorPoint (⟨x, hp⟩ : B.base.components.piece i) at hy
  exact ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mp hy

def zeroPortDiffeomorph (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0) :
    (componentCarrier B.base.cutCarrier B.base.components i).Carrier
      ≃ₘ⟮(componentCarrier B.base.cutCarrier B.base.components i).model,
        (NoCuts.carrier Q).model⟯ (NoCuts.carrier Q).Carrier := by
  have hp : ∀ x, x ∈ B.base.components.piece i := by
    intro x
    rw [B.piece_eq_top_of_zeroPort i h]
    trivial
  have hc : ∀ x, x ∈ B.base.cutCarrier.interior := by
    intro x
    change x ∈ (B.base.cutCarrier.interior : Set _)
    rw [B.cutInterior_eq_univ_of_zeroPort i h]
    trivial
  have hq : ∀ x, x ∈ B.base.interiorImage := by
    intro x
    rw [B.base.interiorImage_eq_interior_of_pairing_count_zero
      (B.unique_block_of_ports_eq_zero i h).2]
    exact BoundarylessManifold.isInteriorPoint
  exact (dispatchOpenDiffeomorph (I := B.base.cutCarrier.model)
    (B.base.components.piece i) hp).trans
    ((dispatchOpenDiffeomorph (I := B.base.cutCarrier.model)
      B.base.cutCarrier.interior hc).symm.trans
      (B.base.interiorDiffeomorph.trans
        (dispatchOpenDiffeomorph (I := (NoCuts.carrier Q).model) B.base.interiorImage hq)))

theorem zeroPortDiffeomorph_apply (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0)
    (x : (componentCarrier B.base.cutCarrier B.base.components i).Carrier) :
    B.zeroPortDiffeomorph i h x = B.base.cutMap x.val := by
  exact B.base.interior_map _

theorem zeroPortDiffeomorph_preservesOrientation
    (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0) :
    (B.zeroPortDiffeomorph i h).preservesOrientation
      (componentCarrier B.base.cutCarrier B.base.components i).orientation
      (NoCuts.carrier Q).orientation := by
  intro x
  obtain ⟨L, hL, ho⟩ := B.base.quotient_oriented x.val
  have he : ((B.zeroPortDiffeomorph i h).mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv = L := by
    ext v
    change mfderiv (componentCarrier B.base.cutCarrier B.base.components i).model
      (NoCuts.carrier Q).model
      (B.zeroPortDiffeomorph i h) x v = L v
    have hf : (B.zeroPortDiffeomorph i h :
        (componentCarrier B.base.cutCarrier B.base.components i).Carrier →
          (NoCuts.carrier Q).Carrier) =
        (fun y => B.base.cutMap y.val) := funext (B.zeroPortDiffeomorph_apply i h)
    rw [hf]
    change mfderiv B.base.cutCarrier.model (NoCuts.carrier Q).model
      (fun y : B.base.components.piece i => B.base.cutMap y.val) x v = L v
    have hd := Manifold.mfderiv_restrict_open B.base.cutCarrier.model
      (NoCuts.carrier Q).model (B.base.components.piece i) B.base.cutMap
      B.base.quotient_smooth (show B.base.components.piece i from x)
    exact (congrArg (fun f => f v) hd).trans (hL v).symm
  rw [he]
  change Orientation.map (Fin 3) L (B.base.cutCarrier.orientation.orientation x.val) = _
  rw [B.zeroPortDiffeomorph_apply i h]
  exact ho

def zeroPortBlock (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0) :
    SeifertBlock (NoCuts.carrier Q) (B.data i) :=
  (B.block i).transport (B.zeroPortDiffeomorph i h)
    (B.zeroPortDiffeomorph_preservesOrientation i h)

theorem closedTriangleBlock_of_zeroPort (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0)
    (hc : (B.data i).cones.length = 3) : ClosedTriangleBlock Q :=
  ⟨B.data i, h, hc, ⟨B.zeroPortBlock i h⟩⟩

theorem geometricDecomposition_of_zeroPort_triangle
    (B : BlockedPresentation (NoCuts.carrier Q)) (hC : ClosedTriangleBlockGeometry.{u})
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0)
    (hc : (B.data i).cones.length = 3) : Nonempty (GeometricDecomposition Q) :=
  hC Q (B.closedTriangleBlock_of_zeroPort i h hc)

def geometricDecomposition_of_positivePorts (B : BlockedPresentation (NoCuts.carrier Q))
    (hB : B.IsGood) (hp : ∀ i, 0 < (B.data i).ports)
    (hT : TorusMappingClassLinear) (hA : FilledPantsBlockGeometry.{u}) :
    GeometricDecomposition Q :=
  geometricDecomposition_of_blockGeometry B hB
    (fun i => (B.block i).openInteriorGeometry (hB i) (hp i) hT hA)

end BlockedPresentation

theorem goodBlockUnionGeometry_or_closedSmallBlock
    (hT : TorusMappingClassLinear) (hA : FilledPantsBlockGeometry.{u})
    (hC : ClosedTriangleBlockGeometry.{u}) (Q : ConnectedClosedOrientedManifold.{u} 3)
    (hQ : GoodBlockUnion Q) :
    Nonempty (GeometricDecomposition Q) ∨
      ∃ d : SeifertData, d.ports = 0 ∧ d.cones.length ≤ 2 ∧
        Nonempty (SeifertBlock (NoCuts.carrier Q) d) := by
  classical
  obtain ⟨B, hB⟩ := hQ
  by_cases hz : ∃ i, (B.data i).ports = 0
  · obtain ⟨i, hp⟩ := hz
    by_cases hc : (B.data i).cones.length = 3
    · exact Or.inl (B.geometricDecomposition_of_zeroPort_triangle hC i hp hc)
    · have hs := (B.data i).ports_add_length_add_length
      have hk := (B.data i).k_le_three
      exact Or.inr ⟨B.data i, hp, by omega, ⟨B.zeroPortBlock i hp⟩⟩
  · have hp : ∀ i, 0 < (B.data i).ports := by
      intro i
      exact Nat.pos_of_ne_zero (fun hi => hz ⟨i, hi⟩)
    exact Or.inl ⟨B.geometricDecomposition_of_positivePorts hB hp hT hA⟩


namespace TorusPresentation

variable {W : CompactCarrier.{u}}

theorem exists_elementary_of_pieces_diffeomorph_counts (T : TorusPresentation W)
    (kind : Fin T.components.count → ℕ) (hkind : ∀ i, kind i ∈ ({1, 2, 3} : Finset ℕ))
    (base : ∀ i, PlanarBase.{u} (kind i))
    (hcard : ∀ i, Fintype.card (T.OwnedSide i) = kind i)
    (e : ∀ i, ((base i).surface.Carrier × Circle)
      ≃ₘ⟮(SurfaceModel.model (base i).surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
        T.components.piece i) :
    ∃ E : ElementaryPresentation W, E.complexity = T.pairing.count ∧
      E.toTorus.components.count = T.components.count := by
  have hport := fun i => T.exists_port_of_diffeomorph i (base i) (hcard i) (e i)
  choose port ψ hzero using hport
  let ψ' : ∀ i, T.OwnedSide i →
      (GC.Endpoint.Torus ≃ₘ⟮torusModel, torusModel⟯ GC.Endpoint.Torus) :=
    fun i s => ψ i ((port i).symm s)
  let Ψ : T.Side → (GC.Endpoint.Torus ≃ₘ⟮torusModel, torusModel⟯ GC.Endpoint.Torus) :=
    fun s => ψ' (T.sidePiece s) ⟨s, rfl⟩
  have hΨ : ∀ i (s : T.OwnedSide i), Ψ s.val = ψ' i s := by
    rintro i ⟨s, hs⟩
    subst hs
    rfl
  obtain ⟨δ, hδ, hδ1, E, hT, hE⟩ := T.exists_elementary_of_torus_products Ψ
    kind hkind base port e fun i j t => by
      rw [hΨ i (port i j)]
      change T.pieceCollar i (port i j) (ψ i ((port i).symm (port i j)) t, halfZero) = _
      rw [Equiv.symm_apply_apply]
      exact hzero i j t
  refine ⟨E, hE, ?_⟩
  rw [hT]
  rfl

theorem exists_elementary_of_forall_piece_counts (T : TorusPresentation W)
    (h : ∀ i, ∃ k, k ∈ ({1, 2, 3} : Finset ℕ) ∧ Fintype.card (T.OwnedSide i) = k ∧
      ∃ B : PlanarBase.{u} k, Nonempty (((B.surface.Carrier × Circle)
        ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
          T.components.piece i))) :
    ∃ E : ElementaryPresentation W, E.complexity = T.pairing.count ∧
      E.toTorus.components.count = T.components.count := by
  choose kind hkind hcard base e using h
  exact T.exists_elementary_of_pieces_diffeomorph_counts kind hkind base hcard
    fun i => (e i).some

end TorusPresentation

theorem exists_elementary_contract_counts {W : CompactCarrier.{u}}
    (E : ElementaryPresentation W)
    (S : Finset (Fin E.toTorus.components.count)) (hext : ∀ i, E.toTorus.externalPiece i ∉ S)
    (hk : E.toTorus.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (E.toTorus.restrictMap S) \ E.toTorus.crossingSurface S))
    (k : ℕ) (hk3 : k ∈ ({1, 2, 3} : Finset ℕ))
    (hcard : Fintype.card ((E.toTorus.contract S hext hk hconn).OwnedSide
      (E.toTorus.contractLast S hext hk hconn)) = k)
    (B : PlanarBase.{u} k)
    (he : Nonempty ((B.surface.Carrier × Circle)
      ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (E.toTorus.contract S hext hk hconn).cutCarrier.model⟯
          (E.toTorus.contract S hext hk hconn).components.piece
            (E.toTorus.contractLast S hext hk hconn))) :
    ∃ E' : ElementaryPresentation W,
      E'.complexity = (E.toTorus.contract S hext hk hconn).pairing.count ∧
        E'.toTorus.components.count = (E.toTorus.contract S hext hk hconn).components.count := by
  refine (E.toTorus.contract S hext hk hconn).exists_elementary_of_forall_piece_counts ?_
  intro i
  induction i using Fin.lastCases with
  | last => exact ⟨k, hk3, hcard, B, he⟩
  | cast j =>
    exact ⟨E.kind (E.toTorus.subIndex Sᶜ j), E.kind_mem _,
      (E.toTorus.card_contract_ownedSide_kept S hext hk hconn j).trans
        (E.piece _).card_ownedSide, (E.piece _).base,
      ⟨(E.piece _).trivialization.trans
        (E.toTorus.contractKeptDiffeomorph S hext hk hconn j)⟩⟩

namespace ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}
  (E : ElementaryPresentation (NoCuts.carrier Q))

theorem sum_kind_closed : ∑ i, E.kind i = 2 * E.complexity := by
  have hc := Fintype.card_congr E.portEquiv
  simp only [TorusPresentation.Side, Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma,
    E.toTorus.externalCount_eq_zero] at hc
  exact hc.symm.trans (by dsimp [complexity]; omega)

theorem sum_kind_sub_one_closed :
    ∑ i, (E.kind i - 1) = 2 * E.complexity - E.toTorus.components.count := by
  have hk : ∀ i ∈ (Finset.univ : Finset (Fin E.toTorus.components.count)), 1 ≤ E.kind i := by
    intro i hi
    have hh := E.kind_mem i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  rw [Finset.sum_tsub_distrib Finset.univ hk, E.sum_kind_closed]
  simp

theorem kind_le_of_closed_counts (i : Fin E.toTorus.components.count) :
    E.kind i - 1 ≤ 2 * E.complexity - E.toTorus.components.count := by
  rw [← E.sum_kind_sub_one_closed]
  exact Finset.single_le_sum (fun j hj => Nat.zero_le (E.kind j - 1)) (Finset.mem_univ i)

theorem isStandardFactor_of_twoPieces_oneSeam (hc : E.toTorus.components.count = 2)
    (hn : E.complexity = 1) : isStandardFactor Q := by
  have hk : ∀ i, E.kind i = 1 := by
    intro i
    have hb := E.kind_le_of_closed_counts i
    have hm := E.kind_mem i
    rw [hc, hn] at hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  exact isStandardFactor_of_twoSolidTori E.toTorus hc
    (fun i => by simpa only [hk i] using E.piece i)

theorem exists_absorb_counts (j : Fin E.toTorus.pairing.count) (b : Bool)
    (h : E.IsAbsorbSeam j b) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q),
      E'.complexity + 1 = E.complexity ∧
        E'.toTorus.components.count + 1 = E.toTorus.components.count := by
  let hext := TorusPresentation.externalPiece_not_mem_of_closed E.toTorus (E.toTorus.seamPair j)
  obtain ⟨e⟩ := mergedSolidTorus (NoCuts.carrier Q) E j b h hext
  let P : SolidTorusPiece E.toTorus (E.seamPiece j b) := by
    simpa only [h.1] using E.piece (E.seamPiece j b)
  obtain ⟨E', hn, hc⟩ := exists_elementary_contract_counts E (E.toTorus.seamPair j)
    hext (E.toTorus.cutCarrier_kind_of_pos j.pos) (h.isConnected_region hext)
    1 (by simp) (E.absorbContraction_card_ownedSide_last j b h hext)
    P.base ⟨P.trivialization.trans e.symm⟩
  refine ⟨E', ?_, ?_⟩
  · rw [hn]
    exact E.absorbContraction_pairing_count j b h hext
  · rw [hc]
    exact E.absorbContraction_components_count j b h hext

theorem exists_absorbSeam_of_threePieces_twoSeams
    (hc : E.toTorus.components.count = 3) (hn : E.complexity = 2) :
    ∃ j b, E.IsAbsorbSeam j b := by
  classical
  have hbound : ∀ i, E.kind i ≤ 2 := by
    intro i
    have hb := E.kind_le_of_closed_counts i
    rw [hc, hn] at hb
    omega
  have hsolid : ∃ i, E.kind i = 1 := by
    by_contra hs
    have hk : ∀ i, 2 ≤ E.kind i := by
      intro i
      have hm := E.kind_mem i
      have hi : E.kind i ≠ 1 := fun hi => hs ⟨i, hi⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    have he : (∑ i : Fin E.toTorus.components.count, 2) ≤ ∑ i, E.kind i :=
      Finset.sum_le_sum (fun i hi => hk i)
    rw [E.sum_kind_closed, hn] at he
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hc] at he
    omega
  have hhost : ∀ j b, E.kind (E.seamPiece j b) = 1 → E.kind (E.hostPiece j b) = 2 := by
    intro j b hs
    have hh := hbound (E.hostPiece j b)
    have hm := E.kind_mem (E.hostPiece j b)
    by_contra he
    have hh1 : E.kind (E.hostPiece j b) = 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    let PS : SolidTorusPiece E.toTorus (E.seamPiece j b) := by
      simpa only [hs] using E.piece (E.seamPiece j b)
    let PH : SolidTorusPiece E.toTorus (E.hostPiece j b) := by
      simpa only [hh1] using E.piece (E.hostPiece j b)
    have hc2 : E.toTorus.components.count = 2 := by
      cases b
      · exact E.toTorus.components_count_of_solidSides j PH PS
      · exact E.toTorus.components_count_of_solidSides j PS PH
    omega
  obtain ⟨i, hi⟩ := hsolid
  let P : SolidTorusPiece E.toTorus i := by simpa only [hi] using E.piece i
  obtain ⟨s, hs⟩ := P.port 0
  rcases s with j | j | j
  · have he : E.kind (E.seamPiece j true) = 1 := by
      change E.kind (E.toTorus.leftPiece j) = 1
      rw [show E.toTorus.leftPiece j = i from hs]
      exact hi
    exact ⟨j, true, he, hhost j true he⟩
  · have he : E.kind (E.seamPiece j false) = 1 := by
      change E.kind (E.toTorus.rightPiece j) = 1
      rw [show E.toTorus.rightPiece j = i from hs]
      exact hi
    exact ⟨j, false, he, hhost j false he⟩
  · have he : j.val < 0 := by simpa only [E.toTorus.externalCount_eq_zero] using j.isLt
    omega

theorem isStandardFactor_of_threePieces_twoSeams
    (hc : E.toTorus.components.count = 3) (hn : E.complexity = 2) : isStandardFactor Q := by
  obtain ⟨j, b, h⟩ := E.exists_absorbSeam_of_threePieces_twoSeams hc hn
  obtain ⟨E', hn', hc'⟩ := E.exists_absorb_counts j b h
  exact E'.isStandardFactor_of_twoPieces_oneSeam (by omega) (by omega)

theorem exists_merge_counts (hT : TorusMappingClassLinear)
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q),
      E'.complexity + 1 = E.complexity ∧
        E'.toTorus.components.count + 1 = E.toTorus.components.count := by
  let hext := TorusPresentation.externalPiece_not_mem_of_closed E.toTorus (E.toTorus.seamPair j)
  obtain ⟨B, he⟩ := E.exists_planarBase_diffeomorph_merge_of_torusMappingClassLinear
    hT j b h hf
  have hk3 : E.kind (E.hostPiece j b) - 1 ∈ ({1, 2, 3} : Finset ℕ) := by
    have hk := E.mergeBase_kind_mem j b h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
    omega
  obtain ⟨E', hn, hc⟩ := exists_elementary_contract_counts E (E.toTorus.seamPair j)
    hext (E.toTorus.cutCarrier_kind_of_pos j.pos) (h.isConnected_region hf hext)
    (E.kind (E.hostPiece j b) - 1) hk3
    (E.mergeContraction_card_ownedSide_last j b h hf hext) B he
  refine ⟨E', ?_, ?_⟩
  · rw [hn]
    exact E.mergeContraction_pairing_count j b h hf hext
  · rw [hc]
    exact E.mergeContraction_components_count j b h hf hext

end ElementaryPresentation

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

def elementaryPieceDatum (B : SeifertBlock W d) (x : Option (Fin d.fillingCount)) :
    Σ k, ProductFibredPiece B.presentation (B.piece x) k :=
  match x with
  | none => ⟨d.k, B.product⟩
  | some m => ⟨1, B.solid m⟩

def closedSmallElementary (B : SeifertBlock W d) : ElementaryPresentation W where
  toTorus := B.presentation
  kind i := (B.elementaryPieceDatum (B.piece.symm i)).1
  kind_mem i := by
    cases B.piece.symm i with
    | none =>
      change d.k ∈ ({1, 2, 3} : Finset ℕ)
      have hl := d.one_le_k
      have hu := d.k_le_three
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    | some m => simp [elementaryPieceDatum]
  piece i := by
    have Pi := (B.elementaryPieceDatum (B.piece.symm i)).2
    simpa only [B.piece.apply_symm_apply] using Pi

theorem closedSmallElementary_product_kind (B : SeifertBlock W d) :
    B.closedSmallElementary.kind (B.piece none) = d.k := by
  change (B.elementaryPieceDatum (B.piece.symm (B.piece none))).1 = d.k
  rw [B.piece.symm_apply_apply]
  rfl

theorem closedSmallElementary_solid_kind (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.closedSmallElementary.kind (B.piece (some m)) = 1 := by
  change (B.elementaryPieceDatum (B.piece.symm (B.piece (some m)))).1 = 1
  rw [B.piece.symm_apply_apply]
  rfl

theorem closedSmallElementary_hostSelfSeamFree (B : SeifertBlock W d)
    (m : Fin d.fillingCount) :
    B.closedSmallElementary.HostSelfSeamFree (B.seam m) true := by
  intro j hj
  have hh : B.closedSmallElementary.hostPiece (B.seam m) true = B.piece none :=
    B.rightPiece_seam m
  obtain ⟨n, rfl⟩ := B.seam.surjective j
  have h : B.piece (some n) = B.piece none :=
    (B.leftPiece_seam n).symm.trans (hj.trans hh)
  exact (Option.some_ne_none n (B.piece.injective h)).elim

theorem closedSmallElementary_normal_isMergeSeam (B : SeifertBlock W d)
    (hk : d.k = 3) (n : Fin d.normals.length) :
    B.closedSmallElementary.IsMergeSeam (B.seam (Fin.natAdd d.cones.length n)) true := by
  refine ⟨?_, ?_, ?_⟩
  · change B.closedSmallElementary.kind
      (B.presentation.leftPiece (B.seam (Fin.natAdd d.cones.length n))) = 1
    rw [B.leftPiece_seam, B.closedSmallElementary_solid_kind]
  · change 2 ≤ B.closedSmallElementary.kind
      (B.presentation.rightPiece (B.seam (Fin.natAdd d.cones.length n)))
    rw [B.rightPiece_seam, B.closedSmallElementary_product_kind, hk]
    norm_num
  · change PrimitiveSlope.delta
      (torusUnit (B.presentation.pairing.matching (B.seam (Fin.natAdd d.cones.length n))) •
        meridianSlope) fiberSlope = 1
    rw [B.delta_fiberSlope, SeifertData.fillingSlope, Fin.append_right]
    norm_num

end SeifertBlock
namespace SeifertBlock

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {d : SeifertData}

theorem isStandardFactor_of_closed_kind_two (B : SeifertBlock (NoCuts.carrier Q) d)
    (hp : d.ports = 0) (hk : d.k = 2) : isStandardFactor Q := by
  have hf : d.fillingCount = 2 := by
    simpa only [hp, hk, zero_add] using d.ports_add_fillingCount
  apply B.closedSmallElementary.isStandardFactor_of_threePieces_twoSeams
  · change B.presentation.components.count = 3
    rw [B.components_count, hf]
  · change B.presentation.pairing.count = 2
    rw [B.pairing_count, hf]

theorem isStandardFactor_of_closed_kind_three (B : SeifertBlock (NoCuts.carrier Q) d)
    (hp : d.ports = 0) (hk : d.k = 3) (hc : d.cones.length ≤ 2)
    (hT : TorusMappingClassLinear) : isStandardFactor Q := by
  have hf : d.fillingCount = 3 := by
    simpa only [hp, hk, zero_add] using d.ports_add_fillingCount
  have hn : 0 < d.normals.length := by
    have hh := d.ports_add_length_add_length
    omega
  let n : Fin d.normals.length := ⟨0, hn⟩
  let m : Fin d.fillingCount := Fin.natAdd d.cones.length n
  have hm := B.closedSmallElementary_normal_isMergeSeam hk n
  have hs := B.closedSmallElementary_hostSelfSeamFree m
  obtain ⟨E, hnE, hcE⟩ := B.closedSmallElementary.exists_merge_counts hT (B.seam m) true hm hs
  have hpieces : B.closedSmallElementary.toTorus.components.count = 4 := by
    change B.presentation.components.count = 4
    rw [B.components_count, hf]
  have hseams : B.closedSmallElementary.complexity = 3 := by
    change B.presentation.pairing.count = 3
    rw [B.pairing_count, hf]
  exact E.isStandardFactor_of_threePieces_twoSeams (by omega) (by omega)

end SeifertBlock

theorem SeifertBlock.isStandardFactor_of_closed_kind_one
    {Q : ConnectedClosedOrientedManifold.{u} 3} {d : SeifertData}
    (B : SeifertBlock (NoCuts.carrier Q) d) (hp : d.ports = 0) (hk : d.k = 1) :
    isStandardFactor Q := by
  have hf : d.fillingCount = 1 := by
    simpa only [hp, hk, zero_add] using d.ports_add_fillingCount
  have hc : B.presentation.components.count = 2 := by
    rw [B.components_count, hf]
  have P0 : SolidTorusPiece B.presentation (B.piece none) := by
    simpa only [hk] using B.product
  apply isStandardFactor_of_twoSolidTori B.presentation hc
  intro i
  have Pi : SolidTorusPiece B.presentation (B.piece (B.piece.symm i)) := by
    cases B.piece.symm i with
    | none => exact P0
    | some m => exact B.solid m
  exact (B.piece.apply_symm_apply i) ▸ Pi

theorem SeifertBlock.geometricDecomposition_of_closed_kind_one
    {Q : ConnectedClosedOrientedManifold.{u} 3} {d : SeifertData}
    (B : SeifertBlock (NoCuts.carrier Q) d) (hp : d.ports = 0) (hk : d.k = 1) :
    Nonempty (GeometricDecomposition Q) :=
  geometricDecomposition_of_isStandardFactor (B.isStandardFactor_of_closed_kind_one hp hk)

namespace SeifertBlock

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {d : SeifertData}

theorem isStandardFactor_of_closed_small (B : SeifertBlock (NoCuts.carrier Q) d)
    (hp : d.ports = 0) (hc : d.cones.length ≤ 2) (hT : TorusMappingClassLinear) :
    isStandardFactor Q := by
  by_cases hk1 : d.k = 1
  · exact B.isStandardFactor_of_closed_kind_one hp hk1
  by_cases hk2 : d.k = 2
  · exact B.isStandardFactor_of_closed_kind_two hp hk2
  have hk3 : d.k = 3 := by
    have hlow := d.one_le_k
    have hhigh := d.k_le_three
    omega
  exact B.isStandardFactor_of_closed_kind_three hp hk3 hc hT

theorem geometricDecomposition_of_closed_small (B : SeifertBlock (NoCuts.carrier Q) d)
    (hp : d.ports = 0) (hc : d.cones.length ≤ 2) (hT : TorusMappingClassLinear) :
    Nonempty (GeometricDecomposition Q) :=
  geometricDecomposition_of_isStandardFactor (B.isStandardFactor_of_closed_small hp hc hT)

end SeifertBlock

theorem goodBlockUnionGeometry (hT : TorusMappingClassLinear)
    (hA : FilledPantsBlockGeometry.{u}) (hC : ClosedTriangleBlockGeometry.{u}) :
    GoodBlockUnionGeometry.{u} := by
  intro Q hQ
  rcases goodBlockUnionGeometry_or_closedSmallBlock hT hA hC Q hQ with hG | ⟨d, hp, hc, B⟩
  · exact hG
  · exact B.some.geometricDecomposition_of_closed_small hp hc hT

end GC.Seifert
