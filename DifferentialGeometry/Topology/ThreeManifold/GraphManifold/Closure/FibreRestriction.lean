import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverDiscGlobal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryAtlas
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProdLeft
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas

/-!
The actual pullback of a circle fibration along a compact smooth surface inclusion has
its own boundary-sensitive atlas, original-fibre trivializations and pulled-back orientation.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.CircleFibration

section ModelCoordinates

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')

private theorem fibreRestrictionModel_smooth (e : H ≃ₜ H') (L : E ≃L[ℝ] E')
    (h : ∀ x, J (e x) = L (I x)) : ContMDiff I J ∞ e := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨e.continuous.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ∞ (J ∘ e ∘ I.symm) (range I) (I x)
  apply L.contDiff.contDiffAt.contDiffWithinAt.congr_of_mem
    (fun v hv => ?_) (mem_range_self x)
  change J (e (I.symm v)) = L v
  rw [h, I.right_inv hv]

private def fibreRestrictionModelDiffeomorph (e : H ≃ₜ H') (L : E ≃L[ℝ] E')
    (h : ∀ x, J (e x) = L (I x)) : H ≃ₘ⟮I, J⟯ H' where
  toEquiv := e.toEquiv
  contMDiff_toFun := fibreRestrictionModel_smooth I J e L h
  contMDiff_invFun := fibreRestrictionModel_smooth J I e.symm L.symm (by
    intro x
    have he := congrArg L.symm (h (e.symm x))
    rw [e.apply_symm_apply, L.symm_apply_apply] at he
    exact he.symm)

end ModelCoordinates

def fibreRestrictionKind : ModelBoundaryKind → CarrierModel
  | .closed => .closed
  | .withBoundary => .withBoundary

private def fibreRestrictionProductModelIso (k : ModelBoundaryKind) :
    ModelProd (k.Space 2) (EuclideanSpace ℝ (Fin 1))
      ≃ₘ⟮(k.model 2).prod (𝓡 1), (fibreRestrictionKind k).model⟯
      (fibreRestrictionKind k).Space := by
  cases k with
  | closed =>
    let L : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin 3) := EuclideanSpace.finAddEquivProd.symm
    exact fibreRestrictionModelDiffeomorph _ _ L.toHomeomorph L (fun x => rfl)
  | withBoundary =>
    exact fibreRestrictionModelDiffeomorph _ _
      (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftHomeomorph 1 1)
      (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftCoordinates 1 1)
      (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftHomeomorph_model 1 1)

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
variable (F : CircleFibration C U) (B' : CompactSurface.{u})
variable (b : C(B'.Carrier, F.base.Carrier)) (hinj : Injective b)

abbrev FibrePullbackTotal := {x : U | F.projection x ∈ range b}

def fibrePullbackBaseHomeomorph : B'.Carrier ≃ₜ range b :=
  (b.continuous.isClosedEmbedding hinj).isEmbedding.toHomeomorph

def fibrePullbackProjection : C(FibrePullbackTotal F B' b, B'.Carrier) :=
  ⟨fun x => (F.fibrePullbackBaseHomeomorph B' b hinj).symm ⟨F.projection x.val, x.property⟩,
    (F.fibrePullbackBaseHomeomorph B' b hinj).symm.continuous.comp
      ((F.projection.continuous.comp continuous_subtype_val).subtype_mk
        (fun x => x.property))⟩

theorem fibrePullbackProjection_square (x : FibrePullbackTotal F B' b) :
    b (F.fibrePullbackProjection B' b hinj x) = F.projection x.val :=
  congrArg Subtype.val
    ((F.fibrePullbackBaseHomeomorph B' b hinj).apply_symm_apply
      ⟨F.projection x.val, x.property⟩)

instance fibrePullbackCompact : CompactSpace (FibrePullbackTotal F B' b) := by
  apply isCompact_iff_compactSpace.mp
  apply GC.Seifert.CircleFibration.isCompact_preimage F
  exact (isCompact_range b.continuous).isClosed

def fibrePullbackInclusion : C(FibrePullbackTotal F B' b, C.Carrier) :=
  ⟨fun x => x.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

theorem fibrePullbackInclusion_injective : Injective (F.fibrePullbackInclusion B' b) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem fibrePullbackInclusion_range :
    range (F.fibrePullbackInclusion B' b) =
      Subtype.val '' {x : U | F.projection x ∈ range b} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

def fibrePullbackNeighborhood (y : B'.Carrier) : TopologicalSpace.Opens B'.Carrier :=
  TopologicalSpace.Opens.comap b (F.neighborhood (b y))

theorem mem_fibrePullbackNeighborhood (y : B'.Carrier) :
    y ∈ F.fibrePullbackNeighborhood B' b y := F.mem_neighborhood (b y)

def fibrePullbackTotalOpen (y : B'.Carrier) :
    TopologicalSpace.Opens (FibrePullbackTotal F B' b) :=
  TopologicalSpace.Opens.comap (F.fibrePullbackProjection B' b hinj)
    (F.fibrePullbackNeighborhood B' b y)

private def fibrePullbackLocalInverse (y : B'.Carrier)
    (q : F.fibrePullbackNeighborhood B' b y × Circle) : F.fibrePullbackTotalOpen B' b hinj y :=
  let v : F.neighborhood (b y) := ⟨b q.1.val, q.1.property⟩
  let z := (F.trivialization (b y)).symm (v, q.2)
  have hz : F.projection z.val = b q.1.val := by
    rw [← F.projection_trivialization (b y) z, Diffeomorph.apply_symm_apply]
  let x : FibrePullbackTotal F B' b := ⟨z.val, q.1.val, hz.symm⟩
  have hp : F.fibrePullbackProjection B' b hinj x = q.1.val :=
    hinj ((F.fibrePullbackProjection_square B' b hinj x).trans hz)
  ⟨x, by
    change F.fibrePullbackProjection B' b hinj x ∈ F.fibrePullbackNeighborhood B' b y
    rw [hp]
    exact q.1.property⟩

private theorem fibrePullbackLocalInverse_val (y : B'.Carrier)
    (q : F.fibrePullbackNeighborhood B' b y × Circle) :
    (F.fibrePullbackLocalInverse B' b hinj y q).val.val =
      ((F.trivialization (b y)).symm (⟨b q.1.val, q.1.property⟩, q.2)).val := rfl

private theorem fibrePullbackLocalInverse_projection (y : B'.Carrier)
    (q : F.fibrePullbackNeighborhood B' b y × Circle) :
    F.fibrePullbackProjection B' b hinj (F.fibrePullbackLocalInverse B' b hinj y q).val =
      q.1.val := by
  apply hinj
  rw [F.fibrePullbackProjection_square, F.fibrePullbackLocalInverse_val]
  rw [← F.projection_trivialization (b y), Diffeomorph.apply_symm_apply]

private def fibrePullbackLocalForward (y : B'.Carrier)
    (x : F.fibrePullbackTotalOpen B' b hinj y) : F.fibrePullbackNeighborhood B' b y × Circle :=
  let hx : F.projection x.val.val ∈ F.neighborhood (b y) := by
    rw [← F.fibrePullbackProjection_square B' b hinj x.val]
    exact x.property
  (⟨F.fibrePullbackProjection B' b hinj x.val, x.property⟩,
    (F.trivialization (b y) ⟨x.val.val, hx⟩).2)

private def fibrePullbackLocalHomeomorph (y : B'.Carrier) :
    (F.fibrePullbackNeighborhood B' b y × Circle) ≃ₜ
      F.fibrePullbackTotalOpen B' b hinj y where
  toFun := F.fibrePullbackLocalInverse B' b hinj y
  invFun := F.fibrePullbackLocalForward B' b hinj y
  left_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      exact F.fibrePullbackLocalInverse_projection B' b hinj y q
    · change (F.trivialization (b y)
        ((F.trivialization (b y)).symm (⟨b q.1.val, q.1.property⟩, q.2))).2 = q.2
      rw [Diffeomorph.apply_symm_apply]
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    let z : TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y)) :=
      ⟨x.val.val, by
        change F.projection x.val.val ∈ F.neighborhood (b y)
        rw [← F.fibrePullbackProjection_square B' b hinj x.val]
        exact x.property⟩
    have he : (⟨b (F.fibrePullbackProjection B' b hinj x.val), x.property⟩,
        (F.trivialization (b y) z).2) = F.trivialization (b y) z := by
      apply Prod.ext
      · apply Subtype.ext
        exact (F.fibrePullbackProjection_square B' b hinj x.val).trans
          (F.projection_trivialization (b y) z).symm
      · rfl
    change ((F.trivialization (b y)).symm
      (⟨b (F.fibrePullbackProjection B' b hinj x.val), x.property⟩,
        (F.trivialization (b y) z).2)).val = x.val.val
    rw [he, Diffeomorph.symm_apply_apply]
  continuous_toFun := by
    have hc : Continuous (fun q : F.fibrePullbackNeighborhood B' b y × Circle =>
        ((⟨b q.1.val, q.1.property⟩ : F.neighborhood (b y)), q.2)) :=
      ((b.continuous.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk
        (fun q => q.1.property)).prodMk continuous_snd
    have ht := continuous_subtype_val.comp ((F.trivialization (b y)).symm.continuous.comp hc)
    exact (ht.subtype_mk
      (fun q => (F.fibrePullbackLocalInverse B' b hinj y q).val.property)).subtype_mk
        (fun q => (F.fibrePullbackLocalInverse B' b hinj y q).property)
  continuous_invFun := by
    have hp : Continuous (fun x : F.fibrePullbackTotalOpen B' b hinj y =>
        F.fibrePullbackProjection B' b hinj x.val) :=
      (F.fibrePullbackProjection B' b hinj).continuous.comp continuous_subtype_val
    have hx : Continuous (fun x : F.fibrePullbackTotalOpen B' b hinj y =>
        (⟨x.val.val, by
          change F.projection x.val.val ∈ F.neighborhood (b y)
          rw [← F.fibrePullbackProjection_square B' b hinj x.val]
          exact x.property⟩ : TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y)))) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun x => by
          change F.projection x.val.val ∈ F.neighborhood (b y)
          rw [← F.fibrePullbackProjection_square B' b hinj x.val]
          exact x.property)
    exact (hp.subtype_mk (fun x => x.property)).prodMk
      ((F.trivialization (b y)).continuous.comp hx).snd

def fibrePullbackPatch (y : B'.Carrier) :
    OpenPartialHomeomorph (F.fibrePullbackNeighborhood B' b y × Circle)
      (FibrePullbackTotal F B' b) :=
  let q : F.fibrePullbackNeighborhood B' b y × Circle :=
    (⟨y, F.mem_fibrePullbackNeighborhood B' b y⟩, 1)
  let hne : Nonempty (F.fibrePullbackTotalOpen B' b hinj y) :=
    ⟨F.fibrePullbackLocalInverse B' b hinj y q⟩
  (F.fibrePullbackLocalHomeomorph B' b hinj y).toOpenPartialHomeomorph.trans
    ((F.fibrePullbackTotalOpen B' b hinj y).openPartialHomeomorphSubtypeCoe hne)

theorem fibrePullbackPatch_source (y : B'.Carrier) :
    (F.fibrePullbackPatch B' b hinj y).source = univ := by
  ext q
  change (q ∈ univ ∧ _ ∈ univ) ↔ q ∈ univ
  simp only [mem_univ, and_self]

theorem fibrePullbackPatch_target (y : B'.Carrier) :
    (F.fibrePullbackPatch B' b hinj y).target = F.fibrePullbackTotalOpen B' b hinj y := by
  let q : F.fibrePullbackNeighborhood B' b y × Circle :=
    (⟨y, F.mem_fibrePullbackNeighborhood B' b y⟩, 1)
  let hne : Nonempty (F.fibrePullbackTotalOpen B' b hinj y) :=
    ⟨F.fibrePullbackLocalInverse B' b hinj y q⟩
  let inc := (F.fibrePullbackTotalOpen B' b hinj y).openPartialHomeomorphSubtypeCoe hne
  ext x
  change (x ∈ inc.target ∧ inc.symm x ∈ univ) ↔ x ∈ F.fibrePullbackTotalOpen B' b hinj y
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  simp only [mem_univ, and_true]
  rfl

theorem fibrePullbackPatch_cover (x : FibrePullbackTotal F B' b) :
    ∃ y, x ∈ (F.fibrePullbackPatch B' b hinj y).target := by
  refine ⟨F.fibrePullbackProjection B' b hinj x, ?_⟩
  rw [F.fibrePullbackPatch_target]
  exact F.mem_fibrePullbackNeighborhood B' b (F.fibrePullbackProjection B' b hinj x)

theorem fibrePullbackPatch_projection (y : B'.Carrier)
    (q : F.fibrePullbackNeighborhood B' b y × Circle) :
    F.fibrePullbackProjection B' b hinj (F.fibrePullbackPatch B' b hinj y q) = q.1.val :=
  F.fibrePullbackLocalInverse_projection B' b hinj y q

theorem fibrePullbackPatch_val (y : B'.Carrier)
    (q : F.fibrePullbackNeighborhood B' b y × Circle) :
    (F.fibrePullbackPatch B' b hinj y q).val =
      ((F.trivialization (b y)).symm (⟨b q.1.val, q.1.property⟩, q.2)).val := rfl

theorem fibrePullbackPatch_symm_fst (y : B'.Carrier) (x : FibrePullbackTotal F B' b)
    (hx : x ∈ (F.fibrePullbackPatch B' b hinj y).target) :
    ((F.fibrePullbackPatch B' b hinj y).symm x).1.val =
      F.fibrePullbackProjection B' b hinj x := by
  have he := F.fibrePullbackPatch_projection B' b hinj y
    ((F.fibrePullbackPatch B' b hinj y).symm x)
  rw [(F.fibrePullbackPatch B' b hinj y).right_inv hx] at he
  exact he.symm

variable (hsm : ContMDiff (SurfaceModel.model B'.kind) (SurfaceModel.model F.base.kind) ∞ b)

include hsm in
theorem fibrePullbackPatch_native_smooth (y : B'.Carrier) :
    ContMDiff ((SurfaceModel.model B'.kind).prod (𝓡 1)) C.model ∞
      (fun q : F.fibrePullbackNeighborhood B' b y × Circle =>
        (F.fibrePullbackPatch B' b hinj y q).val) := by
  have hb : ContMDiff ((SurfaceModel.model B'.kind).prod (𝓡 1))
      (SurfaceModel.model F.base.kind) ∞
      (fun q : F.fibrePullbackNeighborhood B' b y × Circle =>
        (⟨b q.1.val, q.1.property⟩ : F.neighborhood (b y))) :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp
      (hsm.comp (contMDiff_subtype_val.comp contMDiff_fst))
  exact contMDiff_subtype_val.comp
    ((F.trivialization (b y)).symm.contMDiff.comp (hb.prodMk contMDiff_snd))

private def fibrePullbackOldCoordinate (y : B'.Carrier) :
    PartialDiffeomorph C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      U (F.neighborhood (b y) × Circle) ∞ :=
  let x := (F.trivialization (b y)).symm (⟨b y, F.mem_neighborhood (b y)⟩, 1)
  let V := TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y))
  let inc := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model V ⟨x⟩
  inc.symm.trans (F.trivialization (b y)).toPartialDiffeomorph

private theorem fibrePullbackOldCoordinate_source (y : B'.Carrier) :
    (F.fibrePullbackOldCoordinate B' b y).source =
      TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y)) := by
  let x := (F.trivialization (b y)).symm (⟨b y, F.mem_neighborhood (b y)⟩, 1)
  let V := TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y))
  let inc := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model V ⟨x⟩
  ext z
  change (z ∈ inc.target ∧ inc.symm z ∈ univ) ↔ z ∈ V
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  simp only [mem_univ, and_true]
  rfl

private theorem fibrePullbackOldCoordinate_apply (y : B'.Carrier) (x : U)
    (hx : F.projection x ∈ F.neighborhood (b y)) :
    F.fibrePullbackOldCoordinate B' b y x = F.trivialization (b y) ⟨x, hx⟩ := by
  let z := (F.trivialization (b y)).symm (⟨b y, F.mem_neighborhood (b y)⟩, 1)
  change F.trivialization (b y)
    ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model
      (TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y))) ⟨z⟩).symm x) = _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply]
  exact hx

theorem fibrePullbackPatch_symm_snd (y : B'.Carrier) (x : FibrePullbackTotal F B' b)
    (hx : x ∈ (F.fibrePullbackPatch B' b hinj y).target)
    (ho : F.projection x.val ∈ F.neighborhood (b y)) :
    ((F.fibrePullbackPatch B' b hinj y).symm x).2 =
      (F.fibrePullbackOldCoordinate B' b y x.val).2 := by
  let q := (F.fibrePullbackPatch B' b hinj y).symm x
  have hv := congrArg (fun z : FibrePullbackTotal F B' b => z.val)
    ((F.fibrePullbackPatch B' b hinj y).right_inv hx)
  rw [F.fibrePullbackPatch_val] at hv
  have he : (F.trivialization (b y)).symm (⟨b q.1.val, q.1.property⟩, q.2) =
      (⟨x.val, ho⟩ : TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y))) :=
    Subtype.ext hv
  have ht := congrArg (fun z => (F.trivialization (b y) z).2) he
  rw [Diffeomorph.apply_symm_apply] at ht
  rw [F.fibrePullbackOldCoordinate_apply B' b y x.val ho]
  exact ht

include hsm in
theorem fibrePullbackPatch_compatible (y z : B'.Carrier) :
    ContMDiffOn ((SurfaceModel.model B'.kind).prod (𝓡 1))
      ((SurfaceModel.model B'.kind).prod (𝓡 1)) ∞
      ((F.fibrePullbackPatch B' b hinj y).trans
        (F.fibrePullbackPatch B' b hinj z).symm)
      ((F.fibrePullbackPatch B' b hinj y).trans
        (F.fibrePullbackPatch B' b hinj z).symm).source := by
  let e := F.fibrePullbackPatch B' b hinj y
  let d := F.fibrePullbackPatch B' b hinj z
  let T := e.trans d.symm
  let a := F.fibrePullbackOldCoordinate B' b z
  have hm (q : F.fibrePullbackNeighborhood B' b y × Circle) (hq : q ∈ T.source) :
      F.projection (e q).val ∈ F.neighborhood (b z) := by
    rw [← F.fibrePullbackProjection_square B' b hinj (e q)]
    have ht := hq.2
    change e q ∈ (F.fibrePullbackPatch B' b hinj z).target at ht
    rw [F.fibrePullbackPatch_target] at ht
    exact ht
  intro p hp
  have ha : (e p).val ∈ a.source := by
    rw [F.fibrePullbackOldCoordinate_source]
    exact hm p hp
  have hs : ContMDiffAt ((SurfaceModel.model B'.kind).prod (𝓡 1))
      ((SurfaceModel.model F.base.kind).prod (𝓡 1)) ∞
      (fun q : F.fibrePullbackNeighborhood B' b y × Circle => a (e q).val) p :=
    (a.contMDiffOn.contMDiffAt (a.open_source.mem_nhds ha)).comp p
      (F.fibrePullbackPatch_native_smooth B' b hinj hsm y p)
  have hfirst : ContMDiffAt ((SurfaceModel.model B'.kind).prod (𝓡 1))
      (SurfaceModel.model B'.kind) ∞ (fun q => (T q).1) p := by
    apply (ContMDiffAt.subtypeVal_comp_iff _ _ p).mp
    apply (contMDiff_subtype_val.comp contMDiff_fst p).congr_of_eventuallyEq
    filter_upwards [T.open_source.mem_nhds hp] with q hq
    exact (F.fibrePullbackPatch_symm_fst B' b hinj z (e q) hq.2).trans
      (F.fibrePullbackPatch_projection B' b hinj y q)
  have hsecond : ContMDiffAt ((SurfaceModel.model B'.kind).prod (𝓡 1))
      (𝓡 1) ∞ (fun q => (T q).2) p := by
    apply hs.snd.congr_of_eventuallyEq
    filter_upwards [T.open_source.mem_nhds hp] with q hq
    exact F.fibrePullbackPatch_symm_snd B' b hinj z (e q) hq.2 (hm q hq)
  exact (hfirst.prodMk hsecond).contMDiffWithinAt

include hsm in
theorem exists_fibrePullbackAtlas :
    ∃ A : ChartedSpace ((fibreRestrictionKind B'.kind).Space) (FibrePullbackTotal F B' b), letI := A
      IsManifold ((fibreRestrictionKind B'.kind).model) ∞ (FibrePullbackTotal F B' b) ∧
      ∀ y : B'.Carrier,
        ContMDiffOn ((SurfaceModel.model B'.kind).prod (𝓡 1)) (fibreRestrictionKind B'.kind).model ∞
          (F.fibrePullbackPatch B' b hinj y) (F.fibrePullbackPatch B' b hinj y).source ∧
        ContMDiffOn (fibreRestrictionKind B'.kind).model ((SurfaceModel.model B'.kind).prod (𝓡 1)) ∞
          (F.fibrePullbackPatch B' b hinj y).symm (F.fibrePullbackPatch B' b hinj y).target := by
  refine exists_carrierSurgeryAtlas_of_openCover ((fibreRestrictionKind B'.kind).model)
    (F.fibrePullbackPatch B' b hinj) (F.fibrePullbackPatch_cover B' b hinj)
    (F.fibrePullbackPatch_compatible B' b hinj hsm) ?_
  intro y p hp
  let d : PartialDiffeomorph ((SurfaceModel.model B'.kind).prod (𝓡 1))
      ((SurfaceModel.model B'.kind).prod (𝓡 1))
      (F.fibrePullbackNeighborhood B' b y × Circle)
      (ModelProd (B'.kind.Space 2) (EuclideanSpace ℝ (Fin 1))) ∞ :=
    { __ := chartAt (ModelProd (B'.kind.Space 2) (EuclideanSpace ℝ (Fin 1))) p
      contMDiffOn_toFun := contMDiffOn_chart
        (I := (SurfaceModel.model B'.kind).prod (𝓡 1))
      contMDiffOn_invFun := contMDiffOn_chart_symm
        (I := (SurfaceModel.model B'.kind).prod (𝓡 1)) }
  exact ⟨d.trans (fibreRestrictionProductModelIso B'.kind).toPartialDiffeomorph,
    mem_chart_source _ p, mem_univ _⟩

@[instance_reducible]
def fibrePullbackChartedSpace :
    ChartedSpace (fibreRestrictionKind B'.kind).Space (FibrePullbackTotal F B' b) :=
  (F.exists_fibrePullbackAtlas B' b hinj hsm).choose

theorem fibrePullbackIsManifold :
    letI := F.fibrePullbackChartedSpace B' b hinj hsm
    IsManifold ((fibreRestrictionKind B'.kind).model) ∞ (FibrePullbackTotal F B' b) :=
  (F.exists_fibrePullbackAtlas B' b hinj hsm).choose_spec.1

private def fibrePullbackBaseMap (y : B'.Carrier) :
    F.fibrePullbackNeighborhood B' b y → F.neighborhood (b y) :=
  fun q => ⟨b q.val, q.property⟩

include hsm in
private theorem fibrePullbackBaseMap_smooth (y : B'.Carrier) :
    ContMDiff (SurfaceModel.model B'.kind) (SurfaceModel.model F.base.kind) ∞
      (F.fibrePullbackBaseMap B' b y) :=
  (ContMDiff.subtypeVal_comp_iff _ _).mp (hsm.comp contMDiff_subtype_val)

set_option backward.isDefEq.respectTransparency false in
private theorem fibrePullbackBaseMap_mfderiv (y : B'.Carrier)
    (q : F.fibrePullbackNeighborhood B' b y) :
    mfderiv (SurfaceModel.model B'.kind) (SurfaceModel.model F.base.kind)
      (F.fibrePullbackBaseMap B' b y) q =
      mfderiv (SurfaceModel.model B'.kind) (SurfaceModel.model F.base.kind) b q.val := by
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp]
  exact DifferentialGeometry.mfderiv_restrict_open b (F.fibrePullbackNeighborhood B' b y) q

variable (hbij : ∀ y, Bijective
  (mfderiv (SurfaceModel.model B'.kind) (SurfaceModel.model F.base.kind) b y))

set_option backward.isDefEq.respectTransparency false in
include hsm hbij in
theorem fibrePullbackPatch_native_mfderiv_bijective (y : B'.Carrier)
    (q : F.fibrePullbackNeighborhood B' b y × Circle) :
    Bijective (mfderiv ((SurfaceModel.model B'.kind).prod (𝓡 1)) C.model
      (fun p : F.fibrePullbackNeighborhood B' b y × Circle =>
        (F.fibrePullbackPatch B' b hinj y p).val) q) := by
  let f := Prod.map (F.fibrePullbackBaseMap B' b y) (id : Circle → Circle)
  let g := (F.trivialization (b y)).symm
  have hf : ContMDiff ((SurfaceModel.model B'.kind).prod (𝓡 1))
      ((SurfaceModel.model F.base.kind).prod (𝓡 1)) ∞ f :=
    (F.fibrePullbackBaseMap_smooth B' b hsm y).prodMap contMDiff_id
  have hd : Bijective (mfderiv ((SurfaceModel.model B'.kind).prod (𝓡 1))
      ((SurfaceModel.model F.base.kind).prod (𝓡 1)) f q) := by
    rw [mfderiv_prodMap
      ((F.fibrePullbackBaseMap_smooth B' b hsm y).mdifferentiable (by simp) q.1)
      (mdifferentiableAt_id : MDifferentiableAt (𝓡 1) (𝓡 1) id q.2),
      F.fibrePullbackBaseMap_mfderiv B' b y q.1, mfderiv_id]
    exact ((LinearEquiv.ofBijective
      (mfderiv (SurfaceModel.model B'.kind) (SurfaceModel.model F.base.kind) b q.1.val).toLinearMap
      (hbij q.1.val)).prodCongr
        (LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1)))).bijective
  have hg : Bijective (mfderiv ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model
      g (f q)) :=
    (g.mfderivToContinuousLinearEquiv (by simp) (f q)).bijective
  change Bijective (mfderiv _ _ (fun p => (g (f p)).val) q)
  rw [DifferentialGeometry.mfderiv_subtypeVal_comp]
  change Bijective (mfderiv ((SurfaceModel.model B'.kind).prod (𝓡 1)) C.model (g ∘ f) q)
  rw [mfderiv_comp q (g.contMDiff.mdifferentiable (by simp) (f q))
    (hf.mdifferentiable (by simp) q)]
  exact hg.comp hd

theorem fibrePullbackProjection_surjective :
    Surjective (F.fibrePullbackProjection B' b hinj) := by
  intro y
  exact ⟨F.fibrePullbackPatch B' b hinj y
    (⟨y, F.mem_fibrePullbackNeighborhood B' b y⟩, 1),
    F.fibrePullbackPatch_projection B' b hinj y _⟩

private theorem fibrePullbackProjection_fibre_connected (y : B'.Carrier) :
    IsConnected ((F.fibrePullbackProjection B' b hinj) ⁻¹' {y}) := by
  let f : Circle → FibrePullbackTotal F B' b := fun t =>
    F.fibrePullbackPatch B' b hinj y (⟨y, F.mem_fibrePullbackNeighborhood B' b y⟩, t)
  have hf : Continuous f :=
    (continuous_subtype_val.comp (F.fibrePullbackLocalHomeomorph B' b hinj y).continuous).comp
      (continuous_const.prodMk continuous_id)
  have hr : f '' univ = (F.fibrePullbackProjection B' b hinj) ⁻¹' {y} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact F.fibrePullbackPatch_projection B' b hinj y _
    · intro hx
      change F.fibrePullbackProjection B' b hinj x = y at hx
      have ht : x ∈ (F.fibrePullbackPatch B' b hinj y).target := by
        rw [F.fibrePullbackPatch_target]
        change F.fibrePullbackProjection B' b hinj x ∈ F.fibrePullbackNeighborhood B' b y
        rw [hx]
        exact F.mem_fibrePullbackNeighborhood B' b y
      let q := (F.fibrePullbackPatch B' b hinj y).symm x
      have hq : q.1 = (⟨y, F.mem_fibrePullbackNeighborhood B' b y⟩ :
          F.fibrePullbackNeighborhood B' b y) :=
        Subtype.ext ((F.fibrePullbackPatch_symm_fst B' b hinj y x ht).trans hx)
      refine ⟨q.2, mem_univ _, ?_⟩
      change F.fibrePullbackPatch B' b hinj y (_, q.2) = x
      rw [← hq]
      exact (F.fibrePullbackPatch B' b hinj y).right_inv ht
  rw [← hr]
  exact isConnected_univ.image f hf.continuousOn

include hinj in
theorem fibrePullbackConnected : ConnectedSpace (FibrePullbackTotal F B' b) := by
  have hp := (F.fibrePullbackProjection B' b hinj).continuous.isClosedMap.isQuotientMap
    (F.fibrePullbackProjection B' b hinj).continuous
    (F.fibrePullbackProjection_surjective B' b hinj)
  apply connectedSpace_iff_univ.mpr
  simpa only [preimage_univ] using
    hp.isCoinducing.isConnected_preimage_of_isClosed
      (F.fibrePullbackProjection_fibre_connected B' b hinj) isClosed_univ isConnected_univ

section Installed

variable [ChartedSpace (fibreRestrictionKind B'.kind).Space (FibrePullbackTotal F B' b)]
  [IsManifold (fibreRestrictionKind B'.kind).model ∞ (FibrePullbackTotal F B' b)]
  (hA : ∀ y : B'.Carrier,
    ContMDiffOn ((SurfaceModel.model B'.kind).prod (𝓡 1)) (fibreRestrictionKind B'.kind).model ∞
      (F.fibrePullbackPatch B' b hinj y) (F.fibrePullbackPatch B' b hinj y).source ∧
    ContMDiffOn (fibreRestrictionKind B'.kind).model ((SurfaceModel.model B'.kind).prod (𝓡 1)) ∞
      (F.fibrePullbackPatch B' b hinj y).symm (F.fibrePullbackPatch B' b hinj y).target)

def fibrePullbackPatchDiffeomorph (y : B'.Carrier) :
    PartialDiffeomorph ((SurfaceModel.model B'.kind).prod (𝓡 1))
      (fibreRestrictionKind B'.kind).model (F.fibrePullbackNeighborhood B' b y × Circle)
      (FibrePullbackTotal F B' b) ∞ where
  __ := F.fibrePullbackPatch B' b hinj y
  contMDiffOn_toFun := (hA y).1
  contMDiffOn_invFun := (hA y).2

omit [IsManifold (fibreRestrictionKind B'.kind).model ∞ (FibrePullbackTotal F B' b)] in
include hsm hinj hA in
theorem fibrePullbackInclusion_smooth :
    ContMDiff (fibreRestrictionKind B'.kind).model C.model ∞
      (F.fibrePullbackInclusion B' b) := by
  intro x
  obtain ⟨y, hx⟩ := F.fibrePullbackPatch_cover B' b hinj x
  let d := F.fibrePullbackPatchDiffeomorph B' b hinj hA y
  have hs : ContMDiffAt (fibreRestrictionKind B'.kind).model C.model ∞
      (fun z => (d (d.symm z)).val.val) x :=
    ((contMDiff_subtype_val.comp
      (F.fibrePullbackPatch_native_smooth B' b hinj hsm y)) (d.symm x)).comp x
      (d.symm.contMDiffOn.contMDiffAt (d.open_target.mem_nhds hx))
  apply hs.congr_of_eventuallyEq
  filter_upwards [d.open_target.mem_nhds hx] with z hz
  exact congrArg (fun q : FibrePullbackTotal F B' b => q.val.val) (d.right_inv hz).symm

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold (fibreRestrictionKind B'.kind).model ∞ (FibrePullbackTotal F B' b)] in
include hsm hbij hinj hA in
theorem fibrePullbackInclusion_mfderiv_bijective (x : FibrePullbackTotal F B' b) :
    Bijective (mfderiv (fibreRestrictionKind B'.kind).model C.model
      (F.fibrePullbackInclusion B' b) x) := by
  obtain ⟨y, hx⟩ := F.fibrePullbackPatch_cover B' b hinj x
  let d := F.fibrePullbackPatchDiffeomorph B' b hinj hA y
  let q := d.symm x
  have hq : q ∈ d.source := d.map_target hx
  have hn := F.fibrePullbackPatch_native_mfderiv_bijective B' b hinj hsm hbij y q
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp] at hn
  change Bijective (mfderiv _ _ ((F.fibrePullbackInclusion B' b) ∘ d) q) at hn
  rw [mfderiv_comp q
    ((F.fibrePullbackInclusion_smooth B' b hinj hsm hA).mdifferentiable (by simp) (d q))
    (d.mdifferentiableAt (by simp) hq)] at hn
  have he : d q = x := d.right_inv hx
  rw [he] at hn
  exact (Bijective.of_comp_iff _
    ((d.isLocalDiffeomorphAt _ _ ∞ hq).mfderivToContinuousLinearEquiv (by simp)).bijective).mp hn

omit [IsManifold (fibreRestrictionKind B'.kind).model ∞ (FibrePullbackTotal F B' b)] in
include hinj hA in
theorem fibrePullbackProjection_smooth :
    ContMDiff (fibreRestrictionKind B'.kind).model (SurfaceModel.model B'.kind) ∞
      (F.fibrePullbackProjection B' b hinj) := by
  intro x
  obtain ⟨y, hx⟩ := F.fibrePullbackPatch_cover B' b hinj x
  let d := F.fibrePullbackPatchDiffeomorph B' b hinj hA y
  have hs : ContMDiffAt (fibreRestrictionKind B'.kind).model (SurfaceModel.model B'.kind) ∞
      (fun z => (d.symm z).1.val) x :=
    (contMDiff_subtype_val.comp contMDiff_fst (d.symm x)).comp x
      (d.symm.contMDiffOn.contMDiffAt (d.open_target.mem_nhds hx))
  apply hs.congr_of_eventuallyEq
  filter_upwards [d.open_target.mem_nhds hx] with z hz
  exact (F.fibrePullbackPatch_symm_fst B' b hinj y z hz).symm

end Installed

@[instance_reducible]
def fibreRestrictionCarrier : CompactCarrier.{u} := by
  let := F.fibrePullbackChartedSpace B' b hinj hsm
  let := F.fibrePullbackIsManifold B' b hinj hsm
  let hA := (F.exists_fibrePullbackAtlas B' b hinj hsm).choose_spec.2
  exact
    { kind := fibreRestrictionKind B'.kind
      Carrier := FibrePullbackTotal F B' b
      orientation := DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback
        (fibreRestrictionKind B'.kind).model C.model (by simp)
        (F.fibrePullbackInclusion B' b)
        (F.fibrePullbackInclusion_smooth B' b hinj hsm hA)
        (F.fibrePullbackInclusion_mfderiv_bijective B' b hinj hsm hbij hA) C.orientation }

theorem fibreRestrictionCarrier_kind :
    (F.fibreRestrictionCarrier B' b hinj hsm hbij).kind = fibreRestrictionKind B'.kind := rfl

theorem fibreRestrictionCarrier_kind_withBoundary (hk : B'.kind = .withBoundary) :
    (F.fibreRestrictionCarrier B' b hinj hsm hbij).kind = .withBoundary := by
  change fibreRestrictionKind B'.kind = .withBoundary
  rw [hk]
  rfl

instance fibreRestrictionCarrier_connected :
    ConnectedSpace (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier :=
  F.fibrePullbackConnected B' b hinj

section Canonical

def fibreRestrictionPatch (y : B'.Carrier) :
    PartialDiffeomorph ((SurfaceModel.model B'.kind).prod (𝓡 1))
      (F.fibreRestrictionCarrier B' b hinj hsm hbij).model
      (F.fibrePullbackNeighborhood B' b y × Circle)
      (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier ∞ := by
  let := F.fibrePullbackChartedSpace B' b hinj hsm
  exact F.fibrePullbackPatchDiffeomorph B' b hinj
    (F.exists_fibrePullbackAtlas B' b hinj hsm).choose_spec.2 y

def fibreRestrictionProjection :
    C((⊤ : TopologicalSpace.Opens (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier),
      B'.Carrier) :=
  ⟨fun x => F.fibrePullbackProjection B' b hinj x.val,
    (F.fibrePullbackProjection B' b hinj).continuous.comp continuous_subtype_val⟩

theorem fibreRestrictionProjection_smooth :
    ContMDiff (F.fibreRestrictionCarrier B' b hinj hsm hbij).model
      (SurfaceModel.model B'.kind) ∞ (F.fibreRestrictionProjection B' b hinj hsm hbij) := by
  let := F.fibrePullbackChartedSpace B' b hinj hsm
  exact (F.fibrePullbackProjection_smooth B' b hinj
    (F.exists_fibrePullbackAtlas B' b hinj hsm).choose_spec.2).comp contMDiff_subtype_val

def fibreRestrictionTrivialization (y : B'.Carrier) :
    (TopologicalSpace.Opens.comap (F.fibreRestrictionProjection B' b hinj hsm hbij)
      (F.fibrePullbackNeighborhood B' b y))
      ≃ₘ⟮(F.fibreRestrictionCarrier B' b hinj hsm hbij).model,
        (SurfaceModel.model B'.kind).prod (𝓡 1)⟯
      (F.fibrePullbackNeighborhood B' b y × Circle) := by
  let d := F.fibreRestrictionPatch B' b hinj hsm hbij y
  have ht (x : TopologicalSpace.Opens.comap (F.fibreRestrictionProjection B' b hinj hsm hbij)
      (F.fibrePullbackNeighborhood B' b y)) : x.val.val ∈ d.target := by
    change x.val.val ∈ (F.fibrePullbackPatch B' b hinj y).target
    rw [F.fibrePullbackPatch_target]
    exact x.property
  refine
    { toFun := fun x => d.symm x.val.val
      invFun := fun q => ⟨⟨d q, mem_univ _⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · change F.fibrePullbackProjection B' b hinj (F.fibrePullbackPatch B' b hinj y q) ∈
      F.fibrePullbackNeighborhood B' b y
    rw [F.fibrePullbackPatch_projection]
    exact q.1.property
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    exact d.right_inv (ht x)
  · intro q
    exact d.left_inv (by
      change q ∈ (F.fibrePullbackPatch B' b hinj y).source
      rw [F.fibrePullbackPatch_source]
      exact mem_univ q)
  · intro x
    let V := TopologicalSpace.Opens.comap (F.fibreRestrictionProjection B' b hinj hsm hbij)
      (F.fibrePullbackNeighborhood B' b y)
    have hv : ContMDiff (F.fibreRestrictionCarrier B' b hinj hsm hbij).model
        (F.fibreRestrictionCarrier B' b hinj hsm hbij).model ∞
        (fun z : V => z.val.val) := contMDiff_subtype_val.comp contMDiff_subtype_val
    exact ContMDiffAt.comp
      (f := fun z : V => z.val.val)
      (g := fun z : (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier => d.symm z)
      x (d.symm.contMDiffOn.contMDiffAt (d.open_target.mem_nhds (ht x))) (hv x)
  · apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact d.contMDiffOn.comp_contMDiff contMDiff_id
      (fun q => by
        change q ∈ (F.fibrePullbackPatch B' b hinj y).source
        rw [F.fibrePullbackPatch_source]
        exact mem_univ q)

def fibreRestriction :
    CircleFibration (F.fibreRestrictionCarrier B' b hinj hsm hbij) ⊤ where
  base := B'
  projection := F.fibreRestrictionProjection B' b hinj hsm hbij
  surjective y := by
    obtain ⟨x, hx⟩ := F.fibrePullbackProjection_surjective B' b hinj y
    exact ⟨⟨x, mem_univ _⟩, hx⟩
  smooth := F.fibreRestrictionProjection_smooth B' b hinj hsm hbij
  neighborhood := F.fibrePullbackNeighborhood B' b
  mem_neighborhood := F.mem_fibrePullbackNeighborhood B' b
  trivialization := F.fibreRestrictionTrivialization B' b hinj hsm hbij
  projection_trivialization y x :=
    F.fibrePullbackPatch_symm_fst B' b hinj y x.val.val (by
      rw [F.fibrePullbackPatch_target]
      exact x.property)

theorem fibreRestriction_base : (F.fibreRestriction B' b hinj hsm hbij).base = B' := rfl

theorem fibreRestriction_projection_square
    (x : (⊤ : TopologicalSpace.Opens (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier)) :
    b ((F.fibreRestriction B' b hinj hsm hbij).projection x) = F.projection x.val.val :=
  F.fibrePullbackProjection_square B' b hinj x.val

theorem fibreRestrictionPatch_source (y : B'.Carrier) :
    (F.fibreRestrictionPatch B' b hinj hsm hbij y).source = univ :=
  F.fibrePullbackPatch_source B' b hinj y

theorem fibreRestrictionPatch_target (y : B'.Carrier) :
    (F.fibreRestrictionPatch B' b hinj hsm hbij y).target =
      F.fibrePullbackTotalOpen B' b hinj y :=
  F.fibrePullbackPatch_target B' b hinj y

theorem fibreRestrictionPatch_inclusion (y : B'.Carrier)
    (q : F.fibrePullbackNeighborhood B' b y × Circle) :
    F.fibrePullbackInclusion B' b (F.fibreRestrictionPatch B' b hinj hsm hbij y q) =
      ((F.trivialization (b y)).symm (⟨b q.1.val, q.1.property⟩, q.2)).val.val := rfl

def fibreRestrictionBaseProjection :
    C((F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier, B'.Carrier) :=
  F.fibrePullbackProjection B' b hinj

theorem fibreRestrictionBaseProjection_smooth :
    ContMDiff (F.fibreRestrictionCarrier B' b hinj hsm hbij).model
      (SurfaceModel.model B'.kind) ∞ (F.fibreRestrictionBaseProjection B' b hinj hsm hbij) := by
  let := F.fibrePullbackChartedSpace B' b hinj hsm
  exact F.fibrePullbackProjection_smooth B' b hinj
    (F.exists_fibrePullbackAtlas B' b hinj hsm).choose_spec.2

theorem fibreRestrictionPatch_symm_fibre (y : B'.Carrier)
    (x : (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier)
    (hx : x ∈ (F.fibreRestrictionPatch B' b hinj hsm hbij y).target)
    (ho : F.projection x.val ∈ F.neighborhood (b y)) :
    ((F.fibreRestrictionPatch B' b hinj hsm hbij y).symm x).2 =
      (F.trivialization (b y) ⟨x.val, ho⟩).2 := by
  exact (F.fibrePullbackPatch_symm_snd B' b hinj y x hx ho).trans
    (congrArg Prod.snd (F.fibrePullbackOldCoordinate_apply B' b y x.val ho))

def fibreRestrictionInclusion : C((F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier,
    C.Carrier) := F.fibrePullbackInclusion B' b

theorem fibreRestrictionInclusion_injective :
    Injective (F.fibreRestrictionInclusion B' b hinj hsm hbij) :=
  F.fibrePullbackInclusion_injective B' b

theorem fibreRestrictionInclusion_isClosedEmbedding :
    _root_.Topology.IsClosedEmbedding (F.fibreRestrictionInclusion B' b hinj hsm hbij) :=
  (F.fibreRestrictionInclusion B' b hinj hsm hbij).continuous.isClosedEmbedding
    (F.fibreRestrictionInclusion_injective B' b hinj hsm hbij)

theorem fibreRestrictionInclusion_range :
    range (F.fibreRestrictionInclusion B' b hinj hsm hbij) =
      Subtype.val '' {x : U | F.projection x ∈ range b} :=
  F.fibrePullbackInclusion_range B' b

theorem fibreRestrictionInclusion_smooth :
    ContMDiff (F.fibreRestrictionCarrier B' b hinj hsm hbij).model C.model ∞
      (F.fibreRestrictionInclusion B' b hinj hsm hbij) := by
  let := F.fibrePullbackChartedSpace B' b hinj hsm
  exact F.fibrePullbackInclusion_smooth B' b hinj hsm
    (F.exists_fibrePullbackAtlas B' b hinj hsm).choose_spec.2

theorem fibreRestrictionInclusion_mfderiv_bijective
    (x : (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier) :
    Bijective (mfderiv (F.fibreRestrictionCarrier B' b hinj hsm hbij).model C.model
      (F.fibreRestrictionInclusion B' b hinj hsm hbij) x) := by
  let := F.fibrePullbackChartedSpace B' b hinj hsm
  exact F.fibrePullbackInclusion_mfderiv_bijective B' b hinj hsm hbij
    (F.exists_fibrePullbackAtlas B' b hinj hsm).choose_spec.2 x

def fibreRestrictionInclusionTangentEquiv
    (x : (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier) :
    TangentSpace (F.fibreRestrictionCarrier B' b hinj hsm hbij).model x ≃ₗ[ℝ]
      TangentSpace C.model (F.fibreRestrictionInclusion B' b hinj hsm hbij x) :=
  (DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective
    (F.fibreRestrictionCarrier B' b hinj hsm hbij).model C.model
    (F.fibreRestrictionInclusion B' b hinj hsm hbij)
    (F.fibreRestrictionInclusion_mfderiv_bijective B' b hinj hsm hbij) x).toLinearEquiv

theorem fibreRestrictionInclusionTangentEquiv_apply
    (x : (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier)
    (v : TangentSpace (F.fibreRestrictionCarrier B' b hinj hsm hbij).model x) :
    F.fibreRestrictionInclusionTangentEquiv B' b hinj hsm hbij x v =
      mfderiv (F.fibreRestrictionCarrier B' b hinj hsm hbij).model C.model
        (F.fibreRestrictionInclusion B' b hinj hsm hbij) x v := rfl

theorem fibreRestrictionInclusion_positive
    (x : (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier) :
    Orientation.map (Fin 3) (F.fibreRestrictionInclusionTangentEquiv B' b hinj hsm hbij x)
      ((F.fibreRestrictionCarrier B' b hinj hsm hbij).orientation.orientation x) =
      C.orientation.orientation (F.fibreRestrictionInclusion B' b hinj hsm hbij x) := by
  let := F.fibrePullbackChartedSpace B' b hinj hsm
  let := F.fibrePullbackIsManifold B' b hinj hsm
  exact DifferentialGeometry.Topology.Manifold.orientation_map_manifoldOrientationPullback
    (fibreRestrictionKind B'.kind).model C.model (by simp)
    (F.fibrePullbackInclusion B' b)
    (F.fibrePullbackInclusion_smooth B' b hinj hsm
      (F.exists_fibrePullbackAtlas B' b hinj hsm).choose_spec.2)
    (F.fibrePullbackInclusion_mfderiv_bijective B' b hinj hsm hbij
      (F.exists_fibrePullbackAtlas B' b hinj hsm).choose_spec.2) C.orientation x

section Lifts

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
  (hb : IsSmoothEmbedding (SurfaceModel.model B'.kind) (SurfaceModel.model F.base.kind) ∞ b)
  (f : N → C.Carrier) (hf : ContMDiff I C.model ∞ f)
  (hU : ∀ x, f x ∈ U) (hr : ∀ x, F.projection ⟨f x, hU x⟩ ∈ range b)

def fibreRestrictionLift : N → (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier :=
  fun x => ⟨⟨f x, hU x⟩, hr x⟩

include hb hf in
theorem fibreRestrictionLift_smooth :
    ContMDiff I (F.fibreRestrictionCarrier B' b hinj hsm hbij).model ∞
      (F.fibreRestrictionLift B' b hinj hsm hbij f hU hr) := by
  let g : N → U := fun x => ⟨f x, hU x⟩
  let l : N → (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier :=
    fun x => ⟨g x, hr x⟩
  have hg : ContMDiff I C.model ∞ g := (ContMDiff.subtypeVal_comp_iff _ _).mp hf
  have hl : Continuous l := hg.continuous.subtype_mk hr
  have hpb : ContMDiff I (SurfaceModel.model F.base.kind) ∞ (F.projection ∘ g) :=
    F.smooth.comp hg
  have hrange : range (F.projection ∘ g) ⊆ range b := by
    rintro z ⟨x, rfl⟩
    exact hr x
  have hbase : ContMDiff I (SurfaceModel.model B'.kind) ∞
      (fun x => F.fibrePullbackProjection B' b hinj (l x)) := by
    apply (hb.contMDiff_lift hpb hrange).congr
    intro x
    apply hinj
    exact (F.fibrePullbackProjection_square B' b hinj (l x)).trans
      (hb.comp_lift hrange x).symm
  intro x
  let y := F.fibrePullbackProjection B' b hinj (l x)
  let d := F.fibreRestrictionPatch B' b hinj hsm hbij y
  let a := F.fibrePullbackOldCoordinate B' b y
  have ht : l x ∈ d.target := by
    rw [F.fibreRestrictionPatch_target]
    exact F.mem_fibrePullbackNeighborhood B' b y
  have ha : g x ∈ a.source := by
    rw [F.fibrePullbackOldCoordinate_source]
    change F.projection (l x).val ∈ F.neighborhood (b y)
    rw [← F.fibrePullbackProjection_square B' b hinj (l x)]
    exact F.mem_neighborhood (b y)
  have hfirst : ContMDiffAt I (SurfaceModel.model B'.kind) ∞
      (fun z => (d.symm (l z)).1) x := by
    apply (ContMDiffAt.subtypeVal_comp_iff _ _ x).mp
    apply (hbase x).congr_of_eventuallyEq
    filter_upwards [hl.continuousAt.preimage_mem_nhds (d.open_target.mem_nhds ht)] with z hz
    exact F.fibrePullbackPatch_symm_fst B' b hinj y (l z) hz
  have hsecond : ContMDiffAt I (𝓡 1) ∞ (fun z => (d.symm (l z)).2) x := by
    apply ((a.contMDiffOn.contMDiffAt (a.open_source.mem_nhds ha)).comp x (hg x)).snd
      |>.congr_of_eventuallyEq
    filter_upwards [hl.continuousAt.preimage_mem_nhds (d.open_target.mem_nhds ht)] with z hz
    have ho : F.projection (l z).val ∈ F.neighborhood (b y) := by
      rw [← F.fibrePullbackProjection_square B' b hinj (l z)]
      have hz' := hz
      rw [F.fibreRestrictionPatch_target] at hz'
      exact hz'
    exact F.fibrePullbackPatch_symm_snd B' b hinj y (l z) hz ho
  have hs := (d.contMDiffOn.contMDiffAt
    (d.open_source.mem_nhds (d.map_target ht))).comp x (hfirst.prodMk hsecond)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hl.continuousAt.preimage_mem_nhds (d.open_target.mem_nhds ht)] with z hz
  exact (d.right_inv hz).symm

end Lifts

end Canonical

end GC.GraphManifold.CircleFibration
