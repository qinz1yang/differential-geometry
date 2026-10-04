import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreTube
import DifferentialGeometry.Topology.Manifold.PuncturedBoundaryAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.LocalMaps
import DifferentialGeometry.Topology.PuncturedConnected
import DifferentialGeometry.Topology.Manifold.HalfSpaceCenteredChart
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

/-!
Actual boundaryless bases of closed circle fibrations and excision in a fixed base chart.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.CircleFibration

variable {C : CompactCarrier.{u}}

private theorem closedCarrierBoundaryless (hc : C.kind = .closed) :
    BoundarylessManifold C.model C.Carrier := by
  cases C
  cases hc
  infer_instance

private theorem firstInterior {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (p : M × Circle)
    (hp : (I.prod (𝓡 1)).IsInteriorPoint p) : I.IsInteriorPoint p.1 := by
  have h : p ∈ (I.prod (𝓡 1)).interior (M × Circle) := hp
  rw [ModelWithCorners.interior_prod] at h
  exact h.1

private theorem basePointInterior (F : CircleFibration C ⊤)
    [BoundarylessManifold C.model C.Carrier] (b : F.base.Carrier) :
    (SurfaceModel.model F.base.kind).IsInteriorPoint b := by
  let V := F.neighborhood b
  let p : V × Circle := (⟨b, F.mem_neighborhood b⟩, 1)
  let d := F.trivialization b
  have hx : C.model.IsInteriorPoint (d.symm p) := BoundarylessManifold.isInteriorPoint
  have h := ((d.isLocalDiffeomorph (d.symm p)).isInteriorPoint_iff
    (by simp : (∞ : ℕ∞ω) ≠ 0)).mp hx
  rw [Diffeomorph.apply_symm_apply] at h
  have hb := firstInterior (SurfaceModel.model F.base.kind) p h
  exact (SurfaceModel.model F.base.kind).isInteriorPoint_iff_isInteriorPoint_val.mp hb

theorem base_boundary_eq_empty (F : CircleFibration C ⊤) (hc : C.kind = .closed) :
    (SurfaceModel.model F.base.kind).boundary F.base.Carrier = ∅ := by
  have := closedCarrierBoundaryless hc
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro b hb
  exact ((SurfaceModel.model F.base.kind).isInteriorPoint_iff_not_isBoundaryPoint b).mp
    (basePointInterior F b) hb

private theorem baseBoundaryless (F : CircleFibration C ⊤) (hc : C.kind = .closed) :
    BoundarylessManifold (SurfaceModel.model F.base.kind) F.base.Carrier := by
  have := closedCarrierBoundaryless hc
  exact ⟨basePointInterior F⟩

private abbrev closedBase (F : CircleFibration C ⊤) (hc : C.kind = .closed) :
    CompactSurface.{u} := by
  let hb := baseBoundaryless F hc
  let cs := @DifferentialGeometry.Manifold.interiorChartedSpace ℝ inferInstance
    (EuclideanSpace ℝ (Fin 2)) inferInstance inferInstance
    (SurfaceModel.Space F.base.kind) F.base.Carrier inferInstance inferInstance F.base.charts
    (SurfaceModel.model F.base.kind) ∞ F.base.smooth hb
  let hs := @DifferentialGeometry.Manifold.interiorIsManifold ℝ inferInstance
    (EuclideanSpace ℝ (Fin 2)) inferInstance inferInstance
    (SurfaceModel.Space F.base.kind) F.base.Carrier inferInstance inferInstance F.base.charts
    (SurfaceModel.model F.base.kind) ∞ F.base.smooth hb
  letI := cs
  letI : IsManifold (𝓡 2) ∞ F.base.Carrier := hs
  exact { kind := .closed, Carrier := F.base.Carrier }

private instance closedBaseCharts (F : CircleFibration C ⊤) (hc : C.kind = .closed) :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) (closedBase F hc).Carrier :=
  (closedBase F hc).charts

private instance closedBaseSmooth (F : CircleFibration C ⊤) (hc : C.kind = .closed) :
    IsManifold (𝓡 2) ∞ (closedBase F hc).Carrier := (closedBase F hc).smooth

private def closedBaseDiffeomorph (F : CircleFibration C ⊤) (hc : C.kind = .closed) :
    (closedBase F hc).Carrier ≃ₘ⟮𝓡 2, SurfaceModel.model F.base.kind⟯ F.base.Carrier where
  toEquiv := Equiv.refl F.base.Carrier
  contMDiff_toFun := @DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id
    ℝ inferInstance (EuclideanSpace ℝ (Fin 2)) inferInstance inferInstance
    (SurfaceModel.Space F.base.kind) F.base.Carrier inferInstance inferInstance F.base.charts
    (SurfaceModel.model F.base.kind) ∞ F.base.smooth (baseBoundaryless F hc)
  contMDiff_invFun := @DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas
    ℝ inferInstance (EuclideanSpace ℝ (Fin 2)) inferInstance inferInstance
    (SurfaceModel.Space F.base.kind) F.base.Carrier inferInstance inferInstance F.base.charts
    (SurfaceModel.model F.base.kind) ∞ F.base.smooth (baseBoundaryless F hc)

private def planeCoordinates :
    EuclideanSpace ℝ (Fin 2) ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℂ)⟯ PlaneLift.{u} :=
  Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.toDiffeomorph.trans
    (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ)

private theorem planeCoordinates_norm (z : EuclideanSpace ℝ (Fin 2)) :
    ‖(planeCoordinates.{u} z).down‖ = ‖z‖ :=
  Complex.orthonormalBasisOneI.repr.symm.norm_map z

private def excisionBallChart (F : CircleFibration C ⊤) (hc : C.kind = .closed)
    (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
      PlaneLift.{u} F.base.Carrier ∞)
    (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source) :
    BallChart 2 (𝓡 2) (closedBase F hc).Carrier where
  chart := (planeCoordinates.{u}.toPartialDiffeomorph.trans β).trans
    (closedBaseDiffeomorph F hc).symm.toPartialDiffeomorph
  closedBall_subset_source := by
    intro z hz
    change (z ∈ univ ∧ planeCoordinates.{u} z ∈ β.source) ∧
      β (planeCoordinates.{u} z) ∈ univ
    refine ⟨⟨mem_univ z, hβ ?_⟩, mem_univ (β (planeCoordinates.{u} z))⟩
    change ‖(planeCoordinates.{u} z).down‖ ≤ 3
    rw [planeCoordinates_norm.{u}]
    have h : ‖z‖ ≤ 2 := mem_closedBall_zero_iff.mp hz
    linarith

private theorem existsSinglePunctureAtlas {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    (c : BallChart 2 (𝓡 2) M) :
    ∃ A : SmoothBoundaryAtlas (𝓡 2) 2 (c.chart '' ball 0 1)ᶜ,
      ∀ x : ↥(c.chart '' ball 0 1)ᶜ,
        A.ambientChart x x.val 0 = 0 ↔ x.val ∈ c.chart '' sphere 0 1 := by
  let f : PUnit.{1} → BallChart 2 (𝓡 2) M := fun a => c
  have hd : Pairwise fun a b =>
      Disjoint ((f a).chart '' closedBall 0 2) ((f b).chart '' closedBall 0 2) := by
    intro a b hab
    exact False.elim (hab (Subsingleton.elim a b))
  have hU : (⋃ a : PUnit.{1}, (f a).chart '' ball 0 1) = c.chart '' ball 0 1 := by
    ext x
    simp only [f, mem_iUnion, exists_const]
  have hS : (⋃ a : PUnit.{1}, (f a).chart '' sphere 0 1) = c.chart '' sphere 0 1 := by
    ext x
    simp only [f, mem_iUnion, exists_const]
  have h := BallChart.exists_smoothBoundaryAtlas_ball_complement f hd
  rw [hU] at h
  simpa only [hS] using h

private def punctureAtlas {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    (c : BallChart 2 (𝓡 2) M) :
    SmoothBoundaryAtlas (𝓡 2) 2 (c.chart '' ball 0 1)ᶜ :=
  Classical.choose (existsSinglePunctureAtlas c)

private theorem punctureAtlas_boundary {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    (c : BallChart 2 (𝓡 2) M) (x : ↥(c.chart '' ball 0 1)ᶜ) :
    (punctureAtlas c).ambientChart x x.val 0 = 0 ↔ x.val ∈ c.chart '' sphere 0 1 :=
  Classical.choose_spec (existsSinglePunctureAtlas c) x

private abbrev puncturedSurface {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (c : BallChart 2 (𝓡 2) M) : CompactSurface.{u} := by
  let K := (c.chart '' ball 0 1)ᶜ
  have ho : IsOpen (c.chart '' ball 0 1) :=
    c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      c.ball_subset_source
  letI : CompactSpace K := isCompact_iff_compactSpace.mp ho.isClosed_compl.isCompact
  letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace
    (EuclideanSpace ℝ (Fin 2)) M
  have hr : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    exact Module.one_lt_rank_of_one_lt_finrank (by simp)
  have hcon := isPathConnected_compl_image_ball c.chart.toOpenPartialHomeomorph hr
    c.closedBall_one_subset_source
  letI : ConnectedSpace K := isConnected_iff_connectedSpace.mp hcon.isConnected
  letI := (punctureAtlas c).toChartedSpace
  letI := (punctureAtlas c).isManifold
  exact { kind := .withBoundary, Carrier := K }

private theorem planeCoordinates_symm_norm (z : PlaneLift.{u}) :
    ‖planeCoordinates.{u}.symm z‖ = ‖z.down‖ := by
  have h := planeCoordinates_norm.{u} (planeCoordinates.{u}.symm z)
  simpa only [Diffeomorph.apply_symm_apply] using h.symm

private def doubledPlane : PlaneLift.{u} ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ PlaneLift.{u} :=
  (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm.trans
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ)
      (Units.mk0 (2 : ℝ) (by norm_num))).toDiffeomorph).trans
        (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ))

private theorem doubledPlane_down (z : PlaneLift.{u}) :
    (doubledPlane z).down = (2 : ℝ) • z.down := rfl

private def collarAmbient {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (c : BallChart 2 (𝓡 2) M) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) (𝓡 2) PlaneLift.{u} M ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    ((doubledPlane.toPartialDiffeomorph.trans
      planeCoordinates.{u}.symm.toPartialDiffeomorph).trans c.chart)
    {z | ‖z.down‖ < 3 / 4}
    (isOpen_lt (continuous_norm.comp contMDiff_planeLift_down.continuous) continuous_const)

private theorem collarAmbient_source {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (c : BallChart 2 (𝓡 2) M) :
    (collarAmbient c).source = {z : PlaneLift.{u} | ‖z.down‖ < 3 / 4} := by
  ext z
  change (((z ∈ univ ∧ doubledPlane z ∈ univ) ∧
    planeCoordinates.{u}.symm (doubledPlane z) ∈ c.chart.source) ∧ ‖z.down‖ < 3 / 4) ↔ _
  constructor
  · exact And.right
  · intro hz
    refine ⟨⟨⟨mem_univ z, mem_univ (doubledPlane z)⟩, ?_⟩, hz⟩
    change ‖z.down‖ < 3 / 4 at hz
    apply c.closedBall_subset_source
    rw [mem_closedBall_zero_iff, planeCoordinates_symm_norm, doubledPlane_down,
      norm_smul, Real.norm_eq_abs]
    rw [show |(2 : ℝ)| = 2 by norm_num]
    linarith

private theorem collarAmbient_apply {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (c : BallChart 2 (𝓡 2) M) (z : PlaneLift.{u}) :
    collarAmbient c z = c.chart (planeCoordinates.{u}.symm (doubledPlane z)) := rfl

private theorem collarAmbient_membership {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (c : BallChart 2 (𝓡 2) M) (z : PlaneLift.{u}) (hz : z ∈ (collarAmbient c).source) :
    z ∈ planarSet 2 ↔ collarAmbient c z ∈ (c.chart '' ball 0 1)ᶜ := by
  have hzsmall := hz
  rw [collarAmbient_source c] at hzsmall
  change ‖z.down‖ < 3 / 4 at hzsmall
  let w := planeCoordinates.{u}.symm (doubledPlane z)
  have hn : ‖w‖ = 2 * ‖z.down‖ := by
    rw [planeCoordinates_symm_norm, doubledPlane_down, norm_smul, Real.norm_eq_abs]
    norm_num
  have hw : w ∈ c.chart.source := c.closedBall_subset_source
    (mem_closedBall_zero_iff.mpr (by rw [hn]; linarith))
  have he : collarAmbient c z = c.chart w := rfl
  have hnot : c.chart w ∈ (c.chart '' ball 0 1)ᶜ ↔ 1 ≤ ‖w‖ := by
    constructor
    · intro h
      by_contra hlt
      exact h ⟨w, mem_ball_zero_iff.mpr (lt_of_not_ge hlt), rfl⟩
    · intro h
      rintro ⟨v, hv, hvw⟩
      have hvw' := c.chart.injOn (c.ball_subset_source hv) hw hvw
      rw [hvw'] at hv
      exact (not_lt_of_ge h) (mem_ball_zero_iff.mp hv)
  rw [mem_planarSet_iff (Or.inl rfl), mem_planarModel_two, he, hnot, hn]
  constructor
  · intro h
    linarith [h.2]
  · intro h
    constructor <;> linarith

private def inverseCircle : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toEquiv := Equiv.inv Circle
  contMDiff_toFun := contMDiff_inv (𝓡 1) ∞
  contMDiff_invFun := contMDiff_inv (𝓡 1) ∞

private def inverseCircleCollar :
    (Circle × EuclideanHalfSpace 1) ≃ₘ⟮circleCollarModel, circleCollarModel⟯
      (Circle × EuclideanHalfSpace 1) :=
  inverseCircle.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)

private def annulusPoint : planarSet.{u} 2 :=
  planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (1, halfZero)

private def collarRestriction {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (c : BallChart 2 (𝓡 2) M) :
    let _ := (punctureAtlas c).toChartedSpace
    PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) (planarSet.{u} 2)
      ↥(c.chart '' ball 0 1)ᶜ ∞ := by
  let K := (c.chart '' ball 0 1)ᶜ
  let : Nonempty K := (puncturedSurface c).connected.toNonempty
  exact (planarAtlas 2).partialDiffeomorphOfAmbient (punctureAtlas c)
    (collarAmbient c) annulusPoint (Classical.ofNonempty) (collarAmbient_membership c)

private def punctureCollar {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (c : BallChart 2 (𝓡 2) M) :
    let _ := (punctureAtlas c).toChartedSpace
    PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      ↥(c.chart '' ball 0 1)ᶜ ∞ := by
  let _ := (punctureAtlas c).toChartedSpace
  exact (inverseCircleCollar.toPartialDiffeomorph.trans
    (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2))).trans (collarRestriction c)

private theorem invertedPlanarCollar_val (p : Circle × EuclideanHalfSpace 1)
    (hp : p ∈ circleCollarSource) :
    (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2)).val.down =
      (1 / 2 + p.2.val 0 / 4 : ℝ) • (p.1 : ℂ) := by
  have hi : (p.1⁻¹, p.2) ∈ circleCollarSource := hp
  rw [planarCollar_apply_val (Or.inl rfl) (1 : Fin 2) hi]
  change (0 : ℂ) + (1 / 2 + (1 : ℝ) * p.2.val 0 / 4) • (starRingEnd ℂ) (↑p.1⁻¹ : ℂ) = _
  rw [Circle.coe_inv_eq_conj, Complex.conj_conj]
  simp only [zero_add, one_mul]

private theorem punctureCollar_source {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (c : BallChart 2 (𝓡 2) M) :
    let _ := (punctureAtlas c).toChartedSpace
    (punctureCollar c).source = circleCollarSource := by
  let _ := (punctureAtlas c).toChartedSpace
  ext p
  change ((p ∈ univ ∧ (p.1⁻¹, p.2) ∈ circleCollarSource) ∧
    planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2) ∈
      (collarRestriction c).source) ↔ p ∈ circleCollarSource
  constructor
  · exact fun h => h.1.2
  · intro hp
    refine ⟨⟨mem_univ p, hp⟩, ?_⟩
    change (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2)).val ∈
      (collarAmbient c).source
    rw [collarAmbient_source]
    change ‖(planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2)).val.down‖ < 3 / 4
    rw [invertedPlanarCollar_val _ hp, norm_smul, Real.norm_eq_abs, Circle.norm_coe]
    have hn := p.2.property
    change p.2.val 0 < 1 at hp
    rw [abs_of_nonneg (by linarith : 0 ≤ (1 / 2 + p.2.val 0 / 4 : ℝ))]
    linarith

private theorem punctureCollar_val {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (c : BallChart 2 (𝓡 2) M) (p : Circle × EuclideanHalfSpace 1)
    (hp : p ∈ circleCollarSource) :
    let _ := (punctureAtlas c).toChartedSpace
    (punctureCollar c p).val =
      c.chart (planeCoordinates.{u}.symm (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1 : ℂ)))) := by
  let _ := (punctureAtlas c).toChartedSpace
  have hs := punctureCollar_source c
  have hx : planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2) ∈
      (collarRestriction c).source := by
    have h : p ∈ (punctureCollar c).source := hs ▸ hp
    exact h.2
  change (collarRestriction c
    (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2))).val = _
  unfold collarRestriction
  rw [(planarAtlas 2).partialDiffeomorphOfAmbient_apply_val _ _ _ _ _ _ hx]
  rw [collarAmbient_apply]
  congr 2
  apply ULift.ext
  rw [doubledPlane_down, invertedPlanarCollar_val _ hp, smul_smul]
  congr 1
  ring

private theorem punctureCollar_boundary {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (c : BallChart 2 (𝓡 2) M) :
    let _ := (punctureAtlas c).toChartedSpace
    (𝓡∂ 2).boundary ↥(c.chart '' ball 0 1)ᶜ =
      range (fun t : Circle => punctureCollar c (t, halfZero)) := by
  let _ := (punctureAtlas c).toChartedSpace
  ext x
  change (𝓡∂ 2).IsBoundaryPoint x ↔ _
  rw [(punctureAtlas c).isBoundaryPoint_iff, punctureAtlas_boundary]
  constructor
  · rintro ⟨v, hv, hcv⟩
    have hvn : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
    let t := unitOf (planeCoordinates.{u} v).down
    have ht : (t : ℂ) = (planeCoordinates.{u} v).down := by
      have he := norm_smul_unitOf (planeCoordinates.{u} v).down
      rw [planeCoordinates_norm, hvn, one_smul] at he
      exact he
    refine ⟨t, Subtype.ext ?_⟩
    rw [punctureCollar_val c _ (halfZero_mem_circleCollarSource t)]
    have hz : ULift.up ((1 + halfZero.val 0 / 2 : ℝ) • (t : ℂ)) =
        planeCoordinates.{u} v := by
      apply ULift.ext
      change (1 + 0 / 2 : ℝ) • (t : ℂ) = _
      simpa only [zero_div, add_zero, one_smul] using ht
    rw [hz, Diffeomorph.symm_apply_apply]
    exact hcv
  · rintro ⟨t, rfl⟩
    refine ⟨planeCoordinates.{u}.symm (ULift.up (t : ℂ)), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, planeCoordinates_symm_norm]
      exact Circle.norm_coe t
    · rw [punctureCollar_val c _ (halfZero_mem_circleCollarSource t)]
      congr 2
      apply ULift.ext
      change (t : ℂ) = (1 + 0 / 2 : ℝ) • (t : ℂ)
      simp only [zero_div, add_zero, one_smul]

private instance puncturedSurfaceCharts {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (c : BallChart 2 (𝓡 2) M) :
    ChartedSpace (EuclideanHalfSpace 2) (puncturedSurface c).Carrier :=
  (puncturedSurface c).charts

private instance puncturedSurfaceSmooth {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (c : BallChart 2 (𝓡 2) M) :
    IsManifold (𝓡∂ 2) ∞ (puncturedSurface c).Carrier := (puncturedSurface c).smooth

private def puncturedInclusion (F : CircleFibration C ⊤) (hc : C.kind = .closed)
    (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
      PlaneLift.{u} F.base.Carrier ∞)
    (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source) :
    C((puncturedSurface (excisionBallChart F hc β hβ)).Carrier, F.base.Carrier) :=
  ⟨(closedBaseDiffeomorph F hc) ∘ Subtype.val,
    (closedBaseDiffeomorph F hc).continuous.comp continuous_subtype_val⟩

private theorem excisionBallChart_image (F : CircleFibration C ⊤) (hc : C.kind = .closed)
    (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
      PlaneLift.{u} F.base.Carrier ∞)
    (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source) :
    (excisionBallChart F hc β hβ).chart '' ball 0 1 =
      β '' {z : PlaneLift.{u} | ‖z.down‖ < 1} := by
  ext x
  constructor
  · rintro ⟨v, hv, hvx⟩
    refine ⟨planeCoordinates.{u} v, ?_, hvx⟩
    change ‖(planeCoordinates.{u} v).down‖ < 1
    rw [planeCoordinates_norm]
    exact mem_ball_zero_iff.mp hv
  · rintro ⟨z, hz, hzx⟩
    refine ⟨planeCoordinates.{u}.symm z, ?_, ?_⟩
    · rw [mem_ball_zero_iff, planeCoordinates_symm_norm]
      exact hz
    · change β (planeCoordinates.{u} (planeCoordinates.{u}.symm z)) = x
      rwa [Diffeomorph.apply_symm_apply]

private theorem puncturedInclusion_range (F : CircleFibration C ⊤) (hc : C.kind = .closed)
    (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
      PlaneLift.{u} F.base.Carrier ∞)
    (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source) :
    range (puncturedInclusion F hc β hβ) =
      (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1})ᶜ := by
  change range (Subtype.val : ↥((excisionBallChart F hc β hβ).chart '' ball 0 1)ᶜ →
    F.base.Carrier) = _
  rw [Subtype.range_coe, excisionBallChart_image]

private theorem puncturedInclusion_derivative (F : CircleFibration C ⊤)
    (hc : C.kind = .closed)
    (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
      PlaneLift.{u} F.base.Carrier ∞)
    (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source)
    (x : (puncturedSurface (excisionBallChart F hc β hβ)).Carrier) :
    Bijective (mfderiv (𝓡∂ 2) (SurfaceModel.model F.base.kind)
      (puncturedInclusion F hc β hβ) x) := by
  let c := excisionBallChart F hc β hβ
  let e := closedBaseDiffeomorph F hc
  have hi := (punctureAtlas c).contMDiff_subtype_val.mdifferentiable (by simp) x
  have he := e.contMDiff.mdifferentiable (by simp) x.val
  change Bijective (mfderiv (𝓡∂ 2) (SurfaceModel.model F.base.kind)
    (e ∘ Subtype.val) x)
  rw [mfderiv_comp x he hi]
  have hb : Bijective (mfderiv (𝓡 2) (SurfaceModel.model F.base.kind) e x.val) := by
    rw [← e.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (e.mfderivToContinuousLinearEquiv (by simp) x.val).bijective
  exact hb.comp ((punctureAtlas c).mfderiv_subtypeVal_bijective x)

private abbrev BaseE2 := EuclideanSpace ℝ (Fin 2)

private def halfTwoInterior :
    PartialDiffeomorph (𝓡 2) (𝓡∂ 2) BaseE2 (EuclideanHalfSpace 2) ∞ where
  toFun := (𝓡∂ 2).symm
  invFun := Subtype.val
  source := {v | 0 < v 0}
  target := {v | 0 < v.val 0}
  map_source' := by
    intro v hv
    change 0 < v 0 at hv
    have hr : v ∈ range (𝓡∂ 2) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact hv.le
    have he := (𝓡∂ 2).right_inv hr
    change ((𝓡∂ 2).symm v).val = v at he
    change 0 < ((𝓡∂ 2).symm v).val 0
    rwa [he]
  map_target' := fun v hv => hv
  left_inv' := by
    intro v hv
    change 0 < v 0 at hv
    apply (𝓡∂ 2).right_inv
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact hv.le
  right_inv' := fun v hv => (𝓡∂ 2).left_inv v
  open_source := isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
  open_target := isOpen_lt continuous_const
    ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
  contMDiffOn_toFun := (𝓡∂ 2).contMDiffOn_symm.mono fun v hv => by
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 < v 0 at hv
    exact hv.le
  contMDiffOn_invFun := (𝓡∂ 2).contMDiff.contMDiffOn

private theorem halfTwoInterior_val (v : BaseE2) (hv : 0 < v 0) :
    (halfTwoInterior v).val = v := by
  apply (𝓡∂ 2).right_inv
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact hv.le

private def baseTranslation (v : BaseE2) : BaseE2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ BaseE2 where
  toFun z := z + v
  invFun z := z - v
  left_inv z := by simp
  right_inv z := by simp
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

private def baseSwap : BaseE2 ≃L[ℝ] BaseE2 :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)).toContinuousLinearEquiv

private theorem baseSwap_zero (v : BaseE2) : baseSwap v 0 = v 1 := by
  simp [baseSwap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

private theorem punctureEmbedding_half
    {M N : Type u} [TopologicalSpace M] [ChartedSpace BaseE2 M] [IsManifold (𝓡 2) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 2) N]
    [IsManifold (𝓡∂ 2) ∞ N] {K : Set M}
    (A : SmoothBoundaryAtlas (𝓡 2) 2 K) (D : M ≃ₘ⟮𝓡 2, 𝓡∂ 2⟯ N) :
    let _ := A.toChartedSpace
    IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 2) ∞ (D ∘ (Subtype.val : K → M)) := by
  let _ := A.toChartedSpace
  let _ := A.isManifold
  refine ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1}) ?_,
    D.toHomeomorph.isEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal⟩
  intro x
  let a := A.ambientChart x
  let v : BaseE2 := WithLp.toLp 2 (fun i => if i = 1 then 1 - a x.val 1 else 0)
  have hv : v 0 = 0 := by simp [v]
  let d := EuclideanHalfSpace.tangentialShiftDiffeomorph 1 v hv
  let α₀ := (A.chart x).trans d.toHomeomorph.toOpenPartialHomeomorph
  let s : Set K := α₀.source ∩ α₀ ⁻¹' {y : EuclideanHalfSpace 2 | 0 < y.val 1}
  have hs : IsOpen s := α₀.isOpen_inter_preimage
    (isOpen_lt continuous_const ((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val))
  let α := α₀.restr s
  let c := (((D.symm.toPartialDiffeomorph.trans a).trans
    (baseTranslation v).toPartialDiffeomorph).trans
    baseSwap.toDiffeomorph.toPartialDiffeomorph).trans halfTwoInterior
  have hαsource : α.source = s := by
    rw [OpenPartialHomeomorph.restr_source' α₀ s hs, inter_eq_right]
    exact inter_subset_left
  have hxs : x ∈ s := by
    refine ⟨⟨A.mem_source x, mem_univ _⟩, ?_⟩
    change 0 < (A.chart x x).val 1 + v 1
    rw [show (A.chart x x).val = a x.val from
      OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ (A.mem_source x)]
    change 0 < a x.val 1 + (1 - a x.val 1)
    linarith
  have hαmax : α ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ K := by
    apply restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ 2)) ?_ hs
    apply α₀.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (d ∘ A.chart x) α₀.source
      exact d.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas x)).mono (fun y hy => hy.1))
    · change ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ ((A.chart x).symm ∘ d.symm) α₀.target
      exact (contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas x)).comp d.symm.contMDiff.contMDiffOn
        (fun y hy => hy.2)
  have hcmax : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ N :=
    c.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      c.contMDiffOn_toFun c.contMDiffOn_invFun
  have ha (y : K) (hy : y ∈ s) :
      (α₀ y).val = a y.val + v := by
    change (A.chart x y).val + v = a y.val + v
    exact congrArg (fun w : BaseE2 => w + v)
      (OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hy.1.1)
  have hc (y : K) (hy : y ∈ s) : D y.val ∈ c.source := by
    change (((D y.val ∈ univ ∧ D.symm (D y.val) ∈ a.source) ∧
      a (D.symm (D y.val)) ∈ univ) ∧
      baseTranslation v (a (D.symm (D y.val))) ∈ univ) ∧
      baseSwap (baseTranslation v (a (D.symm (D y.val)))) ∈ halfTwoInterior.source
    rw [Diffeomorph.symm_apply_apply]
    refine ⟨⟨⟨⟨mem_univ _, hy.1.1⟩, mem_univ _⟩, mem_univ _⟩, ?_⟩
    change 0 < baseSwap (a y.val + v) 0
    rw [baseSwap_zero, ← ha y hy]
    exact hy.2
  have hf (y : K) (hy : y ∈ s) :
      c.toOpenPartialHomeomorph.extend (𝓡∂ 2) (D y.val) =
        baseSwap ((α.extend (𝓡∂ 2)) y) := by
    change (halfTwoInterior
      (baseSwap (a (D.symm (D y.val)) + v))).val = baseSwap ((α₀ y).val)
    rw [Diffeomorph.symm_apply_apply, halfTwoInterior_val, ha y hy]
    rw [baseSwap_zero, ← ha y hy]
    exact hy.2
  refine IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ BaseE2 PUnit.{1}).trans baseSwap)
    α c.toOpenPartialHomeomorph (hαsource.symm ▸ hxs) (hc x hxs)
    hαmax hcmax (fun y hy => hc y (hαsource ▸ hy)) ?_
  intro w hw
  let y := (α.extend (𝓡∂ 2)).symm w
  have hy : y ∈ s := by
    have h := (α.extend (𝓡∂ 2)).map_target hw
    rwa [OpenPartialHomeomorph.extend_source, hαsource] at h
  change c.toOpenPartialHomeomorph.extend (𝓡∂ 2) (D y.val) = baseSwap w
  rw [hf y hy]
  exact congrArg baseSwap ((α.extend (𝓡∂ 2)).right_inv hw)

private theorem punctureEmbedding_surface
    {M : Type u} [TopologicalSpace M] [ChartedSpace BaseE2 M] [IsManifold (𝓡 2) ∞ M]
    (N : CompactSurface.{u}) {K : Set M} (A : SmoothBoundaryAtlas (𝓡 2) 2 K)
    (D : M ≃ₘ⟮𝓡 2, SurfaceModel.model N.kind⟯ N.Carrier) :
    let _ := A.toChartedSpace
    IsSmoothEmbedding (𝓡∂ 2) (SurfaceModel.model N.kind) ∞
      (D ∘ (Subtype.val : K → M)) := by
  let _ := A.toChartedSpace
  cases N with
  | mk N =>
    cases N with
    | mk k Y =>
      cases k
      · exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
          (𝓡∂ 2) (𝓡 2) Subtype.val A.isSmoothEmbedding_subtype_val D
      · exact punctureEmbedding_half A D

theorem exists_fibreBaseExcision_data (F : CircleFibration C ⊤)
    (hc : C.kind = .closed)
    (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
      PlaneLift.{u} F.base.Carrier ∞)
    (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source) :
    ∃ B : CompactSurface.{u}, ∃ b : C(B.Carrier, F.base.Carrier),
      ∃ γ : PartialDiffeomorph circleCollarModel (SurfaceModel.model B.kind)
        (Circle × EuclideanHalfSpace 1) B.Carrier ∞,
      B.kind = .withBoundary ∧
      range b = (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1})ᶜ ∧
      ContMDiff (SurfaceModel.model B.kind) (SurfaceModel.model F.base.kind) ∞ b ∧
      _root_.Topology.IsEmbedding b ∧
      (∀ x : B.Carrier, Bijective (mfderiv (SurfaceModel.model B.kind)
        (SurfaceModel.model F.base.kind) b x)) ∧
      γ.source = circleCollarSource ∧
      (∀ p ∈ circleCollarSource,
        b (γ p) = β (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1 : ℂ)))) ∧
      (SurfaceModel.model B.kind).boundary B.Carrier =
        range (fun t : Circle => γ (t, halfZero)) := by
  let c := excisionBallChart F hc β hβ
  let B := puncturedSurface c
  let b := puncturedInclusion F hc β hβ
  let γ := punctureCollar c
  refine ⟨B, b, γ, rfl, puncturedInclusion_range F hc β hβ, ?_, ?_,
    puncturedInclusion_derivative F hc β hβ, punctureCollar_source c, ?_,
    punctureCollar_boundary c⟩
  · exact (closedBaseDiffeomorph F hc).contMDiff.comp
      (punctureAtlas c).contMDiff_subtype_val
  · exact (closedBaseDiffeomorph F hc).toHomeomorph.isEmbedding.comp
      _root_.Topology.IsEmbedding.subtypeVal
  · intro p hp
    change closedBaseDiffeomorph F hc (punctureCollar c p).val = _
    rw [punctureCollar_val c p hp]
    change β (planeCoordinates.{u}
      (planeCoordinates.{u}.symm (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1 : ℂ))))) = _
    rw [Diffeomorph.apply_symm_apply]

theorem exists_fibreBaseExcision_of_source (F : CircleFibration C ⊤) (hc : C.kind = .closed)
    (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
      PlaneLift.{u} F.base.Carrier ∞)
    (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source) :
    ∃ B : CompactSurface.{u}, ∃ b : C(B.Carrier, F.base.Carrier),
      ∃ γ : PartialDiffeomorph circleCollarModel (SurfaceModel.model B.kind)
        (Circle × EuclideanHalfSpace 1) B.Carrier ∞,
      B.kind = .withBoundary ∧
      range b = (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1})ᶜ ∧
      IsSmoothEmbedding (SurfaceModel.model B.kind) (SurfaceModel.model F.base.kind) ∞ b ∧
      (∀ x : B.Carrier, Bijective (mfderiv (SurfaceModel.model B.kind)
        (SurfaceModel.model F.base.kind) b x)) ∧
      γ.source = circleCollarSource ∧
      (∀ p ∈ circleCollarSource,
        b (γ p) = β (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1 : ℂ)))) ∧
      (SurfaceModel.model B.kind).boundary B.Carrier =
        range (fun t : Circle => γ (t, halfZero)) := by
  let c := excisionBallChart F hc β hβ
  let B := puncturedSurface c
  let b := puncturedInclusion F hc β hβ
  let γ := punctureCollar c
  refine ⟨B, b, γ, rfl, puncturedInclusion_range F hc β hβ, ?_,
    puncturedInclusion_derivative F hc β hβ, punctureCollar_source c, ?_,
    punctureCollar_boundary c⟩
  · exact punctureEmbedding_surface F.base (punctureAtlas c) (closedBaseDiffeomorph F hc)
  · intro p hp
    change closedBaseDiffeomorph F hc (punctureCollar c p).val = _
    rw [punctureCollar_val c p hp]
    change β (planeCoordinates.{u}
      (planeCoordinates.{u}.symm (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1 : ℂ))))) = _
    rw [Diffeomorph.apply_symm_apply]

theorem exists_fibreBaseExcision (F : CircleFibration C ⊤) (hc : C.kind = .closed)
    (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
      PlaneLift.{u} F.base.Carrier ∞)
    (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source)
    (hβI : β.target ⊆ (SurfaceModel.model F.base.kind).interior F.base.Carrier) :
    ∃ B : CompactSurface.{u}, ∃ b : C(B.Carrier, F.base.Carrier),
      ∃ γ : PartialDiffeomorph circleCollarModel (SurfaceModel.model B.kind)
        (Circle × EuclideanHalfSpace 1) B.Carrier ∞,
      B.kind = .withBoundary ∧
      range b = (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1})ᶜ ∧
      IsSmoothEmbedding (SurfaceModel.model B.kind) (SurfaceModel.model F.base.kind) ∞ b ∧
      (∀ x : B.Carrier, Bijective (mfderiv (SurfaceModel.model B.kind)
        (SurfaceModel.model F.base.kind) b x)) ∧
      γ.source = circleCollarSource ∧
      (∀ p ∈ circleCollarSource,
        b (γ p) = β (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1 : ℂ)))) ∧
      (SurfaceModel.model B.kind).boundary B.Carrier =
        range (fun t : Circle => γ (t, halfZero)) := by
  exact (And.intro hβI (exists_fibreBaseExcision_of_source F hc β hβ)).2

end GC.GraphManifold.CircleFibration
