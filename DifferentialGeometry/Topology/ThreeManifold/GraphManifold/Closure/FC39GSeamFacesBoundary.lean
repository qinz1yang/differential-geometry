import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFacesBase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormBadModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormRP3Pieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapProjectiveShell
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormSplitTools

/-!
# FC39 GROUP G, target `stub_exists_seams_faces` (lane FC39-G-SF): the faces of every vertex

Step G7 of the lane sheet (`build-logs/resume/sheet-FC39-G-SF.md`): for an ARBITRARY vertex
`v : Vertex W` the model boundary of `v.piece` has finitely many actual components, and the image of
each one in `W` is a two-sphere or a two-torus. Route:

* the kernel `faces_of_family_GSF` (pure topology): if a set `B` is the union of the ranges of a
  finite family of continuous injective maps of ONE compact connected space `S`, with pairwise
  disjoint ranges, then every actual component of `B` is one of the ranges (the ranges are closed,
  a component is preconnected), so there are finitely many, and the image of each under a continuous
  injective map into a Hausdorff space is homeomorphic to `S`;
* the boundary families of the vertex models: the ball (the unit sphere through the model
  diffeomorphism), the punctured `RP³` (the chart sphere `c (S²)`, `isBoundaryPoint_iff_mem_image_sphere`),
  `S² × I` (the two end spheres, `isBoundaryPoint_sphereIcc_iff`), the four torus-faced models
  (the raw presentations of `Vertex.rawPiece_of_torusFaced`: the external tori), and the two closed
  models (`ClosedZeroPiece.boundary_empty`, `overCircle … hclosed`: no face).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance ballChartsBoundary_GSF : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothBoundary_GSF : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

/-! ## The kernel -/

/-- **G7 kernel.** An actual component of a finite disjoint union of compact connected images is
one of the images. -/
theorem actualComponent_eq_range_GSF {X : Type*} [TopologicalSpace X] [T2Space X] {B : Set X}
    {ι : Type*} [Finite ι] {S : Type*} [TopologicalSpace S] [CompactSpace S] [ConnectedSpace S]
    (g : ι → S → X) (hg : ∀ i, Continuous (g i))
    (hdisj : Pairwise fun i j => Disjoint (range (g i)) (range (g j)))
    (hB : (⋃ i, range (g i)) = B) (C : ActualComponent B) : ∃ i, C.1 = range (g i) := by
  obtain ⟨x, hxB, hC⟩ := C.2
  have hxU : x ∈ ⋃ i, range (g i) := hB ▸ hxB
  obtain ⟨i, hxi⟩ := mem_iUnion.1 hxU
  refine ⟨i, ?_⟩
  rw [hC]
  have hsubB : range (g i) ⊆ B := hB ▸ subset_iUnion (fun j => range (g j)) i
  apply Subset.antisymm
  · let R : Set X := ⋃ (j : ι) (_ : j ≠ i), range (g j)
    have hAc : IsClosed (range (g i)) := (isCompact_range (hg i)).isClosed
    have hRc : IsClosed R := isClosed_iUnion_of_finite fun j =>
      isClosed_iUnion_of_finite fun _ => (isCompact_range (hg j)).isClosed
    have hcover : connectedComponentIn B x ⊆ range (g i) ∪ R := by
      intro y hy
      have hyU : y ∈ ⋃ j, range (g j) := hB ▸ connectedComponentIn_subset B x hy
      obtain ⟨j, hj⟩ := mem_iUnion.1 hyU
      by_cases hji : j = i
      · subst hji
        exact Or.inl hj
      · exact Or.inr (mem_iUnion₂.2 ⟨j, hji, hj⟩)
    have hdAR : Disjoint (range (g i)) R :=
      disjoint_iUnion_right.2 fun j => disjoint_iUnion_right.2 fun hji => hdisj (Ne.symm hji)
    have hpre := isPreconnected_connectedComponentIn (F := B) (x := x)
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hpre
    have hempty : connectedComponentIn B x ∩ (range (g i) ∩ R) = ∅ := by
      rw [hdAR.inter_eq, inter_empty]
    rcases hpre _ _ hAc hRc hcover hempty with h | h
    · exact h
    · exact (Set.disjoint_left.1 hdAR hxi (h (mem_connectedComponentIn hxB))).elim
  · exact (isConnected_range (hg i)).isPreconnected.subset_connectedComponentIn hxi hsubB

/-- **G7 kernel, consequences.** Finitely many actual components, each with image homeomorphic to
the common source `S` under a continuous injective map into a Hausdorff space. -/
theorem faces_of_family_GSF {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    [T2Space Y] {B : Set X} {ι : Type*} [Finite ι] {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [ConnectedSpace S] (g : ι → S → X) (hg : ∀ i, Continuous (g i))
    (hgi : ∀ i, Injective (g i)) (hdisj : Pairwise fun i j => Disjoint (range (g i)) (range (g j)))
    (hB : (⋃ i, range (g i)) = B) (φ : X → Y) (hφ : Continuous φ) (hφi : Injective φ) :
    Finite (ActualComponent B) ∧ ∀ C : ActualComponent B, Nonempty (φ '' C.1 ≃ₜ S) := by
  have hex := actualComponent_eq_range_GSF g hg hdisj hB
  refine ⟨?_, fun C => ?_⟩
  · refine Finite.of_injective (fun C => (hex C).choose) fun C C' h => Subtype.ext ?_
    rw [(hex C).choose_spec, (hex C').choose_spec]
    exact congrArg (fun i => range (g i)) h
  · obtain ⟨i, hi⟩ := hex C
    have hcont : Continuous (φ ∘ g i) := hφ.comp (hg i)
    have hinj : Injective (φ ∘ g i) := hφi.comp (hgi i)
    have heq : φ '' C.1 = range (φ ∘ g i) := by rw [hi, range_comp]
    exact ⟨(Homeomorph.setCongr heq).trans
      ((hcont.isClosedEmbedding hinj).isEmbedding.toHomeomorph).symm⟩

/-! ## The boundary families of the vertex models -/

/-- The unit sphere of `ℝ³` is connected. -/
theorem connectedSpace_sphereThree_GSF :
    ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  isConnected_iff_connectedSpace.mp (isConnected_sphere (by
    rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)

/-- The two closed models have no model boundary face. -/
theorem isEmpty_actualComponent_of_boundary_empty_GSF {X : Type*} [TopologicalSpace X]
    {B : Set X} (hB : B = ∅) : IsEmpty (ActualComponent B) := by
  refine ⟨fun C => ?_⟩
  obtain ⟨x, hx, -⟩ := C.2
  rw [hB] at hx
  exact hx

/-- **G7 for the ball model.** -/
theorem faces_ball_GSF {W : CompactCarrier.{u}} (P : PieceEmbedding W)
    (e : P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    Finite (ModelBoundaryFace P) ∧ ∀ m : ModelBoundaryFace P,
      Nonempty (P.map '' m.1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have _ := connectedSpace_sphereThree_GSF
  have hS : ∀ x : ClosedCell 3, (𝓡∂ 3).IsBoundaryPoint x ↔ ‖x.1‖ = 1 := fun x =>
    Set.ext_iff.mp (DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2) x
  have hbd : ∀ q : P.Piece, q ∈ (𝓡∂ 3).boundary P.Piece ↔ ‖(e q).1‖ = 1 := fun q =>
    ((e.isLocalDiffeomorph q).isBoundaryPoint_iff (by simp)).trans (hS (e q))
  let g : Unit → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → P.Piece := fun _ z =>
    e.symm ⟨z.1, le_of_eq (mem_sphere_zero_iff_norm.mp z.2)⟩
  refine faces_of_family_GSF g (fun _ => e.symm.continuous.comp (by fun_prop))
    (fun _ z z' h => by
      have h1 := e.symm.injective h
      exact Subtype.ext (congrArg (fun x : ClosedCell 3 => x.1) h1))
    (Subsingleton.pairwise) ?_ P.map P.continuous_map P.injective
  ext q
  simp only [mem_iUnion, mem_range]
  constructor
  · rintro ⟨-, z, rfl⟩
    rw [hbd, Diffeomorph.apply_symm_apply]
    exact mem_sphere_zero_iff_norm.mp z.2
  · intro hq
    refine ⟨(), ⟨(e q).1, mem_sphere_zero_iff_norm.mpr ((hbd q).mp hq)⟩, ?_⟩
    change e.symm ⟨(e q).1, _⟩ = q
    rw [show (⟨(e q).1, _⟩ : ClosedCell 3) = e q from rfl, Diffeomorph.symm_apply_apply]

/-- **G7 for the punctured `RP³` model.** -/
theorem faces_puncturedRP3_GSF {W : CompactCarrier.{u}} (P : PieceEmbedding W)
    (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
    (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier) (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}) :
    Finite (ModelBoundaryFace P) ∧ ∀ m : ModelBoundaryFace P,
      Nonempty (P.map '' m.1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have _ := connectedSpace_sphereThree_GSF
  have hc2 := c.closedBall_subset_source
  have hc1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ c.chart.source :=
    (Metric.closedBall_subset_closedBall (by norm_num)).trans hc2
  have hsph : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖(z : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    fun z => mem_sphere_zero_iff_norm.mp z.2
  have hmem : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, c.chart z ∈ range f := by
    intro z
    rw [hr]
    exact chart_not_mem_ball hc2 (hsph z).ge (by rw [hsph z]; norm_num)
  have hcont : Continuous fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      c.chart (z : EuclideanSpace ℝ (Fin 3)) :=
    c.chart.toOpenPartialHomeomorph.continuousOn.comp_continuous continuous_subtype_val fun z =>
      hc1 (Metric.sphere_subset_closedBall z.2)
  let g : Unit → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → P.Piece := fun _ z =>
    hf.isEmbedding.toHomeomorph.symm ⟨c.chart z, hmem z⟩
  have hfg : ∀ z, f (g () z) = c.chart z := fun z =>
    congrArg Subtype.val (hf.isEmbedding.toHomeomorph.apply_symm_apply ⟨c.chart z, hmem z⟩)
  refine faces_of_family_GSF g
    (fun _ => hf.isEmbedding.toHomeomorph.symm.continuous.comp (hcont.subtype_mk hmem))
    (fun _ z z' h => ?_) (Subsingleton.pairwise) ?_ P.map P.continuous_map P.injective
  · have h1 : c.chart z = c.chart z' := by rw [← hfg z, ← hfg z', h]
    exact Subtype.ext (chart_injOn hc2 (by rw [hsph z]; norm_num) (by rw [hsph z']; norm_num) h1)
  · ext q
    simp only [mem_iUnion, mem_range]
    have hbd := isBoundaryPoint_iff_mem_image_sphere c.chart hf hc1 hr (q := q)
    change _ ↔ (𝓡∂ 3).IsBoundaryPoint q
    rw [hbd]
    constructor
    · rintro ⟨-, z, rfl⟩
      exact ⟨z, z.2, (hfg z).symm⟩
    · rintro ⟨v, hv, hvq⟩
      refine ⟨(), ⟨v, hv⟩, hf.isEmbedding.injective ?_⟩
      rw [hfg]
      exact hvq

/-- **G7 for the `S² × I` model.** -/
theorem faces_sphereInterval_GSF {W : CompactCarrier.{u}} (P : PieceEmbedding W)
    (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece) :
    Finite (ModelBoundaryFace P) ∧ ∀ m : ModelBoundaryFace P,
      Nonempty (P.map '' m.1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have _ := connectedSpace_sphereThree_GSF
  let g : Bool → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → P.Piece := fun b z =>
    e (ULift.up z, iccEnd b)
  have hend : ∀ b b' : Bool, iccEnd b = iccEnd b' → b = b' := fun b b' h =>
    iccEnd_injective_GSAFE h
  refine faces_of_family_GSF g
    (fun b => e.continuous.comp ((continuous_uliftUp).prodMk continuous_const))
    (fun b z z' h => ULift.up_injective (congrArg Prod.fst (e.injective h)))
    (fun b b' hbb => Set.disjoint_left.2 ?_) ?_ P.map P.continuous_map P.injective
  · rintro _ ⟨z, rfl⟩ ⟨z', hz'⟩
    exact hbb (hend _ _ (congrArg Prod.snd (e.injective hz'))).symm
  · ext q
    simp only [mem_iUnion, mem_range]
    obtain ⟨p, rfl⟩ := e.surjective q
    have hbd : e p ∈ (𝓡∂ 3).boundary P.Piece ↔ p.2 = iccZero ∨ p.2 = iccOne :=
      ((e.isLocalDiffeomorph p).isBoundaryPoint_iff (by simp)).symm.trans
        isBoundaryPoint_sphereIcc_iff
    refine Iff.trans ?_ hbd.symm
    have h0 : iccEnd false = iccZero := Subtype.ext rfl
    have h1 : iccEnd true = iccOne := Subtype.ext rfl
    constructor
    · rintro ⟨b, z, hz⟩
      have hp := e.injective hz
      rw [← hp]
      cases b
      · exact Or.inl h0
      · exact Or.inr h1
    · intro hp
      refine ⟨decide (p.2 = iccOne), p.1.down, congrArg e (Prod.ext rfl ?_)⟩
      rcases hp with hp | hp
      · have hne : p.2 ≠ iccOne := by
          rw [hp]
          intro h
          have := congrArg Subtype.val h
          norm_num [iccZero, iccOne] at this
        rw [decide_eq_false hne, h0, hp]
      · rw [decide_eq_true hp, h1, hp]

/-- **G7 for the torus-faced models** (zero solid torus, zero twisted `I`-bundle, slim `T² × I`,
cusp core): through their raw presentations, the faces are the external tori. -/
theorem faces_torusFaced_GSF {W : CompactCarrier.{u}} (v : Vertex W)
    (hv : (∃ P e, v = .zero P (.solidTorus e)) ∨ (∃ P e, v = .zero P (.twistedIBundle e)) ∨
      (∃ P e, v = .slim P (.torusInterval e)) ∨ (∃ P e, v = .cuspCore P e)) :
    Finite (ModelBoundaryFace v.piece) ∧ ∀ m : ModelBoundaryFace v.piece,
      Nonempty (v.piece.map '' m.1 ≃ₜ Circle × Circle) := by
  obtain ⟨X, ⟨R⟩, ⟨ψ⟩⟩ := v.rawPiece_of_torusFaced hv
  have hpre := ψ.isLocalDiffeomorph.preimage_boundary (by simp)
  let g : Fin R.externalCount → Torus → v.piece.Piece := fun i t => ψ (R.external.torusMap i t)
  refine faces_of_family_GSF g
    (fun i => ψ.continuous.comp (R.external.torusMap_isEmbedding i).continuous)
    (fun i => ψ.injective.comp (R.external.torusMap_isEmbedding i).injective)
    (fun i j hij => Set.disjoint_left.2 ?_) ?_ v.piece.map v.piece.continuous_map v.piece.injective
  · rintro _ ⟨t, rfl⟩ ⟨s, hs⟩
    have h := ψ.injective hs
    exact Set.disjoint_left.mp (R.external.disjoint hij.symm)
      (PortRestriction.torusMap_mem_target R.external j s)
      (h ▸ PortRestriction.torusMap_mem_target R.external i t)
  · ext q
    simp only [mem_iUnion, mem_range]
    constructor
    · rintro ⟨i, t, rfl⟩
      have h : R.external.torusMap i t ∈ X.model.boundary X.Carrier := by
        rw [R.external_exhausted]
        exact mem_iUnion.mpr ⟨i, t, rfl⟩
      rw [← hpre] at h
      exact h
    · intro hq
      have hq' : ψ.symm q ∈ X.model.boundary X.Carrier := by
        have : ψ.symm q ∈ ψ ⁻¹' (𝓡∂ 3).boundary v.piece.Piece := by
          rw [mem_preimage, Diffeomorph.apply_symm_apply]
          exact hq
        rwa [hpre] at this
      rw [R.external_exhausted] at hq'
      obtain ⟨i, t, ht⟩ := mem_iUnion.mp hq'
      refine ⟨i, t, ?_⟩
      change ψ (R.external.torusMap i t) = q
      rw [ht, Diffeomorph.apply_symm_apply]

/-- **G7.** The model boundary of every vertex has finitely many actual components, each with
image a two-sphere or a two-torus. -/
theorem vertex_faces_GSF {W : CompactCarrier.{u}} (v : Vertex W) :
    Finite (ModelBoundaryFace v.piece) ∧ ∀ m : ModelBoundaryFace v.piece,
      Nonempty (v.piece.map '' m.1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
        Nonempty (v.piece.map '' m.1 ≃ₜ Circle × Circle) := by
  have hsph : ∀ {P : PieceEmbedding W}, (Finite (ModelBoundaryFace P) ∧ ∀ m : ModelBoundaryFace P,
      Nonempty (P.map '' m.1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) →
      Finite (ModelBoundaryFace P) ∧ ∀ m : ModelBoundaryFace P,
        Nonempty (P.map '' m.1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
          Nonempty (P.map '' m.1 ≃ₜ Circle × Circle) :=
    fun h => ⟨h.1, fun m => Or.inl (h.2 m)⟩
  have htor : (Finite (ModelBoundaryFace v.piece) ∧ ∀ m : ModelBoundaryFace v.piece,
      Nonempty (v.piece.map '' m.1 ≃ₜ Circle × Circle)) →
      Finite (ModelBoundaryFace v.piece) ∧ ∀ m : ModelBoundaryFace v.piece,
        Nonempty (v.piece.map '' m.1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
          Nonempty (v.piece.map '' m.1 ≃ₜ Circle × Circle) :=
    fun h => ⟨h.1, fun m => Or.inr (h.2 m)⟩
  have hempty : ∀ {P : PieceEmbedding W}, (𝓡∂ 3).boundary P.Piece = ∅ →
      Finite (ModelBoundaryFace P) ∧ ∀ m : ModelBoundaryFace P,
        Nonempty (P.map '' m.1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
          Nonempty (P.map '' m.1 ≃ₜ Circle × Circle) := by
    intro P hP
    have := isEmpty_actualComponent_of_boundary_empty_GSF hP
    exact ⟨inferInstance, fun m => isEmptyElim m⟩
  rcases hk : v with ⟨P, m⟩ | C | ⟨P, m⟩ | ⟨P, e⟩
  · rcases m with e | e | e | ⟨c, f, hf, hr⟩
    · exact hsph (faces_ball_GSF P e)
    · rw [← hk]
      exact htor (faces_torusFaced_GSF v (Or.inl ⟨P, e, hk⟩))
    · rw [← hk]
      exact htor (faces_torusFaced_GSF v (Or.inr (Or.inl ⟨P, e, hk⟩)))
    · exact hsph (faces_puncturedRP3_GSF P c f hf hr)
  · exact hempty C.boundary_empty
  · rcases m with e | e | ⟨p, hp, hsub, fib, hcl⟩
    · exact hsph (faces_sphereInterval_GSF P e)
    · rw [← hk]
      exact htor (faces_torusFaced_GSF v (Or.inr (Or.inr (Or.inl ⟨P, e, hk⟩))))
    · exact hempty hcl
  · rw [← hk]
    exact htor (faces_torusFaced_GSF v (Or.inr (Or.inr (Or.inr ⟨P, e, hk⟩))))

/-! ## The catalogue -/

instance finite_modelBoundaryFace_GSF {W : CompactCarrier.{u}} (v : Vertex W) :
    Finite (ModelBoundaryFace v.piece) :=
  (vertex_faces_GSF v).1

instance finite_catalogue_GSF {W : CompactCarrier.{u}} (V : VertexLayer W) :
    Finite (Catalogue_GSF V) :=
  inferInstance

/-- **The face model of a catalogue entry**: a two-sphere or a two-torus. -/
theorem catImage_model_GSF {W : CompactCarrier.{u}} {V : VertexLayer W} (p : Catalogue_GSF V) :
    Nonempty (catImage_GSF p ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
      Nonempty (catImage_GSF p ≃ₜ Circle × Circle) :=
  (vertex_faces_GSF (V.vertex p.1)).2 p.2

open Classical in
/-- The chosen face model of a catalogue entry. -/
def catModel_GSF {W : CompactCarrier.{u}} {V : VertexLayer W} (p : Catalogue_GSF V) :
    (catImage_GSF p ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ⊕
      (catImage_GSF p ≃ₜ Circle × Circle) :=
  if h : Nonempty (catImage_GSF p ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) then
    .inl h.some
  else .inr (Classical.choice ((catImage_model_GSF p).resolve_left h))

/-- The catalogue numbering. -/
def catEquiv_GSF {W : CompactCarrier.{u}} (V : VertexLayer W) :
    Fin (Nat.card (Catalogue_GSF V)) ≃ Catalogue_GSF V :=
  (Finite.equivFin _).symm

end GC.GraphManifold.Assembly.FC39P0
