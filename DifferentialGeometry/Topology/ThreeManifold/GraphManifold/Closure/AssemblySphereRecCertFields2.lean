import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertFields1

/-!
# FC42 sphere recursion, packet S4 (group G5, first module): handle ends, arcs, loops

Lane ASM-SPH2b (review 40 §2.4 "third layer"). On the component `i` of the capped carrier:

* smooth embeddings restricted to an open subset of the codomain
  (`isSmoothEmbedding_codRestrict_opens`, through `subtypeRestr_mem_maximalAtlas_of_mem_maximalAtlas`);
* base points of the component circle region (`ccBaseOf`), with the projections of transported
  points (`ccCirc_proj_val`);
* the handle ends and faces `ccHandleEnd`, `ccHandleFace`, the arcs `ccArcFace`, `ccArcOwner`,
  `ccArcBase`, `ccArcDefining`, `ccArcAnnulus`, the loops `ccLoopFace`, `ccLoopOwner`, `ccLoopBase`,
  `ccLoopDefining`, the disk–arc incidence `ccHandleArc`, `ccArcEnd`;
* the corresponding certificate fields (`cc_<field>`), including the partition `face_partition` and
  the circle-region intersection `face_region_inter`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsF2_ASMSPH2b : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothF2_ASMSPH2b : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-! ## Smooth embeddings into an open subset -/

/-- A chart of the maximal atlas restricted to an open subset is in the maximal atlas of the
subset. -/
theorem subtypeRestr_mem_maximalAtlas_of_mem_maximalAtlas {H M : Type*} [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {G : StructureGroupoid H} [HasGroupoid M G]
    [ClosedUnderRestriction G] {e : OpenPartialHomeomorph M H} (he : e ∈ G.maximalAtlas M)
    {s : TopologicalSpace.Opens M} (hs : Nonempty s) : e.subtypeRestr hs ∈ G.maximalAtlas s := by
  intro e' he'
  obtain ⟨x, this⟩ := TopologicalSpace.Opens.chart_eq hs he'
  rw [this]
  exact ⟨G.mem_of_eqOnSource (closedUnderRestriction'
      (G.compatible_of_mem_maximalAtlas he (G.chart_mem_maximalAtlas (x : M)))
      (e.isOpen_inter_preimage_symm s.2)) (e.subtypeRestr_symm_trans_subtypeRestr hs _),
    G.mem_of_eqOnSource (closedUnderRestriction'
      (G.compatible_of_mem_maximalAtlas (G.chart_mem_maximalAtlas (x : M)) he)
      ((chartAt H (x : M)).isOpen_inter_preimage_symm s.2))
      ((chartAt H (x : M)).subtypeRestr_symm_trans_subtypeRestr hs e)⟩

/-- **A smooth embedding with range in an open subset is a smooth embedding into the subset.** -/
theorem isSmoothEmbedding_codRestrict_opens {E F H G M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace G N] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [IsManifold J ∞ N] {f : M → N} (hf : IsSmoothEmbedding I J ∞ f)
    (U : TopologicalSpace.Opens N) (hU : ∀ x, f x ∈ U) :
    IsSmoothEmbedding I J ∞ (fun x => (⟨f x, hU x⟩ : U)) := by
  refine ⟨?_, hf.isEmbedding.codRestrict _ hU⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  refine ⟨C, hC, hC', fun x => ?_⟩
  let h := hImm x
  have hne : Nonempty U := ⟨⟨f x, hU x⟩⟩
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    ((hf.isEmbedding.continuous.subtype_mk hU).continuousAt) h.equiv h.domChart
    (h.codChart.subtypeRestr hne) h.mem_domChart_source ?_ h.domChart_mem_maximalAtlas ?_ ?_
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact h.mem_codChart_source
  · exact subtypeRestr_mem_maximalAtlas_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hne
  · intro z hz
    exact h.writtenInCharts hz

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

/-! ## Base points of the component circle region -/

/-- A base point of the component circle region: a base point avoiding the cut seam whose fibre
has a transported point in the component. -/
def ccBaseOf (b : D.circ.Base) (hb : b ∈ D.seamAvoidingBase c)
    (hi : ∃ y : D.circ.domain, D.circ.proj y = b ∧ X.transport y.val ∈ DQ.piece i) :
    (D.ccCirc c X DQ i).Base :=
  ⟨⟨b, hb⟩, by
    obtain ⟨y, rfl, hy⟩ := hi
    obtain ⟨hb', -⟩ := ccCirc_proj (X := X) (DQ := DQ) (i := i) (x := ⟨_, hy⟩) hb rfl
    exact hb'⟩

variable {D c X DQ i}

theorem eq_ccBaseOf_iff {b : D.circ.Base} {hb : b ∈ D.seamAvoidingBase c}
    {hi : ∃ y : D.circ.domain, D.circ.proj y = b ∧ X.transport y.val ∈ DQ.piece i}
    {b' : (D.ccCirc c X DQ i).Base} : b' = D.ccBaseOf c X DQ i b hb hi ↔ b'.val.val = b := by
  constructor
  · rintro rfl
    rfl
  · intro h
    exact Subtype.ext (Subtype.ext h)

/-- The projection of a transported point of the component circle region. -/
theorem ccCirc_proj_val {y : D.circ.domain} (hb : D.circ.proj y ∈ D.seamAvoidingBase c)
    {x : (GC.Topology.componentCarrier X.Q DQ i).Carrier} (hx : x.val = X.transport y.val) :
    ∃ hxd : x ∈ (D.ccCirc c X DQ i).domain,
      ((D.ccCirc c X DQ i).proj ⟨x, hxd⟩).val.val = D.circ.proj y := by
  obtain ⟨hb', hxd, hp⟩ := ccCirc_proj (X := X) hb hx
  exact ⟨hxd, by rw [hp]⟩

/-- The two conditions of `ccBaseOf` for a base point whose fibre lies in a set off the seam
sphere, transported into the component. -/
theorem ccBase_conds {b : D.circ.Base} {A : Set W.Carrier}
    (hA : Subtype.val '' (D.circ.proj ⁻¹' {b}) ⊆ A) (hAS : A ⊆ (D.sphereSeam c).zeroSphereᶜ)
    (hAi : X.transport '' A ⊆ DQ.piece i) :
    b ∈ D.seamAvoidingBase c ∧
      ∃ y : D.circ.domain, D.circ.proj y = b ∧ X.transport y.val ∈ DQ.piece i := by
  refine ⟨fun x hx => hAS (hA ⟨x, hx, rfl⟩), ?_⟩
  obtain ⟨y, hy⟩ := D.circ.surjective_proj b
  exact ⟨y, hy, hAi ⟨_, hA ⟨y, hy, rfl⟩, rfl⟩⟩

theorem ccCirc_defining_apply (l : Fin (D.ccCirc c X DQ i).definingCount)
    (b : (D.ccCirc c X DQ i).Base) :
    (D.ccCirc c X DQ i).defining l b = D.circ.defining l b.val.val :=
  rfl

/-! ## Handle ends -/

theorem endDisk_ccHandle (h' : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    (D.ccHandle c X DQ i h').endDisk b =
      Subtype.val ⁻¹' (X.transport '' (D.handle (ccEquiv _ h').1).endDisk b) := by
  refine (EdgeHandle.endDisk_toComponent _ _ b).trans ?_
  exact congrArg (Subtype.val ⁻¹' ·)
    (range_comp X.transport (fun x : ClosedCell 2 => (D.handle (ccEquiv _ h').1).map (x, iccEnd b)))

theorem endDisk_subset_compl (h : Fin D.handleCount) (b : Bool) :
    (D.handle h).endDisk b ⊆ (D.sphereSeam c).zeroSphereᶜ := by
  rintro _ ⟨x, rfl⟩
  exact D.handle_subset_compl h ⟨_, rfl⟩

/-- The end vertex of a handle of the component is a vertex of the component. -/
theorem ccV_handleEnd {h : Fin D.handleCount} (hh : D.ccH c X DQ i h) (b : Bool) :
    D.ccV c X DQ i (D.handleEnd h b) := by
  let x₀ : ClosedCell 2 := ⟨0, by simp⟩
  have hy : (D.handle h).map (x₀, iccEnd b) ∈ D.face (D.handleFace h b) :=
    D.handleEnd_face h b ⟨x₀, rfl⟩
  rw [← D.handleFace_owner h b]
  exact ccV_of_transport_mem ((Vertex.boundaryImage_subset_image' _) (D.face_subset_boundaryImage _ hy))
    (D.handle_subset_compl h ⟨_, rfl⟩) (hh ⟨(x₀, iccEnd b), rfl⟩)

theorem ccF_handleFace {h : Fin D.handleCount} (hh : D.ccH c X DQ i h) (b : Bool) :
    D.ccF c X DQ i (D.handleFace h b) :=
  ⟨(fun b' h' => by rw [D.handleFace_kind] at h'; cases h'),
    (D.handleFace_owner h b).symm ▸ ccV_handleEnd hh b⟩

theorem ccA_handleArc {h : Fin D.handleCount} (hh : D.ccH c X DQ i h) (b : Bool) :
    D.ccA c X DQ i (D.handleArc h b) := by
  unfold ccA
  rw [D.handleArc_owner]
  exact ccF_handleFace hh b

variable (D c X DQ i)

/-- The end vertices of the handles of the component. -/
def ccHandleEnd (h' : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    Fin (Nat.card {k // D.ccV c X DQ i k}) :=
  (ccEquiv _).symm ⟨D.handleEnd (ccEquiv _ h').1 b, ccV_handleEnd (ccEquiv _ h').2 b⟩

/-- The end faces of the handles of the component. -/
def ccHandleFace (h' : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    Fin (Nat.card {f // D.ccF c X DQ i f}) :=
  (ccEquiv _).symm ⟨D.handleFace (ccEquiv _ h').1 b, ccF_handleFace (ccEquiv _ h').2 b⟩

/-- **Field `handleFace_owner`.** -/
theorem cc_handleFace_owner (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    D.ccFaceOwner c X DQ i (D.ccHandleFace c X DQ i h b) = D.ccHandleEnd c X DQ i h b := by
  rw [ccHandleFace, ccFaceOwner_symm, ccHandleEnd]
  congr 1
  exact Subtype.ext (D.handleFace_owner _ b)

/-- **Field `handleFace_kind`.** -/
theorem cc_handleFace_kind (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    D.ccFaceKind c X DQ i (D.ccHandleFace c X DQ i h b) = .partitioned := by
  rw [ccHandleFace, ccFaceKind_symm, D.handleFace_kind, ccKind_partitioned]

/-- **Field `handleEnd_face`.** -/
theorem cc_handleEnd_face (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    (D.ccHandle c X DQ i h).endDisk b ⊆ D.ccFace c X DQ i (D.ccHandleFace c X DQ i h b) := by
  rw [endDisk_ccHandle, ccHandleFace, ccFace_symm]
  exact preimage_mono (image_mono (D.handleEnd_face _ b))

/-- **Field `endDisk_disjoint`.** -/
theorem cc_endDisk_disjoint (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    (h' : Fin (Nat.card {h // D.ccH c X DQ i h})) (b' : Bool) (hne : (h, b) ≠ (h', b')) :
    Disjoint ((D.ccHandle c X DQ i h).endDisk b) ((D.ccHandle c X DQ i h').endDisk b') := by
  rw [endDisk_ccHandle, endDisk_ccHandle]
  refine (X.disjoint_transport_image (D.endDisk_subset_compl _ _) (D.endDisk_subset_compl _ _)
    (D.endDisk_disjoint _ _ _ _ fun he => hne ?_)).preimage _
  obtain ⟨h1, h2⟩ := Prod.mk.inj he
  rw [(ccEquiv _).injective (Subtype.ext h1), h2]

end DecompositionCertificate

/-! ## Arcs and loops -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {D : DecompositionCertificate W E}
  {c : Fin D.sphereSeamCount} {X : SphereCutCapped W (D.sphereSeam c) E} {DQ : X.Q.Components}
  {i : Fin DQ.count}

theorem arc_conds {j : Fin D.arcFaceCount} (hj : D.ccA c X DQ i j) (t : Icc (0 : ℝ) 1) :
    D.arcBase j t ∈ D.seamAvoidingBase c ∧
      ∃ y : D.circ.domain, D.circ.proj y = D.arcBase j t ∧ X.transport y.val ∈ DQ.piece i := by
  refine ccBase_conds (A := D.face (D.arcOwner j)) ?_ (D.face_subset_compl_zeroSphere c hj.1)
    (transport_face_subset hj)
  intro x hx
  refine D.arcFace_subset_face j ?_
  rw [D.arcFace_eq]
  exact image_mono (preimage_mono (singleton_subset_iff.mpr (mem_range_self t))) hx

theorem loop_conds {j : Fin D.loopFaceCount} (hj : D.ccL c X DQ i j) (z : Circle) :
    D.loopBase j z ∈ D.seamAvoidingBase c ∧
      ∃ y : D.circ.domain, D.circ.proj y = D.loopBase j z ∧ X.transport y.val ∈ DQ.piece i := by
  refine ccBase_conds (A := D.face (D.loopOwner j)) ?_ (D.face_subset_compl_zeroSphere c hj.1)
    (transport_face_subset hj)
  intro x hx
  refine D.loopFace_subset_face j ?_
  rw [D.loopFace_eq]
  exact image_mono (preimage_mono (singleton_subset_iff.mpr (mem_range_self z))) hx

theorem arcFace_subset_compl {j : Fin D.arcFaceCount} (hj : D.ccA c X DQ i j) :
    D.arcFace j ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  (D.arcFace_subset_face j).trans (D.face_subset_compl_zeroSphere c hj.1)

theorem loopFace_subset_compl {j : Fin D.loopFaceCount} (hj : D.ccL c X DQ i j) :
    D.loopFace j ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  (D.loopFace_subset_face j).trans (D.face_subset_compl_zeroSphere c hj.1)

theorem transport_arcFace_subset {j : Fin D.arcFaceCount} (hj : D.ccA c X DQ i j) :
    X.transport '' D.arcFace j ⊆ DQ.piece i :=
  (image_mono (D.arcFace_subset_face j)).trans (transport_face_subset hj)

theorem transport_loopFace_subset {j : Fin D.loopFaceCount} (hj : D.ccL c X DQ i j) :
    X.transport '' D.loopFace j ⊆ DQ.piece i :=
  (image_mono (D.loopFace_subset_face j)).trans (transport_face_subset hj)

/-- The handle at an end of an arc of the component is a handle of the component. -/
theorem ccH_arcEnd {j : Fin D.arcFaceCount} (hj : D.ccA c X DQ i j) (e : Bool) :
    D.ccH c X DQ i (D.arcEnd j e).1 := by
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 2)) (x := 0)
    (r := 1)).2 zero_le_one
  have hmem : D.arcAnnulus j (⟨v, hv⟩, iccEnd e) ∈
      (D.handle (D.arcEnd j e).1).endDisk (D.arcEnd j e).2 ∩ D.arcFace j := by
    rw [D.arcAnnulus_end]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨⟨x, hx⟩, hA⟩ := hmem
  refine ccH_of_mem (p := (x, iccEnd (D.arcEnd j e).2)) ?_
  have hx' : (D.handle (D.arcEnd j e).1).map (x, iccEnd (D.arcEnd j e).2) =
      D.arcAnnulus j (⟨v, hv⟩, iccEnd e) := hx
  change X.transport ((D.handle _).map _) ∈ DQ.piece i
  rw [hx']
  exact transport_arcFace_subset hj ⟨_, hA, rfl⟩

variable (D c X DQ i)

/-- The arcs of the component. -/
def ccArcFace (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    Set (GC.Topology.componentCarrier X.Q DQ i).Carrier :=
  Subtype.val ⁻¹' (X.transport '' D.arcFace (ccEquiv _ j).1)

/-- The owner faces of the arcs of the component. -/
def ccArcOwner (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    Fin (Nat.card {f // D.ccF c X DQ i f}) :=
  (ccEquiv _).symm ⟨D.arcOwner (ccEquiv _ j).1, (ccEquiv _ j).2⟩

/-- The interval bases of the arcs of the component. -/
def ccArcBase (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (t : Icc (0 : ℝ) 1) :
    (D.ccCirc c X DQ i).Base :=
  D.ccBaseOf c X DQ i (D.arcBase (ccEquiv _ j).1 t) (arc_conds (ccEquiv _ j).2 t).1
    (arc_conds (ccEquiv _ j).2 t).2

/-- The defining functions of the arcs of the component. -/
def ccArcDefining (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    Fin (D.ccCirc c X DQ i).definingCount :=
  D.arcDefining (ccEquiv _ j).1

/-- The annulus parametrizations of the arcs of the component. -/
def ccArcAnnulus (j : Fin (Nat.card {j // D.ccA c X DQ i j}))
    (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1) :
    (GC.Topology.componentCarrier X.Q DQ i).Carrier :=
  ⟨X.transport (D.arcAnnulus (ccEquiv _ j).1 q), transport_arcFace_subset (ccEquiv _ j).2
    ⟨_, by rw [← D.arcAnnulus_range]; exact ⟨q, rfl⟩, rfl⟩⟩

/-- The loops of the component. -/
def ccLoopFace (j : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    Set (GC.Topology.componentCarrier X.Q DQ i).Carrier :=
  Subtype.val ⁻¹' (X.transport '' D.loopFace (ccEquiv _ j).1)

/-- The owner faces of the loops of the component. -/
def ccLoopOwner (j : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    Fin (Nat.card {f // D.ccF c X DQ i f}) :=
  (ccEquiv _).symm ⟨D.loopOwner (ccEquiv _ j).1, (ccEquiv _ j).2⟩

/-- The circle bases of the loops of the component. -/
def ccLoopBase (j : Fin (Nat.card {j // D.ccL c X DQ i j})) (z : Circle) :
    (D.ccCirc c X DQ i).Base :=
  D.ccBaseOf c X DQ i (D.loopBase (ccEquiv _ j).1 z) (loop_conds (ccEquiv _ j).2 z).1
    (loop_conds (ccEquiv _ j).2 z).2

/-- The defining functions of the loops of the component. -/
def ccLoopDefining (j : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    Fin (D.ccCirc c X DQ i).definingCount :=
  D.loopDefining (ccEquiv _ j).1

/-! ### Arc fields -/

/-- **Field `arcOwner_kind`.** -/
theorem cc_arcOwner_kind (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    D.ccFaceKind c X DQ i (D.ccArcOwner c X DQ i j) = .partitioned := by
  refine (D.ccFaceKind_symm c X DQ i (ccEquiv _ j).2).trans ?_
  rw [D.arcOwner_kind, ccKind_partitioned]

/-- **Field `arcBase_embedding`.** -/
theorem cc_arcBase_embedding (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (D.ccArcBase c X DQ i j) :=
  isSmoothEmbedding_codRestrict_opens
    (isSmoothEmbedding_codRestrict_opens (D.arcBase_embedding (ccEquiv _ j).1) (D.seamAvoidingBase c)
      fun t => (arc_conds (ccEquiv _ j).2 t).1)
    ((D.liftCircleRegion c X).compBase DQ i) fun t => (D.ccArcBase c X DQ i j t).2

/-- **Field `arcFace_eq`.** -/
theorem cc_arcFace_eq (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    D.ccArcFace c X DQ i j =
      Subtype.val '' ((D.ccCirc c X DQ i).proj ⁻¹' range (D.ccArcBase c X DQ i j)) := by
  have hr : range (D.ccArcBase c X DQ i j) = {b | b.val.val ∈ range (D.arcBase (ccEquiv _ j).1)} := by
    ext b
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, (eq_ccBaseOf_iff.mpr ht.symm).symm⟩
  rw [hr, val_image_ccCirc_proj_preimage (by rintro _ ⟨t, rfl⟩; exact (arc_conds (ccEquiv _ j).2 t).1),
    ← D.arcFace_eq]
  rfl

/-- **Field `arcBase_defining`.** -/
theorem cc_arcBase_defining (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (t : Icc (0 : ℝ) 1) :
    (D.ccCirc c X DQ i).defining (D.ccArcDefining c X DQ i j) (D.ccArcBase c X DQ i j t) = 0 :=
  D.arcBase_defining _ t

/-- **Field `arcAnnulus_continuous`.** -/
theorem cc_arcAnnulus_continuous (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    Continuous (D.ccArcAnnulus c X DQ i j) :=
  (X.transport.contMDiffOn.continuousOn.comp_continuous (D.arcAnnulus_continuous _) fun q =>
    arcFace_subset_compl (ccEquiv _ j).2 (by rw [← D.arcAnnulus_range]; exact ⟨q, rfl⟩)).subtype_mk _

/-- **Field `arcAnnulus_injective`.** -/
theorem cc_arcAnnulus_injective (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    Injective (D.ccArcAnnulus c X DQ i j) := by
  intro q q' h
  have hS : ∀ q, D.arcAnnulus (ccEquiv _ j).1 q ∉ (D.sphereSeam c).zeroSphere := fun q =>
    arcFace_subset_compl (ccEquiv _ j).2 (by rw [← D.arcAnnulus_range]; exact ⟨q, rfl⟩)
  exact D.arcAnnulus_injective _ (X.injOn_transport (hS q) (hS q') (congrArg Subtype.val h))

/-- **Field `arcAnnulus_range`.** -/
theorem cc_arcAnnulus_range (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    range (D.ccArcAnnulus c X DQ i j) = D.ccArcFace c X DQ i j := by
  rw [range_eq_preimage_val (g₀ := X.transport ∘ D.arcAnnulus (ccEquiv _ j).1) fun q => rfl,
    range_comp, D.arcAnnulus_range]
  rfl

/-- **Field `arcAnnulus_proj`.** -/
theorem cc_arcAnnulus_proj (j : Fin (Nat.card {j // D.ccA c X DQ i j}))
    (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1) :
    ∃ hx : D.ccArcAnnulus c X DQ i j q ∈ (D.ccCirc c X DQ i).domain,
      (D.ccCirc c X DQ i).proj ⟨_, hx⟩ = D.ccArcBase c X DQ i j q.2 := by
  obtain ⟨hx0, hp⟩ := D.arcAnnulus_proj (ccEquiv _ j).1 q
  have hb : D.circ.proj ⟨_, hx0⟩ ∈ D.seamAvoidingBase c := by
    rw [hp]
    exact (arc_conds (ccEquiv _ j).2 q.2).1
  obtain ⟨hxd, hv⟩ := ccCirc_proj_val (X := X) (DQ := DQ) (i := i) hb
    (x := D.ccArcAnnulus c X DQ i j q) rfl
  exact ⟨hxd, eq_ccBaseOf_iff.mpr (hv.trans hp)⟩

/-! ### Loop fields -/

/-- **Field `loopOwner_kind`.** -/
theorem cc_loopOwner_kind (j : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    D.ccFaceKind c X DQ i (D.ccLoopOwner c X DQ i j) = .partitioned := by
  refine (D.ccFaceKind_symm c X DQ i (ccEquiv _ j).2).trans ?_
  rw [D.loopOwner_kind, ccKind_partitioned]

/-- **Field `loopBase_embedding`.** -/
theorem cc_loopBase_embedding (j : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D.ccLoopBase c X DQ i j) :=
  isSmoothEmbedding_codRestrict_opens
    (isSmoothEmbedding_codRestrict_opens (D.loopBase_embedding (ccEquiv _ j).1)
      (D.seamAvoidingBase c) fun z => (loop_conds (ccEquiv _ j).2 z).1)
    ((D.liftCircleRegion c X).compBase DQ i) fun z => (D.ccLoopBase c X DQ i j z).2

/-- **Field `loopFace_eq`.** -/
theorem cc_loopFace_eq (j : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    D.ccLoopFace c X DQ i j =
      Subtype.val '' ((D.ccCirc c X DQ i).proj ⁻¹' range (D.ccLoopBase c X DQ i j)) := by
  have hr : range (D.ccLoopBase c X DQ i j) =
      {b | b.val.val ∈ range (D.loopBase (ccEquiv _ j).1)} := by
    ext b
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, (eq_ccBaseOf_iff.mpr ht.symm).symm⟩
  rw [hr, val_image_ccCirc_proj_preimage (by rintro _ ⟨z, rfl⟩; exact (loop_conds (ccEquiv _ j).2 z).1),
    ← D.loopFace_eq]
  rfl

/-- **Field `loopBase_defining`.** -/
theorem cc_loopBase_defining (j : Fin (Nat.card {j // D.ccL c X DQ i j})) (z : Circle) :
    (D.ccCirc c X DQ i).defining (D.ccLoopDefining c X DQ i j) (D.ccLoopBase c X DQ i j z) = 0 :=
  D.loopBase_defining _ z

/-- **Field `loopFace_closed`.** -/
theorem cc_loopFace_closed (j : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    IsClosed (D.ccLoopFace c X DQ i j) := by
  have hK : IsCompact (X.transport '' D.loopFace (ccEquiv _ j).1) :=
    ((D.loopFace_closed _).isCompact).image_of_continuousOn
      (X.transport.contMDiffOn.continuousOn.mono (loopFace_subset_compl (ccEquiv _ j).2))
  exact hK.isClosed.preimage continuous_subtype_val

/-- **Field `loopFace_nonempty`.** -/
theorem cc_loopFace_nonempty (j : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    (D.ccLoopFace c X DQ i j).Nonempty := by
  obtain ⟨y, hy⟩ := D.loopFace_nonempty (ccEquiv _ j).1
  exact ⟨⟨_, transport_loopFace_subset (ccEquiv _ j).2 ⟨y, hy, rfl⟩⟩, ⟨y, hy, rfl⟩⟩

/-! ### Disjointness of arcs and loops -/

/-- **Field `arcFace_disjoint`.** -/
theorem cc_arcFace_disjoint : Pairwise fun j j' : Fin (Nat.card {j // D.ccA c X DQ i j}) =>
    Disjoint (D.ccArcFace c X DQ i j) (D.ccArcFace c X DQ i j') := by
  intro j j' hjj
  exact (X.disjoint_transport_image (arcFace_subset_compl (ccEquiv _ j).2)
    (arcFace_subset_compl (ccEquiv _ j').2) (D.arcFace_disjoint (ccEquiv_val_ne hjj))).preimage _

/-- **Field `loopFace_disjoint`.** -/
theorem cc_loopFace_disjoint : Pairwise fun j j' : Fin (Nat.card {j // D.ccL c X DQ i j}) =>
    Disjoint (D.ccLoopFace c X DQ i j) (D.ccLoopFace c X DQ i j') := by
  intro j j' hjj
  exact (X.disjoint_transport_image (loopFace_subset_compl (ccEquiv _ j).2)
    (loopFace_subset_compl (ccEquiv _ j').2) (D.loopFace_disjoint (ccEquiv_val_ne hjj))).preimage _

/-- **Field `arc_loop_disjoint`.** -/
theorem cc_arc_loop_disjoint (j : Fin (Nat.card {j // D.ccA c X DQ i j}))
    (j' : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    Disjoint (D.ccArcFace c X DQ i j) (D.ccLoopFace c X DQ i j') :=
  (X.disjoint_transport_image (arcFace_subset_compl (ccEquiv _ j).2)
    (loopFace_subset_compl (ccEquiv _ j').2) (D.arc_loop_disjoint _ _)).preimage _

end DecompositionCertificate

/-! ## Partition of the faces, disk–arc incidence -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

theorem iUnion_ccEndDisk (f : Fin (Nat.card {f // D.ccF c X DQ i f})) :
    (⋃ (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
        (_ : D.ccHandleFace c X DQ i h b = f), (D.ccHandle c X DQ i h).endDisk b) =
      Subtype.val ⁻¹' (X.transport '' ⋃ (h : Fin D.handleCount) (b : Bool)
        (_ : D.handleFace h b = (ccEquiv _ f).1), (D.handle h).endDisk b) := by
  ext x
  constructor
  · intro hx
    simp only [mem_iUnion] at hx
    obtain ⟨h, b, hf, hx⟩ := hx
    rw [endDisk_ccHandle] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨y, mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨ccEquiv_symm_eq_iff.mp hf, hy⟩⟩⟩,
      hyx⟩
  · rintro ⟨y, hy, hyx⟩
    simp only [mem_iUnion] at hy
    obtain ⟨h, b, hf, x₀, rfl⟩ := hy
    have hh : D.ccH c X DQ i h := by
      refine ccH_of_mem (p := (x₀, iccEnd b)) ?_
      change X.transport ((D.handle h).map (x₀, iccEnd b)) ∈ DQ.piece i
      rw [hyx]
      exact x.2
    refine mem_iUnion.mpr ⟨(ccEquiv _).symm ⟨h, hh⟩, mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩
    · rw [ccHandleFace, ccEquiv_symm_eq_iff, Equiv.apply_symm_apply]
      exact hf
    · rw [endDisk_ccHandle, Equiv.apply_symm_apply]
      exact ⟨_, ⟨x₀, rfl⟩, hyx⟩

theorem iUnion_ccArcFace (f : Fin (Nat.card {f // D.ccF c X DQ i f})) :
    (⋃ (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (_ : D.ccArcOwner c X DQ i j = f),
        D.ccArcFace c X DQ i j) =
      Subtype.val ⁻¹' (X.transport '' ⋃ (j : Fin D.arcFaceCount)
        (_ : D.arcOwner j = (ccEquiv _ f).1), D.arcFace j) := by
  ext x
  constructor
  · intro hx
    simp only [mem_iUnion] at hx
    obtain ⟨j, hf, y, hy, hyx⟩ := hx
    exact ⟨y, mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨ccEquiv_symm_eq_iff.mp hf, hy⟩⟩, hyx⟩
  · rintro ⟨y, hy, hyx⟩
    simp only [mem_iUnion] at hy
    obtain ⟨j, hf, hy⟩ := hy
    have hj : D.ccA c X DQ i j := by
      unfold ccA
      rw [hf]
      exact (ccEquiv _ f).2
    refine mem_iUnion.mpr ⟨(ccEquiv _).symm ⟨j, hj⟩, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · refine ccEquiv_symm_eq_iff.mpr ?_
      rw [Equiv.apply_symm_apply]
      exact hf
    · rw [ccArcFace, Equiv.apply_symm_apply]
      exact ⟨y, hy, hyx⟩

theorem iUnion_ccLoopFace (f : Fin (Nat.card {f // D.ccF c X DQ i f})) :
    (⋃ (j : Fin (Nat.card {j // D.ccL c X DQ i j})) (_ : D.ccLoopOwner c X DQ i j = f),
        D.ccLoopFace c X DQ i j) =
      Subtype.val ⁻¹' (X.transport '' ⋃ (j : Fin D.loopFaceCount)
        (_ : D.loopOwner j = (ccEquiv _ f).1), D.loopFace j) := by
  ext x
  constructor
  · intro hx
    simp only [mem_iUnion] at hx
    obtain ⟨j, hf, y, hy, hyx⟩ := hx
    exact ⟨y, mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨ccEquiv_symm_eq_iff.mp hf, hy⟩⟩, hyx⟩
  · rintro ⟨y, hy, hyx⟩
    simp only [mem_iUnion] at hy
    obtain ⟨j, hf, hy⟩ := hy
    have hj : D.ccL c X DQ i j := by
      unfold ccL
      rw [hf]
      exact (ccEquiv _ f).2
    refine mem_iUnion.mpr ⟨(ccEquiv _).symm ⟨j, hj⟩, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · refine ccEquiv_symm_eq_iff.mpr ?_
      rw [Equiv.apply_symm_apply]
      exact hf
    · rw [ccLoopFace, Equiv.apply_symm_apply]
      exact ⟨y, hy, hyx⟩

/-- **Field `face_partition`.** -/
theorem cc_face_partition (f : Fin (Nat.card {f // D.ccF c X DQ i f}))
    (hk : D.ccFaceKind c X DQ i f = .partitioned) :
    (⋃ (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
        (_ : D.ccHandleFace c X DQ i h b = f), (D.ccHandle c X DQ i h).endDisk b) ∪
      (⋃ (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (_ : D.ccArcOwner c X DQ i j = f),
        D.ccArcFace c X DQ i j) ∪
      (⋃ (j : Fin (Nat.card {j // D.ccL c X DQ i j})) (_ : D.ccLoopOwner c X DQ i j = f),
        D.ccLoopFace c X DQ i j) = D.ccFace c X DQ i f := by
  rw [iUnion_ccEndDisk, iUnion_ccArcFace, iUnion_ccLoopFace, ccFace,
    ← D.face_partition _ (eq_partitioned_of_ccKind (ccEquiv _ f).2 hk), image_union, image_union]
  rfl

/-- **Field `face_region_inter`.** -/
theorem cc_face_region_inter (f : Fin (Nat.card {f // D.ccF c X DQ i f}))
    (hk : D.ccFaceKind c X DQ i f = .partitioned) :
    D.ccFace c X DQ i f ∩ (D.ccCirc c X DQ i).region =
      (⋃ (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (_ : D.ccArcOwner c X DQ i j = f),
        D.ccArcFace c X DQ i j) ∪
      (⋃ (j : Fin (Nat.card {j // D.ccL c X DQ i j})) (_ : D.ccLoopOwner c X DQ i j = f),
        D.ccLoopFace c X DQ i j) := by
  have h := D.face_region_inter _ (eq_partitioned_of_ccKind (ccEquiv _ f).2 hk)
  have h2 := X.transport_image_inter (D.face_subset_compl_zeroSphere c (ccEquiv _ f).2.1)
    D.region_subset_compl
  rw [h, image_union] at h2
  rw [iUnion_ccArcFace, iUnion_ccLoopFace, ccFace, region_ccCirc]
  exact (congrArg (Subtype.val ⁻¹' · : Set X.Q.Carrier →
    Set (GC.Topology.componentCarrier X.Q DQ i).Carrier) h2).symm

/-- The arcs of the handle ends of the component. -/
def ccHandleArc (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    Fin (Nat.card {j // D.ccA c X DQ i j}) :=
  (ccEquiv _).symm ⟨D.handleArc (ccEquiv _ h).1 b, ccA_handleArc (ccEquiv _ h).2 b⟩

/-- The ends of the arcs of the component. -/
def ccArcEnd (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (e : Bool) :
    Fin (Nat.card {h // D.ccH c X DQ i h}) × Bool :=
  ((ccEquiv _).symm ⟨(D.arcEnd (ccEquiv _ j).1 e).1, ccH_arcEnd (ccEquiv _ j).2 e⟩,
    (D.arcEnd (ccEquiv _ j).1 e).2)

theorem ccEquiv_ccHandleArc (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    (ccEquiv _ (D.ccHandleArc c X DQ i h b)).1 = D.handleArc (ccEquiv _ h).1 b := by
  rw [ccHandleArc, Equiv.apply_symm_apply]

theorem ccEquiv_ccArcEnd_fst (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (e : Bool) :
    (ccEquiv _ (D.ccArcEnd c X DQ i j e).1).1 = (D.arcEnd (ccEquiv _ j).1 e).1 := by
  rw [ccArcEnd, Equiv.apply_symm_apply]

/-- **Field `handleArc_owner`.** -/
theorem cc_handleArc_owner (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    D.ccArcOwner c X DQ i (D.ccHandleArc c X DQ i h b) = D.ccHandleFace c X DQ i h b := by
  refine ccEquiv_symm_eq_iff.mpr ?_
  rw [ccHandleFace, Equiv.apply_symm_apply, ccEquiv_ccHandleArc, D.handleArc_owner]

/-- **Field `handleArc_meets`.** -/
theorem cc_handleArc_meets (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    (j : Fin (Nat.card {j // D.ccA c X DQ i j}))
    (hne : ((D.ccHandle c X DQ i h).endDisk b ∩ D.ccArcFace c X DQ i j).Nonempty) :
    D.ccHandleArc c X DQ i h b = j := by
  obtain ⟨x, hx1, hx2⟩ := hne
  rw [endDisk_ccHandle] at hx1
  obtain ⟨y, hy, hyx⟩ := hx1
  obtain ⟨y', hy', hy'x⟩ := hx2
  have hyy : y = y' := X.injOn_transport (D.endDisk_subset_compl _ _ hy)
    (arcFace_subset_compl (ccEquiv _ j).2 hy') (hyx.trans hy'x.symm)
  rw [ccHandleArc, ccEquiv_symm_eq_iff]
  exact D.handleArc_meets _ b _ ⟨y, hy, hyy ▸ hy'⟩

/-- **Field `endDisk_loop_disjoint`.** -/
theorem cc_endDisk_loop_disjoint (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    (j : Fin (Nat.card {j // D.ccL c X DQ i j})) :
    Disjoint ((D.ccHandle c X DQ i h).endDisk b) (D.ccLoopFace c X DQ i j) := by
  rw [endDisk_ccHandle]
  exact (X.disjoint_transport_image (D.endDisk_subset_compl _ _)
    (loopFace_subset_compl (ccEquiv _ j).2) (D.endDisk_loop_disjoint _ _ _)).preimage _

/-- **Field `endDisk_rim`.** -/
theorem cc_endDisk_rim (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    (fun x : ClosedCell 2 => (D.ccHandle c X DQ i h).map (x, iccEnd b)) '' diskRim =
      (D.ccHandle c X DQ i h).endDisk b ∩ D.ccArcFace c X DQ i (D.ccHandleArc c X DQ i h b) := by
  have h2 : (fun x : ClosedCell 2 => X.transport ((D.handle (ccEquiv _ h).1).map (x, iccEnd b))) ''
      diskRim = X.transport '' (D.handle (ccEquiv _ h).1).endDisk b ∩
        X.transport '' D.arcFace (D.handleArc (ccEquiv _ h).1 b) := by
    rw [← X.transport_image_inter (D.endDisk_subset_compl _ _)
      (arcFace_subset_compl (ccA_handleArc (ccEquiv _ h).2 b)), ← D.endDisk_rim, image_image]
  rw [image_eq_preimage_val (g₀ := fun x : ClosedCell 2 =>
      X.transport ((D.handle (ccEquiv _ h).1).map (x, iccEnd b))) (fun x => rfl),
    endDisk_ccHandle, ccArcFace, ccEquiv_ccHandleArc, h2]
  rfl

/-- **Field `arcEnd_arc`.** -/
theorem cc_arcEnd_arc (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (e : Bool) :
    D.ccHandleArc c X DQ i (D.ccArcEnd c X DQ i j e).1 (D.ccArcEnd c X DQ i j e).2 = j := by
  rw [ccHandleArc, ccEquiv_symm_eq_iff, ccEquiv_ccArcEnd_fst]
  exact D.arcEnd_arc _ e

/-- **Field `arcEnd_injective`.** -/
theorem cc_arcEnd_injective (j : Fin (Nat.card {j // D.ccA c X DQ i j})) :
    Injective (D.ccArcEnd c X DQ i j) := by
  intro e e' h
  apply D.arcEnd_injective (ccEquiv _ j).1
  have h1 := congrArg (fun p => (ccEquiv _ p.1).1) h
  have h2 := congrArg Prod.snd h
  simp only [ccEquiv_ccArcEnd_fst] at h1
  exact Prod.ext h1 h2

/-- **Field `arcEnd_surjective`.** -/
theorem cc_arcEnd_surjective (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    ∃ e, D.ccArcEnd c X DQ i (D.ccHandleArc c X DQ i h b) e = (h, b) := by
  obtain ⟨e, he⟩ := D.arcEnd_surjective (ccEquiv _ h).1 b
  refine ⟨e, Prod.ext ?_ ?_⟩
  · apply (ccEquiv _).injective
    apply Subtype.ext
    rw [ccEquiv_ccArcEnd_fst, ccEquiv_ccHandleArc, he]
  · change (D.arcEnd (ccEquiv _ (D.ccHandleArc c X DQ i h b)).1 e).2 = b
    rw [ccEquiv_ccHandleArc, he]

/-- **Field `arcAnnulus_end`.** -/
theorem cc_arcAnnulus_end (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (e : Bool) :
    (D.ccHandle c X DQ i (D.ccArcEnd c X DQ i j e).1).endDisk (D.ccArcEnd c X DQ i j e).2 ∩
        D.ccArcFace c X DQ i j =
      D.ccArcAnnulus c X DQ i j '' {q | q.2 = iccEnd e} := by
  have h2 : X.transport '' (D.handle (D.arcEnd (ccEquiv _ j).1 e).1).endDisk
      (D.arcEnd (ccEquiv _ j).1 e).2 ∩ X.transport '' D.arcFace (ccEquiv _ j).1 =
        (X.transport ∘ D.arcAnnulus (ccEquiv _ j).1) '' {q | q.2 = iccEnd e} := by
    rw [← X.transport_image_inter (D.endDisk_subset_compl _ _)
      (arcFace_subset_compl (ccEquiv _ j).2), D.arcAnnulus_end, image_comp]
  rw [endDisk_ccHandle, ccEquiv_ccArcEnd_fst, ccArcFace,
    image_eq_preimage_val (g₀ := X.transport ∘ D.arcAnnulus (ccEquiv _ j).1) (fun q => rfl), ← h2]
  rfl

end DecompositionCertificate

end GC.GraphManifold.Assembly
