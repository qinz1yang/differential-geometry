import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertIndex
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertCircleApplications

/-!
# FC42 sphere recursion, packet S4 (group G4): the inherited data and the first fields

Lane ASM-SPH2b (review 40 §2.4 "third layer"). On the component `i` of the capped carrier (indices
of `AssemblySphereRecCertIndex`):

* the data: handles `ccHandle`, edge-circle pieces `ccEdgeCircle`, the circle region `ccCirc`
  (the lifted circle region restricted to the component), torus seams `ccTorusSeam` with sides
  `ccTorusSide`, the other sphere seams `ccSphereSeam` with sides `ccSphereSide`, the owners of the
  ports `ccExternalOwner`;
* base points of the component circle region (`ccCirc_proj`, `val_image_ccCirc_proj_preimage`);
* the certificate fields: `cover`, the nine disjointness clauses, `vertical_fibre`,
  `edgeCircle_vertical`, the torus and sphere seam sides, `external_owned`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsF1_ASMSPH2b : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothF1_ASMSPH2b : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-! ## Traces in the component -/

section Trace

variable {Q : CompactCarrier.{u}} {DQ : Q.Components} {i : Fin DQ.count}

theorem range_eq_preimage_val {α : Type*} {g : α → (GC.Topology.componentCarrier Q DQ i).Carrier}
    {g₀ : α → Q.Carrier} (h : ∀ a, (g a).val = g₀ a) :
    range g = Subtype.val ⁻¹' range g₀ := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (h a).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ((h a).trans ha)⟩

theorem disjoint_interior_preimage_val {P P' : Set Q.Carrier}
    (h : Disjoint (interior P) (interior P')) :
    Disjoint (interior (Subtype.val ⁻¹' P : Set (GC.Topology.componentCarrier Q DQ i).Carrier))
      (interior (Subtype.val ⁻¹' P' : Set (GC.Topology.componentCarrier Q DQ i).Carrier)) := by
  rw [interior_preimage_val, interior_preimage_val]
  exact h.preimage _

end Trace

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

/-! ## The inherited data -/

/-- The handles of the component. -/
def ccHandle (h' : Fin (Nat.card {h // D.ccH c X DQ i h})) :
    EdgeHandle (GC.Topology.componentCarrier X.Q DQ i) :=
  (D.liftHandle c X (ccEquiv _ h').1).toComponent (ccEquiv _ h').2

/-- The edge-circle pieces of the component. -/
def ccEdgeCircle (e' : Fin (Nat.card {e // D.ccE c X DQ i e})) :
    EdgeCirclePiece (GC.Topology.componentCarrier X.Q DQ i) :=
  (D.liftEdgeCircle c X (ccEquiv _ e').1).toComponent (ccEquiv _ e').2

/-- The circle region of the component. -/
def ccCirc : CircleRegion (GC.Topology.componentCarrier X.Q DQ i) :=
  (D.liftCircleRegion c X).toComponent DQ i

theorem liftTorusSeam_target (d : Fin D.torusSeamCount) :
    (D.liftTorusSeam c X d).collar.target = X.transport '' (D.torusSeam d).collar.target :=
  X.liftPartialDiffeomorph_target (D.torusSeam d).collar
    (D.subset_compl_zeroSphere_of_disjoint (D.sphere_torus_seam_disjoint c d).symm)

theorem liftOtherSphereSeam_target {c' : Fin D.sphereSeamCount} (hc : c' ≠ c) :
    (D.liftOtherSphereSeam c X hc).collar.target =
      X.transport '' (D.sphereSeam c').collar.target :=
  X.liftPartialDiffeomorph_target (D.sphereSeam c').collar
    (D.subset_compl_zeroSphere_of_disjoint (D.sphereSeam_disjoint hc))

/-- The torus seams of the component. -/
def ccTorusSeam (d' : Fin (Nat.card {d // D.ccT c X DQ i d})) :
    TorusSeam (GC.Topology.componentCarrier X.Q DQ i) :=
  (D.liftTorusSeam c X (ccEquiv _ d').1).toComponent
    (by rw [liftTorusSeam_target]; exact (ccEquiv _ d').2)

/-- The other sphere seams of the component. -/
def ccSphereSeam (c'' : Fin (Nat.card {c' // D.ccS c X DQ i c'})) :
    SphereSeam (GC.Topology.componentCarrier X.Q DQ i) :=
  (D.liftOtherSphereSeam c X (ccEquiv _ c'').2.1).toComponent
    (by rw [liftOtherSphereSeam_target]; exact (ccEquiv _ c'').2.2)

open Classical in
/-- The index in the component of an old vertex (`none` outside the component). -/
def ccVIdx (k : Fin D.vertexCount) : Option (Fin (Nat.card {k // D.ccV c X DQ i k})) :=
  if h : D.ccV c X DQ i k then some ((ccEquiv _).symm ⟨k, h⟩) else none

/-- The torus seam sides of the component. -/
def ccTorusSide (d' : Fin (Nat.card {d // D.ccT c X DQ i d})) (b : Bool) :
    Option (Fin (Nat.card {k // D.ccV c X DQ i k})) :=
  (D.torusSide (ccEquiv _ d').1 b).bind (D.ccVIdx c X DQ i)

variable {D c X DQ i}

/-- A side vertex of a sphere seam of the component is a vertex of the component. -/
theorem ccV_sphereSide {c' : Fin D.sphereSeamCount} (hc : D.ccS c X DQ i c') (b : Bool) :
    D.ccV c X DQ i (D.sphereSide c' b) := by
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  have hT := (D.sphereSeam c').zeroSphere_subset_target ⟨z₀, rfl⟩
  exact ccV_of_transport_mem (D.zeroSphere_subset_image c' b ⟨z₀, rfl⟩)
    (D.sphereTarget_subset_compl hc.1 hT) (hc.2 ⟨_, hT, rfl⟩)

/-- The owner of an external port of the component is a vertex of the component. -/
theorem ccV_externalOwner
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))) :
    D.ccV c X DQ i (D.externalOwner
      (Fin.cast X.hn (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1)) := by
  set ā := (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1
  let t : Torus := (1, 1)
  have hx : E.torusMap (Fin.cast X.hn ā) t ∈ (E.collar (Fin.cast X.hn ā)).target :=
    PortRestriction.torusMap_mem_target E _ t
  have hpiece : X.transport '' (E.collar (Fin.cast X.hn ā)).target ⊆ DQ.piece i := by
    rw [X.transport_image_externalTarget]
    have h := PortRestriction.target_subset_of_port X.capping.retained DQ i
      (PortRestriction.componentPortEquiv X.capping.retained DQ i a)
    simpa using h
  exact ccV_of_transport_mem (D.external_owned _ hx) (X.externalTarget_subset_compl _ hx)
    (hpiece ⟨_, hx, rfl⟩)

variable (D c X DQ i)

/-- The sphere seam sides of the component. -/
def ccSphereSide (c'' : Fin (Nat.card {c' // D.ccS c X DQ i c'})) (b : Bool) :
    Fin (Nat.card {k // D.ccV c X DQ i k}) :=
  (ccEquiv _).symm ⟨D.sphereSide (ccEquiv _ c'').1 b, ccV_sphereSide (ccEquiv _ c'').2 b⟩

/-- The owners of the ports of the component. -/
def ccExternalOwner
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))) :
    Fin (Nat.card {k // D.ccV c X DQ i k}) :=
  (ccEquiv _).symm ⟨_, ccV_externalOwner a⟩

variable {D c X DQ i}

/-! ## Shapes of the inherited objects -/

theorem range_ccHandle (h' : Fin (Nat.card {h // D.ccH c X DQ i h})) :
    range (D.ccHandle c X DQ i h').map =
      Subtype.val ⁻¹' (X.transport '' range (D.handle (ccEquiv _ h').1).map) := by
  refine (EdgeHandle.range_toComponent _ _).trans ?_
  rw [liftHandle, ← range_comp]
  rfl

theorem ccHandle_map_val (h' : Fin (Nat.card {h // D.ccH c X DQ i h}))
    (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    ((D.ccHandle c X DQ i h').map p).val = X.transport ((D.handle (ccEquiv _ h').1).map p) :=
  rfl

theorem range_ccEdgeCircle (e' : Fin (Nat.card {e // D.ccE c X DQ i e})) :
    range (D.ccEdgeCircle c X DQ i e').piece.map =
      Subtype.val ⁻¹' (X.transport '' range (D.edgeCircle (ccEquiv _ e').1).piece.map) := by
  refine (EdgeCirclePiece.range_toComponent _ _).trans ?_
  exact congrArg (Subtype.val ⁻¹' ·) (X.range_liftPieceAway _
    (D.subset_compl_zeroSphere_of_disjoint (D.edgeCircle_image_disjoint_sphereCollar c _)))

theorem region_ccCirc :
    (D.ccCirc c X DQ i).region = Subtype.val ⁻¹' (X.transport '' D.circ.region) :=
  D.region_toComponent_liftCircleRegion c X DQ i

theorem ccTorusSeam_collar_val (d' : Fin (Nat.card {d // D.ccT c X DQ i d}))
    {p : Torus × ℝ} (hp : p ∈ (D.torusSeam (ccEquiv _ d').1).collar.source) :
    ((D.ccTorusSeam c X DQ i d').collar p).val =
      X.transport ((D.torusSeam (ccEquiv _ d').1).collar p) := by
  refine (TorusSeam.toComponent_collar_val _ _ ?_).trans rfl
  rw [(D.liftTorusSeam c X (ccEquiv _ d').1).source_eq, ← (D.torusSeam _).source_eq]
  exact hp

theorem ccTorusSeam_target (d' : Fin (Nat.card {d // D.ccT c X DQ i d})) :
    (D.ccTorusSeam c X DQ i d').collar.target =
      Subtype.val ⁻¹' (X.transport '' (D.torusSeam (ccEquiv _ d').1).collar.target) := by
  refine (TorusSeam.toComponent_collar_target _ _).trans ?_
  rw [liftTorusSeam_target]

theorem ccSphereSeam_collar_val (c'' : Fin (Nat.card {c' // D.ccS c X DQ i c'}))
    {p : ClosureSphere.{u} × ℝ} (hp : p ∈ (D.sphereSeam (ccEquiv _ c'').1).collar.source) :
    ((D.ccSphereSeam c X DQ i c'').collar p).val =
      X.transport ((D.sphereSeam (ccEquiv _ c'').1).collar p) := by
  refine (SphereSeam.toComponent_collar_val _ _ ?_).trans rfl
  rw [(D.liftOtherSphereSeam c X _).source_eq, ← (D.sphereSeam _).source_eq]
  exact hp

theorem ccSphereSeam_target (c'' : Fin (Nat.card {c' // D.ccS c X DQ i c'})) :
    (D.ccSphereSeam c X DQ i c'').collar.target =
      Subtype.val ⁻¹' (X.transport '' (D.sphereSeam (ccEquiv _ c'').1).collar.target) := by
  refine (SphereSeam.toComponent_collar_target _ _).trans ?_
  rw [liftOtherSphereSeam_target]

end DecompositionCertificate

/-! ## Vertex indices, sides, and the circle base -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {D : DecompositionCertificate W E}
  {c : Fin D.sphereSeamCount} {X : SphereCutCapped W (D.sphereSeam c) E} {DQ : X.Q.Components}
  {i : Fin DQ.count}

theorem ccVIdx_eq_some_iff {k : Fin D.vertexCount} {k' : Fin (Nat.card {k // D.ccV c X DQ i k})} :
    D.ccVIdx c X DQ i k = some k' ↔ k = (ccEquiv _ k').1 := by
  unfold ccVIdx
  split_ifs with h
  · rw [Option.some_inj]
    exact ccEquiv_symm_eq_iff
  · constructor
    · intro h'
      cases h'
    · intro hk
      exact (h (hk ▸ (ccEquiv _ k').2)).elim

theorem ccTorusSide_eq_some_iff {d' : Fin (Nat.card {d // D.ccT c X DQ i d})} {b : Bool}
    {k' : Fin (Nat.card {k // D.ccV c X DQ i k})} :
    D.ccTorusSide c X DQ i d' b = some k' ↔ D.torusSide (ccEquiv _ d').1 b = some (ccEquiv _ k').1 := by
  unfold ccTorusSide
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨k, hk, hk'⟩
    rw [hk, ccVIdx_eq_some_iff.mp hk']
  · intro h
    exact ⟨_, h, ccVIdx_eq_some_iff.mpr rfl⟩

theorem sdiff_zeroSphere_eq {A : Set W.Carrier} (h : A ⊆ (D.sphereSeam c).zeroSphereᶜ) :
    A \ (D.sphereSeam c).zeroSphere = A :=
  sdiff_eq_left.mpr (Set.disjoint_left.mpr fun _ hx hxS => h hx hxS)

theorem handle_subset_compl (h : Fin D.handleCount) :
    range (D.handle h).map ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  D.subset_compl_zeroSphere_of_disjoint (D.sphereSeam_handle_disjoint c h).symm

theorem edgeCircle_subset_compl (e : Fin D.edgeCircleCount) :
    range (D.edgeCircle e).piece.map ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  D.subset_compl_zeroSphere_of_disjoint (D.edgeCircle_image_disjoint_sphereCollar c e)

theorem region_subset_compl : D.circ.region ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  D.subset_compl_zeroSphere_of_disjoint (D.sphereSeam_region_disjoint c).symm

/-- A torus seam side of a torus seam of the component is a vertex of the component. -/
theorem ccV_torusSide {d : Fin D.torusSeamCount} (hd : D.ccT c X DQ i d) {b : Bool}
    {k : Fin D.vertexCount} (h : D.torusSide d b = some k) : D.ccV c X DQ i k := by
  let t : Torus := (1, 1)
  let s : ℝ := if b then -(1 / 2) else 1 / 2
  have hsrc : (t, s) ∈ (D.torusSeam d).collar.source := by
    rw [(D.torusSeam d).source_eq]
    change -1 < s ∧ s < 1
    cases b <;> norm_num [s]
  have hmem : (D.torusSeam d).collar (t, s) ∈ (D.vertex k).image := by
    cases b
    · have h' := D.torusSide_pos d t s (by norm_num [s]) (by norm_num [s])
      rw [h] at h'
      exact h'
    · have h' := D.torusSide_neg d t s (by norm_num [s]) (by norm_num [s])
      rw [h] at h'
      exact h'
  have hT := (D.torusSeam d).collar.map_source hsrc
  exact ccV_of_transport_mem hmem (D.torusTarget_subset_compl d hT) (hd ⟨_, hT, rfl⟩)

theorem ccTorusSide_eq_none_iff {d' : Fin (Nat.card {d // D.ccT c X DQ i d})} {b : Bool} :
    D.ccTorusSide c X DQ i d' b = none ↔ D.torusSide (ccEquiv _ d').1 b = none := by
  unfold ccTorusSide
  rw [Option.bind_eq_none_iff]
  constructor
  · intro h
    cases hk : D.torusSide (ccEquiv _ d').1 b with
    | none => rfl
    | some k =>
      have := h k hk
      unfold ccVIdx at this
      split_ifs at this with hv
      exact (hv (ccV_torusSide (ccEquiv _ d').2 hk)).elim
  · intro h k hk
    rw [h] at hk
    cases hk

/-- **The cut circle region lifted**: base points and projections. -/
theorem liftCirc_proj_eq {y : D.circ.domain} (hy : D.circ.proj y ∈ D.seamAvoidingBase c) :
    ∃ hx : X.transport y.val ∈ (D.liftCircleRegion c X).domain,
      (D.liftCircleRegion c X).proj ⟨_, hx⟩ = ⟨D.circ.proj y, hy⟩ := by
  have hyS : y.val ∉ (D.sphereSeam c).zeroSphere := hy y rfl
  refine ⟨⟨y.val, ⟨y.2, hy⟩, rfl⟩, Subtype.ext ?_⟩
  change D.circ.proj ⟨X.transport.symm (X.transport y.val), _⟩ = D.circ.proj y
  congr 1
  exact Subtype.ext (X.transport_symm_transport hyS)

/-- **Base points of the component circle region.** -/
theorem ccCirc_proj {y : D.circ.domain} (hy : D.circ.proj y ∈ D.seamAvoidingBase c)
    {x : (GC.Topology.componentCarrier X.Q DQ i).Carrier} (hx : x.val = X.transport y.val) :
    ∃ (hb : (⟨D.circ.proj y, hy⟩ : D.seamAvoidingBase c) ∈
        (D.liftCircleRegion c X).compBase DQ i)
      (hxd : x ∈ (D.ccCirc c X DQ i).domain),
      (D.ccCirc c X DQ i).proj ⟨x, hxd⟩ = ⟨⟨D.circ.proj y, hy⟩, hb⟩ := by
  obtain ⟨hx', hp⟩ := liftCirc_proj_eq (X := X) hy
  have hb : (⟨D.circ.proj y, hy⟩ : D.seamAvoidingBase c) ∈
      (D.liftCircleRegion c X).compBase DQ i := by
    rw [← hp]
    refine CircleRegion.mem_compBase_iff.mpr ?_
    change X.transport y.val ∈ DQ.piece i
    rw [← hx]
    exact x.2
  obtain ⟨hxd, hproj⟩ := (D.liftCircleRegion c X).exists_toComponent_proj DQ i
    (x := x) (y := ⟨_, hx'⟩) hx
  refine ⟨hb, hxd, Subtype.ext ?_⟩
  exact hproj.trans hp

/-- **Fibres of the component circle region** over a set of base points avoiding the seam. -/
theorem val_image_ccCirc_proj_preimage {A : Set D.circ.Base} (hA : A ⊆ D.seamAvoidingBase c) :
    Subtype.val '' ((D.ccCirc c X DQ i).proj ⁻¹' {b | b.val.val ∈ A}) =
      Subtype.val ⁻¹' (X.transport '' (Subtype.val '' (D.circ.proj ⁻¹' A))) := by
  have h1 := CircleRegion.val_image_proj_preimage_toComponent (D.liftCircleRegion c X) DQ i
    (Subtype.val ⁻¹' A)
  have h2 := X.val_image_proj_preimage_liftCircleRegion (D.circAway c) (D.circAway_domain_subset c)
    (Subtype.val ⁻¹' A)
  have h3 := D.circ.val_image_proj_preimage_restrictBase (D.cornerBase_subset_seamAvoidingBase c)
    (D.rounded_subset_seamAvoidingBase c) (D.cornerChart_target_subset_seamAvoidingBase c) hA
  exact h1.trans (congrArg (Subtype.val ⁻¹' ·) (h2.trans (congrArg (X.transport '' ·) h3)))

end DecompositionCertificate

/-! ## The first fields -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)
  (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i → D.SideSphereInterval c b)

theorem image_ccVertex (k' : Fin (Nat.card {k // D.ccV c X DQ i k})) :
    (D.ccVertex c X DQ i hcap k').image = Subtype.val ⁻¹' (X.transport ''
      ((D.vertex (ccEquiv _ k').1).image \ (D.sphereSeam c).zeroSphere) ∪
        D.ccCapPart c X (ccEquiv _ k').1) :=
  D.image_ccVertexOf c X DQ i hcap _ _

theorem boundaryImage_ccVertex (k' : Fin (Nat.card {k // D.ccV c X DQ i k})) :
    (D.ccVertex c X DQ i hcap k').boundaryImage = Subtype.val ⁻¹' (X.transport ''
      ((D.vertex (ccEquiv _ k').1).boundaryImage \ (D.sphereSeam c).zeroSphere)) :=
  D.boundaryImage_ccVertexOf c X DQ i hcap _ _

variable {D c X DQ i} in
theorem mem_image_ccVertex {k' : Fin (Nat.card {k // D.ccV c X DQ i k})} {y : W.Carrier}
    (hy : y ∈ (D.vertex (ccEquiv _ k').1).image) (hyS : y ∉ (D.sphereSeam c).zeroSphere)
    {x : (GC.Topology.componentCarrier X.Q DQ i).Carrier} (hx : x.val = X.transport y) :
    x ∈ (D.ccVertex c X DQ i hcap k').image := by
  rw [image_ccVertex]
  exact Or.inl ⟨y, ⟨hy, hyS⟩, hx.symm⟩

variable {D c X DQ i} in
theorem mem_image_ccVertex_symm {k : Fin D.vertexCount} (hk : D.ccV c X DQ i k) {y : W.Carrier}
    (hy : y ∈ (D.vertex k).image) (hyS : y ∉ (D.sphereSeam c).zeroSphere)
    {x : (GC.Topology.componentCarrier X.Q DQ i).Carrier} (hx : x.val = X.transport y) :
    x ∈ (D.ccVertex c X DQ i hcap ((ccEquiv _).symm ⟨k, hk⟩)).image :=
  mem_image_ccVertex hcap (by rw [Equiv.apply_symm_apply]; exact hy) hyS hx

theorem ccCapPart_side (b : Bool) :
    D.ccCapPart c X (D.sphereSide c b) = range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b))) := by
  unfold ccCapPart
  rw [D.vertexSide_sphereSide, ite_eq_left rfl]

/-- **Field `cover`.** -/
theorem cc_cover :
    (⋃ k', (D.ccVertex c X DQ i hcap k').image) ∪ (⋃ h', range (D.ccHandle c X DQ i h').map) ∪
      (⋃ e', range (D.ccEdgeCircle c X DQ i e').piece.map) ∪ (D.ccCirc c X DQ i).region = univ := by
  refine eq_univ_of_forall fun x => ?_
  by_cases hx : x.val ∈ X.capSet
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨b, hb⟩ := exists_sideCopy_eq (Fin.cast X.h2 j)
    have hj' : j = Fin.cast X.h2.symm (sideCopy b) := by rw [hb]; simp
    subst hj'
    have hsp : X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i :=
      (piece_eq_of_mem x.2 (X.range_cap_subset_spherePiece DQ (sideCopy b) hj)).symm
    let z₀ : ClosureSphere.{u} :=
      @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
    have hz := D.zeroSphere_subset_image c b ⟨z₀, rfl⟩
    rw [Vertex.image_eq_range_piece] at hz
    obtain ⟨q, hq⟩ := hz
    have hk : D.ccV c X DQ i (D.sphereSide c b) := by
      refine ccV_of_mem (q := q) ?_
      rw [D.liftVertex_map_of_mem c X b hq]
      have h := X.range_cap_subset_spherePiece DQ (sideCopy b)
      rw [hsp] at h
      exact h (X.core_cutSphere_mem_range_cap _ z₀)
    refine Or.inl (Or.inl (Or.inl (mem_iUnion.mpr ⟨(ccEquiv _).symm ⟨_, hk⟩, ?_⟩)))
    rw [image_ccVertex, Equiv.apply_symm_apply]
    right
    rw [ccCapPart_side]
    exact hj
  · set y := X.transport.symm x.val with hy
    have hyS : y ∉ (D.sphereSeam c).zeroSphere := X.transport_symm_notMem hx
    have hTy : X.transport y = x.val := X.transport_transport_symm hx
    have hcov : y ∈ (⋃ k, (D.vertex k).image) ∪ (⋃ h, range (D.handle h).map) ∪
        (⋃ e, range (D.edgeCircle e).piece.map) ∪ D.circ.region := by
      rw [D.cover]
      exact mem_univ y
    rcases hcov with ((hv | hh) | he) | hr
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hv
      have hkc : D.ccV c X DQ i k := ccV_of_transport_mem hk hyS (hTy ▸ x.2)
      exact Or.inl (Or.inl (Or.inl (mem_iUnion.mpr ⟨_, mem_image_ccVertex_symm hcap hkc hk hyS hTy.symm⟩)))
    · obtain ⟨h, p, hp⟩ := mem_iUnion.mp hh
      have hhc : D.ccH c X DQ i h := by
        refine ccH_of_mem (p := p) ?_
        change X.transport ((D.handle h).map p) ∈ DQ.piece i
        rw [hp, hTy]
        exact x.2
      refine Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨(ccEquiv _).symm ⟨h, hhc⟩, ?_⟩)))
      rw [range_ccHandle, Equiv.apply_symm_apply]
      exact ⟨_, ⟨p, hp⟩, hTy⟩
    · obtain ⟨e, q, hq⟩ := mem_iUnion.mp he
      have hec : D.ccE c X DQ i e := by
        refine ccE_of_mem (q := q) ?_
        change X.transport ((D.edgeCircle e).piece.map q) ∈ DQ.piece i
        rw [hq, hTy]
        exact x.2
      refine Or.inl (Or.inr (mem_iUnion.mpr ⟨(ccEquiv _).symm ⟨e, hec⟩, ?_⟩))
      rw [range_ccEdgeCircle, Equiv.apply_symm_apply]
      exact ⟨_, ⟨q, hq⟩, hTy⟩
    · refine Or.inr ?_
      rw [region_ccCirc]
      exact ⟨y, hr, hTy⟩

/-! ### Disjointness -/

theorem ccShape_handle (h' : Fin (Nat.card {h // D.ccH c X DQ i h})) :
    range (D.ccHandle c X DQ i h').map = Subtype.val ⁻¹' (X.transport ''
      (range (D.handle (ccEquiv _ h').1).map \ (D.sphereSeam c).zeroSphere) ∪ ∅) := by
  rw [union_empty, sdiff_zeroSphere_eq (D.handle_subset_compl _), range_ccHandle]

theorem ccShape_edgeCircle (e' : Fin (Nat.card {e // D.ccE c X DQ i e})) :
    range (D.ccEdgeCircle c X DQ i e').piece.map = Subtype.val ⁻¹' (X.transport ''
      (range (D.edgeCircle (ccEquiv _ e').1).piece.map \ (D.sphereSeam c).zeroSphere) ∪ ∅) := by
  rw [union_empty, sdiff_zeroSphere_eq (D.edgeCircle_subset_compl _), range_ccEdgeCircle]

theorem ccShape_region :
    (D.ccCirc c X DQ i).region = Subtype.val ⁻¹' (X.transport ''
      (D.circ.region \ (D.sphereSeam c).zeroSphere) ∪ ∅) := by
  rw [union_empty, sdiff_zeroSphere_eq D.region_subset_compl, region_ccCirc]

theorem ccEquiv_val_ne {α : Type*} [Finite α] {P : α → Prop} {k k' : Fin (Nat.card {a // P a})}
    (h : k ≠ k') : (ccEquiv P k).1 ≠ (ccEquiv P k').1 :=
  fun h' => h ((ccEquiv P).injective (Subtype.ext h'))

/-- **Field `vertex_disjoint`.** -/
theorem cc_vertex_disjoint : Pairwise fun k k' : Fin (Nat.card {k // D.ccV c X DQ i k}) =>
    Disjoint (interior (D.ccVertex c X DQ i hcap k).image)
      (interior (D.ccVertex c X DQ i hcap k').image) := by
  intro k k' hkk
  rw [image_ccVertex, image_ccVertex]
  exact disjoint_interior_preimage_val (X.disjoint_interior_lift (D.ccCapPart_subset_capSet c X _)
    (D.ccCapPart_subset_capSet c X _) (D.disjoint_ccCapPart c X (ccEquiv_val_ne hkk))
    (D.vertex_disjoint (ccEquiv_val_ne hkk)))

/-- **Field `handle_disjoint`.** -/
theorem cc_handle_disjoint : Pairwise fun h h' : Fin (Nat.card {h // D.ccH c X DQ i h}) =>
    Disjoint (interior (range (D.ccHandle c X DQ i h).map))
      (interior (range (D.ccHandle c X DQ i h').map)) := by
  intro h h' hhh
  rw [ccShape_handle, ccShape_handle]
  exact disjoint_interior_preimage_val (X.disjoint_interior_lift (empty_subset _) (empty_subset _)
    (disjoint_empty _) (D.handle_disjoint (ccEquiv_val_ne hhh)))

/-- **Field `edgeCircle_disjoint`.** -/
theorem cc_edgeCircle_disjoint : Pairwise fun e e' : Fin (Nat.card {e // D.ccE c X DQ i e}) =>
    Disjoint (range (D.ccEdgeCircle c X DQ i e).piece.map)
      (range (D.ccEdgeCircle c X DQ i e').piece.map) := by
  intro e e' hee
  rw [range_ccEdgeCircle, range_ccEdgeCircle]
  exact (X.disjoint_transport_image (D.edgeCircle_subset_compl _) (D.edgeCircle_subset_compl _)
    (D.edgeCircle_disjoint (ccEquiv_val_ne hee))).preimage _

/-- **Field `vertex_handle_disjoint`.** -/
theorem cc_vertex_handle_disjoint (k : Fin (Nat.card {k // D.ccV c X DQ i k}))
    (h : Fin (Nat.card {h // D.ccH c X DQ i h})) :
    Disjoint (interior (D.ccVertex c X DQ i hcap k).image)
      (interior (range (D.ccHandle c X DQ i h).map)) := by
  rw [image_ccVertex, ccShape_handle]
  exact disjoint_interior_preimage_val (X.disjoint_interior_lift (D.ccCapPart_subset_capSet c X _)
    (empty_subset _) (disjoint_empty _) (D.vertex_handle_disjoint _ _))

/-- **Field `edgeCircle_vertex_disjoint`.** -/
theorem cc_edgeCircle_vertex_disjoint (e : Fin (Nat.card {e // D.ccE c X DQ i e}))
    (k : Fin (Nat.card {k // D.ccV c X DQ i k})) :
    Disjoint (interior (range (D.ccEdgeCircle c X DQ i e).piece.map))
      (interior (D.ccVertex c X DQ i hcap k).image) := by
  rw [image_ccVertex, ccShape_edgeCircle]
  exact disjoint_interior_preimage_val (X.disjoint_interior_lift (empty_subset _)
    (D.ccCapPart_subset_capSet c X _) (empty_disjoint _) (D.edgeCircle_vertex_disjoint _ _))

/-- **Field `edgeCircle_handle_disjoint`.** -/
theorem cc_edgeCircle_handle_disjoint (e : Fin (Nat.card {e // D.ccE c X DQ i e}))
    (h : Fin (Nat.card {h // D.ccH c X DQ i h})) :
    Disjoint (interior (range (D.ccEdgeCircle c X DQ i e).piece.map))
      (interior (range (D.ccHandle c X DQ i h).map)) := by
  rw [ccShape_handle, ccShape_edgeCircle]
  exact disjoint_interior_preimage_val (X.disjoint_interior_lift (empty_subset _) (empty_subset _)
    (empty_disjoint _) (D.edgeCircle_handle_disjoint _ _))

/-- **Field `circ_vertex_disjoint`.** -/
theorem cc_circ_vertex_disjoint (k : Fin (Nat.card {k // D.ccV c X DQ i k})) :
    Disjoint (interior (D.ccCirc c X DQ i).region)
      (interior (D.ccVertex c X DQ i hcap k).image) := by
  rw [image_ccVertex, ccShape_region]
  exact disjoint_interior_preimage_val (X.disjoint_interior_lift (empty_subset _)
    (D.ccCapPart_subset_capSet c X _) (empty_disjoint _) (D.circ_vertex_disjoint _))

/-- **Field `circ_handle_disjoint`.** -/
theorem cc_circ_handle_disjoint (h : Fin (Nat.card {h // D.ccH c X DQ i h})) :
    Disjoint (interior (D.ccCirc c X DQ i).region)
      (interior (range (D.ccHandle c X DQ i h).map)) := by
  rw [ccShape_handle, ccShape_region]
  exact disjoint_interior_preimage_val (X.disjoint_interior_lift (empty_subset _) (empty_subset _)
    (empty_disjoint _) (D.circ_handle_disjoint _))

/-- **Field `circ_edgeCircle_disjoint`.** -/
theorem cc_circ_edgeCircle_disjoint (e : Fin (Nat.card {e // D.ccE c X DQ i e})) :
    Disjoint (interior (D.ccCirc c X DQ i).region)
      (interior (range (D.ccEdgeCircle c X DQ i e).piece.map)) := by
  rw [ccShape_edgeCircle, ccShape_region]
  exact disjoint_interior_preimage_val (X.disjoint_interior_lift (empty_subset _) (empty_subset _)
    (empty_disjoint _) (D.circ_edgeCircle_disjoint _))

end DecompositionCertificate

/-! ## Vertical fibres, seams and ports -/

theorem image_eq_preimage_val {Q : CompactCarrier.{u}} {DQ : Q.Components} {i : Fin DQ.count}
    {α : Type*} {g : α → (GC.Topology.componentCarrier Q DQ i).Carrier} {g₀ : α → Q.Carrier}
    (h : ∀ a, (g a).val = g₀ a) (A : Set α) : g '' A = Subtype.val ⁻¹' (g₀ '' A) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (h a).symm⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, Subtype.ext ((h a).trans hax)⟩

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)
  (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i → D.SideSphereInterval c b)

variable {D c X DQ i} in
theorem singleton_ccBase {b₀ : D.circ.Base} {b : (D.ccCirc c X DQ i).Base}
    (hb : b.val.val = b₀) : ({b} : Set (D.ccCirc c X DQ i).Base) = {b' | b'.val.val ∈ ({b₀} : Set _)} := by
  ext b'
  simp only [mem_singleton_iff, mem_ofPred_eq]
  constructor
  · rintro rfl
    exact hb
  · intro h
    exact Subtype.ext (Subtype.ext (h.trans hb.symm))

/-- **Field `vertical_fibre`.** -/
theorem cc_vertical_fibre (h' : Fin (Nat.card {h // D.ccH c X DQ i h})) (t : Icc (0 : ℝ) 1) :
    ∃ b : (D.ccCirc c X DQ i).Base,
      (fun x : ClosedCell 2 => (D.ccHandle c X DQ i h').map (x, t)) '' diskRim =
        Subtype.val '' ((D.ccCirc c X DQ i).proj ⁻¹' {b}) := by
  set h := (ccEquiv _ h').1 with hhdef
  obtain ⟨b, hb⟩ := D.vertical_fibre h t
  have hsub : Subtype.val '' (D.circ.proj ⁻¹' {b}) ⊆ range (D.handle h).map := by
    rw [← hb]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨_, rfl⟩
  have hb1 : b ∈ D.seamAvoidingBase c := by
    intro x hx
    exact D.handle_subset_compl h (hsub ⟨x, hx, rfl⟩)
  obtain ⟨y, rfl⟩ := D.circ.surjective_proj b
  have hyH : y.val ∈ range (D.handle h).map := hsub ⟨y, rfl, rfl⟩
  obtain ⟨p, hp⟩ := hyH
  have hpi : X.transport y.val ∈ DQ.piece i := by
    rw [← hp]
    exact ((D.ccHandle c X DQ i h').map p).2
  obtain ⟨hbc, -, -⟩ := ccCirc_proj (X := X) (DQ := DQ) (i := i) (x := ⟨_, hpi⟩) hb1 rfl
  refine ⟨⟨⟨_, hb1⟩, hbc⟩, ?_⟩
  have e1 := singleton_ccBase (X := X) (DQ := DQ) (i := i) (b := ⟨⟨_, hb1⟩, hbc⟩) rfl
  have e2 := val_image_ccCirc_proj_preimage (X := X) (DQ := DQ) (i := i)
    (A := {D.circ.proj y}) (fun _ hb' => (mem_singleton_iff.mp hb') ▸ hb1)
  have e3 : (fun x : ClosedCell 2 => (D.ccHandle c X DQ i h').map (x, t)) '' diskRim =
      Subtype.val ⁻¹' (X.transport '' ((fun x : ClosedCell 2 => (D.handle h).map (x, t)) '' diskRim)) := by
    rw [image_eq_preimage_val (g₀ := fun x : ClosedCell 2 => X.transport ((D.handle h).map (x, t)))
      (fun x => rfl), image_image]
  exact e3.trans ((congrArg (fun A => Subtype.val ⁻¹' (X.transport '' A)) hb).trans
    (e2.symm.trans (congrArg (fun B => Subtype.val '' ((D.ccCirc c X DQ i).proj ⁻¹' B)) e1.symm)))

/-- **Field `edgeCircle_vertical`.** -/
theorem cc_edgeCircle_vertical (e' : Fin (Nat.card {e // D.ccE c X DQ i e})) :
    (D.ccEdgeCircle c X DQ i e').piece.map '' {q | (𝓡∂ 3).IsBoundaryPoint q} ⊆
      (D.ccCirc c X DQ i).region := by
  refine (EdgeCirclePiece.image_boundary_toComponent _ _).trans_subset ?_
  rw [region_ccCirc]
  rintro x ⟨q, hq, hqx⟩
  exact ⟨_, D.edgeCircle_vertical _ ⟨q, hq, rfl⟩, hqx⟩

theorem cc_torusSide_mem (d' : Fin (Nat.card {d // D.ccT c X DQ i d})) (b : Bool)
    {p : Torus × ℝ} (hp : p ∈ (D.torusSeam (ccEquiv _ d').1).collar.source)
    (h0 : (D.torusSeam (ccEquiv _ d').1).collar p ∈
      (D.torusSide (ccEquiv _ d').1 b).elim D.circ.region fun k => (D.vertex k).image) :
    (D.ccTorusSeam c X DQ i d').collar p ∈
      (D.ccTorusSide c X DQ i d' b).elim (D.ccCirc c X DQ i).region
        fun k => (D.ccVertex c X DQ i hcap k).image := by
  have hx := ccTorusSeam_collar_val d' hp
  have hT := (D.torusSeam (ccEquiv _ d').1).collar.map_source hp
  cases hk : D.torusSide (ccEquiv _ d').1 b with
  | none =>
    rw [hk] at h0
    rw [ccTorusSide_eq_none_iff.mpr hk]
    change _ ∈ (D.ccCirc c X DQ i).region
    rw [region_ccCirc]
    exact ⟨_, h0, hx.symm⟩
  | some k =>
    rw [hk] at h0
    have hkc := ccV_torusSide (ccEquiv _ d').2 hk
    have hs : D.ccTorusSide c X DQ i d' b = some ((ccEquiv _).symm ⟨k, hkc⟩) := by
      rw [ccTorusSide_eq_some_iff, Equiv.apply_symm_apply]
      exact hk
    rw [hs]
    exact mem_image_ccVertex_symm hcap hkc h0 (D.torusTarget_subset_compl _ hT) hx

/-- **Field `torusSide_neg`.** -/
theorem cc_torusSide_neg (d' : Fin (Nat.card {d // D.ccT c X DQ i d})) (t : Torus) (s : ℝ)
    (h1 : -1 < s) (h2 : s ≤ 0) :
    (D.ccTorusSeam c X DQ i d').collar (t, s) ∈
      (D.ccTorusSide c X DQ i d' true).elim (D.ccCirc c X DQ i).region
        fun k => (D.ccVertex c X DQ i hcap k).image :=
  D.cc_torusSide_mem c X DQ i hcap d' true
    (by rw [(D.torusSeam _).source_eq]; exact ⟨h1, by linarith⟩) (D.torusSide_neg _ t s h1 h2)

/-- **Field `torusSide_pos`.** -/
theorem cc_torusSide_pos (d' : Fin (Nat.card {d // D.ccT c X DQ i d})) (t : Torus) (s : ℝ)
    (h1 : 0 ≤ s) (h2 : s < 1) :
    (D.ccTorusSeam c X DQ i d').collar (t, s) ∈
      (D.ccTorusSide c X DQ i d' false).elim (D.ccCirc c X DQ i).region
        fun k => (D.ccVertex c X DQ i hcap k).image :=
  D.cc_torusSide_mem c X DQ i hcap d' false
    (by rw [(D.torusSeam _).source_eq]; exact ⟨by linarith, h2⟩) (D.torusSide_pos _ t s h1 h2)

/-- **Field `torusSeam_disjoint`.** -/
theorem cc_torusSeam_disjoint : Pairwise fun d d' : Fin (Nat.card {d // D.ccT c X DQ i d}) =>
    Disjoint (D.ccTorusSeam c X DQ i d).collar.target (D.ccTorusSeam c X DQ i d').collar.target := by
  intro d d' hdd
  rw [ccTorusSeam_target, ccTorusSeam_target]
  exact (X.disjoint_transport_image (D.torusTarget_subset_compl _) (D.torusTarget_subset_compl _)
    (D.torusSeam_disjoint (ccEquiv_val_ne hdd))).preimage _

theorem cc_sphereSide_mem (c'' : Fin (Nat.card {c' // D.ccS c X DQ i c'})) (b : Bool)
    {p : ClosureSphere.{u} × ℝ} (hp : p ∈ (D.sphereSeam (ccEquiv _ c'').1).collar.source)
    (h0 : (D.sphereSeam (ccEquiv _ c'').1).collar p ∈
      (D.vertex (D.sphereSide (ccEquiv _ c'').1 b)).image) :
    (D.ccSphereSeam c X DQ i c'').collar p ∈
      (D.ccVertex c X DQ i hcap (D.ccSphereSide c X DQ i c'' b)).image :=
  mem_image_ccVertex_symm hcap _ h0
    (D.sphereTarget_subset_compl (ccEquiv _ c'').2.1
      ((D.sphereSeam (ccEquiv _ c'').1).collar.map_source hp))
    (ccSphereSeam_collar_val c'' hp)

/-- **Field `sphereSide_neg`.** -/
theorem cc_sphereSide_neg (c'' : Fin (Nat.card {c' // D.ccS c X DQ i c'})) (z : ClosureSphere.{u})
    (s : ℝ) (h1 : s ≤ 0) (h2 : -1 < s) :
    (D.ccSphereSeam c X DQ i c'').collar (z, s) ∈
      (D.ccVertex c X DQ i hcap (D.ccSphereSide c X DQ i c'' true)).image :=
  D.cc_sphereSide_mem c X DQ i hcap c'' true
    ((D.sphereSeam _).mem_source_iff.mpr ⟨h2, by linarith⟩) (D.sphereSide_neg _ z s h1 h2)

/-- **Field `sphereSide_pos`.** -/
theorem cc_sphereSide_pos (c'' : Fin (Nat.card {c' // D.ccS c X DQ i c'})) (z : ClosureSphere.{u})
    (s : ℝ) (h1 : 0 ≤ s) (h2 : s < 1) :
    (D.ccSphereSeam c X DQ i c'').collar (z, s) ∈
      (D.ccVertex c X DQ i hcap (D.ccSphereSide c X DQ i c'' false)).image :=
  D.cc_sphereSide_mem c X DQ i hcap c'' false
    ((D.sphereSeam _).mem_source_iff.mpr ⟨by linarith, h2⟩) (D.sphereSide_pos _ z s h1 h2)

/-- **Field `sphereSeam_disjoint`.** -/
theorem cc_sphereSeam_disjoint : Pairwise fun d d' : Fin (Nat.card {c' // D.ccS c X DQ i c'}) =>
    Disjoint (D.ccSphereSeam c X DQ i d).collar.target
      (D.ccSphereSeam c X DQ i d').collar.target := by
  intro d d' hdd
  rw [ccSphereSeam_target, ccSphereSeam_target]
  exact (X.disjoint_transport_image (D.sphereTarget_subset_compl (ccEquiv _ d).2.1)
    (D.sphereTarget_subset_compl (ccEquiv _ d').2.1)
    (D.sphereSeam_disjoint (ccEquiv_val_ne hdd))).preimage _

/-- **Field `sphere_torus_seam_disjoint`.** -/
theorem cc_sphere_torus_seam_disjoint (d : Fin (Nat.card {c' // D.ccS c X DQ i c'}))
    (d' : Fin (Nat.card {d // D.ccT c X DQ i d})) :
    Disjoint (D.ccSphereSeam c X DQ i d).collar.target (D.ccTorusSeam c X DQ i d').collar.target := by
  rw [ccSphereSeam_target, ccTorusSeam_target]
  exact (X.disjoint_transport_image (D.sphereTarget_subset_compl (ccEquiv _ d).2.1)
    (D.torusTarget_subset_compl _) (D.sphere_torus_seam_disjoint _ _)).preimage _

/-- The collar targets of the ports of the component. -/
theorem componentTori_target_eq
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))) :
    ((X.componentTori DQ i).collar a).target = Subtype.val ⁻¹' (X.transport ''
      (E.collar (Fin.cast X.hn (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1)).target) := by
  rw [PortRestriction.restrictComponent_collar_target, X.transport_image_externalTarget]
  rfl

/-- **Field `external_owned`.** -/
theorem cc_external_owned
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))) :
    ((X.componentTori DQ i).collar a).target ⊆
      (D.ccVertex c X DQ i hcap (D.ccExternalOwner c X DQ i a)).image := by
  rw [componentTori_target_eq]
  rintro x ⟨y, hy, hyx⟩
  exact mem_image_ccVertex_symm hcap _ (D.external_owned _ hy) (X.externalTarget_subset_compl _ hy)
    hyx.symm

end DecompositionCertificate

/-! ## The face fields -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)
  (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i → D.SideSphereInterval c b)

theorem ccFace_symm {f : Fin D.faceCount} (hf : D.ccF c X DQ i f) :
    D.ccFace c X DQ i ((ccEquiv _).symm ⟨f, hf⟩) = Subtype.val ⁻¹' (X.transport '' D.face f) := by
  rw [ccFace, Equiv.apply_symm_apply]
  rfl

theorem ccFaceKind_symm {f : Fin D.faceCount} (hf : D.ccF c X DQ i f) :
    D.ccFaceKind c X DQ i ((ccEquiv _).symm ⟨f, hf⟩) = D.ccKind c X DQ i (D.faceKind f) := by
  rw [ccFaceKind, Equiv.apply_symm_apply]

theorem ccFaceOwner_symm {f : Fin D.faceCount} (hf : D.ccF c X DQ i f) :
    D.ccFaceOwner c X DQ i ((ccEquiv _).symm ⟨f, hf⟩) = (ccEquiv _).symm ⟨D.faceOwner f, hf.2⟩ := by
  rw [ccFaceOwner_eq_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Field `face_exhausted`.** -/
theorem cc_face_exhausted (k : Fin (Nat.card {k // D.ccV c X DQ i k})) :
    (⋃ (f : Fin (Nat.card {f // D.ccF c X DQ i f})) (_ : D.ccFaceOwner c X DQ i f = k),
      D.ccFace c X DQ i f) = (D.ccVertex c X DQ i hcap k).boundaryImage := by
  rw [boundaryImage_ccVertex, boundaryImage_sdiff_zeroSphere]
  ext x
  constructor
  · intro hx
    obtain ⟨f, hf, y, hy, hyx⟩ := mem_iUnion₂.mp hx
    exact ⟨y, mem_iUnion₂.mpr ⟨_, ⟨ccFaceOwner_eq_iff.mp hf, (ccEquiv _ f).2.1⟩, hy⟩, hyx⟩
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨f, ⟨hfo, hfk⟩, hyf⟩ := mem_iUnion₂.mp hy
    have hF : D.ccF c X DQ i f := ⟨hfk, hfo ▸ (ccEquiv _ k).2⟩
    refine mem_iUnion₂.mpr ⟨(ccEquiv _).symm ⟨f, hF⟩, ?_, ?_⟩
    · rw [ccFaceOwner_eq_iff, Equiv.apply_symm_apply]
      exact hfo
    · rw [ccFace_symm]
      exact ⟨y, hyf, hyx⟩

/-- **Field `face_disjoint`.** -/
theorem cc_face_disjoint (f f' : Fin (Nat.card {f // D.ccF c X DQ i f})) (hne : f ≠ f')
    (hs : ∀ c'' b, ¬ (D.ccFaceKind c X DQ i f = .sphereSeam c'' b ∧
      D.ccFaceKind c X DQ i f' = .sphereSeam c'' (!b)))
    (ht : ∀ d b, ¬ (D.ccFaceKind c X DQ i f = .torusSeam d b ∧
      D.ccFaceKind c X DQ i f' = .torusSeam d (!b))) :
    Disjoint (D.ccFace c X DQ i f) (D.ccFace c X DQ i f') := by
  have hf := (ccEquiv _ f).2
  have hf' := (ccEquiv _ f').2
  refine (X.disjoint_transport_image (D.face_subset_compl_zeroSphere c hf.1)
    (D.face_subset_compl_zeroSphere c hf'.1) ?_).preimage _
  refine D.face_disjoint _ _ (ccEquiv_val_ne hne) ?_ ?_
  · rintro c' b ⟨h1, h2⟩
    refine hs ((ccEquiv _).symm ⟨c', ccS_of_face hf h1⟩) b ⟨?_, ?_⟩
    · rw [ccFaceKind, h1, ccKind_sphereSeam]
    · rw [ccFaceKind, h2, ccKind_sphereSeam]
  · rintro d b ⟨h1, h2⟩
    refine ht ((ccEquiv _).symm ⟨d, ccT_of_face hf h1⟩) b ⟨?_, ?_⟩
    · rw [ccFaceKind, h1, ccKind_torusSeam]
    · rw [ccFaceKind, h2, ccKind_torusSeam]

theorem range_componentTori_torusMap
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))) :
    range ((X.componentTori DQ i).torusMap a) = Subtype.val ⁻¹' (X.transport ''
      range (E.torusMap (Fin.cast X.hn (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1))) := by
  rw [X.transport_image_range_torusMap]
  exact range_eq_preimage_val (PortRestriction.restrictComponent_torusMap _ DQ i a)

/-- **Field `face_external`.** -/
theorem cc_face_external (f : Fin (Nat.card {f // D.ccF c X DQ i f}))
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i)))
    (h : D.ccFaceKind c X DQ i f = .external a) :
    D.ccFace c X DQ i f = range ((X.componentTori DQ i).torusMap a) ∧
      D.ccExternalOwner c X DQ i a = D.ccFaceOwner c X DQ i f := by
  have hk := eq_of_ccKind_eq_external h
  obtain ⟨h1, h2⟩ := D.face_external _ _ hk
  refine ⟨?_, ?_⟩
  · rw [ccFace, h1, range_componentTori_torusMap]
    rfl
  · unfold ccExternalOwner ccFaceOwner
    congr 1
    exact Subtype.ext h2

/-- **Field `external_face`.** -/
theorem cc_external_face
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))) :
    ∃ f, D.ccFaceKind c X DQ i f = .external a := by
  set a₀ := Fin.cast X.hn (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1
  obtain ⟨f, hf⟩ := D.external_face a₀
  have hown := (D.face_external f a₀ hf).2
  have hF : D.ccF c X DQ i f := ⟨(fun b h => by rw [hf] at h; cases h), hown ▸ ccV_externalOwner a⟩
  refine ⟨(ccEquiv _).symm ⟨f, hF⟩, ?_⟩
  have hp : PortRestriction.portPiece X.capping.retained DQ (Fin.cast X.hn.symm a₀) = i :=
    portPiece_eq_of_face hF hf
  rw [ccFaceKind_symm, hf, ccKind_external hp]
  congr 1
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext (by simp [a₀])

theorem range_ccTorusSeam_zero (d : Fin (Nat.card {d // D.ccT c X DQ i d})) :
    range (fun t => (D.ccTorusSeam c X DQ i d).collar (t, 0)) =
      Subtype.val ⁻¹' (X.transport '' range fun t => (D.torusSeam (ccEquiv _ d).1).collar (t, 0)) := by
  rw [← range_comp]
  refine range_eq_preimage_val fun t => ccTorusSeam_collar_val d ?_
  rw [(D.torusSeam _).source_eq]
  exact ⟨by norm_num, by norm_num⟩

theorem range_ccSphereSeam_zero (d : Fin (Nat.card {c' // D.ccS c X DQ i c'})) :
    range (fun z => (D.ccSphereSeam c X DQ i d).collar (z, 0)) =
      Subtype.val ⁻¹' (X.transport '' range fun z => (D.sphereSeam (ccEquiv _ d).1).collar (z, 0)) := by
  rw [← range_comp]
  exact range_eq_preimage_val fun z => ccSphereSeam_collar_val d ((D.sphereSeam _).zero_mem_source z)

/-- **Field `face_torusSeam`.** -/
theorem cc_face_torusSeam (f : Fin (Nat.card {f // D.ccF c X DQ i f}))
    (d : Fin (Nat.card {d // D.ccT c X DQ i d})) (b : Bool)
    (h : D.ccFaceKind c X DQ i f = .torusSeam d b) :
    D.ccFace c X DQ i f = range (fun t => (D.ccTorusSeam c X DQ i d).collar (t, 0)) ∧
      D.ccTorusSide c X DQ i d b = some (D.ccFaceOwner c X DQ i f) := by
  have hk := eq_of_ccKind_eq_torusSeam h
  obtain ⟨h1, h2⟩ := D.face_torusSeam _ _ _ hk
  refine ⟨?_, ?_⟩
  · rw [ccFace, h1, range_ccTorusSeam_zero]
    rfl
  · rw [ccTorusSide_eq_some_iff, ccFaceOwner, Equiv.apply_symm_apply]
    exact h2

/-- **Field `torusSeam_face`.** -/
theorem cc_torusSeam_face (d : Fin (Nat.card {d // D.ccT c X DQ i d})) (b : Bool)
    (k : Fin (Nat.card {k // D.ccV c X DQ i k})) (h : D.ccTorusSide c X DQ i d b = some k) :
    ∃ f, D.ccFaceOwner c X DQ i f = k ∧ D.ccFaceKind c X DQ i f = .torusSeam d b := by
  obtain ⟨f, hfo, hfk⟩ := D.torusSeam_face _ b _ (ccTorusSide_eq_some_iff.mp h)
  have hF : D.ccF c X DQ i f := ⟨(fun b' h' => by rw [hfk] at h'; cases h'), hfo ▸ (ccEquiv _ k).2⟩
  refine ⟨(ccEquiv _).symm ⟨f, hF⟩, ?_, ?_⟩
  · rw [ccFaceOwner_eq_iff, Equiv.apply_symm_apply]
    exact hfo
  · rw [ccFaceKind_symm, hfk, ccKind_torusSeam (ccEquiv _ d).2, ccEquiv_symm_val]

/-- **Field `face_sphereSeam`.** -/
theorem cc_face_sphereSeam (f : Fin (Nat.card {f // D.ccF c X DQ i f}))
    (d : Fin (Nat.card {c' // D.ccS c X DQ i c'})) (b : Bool)
    (h : D.ccFaceKind c X DQ i f = .sphereSeam d b) :
    D.ccFace c X DQ i f = range (fun z => (D.ccSphereSeam c X DQ i d).collar (z, 0)) ∧
      D.ccSphereSide c X DQ i d b = D.ccFaceOwner c X DQ i f := by
  have hk := eq_of_ccKind_eq_sphereSeam h
  obtain ⟨h1, h2⟩ := D.face_sphereSeam _ _ _ hk
  refine ⟨?_, ?_⟩
  · rw [ccFace, h1, range_ccSphereSeam_zero]
    rfl
  · unfold ccSphereSide ccFaceOwner
    congr 1
    exact Subtype.ext h2

/-- **Field `sphereSeam_face`.** -/
theorem cc_sphereSeam_face (d : Fin (Nat.card {c' // D.ccS c X DQ i c'})) (b : Bool) :
    ∃ f, D.ccFaceOwner c X DQ i f = D.ccSphereSide c X DQ i d b ∧
      D.ccFaceKind c X DQ i f = .sphereSeam d b := by
  obtain ⟨f, hfo, hfk⟩ := D.sphereSeam_face (ccEquiv _ d).1 b
  have hF : D.ccF c X DQ i f :=
    ⟨fun b' h' => by
      rw [hfk] at h'
      injection h' with h'
      exact (ccEquiv _ d).2.1 h',
     hfo ▸ ccV_sphereSide (ccEquiv _ d).2 b⟩
  refine ⟨(ccEquiv _).symm ⟨f, hF⟩, ?_, ?_⟩
  · rw [ccFaceOwner_symm]
    unfold ccSphereSide
    congr 1
    exact Subtype.ext hfo
  · rw [ccFaceKind_symm, hfk, ccKind_sphereSeam (ccEquiv _ d).2, ccEquiv_symm_val]

end DecompositionCertificate

/-! ## Consumer (G4) -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

/-- **Consumer (G4).** On a capped component all of whose caps belong to `S² × I` sides, the
inherited vertices, handles, edge-circle pieces and circle region cover the component carrier, the
vertices have pairwise disjoint interiors, and every port of the component is owned by an inherited
vertex. -/
theorem exists_ccCover
    (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i →
      D.SideSphereInterval c b) :
    ∃ (m : ℕ) (V : Fin m → Vertex (GC.Topology.componentCarrier X.Q DQ i)) (mh : ℕ)
      (H : Fin mh → EdgeHandle (GC.Topology.componentCarrier X.Q DQ i)) (me : ℕ)
      (C : Fin me → EdgeCirclePiece (GC.Topology.componentCarrier X.Q DQ i))
      (R : CircleRegion (GC.Topology.componentCarrier X.Q DQ i)),
      (⋃ k, (V k).image) ∪ (⋃ h, range (H h).map) ∪ (⋃ e, range (C e).piece.map) ∪ R.region =
        univ ∧
      (Pairwise fun k k' => Disjoint (interior (V k).image) (interior (V k').image)) ∧
      ∀ a, ∃ k, ((X.componentTori DQ i).collar a).target ⊆ (V k).image :=
  ⟨_, D.ccVertex c X DQ i hcap, _, D.ccHandle c X DQ i, _, D.ccEdgeCircle c X DQ i,
    D.ccCirc c X DQ i, D.cc_cover c X DQ i hcap, D.cc_vertex_disjoint c X DQ i hcap,
    fun a => ⟨_, D.cc_external_owned c X DQ i hcap a⟩⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
