import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceTorusFamilyComponent_S19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BlockCoreAbstract_S28
import DifferentialGeometry.Topology.Manifold.ImmersionInterior

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

section Core

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} {t : ℝ}
  (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)

/-- The stage image of the `c`-th truncated core: `cores.map c t ∘ inclusion`. -/
def corePhi_S28 (c : Fin cores.count) :
    (D.truncation c).core.Carrier → (postStage F.observation t).Carrier :=
  fun x => cores.map c t ht ((D.truncation c).inclusion x)

/-- The connected component of the slice stage containing the `c`-th truncated core. -/
def coreComp_S28 (c : Fin cores.count) :
    ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier :=
  ConnectedComponents.mk (corePhi_S28 D ht c
    (Classical.choice (D.truncation c).connected.toNonempty))

variable (hdom : ∀ i, range (D.truncation i).inclusion ⊆
  (cores.domain i t : Set (cores.model i).Carrier))
include hdom

theorem corePhi_continuous_S28 (c : Fin cores.count) : Continuous (corePhi_S28 D ht c) :=
  (cores.smooth c t ht).continuousOn.comp_continuous (D.truncation c).inclusion.continuous
    (fun x => hdom c ⟨x, rfl⟩)

omit hdom in
theorem isLocalDiffeomorphAt_map_S28 (c : Fin cores.count) {y : (cores.model c).Carrier}
    (hy : y ∈ (cores.domain c t : Set _)) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (cores.map c t ht) y := by
  obtain ⟨φ, hs, hap, -⟩ := exists_openEmbChart_S19 (cores.domain c t) ⟨⟨y, hy⟩⟩
    (cores.map c t ht) (cores.embedding c t ht)
  exact ⟨φ, by rw [hs]; exact hy, fun z hz => (hap z (by rw [hs] at hz; exact hz)).symm⟩

theorem corePhi_localDiffeo_S28 (c : Fin cores.count) :
    IsLocalDiffeomorph (D.truncation c).core.model (𝓡 3) ∞
      (fun x : (D.truncation c).core.interior => corePhi_S28 D ht c x.1) := by
  intro x
  have hi := isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion
    (D.truncation c).embedding.isImmersion x.property (by rfl)
  have h1 : IsLocalDiffeomorphAt (D.truncation c).core.model (𝓡 3) ∞
      (fun x : (D.truncation c).core.interior => (D.truncation c).inclusion x.1) x :=
    (isLocalDiffeomorph_subtype_val (D.truncation c).core.interior x).comp (𝓡 3) _ hi
  exact IsLocalDiffeomorphAt.comp (hf := h1)
    (hg := isLocalDiffeomorphAt_map_S28 ht c (hdom c ⟨x.1, rfl⟩))

theorem corePhi_injective_S28 (c : Fin cores.count) : Injective (corePhi_S28 D ht c) := by
  intro x y hxy
  have h := (cores.embedding c t ht).isEmbedding.injective
    (a₁ := ⟨_, hdom c ⟨x, rfl⟩⟩) (a₂ := ⟨_, hdom c ⟨y, rfl⟩⟩) hxy
  have h2 := Subtype.ext_iff.mp h
  exact (D.truncation c).embedding.isEmbedding.injective h2

theorem corePhi_ne_S28 {c c' : Fin cores.count} (h : c ≠ c')
    (x : (D.truncation c).core.Carrier) (y : (D.truncation c').core.Carrier) :
    corePhi_S28 D ht c x ≠ corePhi_S28 D ht c' y := fun hxy =>
  Set.disjoint_left.mp (cores.disjoint t ht h)
    ⟨_, hdom c ⟨x, rfl⟩, rfl⟩ ⟨_, hdom c' ⟨y, rfl⟩, hxy.symm⟩

theorem corePhi_comp_S28 (c : Fin cores.count) (x : (D.truncation c).core.Carrier) :
    ConnectedComponents.mk (corePhi_S28 D ht c x) = coreComp_S28 D ht c := by
  have := (D.truncation c).connected
  have hpre := isPreconnected_range (corePhi_continuous_S28 D ht hdom c)
  exact ConnectedComponents.coe_eq_coe'.mpr
    (hpre.subset_connectedComponent ⟨_, rfl⟩ ⟨x, rfl⟩)

end Core

section Block

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} {t : ℝ}
  (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)

/-- The connected component `C` of the slice stage, as a connected closed oriented manifold. -/
abbrev sliceM_S28
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier) :=
  (postStage F.observation t).toClosedOrientedManifold.component C

/-- **The real cut of the component `C`**: the S12 cut presentation of the seam family
`componentFamily_S19 D ht C`.  Its carrier is `cutCarrier_C2a (componentFamily_S19 D ht C)`
(`rfl`), its seam `torusInPrime e = σ_e(·,0)`. -/
def sliceDec_S28
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier) :
    GC.Topology.TorusDecomposition (sliceM_S28 C) :=
  (cutPresentation_S12 (sliceM_S28 C) (componentFamily_S19 D ht C)).toTorusDecomposition

theorem sliceDec_carrier_S28
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier) :
    (sliceDec_S28 D ht C).carrier = cutCarrier_C2a (componentFamily_S19 D ht C) := rfl

/-- The cut tori `zeroSet` of the component family are exactly the seam tori
`cores.map i t (cuspMap q (p, 0))` of the collars lying in the component `C`. -/
theorem mem_zeroSet_S28
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (z : (sliceM_S28 C).Carrier) :
    z ∈ zeroSet_S12 (componentFamily_S19 D ht C) ↔
      ∃ (x : SliceIdx_S19 D) (p : Torus), comp_S19 D ht x = C ∧
        (z.1 : (postStage F.observation t).Carrier) =
          cores.map x.1 t ht ((D.truncation x.1).cuspMap x.2 (p, halfZero)) := by
  have key : ∀ (k : Fin (componentFamily_S19 D ht C).count) (p : Torus),
      ((((componentFamily_S19 D ht C).collar k) (p, 0)).val : (postStage F.observation t).Carrier) =
        stageCollar_S19 D ht ((cidxEquiv_S19 D ht C).symm k).1 (p, 0) := fun k p =>
    restrictCollar_apply_S19 _ _ _ (cidx_target_subset_S19 D ht _) (p, 0)
      (by rw [stageCollar_source_S19]; exact zero_mem_source_S19 p)
  constructor
  · intro hz
    obtain ⟨k, ⟨⟨p, s⟩, ⟨-, hs⟩, hq⟩⟩ := mem_iUnion.mp hz
    have hs0 : s = 0 := hs
    subst hs0
    refine ⟨((cidxEquiv_S19 D ht C).symm k).1, p, ((cidxEquiv_S19 D ht C).symm k).2, ?_⟩
    rw [← stageCollar_zero_S19 D ht, ← key k p]
    exact (congrArg Subtype.val hq).symm
  · rintro ⟨x, p, hx, hz⟩
    refine mem_iUnion.mpr ⟨cidxEquiv_S19 D ht C ⟨x, hx⟩, ⟨(p, 0), ⟨trivial, rfl⟩, ?_⟩⟩
    apply Subtype.ext
    have h := key (cidxEquiv_S19 D ht C ⟨x, hx⟩) p
    rw [Equiv.symm_apply_apply] at h
    exact h.trans ((stageCollar_zero_S19 D ht x p).trans hz.symm)

/-- The image in the slice stage of the interior of the `j`-th block of the real cut of `C`. -/
def blockImage_S28
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (j : Fin (sliceDec_S28 D ht C).components.count) : Set (postStage F.observation t).Carrier :=
  (fun x => (rmapK_S12 (componentFamily_S19 D ht C) x).1) ''
    ((cutCarrier_C2a (componentFamily_S19 D ht C)).pieceInterior
      ((sliceDec_S28 D ht C).components.piece j) : Set _)

variable (hdom : ∀ i, range (D.truncation i).inclusion ⊆
  (cores.domain i t : Set (cores.model i).Carrier))

/-- The core, as a map into the component `C` it lies in. -/
def corePhiComp_S28 (c : Fin cores.count) (x : (D.truncation c).core.Carrier) :
    (sliceM_S28 (coreComp_S28 D ht c)).Carrier :=
  ⟨corePhi_S28 D ht c x, corePhi_comp_S28 D ht hdom c x⟩

theorem corePhi_not_zeroSet_S28 (c : Fin cores.count) {x : (D.truncation c).core.Carrier}
    (hx : x ∈ ((D.truncation c).core.interior : Set _)) :
    corePhiComp_S28 D ht hdom c x ∉
      zeroSet_S12 (componentFamily_S19 D ht (coreComp_S28 D ht c)) := by
  rw [mem_zeroSet_S28]
  rintro ⟨⟨c', q⟩, p, -, hz⟩
  have hz' : corePhi_S28 D ht c x = corePhi_S28 D ht c' ((D.truncation c').boundary.torusMap q p) := by
    have := (D.truncation c').cusp_zero q p
    change cores.map c t ht _ = cores.map c' t ht ((D.truncation c').cuspMap q (p, halfZero)) at hz
    rw [this] at hz
    exact hz
  by_cases h : c = c'
  · subst h
    have := corePhi_injective_S28 D ht hdom c hz'
    have hb : x ∈ (D.truncation c).core.model.boundary (D.truncation c).core.Carrier := by
      rw [(D.truncation c).boundary_exhausted, this]
      exact mem_iUnion.mpr ⟨q, p, rfl⟩
    exact (D.truncation c).core.model.disjoint_interior_boundary.le_bot ⟨hx, hb⟩
  · exact corePhi_ne_S28 D ht hdom h _ _ hz'

theorem corePhi_boundary_zeroSet_S28 (c : Fin cores.count) {y : (D.truncation c).core.Carrier}
    (hy : y ∈ (D.truncation c).core.model.boundary (D.truncation c).core.Carrier) :
    corePhiComp_S28 D ht hdom c y ∈
      zeroSet_S12 (componentFamily_S19 D ht (coreComp_S28 D ht c)) := by
  rw [(D.truncation c).boundary_exhausted] at hy
  obtain ⟨q, p, rfl⟩ := mem_iUnion.mp hy
  rw [mem_zeroSet_S28]
  refine ⟨⟨c, q⟩, p, ?_, ?_⟩
  · have hsrc : ((p : Torus), (0 : ℝ)) ∈ (stageCollar_S19 D ht ⟨c, q⟩).source := by
      rw [stageCollar_source_S19]; exact zero_mem_source_S19 p
    have hmem := stageCollar_target_subset_comp_S19 D ht ⟨c, q⟩
      ((stageCollar_S19 D ht ⟨c, q⟩).map_source hsrc)
    have h2 : stageCollar_S19 D ht ⟨c, q⟩ (p, 0) =
        corePhi_S28 D ht c ((D.truncation c).boundary.torusMap q p) := by
      rw [stageCollar_zero_S19 D ht ⟨c, q⟩ p]
      exact congrArg _ ((D.truncation c).cusp_zero q p)
    rw [h2] at hmem
    exact hmem.symm.trans (corePhi_comp_S28 D ht hdom c _)
  · exact congrArg _ ((D.truncation c).cusp_zero q p).symm

include hdom in
/-- **Block = core (S28).**  For the real cut `sliceDec_S28` of the component `C` containing the
`c`-th truncated core `D.truncation c`, exactly one block `j` contains the core: its interior is
diffeomorphic to the interior of `(D.truncation c).core` (the `∃ c, Nonempty (Diffeomorph …)`
branch of S24's `hthin`), its stage image is `cores.map c t '' inclusion '' core°`, and all other
blocks of `C` have interior image disjoint from it. -/
theorem blockCoreIdentification_S28 (c : Fin cores.count) :
    ∃ j : Fin (sliceDec_S28 D ht (coreComp_S28 D ht c)).components.count,
      Nonempty (Diffeomorph (sliceDec_S28 D ht (coreComp_S28 D ht c)).carrier.model
        (D.truncation c).core.model
        ((sliceDec_S28 D ht (coreComp_S28 D ht c)).carrier.pieceInterior
          ((sliceDec_S28 D ht (coreComp_S28 D ht c)).components.piece j))
        (D.truncation c).core.interior ∞) ∧
      blockImage_S28 D ht (coreComp_S28 D ht c) j =
        corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _) ∧
      ∀ j' : Fin (sliceDec_S28 D ht (coreComp_S28 D ht c)).components.count, j' ≠ j →
        Disjoint (blockImage_S28 D ht (coreComp_S28 D ht c) j')
          (corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _)) := by
  have := (D.truncation c).connected
  have hloc : IsLocalDiffeomorph (D.truncation c).core.model (𝓡 3) ∞
      (fun x : (D.truncation c).core.interior => corePhiComp_S28 D ht hdom c x.1) := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict
      (V := (postStage F.observation t).toClosedOrientedManifold.componentOpen
        (coreComp_S28 D ht c))
      (f := fun x : (D.truncation c).core.interior => corePhi_S28 D ht c x.1)
      (fun x => corePhi_comp_S28 D ht hdom c x.1) (corePhi_localDiffeo_S28 D ht hdom c x)
  obtain ⟨j, hdiff, himg, hdisj⟩ := blockCore_diffeo_S28
    (componentFamily_S19 D ht (coreComp_S28 D ht c)) (D.truncation c).core
    (corePhiComp_S28 D ht hdom c)
    (Continuous.subtype_mk (corePhi_continuous_S28 D ht hdom c) _) hloc
    (fun x y hxy => Subtype.ext (corePhi_injective_S28 D ht hdom c (congrArg Subtype.val hxy)))
    (fun x hx => corePhi_not_zeroSet_S28 D ht hdom c hx)
    (fun y hy => corePhi_boundary_zeroSet_S28 D ht hdom c hy)
    (sliceDec_S28 D ht (coreComp_S28 D ht c)).components
  refine ⟨j, hdiff, ?_, fun j' hj' => ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz, hzx⟩ := himg.subset (mem_image_of_mem _ hx)
      exact ⟨z, hz, congrArg Subtype.val hzx⟩
    · rintro ⟨z, hz, rfl⟩
      have hmem : corePhiComp_S28 D ht hdom c z ∈
          coreImage_S28 (D.truncation c).core (corePhiComp_S28 D ht hdom c) := ⟨z, hz, rfl⟩
      obtain ⟨x, hx, hxz⟩ := himg.superset hmem
      exact ⟨x, hx, congrArg Subtype.val hxz⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨w, hw, hwe⟩
    exact Set.disjoint_left.mp (hdisj j' hj') ⟨x, hx, rfl⟩ ⟨w, hw, Subtype.ext hwe⟩

end Block

end GC.LongTime.Ch12
