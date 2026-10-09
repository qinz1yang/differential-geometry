import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceTorusFamilyStage_S19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationMain

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic
  GC.LongTime.CuspP1 GC.Endpoint DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

section Restrict

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N]

/-- Restriction of a collar whose image lies in an open subset `U` to a collar in `U`. -/
def restrictCollar_S19 (U : Opens N) (hU : Nonempty U)
    (σ : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) N ∞) :
    PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) U ∞ :=
  σ.trans (PartialDiffeomorph.subtypeVal (I := 𝓡 3) U hU).symm

theorem restrictCollar_source_S19 (U : Opens N) (hU : Nonempty U)
    (σ : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) N ∞)
    (h : σ.target ⊆ (U : Set N)) : (restrictCollar_S19 U hU σ).source = σ.source := by
  change σ.source ∩ σ ⁻¹' ((PartialDiffeomorph.subtypeVal (I := 𝓡 3) U hU).symm).source = _
  refine inter_eq_left.mpr fun p hp => ?_
  have : σ p ∈ U := h (σ.map_source hp)
  simpa [PartialDiffeomorph.subtypeVal] using this

theorem restrictCollar_apply_S19 (U : Opens N) (hU : Nonempty U)
    (σ : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) N ∞)
    (h : σ.target ⊆ (U : Set N)) (p : Torus × ℝ) (hp : p ∈ σ.source) :
    ((restrictCollar_S19 U hU σ p : U) : N) = σ p := by
  have hy : σ p ∈ U := h (σ.map_source hp)
  have e : ((PartialDiffeomorph.subtypeVal (I := 𝓡 3) U hU).symm (σ p) : U) = ⟨σ p, hy⟩ := by
    apply Subtype.ext
    have := (U.openPartialHomeomorphSubtypeCoe hU).right_inv
      (show σ p ∈ (U.openPartialHomeomorphSubtypeCoe hU).target by simpa using hy)
    simpa [PartialDiffeomorph.subtypeVal] using this
  change (((PartialDiffeomorph.subtypeVal (I := 𝓡 3) U hU).symm (σ p) : U) : N) = _
  rw [e]

theorem restrictCollar_target_S19 (U : Opens N) (hU : Nonempty U)
    (σ : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) N ∞) :
    ∀ z ∈ (restrictCollar_S19 U hU σ).target, (z : N) ∈ σ.target := by
  intro z hz
  have : z ∈ ((PartialDiffeomorph.subtypeVal (I := 𝓡 3) U hU).symm).target ∧
      ((PartialDiffeomorph.subtypeVal (I := 𝓡 3) U hU).symm).symm z ∈ σ.target := hz
  simpa [PartialDiffeomorph.subtypeVal] using this.2

end Restrict

section Component

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} {t : ℝ}
  (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)

theorem stageCollar_target_nonempty_S19 (x : SliceIdx_S19 D) :
    (stageCollar_S19 D ht x).target.Nonempty := by
  have hs : (@Classical.choice Torus nonemptyTorus_S19, (0 : ℝ)) ∈
      (stageCollar_S19 D ht x).source := by
    rw [stageCollar_source_S19]; exact zero_mem_source_S19 _
  exact ⟨_, (stageCollar_S19 D ht x).map_source hs⟩

theorem isPreconnected_stageCollar_target_S19 (x : SliceIdx_S19 D) :
    IsPreconnected (stageCollar_S19 D ht x).target := by
  rw [← (stageCollar_S19 D ht x).image_source_eq_target, stageCollar_source_S19]
  have h1 : IsPreconnected (signedCollarSource : Set (Torus × ℝ)) := by
    have : signedCollarSource = (univ : Set Torus) ×ˢ Ioo (-1 : ℝ) 1 := by
      ext p; simp [signedCollarSource]
    rw [this]
    exact isPreconnected_univ.prod isPreconnected_Ioo
  refine h1.image _ ?_
  have := (stageCollar_S19 D ht x).contMDiffOn_toFun.continuousOn
  rwa [stageCollar_source_S19] at this

/-- The connected component of the slice stage containing the `x`-th seam collar. -/
def comp_S19 (x : SliceIdx_S19 D) : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier :=
  ConnectedComponents.mk (stageCollar_target_nonempty_S19 D ht x).some

theorem stageCollar_target_subset_comp_S19 (x : SliceIdx_S19 D) :
    (stageCollar_S19 D ht x).target ⊆
      ClosedOrientedManifold.componentSet (postStage F.observation t).toClosedOrientedManifold
        (comp_S19 D ht x) := by
  intro y hy
  change ConnectedComponents.mk y = ConnectedComponents.mk _
  exact ConnectedComponents.coe_eq_coe'.mpr
    ((isPreconnected_stageCollar_target_S19 D ht x).subset_connectedComponent
      (stageCollar_target_nonempty_S19 D ht x).some_mem hy)

/-- Seam collars living in the component `C`. -/
abbrev CIdx_S19 (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier) : Type :=
  {x : SliceIdx_S19 D // comp_S19 D ht x = C}

theorem cidx_target_subset_S19 {C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier}
    (x : CIdx_S19 D ht C) :
    (stageCollar_S19 D ht x.1).target ⊆
      ClosedOrientedManifold.componentSet (postStage F.observation t).toClosedOrientedManifold C := by
  intro y hy
  have := stageCollar_target_subset_comp_S19 D ht x.1 hy
  rw [x.2] at this
  exact this

theorem cidx_nonempty_S19 {C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier}
    (x : CIdx_S19 D ht C) :
    Nonempty (ClosedOrientedManifold.componentOpen
      (postStage F.observation t).toClosedOrientedManifold C) :=
  ⟨⟨(stageCollar_target_nonempty_S19 D ht x.1).some,
    cidx_target_subset_S19 D ht x (stageCollar_target_nonempty_S19 D ht x.1).some_mem⟩⟩

/-- Enumeration of the seam collars of the component `C`. -/
def cidxEquiv_S19 (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier) :
    CIdx_S19 D ht C ≃ Fin (Nat.card (CIdx_S19 D ht C)) :=
  haveI : Finite (CIdx_S19 D ht C) := inferInstance
  Finite.equivFin _

/-- The family of seam collars of the component `C`, as a collar family in `C` itself. -/
def componentFamily_S19 (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier) :
    CollaredTorusFamily_C2a
      ((postStage F.observation t).toClosedOrientedManifold.component C).Carrier where
  count := Nat.card (CIdx_S19 D ht C)
  collar := fun k =>
    restrictCollar_S19 _ (cidx_nonempty_S19 D ht ((cidxEquiv_S19 D ht C).symm k))
      (stageCollar_S19 D ht ((cidxEquiv_S19 D ht C).symm k).1)
  source_eq := fun k => by
    exact (restrictCollar_source_S19 _ _ _ (cidx_target_subset_S19 D ht _)).trans
      (stageCollar_source_S19 D ht _)
  disjoint := fun k l hkl => by
    refine Set.disjoint_left.mpr fun z hz1 hz2 => ?_
    have h1 := restrictCollar_target_S19 _ _ _ z hz1
    have h2 := restrictCollar_target_S19 _ _ _ z hz2
    refine Set.disjoint_left.mp (stageCollar_disjoint_S19 D ht (x := _) (y := _) ?_) h1 h2
    intro h
    exact hkl ((cidxEquiv_S19 D ht C).symm.injective (Subtype.ext h))

/-- **C2c, one component of the slice.** The seam collars lying in the component `C` are the seam
family of a torus decomposition of `C`: the seam torus `e x` is the stage image of the `x`-th
collar at `s = 0`. -/
theorem componentTorusDecomposition_S19
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier) :
    ∃ (G : GC.Topology.TorusDecomposition
        ((postStage F.observation t).toClosedOrientedManifold.component C))
      (e : CIdx_S19 D ht C ≃ Fin G.boundary.count),
      ∀ (x : CIdx_S19 D ht C) (p : Torus),
        ((G.reconstructionAtlas.torusInPrime G.reconstruction (e x) p).val :
          (postStage F.observation t).Carrier) = stageCollar_S19 D ht x.1 (p, 0) := by
  obtain ⟨G, e0, -, h0, -⟩ := cutAlongTori_C2a_S12
    ((postStage F.observation t).toClosedOrientedManifold.component C)
    (componentFamily_S19 D ht C)
  refine ⟨G, (cidxEquiv_S19 D ht C).trans e0, fun x p => ?_⟩
  have h := h0 (cidxEquiv_S19 D ht C x) p
  have key : ∀ k : Fin (componentFamily_S19 D ht C).count,
      ((((componentFamily_S19 D ht C).collar k) (p, 0)).val : (postStage F.observation t).Carrier) =
        stageCollar_S19 D ht ((cidxEquiv_S19 D ht C).symm k).1 (p, 0) := fun k =>
    restrictCollar_apply_S19 _ _ _ (cidx_target_subset_S19 D ht _) (p, 0)
      (by rw [stageCollar_source_S19]; exact zero_mem_source_S19 p)
  have key' := key (cidxEquiv_S19 D ht C x)
  rw [Equiv.symm_apply_apply] at key'
  exact (congrArg Subtype.val h).trans key'

/-- **C2c main theorem (slice torus decomposition).** For the level-`S` truncation data `D` of the
persistent cores at a late time `t ≥ start`, every connected component `C` of the slice stage carries
a `TorusDecomposition` `G C`, and the boundary tori of all `G C` are in bijection `port` with the
cusp tori `Σ i, Fin (D.truncation i).count` of the truncations, such that the seam torus is exactly
the stage image under `cores.map · t` of the truncation's boundary torus
(`LateCutFamily.port` / `seam_image` data, up to the stage-transport `HEq` adapter). -/
theorem sliceTorusDecomposition_S19 :
    ∃ (G : ∀ C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier,
        GC.Topology.TorusDecomposition
          ((postStage F.observation t).toClosedOrientedManifold.component C))
      (port : (Σ C, Fin (G C).boundary.count) ≃ Σ i : Fin cores.count, Fin (D.truncation i).count),
      ∀ C (s : Fin (G C).boundary.count) (p : Torus),
        ((G C).reconstructionAtlas.torusInPrime (G C).reconstruction s p).val =
          cores.map (port ⟨C, s⟩).1 t ht
            ((D.truncation (port ⟨C, s⟩).1).cuspMap (port ⟨C, s⟩).2 (p, halfZero)) := by
  choose G e hG using fun C => componentTorusDecomposition_S19 D ht C
  refine ⟨G, (Equiv.sigmaCongrRight fun C => (e C).symm).trans
    (Equiv.sigmaFiberEquiv (comp_S19 D ht)), fun C s p => ?_⟩
  have h := hG C ((e C).symm s) p
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  exact stageCollar_zero_S19 D ht _ p

end Component

end GC.LongTime.Ch12
