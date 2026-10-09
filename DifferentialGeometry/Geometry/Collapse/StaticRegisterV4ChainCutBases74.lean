import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLinkValues74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSmoothBases
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSmoothBasesEuclid

/-!
# The cut choice's open bases as smooth manifolds (the rows' `EdgeBundle.Base`, `CircleBundle.Base`)

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G15 (closed binding). D74-11 / D74-13: the rows' `Base`
is the SUBTYPE of the chosen open good neighbourhood; D74-5: `edgeBaseIdent` /
`circleBaseIdent` identify the rows' bases with `D.edgeBaseOpen` / `D.circleBaseOpen`. Here the two
open neighbourhoods of a cut choice `D` become open subsets of the actual final bases `W₂`, `W₁`
(relative openness, field of `D`), and with the smooth stage bases `A` (G11; for the edge in the
rows' model `EuclideanSpace ℝ (Fin 1)`, G15 kernel) they are smooth manifolds of the models the
rows require (`𝓡 1`, `𝓡 2`), Hausdorff:

* `ClosedCutChoice74.edgeBaseOpens_R74`, `circleBaseOpens_R74` (`Opens` of `W₂`, `W₁`) with
  `edgeBaseOpens_val_R74` / `circleBaseOpens_val_R74` (their points are exactly the chosen sets);
* `ClosedCutChoice74.edgeBase_isManifold_R74` (`IsManifold (𝓡 1) ∞`), `circleBase_isManifold_R74`
  (`IsManifold (𝓡 2) ∞`), and the actual compact bases `C₂`, `C₁` lie in them.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedCutChoice74

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
  {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}

/-- The open edge base of the choice as an open subset of `W₂`. -/
def edgeBaseOpens_R74 (D : ClosedCutChoice74 S B) :
    TopologicalSpace.Opens (S.chain.toChain.finalBase_BAS 1) :=
  ⟨Subtype.val ⁻¹' D.edgeBaseOpen, by
    obtain ⟨G, hG, hGe⟩ := D.edgeBaseOpen_rel
    refine isOpen_induced_iff.mpr ⟨G, hG, ?_⟩
    ext x
    rw [← hGe]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩⟩

/-- The open circle base of the choice as an open subset of `W₁`. -/
def circleBaseOpens_R74 (D : ClosedCutChoice74 S B) :
    TopologicalSpace.Opens (S.chain.toChain.finalBase_BAS 0) :=
  ⟨Subtype.val ⁻¹' D.circleBaseOpen, by
    obtain ⟨G, hG, hGe⟩ := D.circleBaseOpen_rel
    refine isOpen_induced_iff.mpr ⟨G, hG, ?_⟩
    ext x
    rw [← hGe]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩⟩

/-- The points of the edge base opens are exactly the chosen open edge base. -/
theorem edgeBaseOpens_val_R74 (D : ClosedCutChoice74 S B) :
    Subtype.val '' (D.edgeBaseOpens_R74 : Set (S.chain.toChain.finalBase_BAS 1)) =
      D.edgeBaseOpen := by
  rw [edgeBaseOpens_R74, TopologicalSpace.Opens.coe_mk, Subtype.image_preimage_coe,
    inter_eq_right.mpr D.edgeBaseOpen_subset]

/-- The points of the circle base opens are exactly the chosen open circle base. -/
theorem circleBaseOpens_val_R74 (D : ClosedCutChoice74 S B) :
    Subtype.val '' (D.circleBaseOpens_R74 : Set (S.chain.toChain.finalBase_BAS 0)) =
      D.circleBaseOpen := by
  rw [circleBaseOpens_R74, TopologicalSpace.Opens.coe_mk, Subtype.image_preimage_coe,
    inter_eq_right.mpr D.circleBaseOpen_subset]

/-- **The rows' edge base is a smooth `𝓡 1`-manifold** (open subset of `W₂` in the rows' model),
and the actual compact edge base `C₂` lies in it. -/
theorem edgeBase_isManifold_R74 (D : ClosedCutChoice74 S B) (A : SmoothStageBases74 S) :
    (let _ := A.edgeChartedSpace1
     IsManifold (𝓡 1) ∞ D.edgeBaseOpens_R74) ∧
      D.C₂ ⊆ Subtype.val '' (D.edgeBaseOpens_R74 : Set (S.chain.toChain.finalBase_BAS 1)) := by
  refine ⟨?_, ?_⟩
  · let _ := A.edgeChartedSpace1
    have := A.edge_isManifold1.1
    infer_instance
  · rw [edgeBaseOpens_val_R74]
    exact D.edgeBaseOpen_sub

/-- **The rows' circle base is a smooth `𝓡 2`-manifold** (open subset of `W₁`), and the actual
compact circle base `C₁` lies in it. -/
theorem circleBase_isManifold_R74 (D : ClosedCutChoice74 S B) (A : SmoothStageBases74 S) :
    (let _ := A.circleChartedSpace
     IsManifold (𝓡 2) ∞ D.circleBaseOpens_R74) ∧
      D.C₁ ⊆ Subtype.val '' (D.circleBaseOpens_R74 : Set (S.chain.toChain.finalBase_BAS 0)) := by
  refine ⟨?_, ?_⟩
  · let _ := A.circleChartedSpace
    have := A.circle_isManifold.1
    infer_instance
  · rw [circleBaseOpens_val_R74]
    exact D.circleBaseOpen_sub

end ClosedCutChoice74

end DifferentialGeometry.Geometry.Collapse
