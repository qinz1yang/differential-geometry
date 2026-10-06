import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeStage74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRestrictOCL

/-!
# Draft 74 CL0, G2: the actual slim stage `f₃ : parent → W₃` on the member (closed route)

Lane O-CL0 (`_OCL`), G2. The closed route's slim stage of the rows assembler (draft 74 §4.1,
`SlimStage74`), produced from the closed source `S`, its smooth stage bases `A` (D74-2, G11 /
G15) and the ONE identification `M.ψ`, in the same way as lane S-REG-CHAIN2's edge stage (G30):

* `slimParent_OCL S`: the open ambient parent `M.ψ(U₃)` (`U₃` = FC33's threshold-5 slim domain,
  open in `X`, D74-2 row 4), inside the interior of `W` (`∂W = ∅`);
* `slimProj_OCL S A : C(slimParent, W₃)`: the FINAL map `f₃ ∘ M.ψ⁻¹` (`f₃ = π₃ ∘ E`,
  `slimMap_ZSP35`) into the final slim base `W₃ = finalBase_BAS 2` with the model
  `EuclideanSpace ℝ (Fin 1)` (`A.slimChartedSpace1`), `slimProj_smooth_OCL` (smooth into the
  manifold `W₃`) and **`slimProj_submersion_OCL`** (D74-2 row 5's chart-form threshold-5
  submersion transfers to the abstract `W₃`);
* `slimStageProj_OCL S A : StageProj74 W 1` (the stage over the whole final base `W₃`).

The rows read the stage RESTRICTED to the good open base `W₃ ∩ R₃` (`StageProj74.restrictStage_OCL`,
G2 of this lane), where every fibre lies in `U₃` (GAF07's slim localization).
Universe: `W : CompactCarrier.{0}` (the base is a subtype of the block space, `Type 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
  (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)

/-- FC33's threshold-5 slim domain `U₃` (open in `X`). -/
abbrev slimDomain_OCL : Set M.X :=
  gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 2

/-- **The open slim parent on `W`**: `M.ψ(U₃)`. -/
def slimParent_OCL : TopologicalSpace.Opens W.Carrier :=
  ⟨M.ψ '' S.slimDomain_OCL,
    M.ψ.toHomeomorph.isOpenMap _ (isOpen_gafStageDomain5_R74 _ 2)⟩

theorem mem_slimParent_OCL {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {x : W.Carrier} :
    x ∈ S.slimParent_OCL ↔ M.ψ.symm x ∈ S.slimDomain_OCL := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rwa [M.ψ.symm_apply_apply]
  · intro h
    exact ⟨M.ψ.symm x, h, M.ψ.apply_symm_apply x⟩

/-- The slim parent lies in the interior of `W` (`∂W = ∅` from the model). -/
theorem slimParent_interior_OCL : (S.slimParent_OCL : Set W.Carrier) ⊆ W.interior := by
  have : BoundarylessManifold W.model W.Carrier :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty M.boundary_empty_R74
  intro x _
  exact BoundarylessManifold.isInteriorPoint

/-- **The actual slim projection on the parent**: the final map `f₃ ∘ M.ψ⁻¹` into `W₃`. -/
def slimProj_OCL (A : SmoothStageBases74 S) :
    C(S.slimParent_OCL, ↥(S.chain.toChain.finalBase_BAS 2)) where
  toFun x := ⟨S.stageProjW_R74 2 x.1,
    A.proj.mapsTo_final 2 ((mem_slimParent_OCL (S := S)).1 x.2)⟩
  continuous_toFun :=
    ((S.stageProjW_smooth_R74 2).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem slimProj_val_OCL (A : SmoothStageBases74 S) (x : S.slimParent_OCL) :
    ((S.slimProj_OCL A x : ↥(S.chain.toChain.finalBase_BAS 2)) : S.blockSpace_R74) =
      S.stageProjW_R74 2 x.1 :=
  rfl

/-- **`f₃ ∘ M.ψ⁻¹` is smooth into `W₃`** (model `EuclideanSpace ℝ (Fin 1)`). -/
theorem slimProj_smooth_OCL (A : SmoothStageBases74 S) :
    letI := A.slimChartedSpace1
    ContMDiff W.model (𝓡 1) ∞ (S.slimProj_OCL A) := by
  let _ := A.slimChartedSpace1
  have := A.slim_isManifold1.1
  refine contMDiff_into_linear_R74 (W := S.chain.toChain.finalBase_BAS 2) ?_
    (S.slimProj_OCL A).continuous ?_
  · exact linearChartedSpace_R74_hlin _ _ _ _ _ _ _ _ _ _
  · exact (S.stageProjW_smooth_R74 2).comp contMDiff_subtype_val

/-- **The threshold-5 slim submersion on the abstract base**: `f₃ ∘ M.ψ⁻¹` is a submersion onto
the one-dimensional manifold `W₃` (D74-2 row 5 in chart form: `κ_j ∘ π₃E` is a submersion at a
point of `U₃`; a zero differential composed with `κ_j` and `dM.ψ` could not be onto `ℝ`). -/
theorem slimProj_submersion_OCL (A : SmoothStageBases74 S) :
    letI := A.slimChartedSpace1
    ∀ x : S.slimParent_OCL, Surjective (mfderiv W.model (𝓡 1) (S.slimProj_OCL A) x) := by
  let _ := A.slimChartedSpace1
  have hman := A.slim_isManifold1.1
  rintro ⟨y, hy⟩
  refine surjective_mfderiv_of_val_ne_zero_R74 (W := S.chain.toChain.finalBase_BAS 2)
    A.slim_isManifold1.2.1 (by simp) (S.slimProj_smooth_OCL A) ⟨y, hy⟩ ?_
  intro hzero
  have hy' := hy
  obtain ⟨p, hp, hpx⟩ := hy'
  obtain ⟨j, hjb, hjc⟩ := hp
  obtain ⟨-, hsub⟩ := A.proj.slim_submersion j hjb hjc
  subst hpx
  have hπ := ((S.stageProjW_smooth_R74 2) (M.ψ p)).mdifferentiableAt (by simp)
  have h0 := mfderiv_comp_subtype_val_R74 (I := W.model) S.slimParent_OCL
    (g := fun z : S.slimParent_OCL => ((S.slimProj_OCL A z : ↥(S.chain.toChain.finalBase_BAS 2)) :
      S.blockSpace_R74)) (fun _ => rfl) ⟨M.ψ p, hy⟩ hπ
  have h0' : mfderiv W.model 𝓘(ℝ, S.blockSpace_R74) (S.stageProjW_R74 2) (M.ψ p) = 0 :=
    h0.symm.trans hzero
  have hns := not_surjective_mfderiv_of_zero_R74 (ψ := (M.ψ : M.X → W.Carrier))
    (pr := S.stageProjW_R74 2)
    ((S.F.ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector _ _ j)) p
    (f := fun q => ((S.F.ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector _ _ j))
      (S.chain.toGaf02ChainE.cutQ_R74 2 q))
    (fun q => congrArg _ (S.stageProjW_apply_R74 2 q).symm) (M.ψ.mdifferentiable (by simp) p)
    hπ h0'
  exact hns hsub

/-- **The closed-route slim stage over the whole final base** `W₃` (`StageProj74 W 1`). -/
def slimStageProj_OCL (A : SmoothStageBases74 S) : StageProj74 W 1 where
  Base := ↥(S.chain.toChain.finalBase_BAS 2)
  baseCharts := A.slimChartedSpace1
  baseSmooth := A.slim_isManifold1.1
  parent := S.slimParent_OCL
  parent_interior := S.slimParent_interior_OCL
  proj := S.slimProj_OCL A
  proj_smooth := S.slimProj_smooth_OCL A
  proj_submersion := S.slimProj_submersion_OCL A

/-- The slim stage is identified with `f₃ = π₃ ∘ E` on its parent `M.ψ(U₃)`. -/
theorem slimStageProj_ident_OCL (A : SmoothStageBases74 S) :
    StageIdentU_LND74 M.ψ.toEquiv (S.slimStageProj_OCL A) S.chain.slimMap_ZSP35
      (fun b : ↥(S.chain.toChain.finalBase_BAS 2) => (b : S.blockSpace_R74)) S.slimDomain_OCL where
  emb := Topology.IsEmbedding.subtypeVal
  proj_eq := fun x => by
    change S.stageProjW_R74 2 x.1 = S.chain.slimMap_ZSP35 (M.ψ.symm x.1)
    rfl
  parent_eq := rfl

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
