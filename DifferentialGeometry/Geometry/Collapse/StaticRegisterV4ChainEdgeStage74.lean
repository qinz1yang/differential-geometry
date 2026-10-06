import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLinkValues74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSmoothBases
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCusp74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSmoothBasesEuclid
import DifferentialGeometry.Topology.Manifold.LinearChartMaps74

/-!
# Draft 74 §4.1 / G30: the actual edge stage `q₁ : parent → B₂` on the member (closed route)

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G30 (data skeleton of the rows' `EdgeBundle`, stage level).
The rows' edge bundle is the restriction of ONE actual stage to the chosen good open base
(`EdgeStage74` of the rows assembler); the stage itself, over the FULL final base `W₂`, is
produced here from the closed source `S`, its smooth stage bases `A` (G11 / G15) and the ONE
identification `M.ψ`:

* `edgeParent_R74 S`: the open ambient parent `M.ψ(U₂)` (`U₂` = FC33's threshold-5 edge domain,
  open in `X`, D74-2 row 4), inside the interior of `W` (`∂W = ∅`);
* `edgeProj_R74 S A : C(edgeParent, W₂)`: the FINAL map `q₁ ∘ M.ψ⁻¹` (D74-5) into the final base
  `W₂ = finalBase_BAS 1` with the model `EuclideanSpace ℝ (Fin 1)` (`A.edgeChartedSpace1`),
  `edgeProj_smooth_R74` (smooth INTO the manifold `W₂`: its coordinate expression is linear after
  the smooth block map, `contMDiff_into_linear_R74`) and **`edgeProj_submersion_R74`** (the
  chart-form threshold-5 submersion of D74-2 row 5 transfers to the abstract `W₂`: GAP (c) of G11
  closed — `dι ∘ dq₁ ≠ 0` and `dim W₂ = 1`);
* `edgeHeightP_R74`: the height `A/s ∘ M.ψ⁻¹` on the parent, smooth, with
  `ClosedRegisterV4.edgeLevel_R74` the level `4Δ`.

The cut-dependent fields of the rows' `EdgeBundle` (`fibre_disk` over the whole good base —
EDP04 `edp04_fibre_disk_EFE` plus base-level marker exactness —, `rank_two`, `proper`,
`cbase_compact`, `cbase_domain`) are NOT here: they are the EDP04 / EDP05 / FDC02 exits.
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

/-- The block space of the chain. -/
abbrev blockSpace_R74 : Type :=
  BlockSpace (fun _ : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
    S.F.family.toLocalChartPacketsC14.zero => ℝ²)

/-- FC33's threshold-5 edge domain `U₂` (open in `X`, the open ambient parent). -/
abbrev edgeDomain_R74 : Set M.X :=
  gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1

/-- **The open edge parent on `W`**: `M.ψ(U₂)`. -/
def edgeParent_R74 : TopologicalSpace.Opens W.Carrier :=
  ⟨M.ψ '' S.edgeDomain_R74,
    M.ψ.toHomeomorph.isOpenMap _ (isOpen_gafStageDomain5_R74 _ 1)⟩

theorem mem_edgeParent_R74 {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {x : W.Carrier} :
    x ∈ S.edgeParent_R74 ↔ M.ψ.symm x ∈ S.edgeDomain_R74 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rwa [M.ψ.symm_apply_apply]
  · intro h
    exact ⟨M.ψ.symm x, h, M.ψ.apply_symm_apply x⟩

/-- The edge parent lies in the interior of `W` (`∂W = ∅` from the model). -/
theorem edgeParent_interior_R74 : (S.edgeParent_R74 : Set W.Carrier) ⊆ W.interior := by
  have : BoundarylessManifold W.model W.Carrier :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty M.boundary_empty_R74
  intro x _
  exact BoundarylessManifold.isInteriorPoint

/-- The final projection on `W` at the image of a point of `X` is the final projection there. -/
theorem stageProjW_apply_R74 (j : Fin 3) (q : M.X) :
    S.stageProjW_R74 j (M.ψ q) = S.chain.toGaf02ChainE.cutQ_R74 j q := by
  change S.chain.toGaf02ChainE.cutQ_R74 j (M.ψ.symm (M.ψ q)) = _
  rw [M.ψ.symm_apply_apply]

/-- **The actual edge projection on the parent**: the final map `q₁ ∘ M.ψ⁻¹` into `W₂`. -/
def edgeProj_R74 (A : SmoothStageBases74 S) :
    C(S.edgeParent_R74, ↥(S.chain.toChain.finalBase_BAS 1)) where
  toFun x := ⟨S.stageProjW_R74 1 x.1,
    A.proj.mapsTo_final 1 ((mem_edgeParent_R74 (S := S)).1 x.2)⟩
  continuous_toFun :=
    ((S.stageProjW_smooth_R74 1).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem edgeProj_val_R74 (A : SmoothStageBases74 S) (x : S.edgeParent_R74) :
    ((S.edgeProj_R74 A x : ↥(S.chain.toChain.finalBase_BAS 1)) : BlockSpace
      (fun _ : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
        S.F.family.toLocalChartPacketsC14.zero => ℝ²)) = S.stageProjW_R74 1 x.1 :=
  rfl

/-- **`q₁ ∘ M.ψ⁻¹` is smooth into `W₂`** (model `EuclideanSpace ℝ (Fin 1)`). -/
theorem edgeProj_smooth_R74 (A : SmoothStageBases74 S) :
    letI := A.edgeChartedSpace1
    ContMDiff W.model (𝓡 1) ∞ (S.edgeProj_R74 A) := by
  let _ := A.edgeChartedSpace1
  have := A.edge_isManifold1.1
  refine contMDiff_into_linear_R74 (W := S.chain.toChain.finalBase_BAS 1) ?_
    (S.edgeProj_R74 A).continuous ?_
  · exact linearChartedSpace_R74_hlin _ _ _ _ _ _ _ _ _ _
  · exact (S.stageProjW_smooth_R74 1).comp contMDiff_subtype_val

/-- **The threshold-5 submersion on the abstract base** (G11 gap (c) closed): `q₁ ∘ M.ψ⁻¹` is a
submersion onto the one-dimensional manifold `W₂`. The chart-form submersion of D74-2 row 5
(`κ_j ∘ π₂E` at a point of `U₂`, with the linear chart `κ_j` of the marked piece) gives
`d(π₂E ∘ M.ψ⁻¹) ≠ 0` (a zero differential composed with `κ_j` and the invertible `dM.ψ` cannot be
onto `ℝ`), and a nonzero differential into the line `W₂` is onto. -/
theorem edgeProj_submersion_R74 (A : SmoothStageBases74 S) :
    letI := A.edgeChartedSpace1
    ∀ x : S.edgeParent_R74, Surjective (mfderiv W.model (𝓡 1) (S.edgeProj_R74 A) x) := by
  let _ := A.edgeChartedSpace1
  have hman := A.edge_isManifold1.1
  rintro ⟨y, hy⟩
  refine surjective_mfderiv_of_val_ne_zero_R74 (W := S.chain.toChain.finalBase_BAS 1)
    A.edge_isManifold1.2.1 (by simp) (S.edgeProj_smooth_R74 A) ⟨y, hy⟩ ?_
  intro hzero
  have hy' := hy
  obtain ⟨p, hp, hpx⟩ := hy'
  obtain ⟨j, hjb, hjc, hjh⟩ := hp
  obtain ⟨-, hsub⟩ := A.proj.edge_submersion j hjb hjc hjh
  subst hpx
  have hπ := ((S.stageProjW_smooth_R74 1) (M.ψ p)).mdifferentiableAt (by simp)
  have h0 := mfderiv_comp_subtype_val_R74 (I := W.model) S.edgeParent_R74
    (g := fun z : S.edgeParent_R74 => ((S.edgeProj_R74 A z : ↥(S.chain.toChain.finalBase_BAS 1)) :
      S.blockSpace_R74)) (fun _ => rfl) ⟨M.ψ p, hy⟩ hπ
  have h0' : mfderiv W.model 𝓘(ℝ, S.blockSpace_R74) (S.stageProjW_R74 1) (M.ψ p) = 0 :=
    h0.symm.trans hzero
  have hns := not_surjective_mfderiv_of_zero_R74 (ψ := (M.ψ : M.X → W.Carrier))
    (pr := S.stageProjW_R74 1)
    ((S.F.ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector _ _ j)) p
    (f := fun q => ((S.F.ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector _ _ j))
      (S.chain.toGaf02ChainE.cutQ_R74 1 q))
    (fun q => congrArg _ (S.stageProjW_apply_R74 1 q).symm) (M.ψ.mdifferentiable (by simp) p)
    hπ h0'
  exact hns hsub

/-- **The actual edge height on the parent**: `H_S ∘ M.ψ⁻¹` (`H_S = A/s`), restricted. -/
def edgeHeightP_R74 : S.edgeParent_R74 → ℝ :=
  fun x => S.edgeHeightW_R74 x.1

/-- The edge height on the parent is smooth. -/
theorem edgeHeightP_smooth_R74 : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ S.edgeHeightP_R74 :=
  S.edgeHeightW_smooth_R74.comp contMDiff_subtype_val

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
