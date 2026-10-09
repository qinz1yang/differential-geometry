import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeStage74
import DifferentialGeometry.Topology.Manifold.LinearChartSurj74

/-!
# Draft 74 §4.1 / G31: the actual circle stage `q₀ : parent → W₁` on the member (closed route)

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G31, the circle analogue of
`StaticRegisterV4ChainEdgeStage74` (stage level; the circle bundle's cut-dependent fields — local
trivializations over the good base, whole-circle properness, `cbase`, saturation of `M₃` — are the
C0 / FDC03 exits). Over the FULL final base `W₁ = finalBase_BAS 0` (model `𝓡 2`,
`A.circleChartedSpace`):

* `circleParent_R74 S := M.ψ(U₁)` (FC33's threshold-5 circle domain, open) inside `int W`;
* `circleProj_R74 S A : C(circleParent, W₁)`, the FINAL map `q₀ ∘ M.ψ⁻¹`, smooth into `W₁`
  (`circleProj_smooth_R74`) and a submersion onto the abstract surface `W₁`
  (`circleProj_submersion_R74`: the chart-form threshold-5 submersion `κ_j ∘ π₁E` of D74-2 row 5
  transfers because `dim W₁ = 2 = dim ℝ²`, `LinearChartSurj74`).
Universe: `W : CompactCarrier.{0}`.
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

/-- FC33's threshold-5 circle domain `U₁` (open in `X`). -/
abbrev circleDomain_R74 : Set M.X :=
  gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 0

/-- **The open circle parent on `W`**: `M.ψ(U₁)`. -/
def circleParent_R74 : TopologicalSpace.Opens W.Carrier :=
  ⟨M.ψ '' S.circleDomain_R74,
    M.ψ.toHomeomorph.isOpenMap _ (isOpen_gafStageDomain5_R74 _ 0)⟩

theorem mem_circleParent_R74 {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {x : W.Carrier} :
    x ∈ S.circleParent_R74 ↔ M.ψ.symm x ∈ S.circleDomain_R74 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rwa [M.ψ.symm_apply_apply]
  · intro h
    exact ⟨M.ψ.symm x, h, M.ψ.apply_symm_apply x⟩

/-- The circle parent lies in the interior of `W` (`∂W = ∅` from the model). -/
theorem circleParent_interior_R74 : (S.circleParent_R74 : Set W.Carrier) ⊆ W.interior := by
  have : BoundarylessManifold W.model W.Carrier :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty M.boundary_empty_R74
  intro x _
  exact BoundarylessManifold.isInteriorPoint

/-- **The actual circle projection on the parent**: the final map `q₀ ∘ M.ψ⁻¹` into `W₁`. -/
def circleProj_R74 (A : SmoothStageBases74 S) :
    C(S.circleParent_R74, ↥(S.chain.toChain.finalBase_BAS 0)) where
  toFun x := ⟨S.stageProjW_R74 0 x.1,
    A.proj.mapsTo_final 0 ((mem_circleParent_R74 (S := S)).1 x.2)⟩
  continuous_toFun :=
    ((S.stageProjW_smooth_R74 0).continuous.comp continuous_subtype_val).subtype_mk _

/-- **`q₀ ∘ M.ψ⁻¹` is smooth into `W₁`** (model `𝓡 2`). -/
theorem circleProj_smooth_R74 (A : SmoothStageBases74 S) :
    letI := A.circleChartedSpace
    ContMDiff W.model (𝓡 2) ∞ (S.circleProj_R74 A) := by
  let _ := A.circleChartedSpace
  have := A.circle_isManifold.1
  refine contMDiff_into_linear_R74 (W := S.chain.toChain.finalBase_BAS 0) ?_
    (S.circleProj_R74 A).continuous ?_
  · exact linearChartedSpace_R74_hlin _ _ _ _ _ _ _ _ _ _
  · exact (S.stageProjW_smooth_R74 0).comp contMDiff_subtype_val

/-- **The threshold-5 submersion on the abstract surface `W₁`**: the chart-form submersion of
D74-2 row 5 (`κ_j ∘ π₁E` onto `ℝ²` at a point of `U₁`) transfers to `q₀ ∘ M.ψ⁻¹ : parent → W₁`. -/
theorem circleProj_submersion_R74 (A : SmoothStageBases74 S) :
    letI := A.circleChartedSpace
    ∀ x : S.circleParent_R74, Surjective (mfderiv W.model (𝓡 2) (S.circleProj_R74 A) x) := by
  let _ := A.circleChartedSpace
  have hman := A.circle_isManifold.1
  rintro ⟨y, hy⟩
  have hy' := hy
  obtain ⟨p, hp, hpx⟩ := hy'
  obtain ⟨j, hjb, hjc⟩ := hp
  obtain ⟨-, hsub⟩ := A.proj.circle_submersion j hjb hjc
  subst hpx
  let κ : S.blockSpace_R74 →L[ℝ] ℝ² := (S.F.ρ j.1)⁻¹ • gafCircleVector _ j
  have hg : MDifferentiableAt W.model 𝓘(ℝ, ℝ²) (fun y' => κ (S.stageProjW_R74 0 y')) (M.ψ p) :=
    (κ.contDiff.contMDiff.comp (S.stageProjW_smooth_R74 0) (M.ψ p)).mdifferentiableAt (by simp)
  have hgs := surjective_mfderiv_of_comp_surjective_R74 (ψ := (M.ψ : M.X → W.Carrier))
    (g := fun y' => κ (S.stageProjW_R74 0 y')) p
    (f := fun q => κ (S.chain.toGaf02ChainE.cutQ_R74 0 q))
    (fun q => congrArg κ (S.stageProjW_apply_R74 0 q).symm) (M.ψ.mdifferentiable (by simp) p) hg
    hsub
  have hgs' := surjective_mfderiv_subtype_val_R74 (I := W.model) S.circleParent_R74
    (g := fun z : S.circleParent_R74 =>
      κ ((S.circleProj_R74 A z : ↥(S.chain.toChain.finalBase_BAS 0)) : S.blockSpace_R74))
    (f := fun y' => κ (S.stageProjW_R74 0 y')) (fun _ => rfl) ⟨M.ψ p, hy⟩ hg hgs
  exact surjective_mfderiv_of_coord_surjective_R74 A.circle_isManifold.2.1 κ
    (S.circleProj_smooth_R74 A) ⟨M.ψ p, hy⟩ hgs'

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
