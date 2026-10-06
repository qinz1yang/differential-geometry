import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialPreparedRows
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageOfBundlesModels74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankKernel74

/-!
# Draft 74, G5 (X135 radial `D² × S¹`): the slim stage, the cut choice and the slim pieces

Lane S-JUNCTIONS2 (suffix `_JN74`). The solid torus `X135Radial.carrier` with the X135 decomposition
(cusp collar `h ≥ -1/4`, slim band `-1/2 ≤ h ≤ -1/4`, circle region `-3/4 ≤ h ≤ -1/2`, edge core
`h ≤ -3/4`, no zero domain) as a smooth stage geometry: the slim stage is the height
`h : {-1 < h < 0} → ℝ¹` (a submersion), the edge and circle stages are those of the X135 edge and
circle bundles (`SmoothStageGeometry74.ofBundles74`), the cut choice takes
`K₃ = D₃ = {-1/2 ≤ h ≤ -1/4}` and the whole bases. The slim cut pieces are the X135 slim pieces
`radialSlims` (one torus interval).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierCharts_StageSlimJN74 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_StageSlimJN74 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-- The identification of `ℝ` with the one-dimensional model space. -/
def e1Equiv74 : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- The slim stage projection: the height, as a point of `ℝ¹`. -/
def radialSlimProj74 : C(radialCircleDomain, EuclideanSpace ℝ (Fin 1)) where
  toFun x := e1Equiv74 (height x.1)
  continuous_toFun := e1Equiv74.continuous.comp (height_continuous.comp continuous_subtype_val)

theorem radialSlimProj74_smooth : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ radialSlimProj74 :=
  (e1Equiv74.contDiff.contMDiff).comp (height_smooth.comp contMDiff_subtype_val)

theorem radialSlimProj74_submersion (x : radialCircleDomain) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1) radialSlimProj74 x) := by
  have hreg := carrier_height_regular x.1 ⟨x.2.1, x.2.2.trans zero_lt_one⟩
  have hh := DifferentialGeometry.mfderiv_restrict_open (I := 𝓡∂ 3) (J := 𝓘(ℝ, ℝ)) height
    radialCircleDomain x
  have hsm : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (fun y : radialCircleDomain => height y.1) :=
    height_smooth.comp contMDiff_subtype_val
  have hhd : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ, ℝ) (fun y : radialCircleDomain => height y.1) x :=
    hsm.mdifferentiableAt (by decide)
  have hLs : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (e1Equiv74 : ℝ → EuclideanSpace ℝ (Fin 1)) :=
    e1Equiv74.contDiff.contMDiff
  have hL : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) (e1Equiv74 : ℝ → EuclideanSpace ℝ (Fin 1))
      (height x.1) := hLs.mdifferentiableAt (by decide)
  have hc := mfderiv_comp x hL hhd
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (e1Equiv74 : ℝ → EuclideanSpace ℝ (Fin 1)) (height x.1) =
      (e1Equiv74 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) := by
    rw [mfderiv_eq_fderiv]
    exact ContinuousLinearEquiv.fderiv e1Equiv74
  have hsurj :
      Surjective (mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) (fun y : radialCircleDomain => height y.1) x) := by
    rw [hh]
    exact surjective_of_ne_zero_JN74 hreg
  intro v
  obtain ⟨u, hu⟩ := hsurj (e1Equiv74.symm v)
  refine ⟨u, ?_⟩
  change (mfderiv (𝓡∂ 3) (𝓡 1) ((e1Equiv74 : ℝ → EuclideanSpace ℝ (Fin 1)) ∘
    fun y : radialCircleDomain => height y.1) x) u = v
  rw [hc, hd]
  change e1Equiv74 (mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) (fun y : radialCircleDomain => height y.1) x u) = v
  rw [hu]
  exact e1Equiv74.apply_symm_apply v

/-- **The slim stage of the radial solid torus**: `f₃ = h` on `{-1 < h < 0}`. -/
def radialSlimStage74 : SlimStage74 carrier where
  Base := EuclideanSpace ℝ (Fin 1)
  parent := radialCircleDomain
  parent_interior := radialCircleBundle.domain_interior
  proj := radialSlimProj74
  proj_smooth := radialSlimProj74_smooth
  proj_submersion := radialSlimProj74_submersion
  C₃ := univ
  slabImage := ∅
  facePoints := ∅

/-- The compact slim base domain `K₃ = D₃ = [-1/2, -1/4]`. -/
def radialK3_74 : Set (EuclideanSpace ℝ (Fin 1)) :=
  e1Equiv74 '' Icc (-(1 / 2 : ℝ)) (-(1 / 4 : ℝ))

theorem radialK3_74_compact : IsCompact radialK3_74 :=
  isCompact_Icc.image e1Equiv74.continuous

theorem radialK3_74_connected : IsPreconnected radialK3_74 :=
  (isPreconnected_Icc).image _ e1Equiv74.continuous.continuousOn

/-- The stage geometry of the radial solid torus. -/
def radialStage74 : SmoothStageGeometry74 carrier boundary :=
  SmoothStageGeometry74.ofBundles74 radialZeros radialCuspCores radialSlimStage74
    radialEdgeBundle radialCircleBundle

/-- The cut choice of the radial solid torus: slim base `[-1/2, -1/4]`, the whole edge and circle
bases. -/
def radialCut74 : StageCutChoice74 radialStage74 :=
  StageCutChoice74.ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm
    (by
      change (∅ : Set (EuclideanSpace ℝ (Fin 1))) ∪ ∅ ⊆ interior radialK3_74
      simp)
    (disjoint_empty _)

/-- The slim set of the cut is the union of the X135 slim pieces. -/
theorem radialCut74_slimSet : radialCut74.slimSet = radialSlims.union := by
  rw [radial_slim_union, slimToCarrier_range]
  ext x
  constructor
  · rintro ⟨hx, t, ht, hte⟩
    have h : t = height x := e1Equiv74.injective hte
    rw [h] at ht
    exact ht
  · intro hx
    obtain ⟨hlo, hhi⟩ := hx
    refine ⟨⟨by linarith, by linarith⟩, height x, ⟨hlo, hhi⟩, rfl⟩

end GC.GraphManifold.Assembly.FC39P0.X135Radial
