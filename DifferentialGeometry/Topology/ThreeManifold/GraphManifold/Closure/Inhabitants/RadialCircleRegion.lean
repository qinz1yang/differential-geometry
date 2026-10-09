import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialCircleRounding

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_RegionX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_RegionX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialCircleTopBase : TopologicalSpace.Opens radialCircleBase := ⊤
def radialCircleTopDomain : TopologicalSpace.Opens radialCircleDomain :=
  TopologicalSpace.Opens.comap radialCircleProjection radialCircleTopBase

def radialCircleTopForward (p : radialCircleTopDomain) : radialCircleTopBase × Circle :=
  (⟨(radialCircleProduct p.val).1, mem_univ _⟩, (radialCircleProduct p.val).2)

def radialCircleTopBackward (q : radialCircleTopBase × Circle) : radialCircleTopDomain :=
  ⟨radialCircleProduct.symm (q.1.val, q.2), mem_univ _⟩

theorem radialCircleTopForward_smooth :
    ContMDiff (𝓡∂ 3) ((𝓡 2).prod (𝓡 1)) ∞ radialCircleTopForward := by
  have hv : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
      (Subtype.val : radialCircleTopDomain → radialCircleDomain) := contMDiff_subtype_val
  have hd := radialCircleProduct.contMDiff.comp hv
  have hf : ContMDiff (𝓡∂ 3) (𝓡 2) ∞ (fun p => (radialCircleTopForward p).1) :=
    (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
      radialCircleTopBase (fun p => (radialCircleTopForward p).1)).mp hd.fst
  exact hf.prodMk hd.snd

theorem radialCircleTopBackward_smooth :
    ContMDiff ((𝓡 2).prod (𝓡 1)) (𝓡∂ 3) ∞ radialCircleTopBackward := by
  have hi : ContMDiff ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1)) ∞
      (fun q : radialCircleTopBase × Circle => (q.1.val, q.2)) :=
    (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd
  exact (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialCircleTopDomain radialCircleTopBackward).mp
      (radialCircleProduct.symm.contMDiff.comp hi)

def radialCircleTrivialization : radialCircleTopDomain
    ≃ₘ⟮𝓡∂ 3, (𝓡 2).prod (𝓡 1)⟯ (radialCircleTopBase × Circle) where
  toFun := radialCircleTopForward
  invFun := radialCircleTopBackward
  left_inv := by
    intro p
    apply Subtype.ext
    exact radialCircleProduct.symm_apply_apply p.val
  right_inv := by
    intro q
    have hh := radialCircleProduct.apply_symm_apply (q.1.val, q.2)
    have hf := congrArg Prod.fst hh
    have hs := congrArg Prod.snd hh
    apply Prod.ext
    · exact Subtype.ext hf
    · exact hs
  contMDiff_toFun := radialCircleTopForward_smooth
  contMDiff_invFun := radialCircleTopBackward_smooth

def radialCircleRegion : CircleRegion carrier where
  Base := radialCircleBase
  domain := radialCircleDomain
  domain_interior := fun p hp => sphereInteriorToCarrier_interior
    (openCarrierToSphere ⟨p, hp.2⟩)
  proj := radialCircleProjection
  proj_smooth := radialCircleProjection_smooth
  proj_submersion := radialCircleProjection_onto
  neighborhood _ := radialCircleTopBase
  mem_neighborhood _ := mem_univ _
  trivialization _ := radialCircleTrivialization
  projection_trivialization _ _ := rfl
  definingCount := 2
  defining := radialCircleDefining
  defining_smooth := radialCircleDefining_smooth
  defining_regular l b _ := radialCircleDefining_regular l b
  depth_le_two b := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  defining_independent b l l' hn hl hl' :=
    (radialCircleDefining_no_double b hn hl hl').elim
  cornerBase := radialCircleCornerBase
  cornerBase_eq := radialCircleCornerBase_eq
  cornerBase_compact := radialCircleCornerBase_compact
  cornerCount := 0
  cornerChart k := k.elim0
  cornerChart_source k := k.elim0
  cornerChart_disjoint k := k.elim0
  cornerFirst k := k.elim0
  cornerSecond k := k.elim0
  corner_ne k := k.elim0
  cornerScale k := k.elim0
  cornerScale_pos k := k.elim0
  chart_first k := k.elim0
  chart_second k := k.elim0
  chart_other k := k.elim0
  corner_center b l l' hn hl hl' := (radialCircleDefining_no_double b hn hl hl').elim
  rounding := radialCircleRounding
  rounding_smooth := radialCircleRounding_smooth
  rounding_regular := radialCircleRounding_regular
  rounding_chart k := k.elim0
  rounding_agree := by simpa using radialCircleRounding_sublevel
  rounded_compact := radialCircleRounding_compact

theorem radialCircleRegion_range : radialCircleRegion.region =
    {p : carrier.Carrier | -(3 / 4 : ℝ) ≤ height p ∧ height p ≤ -(1 / 2 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨q, ⟨hl, hh⟩, rfl⟩
    have he := radialCircleProjection_height q
    change height q.val = 1 - 2 * radialBaseNorm (radialCircleProjection q) at he
    change (3 / 4 : ℝ) ≤ radialBaseNorm (radialCircleProjection q) at hl
    change radialBaseNorm (radialCircleProjection q) ≤ (7 / 8 : ℝ) at hh
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hl, hh⟩
    have hi : -1 < height p ∧ height p < 0 := ⟨by linarith, by linarith⟩
    let q : radialCircleDomain := ⟨p, hi⟩
    refine ⟨q, ?_, rfl⟩
    have he := radialCircleProjection_height q
    change height p = 1 - 2 * radialBaseNorm (radialCircleProjection q) at he
    change (3 / 4 : ℝ) ≤ radialBaseNorm (radialCircleProjection q) ∧
      radialBaseNorm (radialCircleProjection q) ≤ (7 / 8 : ℝ)
    exact ⟨by linarith, by linarith⟩

theorem radialCircleRegion_rounded : radialCircleRegion.rounded = radialCircleRegion.region := by
  change Subtype.val '' (radialCircleProjection ⁻¹' {b | radialCircleRounding b ≤ 0}) =
    Subtype.val '' (radialCircleProjection ⁻¹' radialCircleCornerBase)
  rw [radialCircleRounding_sublevel]

end GC.GraphManifold.Assembly.FC39P0.X135Radial
