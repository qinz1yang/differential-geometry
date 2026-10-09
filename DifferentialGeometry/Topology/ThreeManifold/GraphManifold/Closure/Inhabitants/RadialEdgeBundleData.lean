import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialFibreTarget
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierCharts_BundleX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_BundleX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance
local instance carrierCompact_BundleX135 : CompactSpace carrier.Carrier := carrier.compact
local instance cellCharts_BundleX135 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  Handle.closedCellChartedSpaceSucc 1
local instance cellSmooth_BundleX135 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  Handle.closedCellIsManifold 1

def carrierDiscCircle : carrier.Carrier ≃ₘ⟮𝓡∂ 3, (𝓡∂ 2).prod (𝓡 1)⟯
    UnitDisc.{0} × Circle := solidTorusDiscCircle

def edgeLongitude (p : carrier.Carrier) : Circle := (carrierDiscCircle p).2

theorem edgeLongitude_smooth : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ edgeLongitude :=
  carrierDiscCircle.contMDiff.snd

theorem edgeLongitude_onto (p : carrier.Carrier) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1) edgeLongitude p) := by
  have hd := (carrierDiscCircle.mfderivToContinuousLinearEquiv (by simp) p).surjective
  have hc := mfderiv_comp (g := fun q : UnitDisc.{0} × Circle => q.2)
    (f := carrierDiscCircle) p mdifferentiableAt_snd
    (carrierDiscCircle.contMDiff.mdifferentiableAt (by simp))
  change mfderiv (𝓡∂ 3) (𝓡 1) edgeLongitude p = _ at hc
  rw [mfderiv_snd] at hc
  intro v
  obtain ⟨w, hw⟩ := hd ((0 : TangentSpace (𝓡∂ 2) (carrierDiscCircle p).1), v)
  refine ⟨w, ?_⟩
  rw [hc]
  exact congrArg Prod.snd hw

def edgeBundleProjection : C(radialCarrierInterior, Circle) :=
  ⟨fun p => edgeLongitude p.val, edgeLongitude_smooth.continuous.comp continuous_subtype_val⟩

theorem edgeBundleProjection_smooth :
    ContMDiff (𝓡∂ 3) (𝓡 1) ∞ edgeBundleProjection :=
  edgeLongitude_smooth.comp contMDiff_subtype_val

def edgeBundleHeight (p : radialCarrierInterior) : ℝ := height p.val

theorem edgeBundleHeight_smooth :
    ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ edgeBundleHeight :=
  height_smooth.comp contMDiff_subtype_val

theorem edgeLongitude_core (p : radialEdgeSet) :
    edgeLongitude (edgeToCarrier p) = radialEdgeProjection p := rfl

theorem edgeLongitude_fibre (c : Circle) (x : ClosedCell 2) :
    edgeLongitude (edgeFibreAt c x) = c := by
  change (solidTorusDiscCircle (edgeAsSolidTorus (edgeCoreFibreAt c x))).2 = c
  rw [edgeCoreFibreAt_product]
  have hh := congrArg Prod.snd (edgeProduct.left_inv
    (GC.Seifert.unitDiscClosedCell.{0}.symm x, c))
  exact hh

theorem edgeFibreAt_range (c : Circle) :
    range (edgeFibreAt c) =
      {p : carrier.Carrier | edgeLongitude p = c ∧ height p ≤ -(3 / 4 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨edgeLongitude_fibre c x, edgeCoreFibreAt_height c x⟩
  · rintro ⟨hphase, hh⟩
    have hpr : p ∈ range edgeToCarrier := by
      rw [edgeToCarrier_range]
      exact hh
    obtain ⟨q, hq⟩ := hpr
    let x := GC.Seifert.unitDiscClosedCell.{0} (edgeProductInverse q).1
    refine ⟨x, ?_⟩
    have hc : (edgeProductInverse q).2 = c := by
      rw [← hphase, ← hq]
      rfl
    have he : edgeCoreFibreAt c x = q := by
      rw [edgeCoreFibreAt_product]
      change edgeProductMap
        (GC.Seifert.unitDiscClosedCell.{0}.symm
          (GC.Seifert.unitDiscClosedCell.{0} (edgeProductInverse q).1), c) = q
      rw [GC.Seifert.unitDiscClosedCell.symm_apply_apply, ← hc]
      exact edgeProduct.right_inv q
    change edgeToCarrier (edgeCoreFibreAt c x) = p
    rw [he, hq]

theorem edgeBundle_proper (K : Set Circle) (hK : IsCompact K) :
    IsCompact (Subtype.val '' {p : radialCarrierInterior |
      edgeBundleProjection p ∈ K ∧ edgeBundleHeight p ≤ -(3 / 4 : ℝ)}) := by
  have he : Subtype.val '' {p : radialCarrierInterior |
      edgeBundleProjection p ∈ K ∧ edgeBundleHeight p ≤ -(3 / 4 : ℝ)} =
      edgeLongitude ⁻¹' K ∩ {p | height p ≤ -(3 / 4 : ℝ)} := by
    ext p
    constructor
    · rintro ⟨q, ⟨hk, hh⟩, rfl⟩
      exact ⟨hk, hh⟩
    · rintro ⟨hk, hh⟩
      have hi : height p < 0 := hh.trans_lt (by norm_num : -(3 / 4 : ℝ) < 0)
      exact ⟨⟨p, hi⟩, ⟨hk, hh⟩, rfl⟩
  rw [he]
  exact ((hK.isClosed.preimage edgeLongitude_smooth.continuous).inter
    (isClosed_le height_continuous continuous_const)).isCompact

theorem edgeBundleProjection_onto (p : radialCarrierInterior) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1) edgeBundleProjection p) := by
  change Surjective (mfderiv (𝓡∂ 3) (𝓡 1)
    (fun q : radialCarrierInterior => edgeLongitude q.val) p)
  rw [DifferentialGeometry.mfderiv_restrict_open]
  exact edgeLongitude_onto p.val

theorem edgeBundle_fibre_disk (c : Circle) :
    ∃ φ : ClosedCell 2 → carrier.Carrier, IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ φ ∧
      range φ = Subtype.val '' {p : radialCarrierInterior |
        edgeBundleProjection p = c ∧ edgeBundleHeight p ≤ -(3 / 4 : ℝ)} := by
  refine ⟨edgeFibreAt c, edgeFibreAt_embedding c, ?_⟩
  rw [edgeFibreAt_range]
  ext p
  constructor
  · rintro ⟨hc, hh⟩
    have hi : height p < 0 := hh.trans_lt (by norm_num : -(3 / 4 : ℝ) < 0)
    exact ⟨⟨p, hi⟩, ⟨hc, hh⟩, rfl⟩
  · rintro ⟨q, ⟨hc, hh⟩, rfl⟩
    exact ⟨hc, hh⟩

end GC.GraphManifold.Assembly.FC39P0.X135Radial
