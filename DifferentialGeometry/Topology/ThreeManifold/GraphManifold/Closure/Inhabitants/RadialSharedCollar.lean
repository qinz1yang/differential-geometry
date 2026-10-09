import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialSeamCoordinates
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_SharedCollarX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_SharedCollarX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialSeamShift : (Torus × ℝ)
    ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ) where
  toFun q := (q.1, -(1 / 4 : ℝ) + q.2 / 16)
  invFun q := (q.1, 16 * (q.2 + (1 / 4 : ℝ)))
  left_inv q := by
    apply Prod.ext
    · rfl
    · change 16 * (-(1 / 4 : ℝ) + q.2 / 16 + (1 / 4 : ℝ)) = q.2
      ring
  right_inv q := by
    apply Prod.ext
    · rfl
    · change -(1 / 4 : ℝ) + (16 * (q.2 + (1 / 4 : ℝ))) / 16 = q.2
      ring
  contMDiff_toFun := contMDiff_fst.prodMk
    (contMDiff_const.add (contMDiff_snd.div_const 16))
  contMDiff_invFun := contMDiff_fst.prodMk
    (contMDiff_const.mul (contMDiff_snd.add contMDiff_const))

def radialSharedCollar : PartialDiffeomorph signedCollarModel (𝓡∂ 3)
    (Torus × ℝ) carrier.Carrier ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    (radialSeamShift.toPartialDiffeomorph.trans radialNegativePartial)
    signedCollarSource isOpen_signedCollarSource

theorem radialSharedCollar_source : radialSharedCollar.source = signedCollarSource := by
  change (univ ∩ radialSeamShift ⁻¹' radialNegativePartial.source) ∩ signedCollarSource = _
  rw [radialNegativePartial_source]
  simp only [univ_inter]
  apply inter_eq_right.mpr
  intro q hq
  change -1 < -(1 / 4 : ℝ) + q.2 / 16 ∧ -(1 / 4 : ℝ) + q.2 / 16 < 0
  exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

def radialSharedCoordinate (q : Torus × ℝ) (hq : q ∈ signedCollarSource) :
    radialNegativeSeam :=
  ⟨radialSeamShift q, ⟨by change -1 < -(1 / 4 : ℝ) + q.2 / 16; linarith [hq.1],
    by change -(1 / 4 : ℝ) + q.2 / 16 < 0; linarith [hq.2]⟩⟩

theorem radialSharedCollar_apply (q : Torus × ℝ) (hq : q ∈ signedCollarSource) :
    radialSharedCollar q = negativeSeamToCarrier (radialSharedCoordinate q hq) :=
  radialNegativePartial_apply (radialSharedCoordinate q hq)

theorem radialSharedCollar_height (q : Torus × ℝ) (hq : q ∈ signedCollarSource) :
    height (radialSharedCollar q) = -(1 / 4 : ℝ) + q.2 / 16 := by
  rw [radialSharedCollar_apply q hq]
  exact height_negativeSeam _

theorem radialSharedCollar_target_band : radialSharedCollar.target ⊆
    {p | -(5 / 16 : ℝ) < height p ∧ height p < -(3 / 16 : ℝ)} := by
  intro p hp
  have hs := radialSharedCollar.map_target hp
  rw [radialSharedCollar_source] at hs
  have hh := radialSharedCollar_height (radialSharedCollar.symm p) hs
  have hc : height p = -(1 / 4 : ℝ) + (radialSharedCollar.symm p).2 / 16 :=
    (congrArg height (radialSharedCollar.right_inv hp)).symm.trans hh
  have hlo : -1 < (radialSharedCollar.symm.toPartialEquiv p).2 := hs.1
  have hhi : (radialSharedCollar.symm.toPartialEquiv p).2 < 1 := hs.2
  exact ⟨by linarith only [hc, hlo], by linarith only [hc, hhi]⟩

theorem radialSharedCollar_closure_safe : closure radialSharedCollar.target ⊆
    (cuspNear : Set carrier.Carrier) := by
  have hc : closure radialSharedCollar.target ⊆
      {p : carrier.Carrier | -(5 / 16 : ℝ) ≤ height p ∧ height p ≤ -(3 / 16 : ℝ)} := by
    apply closure_minimal
    · intro p hp
      have hh := radialSharedCollar_target_band hp
      exact ⟨hh.1.le, hh.2.le⟩
    · exact (isClosed_le continuous_const height_continuous).inter
        (isClosed_le height_continuous continuous_const)
  intro p hp
  have hh := hc hp
  change -(3 / 8 : ℝ) < height p ∧ height p < -(1 / 8 : ℝ)
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem radialSharedCollar_interior : radialSharedCollar.target ⊆ carrier.interior := by
  intro p hp
  have hh := radialSharedCollar_target_band hp
  change (𝓡∂ 3).IsInteriorPoint p
  have hn : height p < 0 := by linarith [hh.2]
  exact (solidTorus_isInteriorPoint_iff p).mpr hn

def radialTorusSeam : Assembly.TorusSeam carrier where
  collar := radialSharedCollar
  source_eq := radialSharedCollar_source
  target_interior := radialSharedCollar_interior

theorem radialSharedCollar_zero : range (fun t : Torus => radialSharedCollar (t, 0)) =
    {p | height p = -(1 / 4 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    have hs : (t, (0 : ℝ)) ∈ signedCollarSource := by constructor <;> norm_num
    change height (radialSharedCollar (t, 0)) = -(1 / 4 : ℝ)
    rw [radialSharedCollar_height _ hs]
    norm_num
  · intro hp
    change height p = -(1 / 4 : ℝ) at hp
    obtain ⟨q, hq⟩ := exists_negativeSeam_at p (by rw [hp]; norm_num)
      (by rw [hp]; norm_num)
    have ht : q.val.2 = -(1 / 4 : ℝ) :=
      (height_negativeSeam q).symm.trans ((congrArg height hq).trans hp)
    have hs : (q.val.1, (0 : ℝ)) ∈ signedCollarSource := by constructor <;> norm_num
    have he : radialSharedCoordinate (q.val.1, 0) hs = q := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change -(1 / 4 : ℝ) + (0 : ℝ) / 16 = q.val.2
        rw [ht]
        norm_num
    refine ⟨q.val.1, ?_⟩
    change radialSharedCollar (q.val.1, 0) = p
    rw [radialSharedCollar_apply _ hs, he]
    exact hq

end GC.GraphManifold.Assembly.FC39P0.X135Radial
