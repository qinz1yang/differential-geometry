import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovBoundaryBuffer
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

/-!
# Consumers of the buffered Bishop–Gromov on carriers with boundary (B2)

* `localBishopGromov_at_curvatureScale_of_distanceToBoundary`: on any compact carrier, at a point
  whose (finite) curvature scale `R_p` is below the distance to the boundary, the balls of radii
  `s ≤ R_p` satisfy the relative volume comparison with the model `-R_p⁻²`; the sectional bound is
  the one attained at the curvature scale (`sectionalBoundedBelowAt_of_curvatureRadius_ne_top`).
* `GC.LongTime.LateCutFamily.latePiece_volume_bounds_at_modified_scale`: the bounds LC03 and LC04
  of the blueprint (`master207A.tex`, lemmas `collapse-small-volume-upper` and
  `collapse-fixed-parameter-volume`) for the piece metrics `L.metric j C i` of an arbitrary late
  cut family, at points whose distance to the boundary of the piece exceeds `2ρ` (LC03) and `u`
  (LC04). The pieces are compact carriers which in general have nonempty boundary (the cut tori);
  no completeness, collar or seam assumption is used.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Topology
open scoped ENNReal Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- Bishop–Gromov at the curvature scale on a compact carrier: if the curvature scale
`R_p = curvatureRadius g p` is finite and below the distance to the boundary, the relative volume
comparison with the model `-R_p⁻²` holds for every `0 < s ≤ R_p`. -/
theorem localBishopGromov_at_curvatureScale_of_distanceToBoundary (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (p : W.Carrier)
    (hfin : curvatureRadius g p ≠ ⊤)
    (hdepth : curvatureRadius g p < distanceToBoundary W g p) {s : ℝ} (hs : 0 < s)
    (hsR : s ≤ (curvatureRadius g p).toReal) :
    0 < (ballVolume g p s).toReal ∧ 0 < (ballVolume g p (curvatureRadius g p).toReal).toReal ∧
      ballVolume g p s < ⊤ ∧ ballVolume g p (curvatureRadius g p).toReal < ⊤ ∧
      (ballVolume g p (curvatureRadius g p).toReal).toReal / (ballVolume g p s).toReal ≤
        modelVolume (-(((curvatureRadius g p).toReal) ^ 2)⁻¹) 3 (curvatureRadius g p).toReal /
          modelVolume (-(((curvatureRadius g p).toReal) ^ 2)⁻¹) 3 s ∧
      modelVolume (-(((curvatureRadius g p).toReal) ^ 2)⁻¹) 3 s /
          modelVolume (-(((curvatureRadius g p).toReal) ^ 2)⁻¹) 3 (curvatureRadius g p).toReal ≤
        (ballVolume g p s).toReal / (ballVolume g p (curvatureRadius g p).toReal).toReal := by
  have hdepth' : ENNReal.ofReal (curvatureRadius g p).toReal < distanceToBoundary W g p := by
    rwa [ENNReal.ofReal_toReal hfin]
  exact localBishopGromov_relative_ratios_of_distanceToBoundary W g p
    (inv_nonneg.mpr (sq_nonneg _)) hs hsR hdepth'
    (sectionalBoundedBelowAt_of_curvatureRadius_ne_top g hfin)

end DifferentialGeometry.Geometry.Collapse

namespace GC.LongTime.LateCutFamily

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- LC03 and LC04 on the pieces of a late cut family, below the distance to the boundary of the
piece: an attained volume `w r³` at `r ≤ 2ρ` with `sec ≥ -(2ρ)⁻²` on `B(p, 2ρ)` and
`2ρ < d(p, ∂W)` gives the upper ratio `3 ∫₀¹ sinh² · w` at `2ρ` and the bound `8 · 3 ∫₀¹ sinh² · w`
for the rescaled metric; an attained volume `w' u³` with `sec ≥ -u⁻²` on `B(p, u)` and
`u < d(p, ∂W)` gives the lower ratio `w' / (24 ∫₀¹ sinh²)` at every `0 < ρ' ≤ 2u`. -/
theorem latePiece_volume_bounds_at_modified_scale (L : LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j C).components.count)
    (p : ((L.decomposition j C).component i).Carrier) {w r ρ w' u ρ' : ℝ}
    (hw : 0 < w) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ 2 * ρ)
    (hdepth : ENNReal.ofReal (2 * ρ) <
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p)
    (hvol : ballVolume (L.metric j C i) p r = ENNReal.ofReal (w * r ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf (L.metric j C i) p (2 * ρ),
      SectionalBoundedBelowAt (L.metric j C i) q (-((2 * ρ) ^ 2)⁻¹))
    (hw' : 0 < w') (hu : 0 < u) (hρ' : 0 < ρ') (hρ'u : ρ' ≤ 2 * u)
    (hdepth' : ENNReal.ofReal u <
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p)
    (hvol' : ballVolume (L.metric j C i) p u = ENNReal.ofReal (w' * u ^ 3))
    (hsec' : ∀ q ∈ riemannianBallOf (L.metric j C i) p u,
      SectionalBoundedBelowAt (L.metric j C i) q (-(u ^ 2)⁻¹)) :
    (ballVolume (L.metric j C i) p (2 * ρ)).toReal / (2 * ρ) ^ 3 ≤
        (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w ∧
      (ballVolume (scaleMetric (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) (L.metric j C i))
          p 2).toReal ≤ 8 * (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w ∧
      0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
        (ballVolume (L.metric j C i) p ρ').toReal / ρ' ^ 3 := by
  obtain ⟨hpos, hlow⟩ := volume_lower_at_modified_scale_of_distanceToBoundary _ _ p hw' hu hρ'
    hρ'u hdepth' hvol' hsec'
  exact ⟨volume_upper_at_modified_scale_of_distanceToBoundary _ _ p hw hr hρ hrρ hdepth hvol
      hsec,
    scaled_volume_upper_at_modified_scale_of_distanceToBoundary _ _ p hw hr hρ hrρ hdepth hvol
      hsec, hpos, hlow⟩

end GC.LongTime.LateCutFamily
