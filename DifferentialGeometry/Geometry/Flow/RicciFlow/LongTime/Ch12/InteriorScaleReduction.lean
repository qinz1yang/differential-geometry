import DifferentialGeometry.Geometry.Collapse.CutPieceBallsApplications
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBounds
import DifferentialGeometry.Geometry.Collapse.CuspBoundary

/-!
# CH12 T2 (TCF02), group 1: reduction of the interior scale statement to negative planes

* `curvatureRadius_le_sub_one_of_negative_planes_T2`: if for every `η > 0` some point at
  distance `≤ D - 1 + η` from `p` carries a plane of sectional curvature below `-1/81`, where
  `D > 10` is the boundary distance of `p`, then `R(p) ≤ D - 1`.
* `LateCutFamily.cutPiece_interior_scale_ambient_T2`: for an arbitrary late cut family, a piece
  point with `10 < D` and `R(p) ≤ D - 1` has the same curvature scale, balls (below `R`), volumes
  and derivative norms as the ambient normalized slice component.

The remaining group 2 (collar planes from `NearlyCuspidalBoundary`) supplies the hypothesis.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem curvatureRadius_le_sub_one_of_negative_planes_T2 {W : CompactCarrier.{u}}
    (h : SmoothRiemannianMetric W.model W.Carrier) (p : W.Carrier)
    (hD : ENNReal.ofReal 10 < distanceToBoundary W h p)
    (hneg : ∀ η : ℝ, 0 < η → ∃ q : W.Carrier,
      riemannianEDistOf h p q ≤ ENNReal.ofReal ((distanceToBoundary W h p).toReal - 1 + η) ∧
        ¬ SectionalBoundedBelowAt h q (-(1 / 81 : ℝ))) :
    curvatureRadius h p ≤ distanceToBoundary W h p - 1 := by
  by_cases htop : distanceToBoundary W h p = ⊤
  · rw [htop]; simp
  have hdfin := lt_top_iff_ne_top.mpr htop
  set D := distanceToBoundary W h p with hDdef
  have hd10 : (10 : ℝ) < D.toReal := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal (by norm_num) htop).mp hD
    exact this
  have hDeq : D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal htop).symm
  have hsub : D - 1 = ENNReal.ofReal (D.toReal - 1) := by
    rw [hDeq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
    simp
  rw [hsub]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨q, hq, hsec⟩ := hneg ε (by exact_mod_cast hε)
  have hR : (0 : ℝ) < D.toReal - 1 + ε := by
    have : (0 : ℝ) < ε := by exact_mod_cast hε
    linarith
  have hle := curvatureRadius_le_of_not_sectionalBoundedBelowAt h hR hq (by
    intro hb
    apply hsec
    refine hb.mono ?_
    have h9 : (9 : ℝ) < D.toReal - 1 + ε := by
      have : (0 : ℝ) < ε := by exact_mod_cast hε
      linarith
    have : (81 : ℝ) ≤ (D.toReal - 1 + ε) ^ 2 := by nlinarith
    have : ((D.toReal - 1 + ε) ^ 2)⁻¹ ≤ (1 / 81 : ℝ) := by
      rw [one_div]; exact inv_anti₀ (by norm_num) this
    linarith)
  refine hle.trans ?_
  exact ENNReal.ofReal_add_le.trans (by rw [ENNReal.ofReal_coe_nnreal])

namespace LateCutFamily

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- Group-1 consequence, arbitrary `L`: a scale below the boundary distance gives the ambient
scale, balls (up to the scale), volumes and derivative norms. -/
theorem cutPiece_interior_scale_ambient_T2 (L : GC.LongTime.LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j C).components.count)
    (p : ((L.decomposition j C).component i).Carrier)
    (hlt : curvatureRadius (L.metric j C i) p <
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p) :
    curvatureRadius ((slices j).componentMetric C) (cutPieceMap (L.decomposition j C) i p) =
        curvatureRadius (L.metric j C i) p ∧
      ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ curvatureRadius (L.metric j C i) p →
        cutPieceMap (L.decomposition j C) i '' riemannianBallOf (L.metric j C i) p r =
            riemannianBallOf ((slices j).componentMetric C)
              (cutPieceMap (L.decomposition j C) i p) r ∧
          ballVolume (L.metric j C i) p r =
            ballVolume ((slices j).componentMetric C)
              (cutPieceMap (L.decomposition j C) i p) r ∧
          ∀ k : ℕ, ∀ q ∈ riemannianBallOf (L.metric j C i) p r,
            curvatureDerivativeNorm (L.metric j C i) k q =
              curvatureDerivativeNorm ((slices j).componentMetric C) k
                (cutPieceMap (L.decomposition j C) i q) := by
  refine ⟨(GC.LongTime.LateCutFamily.cutPiece_curvatureRadius_eq_of_lt L j C i p hlt),
    fun r hr hrR => ?_⟩
  have hd : ENNReal.ofReal r <
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p :=
    lt_of_le_of_lt hrR hlt
  obtain ⟨h1, -, h3, h4⟩ := GC.LongTime.LateCutFamily.cutPiece_ball_tests L j C i p hd
  exact ⟨h1, h3, h4⟩

end LateCutFamily

end GC.LongTime.Ch12
