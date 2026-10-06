import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ProjectiveHeightFXR
import DifferentialGeometry.Topology.Manifold.BallChartOrientation
import DifferentialGeometry.Topology.Manifold.BallChartOpenImage
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSum

/-!
# An oriented ball chart of `ℝP³` whose open unit-ball image is `{p₀² > 16/25}`

Lane S-FIX-REG2 (suffix `_FXR`), G4 part 2. The stereographic chart `cycleBallAmbient true` of
`S³` centred at `e₀` (height `(4 − ‖y‖²)/(4 + ‖y‖²)`), rescaled by `2/3`, maps the closed ball of
radius `2` into the open hemisphere `{q₀ > 0}`, on which the covering map `S³ → ℝP³` is injective;
by `BallChart.exists_ballChart_of_open_embedding` this gives a ball chart `d` of `ℝP³`. The
image of the open unit ball is `{p₀² > 16/25}` (stereographic radius `< 2/3`, i.e. height
`> 4/5`). Orientation: `BallChart.exists_oriented` (and `OrientedBallChart.reflect` in the
opposite case) gives an `OrientedBallChart` of `ℝP³` with the same image.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open scoped Manifold ContDiff Topology InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- The open hemisphere `{q₀ > 0}` of `S³`. -/
def rp3Hemisphere_FXR : TopologicalSpace.Opens sphereW.Carrier :=
  ⟨{x | 0 < sphereHeight x}, isOpen_lt continuous_const contMDiff_sphereHeight.continuous⟩

/-- The covering map is injective on the open hemisphere. -/
theorem rp3Cover_injOn_FXR (x x' : sphereW.Carrier) (hx : 0 < sphereHeight x)
    (hx' : 0 < sphereHeight x') (h : rp3Cover_FXR x = rp3Cover_FXR x') : x = x' := by
  have h1 : SphericalSpaceFormGroup.antipodal.projection x.down =
      SphericalSpaceFormGroup.antipodal.projection x'.down := congrArg ULift.down h
  rcases antipodal_orbit_cases_FXR x.down x'.down h1 with h2 | h2
  · exact ULift.ext (Subtype.ext h2.symm)
  · exfalso
    have h3 : sphereHeight x' = -sphereHeight x := by
      unfold sphereHeight spherePoint
      rw [h2, inner_neg_left]
    linarith

theorem antipodal_projection_neg_FXR (p : sphere (0 : E4) 1) :
    SphericalSpaceFormGroup.antipodal.projection (-p) =
      SphericalSpaceFormGroup.antipodal.projection p := by
  have hmem : LinearIsometryEquiv.neg ℝ ∈ SphericalSpaceFormGroup.antipodal.group :=
    Or.inr rfl
  symm
  refine (SphericalSpaceFormGroup.antipodal.projection_eq_iff _ _).2
    ⟨⟨LinearIsometryEquiv.neg ℝ, hmem⟩, ?_⟩
  refine Subtype.ext ?_
  rw [Geometry.sphereDiffeo_coe]
  exact rfl

/-- The covering map identifies antipodal points. -/
theorem rp3Cover_neg_FXR (x : sphereW.Carrier) :
    rp3Cover_FXR (ULift.up (-spherePoint x)) = rp3Cover_FXR x :=
  congrArg ULift.up (antipodal_projection_neg_FXR (spherePoint x))

theorem sphereHeight_neg_FXR (x : sphereW.Carrier) :
    sphereHeight (ULift.up (-spherePoint x) : sphereW.Carrier) = -sphereHeight x := by
  unfold sphereHeight
  change ⟪((-spherePoint x : sphere (0 : E4) 1) : E4), spherePole⟫_ℝ = _
  rw [coe_neg_sphere, inner_neg_left]

theorem neg_stereo_gt_iff_FXR {r : ℝ} (hr : 0 ≤ r) :
    4 / 5 < -((r ^ 2 - 4) / (r ^ 2 + 4)) ↔ r < 2 / 3 := by
  have hpos : 0 < r ^ 2 + 4 := by positivity
  rw [show -((r ^ 2 - 4) / (r ^ 2 + 4)) = (4 - r ^ 2) / (r ^ 2 + 4) by ring, lt_div_iff₀ hpos]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- The rescaled stereographic ball chart of `S³` at `e₀`: `x ↦ amb_true ((2/3) x)`. -/
def rp3SphereChart_FXR : BallChart 3 (𝓡 3) sphereW.Carrier :=
  (⟨cycleBallAmbient true, by rw [cycleBallAmbient_source]; exact subset_univ _⟩ :
    BallChart 3 (𝓡 3) sphereW.Carrier).affine 0 (2 / 3) (by norm_num) (by norm_num)

theorem rp3SphereChart_apply_FXR (x : E3) :
    rp3SphereChart_FXR.chart x = cycleBallAmbient true ((2 / 3 : ℝ) • x) := by
  change cycleBallAmbient true ((0 : E3) + (2 / 3 : ℝ) • x) = _
  rw [zero_add]

end GC.GraphManifold.Assembly
