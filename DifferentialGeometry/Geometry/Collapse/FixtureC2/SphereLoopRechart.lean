import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopGeom
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCircleFibredSurface

/-!
# The sphere loop as a three-dimensional carrier (S-FIXTURE-C2b, K2, G2 file 3)

`LoopC_FXC2 ℓ = CarrierRechart (loopLabel ℓ) (productModelEquiv 2)`: the points of the sphere loop
`S² × AddCircle 1`, with the smooth structure transported to the model `ℝ³` exactly as for
`sphereCylinderRechart`. The labelling homeomorphism `loopLabel ℓ` (a rotation of the circle by
`ℓ`) only makes the type depend on the length, so that the intrinsic metric space of the length-`ℓ`
loop can be a local instance.

* `loopMetric3_FXC2 ℓ`: the metric of `loopMetric_FXC2 ℓ` pulled back along the rechart;
  `loopMS3_FXC2 ℓ` its induced metric space (distance = length distance);
* `loopOrientation_FXC2`: an orientation (product of the sphere and circle orientations);
* `loopMetric3_sectional_FXC2`, `exists_loopMetric3_curvature_bounds_FXC2`,
  `exists_loopMetric3_volume_FXC2`: sectional curvature `≥ 0`, curvature-derivative bounds and a
  volume lower bound of the radius `ε` ball at `π_a (z, 0)`, all uniform in `ℓ` and the shift.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

/-- Positive lengths. -/
abbrev LoopLen_FXC2 := {ℓ : ℝ // 0 < ℓ}

instance : ConnectedSpace SphereLoop_FXC2 := inferInstance

/-- The rotation of the circle by the length (a labelling only). -/
def loopLabel_FXC2 (ℓ : LoopLen_FXC2) : SphereLoop_FXC2 ≃ₜ SphereLoop_FXC2 :=
  Homeomorph.prodCongr (Homeomorph.refl _)
    (Homeomorph.addRight (((ℓ.1 : ℝ) : AddCircle (1 : ℝ))))

/-- The three-dimensional carrier of the length-`ℓ` sphere loop. -/
abbrev LoopC_FXC2 (ℓ : LoopLen_FXC2) :=
  CarrierRechart (loopLabel_FXC2 ℓ) (DifferentialGeometry.Topology.productModelEquiv 2)

def loopDiffeo_FXC2 (ℓ : LoopLen_FXC2) :
    SphereLoop_FXC2 ≃ₘ⟮IC, 𝓡 3⟯ LoopC_FXC2 ℓ :=
  CarrierRechart.diffeomorph (loopLabel_FXC2 ℓ) (DifferentialGeometry.Topology.productModelEquiv 2)

instance (ℓ : LoopLen_FXC2) : CompactSpace (LoopC_FXC2 ℓ) :=
  (CarrierRechart.toSource (loopLabel_FXC2 ℓ)
    (DifferentialGeometry.Topology.productModelEquiv 2)).symm.compactSpace

def loopMetric3_FXC2 (ℓ : LoopLen_FXC2) : SmoothRiemannianMetric (𝓡 3) (LoopC_FXC2 ℓ) :=
  Diffeomorph.pullbackMetricCross (loopMetric_FXC2 ℓ.1 ℓ.2) (loopDiffeo_FXC2 ℓ).symm

/-- The induced length metric space of the three-dimensional sphere loop (a local instance). -/
@[reducible] def loopMS3_FXC2 (ℓ : LoopLen_FXC2) : MetricSpace (LoopC_FXC2 ℓ) :=
  inducedMetricSpace (loopMetric3_FXC2 ℓ)

theorem loopMS3_hmetric_FXC2 (ℓ : LoopLen_FXC2) :
    letI := loopMS3_FXC2 ℓ
    ∀ a b : LoopC_FXC2 ℓ,
      riemannianEDistOf (loopMetric3_FXC2 ℓ) a b = ENNReal.ofReal (dist a b) :=
  inducedMetricSpace_hmetric (loopMetric3_FXC2 ℓ)

theorem loopMetric3_edist_FXC2 (ℓ : LoopLen_FXC2) (a b : LoopC_FXC2 ℓ) :
    riemannianEDistOf (loopMetric3_FXC2 ℓ) a b =
      riemannianEDistOf (loopMetric_FXC2 ℓ.1 ℓ.2) ((loopDiffeo_FXC2 ℓ).symm a)
        ((loopDiffeo_FXC2 ℓ).symm b) :=
  riemannianEDistOf_pullbackMetricCross (loopMetric_FXC2 ℓ.1 ℓ.2) (loopDiffeo_FXC2 ℓ).symm a b

theorem loopMetric3_sectional_FXC2 (ℓ : LoopLen_FXC2) (x : LoopC_FXC2 ℓ) :
    SectionalBoundedBelowAt (loopMetric3_FXC2 ℓ) x 0 := by
  intro v w
  rw [zero_mul]
  rw [loopMetric3_FXC2, Curvature.metricRm04Standard_pullbackCross]
  simpa only [zero_mul] using loopMetric_sectional_FXC2 ℓ.1 ℓ.2 ((loopDiffeo_FXC2 ℓ).symm x)
    (mfderiv (𝓡 3) IC (loopDiffeo_FXC2 ℓ).symm x v) (mfderiv (𝓡 3) IC (loopDiffeo_FXC2 ℓ).symm x w)

theorem exists_loopMetric3_curvature_bounds_FXC2 (K : ℕ) :
    ∃ A : ℝ, ∀ (ℓ : LoopLen_FXC2), ∀ k ≤ K, ∀ x : LoopC_FXC2 ℓ,
      curvDerivNorm k (loopMetric3_FXC2 ℓ) x ≤ A := by
  obtain ⟨A, hA⟩ := exists_loop_curvature_bounds_FXC2 K
  refine ⟨A, fun ℓ k hk x => ?_⟩
  exact (PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross
    (loopMetric_FXC2 ℓ.1 ℓ.2) (loopDiffeo_FXC2 ℓ).symm k x).trans_le
      (hA ℓ.1 ℓ.2 k hk ((loopDiffeo_FXC2 ℓ).symm x))

theorem loopOrientation_FXC2 (ℓ : LoopLen_FXC2) :
    Nonempty (ManifoldOrientation (𝓡 3) (LoopC_FXC2 ℓ) 3) := by
  let product := productOrientation (𝓡 2) 𝓘(ℝ, ℝ) (by decide) (by decide)
    (sphereOrientation 2 (by decide)) GC.GraphManifold.Assembly.addCircleOrientation
  let sourceSmooth := Topology.Manifold.smoothOrientationOfManifoldOrientation IC
    (by simpa using product)
  let targetSmooth := Topology.Manifold.pullbackSmoothOrientation (𝓡 3) IC
    (loopDiffeo_FXC2 ℓ).symm (loopDiffeo_FXC2 ℓ).symm.contMDiff
    (fun x => ((loopDiffeo_FXC2 ℓ).symm.mfderivToContinuousLinearEquiv
      (by simp) x).bijective) sourceSmooth
  obtain ⟨O, hO⟩ :=
    Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3) targetSmooth
  exact ⟨by simpa using O⟩

theorem loopMetric3_preimage_ball_FXC2 (ℓ : LoopLen_FXC2) (p : SphereLoop_FXC2) (ε : ℝ) :
    (loopDiffeo_FXC2 ℓ) ⁻¹' riemannianBallOf (loopMetric3_FXC2 ℓ) (loopDiffeo_FXC2 ℓ p) ε =
      riemannianBallOf (loopMetric_FXC2 ℓ.1 ℓ.2) p ε := by
  ext y
  change riemannianEDistOf (loopMetric3_FXC2 ℓ) (loopDiffeo_FXC2 ℓ p) (loopDiffeo_FXC2 ℓ y) <
    ENNReal.ofReal ε ↔ riemannianEDistOf (loopMetric_FXC2 ℓ.1 ℓ.2) p y < ENNReal.ofReal ε
  rw [loopMetric3_edist_FXC2, Diffeomorph.symm_apply_apply, Diffeomorph.symm_apply_apply]

theorem loopMetric3_volume_ge_FXC2 (ℓ : LoopLen_FXC2) (p : SphereLoop_FXC2) (ε : ℝ) :
    Integral.Measure.riemannianVolumeMeasure IC SphereLoop_FXC2 (loopMetric_FXC2 ℓ.1 ℓ.2)
        (riemannianBallOf (loopMetric_FXC2 ℓ.1 ℓ.2) p ε) ≤
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ)
        (riemannianBallOf (loopMetric3_FXC2 ℓ) (loopDiffeo_FXC2 ℓ p) ε) := by
  let _ : MeasurableSpace SphereLoop_FXC2 := borel _
  have _ : BorelSpace SphereLoop_FXC2 := ⟨rfl⟩
  let _ : MeasurableSpace (LoopC_FXC2 ℓ) := borel _
  have _ : BorelSpace (LoopC_FXC2 ℓ) := ⟨rfl⟩
  have h := Integral.Measure.riemannianVolumeMeasure_pullback_cross
    (loopMetric_FXC2 ℓ.1 ℓ.2) (loopDiffeo_FXC2 ℓ).symm
  have hm : AEMeasurable (loopDiffeo_FXC2 ℓ : SphereLoop_FXC2 → LoopC_FXC2 ℓ)
      (Integral.Measure.riemannianVolumeMeasure IC SphereLoop_FXC2
        (loopMetric_FXC2 ℓ.1 ℓ.2)) :=
    (loopDiffeo_FXC2 ℓ).continuous.aemeasurable
  have h2 : loopMetric3_FXC2 ℓ = Diffeomorph.pullbackMetricCross (loopMetric_FXC2 ℓ.1 ℓ.2)
      (loopDiffeo_FXC2 ℓ).symm := rfl
  rw [h2, h]
  refine le_trans ?_ (MeasureTheory.Measure.le_map_apply hm _)
  rw [← h2, ← loopMetric3_preimage_ball_FXC2]

theorem exists_loopMetric3_volume_FXC2 {ε : ℝ} (hε : 0 < ε) (z : S2) :
    ∃ w : ℝ, 0 < w ∧ ∀ (ℓ : LoopLen_FXC2) (a : ℝ), 2 * ε ≤ ℓ.1 →
      ENNReal.ofReal w ≤
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ)
          (riemannianBallOf (loopMetric3_FXC2 ℓ)
            (loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a (z, 0))) ε) := by
  obtain ⟨w, hw, h⟩ := exists_loop_volume_FXC2 hε z
  refine ⟨w, hw, fun ℓ a h2 => (h ℓ.1 a ℓ.2 h2).trans ?_⟩
  exact loopMetric3_volume_ge_FXC2 ℓ _ ε

end DifferentialGeometry.Geometry.Collapse
