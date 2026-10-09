import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderScalarNormalization
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance coverScalarSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private local instance coverScalarSphereC1 : IsManifold (𝓡 2) 1 SphereTwo :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance coverScalarCylinderC1 : IsManifold CylinderI 1 Cylinder :=
  IsManifold.of_le (n := ∞) (by decide)

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval}

private local instance coverScalarTopology : TopologicalSpace F.M := F.topology
private local instance coverScalarCharted : ChartedSpace H F.M := F.charted
private local instance coverScalarSmooth : IsManifold I ∞ F.M := F.smooth
private local instance coverScalarC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance coverScalarT2 : T2Space F.M := F.t2
private local instance coverScalarSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact

namespace ShrinkingCylinderCover

variable (C : ShrinkingCylinderCover F)

theorem metricScalarAt_eq_inv_sub (t : ℝ) (ht : t ≤ 0) (x : F.M) :
    metricScalarAt (I := I) (F.S.base.metric t) x = 1 / (C.extinctionTime - t) := by
  let gPull : SmoothRiemannianMetric CylinderI Cylinder :=
    localPullMetric (F.S.base.metric t) C.projection C.projection_local
  have hpositive : 0 < C.extinctionTime - t := by
    have hT := C.extinctionTime_pos
    linarith
  have hinner : ∀ (y : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
      gPull.inner (y, s) (v, a) (w, b) =
        (2 * (C.extinctionTime - t)) * (sphereMetric).inner y v w + a * b := by
    intro y s v w a b
    exact (localPullMetric_inner (F.S.base.metric t) C.projection C.projection_local
      (y, s) (v, a) (w, b)).trans (C.projection_metric t ht y s v w a b)
  obtain ⟨p, hp⟩ := C.surjective x
  change C.projection p = x at hp
  have hvalue := metricScalarAt_roundCylinder_of_inner_eq gPull
    (2 * (C.extinctionTime - t)) (mul_pos (by norm_num) hpositive) hinner p
  have hnatural := metricScalarAt_localPull (F.S.base.metric t)
    C.projection C.projection_local p
  have hscalar := hnatural.symm.trans hvalue
  rw [hp] at hscalar
  calc
    metricScalarAt (I := I) (F.S.base.metric t) x =
        2 / (2 * (C.extinctionTime - t)) := hscalar
    _ = 1 / (C.extinctionTime - t) := by
      rw [div_mul_eq_div_div]
      norm_num

theorem extinctionTime_eq_one_of_scalar_at_base_one
    (hbase : PointedFlowScalarAtBase F 1) : C.extinctionTime = 1 := by
  have hscalar : metricScalarAt (I := I) (F.S.base.metric 0) F.basepoint = 1 := by
    simpa only [PointedFlowScalarAtBase, SolutionOn.scalar, SolutionFamily.scalar]
      using hbase
  have hvalue := C.metricScalarAt_eq_inv_sub 0 le_rfl F.basepoint
  rw [hscalar, sub_zero] at hvalue
  have h := (eq_div_iff (ne_of_gt C.extinctionTime_pos)).mp hvalue
  simpa only [one_mul] using h

include C in
theorem metricScalarAt_zero_eq_one_of_scalar_at_base_one
    (hbase : PointedFlowScalarAtBase F 1) (x : F.M) :
    metricScalarAt (I := I) (F.S.base.metric 0) x = 1 := by
  rw [C.metricScalarAt_eq_inv_sub 0 le_rfl x,
    C.extinctionTime_eq_one_of_scalar_at_base_one hbase, sub_zero, div_self one_ne_zero]

end ShrinkingCylinderCover

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
