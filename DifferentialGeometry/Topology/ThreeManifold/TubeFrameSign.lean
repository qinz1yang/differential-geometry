import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.Manifold.Interval.TangentLift
import DifferentialGeometry.Topology.Manifold.ProductOrientationCongruence
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Bundle.Orientation.FrameTransport

set_option autoImplicit false

noncomputable section

open Set Manifold Module Bundle Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalTubeSystem

universe u

local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Interval" => Icc (-2 : ℝ) 2
local notation "Tube" => S2 × Interval
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def intervalBasis (t : Interval) : Basis (Fin 1) ℝ (TangentSpace (𝓡∂ 1) t) :=
  (Basis.singleton (Fin 1) ℝ).map
    (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm.toLinearEquiv

def normalFirstModelBasis (z : S2) (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z))
    (t : Interval) : Basis (Fin 3) ℝ (TangentSpace CI (z, t)) :=
  (((intervalBasis t).prod b).reindex finSumFinEquiv).map
    (LinearEquiv.prodComm ℝ (TangentSpace (𝓡∂ 1) t) (TangentSpace (𝓡 2) z))

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

def tubeDifferential (a : T.Index) (q : Tube) :
    TangentSpace CI q ≃ₗ[ℝ] TangentSpace (𝓡 3) (T.tube a q) :=
  LinearEquiv.ofBijective (mfderiv CI (𝓡 3) (T.tube a) q).toLinearMap
    (DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
      CI (𝓡 3) (T.tube a) q ((T.smooth a).isImmersion.isImmersionAt q)
      (by change Module.finrank ℝ (E2 × E1) = Module.finrank ℝ E3; simp))

def tubeFrame (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) :
    Basis (Fin 3) ℝ (TangentSpace (𝓡 3) (T.tube a (z, t))) :=
  (normalFirstModelBasis z b t).map (tubeDifferential T a (z, t))

theorem tubeFrame_apply (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) (i : Fin 3) :
    tubeFrame T a z b t i =
      mfderiv CI (𝓡 3) (T.tube a) (z, t) (normalFirstModelBasis z b t i) := rfl

end DifferentialGeometry.Topology.SphericalTubeSystem

namespace DifferentialGeometry.Topology.SphericalTubeSystem
universe u
local notation "Interval" => Set.Icc (-2 : ℝ) 2
local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

theorem continuous_intervalVector (r : ℝ) :
    Continuous (fun t : Interval =>
      (⟨t, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm r⟩ :
        TangentBundle (𝓡∂ 1) Interval)) := by
  exact (DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm.continuous.comp
    (continuous_id.prodMk continuous_const))

end DifferentialGeometry.Topology.SphericalTubeSystem


namespace DifferentialGeometry.Topology.SphericalTubeSystem
universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Interval" => Set.Icc (-2 : ℝ) 2
local notation "Tube" => S2 × Interval
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)
local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

theorem continuous_productVector (z : S2) (v : TangentSpace (𝓡 2) z) (r : ℝ) :
    Continuous (fun t : Interval =>
      (⟨(z, t), (v, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm r)⟩ :
        TangentBundle CI Tube)) := by
  let hpair : Continuous (fun t : Interval =>
      ((⟨z, v⟩ : TangentBundle (𝓡 2) S2),
        (⟨t, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm r⟩ :
          TangentBundle (𝓡∂ 1) Interval))) :=
    continuous_const.prodMk (continuous_intervalVector r)
  have he := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓡 2) (I' := 𝓡∂ 1) (M := S2) (M' := Interval) (n := (0 : WithTop ℕ∞))).continuous
  have hc := he.comp hpair
  exact hc.congr (fun t => rfl)

end DifferentialGeometry.Topology.SphericalTubeSystem
