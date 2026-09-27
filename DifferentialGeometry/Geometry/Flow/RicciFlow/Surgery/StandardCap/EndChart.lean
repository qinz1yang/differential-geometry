import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Polar
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Metric.RoundCylinder
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false
noncomputable section

open Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def cylindricalEndDomain : Opens (S2 × ℝ) :=
  ⟨{q | transitionEnd < q.2}, isOpen_lt continuous_const continuous_snd⟩

def cylindricalEndImage : Opens E3 :=
  ⟨euclideanPolarDiffeomorph (n := 2) '' (cylindricalEndDomain : Set (S2 × ℝ)),
    image_opens_isOpen _ (fun _ hq => transitionEnd_pos.trans hq)⟩

def cylindricalEnd : cylindricalEndDomain ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), 𝓡 3⟯ cylindricalEndImage :=
  PartialDiffeomorph.toOpensDiffeo (euclideanPolarDiffeomorph (n := 2))
    (fun _ hq => transitionEnd_pos.trans hq)

@[simp] theorem cylindricalEnd_apply (q : cylindricalEndDomain) :
    (cylindricalEnd q : E3) = euclideanPolarMap (q : S2 × ℝ) := rfl

theorem cylindricalEndImage_eq_compl_core : (cylindricalEndImage : Set E3) = coreᶜ := by
  rw [core_eq_radial]
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    change ¬ ‖euclideanPolarMap q‖ ≤ transitionEnd
    rw [euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans hq)]
    exact not_le.mpr hq
  · intro hx
    have hxL : transitionEnd < ‖x‖ := lt_of_not_ge hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (transitionEnd_pos.trans hxL)
    refine ⟨(euclideanPolarDiffeomorph (n := 2)).symm x, ?_,
      (euclideanPolarDiffeomorph (n := 2)).right_inv' hx0⟩
    change transitionEnd < ((euclideanPolarDiffeomorph (n := 2)).symm x).2
    simpa only [euclideanPolarDiffeomorph_symm_snd hx0] using hxL

theorem polar_image_closed_end :
    euclideanPolarMap '' {q : S2 × ℝ | transitionEnd ≤ q.2} =
      {x : E3 | transitionEnd ≤ ‖x‖} := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    change transitionEnd ≤ ‖euclideanPolarMap q‖
    rw [euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans_le hq)]
    exact hq
  · intro hx
    change transitionEnd ≤ ‖x‖ at hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (transitionEnd_pos.trans_le hx)
    refine ⟨(euclideanPolarDiffeomorph (n := 2)).symm x, ?_,
      (euclideanPolarDiffeomorph (n := 2)).right_inv' hx0⟩
    change transitionEnd ≤ ((euclideanPolarDiffeomorph (n := 2)).symm x).2
    simpa only [euclideanPolarDiffeomorph_symm_snd hx0] using hx

theorem polar_bijOn_closed_end :
    BijOn euclideanPolarMap {q : S2 × ℝ | transitionEnd ≤ q.2}
      {x : E3 | transitionEnd ≤ ‖x‖} := by
  refine ⟨?_, euclideanPolarMap_injOn.mono (fun q hq => transitionEnd_pos.trans_le hq), ?_⟩
  · intro q hq
    change transitionEnd ≤ q.2 at hq
    change transitionEnd ≤ ‖euclideanPolarMap q‖
    simpa only [euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans_le hq)] using hq
  · intro x hx
    rw [← polar_image_closed_end] at hx
    exact hx

theorem cylindricalEnd_norm (q : cylindricalEndDomain) :
    ‖(cylindricalEnd q : E3)‖ = (q : S2 × ℝ).2 :=
  euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans q.property)

theorem cylindricalEnd_symm_snd (x : cylindricalEndImage) :
    (cylindricalEnd.symm x : S2 × ℝ).2 = ‖(x : E3)‖ := by
  have h := cylindricalEnd_norm (cylindricalEnd.symm x)
  simpa only [cylindricalEnd.apply_symm_apply] using h.symm

theorem cylindricalEnd_mfderiv (q : cylindricalEndDomain)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) cylindricalEnd q v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap (q : S2 × ℝ) v :=
  PartialDiffeomorph.mfderiv_toOpensDiffeo _
    (fun _ hq => transitionEnd_pos.trans hq) q v

theorem cylindricalEnd_metric_inner (q : cylindricalEndDomain)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (cylindricalEnd q : E3)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) cylindricalEnd q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) cylindricalEnd q w) =
      (roundCylinderMetric (E := E3) (n := 2)).inner (q : S2 × ℝ) v w := by
  rw [cylindricalEnd_apply, cylindricalEnd_mfderiv, cylindricalEnd_mfderiv]
  exact metric_polar_pullback_cylindrical q q.property.le v w

end DifferentialGeometry.PDE.RicciFlow.StandardCap
