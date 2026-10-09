import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusMetric
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections
import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Geodesic

/-!
# Geodesics of the flat torus are projected lines (S-FIXTURE-C1, K1, file 9)

Review 75 (D75-8, question 6): local isometry transports geodesics. Here:

* `isGeodesic_euclidean_line_FXC1`: the line `t ↦ x + t v` solves the geodesic equation of the
  Euclidean metric of `ℝ³` (zero Christoffel symbols in the identity chart);
* `isGeodesic_torPi_line_FXC1`: for every constant multiple `c · torMetric`, the curve
  `t ↦ π(x + t v)` is a geodesic (`geoOn_map_localIso`, scale invariance of the geodesic equation).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance nezero_finrank_E3_FXC1 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- **The lines of `ℝ³` are geodesics of the Euclidean metric.** -/
theorem isGeodesic_euclidean_line_FXC1 (x v : E3) :
    IsGeodesic (I := 𝓘(ℝ, E3)) (euclideanMetric (E := E3)) (fun t : ℝ => x + t • v) := by
  intro t
  have hcl : chartLocalCurve (I := 𝓘(ℝ, E3)) (fun t : ℝ => x + t • v) t =
      fun s : ℝ => x + s • v := by
    funext s
    simp [chartLocalCurve_def]
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := fun s => by
    have h := ((hasDerivAt_id s).smul_const v).const_add x
    rwa [one_smul] at h
  have hder : deriv (fun s : ℝ => x + s • v) = fun _ => v := funext fun s => (hd s).deriv
  refine ⟨v, 0, ?_, ?_, ?_, ?_⟩
  · rw [hcl]; exact hd t
  · filter_upwards with s
    rw [hcl]; exact (hd s).differentiableAt.hasDerivAt
  · rw [hcl, hder]; exact hasDerivAt_const t v
  · rw [DifferentialGeometry.Geometry.Connection.chartChristoffelContraction_euclideanMetric]
    simp


/-- **Projected lines are geodesics of the (scaled) flat torus**: local isometries transport
geodesics (`geoOn_map_localIso`) and the geodesic equation is scale invariant. -/
theorem isGeodesic_torPi_line_FXC1 (Λ : TorusPeriods_FXC1) {c : ℝ} (hc : 0 < c) (x v : E3) :
    IsGeodesic (I := 𝓘(ℝ, E3)) (scaleMetric c hc (torMetric_FXC1 Λ))
      (fun t : ℝ => torPi_FXC1 Λ (x + t • v)) := by
  have hE : IsGeodesic (I := 𝓘(ℝ, E3)) (scaleMetric c hc (euclideanMetric (E := E3)))
      (fun t : ℝ => x + t • v) :=
    (isGeodesic_scaleMetric_iff c hc).mpr (isGeodesic_euclidean_line_FXC1 x v)
  have hpres : ∀ (y : E3) (a b : TangentSpace 𝓘(ℝ, E3) y),
      (scaleMetric c hc (euclideanMetric (E := E3))).inner y a b =
        (scaleMetric c hc (torMetric_FXC1 Λ)).inner (torPi_FXC1 Λ y)
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) y a)
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) y b) := by
    intro y a b
    rw [scaleMetric_inner, scaleMetric_inner]
    congr 1
    rw [← localPullMetric_inner (torMetric_FXC1 Λ) (torPi_FXC1 Λ)
      (torPi_isLocalDiffeomorph_FXC1 Λ), torMetric_localPull_FXC1]
  have h := geoOn_map_localIso (I := 𝓘(ℝ, E3)) (J := 𝓘(ℝ, E3))
    (scaleMetric c hc (euclideanMetric (E := E3))) (scaleMetric c hc (torMetric_FXC1 Λ))
    (torPi_isLocalDiffeomorph_FXC1 Λ) hpres (γ := fun t : ℝ => x + t • v) (s := univ)
    isOpen_univ (by fun_prop) (hE.isGeodesicOn univ)
  exact fun t => h t (mem_univ t)

end DifferentialGeometry.Geometry.Collapse
