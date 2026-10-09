import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryMetric
import DifferentialGeometry.Geometry.Coordinates.StereographicComplex

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem stereographicComplex_pole_dist_sq
    (ξ : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
    dist ξ.val sphereNorthPole ^ 2 = 16 / (‖stereographicComplex ξ‖ ^ 2 + 4) := by
  have h := dist_stereographicComplex_symm_northPole_sq (stereographicComplex ξ)
  simpa only [stereographicComplex.symm_apply_apply] using h

private theorem stereographicComplex_pair_dist_sq
    (ξ η : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
    dist ξ.val η.val ^ 2 = 16 * dist (stereographicComplex ξ) (stereographicComplex η) ^ 2 /
      ((‖stereographicComplex ξ‖ ^ 2 + 4) * (‖stereographicComplex η‖ ^ 2 + 4)) := by
  have h := dist_stereographicComplex_symm_sq (stereographicComplex ξ) (stereographicComplex η)
  simpa only [stereographicComplex.symm_apply_apply] using h

theorem dist_stereographicComplex_boundaryHomeomorph
    (e : Hyperboloid E3 ≃ᵢ Hyperboloid E3)
    (hn : boundaryHomeomorph e sphereNorthPole = sphereNorthPole)
    (ξ η : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
    dist
      (stereographicComplex ⟨boundaryHomeomorph e ξ.val, by
        intro hp
        exact ξ.property ((boundaryHomeomorph e).injective (hp.trans hn.symm))⟩)
      (stereographicComplex ⟨boundaryHomeomorph e η.val, by
        intro hp
        exact η.property ((boundaryHomeomorph e).injective (hp.trans hn.symm))⟩) =
      (lorentzExtension e (1, (sphereNorthPole : E3))).1 *
        dist (stereographicComplex ξ) (stereographicComplex η) := by
  let f (u : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
      {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole} :=
    ⟨boundaryHomeomorph e u.val, fun hp => u.property
      ((boundaryHomeomorph e).injective (hp.trans hn.symm))⟩
  let scale := (lorentzExtension e (1, (sphereNorthPole : E3))).1
  let T (u : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :=
    (lorentzExtension e (1, (u.val : E3))).1
  let D (u : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :=
    ‖stereographicComplex u‖ ^ 2 + 4
  have hscalePos : 0 < scale := lorentzExtension_sphere_time_pos e sphereNorthPole
  have hT (u : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) : 0 < T u :=
    lorentzExtension_sphere_time_pos e u.val
  have hD (u : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) : 0 < D u := by
    dsimp [D]
    positivity
  have hscale (u : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
      D (f u) = D u * T u * scale := by
    have hh := dist_boundaryHomeomorph_sq e u.val sphereNorthPole
    rw [hn] at hh
    change dist (f u).val sphereNorthPole ^ 2 = dist u.val sphereNorthPole ^ 2 / (T u * scale) at hh
    rw [stereographicComplex_pole_dist_sq, stereographicComplex_pole_dist_sq] at hh
    change 16 / D (f u) = (16 / D u) / (T u * scale) at hh
    field_simp [(hD (f u)).ne', (hD u).ne', (hT u).ne', hscalePos.ne'] at hh
    nlinarith only [hh]
  have hpair := dist_boundaryHomeomorph_sq e ξ.val η.val
  change dist (f ξ).val (f η).val ^ 2 = dist ξ.val η.val ^ 2 / (T ξ * T η) at hpair
  rw [stereographicComplex_pair_dist_sq, stereographicComplex_pair_dist_sq] at hpair
  change 16 * dist (stereographicComplex (f ξ)) (stereographicComplex (f η)) ^ 2 /
      (D (f ξ) * D (f η)) =
    (16 * dist (stereographicComplex ξ) (stereographicComplex η) ^ 2 / (D ξ * D η)) /
      (T ξ * T η) at hpair
  rw [hscale ξ, hscale η] at hpair
  have hden : (D ξ * T ξ * scale) * (D η * T η * scale) =
      (D ξ * D η * (T ξ * T η)) * scale ^ 2 := by ring
  rw [hden, div_mul_eq_div_div, div_div] at hpair
  have hbase : D ξ * D η * (T ξ * T η) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hD ξ).ne' (hD η).ne') (mul_ne_zero (hT ξ).ne' (hT η).ne')
  have hsquare : dist (stereographicComplex (f ξ)) (stereographicComplex (f η)) ^ 2 =
      (scale * dist (stereographicComplex ξ) (stereographicComplex η)) ^ 2 := by
    have hm := congrArg (fun x : ℝ => x * (D ξ * D η * (T ξ * T η))) hpair
    field_simp [hbase, hscalePos.ne', (hD ξ).ne', (hD η).ne', (hT ξ).ne', (hT η).ne'] at hm
    nlinarith only [hm]
  change dist (stereographicComplex (f ξ)) (stereographicComplex (f η)) =
    scale * dist (stereographicComplex ξ) (stereographicComplex η)
  exact (sq_eq_sq₀ dist_nonneg (mul_nonneg hscalePos.le dist_nonneg)).mp hsquare

end DifferentialGeometry.Hyperboloid
