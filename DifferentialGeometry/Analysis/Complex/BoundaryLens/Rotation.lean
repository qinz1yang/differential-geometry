import DifferentialGeometry.Analysis.Complex.BoundaryLens.Geometry
import DifferentialGeometry.Analysis.Integration.PlaneRotation
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Topology
open scoped NNReal

namespace CircleDeg1Lift

theorem continuous_mul_translate (ψ : CircleDeg1Lift) (hψ : Continuous ψ) (d : ℝ) :
    Continuous (ψ * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) : CircleDeg1Lift)) := by
  change Continuous (fun t : ℝ => ψ (d + t))
  exact hψ.comp (continuous_const.add continuous_id)

theorem sub_le_two_thirds_mul_translate (ψ : CircleDeg1Lift)
    (h₁ : ψ (1 / 3 : ℝ) = ψ 0 + 1 / 3)
    (h₂ : ψ (2 / 3 : ℝ) = ψ 0 + 2 / 3) (d : ℝ)
    {a b : ℝ} (hab : b - a ≤ 1 / 3) :
    (ψ * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) : CircleDeg1Lift)) b -
      (ψ * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) : CircleDeg1Lift)) a ≤ 2 / 3 := by
  change ψ (d + b) - ψ (d + a) ≤ 2 / 3
  exact ψ.sub_le_two_thirds_of_map_thirds h₁ h₂ (by linarith)

end CircleDeg1Lift

namespace DifferentialGeometry.Analysis

theorem preimage_rotated_boundaryLens (ζ : Circle) (r : ℝ) :
    rotation ζ ⁻¹' (Metric.closedBall (rotation ζ (-1)) r ∩ Metric.closedBall (0 : ℂ) 1) =
      boundaryLens r := by
  ext z
  simp only [boundaryLens, mem_preimage, mem_inter_iff, Metric.mem_closedBall,
    dist_zero_right, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.dist_map]

theorem preimage_rotated_annular_cap (ζ : Circle) (r R : ℝ) :
    rotation ζ ⁻¹' ({z : ℂ | dist z (rotation ζ (-1)) ∈ Icc r R} ∩
      Metric.closedBall (0 : ℂ) 1) =
      {z : ℂ | dist z (-1) ∈ Icc r R} ∩ Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, Metric.mem_closedBall,
    dist_zero_right, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.dist_map]

theorem lipschitzWith_comp_rotation {M : Type*} [PseudoEMetricSpace M]
    {f : ℂ → M} {K : ℝ≥0} (hf : LipschitzWith K f) (ζ : Circle) :
    LipschitzWith K (f ∘ rotation ζ) := by
  simpa only [mul_one] using hf.comp (rotation ζ).isometry.lipschitzWith

theorem mapsTo_comp_rotation_closedDisk {M : Type*} {f : ℂ → M} {S : Set M}
    (hf : MapsTo f (Metric.closedBall (0 : ℂ) 1) S) (ζ : Circle) :
    MapsTo (f ∘ rotation ζ) (Metric.closedBall (0 : ℂ) 1) S := by
  intro z hz
  apply hf
  simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hz

theorem circle_trace_comp_rotation {M : Type*} (f : ℂ → M) (Γ : loopCircle → M)
    (ψ : ℝ → ℝ)
    (htrace : ∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψ t : loopCircle))
    (d t : ℝ) :
    (f ∘ rotation (Circle.exp (2 * Real.pi * d))) (circleMap 0 1 (2 * Real.pi * t)) =
      Γ (ψ (d + t) : loopCircle) := by
  rw [Function.comp_apply, rotation_exp_circleMap,
    show 2 * Real.pi * d + 2 * Real.pi * t = 2 * Real.pi * (d + t) by ring, htrace]

theorem circle_lift_trace_comp_rotation {M : Type*} (f : ℂ → M) (Γ : loopCircle → M)
    (ψ : CircleDeg1Lift)
    (htrace : ∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψ t : loopCircle))
    (d t : ℝ) :
    (f ∘ rotation (Circle.exp (2 * Real.pi * d))) (circleMap 0 1 (2 * Real.pi * t)) =
      Γ ((ψ * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) :
        CircleDeg1Lift)) t : loopCircle) :=
  circle_trace_comp_rotation f Γ ψ htrace d t

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integral_quadratic_fderiv_comp_rotation_boundaryLens
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) (ζ : Circle) (r : ℝ) :
    (∫ z in boundaryLens r,
      (A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z 1)
          (fderiv ℝ (f ∘ rotation ζ) z 1) +
        A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z Complex.I)
          (fderiv ℝ (f ∘ rotation ζ) z Complex.I)) / 2) =
      ∫ z in Metric.closedBall (rotation ζ (-1)) r ∩ Metric.closedBall (0 : ℂ) 1,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  simpa only [preimage_rotated_boundaryLens] using
    integral_quadratic_fderiv_comp_rotation_preimage A f ζ
      (Metric.closedBall (rotation ζ (-1)) r ∩ Metric.closedBall (0 : ℂ) 1)

theorem integral_quadratic_fderiv_comp_rotation_annular_cap
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) (ζ : Circle) (r R : ℝ) :
    (∫ z in {z : ℂ | dist z (-1) ∈ Icc r R} ∩ Metric.closedBall (0 : ℂ) 1,
      (A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z 1)
          (fderiv ℝ (f ∘ rotation ζ) z 1) +
        A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z Complex.I)
          (fderiv ℝ (f ∘ rotation ζ) z Complex.I)) / 2) =
      ∫ z in {z : ℂ | dist z (rotation ζ (-1)) ∈ Icc r R} ∩ Metric.closedBall (0 : ℂ) 1,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  simpa only [preimage_rotated_annular_cap] using
    integral_quadratic_fderiv_comp_rotation_preimage A f ζ
      ({z : ℂ | dist z (rotation ζ (-1)) ∈ Icc r R} ∩ Metric.closedBall (0 : ℂ) 1)

end DifferentialGeometry.Analysis

end
