import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum
import DifferentialGeometry.Geometry.Neck.Orientation

noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck
universe u
private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩
private instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

theorem oriented_rotatedDatum_chart_eq_of_inward_matching
    (N : NormalizedNeck g δ k) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) (horn : NeckCylinder → M)
    (β : Sphere 2 ≃ Sphere 2) (a γ : ℝ) (hγ : γ ^ 2 = 1)
    (hsign : (N.rotatedDatum e he side).retainedSign = γ)
    (hmatch : ∀ (y : Sphere 2) (s : ℝ), |s| ≤ δ⁻¹ →
      ∀ hs : (β y, γ * s) ∈ neckBuffer δ,
        horn (y, a - s) = N.chart ⟨(β y, γ * s), hs⟩)
    (q : bufferedCylinder δ) (hq : q ∈ controlledCylinder δ) :
    (N.rotatedDatum e he side).oriented.map q =
      horn (β.symm (sphereDiffeo (n := 2) e q.val.1), a - q.val.2) := by
  have hqs : |q.val.2| ≤ δ⁻¹ := abs_le.mpr hq
  have hmem : (β (β.symm (sphereDiffeo (n := 2) e q.val.1)), γ * q.val.2) ∈ neckBuffer δ := by
    have hi := N.delta_pos
    change -δ⁻¹ - 1 < γ * q.val.2 ∧ γ * q.val.2 < δ⁻¹ + 1
    rcases sq_eq_one_iff.mp hγ with rfl | rfl <;> constructor <;> linarith [hq.1, hq.2]
  rw [hmatch _ _ hqs hmem]
  rw [normalizedDatum.oriented_map, rotatedDatum_map]
  apply congrArg N.chart
  apply Subtype.ext
  rw [bufferedCylinderRotation_apply, bufferedCylinderOrientation_apply, hsign, β.apply_symm_apply]

theorem exists_side_of_axial_sign (γ : ℝ) (hγ : γ ^ 2 = 1) :
    ∃ side : Bool, (if side then (1 : ℝ) else -1) = γ := by
  rcases sq_eq_one_iff.mp hγ with h | h
  · exact ⟨true, h.symm⟩
  · exact ⟨false, h.symm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck
