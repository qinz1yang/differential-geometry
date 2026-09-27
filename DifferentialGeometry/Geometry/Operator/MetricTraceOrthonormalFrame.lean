import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Bundle
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricTraceFirstTwo0SAt_eq_sum_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) {s : ℕ} {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (I := I) (M := M) (s + 2) x)
    (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt g T tail =
      ∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons (smoothOrthoFrame g x i x)
          (Fin.cons (smoothOrthoFrame g x i x) tail)) := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : IsEmpty (Fin (Module.finrank ℝ E)) := by
      simpa [hdim] using (Fin.isEmpty : IsEmpty (Fin 0))
    let basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      Module.finBasis ℝ (TangentSpace I x)
    have horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
      intro i
      exact isEmptyElim i
    rw [metricTraceFirstTwo0SAt_eq_sum_basis g basis identityInvMetric
      (metricInverseInBasis_identity_of_orthonormal g basis horth)]
    simp [metricTrace0S2InBasis]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let basis := (smoothOrtho_isLocal g x).toBasisAt (mem_smoothOrthoFrameNeighborhood_self x)
  have horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    simpa only [basis, IsLocalFrameOn.toBasisAt_coe] using
      smoothOrthoFrame_orthonormal_at_center g x i j
  rw [metricTraceFirstTwo0SAt_eq_sum_basis g basis identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g basis horth)]
  simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    basis, IsLocalFrameOn.toBasisAt_coe]
  rfl

end DifferentialGeometry.Geometry.Operator
