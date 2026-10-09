import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SlotInsertion
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] [CompleteSpace E]

omit [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompleteSpace E] [SigmaCompactSpace M] in
theorem endoCovariantDerivative_g0_self_adjoint
    (g₀ : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (hΛ : ∀ (y : M) (a b : TangentSpace I y),
      g₀.inner y (Λ y a) b = g₀.inner y a (Λ y b))
    (x : M) (v : TangentSpace I x) (a b : TangentSpace I x) :
    g₀.inner x ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v a) b =
      g₀.inner x a ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v b) := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g₀.toRiemannianMetric⟩
  let tangentNorm : ∀ y, NormedAddCommGroup (TangentSpace I y) :=
    fun y => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := (TangentSpace I : M → Type _)) y
  let _ : ∀ y, SeminormedAddCommGroup (TangentSpace I y) :=
    fun y => (tangentNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (TangentSpace I y) :=
    fun y => Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) y
  let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
    ⟨g₀.inner, g₀.contMDiff.of_le (by simp), fun _ _ _ => rfl⟩
  have hmetric : @_root_.CovariantDerivative.IsMetricCompatible
      E _ _ H _ I M _ _ E _ _ (TangentSpace I) _ tangentNorm _ _ (LeviCivita g₀) _ _ _ _ := by
    apply (@_root_.CovariantDerivative.isMetricCompatible_iff
      E _ _ H _ I M _ _ E _ _ (TangentSpace I) _ tangentNorm _ _ (LeviCivita g₀) _ _ _ _ _).mpr
    intro y X Y Z _ hY hZ
    exact (LeviCivita_isMetricCompatible g₀).apply hY hZ (X y)
  exact @HomConnectionGen.homBundleCovariantDerivativeGen_isSymmetric_of_eventually
    E _ _ _ H _ I M _ _ _ _ E _ _ _ (TangentSpace I) _ tangentNorm _ _ _ _ _
    (LeviCivita g₀) hmetric Λ x (Filter.Eventually.of_forall hΛ) v a b

end DifferentialGeometry.Geometry.Connection
