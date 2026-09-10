import Batteries.Tactic.Alias
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import DifferentialGeometry.Geometry.Curvature.Nonnegative
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

def hasPositiveSectionalCurvature
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ x : M, ∀ W T : TangentSpace I x,
    LinearIndependent ℝ ![W, T] →
      0 < metricRm04StandardAt (I := I) (M := M) g x W T T W

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem metricRm04StandardAt_eq_zero_of_not_linearIndependent
    (g : SmoothRiemannianMetric I M) (x : M)
    (W T : TangentSpace I x) (hdep : ¬ LinearIndependent ℝ ![W, T]) :
    metricRm04StandardAt (I := I) (M := M) g x W T T W = 0 := by
  let B : TangentSpace I x → TangentSpace I x → TangentSpace I x →
      TangentSpace I x → ℝ :=
    fun X Y Z U ↦ metricRm04StandardAt (I := I) (M := M) g x X Y Z U
  have hB : IsAlgCurvForm B := by
    change IsAlgCurvForm
      (tensor04StandardAt (I := I) (M := M)
        (metricRm04At (I := I) (M := M) g x))
    exact mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (M := M) g x)
  by_cases hW : W = 0
  · subst W
    have hzero := hB.smul_left 0 (0 : TangentSpace I x) T T 0
    simpa [B] using hzero
  · rw [LinearIndependent.pair_iff' hW] at hdep
    push Not at hdep
    obtain ⟨a, rfl⟩ := hdep
    have hdiag : B W W (a • W) W = 0 := by
      have hskew := hB.anti_first W W (a • W) W
      linarith
    have hskew := hB.anti_first W (a • W) (a • W) W
    have hsmul := hB.smul_left a W W (a • W) W
    change B W (a • W) (a • W) W = 0
    rw [hskew, hsmul, hdiag]
    ring

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem hasPositiveSectionalCurvature.toNonnegative
    {g : SmoothRiemannianMetric I M}
    (hsec : hasPositiveSectionalCurvature (I := I) g) :
    hasNonnegativeSectionalCurvature (I := I) g := by
  rw [hasNonnegativeSectionalCurvature_iff (I := I) g]
  intro x W T
  by_cases hlin : LinearIndependent ℝ ![W, T]
  · exact (hsec x W T hlin).le
  · rw [metricRm04StandardAt_eq_zero_of_not_linearIndependent
      (I := I) (M := M) g x W T hlin]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem gram_determinant_pos (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (hvw : LinearIndependent ℝ ![v, w]) :
    0 < g.inner x v v * g.inner x w w - g.inner x v w ^ 2 := by
  have hv : v ≠ 0 := hvw.ne_zero 0
  have ha := g.pos x v hv
  let a := g.inner x v v
  let b := g.inner x v w
  have hne : a • w - b • v ≠ 0 := by
    intro hz
    have hh := hvw.eq_zero_of_pair' (sub_eq_zero.mp hz).symm
    exact ha.ne' hh.2
  have hz := g.pos x (a • w - b • v) hne
  have heq : g.inner x (a • w - b • v) (a • w - b • v) =
      a * (a * g.inner x w w - b ^ 2) := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [g.symm x w v]
    dsimp only [a, b]
    ring
  rw [heq] at hz
  exact pos_of_mul_pos_right hz ha.le

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem positive_sectional_iff_quotient (g : SmoothRiemannianMetric I M) :
    hasPositiveSectionalCurvature g ↔
      ∀ x : M, ∀ v w : TangentSpace I x, LinearIndependent ℝ ![v, w] →
        0 < metricRm04StandardAt g x v w w v /
          (g.inner x v v * g.inner x w w - g.inner x v w ^ 2) := by
  constructor
  · intro hg x v w hvw
    exact div_pos (hg x v w hvw) (gram_determinant_pos g x v w hvw)
  · intro hg x v w hvw
    exact (div_pos_iff_of_pos_right (gram_determinant_pos g x v w hvw)).mp (hg x v w hvw)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem tangent_pair_linearIndependent_of_orthonormal (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) (hv : g.inner x v v = 1)
    (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0) :
    LinearIndependent ℝ ![v, w] := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hwv : g.inner x w v = 0 := (g.symm x w v).trans hvw
  have ho : Orthonormal ℝ ![v, w] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact hv
    · exact hvw
    · exact hwv
    · exact hw
  exact ho.linearIndependent

omit [SigmaCompactSpace M] in
theorem riemann_contraction_pos_of_orthonormal
    (g : SmoothRiemannianMetric I M)
    (hsec : hasPositiveSectionalCurvature (I := I) g)
    (x : M) (v w : TangentSpace I x) (hv : g.inner x v v = 1)
    (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0) :
    0 < g.inner x (riemannOp (LeviCivita (I := I) g) x v w w) v := by
  have hpos := hsec x v w (tangent_pair_linearIndependent_of_orthonormal g x v w hv hw hvw)
  rw [rm04_eq_inner_riem, g.symm] at hpos
  exact hpos

end DifferentialGeometry.Geometry

namespace Poincare.Geometry

@[reducible] alias HasPositiveSectionalCurvature := DifferentialGeometry.Geometry.hasPositiveSectionalCurvature
end Poincare.Geometry

namespace Poincare.Geometry.HasPositiveSectionalCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem toNonnegative {g : DifferentialGeometry.SmoothRiemannianMetric I M}
    (hsec : Poincare.Geometry.HasPositiveSectionalCurvature (I := I) g) :
    Poincare.Geometry.HasNonnegativeSectionalCurvature (I := I) g :=
  DifferentialGeometry.Geometry.hasPositiveSectionalCurvature.toNonnegative hsec

end Poincare.Geometry.HasPositiveSectionalCurvature

namespace Poincare.Geometry

alias gram_determinant_pos := DifferentialGeometry.Geometry.gram_determinant_pos
alias positive_sectional_iff_quotient := DifferentialGeometry.Geometry.positive_sectional_iff_quotient
alias tangent_pair_linearIndependent_of_orthonormal := DifferentialGeometry.Geometry.tangent_pair_linearIndependent_of_orthonormal
alias riemann_contraction_pos_of_orthonormal := DifferentialGeometry.Geometry.riemann_contraction_pos_of_orthonormal

end Poincare.Geometry
