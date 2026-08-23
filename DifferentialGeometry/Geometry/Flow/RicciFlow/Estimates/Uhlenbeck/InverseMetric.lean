import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Isometry
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped BigOperators Topology NNReal Manifold ContDiff Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def solutionGramMatrix
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (t : Real) (x : M) : Matrix Idx Idx ℝ :=
  Matrix.of (fun i j =>
    metricCompInFrame (I := I) S (fun a x => basisAt x a) t x i j)

omit [Fintype Idx] [DecidableEq Idx] [SigmaCompactSpace M] [T2Space M] in
theorem solutionGramMatrix_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (t : Real) (x : M) (i j : Idx) :
    solutionGramMatrix (I := I) (M := M) S basisAt t x i j =
      (S.family.metric t).inner x (basisAt x i) (basisAt x j) := by
  rfl

omit [Fintype Idx] [DecidableEq Idx] [SigmaCompactSpace M] [T2Space M] in
theorem solutionGramMatrix_posDef
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (t : Real) (x : M) :
    (solutionGramMatrix (I := I) (M := M) S basisAt t x).PosDef := by
  classical
  letI : Finite Idx := Module.Finite.finite_basis (basisAt x)
  letI : Fintype Idx := Fintype.ofFinite Idx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ?_
  constructor
  · ext i j
    simp only [solutionGramMatrix, Matrix.conjTranspose]
    exact (S.family.metric t).symm x (basisAt x j) (basisAt x i)
  · intro v hv
    have hlin : LinearIndependent ℝ (fun i : Idx => basisAt x i) :=
      (basisAt x).linearIndependent
    have hinj : Function.Injective (Fintype.linearCombination ℝ (fun i : Idx => basisAt x i)) :=
      (linearIndependent_iff_injective_fintypeLinearCombination.mp hlin)
    have hb : (∑ i : Idx, v i • basisAt x i) ≠ 0 := by
      intro hzero
      have hz : Fintype.linearCombination ℝ (fun i : Idx => basisAt x i) v = 0 := by
        simpa [Fintype.linearCombination] using hzero
      exact hv (hinj (by simpa [Fintype.linearCombination] using hz))
    have hdot : v ⬝ᵥ (solutionGramMatrix (I := I) (M := M) S basisAt t x *ᵥ v) =
        (S.family.metric t).inner x (∑ i : Idx, v i • basisAt x i)
          (∑ i : Idx, v i • basisAt x i) := by
      calc
        v ⬝ᵥ (solutionGramMatrix (I := I) (M := M) S basisAt t x *ᵥ v)
            = ∑ i : Idx, v i * (∑ j : Idx,
                (S.family.metric t).inner x (basisAt x i) (basisAt x j) * v j) := by
              simp [solutionGramMatrix, metricCompInFrame, dotProduct,
                Matrix.mulVec, Finset.mul_sum]
        _ = ∑ i : Idx, v i * ((S.family.metric t).inner x (basisAt x i)
              (∑ j : Idx, v j • basisAt x j)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              congr 1
              simp only [map_sum, map_smul, smul_eq_mul]
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = (S.family.metric t).inner x (∑ i : Idx, v i • basisAt x i)
              (∑ i : Idx, v i • basisAt x i) := by
              simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum',
                ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
                smul_eq_mul, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x1 hx1
              apply Finset.sum_congr rfl
              intro i hi
              rw [show (S.family.metric t).inner x (basisAt x x1) (basisAt x i) =
                  (S.family.metric t).inner x (basisAt x i) (basisAt x x1) from
                (S.family.metric t).symm x (basisAt x x1) (basisAt x i)]
    have hdot' : star v ⬝ᵥ (solutionGramMatrix (I := I) (M := M) S basisAt t x *ᵥ v) =
        (S.family.metric t).inner x (∑ i : Idx, v i • basisAt x i)
          (∑ i : Idx, v i • basisAt x i) := by
      simpa [star_trivial] using hdot
    rw [hdot']
    exact (S.family.metric t).pos x (∑ i : Idx, v i • basisAt x i) hb

omit [SigmaCompactSpace M] [T2Space M] in
theorem solutionGramMatrix_det_isUnit
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (t : Real) (x : M) :
    IsUnit (solutionGramMatrix (I := I) (M := M) S basisAt t x).det := by
  have hunit := (solutionGramMatrix_posDef (I := I) (M := M) S basisAt t x).isUnit
  exact IsUnit.map (Matrix.detMonoidHom) hunit

noncomputable def solutionInverseMetricComponents
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x)) :
    Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx :=
  fun t x i j => (solutionGramMatrix (I := I) (M := M) S basisAt t x)⁻¹ i j

omit [SigmaCompactSpace M] [T2Space M] in
theorem solutionInverseMetricComponents_mul_metric
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (t : Real) (x : M) (i j : Idx) :
    (∑ k : Idx, solutionInverseMetricComponents (I := I) (M := M) S basisAt t x i k *
        metricCompInFrame (I := I) S (fun a x => basisAt x a) t x k j) =
      if i = j then 1 else 0 := by
  have h := Matrix.nonsing_inv_mul (A := solutionGramMatrix (I := I) (M := M) S basisAt t x)
    (solutionGramMatrix_det_isUnit (I := I) (M := M) S basisAt t x)
  have hentry := congrFun (congrFun h i) j
  simpa [solutionInverseMetricComponents, solutionGramMatrix, Matrix.mul_apply,
    Matrix.one_apply] using hentry

omit [SigmaCompactSpace M] [T2Space M] in
theorem solutionInverseMetricComponents_symm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (t : Real) (x : M) (i j : Idx) :
    solutionInverseMetricComponents (I := I) (M := M) S basisAt t x i j =
      solutionInverseMetricComponents (I := I) (M := M) S basisAt t x j i := by
  classical
  have hsymm : (solutionGramMatrix (I := I) (M := M) S basisAt t x).transpose =
      solutionGramMatrix (I := I) (M := M) S basisAt t x := by
    ext a b
    simp only [solutionGramMatrix, Matrix.transpose_apply]
    exact (S.family.metric t).symm x (basisAt x b) (basisAt x a)
  have htr := Matrix.transpose_nonsing_inv (A := solutionGramMatrix (I := I) (M := M) S basisAt t x)
  unfold solutionInverseMetricComponents
  have hmain := congrFun (congrFun htr i) j
  rw [hsymm] at hmain
  simpa [Matrix.transpose_apply] using hmain.symm

omit [SigmaCompactSpace M] in
theorem solutionInverseMetricComponents_entry_continuousOn
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (x : M) (i j : Idx) :
    ContinuousOn (fun t : ℝ => solutionInverseMetricComponents (I := I) (M := M) S basisAt t x i j)
      (Set.Icc 0 T) := by
  classical
  have hsub : Set.Icc 0 T ⊆ (RealTimeInterval.closed 0 T hT.le).carrier := by
    intro s hs
    exact hs
  have hcoeff : ∀ a b : Idx,
      ContinuousOn (fun s : ℝ =>
        (S.family.metric s).inner x (basisAt x a) (basisAt x b)) (Set.Icc 0 T) := by
    intro a b
    simpa [metricCompInFrame] using (hS.smoothMetric.coeff_cont x (basisAt x a) (basisAt x b)).mono hsub
  have hgram_cont : ContinuousOn
      (fun t : ℝ => solutionGramMatrix (I := I) (M := M) S basisAt t x)
      (Set.Icc 0 T) := by
    change ContinuousOn (fun t : ℝ => fun a b : Idx =>
      solutionGramMatrix (I := I) (M := M) S basisAt t x a b) (Set.Icc 0 T)
    rw [continuousOn_pi]
    intro a
    rw [continuousOn_pi]
    intro b
    simpa [solutionGramMatrix, metricCompInFrame] using hcoeff a b
  have hne : ∀ s : ℝ, s ∈ Set.Icc 0 T →
      (solutionGramMatrix (I := I) (M := M) S basisAt s x).det ≠ 0 := by
    intro s hs
    exact (solutionGramMatrix_det_isUnit (I := I) (M := M) S basisAt s x).ne_zero
  have hinvOn : ContinuousOn (fun A : Matrix Idx Idx ℝ => A⁻¹)
      {A : Matrix Idx Idx ℝ | IsUnit A.det} := by
    refine continuousOn_of_forall_continuousAt ?_
    intro A hA
    exact continuousAt_matrix_inv A (by
      have hdet : A.det ≠ 0 := hA.ne_zero
      simpa [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet))
  have hmaps : Set.MapsTo (fun t : ℝ => solutionGramMatrix (I := I) (M := M) S basisAt t x)
      (Set.Icc 0 T) {A : Matrix Idx Idx ℝ | IsUnit A.det} := by
    intro t ht
    exact solutionGramMatrix_det_isUnit (I := I) (M := M) S basisAt t x
  have hinv_cont : ContinuousOn
      (fun t : ℝ => (solutionGramMatrix (I := I) (M := M) S basisAt t x)⁻¹)
      (Set.Icc 0 T) :=
    hinvOn.comp hgram_cont hmaps
  have hproj : Continuous (fun A : Matrix Idx Idx ℝ => A i j) := by
    change Continuous (fun A : Idx → Idx → ℝ => (A i) j)
    exact (continuous_apply (i := j) : Continuous (fun B : Idx → ℝ => B j)).comp
      (continuous_apply (i := i))
  have hcomp := hproj.comp_continuousOn hinv_cont
  simpa [solutionInverseMetricComponents] using hcomp

end DifferentialGeometry.PDE.RicciFlow

end
