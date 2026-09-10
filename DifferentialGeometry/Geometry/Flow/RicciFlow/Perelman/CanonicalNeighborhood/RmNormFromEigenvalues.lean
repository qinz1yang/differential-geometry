import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Pinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.Interfaces
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.CheegerGromovCompactness
open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators



section MatrixAlgebra

theorem trace_mul_self_eq_sum_sq_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ i : n, hA.eigenvalues i ^ 2 := by
  classical
  set U : Matrix n n Real := (hA.eigenvectorUnitary : Matrix n n Real) with hU
  set D : Matrix n n Real := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hUs : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hspec : A = U * D * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [hU, hD]
  calc Matrix.trace (A * A)
      = Matrix.trace ((U * D * star U) * (U * D * star U)) := by rw [← hspec]
    _ = Matrix.trace (U * (D * D) * star U) := by
        congr 1
        simp only [mul_assoc]
        rw [← mul_assoc (star U) U, hUs, one_mul]
    _ = Matrix.trace (D * D * (star U * U)) := by
        rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc]
    _ = Matrix.trace (D * D) := by rw [hUs, mul_one]
    _ = ∑ i : n, hA.eigenvalues i ^ 2 := by
        rw [hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [sq]

theorem sum_mul_self_eq_sum_sq_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.IsHermitian) :
    ∑ p : n, ∑ q : n, A p q * A p q = ∑ i : n, hA.eigenvalues i ^ 2 := by
  have hsymm : ∀ p q : n, A q p = A p q := by
    intro p q
    have h := congrFun (congrFun hA q) p
    simpa [Matrix.conjTranspose_apply] using h.symm
  have htr : Matrix.trace (A * A) = ∑ p : n, ∑ q : n, A p q * A p q := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hsymm p q]
  rw [← htr, trace_mul_self_eq_sum_sq_eigenvalues hA]

end MatrixAlgebra



section NormSquare

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem normSq0S_eq_four_mul_sum_sq_orderedSectionalCurvaturesAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    normSq0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x) =
      4 * ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i ^ 2 := by
  classical
  have hM : (curvatureOperatorMatrixAt (I := I) x basis A).IsHermitian :=
    curvatureOperatorMatrixAt_isHermitian (I := I) x basis A
  have hperm : ∑ i : Fin 3, hM.eigenvalues i ^ 2 =
      ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i ^ 2 := by
    unfold orderedSectionalCurvaturesAt Matrix.IsHermitian.eigenvalues
    exact (Fintype.equivOfCardEq (Fintype.card_fin 3)).symm.sum_comp
      (fun j => hM.eigenvalues₀ j ^ 2)
  rw [normSq0S, inner0S_algebraic_eq_four_mul_operatorInner (I := I) g x basis horth A A,
    sum_mul_self_eq_sum_sq_eigenvalues hM, hperm]

omit [CompleteSpace E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_normSq0S_le_of_abs_orderedSectionalCurvaturesAt_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) {a : Real}
    (ha : ∀ i : Fin 3, |orderedSectionalCurvaturesAt (I := I) x basis A i| ≤ a) :
    Real.sqrt (normSq0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x)) ≤
      2 * Real.sqrt 3 * a := by
  have hann : (0 : Real) ≤ a := le_trans (abs_nonneg _) (ha 0)
  have hsq : ∀ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i ^ 2 ≤ a ^ 2 := by
    intro i
    have h1 := ha i
    have h2 := abs_nonneg (orderedSectionalCurvaturesAt (I := I) x basis A i)
    nlinarith [sq_abs (orderedSectionalCurvaturesAt (I := I) x basis A i)]
  have hsum : ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i ^ 2 ≤ 3 * a ^ 2 := by
    rw [Fin.sum_univ_three]
    linarith [hsq 0, hsq 1, hsq 2]
  have hexp := normSq0S_eq_four_mul_sum_sq_orderedSectionalCurvaturesAt
    (I := I) g x basis horth A
  have hle : normSq0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x) ≤ 12 * a ^ 2 := by
    rw [hexp]
    linarith
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq12 : (12 : Real) * a ^ 2 = (2 * Real.sqrt 3 * a) ^ 2 := by
    nlinarith [h3]
  calc Real.sqrt (normSq0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x))
      ≤ Real.sqrt (12 * a ^ 2) := Real.sqrt_le_sqrt hle
    _ = 2 * Real.sqrt 3 * a := by
        rw [hsq12]
        exact Real.sqrt_sq (by positivity)

end NormSquare



section FlowForm

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis) {a : Real}
    (ha : ∀ i : Fin 3, |orderedSectionalCurvaturesAt (I := I) x basis
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ i| ≤ a) :
    Real.sqrt (FlowMetricBall.rmNormSq (I := I) S t x) ≤ 2 * Real.sqrt 3 * a :=
  sqrt_normSq0S_le_of_abs_orderedSectionalCurvaturesAt_le (I := I) (S.base.metric t) x basis
    horth ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩ ha

end FlowForm

section Packaged

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

theorem exists_rmNormLeOfCurvatureOperatorBounds (I : ModelWithCorners Real E H) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
        (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
        OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
        ∀ a : Real,
          (∀ i : Fin 3, |orderedSectionalCurvaturesAt (I := I) x basis
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩ i| ≤ a) →
            Real.sqrt (FlowMetricBall.rmNormSq (I := I) S t x) ≤ C * a := by
  refine ⟨2 * Real.sqrt 3, by positivity, ?_⟩
  intro M _ _ _ _ _ _ D S t x basis horth a ha
  exact sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le (I := I) S t x basis horth ha

end Packaged



section NonnegativeOperator

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg
    (S : SolutionOn (I := I) (M := M) D) (hdim : Module.finrank Real E = 3)
    (t : Real) (x : M)
    (hnn : curvatureOperatorLowerBoundAt (I := I) (S.base.metric t) x
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ 0) :
    Real.sqrt (FlowMetricBall.rmNormSq (I := I) S t x) ≤ Real.sqrt 3 * S.scalar t x := by
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    calc Module.finrank Real (TangentSpace I x) = Module.finrank Real E := rfl
      _ = 3 := hdim
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t) x hdimT
  have hmin := (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le (I := I)
    (S.base.metric t) x basis horth
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩ 0).mp hnn
  have hanti := orderedSectionalCurvaturesAt_antitone (I := I) x basis
    (⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩ :
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
  have hnonneg : ∀ i : Fin 3, 0 ≤ orderedSectionalCurvaturesAt (I := I) x basis
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ i := by
    intro i
    have hi : i ≤ (2 : Fin 3) := by
      fin_cases i <;> decide
    have hle := hanti hi
    linarith
  have hscal := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt (I := I) S basis horth
  rw [Fin.sum_univ_three] at hscal
  have hub : ∀ i : Fin 3, |orderedSectionalCurvaturesAt (I := I) x basis
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ i| ≤ S.scalar t x / 2 := by
    intro i
    rw [abs_of_nonneg (hnonneg i)]
    have hi0 := hanti (Fin.zero_le i)
    have h1 := hnonneg 1
    have h2 := hnonneg 2
    linarith
  have hmain := sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le
    (I := I) S t x basis horth hub
  have hval : 2 * Real.sqrt 3 * (S.scalar t x / 2) = Real.sqrt 3 * S.scalar t x := by
    ring
  linarith [hmain, hval]

end NonnegativeOperator

section PointedFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

theorem rmNormBoundedByScalarCurvature_of_finrank_three (I : ModelWithCorners Real E H)
    (hdim : Module.finrank Real E = 3) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        (∀ t ∈ D.carrier,
          letI : TopologicalSpace F.M := F.topology
          letI : ChartedSpace H F.M := F.charted
          letI : IsManifold I ∞ F.M := F.smooth
          letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
            change IsManifold I ∞ F.M
            infer_instance
          letI : SigmaCompactSpace F.M := F.sigmaCompact
          letI : T2Space F.M := F.t2
          ∀ x : F.M, ∀ (n : Nat) (c : Fin n → Real) (v w : Fin n → TangentSpace I x),
            0 ≤ ∑ i, ∑ j, c i * c j *
              (F.S.base.rm04 t x (vec4 (I := I) (v i) (w i) (w j) (v j)) +
                (0 : Real) *
                  ((F.S.base.metric t).inner x (v i) (v j) *
                      (F.S.base.metric t).inner x (w i) (w j) -
                    (F.S.base.metric t).inner x (v i) (w j) *
                      (F.S.base.metric t).inner x (w i) (v j)))) →
          letI : TopologicalSpace F.M := F.topology
          letI : ChartedSpace H F.M := F.charted
          letI : IsManifold I ∞ F.M := F.smooth
          letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
            change IsManifold I ∞ F.M
            infer_instance
          letI : SigmaCompactSpace F.M := F.sigmaCompact
          letI : T2Space F.M := F.t2
          ∀ t ∈ D.carrier, ∀ x : F.M,
            Real.sqrt (F.rmNormSq (I := I) t x) ≤ C * F.S.scalar t x := by
  refine ⟨Real.sqrt 3, Real.sqrt_nonneg 3, ?_⟩
  intro D F hlow
  let : TopologicalSpace F.M := F.topology
  let : ChartedSpace H F.M := F.charted
  let : IsManifold I ∞ F.M := F.smooth
  let : IsManifold I 1 F.M :=
    IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  let : SigmaCompactSpace F.M := F.sigmaCompact
  let : T2Space F.M := F.t2
  intro t ht x
  have hnn : curvatureOperatorLowerBoundAt (I := I) (F.S.base.metric t) x
      ⟨F.S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (F.S.base.metric t) x⟩ 0 := by
    intro n c v w
    have h := hlow t ht x n c v w
    simpa [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
      tensor04StandardAt] using h
  have hbound := sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg
    (I := I) F.S hdim t x hnn
  have hrm : F.rmNormSq (I := I) t x = FlowMetricBall.rmNormSq (I := I) F.S t x := by
    simp [PointedFlowData.rmNormSq, FlowMetricBall.rmNormSq]
  rw [hrm]
  exact hbound

end PointedFlow

end

section Wiring

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

theorem rmNormLeOfCurvatureOperatorBounds (I : ModelWithCorners Real E H) :
    RmNormLeOfCurvatureOperatorBounds.{u} I :=
  exists_rmNormLeOfCurvatureOperatorBounds I

theorem rmNormBoundedByScalarCurvature_dim_three (I : ModelWithCorners Real E H)
    (hdim : Module.finrank Real E = 3) :
    RmNormBoundedByScalarCurvature.{u} I :=
  rmNormBoundedByScalarCurvature_of_finrank_three I hdim

end Wiring

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
