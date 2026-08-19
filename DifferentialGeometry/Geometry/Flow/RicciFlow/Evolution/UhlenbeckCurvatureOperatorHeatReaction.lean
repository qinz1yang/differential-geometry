import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ComponentwiseHeatReaction
import DifferentialGeometry.Analysis.InnerProductSpace.MatrixEuclidean
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorLeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIveyRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Uhlenbeck

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable def uhlenbeckCurvatureOperatorMatrix
    (pulledRm : FourComp M (Fin 3)) : Real → M → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  fun t x => WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 =>
    pulledRm t x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
      (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1)

noncomputable def uhlenbeckCurvatureOperatorMatrixAsMatrix
    (pulledRm : FourComp M (Fin 3)) : Real → M → Matrix (Fin 3) (Fin 3) Real :=
  fun t x i j => uhlenbeckCurvatureOperatorMatrix pulledRm t x (i, j)

omit [TopologicalSpace M] in
@[simp] theorem uhlenbeckCurvatureOperatorMatrixAsMatrix_apply
    (pulledRm : FourComp M (Fin 3)) (t : Real) (x : M)
    (i j : Fin 3) :
    uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x i j =
      uhlenbeckCurvatureOperatorMatrix pulledRm t x (i, j) := by
  rfl


omit [FiniteDimensional Real E] [CompleteSpace E] in
theorem uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    {x : M} {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x}
    {pulledRm : FourComp M (Fin 3)} {t : Real}
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t x a b c d =
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis c) (basis d)) :
    uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x =
      curvatureOperatorMatrixAt (I := I) x basis A := by
  ext i j
  unfold uhlenbeckCurvatureOperatorMatrixAsMatrix uhlenbeckCurvatureOperatorMatrix
    curvatureOperatorMatrixAt
  simp [hpull]


omit [FiniteDimensional Real E] [CompleteSpace E] in
theorem uhlenbeckCurvatureOperatorMatrixAsMatrix_isHermitian
    {x : M} {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x}
    {pulledRm : FourComp M (Fin 3)} {t : Real}
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t x a b c d =
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis c) (basis d)) :
    (uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x).IsHermitian := by
  rw [uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    (I := I) (M := M) (x := x) (basis := basis) (A := A) (pulledRm := pulledRm) (t := t) hpull]
  exact curvatureOperatorMatrixAt_isHermitian (I := I) x basis A


omit [FiniteDimensional Real E] [CompleteSpace E] in
theorem uhlenbeckCurvatureOperatorMatrixAsMatrix_mem_hamiltonIveyRegion_iff
    {x : M} {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x}
    {pulledRm : FourComp M (Fin 3)} {t K τ : Real}
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t x a b c d =
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis c) (basis d)) :
    uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x ∈
        hamiltonIveyConvexMatrixRegion K τ ↔
      curvatureOperatorMatrixAt (I := I) x basis A ∈
        hamiltonIveyConvexMatrixRegion K τ := by
  rw [uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    (I := I) (M := M) (x := x) (basis := basis) (A := A) (pulledRm := pulledRm) (t := t) hpull]


noncomputable def uhlenbeckCurvatureOperatorReaction
    (B : FourComp M (Fin 3)) :
    Real → M → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  fun t x => WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 =>
    let a := (bivectorIndex3 ij.1).1;
    let b := (bivectorIndex3 ij.1).2;
    let c := (bivectorIndex3 ij.2).2;
    let d := (bivectorIndex3 ij.2).1;
    -2 * (B t x a b c d - B t x a b d c + B t x a c b d - B t x a d b c))

omit [CompleteSpace E] [TopologicalSpace M] in
theorem uhlenbeckCurvatureOperatorReaction_lipschitz
    (B : FourComp M (Fin 3)) (t : Real) (x : M) :
    LipschitzWith 0 (fun _ : EuclideanSpace ℝ (Fin 3 × Fin 3) =>
      uhlenbeckCurvatureOperatorReaction B t x) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro a b
  simp [uhlenbeckCurvatureOperatorReaction, dist_eq_norm]


omit [CompleteSpace E] in
theorem innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (pulledRm roughLapD B : FourComp M (Fin 3))
    (hU : UhlenbeckCurvatureEvolutionInFrameOn (D := D) pulledRm roughLapD B)
    (hlap : ∀ t : Real, t ∈ D.carrier → ∀ x : M, ∀ ij : Fin 3 × Fin 3,
      roughLapD t x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
          (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1 =
        laplacianAt (I := I) G t
          (fun y : M => uhlenbeckCurvatureOperatorMatrix pulledRm t y ij) x)
    (hjoint : ContinuousOn (fun q : Real × M => uhlenbeckCurvatureOperatorMatrix pulledRm q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hsmooth : ∀ ij : Fin 3 × Fin 3, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M => uhlenbeckCurvatureOperatorMatrix pulledRm t x ij)) :
    IsInnerProductHeatReactionOn (D := D) (G := G)
      (F := EuclideanSpace ℝ (Fin 3 × Fin 3))
      (fun t x _ => uhlenbeckCurvatureOperatorReaction B t x)
      (uhlenbeckCurvatureOperatorMatrix pulledRm) := by
  refine innerProductHeatReactionOn_of_componentwise (D := D) (G := G)
    (u := uhlenbeckCurvatureOperatorMatrix pulledRm)
    (reaction := fun t x _ => uhlenbeckCurvatureOperatorReaction B t x) hjoint hsmooth ?_
  intro ij t ht x
  let a := (bivectorIndex3 ij.1).1
  let b := (bivectorIndex3 ij.1).2
  let c := (bivectorIndex3 ij.2).2
  let d := (bivectorIndex3 ij.2).1
  have hU' := hU ⟨t, ht⟩ x a b c d
  have hderivAt : HasDerivAt (fun s : Real => pulledRm s x a b c d)
      (uhlenbeckCurvatureEvolutionRHSInFrame roughLapD B (t : Real) x a b c d) (t : Real) :=
    hU'.hasDerivAt (D.regular_mem_nhds ht)
  have hrhs : uhlenbeckCurvatureEvolutionRHSInFrame roughLapD B (t : Real) x a b c d =
      laplacianAt (I := I) G (t : Real)
          (fun y : M => uhlenbeckCurvatureOperatorMatrix pulledRm (t : Real) y ij) x +
        uhlenbeckCurvatureOperatorReaction B (t : Real) x ij := by
    unfold uhlenbeckCurvatureEvolutionRHSInFrame uhlenbeckCurvatureOperatorReaction
    rw [hlap (t : Real) (D.regular_subset ht) x ij]
    ring
  have hmain := hderivAt.congr_deriv hrhs
  simpa [uhlenbeckCurvatureOperatorMatrix, a, b, c, d] using hmain

omit [CompleteSpace E] in
omit [TopologicalSpace M] in
theorem uhlenbeckCurvatureOperatorMatrix_eq_matrixToEuclid
    (pulledRm : FourComp M (Fin 3)) (t : Real) (x : M) :
    uhlenbeckCurvatureOperatorMatrix pulledRm t x =
      matrixToEuclid (uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x) := by
  simp [uhlenbeckCurvatureOperatorMatrix, uhlenbeckCurvatureOperatorMatrixAsMatrix,
    matrixToEuclid]

omit [TopologicalSpace M] in
theorem inner_uhlenbeckCurvatureOperatorMatrix_eq_matrix
    (ν : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (pulledRm : FourComp M (Fin 3)) (t : Real) (x : M) :
    inner ℝ ν (uhlenbeckCurvatureOperatorMatrix pulledRm t x) =
      ∑ ij : Fin 3 × Fin 3,
        ν ij * uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x ij.1 ij.2 := by
  change inner ℝ ν (matrixToEuclid
      (fun i j : Fin 3 => uhlenbeckCurvatureOperatorMatrix pulledRm t x (i, j))) =
    ∑ ij : Fin 3 × Fin 3,
      ν ij * uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x ij.1 ij.2
  rw [inner_matrixToEuclid]
  simp [uhlenbeckCurvatureOperatorMatrix, uhlenbeckCurvatureOperatorMatrixAsMatrix]

omit [CompleteSpace E] in
theorem uhlenbeckCurvatureOperator_halfspace_mem_of_tangent
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {T : Real} (hT : 0 ≤ T)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (pulledRm roughLapD B : FourComp M (Fin 3))
    (hU : UhlenbeckCurvatureEvolutionInFrameOn (D := D) pulledRm roughLapD B)
    (hlap : ∀ t : Real, t ∈ D.carrier → ∀ x : M, ∀ ij : Fin 3 × Fin 3,
      roughLapD t x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
          (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1 =
        laplacianAt (I := I) G t
          (fun y : M => uhlenbeckCurvatureOperatorMatrix pulledRm t y ij) x)
    (hjoint : ContinuousOn (fun q : Real × M => uhlenbeckCurvatureOperatorMatrix pulledRm q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hsmooth : ∀ ij : Fin 3 × Fin 3, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M => uhlenbeckCurvatureOperatorMatrix pulledRm t x ij))
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (ν : EuclideanSpace ℝ (Fin 3 × Fin 3)) (hν : ν ≠ 0)
    (s : Real → Real)
    (hsdiff : ∀ t : Real, t ∈ Set.Icc 0 T →
      DifferentiableWithinAt Real s (Set.Icc 0 T) t)
    (htangent : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      ∀ A : EuclideanSpace ℝ (Fin 3 × Fin 3),
        inner ℝ ν A = s t →
          inner ℝ ν (uhlenbeckCurvatureOperatorReaction B t x) ≤
            derivWithin s (Set.Icc 0 T) t)
    (hinit : ∀ x : M,
      inner ℝ ν (uhlenbeckCurvatureOperatorMatrix pulledRm 0 x) ≤ s 0) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      inner ℝ ν (uhlenbeckCurvatureOperatorMatrix pulledRm t x) ≤ s t := by
  have hU_closed : UhlenbeckCurvatureEvolutionInFrameOn
      (D := RealTimeInterval.closed 0 T hT) pulledRm roughLapD B := by
    intro t x a b c d
    have htreg : (t : Real) ∈ D.regular := hTreg ⟨t.2.1, le_of_lt t.2.2⟩
    have hderiv := hU ⟨(t : Real), htreg⟩ x a b c d
    have hmono : Set.Icc 0 T ⊆ D.carrier := hTsub
    exact hderiv.mono hmono
  have hsol : IsInnerProductHeatReactionOn
      (D := RealTimeInterval.closed 0 T hT) (G := G)
      (F := EuclideanSpace ℝ (Fin 3 × Fin 3))
      (fun t x _ => uhlenbeckCurvatureOperatorReaction B t x)
      (uhlenbeckCurvatureOperatorMatrix pulledRm) := by
    exact innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator
      (I := I) (M := M) G pulledRm roughLapD B hU_closed
      (fun t ht x ij => hlap t (hTsub ht) x ij)
      (hjoint.mono (by intro q hq; exact ⟨hTsub hq.1, hq.2⟩))
      (fun ij t ht => hsmooth ij t (hTsub ht))
  have hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith 0 (fun _ : EuclideanSpace ℝ (Fin 3 × Fin 3) =>
        uhlenbeckCurvatureOperatorReaction B t x) := by
    intro t ht x
    refine LipschitzWith.of_dist_le_mul ?_
    intro a b
    simp [uhlenbeckCurvatureOperatorReaction, dist_eq_norm]
  exact timeDepHalfspace_heat_reaction_mem_of_tangent
    (I := I) (M := M) G hT ν hν s hsdiff
    (fun t x _ => uhlenbeckCurvatureOperatorReaction B t x)
    (uhlenbeckCurvatureOperatorMatrix pulledRm) hsol 0 hL htangent hinit

omit [CompleteSpace E] in
theorem uhlenbeckCurvatureOperator_mem_timeDepConvex_of_tangent
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {T : Real} (hT : 0 ≤ T)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (pulledRm roughLapD B : FourComp M (Fin 3))
    (hU : UhlenbeckCurvatureEvolutionInFrameOn (D := D) pulledRm roughLapD B)
    (hlap : ∀ t : Real, t ∈ D.carrier → ∀ x : M, ∀ ij : Fin 3 × Fin 3,
      roughLapD t x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
          (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1 =
        laplacianAt (I := I) G t
          (fun y : M => uhlenbeckCurvatureOperatorMatrix pulledRm t y ij) x)
    (hjoint : ContinuousOn (fun q : Real × M => uhlenbeckCurvatureOperatorMatrix pulledRm q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hsmooth : ∀ ij : Fin 3 × Fin 3, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M => uhlenbeckCurvatureOperatorMatrix pulledRm t x ij))
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (C : Real → Set (EuclideanSpace ℝ (Fin 3 × Fin 3)))
    (hKne : ({q : WithLp 2 (EuclideanSpace ℝ (Fin 3 × Fin 3) × ℝ) |
      (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧ (WithLp.ofLp q).1 ∈ C (WithLp.ofLp q).2}).Nonempty)
    (hKclosed : IsClosed ({q : WithLp 2 (EuclideanSpace ℝ (Fin 3 × Fin 3) × ℝ) |
      (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧ (WithLp.ofLp q).1 ∈ C (WithLp.ofLp q).2}))
    (hKconvex : Convex Real ({q : WithLp 2 (EuclideanSpace ℝ (Fin 3 × Fin 3) × ℝ) |
      (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧ (WithLp.ofLp q).1 ∈ C (WithLp.ofLp q).2}))
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (fun q : WithLp 2 (EuclideanSpace ℝ (Fin 3 × Fin 3) × ℝ) =>
        WithLp.toLp 2 (uhlenbeckCurvatureOperatorReaction B (WithLp.ofLp q).2 x,
          (1 : Real))))
    (htangent : ∀ τ : Real, τ ∈ Set.Ico 0 T → ∀ x : M, ∀ A : EuclideanSpace ℝ (Fin 3 × Fin 3),
      A ∈ C τ →
        WithLp.toLp 2 (uhlenbeckCurvatureOperatorReaction B τ x, (1 : Real)) ∈
          posTangentConeAt {q : WithLp 2 (EuclideanSpace ℝ (Fin 3 × Fin 3) × ℝ) |
            (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧ (WithLp.ofLp q).1 ∈ C (WithLp.ofLp q).2}
            (WithLp.toLp 2 (A, τ)))
    (htangent_fiber : ∀ τ : Real, τ ∈ Set.Icc 0 T → ∀ x : M, ∀ A : EuclideanSpace ℝ (Fin 3 × Fin 3),
      A ∈ C τ → uhlenbeckCurvatureOperatorReaction B τ x ∈ posTangentConeAt (C τ) A)
    (hinit : ∀ x : M, uhlenbeckCurvatureOperatorMatrix pulledRm 0 x ∈ C 0) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      uhlenbeckCurvatureOperatorMatrix pulledRm t x ∈ C t := by
  have hU_closed : UhlenbeckCurvatureEvolutionInFrameOn
      (D := RealTimeInterval.closed 0 T hT) pulledRm roughLapD B := by
    intro t x a b c d
    have htreg : (t : Real) ∈ D.regular := hTreg ⟨t.2.1, le_of_lt t.2.2⟩
    have hderiv := hU ⟨(t : Real), htreg⟩ x a b c d
    have hmono : Set.Icc 0 T ⊆ D.carrier := hTsub
    exact hderiv.mono hmono
  have hsol : IsInnerProductHeatReactionOn
      (D := RealTimeInterval.closed 0 T hT) (G := G)
      (F := EuclideanSpace ℝ (Fin 3 × Fin 3))
      (fun t x _ => uhlenbeckCurvatureOperatorReaction B t x)
      (uhlenbeckCurvatureOperatorMatrix pulledRm) := by
    exact innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator
      (I := I) (M := M) G pulledRm roughLapD B hU_closed
      (fun t ht x ij => hlap t (hTsub ht) x ij)
      (hjoint.mono (by intro q hq; exact ⟨hTsub hq.1, hq.2⟩))
      (fun ij t ht => hsmooth ij t (hTsub ht))
  let K : Set (WithLp 2 (EuclideanSpace ℝ (Fin 3 × Fin 3) × ℝ)) :=
    {q | (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧ (WithLp.ofLp q).1 ∈ C (WithLp.ofLp q).2}
  exact closed_convex_heat_reaction_mem_of_timeDep_tangent
    (I := I) (M := M) G hT C K rfl hKne hKclosed hKconvex
    (fun t x _ => uhlenbeckCurvatureOperatorReaction B t x)
    (uhlenbeckCurvatureOperatorMatrix pulledRm) hsol L hL htangent htangent_fiber hinit




end DifferentialGeometry.PDE.RicciFlow

end
