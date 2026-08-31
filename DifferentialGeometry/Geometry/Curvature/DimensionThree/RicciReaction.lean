import DifferentialGeometry.Geometry.Curvature.CurvatureRicciContraction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {x : M}

noncomputable def ricciReactionDefectAt
    (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  let Ric := metricRicci (I := I) (M := M) g
  normSq0S (I := I) g x 2 (Ric x) ^ 2 -
    metricScalarAt (I := I) g x *
      inner0S (I := I) g x 2
        (curvatureRicciContractionAt (I := I) (M := M) g x) (Ric x)

omit [I.Boundaryless] in
private theorem metricRiemannFromRicci3DTraceDataAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    RiemannFromRicci3DTraceDataAt (I := I) g
      (-(metricRicciAt (I := I) (M := M) g x))
      (-(metricScalarAt (I := I) (M := M) g x))
      (metricRm04At (I := I) (M := M) g x) basis := by
  let K := metricCurvData (I := I) (M := M) g
  have hLower :
      Rm04LowersRm13At (I := I) g x
        (metricRm13At (I := I) (M := M) g x)
        (metricRm04At (I := I) (M := M) g x) := by
    exact rm04LowersRm13At_of_realizes
      (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      K.rm13Realizes K.rm04Realizes x
  have hcurv :
      AlgebraicCurvatureSymmetries3
        (standardRmCompAt (I := I) basis
          (metricRm04At (I := I) (M := M) g x)) :=
    algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes basis
  have hRicFirst :
      RicciRealizesRm04FirstTraceAt (I := I)
        (metricRicciAt (I := I) (M := M) g x)
        (metricRm04At (I := I) (M := M) g x) delta3 basis := by
    have hinv : MetricInverseInBasisGen (I := I) g x basis delta3 :=
      orthonormal_invBasis3 (I := I) g basis horth
    exact ricciFirstTraceAt_of_rm13 (I := I) g basis delta3 hinv
      (metricRicciAt (I := I) (M := M) g x)
      (metricRm13At (I := I) (M := M) g x)
      (metricRm04At (I := I) (M := M) g x)
      (metricRicciAt_eq_trace (I := I) (M := M) g x) hLower
  have hScalarTrace :
      ScalarRealizesRicciTraceAt (I := I)
        (metricScalarAt (I := I) (M := M) g x)
        (metricRicciAt (I := I) (M := M) g x) delta3 basis := by
    have hinv : MetricInverseInBasisGen (I := I) g x basis delta3 :=
      orthonormal_invBasis3 (I := I) g basis horth
    unfold ScalarRealizesRicciTraceAt
    rw [metricScalarAt_def]
    exact metricTracePair0SAt_eq_sum_basis (I := I) g basis delta3 hinv
      (metricRicciAt (I := I) (M := M) g x)
  exact traceDataOfFirst (I := I) horth hcurv hRicFirst hScalarTrace

private noncomputable def ricciReaction3 (l1 l2 l3 : Real) : Real :=
  l1 * l2 * (l1 + l2 - l3) +
    l1 * l3 * (l1 + l3 - l2) +
      l2 * l3 * (l2 + l3 - l1)

private theorem inner_curvatureRicciContraction_metricRicci_eq_ricciReaction3
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (l1 l2 l3 : Real)
    (hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x) l1 l2 l3 basis) :
    inner0S (I := I) g x 2
        (curvatureRicciContractionAt (I := I) (M := M) g x)
        (metricRicciAt (I := I) (M := M) g x) =
      ricciReaction3 l1 l2 l3 := by
  classical
  let Ric := metricRicciAt (I := I) (M := M) g x
  let Rm := metricRm04At (I := I) (M := M) g x
  have hinv : MetricInverseInBasisGen (I := I) g x basis delta3 :=
    orthonormal_invBasis3 (I := I) g basis horth
  have htrace := metricRiemannFromRicci3DTraceDataAt
    (I := I) (M := M) g x basis horth
  have hnegdiag :
      RicciDiagAt (I := I) (-Ric)
        (-(metricScalarAt (I := I) (M := M) g x))
        (-l1) (-l2) (-l3) basis := by
    rcases hdiag with ⟨hscalar, hric⟩
    constructor
    · unfold ricciEigenScalar3 at hscalar ⊢
      linarith
    · intro i j
      change -(ricciCompAt (I := I) basis Ric i j) =
        ricciDiag3 (-l1) (-l2) (-l3) i j
      rw [hric i j]
      fin_cases i <;> fin_cases j <;> simp [ricciDiag3]
  have hRm : forall i j k l : Fin 3,
      rm04CompAt (I := I) basis Rm i j k l =
        stdRmDiag3 (-l1) (-l2) (-l3) i j k l := by
    simpa [standardRmCompAt_apply] using
      stdRmComp_eq_diag (I := I) htrace hnegdiag
  have hRmRaw (i j k l : Fin 3) :
      metricRm04At (I := I) (M := M) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) =
        stdRmDiag3 (-l1) (-l2) (-l3) i j k l := by
    simpa [rm04CompAt_apply] using hRm i j k l
  have hRicRaw (i j : Fin 3) :
      metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        ricciDiag3 l1 l2 l3 i j := by
    simpa [ricciCompAt_apply] using hdiag.2 i j
  have hP : forall i j : Fin 3,
      curvatureRicciContractionAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        -(∑ k : Fin 3, ∑ l : Fin 3,
          stdRmDiag3 (-l1) (-l2) (-l3) i k j l *
            ricciDiag3 l1 l2 l3 k l) := by
    intro i j
    rw [curvatureRicciContractionAt_eq_neg_rm04RicciContractionAt
      (I := I) (M := M) g x basis horth i j]
    unfold rm04RicciContractionAt raised02CompAt
    simp only [identityInvMetric, diagonalInvMetric]
    simp_rw [hRmRaw]
    simp_rw [hRicRaw]
    simp [Fin.sum_univ_three]
  rw [inner0S_two_eq_coord (I := I) g x basis delta3 hinv]
  have hvec (i j : Fin 3) :
      (fun a : Fin 2 => if a = 0 then basis i else basis j) =
        vec2 (I := I) (basis i) (basis j) := by
    funext a
    fin_cases a <;> simp [vec2]
  simp_rw [hvec]
  simp_rw [hP]
  simp_rw [hRicRaw]
  unfold ricciReaction3 stdRmDiag3 ricciDiag3 ricciEigenScalar3 delta3
  simp [Fin.sum_univ_three]
  ring

omit [I.Boundaryless] [T2Space M] in
private theorem normSq_metricRicci_eq_ricciEigenNormSq3
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (l1 l2 l3 : Real)
    (hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x) l1 l2 l3 basis) :
    normSq0S (I := I) g x 2
        (metricRicciAt (I := I) (M := M) g x) =
      ricciEigenNormSq3 l1 l2 l3 := by
  classical
  have hinv : MetricInverseInBasisGen (I := I) g x basis delta3 :=
    orthonormal_invBasis3 (I := I) g basis horth
  rw [normSq0S_two_eq_coord (I := I) g x basis delta3 hinv]
  have hvec (i j : Fin 3) :
      (fun a : Fin 2 => if a = 0 then basis i else basis j) =
        vec2 (I := I) (basis i) (basis j) := by
    funext a
    fin_cases a <;> simp [vec2]
  simp_rw [hvec]
  have hcomp (i j : Fin 3) :
      metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        ricciDiag3 l1 l2 l3 i j := by
    simpa [ricciCompAt_apply] using hdiag.2 i j
  simp_rw [hcomp]
  unfold ricciEigenNormSq3 ricciDiag3 delta3
  simp [Fin.sum_univ_three]
  ring

theorem ricciReactionDefectAt_eq_curvatureReactionPolynomial3
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (lambda mu nu : Real)
    (hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x)
      ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) basis) :
    ricciReactionDefectAt (I := I) g x =
      curvatureReactionPolynomial3 lambda mu nu := by
  let l1 := (mu + nu) / 2
  let l2 := (lambda + nu) / 2
  let l3 := (lambda + mu) / 2
  have hnorm := normSq_metricRicci_eq_ricciEigenNormSq3
    (I := I) (M := M) g x basis horth l1 l2 l3 hdiag
  have hinner := inner_curvatureRicciContraction_metricRicci_eq_ricciReaction3
    (I := I) (M := M) g x basis horth l1 l2 l3 hdiag
  unfold ricciReactionDefectAt
  simp only [metricRicci_apply]
  rw [hnorm, hinner, hdiag.1]
  unfold curvatureReactionPolynomial3 ricciReaction3 ricciEigenScalar3
  dsimp [l1, l2, l3]
  ring

theorem ricciReactionDefectAt_nonneg_of_curvature_eigenframe
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (lambda mu nu : Real)
    (hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x)
      ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) basis) :
    0 ≤ ricciReactionDefectAt (I := I) g x := by
  rw [ricciReactionDefectAt_eq_curvatureReactionPolynomial3
    (I := I) (M := M) g x basis horth lambda mu nu hdiag]
  exact curvatureReactionPolynomial3_nonneg lambda mu nu

theorem ricciReactionDefectAt_eq_zero_iff_of_curvature_eigenframe
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (lambda mu nu : Real)
    (hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x)
      ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) basis)
    (hlambda : 0 < lambda) (hnu : 0 < nu) :
    ricciReactionDefectAt (I := I) g x = 0 ↔
      lambda = mu ∧ mu = nu := by
  rw [ricciReactionDefectAt_eq_curvatureReactionPolynomial3
    (I := I) (M := M) g x basis horth lambda mu nu hdiag]
  exact curvatureReactionPolynomial3_eq_zero_iff lambda mu nu hlambda hnu

end DifferentialGeometry.Geometry.Curvature
