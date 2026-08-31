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
theorem metricRiemannFromRicci3DTraceDataAt
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

omit [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem linearIndependent_vec2_basis
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (i j : Fin 3) (hij : i ≠ j) :
    LinearIndependent Real (vec2 (I := I) (basis i) (basis j)) := by
  let e : Fin 2 → Fin 3 := fun q => if q = 0 then i else j
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e]
  have h := basis.linearIndependent.comp e he
  have heq : basis ∘ e = vec2 (I := I) (basis i) (basis j) := by
    funext q
    fin_cases q <;> simp [e, vec2]
  rw [heq] at h
  exact h

omit [I.Boundaryless] in
theorem curvature_eigenvalues_pos_of_sectional_pos
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (lambda mu nu : Real)
    (hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x)
      ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) basis)
    (hsec : ∀ (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    0 < lambda ∧ 0 < mu ∧ 0 < nu := by
  let Ric := metricRicciAt (I := I) (M := M) g x
  let Rm := metricRm04At (I := I) (M := M) g x
  have htrace := metricRiemannFromRicci3DTraceDataAt
    (I := I) (M := M) g x basis horth
  have hnegdiag :
      RicciDiagAt (I := I) (-Ric)
        (-(metricScalarAt (I := I) (M := M) g x))
        (-((mu + nu) / 2)) (-((lambda + nu) / 2)) (-((lambda + mu) / 2)) basis := by
    rcases hdiag with ⟨hscalar, hric⟩
    constructor
    · unfold ricciEigenScalar3 at hscalar ⊢
      linarith
    · intro i j
      change -(ricciCompAt (I := I) basis Ric i j) =
        ricciDiag3 (-((mu + nu) / 2)) (-((lambda + nu) / 2))
          (-((lambda + mu) / 2)) i j
      rw [hric i j]
      fin_cases i <;> fin_cases j <;> simp [ricciDiag3]
  have hcomp := stdRmComp_eq_diag (I := I) htrace hnegdiag
  have h01 :
      metricRm04StdAt (I := I) (M := M) g x
          (basis 0) (basis 1) (basis 1) (basis 0) = nu / 2 := by
    change standardRmCompAt (I := I) basis Rm 0 1 1 0 = nu / 2
    rw [hcomp]
    simp [stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3]
    ring
  have h02 :
      metricRm04StdAt (I := I) (M := M) g x
          (basis 0) (basis 2) (basis 2) (basis 0) = mu / 2 := by
    change standardRmCompAt (I := I) basis Rm 0 2 2 0 = mu / 2
    rw [hcomp]
    simp [stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3]
    ring
  have h12 :
      metricRm04StdAt (I := I) (M := M) g x
          (basis 1) (basis 2) (basis 2) (basis 1) = lambda / 2 := by
    change standardRmCompAt (I := I) basis Rm 1 2 2 1 = lambda / 2
    rw [hcomp]
    simp [stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3]
    ring
  have hnu := hsec (basis 0) (basis 1)
    (linearIndependent_vec2_basis (I := I) basis 0 1 (by decide))
  have hmu := hsec (basis 0) (basis 2)
    (linearIndependent_vec2_basis (I := I) basis 0 2 (by decide))
  have hlambda := hsec (basis 1) (basis 2)
    (linearIndependent_vec2_basis (I := I) basis 1 2 (by decide))
  rw [h01] at hnu
  rw [h02] at hmu
  rw [h12] at hlambda
  exact ⟨by linarith, by linarith, by linarith⟩

omit [I.Boundaryless] in
theorem exists_orthonormal_curvature_eigenframe
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3) :
    ∃ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      ∃ lambda mu nu : Real,
        OrthonormalBasisAt (I := I) g x basis ∧
          RicciDiagAt (I := I)
            (metricRicciAt (I := I) (M := M) g x)
            (metricScalarAt (I := I) (M := M) g x)
            ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) basis := by
  classical
  have hsymm :
      RicciSymAt (I := I) (metricRicciAt (I := I) (M := M) g x) := by
    intro U V
    let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis
      (I := I) x
    let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
      fun i j =>
        DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
          (I := I) g x i j (extChartAt I x x)
    have hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv := by
      simpa [basis, gInv] using
        (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
          (I := I) g x)
    have hcomp :
        ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          metricRicciAt (I := I) (M := M) g x
              (fun q : Fin 2 => if q = 0 then basis i else basis j) =
            metricRicciAt (I := I) (M := M) g x
              (fun q : Fin 2 => if q = 0 then basis j else basis i) := by
      intro i j
      change metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis j) (basis i))
      exact metricRicciSymm (I := I) (M := M) g basis gInv hinv i j
    exact
      DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
        (I := I) basis (metricRicciAt (I := I) (M := M) g x) hcomp U V
  obtain ⟨basis, l1, l2, l3, horth, hdiag⟩ :=
    ricciEigen3 (I := I) g
      (metricRicciAt (I := I) (M := M) g x) hdim hsymm
  have hinv : MetricInverseInBasisGen (I := I) g x basis delta3 :=
    orthonormal_invBasis3 (I := I) g basis horth
  have hcomp (i j : Fin 3) :
      metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        ricciDiag3 l1 l2 l3 i j := by
    simpa [ricciCompAt_apply] using hdiag.2 i j
  have hscalar :
      metricScalarAt (I := I) (M := M) g x =
        ricciEigenScalar3 l1 l2 l3 := by
    rw [metricScalarAt_def,
      metricTracePair0SAt_eq_sum_basis (I := I) g basis delta3 hinv]
    simp_rw [hcomp]
    unfold ricciEigenScalar3 ricciDiag3 delta3
    simp [Fin.sum_univ_three]
  let lambda := l2 + l3 - l1
  let mu := l1 + l3 - l2
  let nu := l1 + l2 - l3
  refine ⟨basis, lambda, mu, nu, horth, ?_⟩
  constructor
  · rw [hscalar]
    unfold ricciEigenScalar3
    dsimp [lambda, mu, nu]
    ring
  · intro i j
    rw [hdiag.2 i j]
    fin_cases i <;> fin_cases j <;>
      simp [ricciDiag3, lambda, mu, nu] <;> ring

theorem ricciReactionDefectAt_nonneg_of_finrank_eq_three
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3) :
    0 ≤ ricciReactionDefectAt (I := I) g x := by
  obtain ⟨basis, lambda, mu, nu, horth, hdiag⟩ :=
    exists_orthonormal_curvature_eigenframe (I := I) (M := M) g x hdim
  exact ricciReactionDefectAt_nonneg_of_curvature_eigenframe
    (I := I) (M := M) g x basis horth lambda mu nu hdiag

omit [I.Boundaryless] in
theorem metricScalarAt_pos_of_sectional_pos_of_finrank_eq_three
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsec : ∀ (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    0 < metricScalarAt (I := I) (M := M) g x := by
  obtain ⟨basis, lambda, mu, nu, horth, hdiag⟩ :=
    exists_orthonormal_curvature_eigenframe (I := I) (M := M) g x hdim
  obtain ⟨hlambda, hmu, hnu⟩ :=
    curvature_eigenvalues_pos_of_sectional_pos
      (I := I) (M := M) g x basis horth lambda mu nu hdiag hsec
  have hscalar := hdiag.1
  unfold ricciEigenScalar3 at hscalar
  nlinarith

theorem metricRicciAt_eq_scalar_div_three_of_ricciReactionDefectAt_eq_zero_of_sectional_pos
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hzero : ricciReactionDefectAt (I := I) g x = 0)
    (hsec : ∀ (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    ∀ v w : TangentSpace I x,
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) =
        (metricScalarAt (I := I) (M := M) g x / 3) * g.inner x v w := by
  obtain ⟨basis, lambda, mu, nu, horth, hdiag⟩ :=
    exists_orthonormal_curvature_eigenframe (I := I) (M := M) g x hdim
  obtain ⟨hlambda, _hmu, hnu⟩ :=
    curvature_eigenvalues_pos_of_sectional_pos
      (I := I) (M := M) g x basis horth lambda mu nu hdiag hsec
  obtain ⟨hlambda_mu, hmu_nu⟩ :=
    (ricciReactionDefectAt_eq_zero_iff_of_curvature_eigenframe
      (I := I) (M := M) g x basis horth lambda mu nu hdiag hlambda hnu).mp hzero
  subst mu
  subst nu
  have htensor :
      metricRicciAt (I := I) (M := M) g x =
        (metricScalarAt (I := I) (M := M) g x / 3) •
          metricTensor0S (I := I) g x := by
    apply ext0S_basis (I := I) basis
    intro slots
    simp only [component0S_apply, Tensor0SSpace.smul_apply, metricTensor0S_apply]
    have hslots :
        (fun a : Fin 2 => basis (slots a)) =
          vec2 (I := I) (basis (slots 0)) (basis (slots 1)) := by
      funext a
      fin_cases a <;> rfl
    rw [hslots]
    simp only [smul_eq_mul]
    have hric := hdiag.2 (slots 0) (slots 1)
    rw [ricciCompAt_apply] at hric
    rw [hric, horth]
    have hscalar := hdiag.1
    unfold ricciEigenScalar3 at hscalar
    generalize hi : slots 0 = i
    generalize hj : slots 1 = j
    fin_cases i <;> fin_cases j <;>
      simp [ricciDiag3, delta3] at hscalar ⊢ <;> nlinarith
  intro v w
  have happly := congrArg
    (fun A : Tensor02At (I := I) (M := M) x => A (vec2 (I := I) v w)) htensor
  simpa [Tensor0SSpace.smul_apply, metricTensor0S_apply, vec2, smul_eq_mul] using happly

omit [I.Boundaryless] in
theorem metricRm04StdAt_eq_scalar_div_six_of_finrank_eq_three_of_einstein
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hEin : ∀ v w : TangentSpace I x,
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) =
        (metricScalarAt (I := I) (M := M) g x / 3) * g.inner x v w) :
    ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        (metricScalarAt (I := I) (M := M) g x / 6) *
          (g.inner x X X * g.inner x Y Y -
            g.inner x X Y * g.inner x X Y) := by
  obtain ⟨basis, _lambda, _mu, _nu, horth, _hdiag⟩ :=
    exists_orthonormal_curvature_eigenframe (I := I) (M := M) g x hdim
  let K := metricCurvData (I := I) (M := M) g
  have hcurv :
      AlgebraicCurvatureSymmetries3
        (standardRmCompAt (I := I) basis
          (metricRm04At (I := I) (M := M) g x)) :=
    algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes basis
  have hinv : MetricInverseInBasisGen (I := I) g x basis delta3 :=
    orthonormal_invBasis3 (I := I) g basis horth
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
  have hRic :
      RicciRealizesRm04FirstTraceAt (I := I)
        (metricRicciAt (I := I) (M := M) g x)
        (metricRm04At (I := I) (M := M) g x) delta3 basis :=
    ricciFirstTraceAt_of_rm13 (I := I) g basis delta3 hinv
      (metricRicciAt (I := I) (M := M) g x)
      (metricRm13At (I := I) (M := M) g x)
      (metricRm04At (I := I) (M := M) g x)
      (metricRicciAt_eq_trace (I := I) (M := M) g x) hLower
  have hScalar :
      ScalarRealizesRicciTraceAt (I := I)
        (metricScalarAt (I := I) (M := M) g x)
        (metricRicciAt (I := I) (M := M) g x) delta3 basis := by
    unfold ScalarRealizesRicciTraceAt
    rw [metricScalarAt_def]
    exact metricTracePair0SAt_eq_sum_basis (I := I) g basis delta3 hinv
      (metricRicciAt (I := I) (M := M) g x)
  have hEinComp : ∀ i j : Fin 3,
      ricciCompAt (I := I) basis
          (metricRicciAt (I := I) (M := M) g x) i j =
        (metricScalarAt (I := I) (M := M) g x / 3) * delta3 i j := by
    intro i j
    rw [ricciCompAt_apply, hEin, horth]
  intro X Y
  exact rm04Std_ein3_at (I := I) horth hcurv hRic hScalar hEinComp X Y

end DifferentialGeometry.Geometry.Curvature
