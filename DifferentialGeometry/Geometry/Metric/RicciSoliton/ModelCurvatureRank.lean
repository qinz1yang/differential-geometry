import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature
open Curvature.DimensionThree

private theorem curvatureOperatorDiagonal3_rank_zero :
    (curvatureOperatorDiagonal3 0 0 0).rank = 0 := by
  simp [curvatureOperatorDiagonal3, sec12Ric3, sec13Ric3, sec23Ric3]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

theorem euclideanMetric_curvatureOperatorRankAt
    (x : E) (hdim : Module.finrank Real E = 3) :
    metricCurvatureOperatorRankAt (I := modelWithCornersSelf Real E)
      (euclideanMetric (E := E)) x hdim = 0 := by
  obtain ⟨basis, horth⟩ := Curvature.exists_orthonormalBasisAt
    (I := modelWithCornersSelf Real E) (euclideanMetric (E := E)) x hdim
  rw [metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (I := modelWithCornersSelf Real E)
      (euclideanMetric (E := E)) x hdim basis horth]
  have hdiag : RicciDiagAt (I := modelWithCornersSelf Real E)
      (metricRicciAt (I := modelWithCornersSelf Real E)
        (euclideanMetric (E := E)) x)
      (metricScalarAt (I := modelWithCornersSelf Real E)
        (euclideanMetric (E := E)) x)
      0 0 0 basis := by
    constructor
    · rw [euclideanMetric_scalarCurvature]
      simp [ricciEigenScalar3]
    · intro i j
      rw [ricciCompAt_apply, metricRicciAt_apply_eq_ricciTensor,
        euclideanMetric_ricciTensor]
      simp [ricciDiag3]
  rw [metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
    (I := modelWithCornersSelf Real E)
      (euclideanMetric (E := E)) x basis horth 0 0 0 hdiag]
  exact curvatureOperatorDiagonal3_rank_zero

theorem roundThreeSphereShrinkerMetric_curvatureOperatorRankAt
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :
    metricCurvatureOperatorRankAt
      (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 3)))
      roundThreeSphereShrinkerMetric x (by
        change Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3
        simp) = 3 := by
  have hdim : Module.finrank Real (TangentSpace
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))) x) = 3 := by
    change Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3
    simp
  change metricCurvatureOperatorRankAt
      (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 3)))
      roundThreeSphereShrinkerMetric x hdim = 3
  obtain ⟨basis, horth⟩ := Curvature.exists_orthonormalBasisAt
    (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 3)))
      roundThreeSphereShrinkerMetric x hdim
  rw [metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 3)))
      roundThreeSphereShrinkerMetric x hdim basis horth]
  have hdiag : RicciDiagAt
      (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 3)))
      (metricRicciAt
        (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 3)))
        roundThreeSphereShrinkerMetric x)
      (metricScalarAt
        (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 3)))
        roundThreeSphereShrinkerMetric x)
      (1 / 2 : Real) (1 / 2 : Real) (1 / 2 : Real) basis := by
    constructor
    · rw [roundThreeSphereShrinkerMetric_scalarCurvature]
      norm_num [ricciEigenScalar3]
    · intro i j
      rw [ricciCompAt_apply, metricRicciAt_apply_eq_ricciTensor]
      let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) :=
        ⟨by simp⟩
      rw [show roundThreeSphereShrinkerMetric =
          roundSphereShrinkerMetric
            (A := EuclideanSpace Real (Fin 4)) (n := 3) (by decide) by
        rfl]
      rw [roundSphereShrinkerMetric_ricciTensor (by decide)]
      have hinner :
          (roundSphereShrinkerMetric
            (A := EuclideanSpace Real (Fin 4)) (n := 3) (by decide)).inner x
              (basis i) (basis j) = delta3 i j := by
        simpa [roundThreeSphereShrinkerMetric, roundSphereShrinkerMetric] using horth i j
      rw [hinner]
      fin_cases i <;> fin_cases j <;>
        norm_num [ricciDiag3, delta3]
  rw [metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
    (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 3)))
      roundThreeSphereShrinkerMetric x basis horth
      (1 / 2 : Real) (1 / 2 : Real) (1 / 2 : Real) hdiag]
  simp [curvatureOperatorDiagonal3, sec12Ric3, sec13Ric3, sec23Ric3,
    Matrix.rank_diagonal]

set_option backward.isDefEq.respectTransparency false in
noncomputable def roundThreeCylinderProductBasis
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (basisM : Module.Basis (Fin 2) Real
      (TangentSpace (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) x.1))
    (basisN : Module.Basis (Fin 1) Real
      (TangentSpace (modelWithCornersSelf Real Real) x.2)) :
    Module.Basis (Fin 3) Real
      (TangentSpace ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) x) := by
  let basisSum : Module.Basis (Fin 2 ⊕ Fin 1) Real
      (TangentSpace ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) x) := basisM.prod basisN
  exact basisSum.reindex (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)

set_option backward.isDefEq.respectTransparency false in
private theorem roundThreeCylinder_product_basis_orthonormal
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (basisM : Module.Basis (Fin 2) Real
      (TangentSpace (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) x.1))
    (basisN : Module.Basis (Fin 1) Real
      (TangentSpace (modelWithCornersSelf Real Real) x.2))
    (hM : ∀ i j : Fin 2,
      roundTwoSphereShrinkerMetric.inner x.1 (basisM i) (basisM j) =
        if i = j then (1 : Real) else 0)
    (hN : ∀ i j : Fin 1,
      (euclideanMetric (E := Real)).inner x.2 (basisN i) (basisN j) =
        if i = j then (1 : Real) else 0) :
    OrthonormalBasisAt (I :=
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) roundThreeCylinderShrinkerMetric x
      (roundThreeCylinderProductBasis x basisM basisN) := by
  let basisSum : Module.Basis (Fin 2 ⊕ Fin 1) Real
      (TangentSpace ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) x) := basisM.prod basisN
  let eSum : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv
  have hbasisSum_inl (i : Fin 2) : basisSum (Sum.inl i) = (basisM i, 0) := by
    apply Prod.ext
    · change ((basisM.prod basisN) (Sum.inl i)).1 = _
      exact Module.Basis.prod_apply_inl_fst basisM basisN i
    · change ((basisM.prod basisN) (Sum.inl i)).2 = _
      exact Module.Basis.prod_apply_inl_snd basisM basisN i
  have hbasisSum_inr (i : Fin 1) : basisSum (Sum.inr i) = (0, basisN i) := by
    apply Prod.ext
    · change ((basisM.prod basisN) (Sum.inr i)).1 = _
      exact Module.Basis.prod_apply_inr_fst basisM basisN i
    · change ((basisM.prod basisN) (Sum.inr i)).2 = _
      exact Module.Basis.prod_apply_inr_snd basisM basisN i
  have hprod : ∀ i j : Fin 2 ⊕ Fin 1,
      roundThreeCylinderShrinkerMetric.inner x (basisSum i) (basisSum j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · rw [hbasisSum_inl, hbasisSum_inl, roundThreeCylinderShrinkerMetric,
        SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
      change roundTwoSphereShrinkerMetric.inner x.1 (basisM i) (basisM j) +
        (euclideanMetric (E := Real)).inner x.2 0 0 = _
      rw [hM]
      simp
    · rw [hbasisSum_inl, hbasisSum_inr, roundThreeCylinderShrinkerMetric,
        SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
      change roundTwoSphereShrinkerMetric.inner x.1 (basisM i) 0 +
        (euclideanMetric (E := Real)).inner x.2 0 (basisN j) = _
      simp
    · rw [hbasisSum_inr, hbasisSum_inl, roundThreeCylinderShrinkerMetric,
        SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
      change roundTwoSphereShrinkerMetric.inner x.1 0 (basisM j) +
        (euclideanMetric (E := Real)).inner x.2 (basisN i) 0 = _
      simp
    · rw [hbasisSum_inr, hbasisSum_inr, roundThreeCylinderShrinkerMetric,
        SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
      change roundTwoSphereShrinkerMetric.inner x.1 0 0 +
        (euclideanMetric (E := Real)).inner x.2 (basisN i) (basisN j) = _
      rw [hN]
      simp
  intro i j
  simpa [roundThreeCylinderProductBasis, Module.Basis.reindex_apply, delta3] using
    hprod (eSum.symm i) (eSum.symm j)

set_option backward.isDefEq.respectTransparency false in
private theorem roundThreeCylinder_product_basis_ricciDiag
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (basisM : Module.Basis (Fin 2) Real
      (TangentSpace (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) x.1))
    (basisN : Module.Basis (Fin 1) Real
      (TangentSpace (modelWithCornersSelf Real Real) x.2))
    (hM : ∀ i j : Fin 2,
      roundTwoSphereShrinkerMetric.inner x.1 (basisM i) (basisM j) =
        if i = j then (1 : Real) else 0) :
    RicciDiagAt
      (I := (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real))
      (metricRicciAt (I := (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) roundThreeCylinderShrinkerMetric x)
      (metricScalarAt (I := (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) roundThreeCylinderShrinkerMetric x)
      (1 / 2 : Real) (1 / 2 : Real) 0
      (roundThreeCylinderProductBasis x basisM basisN) := by
  let basisSum : Module.Basis (Fin 2 ⊕ Fin 1) Real
      (TangentSpace ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) x) := basisM.prod basisN
  let eSum : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv
  have hbasisSum_inl (i : Fin 2) : basisSum (Sum.inl i) = (basisM i, 0) := by
    apply Prod.ext
    · change ((basisM.prod basisN) (Sum.inl i)).1 = _
      exact Module.Basis.prod_apply_inl_fst basisM basisN i
    · change ((basisM.prod basisN) (Sum.inl i)).2 = _
      exact Module.Basis.prod_apply_inl_snd basisM basisN i
  have hbasisSum_inr (i : Fin 1) : basisSum (Sum.inr i) = (0, basisN i) := by
    apply Prod.ext
    · change ((basisM.prod basisN) (Sum.inr i)).1 = _
      exact Module.Basis.prod_apply_inr_fst basisM basisN i
    · change ((basisM.prod basisN) (Sum.inr i)).2 = _
      exact Module.Basis.prod_apply_inr_snd basisM basisN i
  let basis := (basisM.prod basisN).reindex eSum
  have hroundRicci (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (u v : TangentSpace (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) y) :
      ricciTensor (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 2)))
          roundTwoSphereShrinkerMetric y u v =
        (1 / 2 : Real) * roundTwoSphereShrinkerMetric.inner y u v := by
    let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
      ⟨by simp⟩
    simpa [roundTwoSphereShrinkerMetric] using
      (roundSphereShrinkerMetric_ricciTensor
        (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide) y u v)
  constructor
  · rw [roundThreeCylinderShrinkerMetric_scalarCurvature]
    norm_num [ricciEigenScalar3]
  · intro i j
    have hRicciSum : ∀ i j : Fin 2 ⊕ Fin 1,
        ricciCompAt (I := (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
          (modelWithCornersSelf Real Real)) basisSum
          (metricRicciAt (I := (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
            (modelWithCornersSelf Real Real)) roundThreeCylinderShrinkerMetric x) i j =
          ricciDiag3 (1 / 2 : Real) (1 / 2 : Real) 0 (eSum i) (eSum j) := by
      intro i j
      rcases i with i | i <;> rcases j with j | j
      · rw [roundThreeCylinderShrinkerMetric, ricciCompAt_apply,
          metricRicciAt_apply_eq_ricciTensor, Curvature.ricciTensor_prod,
          hbasisSum_inl, hbasisSum_inl]
        rw [hroundRicci, hM i j]
        fin_cases i <;> fin_cases j <;>
          norm_num [ricciDiag3, delta3, eSum, finSumFinEquiv] <;> decide
      · rw [roundThreeCylinderShrinkerMetric, ricciCompAt_apply,
          metricRicciAt_apply_eq_ricciTensor, Curvature.ricciTensor_prod,
          hbasisSum_inl, hbasisSum_inr]
        fin_cases i <;> fin_cases j <;>
          norm_num [ricciDiag3, delta3, eSum, finSumFinEquiv] <;> decide
      · rw [roundThreeCylinderShrinkerMetric, ricciCompAt_apply,
          metricRicciAt_apply_eq_ricciTensor, Curvature.ricciTensor_prod,
          hbasisSum_inr, hbasisSum_inl]
        fin_cases i; fin_cases j <;>
          norm_num [ricciDiag3, delta3, eSum, finSumFinEquiv] <;> decide
      · rw [roundThreeCylinderShrinkerMetric, ricciCompAt_apply,
          metricRicciAt_apply_eq_ricciTensor, Curvature.ricciTensor_prod,
          hbasisSum_inr, hbasisSum_inr]
        rw [euclideanMetric_ricciTensor]
        fin_cases i; fin_cases j;
          simp [ricciDiag3, eSum, finSumFinEquiv, Fin.ext_iff]
    simpa [basis, roundThreeCylinderProductBasis, Module.Basis.reindex_apply, delta3] using
      hRicciSum (eSum.symm i) (eSum.symm j)

set_option backward.isDefEq.respectTransparency false in
theorem roundThreeCylinderShrinkerMetric_curvatureOperatorRankAt
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    metricCurvatureOperatorRankAt
      (I := (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real))
      roundThreeCylinderShrinkerMetric x (by
        change Module.finrank Real (EuclideanSpace Real (Fin 2) × Real) = 3
        rw [Module.finrank_prod]
        simp) = 1 := by
  have hdimM : Module.finrank Real (TangentSpace
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) x.1) = 2 := by
    change Module.finrank Real (EuclideanSpace Real (Fin 2)) = 2
    simp
  have hdimN : Module.finrank Real (TangentSpace
      (modelWithCornersSelf Real Real) x.2) = 1 := by
    change Module.finrank Real Real = 1
    simp
  obtain ⟨bM, hbM⟩ := Curvature.exists_gOrthonormalBasis
    (I := modelWithCornersSelf Real (EuclideanSpace Real (Fin 2)))
      roundTwoSphereShrinkerMetric x.1
  obtain ⟨bN, hbN⟩ := Curvature.exists_gOrthonormalBasis
    (I := modelWithCornersSelf Real Real) (euclideanMetric (E := Real)) x.2
  let eM : Fin (Module.finrank Real
      (TangentSpace (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) x.1)) ≃ Fin 2 :=
    finCongr hdimM
  let eN : Fin (Module.finrank Real
      (TangentSpace (modelWithCornersSelf Real Real) x.2)) ≃ Fin 1 :=
    finCongr hdimN
  let basisM := bM.reindex eM
  let basisN := bN.reindex eN
  have hM : ∀ i j : Fin 2,
      roundTwoSphereShrinkerMetric.inner x.1 (basisM i) (basisM j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    simpa [basisM, eM] using hbM (eM.symm i) (eM.symm j)
  have hN : ∀ i j : Fin 1,
      (euclideanMetric (E := Real)).inner x.2 (basisN i) (basisN j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    simpa [basisN, eN] using hbN (eN.symm i) (eN.symm j)
  let basis := roundThreeCylinderProductBasis x basisM basisN
  have horth : OrthonormalBasisAt (I :=
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) roundThreeCylinderShrinkerMetric x basis := by
    simpa [basis] using
      roundThreeCylinder_product_basis_orthonormal x basisM basisN hM hN
  have hdim : Module.finrank Real (TangentSpace
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) x) = 3 := by
    change Module.finrank Real (EuclideanSpace Real (Fin 2) × Real) = 3
    rw [Module.finrank_prod]
    simp
  rw [metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (I := (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
      (modelWithCornersSelf Real Real)) roundThreeCylinderShrinkerMetric x hdim basis horth]
  have hdiag := roundThreeCylinder_product_basis_ricciDiag x basisM basisN hM
  rw [metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
    (I := (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
      (modelWithCornersSelf Real Real)) roundThreeCylinderShrinkerMetric x basis horth
      (1 / 2 : Real) (1 / 2 : Real) 0 hdiag]
  simp [curvatureOperatorDiagonal3, sec12Ric3, sec13Ric3, sec23Ric3,
    Matrix.rank_diagonal]

end DifferentialGeometry.Geometry
