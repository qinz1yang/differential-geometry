import DifferentialGeometry.Geometry.Metric.RicciSoliton.RankReduction
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveModelCoverRankThree
import DifferentialGeometry.Geometry.Operator.HessianExtrema

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator
open Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem q_eq_half_of_rank_one
    {g : SmoothRiemannianMetric I M}
    (hscalar : ∀ y : M, 0 < metricScalarAt (I := I) g y)
    (x : M) (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hrank : metricCurvatureOperatorRankAt (I := I) g x hdim = 1) :
    ricciNormSqScalarRatio (I := I) g hscalar x = (1 / 2 : Real) := by
  have h := two_mul_normSq0S_metricRicciAt_eq_metricScalarAt_sq_of_metricCurvatureOperatorRankAt_eq_one
    (I := I) (M := M) g x hdim hrank
  change normSq0S (I := I) g x 2
      (metricRicciAt (I := I) (M := M) g x) *
        metricScalarAt (I := I) g x ^ (-2 : Real) = (1 / 2 : Real)
  have hR : metricScalarAt (I := I) g x ≠ 0 := (hscalar x).ne'
  have hnorm : normSq0S (I := I) g x 2
      (metricRicciAt (I := I) (M := M) g x) =
        metricScalarAt (I := I) g x ^ 2 / 2 := by linarith
  rw [hnorm]
  rw [show metricScalarAt (I := I) g x ^ (-2 : Real) =
      (metricScalarAt (I := I) g x ^ 2)⁻¹ by
    rw [Real.rpow_neg (hscalar x).le]
    congr 1
    exact Real.rpow_natCast _ 2]
  field_simp

omit [SigmaCompactSpace M] in
private theorem q_eq_third_of_rank_three
    {g : SmoothRiemannianMetric I M}
    (hscalar : ∀ y : M, 0 < metricScalarAt (I := I) g y)
    (hdefect : ∀ y : M, ricciReactionDefectAt (I := I) g y = 0)
    (hcone : ∀ y : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M) (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hrank : metricCurvatureOperatorRankAt (I := I) g x hdim = 3) :
    ricciNormSqScalarRatio (I := I) g hscalar x = (1 / 3 : Real) := by
  obtain ⟨basis, lambda, mu, nu, horth, _hdiag⟩ :=
    exists_orthonormal_curvature_eigenframe (I := I) (M := M) g x hdim
  have hsec : ∀ v w : TangentSpace I x,
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v := by
    intro v w hvw
    exact metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative
      (I := I) (M := M) g x hdim hrank (hcone x) v w hvw
  have hEin := metricRicciAt_eq_scalar_div_three_of_ricciReactionDefectAt_eq_zero_of_sectional_pos
    (I := I) (M := M) g x hdim (hdefect x) hsec
  have hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x)
      ((metricScalarAt (I := I) (M := M) g x) / 3)
      ((metricScalarAt (I := I) (M := M) g x) / 3)
      ((metricScalarAt (I := I) (M := M) g x) / 3) basis := by
    constructor
    · unfold ricciEigenScalar3
      ring
    · intro i j
      rw [ricciCompAt_apply, hEin, horth]
      fin_cases i <;> fin_cases j <;> simp [ricciDiag3, delta3]
  change normSq0S (I := I) g x 2
      (metricRicciAt (I := I) (M := M) g x) *
        metricScalarAt (I := I) g x ^ (-2 : Real) = (1 / 3 : Real)
  rw [normSq0S_metricRicciAt_eq_ricciEigenNormSq3_of_ricciDiag
    (I := I) (M := M) g x basis horth
      ((metricScalarAt (I := I) (M := M) g x) / 3)
      ((metricScalarAt (I := I) (M := M) g x) / 3)
      ((metricScalarAt (I := I) (M := M) g x) / 3) hdiag,
    hdiag.1]
  simp only [ricciEigenNormSq3, ricciEigenScalar3]
  ring_nf
  have hR : metricScalarAt (I := I) g x ≠ 0 := (hscalar x).ne'
  rw [show metricScalarAt (I := I) g x ^ (-2 : Real) =
      (metricScalarAt (I := I) g x ^ 2)⁻¹ by
    rw [Real.rpow_neg (hscalar x).le]
    congr 1
    exact Real.rpow_natCast _ 2]
  field_simp

theorem normalizedGradientRicciSoliton_metricCurvatureOperatorRankAt_eq_three_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f 1)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 3 := by
  let _ : NeZero (Module.finrank Real E) := ⟨by rw [hdim]; norm_num⟩
  have hscalar : ∀ y : M, 0 < metricScalarAt (I := I) g y := by
    intro y
    exact normalizedGradientRicciSoliton_scalar_pos_of_not_isGaussian
      (I := I) h hnot y
  have hdefect : ∀ x : M, ricciReactionDefectAt (I := I) g x = 0 :=
    gradientRicciSoliton_ricciReactionDefectAt_eq_zero_of_compact_of_finrank_eq_three
      (I := I) (M := M) h.2.1 hscalar hdim
  have hrank : ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 1 ∨
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 3 :=
    normalizedGradientRicciSoliton_metricCurvatureOperatorRankAt_eq_one_or_three_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
      (I := I) (M := M) h hdim hnot hcone
  cases isEmpty_or_nonempty M with
  | inl hempty =>
      intro x
      exact isEmptyElim (hempty.false x)
  | inr hne =>
      let _ : Nonempty M := hne
      obtain ⟨xmax, _, hmax⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMaxOn
        univ_nonempty (f.contMDiff.continuous.continuousOn)
      have hQconst : ∀ x y : M,
          ricciNormSqScalarRatio (I := I) g hscalar x =
            ricciNormSqScalarRatio (I := I) g hscalar y := by
        let Q := ricciNormSqScalarRatio (I := I) g hscalar
        have hmaps : MapsTo Q univ ({(1 / 2 : Real), (1 / 3 : Real)} : Set Real) := by
          intro y hy
          rcases hrank y with hyone | hythree
          · left
            exact q_eq_half_of_rank_one (I := I) (M := M) hscalar y _ hyone
          · right
            exact q_eq_third_of_rank_three (I := I) (M := M)
              hscalar hdefect hcone y _ hythree
        intro x y
        exact isPreconnected_univ.constant_of_mapsTo
          (Set.toFinite ({(1 / 2 : Real), (1 / 3 : Real)} : Set Real)).isDiscrete
          Q.contMDiff.continuous.continuousOn hmaps trivial trivial
      intro x
      rcases hrank x with hxone | hxthree
      · have hQx := q_eq_half_of_rank_one (I := I) (M := M) hscalar x _ hxone
        have hQmax := hQconst x xmax
        have hQmaxhalf : ricciNormSqScalarRatio (I := I) g hscalar xmax = (1 / 2 : Real) := by
          rw [← hQmax, hQx]
        rcases hrank xmax with hmaxone | hmaxthree
        · obtain ⟨v, hv, hric⟩ := exists_metricRicciAt_nullVector_of_metricCurvatureOperatorRankAt_eq_one
            (I := I) (M := M) g xmax _ hmaxone
          have hmaxlocal : IsLocalMax (f : M → Real) xmax := hmax.isLocalMax (by simp)
          have hhess := hessFun_apply_self_nonpos_at_spatial_max (I := I) (M := M) g
            hmaxlocal f.contMDiff v
          have hsol := h.2.1 xmax v v
          rw [metricRicciAt_apply_eq_ricciTensor (I := I) g xmax v v] at hric
          rw [hric, zero_add] at hsol
          have hpos := g.pos xmax v hv
          nlinarith
        · have hQmaxthird := q_eq_third_of_rank_three (I := I) (M := M)
            hscalar hdefect hcone xmax _ hmaxthree
          linarith [hQmaxhalf, hQmaxthird]
      · exact hxthree

theorem exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f 1)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f cover := by
  have hrank := normalizedGradientRicciSoliton_metricCurvatureOperatorRankAt_eq_three_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
    (I := I) (M := M) h hdim hnot hcone
  exact exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three
    (I := I) (M := M) h hdim hcone hrank

theorem exists_gaussian_or_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    (∃ cover : E → M,
      solitonModelCovering (euclideanMetric (E := E))
        (gaussianPotential (E := E)) g f cover) ∨
    (∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f cover) := by
  classical
  by_cases hGaussian : isGaussianGradientRicciSoliton (E := E) g f 1
  · left
    exact exists_solitonModelCovering_of_isGaussianGradientRicciSoliton
      (I := I) h hGaussian
  · right
    exact exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
      (I := I) (M := M) h hdim hGaussian hcone

theorem isSphericalSpaceForm_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f 1)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    isSphericalSpaceForm (I := I) (M := M) := by
  have hrank := normalizedGradientRicciSoliton_metricCurvatureOperatorRankAt_eq_three_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
    (I := I) (M := M) h hdim hnot hcone
  exact isSphericalSpaceForm_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three
    (I := I) (M := M) h hdim hcone hrank

end DifferentialGeometry.Geometry
