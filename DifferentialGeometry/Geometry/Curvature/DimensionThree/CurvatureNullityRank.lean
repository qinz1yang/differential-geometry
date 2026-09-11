import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciNullity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] [T2Space M] in
private theorem exists_orthonormalBasisAt_last_eq_of_unit
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ E = 3) (e : TangentSpace I x)
    (he : g.inner x e e = 1) :
    ∃ b : Module.Basis (Fin 3) ℝ (TangentSpace I x),
      OrthonormalBasisAt g x b ∧ b 2 = e := by
  let D := (Tensor0SBundle.tangentMetricData (I := I) g x).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have he' : inner ℝ e e = 1 := by
    rw [D.toCore_inner]
    exact he
  have ho : Orthonormal ℝ (({2} : Set (Fin 3)).domRestrict (fun _ => e)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (i.property.trans j.property.symm)
    subst j
    simpa only [Set.domRestrict_apply, ite_true] using he'
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (TangentSpace I x) = Fintype.card (Fin 3) from hdim)
  refine ⟨b.toBasis, ?_, hb 2 rfl⟩
  intro i j
  change D.inner (b i) (b j) = _
  rw [← D.toCore_inner, b.inner_eq_ite]
  rfl

theorem curvatureOperatorImageAt_finrank_eq_of_unit_curvature_nullity
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ E = 3) (e : TangentSpace I x)
    (he : e ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩)
    (hunit : g.inner x e e = 1) :
    Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) =
      if metricScalarAt g x = 0 then 0 else 1 := by
  obtain ⟨b, horth, hb⟩ := exists_orthonormalBasisAt_last_eq_of_unit g x hdim e hunit
  rw [curvatureOperatorImageAt_finrank_eq_traceNormalized_matrix_rank g x b horth]
  change (traceNormalizedMetricCurvatureOperatorMatrixAt g x b).rank = _
  rw [traceNormalizedMetricCurvatureOperatorMatrixAt_eq_diagonal_of_curvature_nullity
    g x b horth (hb.symm ▸ he)]
  classical
  by_cases hs : metricScalarAt g x = 0
  · have hz : Matrix.diagonal (![metricScalarAt g x, 0, 0] : Fin 3 → ℝ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hs, Matrix.diagonal]
    rw [hz, Matrix.rank_zero, if_pos hs]
  · rw [Matrix.rank_diagonal, if_neg hs]
    let _ : Unique {i : Fin 3 // ![metricScalarAt g x, 0, 0] i ≠ 0} :=
      ⟨⟨⟨0, by simpa using hs⟩⟩, by
        rintro ⟨i, hi⟩
        apply Subtype.ext
        fin_cases i
        · rfl
        · exact (hi (show (![metricScalarAt g x, 0, 0] : Fin 3 → ℝ) 1 = 0 from rfl)).elim
        · exact (hi (show (![metricScalarAt g x, 0, 0] : Fin 3 → ℝ) 2 = 0 from rfl)).elim⟩
    exact Fintype.card_unique

end DifferentialGeometry.Geometry.Curvature.DimensionThree
