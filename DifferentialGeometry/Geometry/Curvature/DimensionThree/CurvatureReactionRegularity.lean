import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

open scoped ContDiff
namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

theorem curvatureOperatorReactionEndomorphism3_contDiff :
    ContDiff ℝ ∞ (fun A : W →L[ℝ] W =>
      LinearMap.toContinuousLinearMap (curvatureOperatorReactionEndomorphism3 A.toLinearMap)) := by
  let tr : (W →L[ℝ] W) →L[ℝ] ℝ :=
    ((LinearMap.trace ℝ W).comp LinearMap.toContinuousLinearMap.symm.toLinearMap).toContinuousLinearMap
  have htrace : ContDiff ℝ ∞ (fun A : W →L[ℝ] W => LinearMap.trace ℝ W A.toLinearMap) :=
    tr.contDiff
  have hsq : ContDiff ℝ ∞ (fun A : W →L[ℝ] W => A.comp A) :=
    contDiff_id.clm_comp contDiff_id
  have htrsq : ContDiff ℝ ∞ (fun A : W →L[ℝ] W =>
      LinearMap.trace ℝ W (A.toLinearMap.comp A.toLinearMap)) :=
    htrace.comp hsq
  have h := ((hsq.const_smul (2 : ℝ)).sub (htrace.smul contDiff_id)).add
    ((((htrace.pow 2).sub htrsq).div_const (2 : ℝ)).smul
      (contDiff_const : ContDiff ℝ ∞ (fun _ : W →L[ℝ] W => ContinuousLinearMap.id ℝ W)))
  convert h using 1
  funext A
  ext x
  rfl

theorem curvatureOperatorReactionEndomorphism3_exists_lipschitzOn_closedBall
    (R : ℝ) :
    ∃ L : NNReal, LipschitzOnWith L
      (fun A : W →L[ℝ] W =>
        LinearMap.toContinuousLinearMap (curvatureOperatorReactionEndomorphism3 A.toLinearMap))
      (Metric.closedBall 0 R) :=
  curvatureOperatorReactionEndomorphism3_contDiff.contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)

variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']
  [FiniteDimensional ℝ W']

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ W'] in
private theorem norm_arrowCongr
    (e : W ≃ₗᵢ[ℝ] W') (A : W →L[ℝ] W) :
    ‖e.toContinuousLinearEquiv.arrowCongr e.toContinuousLinearEquiv A‖ = ‖A‖ := by
  change ‖(e : W →L[ℝ] W').comp (A.comp (e.symm : W' →L[ℝ] W))‖ = ‖A‖
  simp only [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem curvatureOperatorReactionEndomorphism3_lipschitzOn_closedBall_of_linearIsometryEquiv
    (e : W ≃ₗᵢ[ℝ] W') {R : ℝ} {L : NNReal}
    (hL : LipschitzOnWith L
      (fun A : W' →L[ℝ] W' =>
        LinearMap.toContinuousLinearMap (curvatureOperatorReactionEndomorphism3 A.toLinearMap))
      (Metric.closedBall 0 R)) :
    LipschitzOnWith L
      (fun A : W →L[ℝ] W =>
        LinearMap.toContinuousLinearMap (curvatureOperatorReactionEndomorphism3 A.toLinearMap))
      (Metric.closedBall 0 R) := by
  let C := e.toContinuousLinearEquiv.arrowCongr e.toContinuousLinearEquiv
  let Q := fun A : W →L[ℝ] W =>
    LinearMap.toContinuousLinearMap (curvatureOperatorReactionEndomorphism3 A.toLinearMap)
  let Q' := fun A : W' →L[ℝ] W' =>
    LinearMap.toContinuousLinearMap (curvatureOperatorReactionEndomorphism3 A.toLinearMap)
  have hQ (A : W →L[ℝ] W) : C (Q A) = Q' (C A) := by
    apply ContinuousLinearMap.coe_injective
    change e.toLinearEquiv.conj (curvatureOperatorReactionEndomorphism3 A.toLinearMap) =
      curvatureOperatorReactionEndomorphism3 (e.toLinearEquiv.conj A.toLinearMap)
    exact (curvatureOperatorReactionEndomorphism3_conj e.toLinearEquiv A.toLinearMap).symm
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro A hA B hB
  have hAC : C A ∈ Metric.closedBall 0 R := by
    rw [mem_closedBall_zero_iff, norm_arrowCongr e]
    exact mem_closedBall_zero_iff.mp hA
  have hBC : C B ∈ Metric.closedBall 0 R := by
    rw [mem_closedBall_zero_iff, norm_arrowCongr e]
    exact mem_closedBall_zero_iff.mp hB
  have h := hL.dist_le_mul _ hAC _ hBC
  rw [dist_eq_norm, dist_eq_norm] at h ⊢
  calc
    ‖Q A - Q B‖ = ‖C (Q A - Q B)‖ := (norm_arrowCongr e _).symm
    _ = ‖Q' (C A) - Q' (C B)‖ := by rw [map_sub, hQ, hQ]
    _ ≤ (L : ℝ) * ‖C A - C B‖ := h
    _ = (L : ℝ) * ‖A - B‖ := by rw [← map_sub, norm_arrowCongr e]

theorem curvatureOperatorReactionEndomorphism3_exists_uniform_lipschitzOn_closedBall
    {ι : Type*} (V : ι → Type*) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℝ (V i)] [∀ i, FiniteDimensional ℝ (V i)]
    (n : ℕ) (hdim : ∀ i, Module.finrank ℝ (V i) = n) (R : ℝ) :
    ∃ L : NNReal, ∀ i, LipschitzOnWith L
      (fun A : V i →L[ℝ] V i =>
        LinearMap.toContinuousLinearMap (curvatureOperatorReactionEndomorphism3 A.toLinearMap))
      (Metric.closedBall 0 R) := by
  obtain ⟨L, hL⟩ := curvatureOperatorReactionEndomorphism3_exists_lipschitzOn_closedBall
    (W := EuclideanSpace ℝ (Fin n)) R
  refine ⟨L, fun i => ?_⟩
  let basis : OrthonormalBasis (Fin n) ℝ (V i) :=
    (stdOrthonormalBasis ℝ (V i)).reindex (finCongr (hdim i))
  exact curvatureOperatorReactionEndomorphism3_lipschitzOn_closedBall_of_linearIsometryEquiv
    basis.repr hL

end DifferentialGeometry.Geometry.Curvature.DimensionThree

end
