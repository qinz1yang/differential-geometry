import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Region
import Mathlib.Analysis.Matrix.Hermitian

noncomputable section
open scoped RealInnerProductSpace
open DifferentialGeometry.Analysis.Convex

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

private theorem minimumRayleighQuotient3_toMatrix
    (b : OrthonormalBasis (Fin 3) ℝ W) (A : W →ₗ[ℝ] W) :
    minimumRayleighQuotient3 (LinearMap.toMatrix b.toBasis b.toBasis A) =
      sInf ((fun v : W => ⟪A v, v⟫) '' Metric.sphere 0 1) := by
  unfold minimumRayleighQuotient3
  congr 1
  have heval : ∀ v : W,
      (∑ i : Fin 3, b.repr v i * (∑ j : Fin 3,
        LinearMap.toMatrix b.toBasis b.toBasis A i j * b.repr v j)) = ⟪A v, v⟫ := by
    intro v
    have h : (LinearMap.toMatrix b.toBasis b.toBasis A).toEuclideanLin (b.repr v) =
        b.repr (A v) := by
      apply WithLp.ofLp_injective
      exact LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis A v
    rw [← b.repr.inner_map_map (A v) v, ← h]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.toLpLin_apply,
      Matrix.mulVec, mul_comm]
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨b.repr.symm v, ?_, ?_⟩
    · simpa only [Metric.mem_sphere, dist_zero_right, b.repr.symm.norm_map] using hv
    · change ⟪A (b.repr.symm v), b.repr.symm v⟫ =
        ∑ i : Fin 3, v i * ∑ j : Fin 3,
          LinearMap.toMatrix b.toBasis b.toBasis A i j * v j
      simpa only [LinearIsometryEquiv.apply_symm_apply] using (heval (b.repr.symm v)).symm
  · rintro ⟨v, hv, rfl⟩
    refine ⟨b.repr v, ?_, heval v⟩
    simpa only [Metric.mem_sphere, dist_zero_right, b.repr.norm_map] using hv

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable [FiniteDimensional ℝ W]

def hamiltonIveyRegion (K : ℝ) : Set (selfAdjoint (W →L[ℝ] W)) :=
  {A | let ν := sInf ((fun v : W => ⟪(A : W →L[ℝ] W) v, v⟫) '' Metric.sphere 0 1);
    -3 * K ≤ LinearMap.trace ℝ W (A : W →L[ℝ] W).toLinearMap ∧
      (ν ≤ -K → (-ν) * (Real.log ((-ν) / K) - 3) ≤
        LinearMap.trace ℝ W (A : W →L[ℝ] W).toLinearMap)}

theorem mem_hamiltonIveyRegion_iff_toMatrix
    (b : OrthonormalBasis (Fin 3) ℝ W) {K : ℝ} (hK : 0 < K)
    (A : selfAdjoint (W →L[ℝ] W)) :
    A ∈ hamiltonIveyRegion K ↔
      LinearMap.toMatrix b.toBasis b.toBasis (A : W →L[ℝ] W).toLinearMap ∈
        hamiltonIveyConvexMatrixRegion K 0 := by
  rw [mem_hamiltonIveyConvexMatrixRegion_initial_iff hK,
    minimumRayleighQuotient3_toMatrix,
    ← LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  have hA : (LinearMap.toMatrix b.toBasis b.toBasis
      (A : W →L[ℝ] W).toLinearMap).IsHermitian :=
    (LinearMap.isHermitian_toMatrix_iff b).mpr
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp A.property)
  exact (and_iff_right hA).symm

theorem mem_hamiltonIveyRegion_iff_eigenvalues
    (hdim : Module.finrank ℝ W = 3) (A : selfAdjoint (W →L[ℝ] W)) (K : ℝ) :
    let hA := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp A.property
    A ∈ hamiltonIveyRegion K ↔
      -3 * K ≤ LinearMap.trace ℝ W (A : W →L[ℝ] W).toLinearMap ∧
        (hA.eigenvalues hdim 2 ≤ -K → (-hA.eigenvalues hdim 2) *
          (Real.log ((-hA.eigenvalues hdim 2) / K) - 3) ≤
            LinearMap.trace ℝ W (A : W →L[ℝ] W).toLinearMap) := by
  let hA := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp A.property
  have heq : sInf ((fun v : W => ⟪(A : W →L[ℝ] W) v, v⟫) '' Metric.sphere 0 1) =
      hA.eigenvalues hdim 2 := by
    have hmatrix := minimumRayleighQuotient3_toMatrix (hA.eigenvectorBasis hdim)
      (A : W →L[ℝ] W).toLinearMap
    change minimumRayleighQuotient3 _ =
      sInf ((fun v : W => ⟪(A : W →L[ℝ] W) v, v⟫) '' Metric.sphere 0 1) at hmatrix
    rw [← hmatrix, hA.toMatrix_eigenvectorBasis hdim]
    have hv : hA.eigenvalues hdim =
        ![hA.eigenvalues hdim 0, hA.eigenvalues hdim 1, hA.eigenvalues hdim 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact minimumRayleighQuotient3_diagonal_eq_last _ _ _
      (hA.eigenvalues_antitone hdim (by decide : (0 : Fin 3) ≤ 1))
      (hA.eigenvalues_antitone hdim (by decide : (1 : Fin 3) ≤ 2))
  change (_ ∧ _) ↔ _
  rw [heq]

private def selfAdjointToMatrix (b : OrthonormalBasis (Fin 3) ℝ W) :
    selfAdjoint (W →L[ℝ] W) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ where
  toFun A := LinearMap.toMatrix b.toBasis b.toBasis (A : W →L[ℝ] W).toLinearMap
  map_add' A B := by change LinearMap.toMatrix _ _ (_ + _) = _; simp
  map_smul' c A := by change LinearMap.toMatrix _ _ (c • _) = _; simp

private theorem hamiltonIveyRegion_eq_preimage
    (b : OrthonormalBasis (Fin 3) ℝ W) {K : ℝ} (hK : 0 < K) :
    hamiltonIveyRegion (W := W) K =
      (selfAdjointToMatrix b) ⁻¹' hamiltonIveyConvexMatrixRegion K 0 := by
  ext A
  exact mem_hamiltonIveyRegion_iff_toMatrix b hK A

theorem convex_hamiltonIveyRegion (hdim : Module.finrank ℝ W = 3)
    {K : ℝ} (hK : 0 < K) : Convex ℝ (hamiltonIveyRegion (W := W) K) := by
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  rw [hamiltonIveyRegion_eq_preimage b hK]
  exact (convex_hamiltonIveyConvexMatrixRegion hK le_rfl).linear_preimage
    (selfAdjointToMatrix b)

theorem isClosed_hamiltonIveyRegion {K : ℝ} (hK : 0 < K) :
    IsClosed (hamiltonIveyRegion (W := W) K) := by
  let ν := fun A : selfAdjoint (W →L[ℝ] W) =>
    sInf ((fun v : W => ⟪(A : W →L[ℝ] W) v, v⟫) '' Metric.sphere 0 1)
  let S := fun A : selfAdjoint (W →L[ℝ] W) =>
    LinearMap.trace ℝ W (A : W →L[ℝ] W).toLinearMap
  have hν : Continuous ν := by
    apply IsCompact.continuous_sInf (isCompact_sphere (0 : W) 1)
    change Continuous fun p : selfAdjoint (W →L[ℝ] W) × W =>
      ⟪(p.1 : W →L[ℝ] W) p.2, p.2⟫
    exact ((continuous_subtype_val.comp continuous_fst).clm_apply continuous_snd).inner
      continuous_snd
  have hS : Continuous S := by
    let b := stdOrthonormalBasis ℝ W
    have heq : S = fun A : selfAdjoint (W →L[ℝ] W) =>
        ∑ i, ⟪b i, (A : W →L[ℝ] W) (b i)⟫ := by
      funext A
      dsimp only [S]
      rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
      simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
        OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
    rw [heq]
    exact continuous_finsetSum _ (fun _ _ =>
      continuous_const.inner (continuous_subtype_val.clm_apply continuous_const))
  have heq : hamiltonIveyRegion (W := W) K =
      {A | -3 * K ≤ S A} ∩
        ({A | -K ≤ ν A} ∪ {A | hamiltonIveyBarrier K 0 (-ν A) ≤ S A}) := by
    ext A
    change (-3 * K ≤ S A ∧ (ν A ≤ -K →
      (-ν A) * (Real.log ((-ν A) / K) - 3) ≤ S A)) ↔
        (-3 * K ≤ S A ∧ (-K ≤ ν A ∨ hamiltonIveyBarrier K 0 (-ν A) ≤ S A))
    constructor
    · rintro ⟨htrace, hlog⟩
      refine ⟨htrace, ?_⟩
      by_cases h : -K ≤ ν A
      · exact Or.inl h
      · exact Or.inr (by
          simpa only [hamiltonIveyBarrier, mul_zero, add_zero, Real.log_one] using
            hlog (le_of_lt (lt_of_not_ge h)))
    · rintro ⟨htrace, h | h⟩
      · refine ⟨htrace, fun h' => ?_⟩
        have he : ν A = -K := le_antisymm h' h
        change (-ν A) * (Real.log ((-ν A) / K) - 3) ≤ S A
        simpa only [he, neg_neg, div_self hK.ne', Real.log_one, zero_sub,
          mul_neg, mul_comm K] using htrace
      · refine ⟨htrace, fun _ => ?_⟩
        simpa only [hamiltonIveyBarrier, mul_zero, add_zero, Real.log_one] using h
  rw [heq]
  exact (isClosed_le continuous_const hS).inter
    ((isClosed_le continuous_const hν).union
      (isClosed_le ((continuous_hamiltonIveyBarrier hK).comp hν.neg) hS))

theorem zero_mem_hamiltonIveyRegion {K : ℝ} (hK : 0 ≤ K) :
    (0 : selfAdjoint (W →L[ℝ] W)) ∈ hamiltonIveyRegion K := by
  have hzero : sInf ((fun _ : W => (0 : ℝ)) '' Metric.sphere 0 1) = 0 := by
    by_cases h : (Metric.sphere (0 : W) 1).Nonempty
    · rw [h.image_const, csInf_singleton]
    · rw [Set.not_nonempty_iff_eq_empty.mp h, Set.image_empty, Real.sInf_empty]
  simp only [hamiltonIveyRegion, Set.mem_ofPred_eq, ZeroMemClass.coe_zero,
    zero_apply, inner_zero_left, hzero,
    ContinuousLinearMap.toLinearMap_zero, map_zero, neg_zero, zero_mul]
  exact ⟨by linarith, fun _ => le_rfl⟩

theorem nonempty_hamiltonIveyRegion {K : ℝ} (hK : 0 ≤ K) :
    (hamiltonIveyRegion (W := W) K).Nonempty :=
  ⟨0, zero_mem_hamiltonIveyRegion hK⟩

variable {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W']
  [FiniteDimensional ℝ W']

theorem mem_hamiltonIveyRegion_conj_iff
    (e : W ≃ₗᵢ[ℝ] W') (A : selfAdjoint (W →L[ℝ] W)) (K : ℝ) :
    (⟨e.conjStarAlgEquiv A, A.property.map e.conjStarAlgEquiv⟩ :
      selfAdjoint (W' →L[ℝ] W')) ∈ hamiltonIveyRegion K ↔ A ∈ hamiltonIveyRegion K := by
  have hinner : ∀ v : W,
      ⟪e.conjStarAlgEquiv (A : W →L[ℝ] W) (e v), e v⟫ = ⟪(A : W →L[ℝ] W) v, v⟫ := by
    intro v
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]
  have himage :
      (fun v : W' => ⟪e.conjStarAlgEquiv (A : W →L[ℝ] W) v, v⟫) '' Metric.sphere 0 1 =
        (fun v : W => ⟪(A : W →L[ℝ] W) v, v⟫) '' Metric.sphere 0 1 := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨e.symm v, ?_, ?_⟩
      · simpa only [Metric.mem_sphere, dist_zero_right, e.symm.norm_map] using hv
      · simpa only [e.apply_symm_apply] using (hinner (e.symm v)).symm
    · rintro ⟨v, hv, rfl⟩
      exact ⟨e v, by simpa only [Metric.mem_sphere, dist_zero_right, e.norm_map] using hv,
        hinner v⟩
  have htrace : LinearMap.trace ℝ W'
      (e.conjStarAlgEquiv (A : W →L[ℝ] W)).toLinearMap =
        LinearMap.trace ℝ W (A : W →L[ℝ] W).toLinearMap := by
    exact LinearMap.trace_conj' (A : W →L[ℝ] W).toLinearMap e.toLinearEquiv
  change (-3 * K ≤ LinearMap.trace ℝ W'
      (e.conjStarAlgEquiv (A : W →L[ℝ] W)).toLinearMap ∧ _) ↔ _
  simp only [htrace, himage]
  rfl

end DifferentialGeometry.Geometry.Curvature.DimensionThree
