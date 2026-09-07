import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace MetricExtension

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private def gramMatrixOnEuclid
    (g : SmoothRiemannianMetric I M) (alpha : M) (y : EuclN) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => gramOnEuclid (I := I) g alpha i j y

private def weightedMatrix
    (g : SmoothRiemannianMetric I M) (alpha : M) (y : EuclN) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => weightedInvGramOnEuclid (I := I) g alpha i j y

private def dualMatrix
    (g : SmoothRiemannianMetric I M) (alpha : M) (y : EuclN) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (densityOnEuclid (I := I) g alpha y)⁻¹ • gramMatrixOnEuclid (I := I) g alpha y

omit [NeZero (Module.finrank ℝ E)] in
private lemma gramMatrixOnEuclid_posDef
    (g : SmoothRiemannianMetric I M) (alpha : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) alpha) :
    (gramMatrixOnEuclid (I := I) g alpha y).PosDef := by
  set x : M := (extChartAt I alpha).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I alpha).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_src : x ∈ (extChartAt I alpha).source :=
    (extChartAt I alpha).map_target h_tgt
  have h_base : x ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    change x ∈ (chartAt H alpha).source
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_src
  have hG :
      (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
        (I := I) g alpha x).PosDef :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_posDef
      (I := I) g alpha h_base
  have h_eq : gramMatrixOnEuclid (I := I) g alpha y =
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
        (I := I) g alpha x := by
    ext i j
    rfl
  rwa [h_eq]

omit [NeZero (Module.finrank ℝ E)] in
private lemma dualMatrix_posDef
    (g : SmoothRiemannianMetric I M) (alpha : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) alpha) :
    (dualMatrix (I := I) g alpha y).PosDef := by
  exact (gramMatrixOnEuclid_posDef (I := I) g alpha hy).smul
    (inv_pos.mpr (densityOnEuclid_pos (I := I) g alpha hy))

private def matrixQuad
    (B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (xi : EuclN) : ℝ :=
  ⟪xi, DeGiorgi.matMulE B xi⟫_ℝ

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma matrixQuad_eq_sum
    (B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (xi : EuclN) :
    matrixQuad (E := E) B xi =
      ∑ i, ∑ j, B i j * xi.ofLp i * xi.ofLp j := by
  classical
  unfold matrixQuad
  have h_inner : ⟪xi, DeGiorgi.matMulE B xi⟫_ℝ =
      B.mulVec xi.ofLp ⬝ᵥ xi.ofLp := by
    change (DeGiorgi.matMulE B xi).ofLp ⬝ᵥ star xi.ofLp = _
    rw [DeGiorgi.matMulE_ofLp]
    have hstar : star xi.ofLp = xi.ofLp := by
      funext i
      exact star_trivial _
    rw [hstar]
  rw [h_inner]
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma matrixQuad_pos
    {B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ}
    (hB : B.PosDef) {xi : EuclN} (hxi : xi ≠ 0) :
    0 < matrixQuad (E := E) B xi := by
  have h_form : matrixQuad (E := E) B xi = B.mulVec xi.ofLp ⬝ᵥ xi.ofLp := by
    unfold matrixQuad
    change (DeGiorgi.matMulE B xi).ofLp ⬝ᵥ star xi.ofLp = _
    rw [DeGiorgi.matMulE_ofLp]
    have hstar : star xi.ofLp = xi.ofLp := by
      funext i
      exact star_trivial _
    rw [hstar]
  rw [h_form]
  have hxi' : xi.ofLp ≠ 0 := by
    intro h
    apply hxi
    have heq : xi = WithLp.toLp 2 xi.ofLp := rfl
    rw [heq, h]
    simp
  have h := hB.dotProduct_mulVec_pos hxi'
  have hstar : star xi.ofLp = xi.ofLp := by
    funext i
    exact star_trivial _
  rw [hstar, dotProduct_comm] at h
  exact h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma matrixQuad_smul
    (c : ℝ)
    (B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (xi : EuclN) :
    matrixQuad (E := E) (c • B) xi = c * matrixQuad (E := E) B xi := by
  unfold matrixQuad
  have h_mul : DeGiorgi.matMulE (c • B) xi = c • DeGiorgi.matMulE B xi := by
    apply WithLp.ofLp_injective 2
    simp only [DeGiorgi.matMulE_ofLp]
    rw [Matrix.smul_mulVec]
    rfl
  rw [h_mul, inner_smul_right]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma matrixQuad_one (xi : EuclN) :
    matrixQuad (E := E)
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) xi =
      ‖xi‖ ^ 2 := by
  unfold matrixQuad
  have hmul : DeGiorgi.matMulE
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) xi = xi := by
    apply WithLp.ofLp_injective 2
    rw [DeGiorgi.matMulE_ofLp]
    exact Matrix.one_mulVec _
  rw [hmul, real_inner_self_eq_norm_sq]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_quad_lower
    {K : Set EuclN} (hK_compact : IsCompact K)
    (B : EuclN → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hB_cont : ∀ i j, ContinuousOn (fun y => B y i j) K)
    (hB_pos : ∀ y ∈ K, (B y).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K, ∀ xi : EuclN,
      c * ‖xi‖ ^ 2 ≤ matrixQuad (E := E) (B y) xi := by
  classical
  set S : Set EuclN := Metric.sphere (0 : EuclN) 1 with hS_def
  have hS_compact : IsCompact S := isCompact_sphere _ _
  have hKS_compact : IsCompact (K ×ˢ S) := hK_compact.prod hS_compact
  have h_cont : ContinuousOn (fun p : EuclN × EuclN =>
      matrixQuad (E := E) (B p.1) p.2) (K ×ˢ S) := by
    rw [show (fun p : EuclN × EuclN => matrixQuad (E := E) (B p.1) p.2) =
        (fun p => ∑ i, ∑ j, B p.1 i j * p.2.ofLp i * p.2.ofLp j) by
      funext p
      exact matrixQuad_eq_sum (E := E) (B p.1) p.2]
    refine continuousOn_finsetSum _ ?_
    intro i _
    refine continuousOn_finsetSum _ ?_
    intro j _
    have hfst : ContinuousOn (fun p : EuclN × EuclN => p.1) (K ×ˢ S) :=
      continuous_fst.continuousOn
    have hsnd : ContinuousOn (fun p : EuclN × EuclN => p.2) (K ×ˢ S) :=
      continuous_snd.continuousOn
    have ha : ContinuousOn (fun p : EuclN × EuclN => B p.1 i j) (K ×ˢ S) :=
      (hB_cont i j).comp hfst fun _ hp => hp.1
    have hxi : Continuous (fun xi : EuclN => xi.ofLp i) :=
      (EuclideanSpace.proj i).continuous
    have hxj : Continuous (fun xi : EuclN => xi.ofLp j) :=
      (EuclideanSpace.proj j).continuous
    exact (ha.mul (hxi.continuousOn.comp hsnd fun _ _ => Set.mem_univ _)).mul
      (hxj.continuousOn.comp hsnd fun _ _ => Set.mem_univ _)
  have h_pos : ∀ p ∈ K ×ˢ S,
      0 < matrixQuad (E := E) (B p.1) p.2 := by
    intro p hp
    have hpS : p.2 ∈ S := hp.2
    have hnorm : ‖p.2‖ = 1 := by
      rw [hS_def, Metric.mem_sphere, dist_zero_right] at hpS
      exact hpS
    have hne : p.2 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact one_ne_zero hnorm.symm
    exact matrixQuad_pos (E := E) (hB_pos p.1 hp.1) hne
  obtain ⟨c, hc, hc_le⟩ := hKS_compact.exists_forall_le' h_cont h_pos
  refine ⟨c, hc, ?_⟩
  intro y hy xi
  by_cases hxi : xi = 0
  · subst xi
    simp [matrixQuad]
  · have hnorm : 0 < ‖xi‖ := norm_pos_iff.mpr hxi
    set eta : EuclN := (1 / ‖xi‖) • xi with heta
    have heta_norm : ‖eta‖ = 1 := by
      rw [heta, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hnorm)]
      field_simp
    have heta_mem : eta ∈ S := by
      rw [hS_def, Metric.mem_sphere, dist_zero_right]
      exact heta_norm
    have hunit : c ≤ matrixQuad (E := E) (B y) eta :=
      hc_le (y, eta) ⟨hy, heta_mem⟩
    have hxi_eq : xi = ‖xi‖ • eta := by
      rw [heta, ← smul_assoc, smul_eq_mul]
      rw [show ‖xi‖ * (1 / ‖xi‖) = 1 by field_simp, one_smul]
    have hscale : matrixQuad (E := E) (B y) xi =
        ‖xi‖ ^ 2 * matrixQuad (E := E) (B y) eta := by
      conv_lhs => rw [hxi_eq]
      unfold matrixQuad
      have hmul : DeGiorgi.matMulE (B y) (‖xi‖ • eta) =
          ‖xi‖ • DeGiorgi.matMulE (B y) eta := by
        apply WithLp.ofLp_injective 2
        simp only [DeGiorgi.matMulE_ofLp]
        change (B y).mulVec (‖xi‖ • eta.ofLp) = ‖xi‖ • (B y).mulVec eta.ofLp
        rw [Matrix.mulVec_smul]
      rw [hmul, inner_smul_left, inner_smul_right]
      simp only [conj_trivial, sq]
      ring
    rw [hscale]
    calc
      c * ‖xi‖ ^ 2 = ‖xi‖ ^ 2 * c := by ring
      _ ≤ ‖xi‖ ^ 2 * matrixQuad (E := E) (B y) eta :=
        mul_le_mul_of_nonneg_left hunit (sq_nonneg ‖xi‖)

omit [NeZero (Module.finrank ℝ E)] in
private lemma dualMatrix_continuousOn
    (g : SmoothRiemannianMetric I M) (alpha : M)
    {K : Set EuclN} (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) alpha) :
    ∀ i j, ContinuousOn (fun y => dualMatrix (I := I) g alpha y i j) K := by
  intro i j
  have hdens : ContinuousOn (densityOnEuclid (I := I) g alpha) K :=
    (densityOnEuclid_contDiffOn (I := I) g alpha).continuousOn.mono hK_target
  have hdens_ne : ∀ y ∈ K, densityOnEuclid (I := I) g alpha y ≠ 0 := by
    intro y hy
    exact (densityOnEuclid_pos (I := I) g alpha (hK_target hy)).ne'
  have hgram : ContinuousOn (gramOnEuclid (I := I) g alpha i j) K :=
    (gramOnEuclid_contDiffOn (I := I) g alpha i j).continuousOn.mono hK_target
  exact (hdens.inv₀ hdens_ne).mul hgram

omit [NeZero (Module.finrank ℝ E)] in
private lemma inv_smul_weighted
    (g : SmoothRiemannianMetric I M) (alpha : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) alpha)
    {s : ℝ} (hs : 0 < s) :
    (s • weightedMatrix (I := I) g alpha y)⁻¹ =
      s⁻¹ • dualMatrix (I := I) g alpha y := by
  let G := gramMatrixOnEuclid (I := I) g alpha y
  have hG : G.PosDef := gramMatrixOnEuclid_posDef (I := I) g alpha hy
  let W := weightedMatrix (I := I) g alpha y
  have hW : W = densityOnEuclid (I := I) g alpha y • G⁻¹ := by
    ext i j
    rfl
  have hdens : 0 < densityOnEuclid (I := I) g alpha y :=
    densityOnEuclid_pos (I := I) g alpha hy
  have hWpos : W.PosDef := by
    rw [hW]
    exact hG.inv.smul hdens
  have hWinv : W⁻¹ = dualMatrix (I := I) g alpha y := by
    rw [hW]
    let : Invertible (densityOnEuclid (I := I) g alpha y) :=
      invertibleOfNonzero hdens.ne'
    have hscalar := Matrix.inv_smul G⁻¹
      (densityOnEuclid (I := I) g alpha y)
      ((Matrix.isUnit_iff_isUnit_det G⁻¹).mp hG.inv.isUnit)
    simp only [invOf_eq_inv] at hscalar
    rw [hscalar]
    let : Invertible G := hG.isUnit.invertible
    rw [Matrix.inv_inv_of_invertible]
    rfl
  let : Invertible s := invertibleOfNonzero hs.ne'
  have hscalar := Matrix.inv_smul W s
    ((Matrix.isUnit_iff_isUnit_det W).mp hWpos.isUnit)
  simp only [invOf_eq_inv] at hscalar
  rw [hscalar]
  simp only [hWinv]

theorem exists_normalizedEllipticCoeff_eq_smul_weightedInvGramOnEuclid
    (g : SmoothRiemannianMetric I M) (alpha : M)
    {c : EuclN} {r : ℝ} (hr : 0 < r)
    (h_target : closure (Metric.ball c r) ⊆
      chartTargetEuclid (I := I) (M := M) alpha) :
    ∃ (A : DeGiorgi.NormalizedEllipticCoeff
        (Module.finrank ℝ E) (Metric.ball c r)) (s : ℝ),
      0 < s ∧ ∀ y ∈ Metric.ball c r, ∀ i j,
        A.1.a y i j = s * weightedInvGramOnEuclid (I := I) g alpha i j y := by
  classical
  let K : Set EuclN := closure (Metric.ball c r)
  have hK_compact : IsCompact K := by
    dsimp only [K]
    rw [closure_ball c hr.ne']
    exact isCompact_closedBall c r
  obtain ⟨lam, hlam, hlam_bound⟩ :=
    exists_uniform_lower_bound_on_compact (I := I) g alpha hK_compact h_target
  obtain ⟨mu, hmu, hmu_bound⟩ := exists_quad_lower (E := E) hK_compact
    (dualMatrix (I := I) g alpha)
    (dualMatrix_continuousOn (I := I) g alpha h_target)
    (fun y hy => dualMatrix_posDef (I := I) g alpha (h_target hy))
  let s : ℝ := lam⁻¹
  have hs : 0 < s := inv_pos.mpr hlam
  let nu : ℝ := min 1 (lam * mu)
  have hnu : 0 < nu := lt_min one_pos (mul_pos hlam hmu)
  have hnu_le : nu ≤ lam * mu := min_le_right _ _
  let aFun : EuclN → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    (Metric.ball c r).piecewise
      (fun y => s • weightedMatrix (I := I) g alpha y)
      (fun _ => 1)
  have hmeas : ∀ i j, Measurable (fun y => aFun y i j) := by
    intro i j
    have hm : Measurable ((Metric.ball c r).piecewise
      (fun y => (s • weightedMatrix (I := I) g alpha y) i j)
      (fun _ => (1 : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) i j)) := by
      apply ContinuousOn.measurable_piecewise
      · have hw : ContinuousOn (weightedInvGramOnEuclid (I := I) g alpha i j)
          (Metric.ball c r) :=
          (weightedInvGramOnEuclid_contDiffOn (I := I) g alpha i j).continuousOn.mono
            (subset_closure.trans h_target)
        have hmul : ContinuousOn
            (fun y => s * weightedInvGramOnEuclid (I := I) g alpha i j y)
            (Metric.ball c r) :=
          (continuousOn_const.mul hw).congr fun _ _ => rfl
        simpa only [Matrix.smul_apply, weightedMatrix, Matrix.of_apply, smul_eq_mul]
          using hmul
      · exact continuous_const.continuousOn
      · exact measurableSet_ball
    convert hm using 1
    funext y
    by_cases hy : y ∈ Metric.ball c r
    · simp [aFun, hy]
    · simp [aFun, hy]
  have hco : ∀ y ∈ Metric.ball c r, ∀ xi : EuclN,
      1 * ‖xi‖ ^ 2 ≤ matrixQuad (E := E) (aFun y) xi := by
    intro y hy xi
    have hraw := hlam_bound y (subset_closure hy) xi
    have hpiece : aFun y = s • weightedMatrix (I := I) g alpha y := by
      simp only [aFun, Set.piecewise, hy, if_pos]
    rw [hpiece, matrixQuad_smul]
    change lam * ‖xi‖ ^ 2 ≤ matrixQuad (E := E) (weightedMatrix (I := I) g alpha y) xi
      at hraw
    have hmul := mul_le_mul_of_nonneg_left hraw hs.le
    have hslam : s * lam = 1 := by
      dsimp [s]
      exact inv_mul_cancel₀ hlam.ne'
    calc
      1 * ‖xi‖ ^ 2 = s * (lam * ‖xi‖ ^ 2) := by rw [← mul_assoc, hslam, one_mul]
      _ ≤ s * matrixQuad (E := E) (weightedMatrix (I := I) g alpha y) xi := hmul
  have hco_inv : ∀ y ∈ Metric.ball c r, ∀ xi : EuclN,
      nu * ‖xi‖ ^ 2 ≤ matrixQuad (E := E) (aFun y)⁻¹ xi := by
    intro y hy xi
    have hdual := hmu_bound y (subset_closure hy) xi
    have hpiece : aFun y = s • weightedMatrix (I := I) g alpha y := by
      simp only [aFun, Set.piecewise, hy, if_pos]
    rw [hpiece, inv_smul_weighted (I := I) g alpha (h_target (subset_closure hy)) hs,
      matrixQuad_smul]
    have hs_inv : s⁻¹ = lam := by simp [s]
    rw [hs_inv]
    calc
      nu * ‖xi‖ ^ 2 ≤ (lam * mu) * ‖xi‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hnu_le (sq_nonneg _)
      _ = lam * (mu * ‖xi‖ ^ 2) := by ring
      _ ≤ lam * matrixQuad (E := E) (dualMatrix (I := I) g alpha y) xi :=
        mul_le_mul_of_nonneg_left hdual hlam.le
  let coeff : DeGiorgi.EllipticCoeff (Module.finrank ℝ E) (Metric.ball c r) :=
    { a := aFun
      lam := 1
      Λ := nu⁻¹
      measurable_comp := hmeas
      hlam := one_pos
      hΛ := (one_le_inv₀ hnu).2 (min_le_left _ _)
      coercive := Filter.Eventually.of_forall fun y xi => by
        by_cases hy : y ∈ Metric.ball c r
        · exact hco y hy xi
        · change 1 * ‖xi‖ ^ 2 ≤ matrixQuad (E := E) (aFun y) xi
          rw [show aFun y = 1 by simp [aFun, hy], matrixQuad_one]
          rw [one_mul]
      coercive_inv := Filter.Eventually.of_forall fun y xi => by
        by_cases hy : y ∈ Metric.ball c r
        · simpa [nu, matrixQuad] using hco_inv y hy xi
        · change (nu⁻¹)⁻¹ * ‖xi‖ ^ 2 ≤ matrixQuad (E := E) (aFun y)⁻¹ xi
          rw [inv_inv]
          rw [show aFun y = 1 by simp [aFun, hy], inv_one, matrixQuad_one]
          exact mul_le_of_le_one_left (sq_nonneg _) (min_le_left _ _) }
  refine ⟨⟨coeff, rfl⟩, s, hs, ?_⟩
  intro y hy i j
  change aFun y i j = s * weightedInvGramOnEuclid (I := I) g alpha i j y
  simp only [aFun, Set.piecewise, hy, if_pos, Matrix.smul_apply, weightedMatrix,
    Matrix.of_apply, smul_eq_mul]

end MetricExtension
end Laplacian
end Analysis
end DifferentialGeometry
