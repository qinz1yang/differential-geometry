import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseOrderPeeling
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.SmoothTensorAllOrderCompleteness
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.NormComparison
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Metric DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [BoundarylessManifold I M] in
omit [T2Space M] in
lemma exists_lowerOrderCoeff_uniform_bound_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) (N : ℕ)
    {K : Set EuclN} (hK : IsCompact K) (hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx' : Fin s → Fin (Module.finrank ℝ E))
        (p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))),
        ∀ l ≤ N, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2) y‖ ≤ C := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_per : ∀ (w : Fin (Module.finrank ℝ E) ×
      (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)) ×
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))),
      ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ l ≤ N, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ l
          (covDerivLowerOrderCoeff (I := I) (M := M) g r s α w.1 w.2.1
            w.2.2.2.1 w.2.2.1 w.2.2.2.2) y‖ ≤ Cw :=
    fun w => exists_iteratedFDeriv_norm_bound_on_compactR
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α w.1 w.2.1
        w.2.2.2.1 w.2.2.1 w.2.2.2.2)
      h_open hK hK_sub N
  choose Cw hCw_nn hCw using h_per
  refine ⟨(Finset.univ : Finset (Fin (Module.finrank ℝ E) ×
      (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)) ×
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))))).sup'
      ⟨⟨0, fun _ => 0, fun _ => 0, ⟨fun _ => 0, fun _ => 0⟩⟩, Finset.mem_univ _⟩ Cw, ?_, ?_⟩
  · refine le_trans (hCw_nn ⟨0, fun _ => 0, fun _ => 0, ⟨fun _ => 0, fun _ => 0⟩⟩) ?_
    exact Finset.le_sup' Cw (Finset.mem_univ _)
  · intro m Idx Jdx' p l hl y hy
    exact (hCw ⟨m, Idx, Jdx', p⟩ l hl y hy).trans
      (Finset.le_sup' Cw (Finset.mem_univ ⟨m, Idx, Jdx', p⟩))

omit [BoundarylessManifold I M] in
omit [T2Space M] in
lemma exists_christoffel_bound_valence_range_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) (P N : ℕ)
    {K : Set EuclN} (hK : IsCompact K) (hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ p ≤ P,
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx' : Fin (s + p) → Fin (Module.finrank ℝ E))
        (q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin (s + p) → Fin (Module.finrank ℝ E))),
        ∀ l ≤ N, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx q.1 Jdx' q.2)
            y‖ ≤ Γ := by
  classical
  have hper : ∀ p : ℕ, ∃ Γ : ℝ, 0 ≤ Γ ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx' : Fin (s + p) → Fin (Module.finrank ℝ E))
        (q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin (s + p) → Fin (Module.finrank ℝ E))),
        ∀ l ≤ N, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx q.1 Jdx' q.2)
            y‖ ≤ Γ :=
    fun p => exists_lowerOrderCoeff_uniform_bound_on_compact (I := I) (M := M)
      g r (s + p) α N hK hK_sub
  choose Γf hΓf_nn hΓf using hper
  refine ⟨(Finset.range (P + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos P)⟩ Γf, ?_, ?_⟩
  · exact le_trans (hΓf_nn 0)
      (Finset.le_sup' Γf (Finset.mem_range.mpr (Nat.succ_pos P)))
  · intro p hp m Idx Jdx' q l hl y hy
    exact (hΓf p m Idx Jdx' q l hl y hy).trans
      (Finset.le_sup' Γf (Finset.mem_range.mpr (by omega)))

omit [BoundarylessManifold I M] in
lemma iteratedFDeriv_rawPullR_le_zeroContent_sum_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : ℕ)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∀ j : ℕ, j ≤ P → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s)
        (l : ℕ), l ≤ j → ∀ (p : ℕ), p + l ≤ P →
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin (s + p) → Fin (Module.finrank ℝ E)),
          ∀ y ∈ K,
            ‖iteratedFDeriv ℝ l
                (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
                  (iteratedCovGrad g r s p T) α Idx Jdx) y‖ ≤
              C * ∑ i ∈ Finset.range (l + 1),
                tensorComponentAbsSum (I := I) (M := M) g r (s + (p + i))
                  (iteratedCovGrad g r s (p + i) T) α y := by
  classical
  obtain ⟨Γ, hΓ_nn, hΓ⟩ :=
    exists_christoffel_bound_valence_range_on_compact (I := I) (M := M) g r s α P P hK hK_sub
  change christoffelOrderBoundOn (I := I) (M := M) K g r s α P Γ at hΓ
  intro j
  induction j with
  | zero =>
      intro _hP
      refine ⟨1, zero_le_one, fun T l hl p _ Idx Jdx y hy => ?_⟩
      have hl0 : l = 0 := Nat.le_zero.mp hl
      subst hl0
      rw [norm_iteratedFDeriv_zero,
        show (Finset.range (0 + 1)) = {0} from rfl, Finset.sum_singleton]
      simp only [Nat.add_zero, one_mul]
      have h1 := abs_rawPullR_le_zeroContentR (I := I) (M := M) g r (s + p)
        (iteratedCovGrad g r s p T) α Idx Jdx y
      calc ‖tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
              (iteratedCovGrad g r s p T) α Idx Jdx y‖
          = |tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
              (iteratedCovGrad g r s p T) α Idx Jdx y| := Real.norm_eq_abs _
        _ ≤ tensorComponentAbsSum (I := I) (M := M) g r (s + (p + 0))
              (iteratedCovGrad g r s (p + 0) T) α y := by
            rw [Nat.add_zero]; exact h1
  | succ j ih =>
      intro hjP
      obtain ⟨Cj, hCj_nn, hCj⟩ := ih (by omega)
      change rawPullOrderBoundOn (I := I) (M := M) K g r s α P j Cj at hCj
      set Np : ℝ := (Module.finrank ℝ E : ℝ) ^ (r + (s + P)) with hNp_def
      set Cstep : ℝ := (Module.finrank ℝ E : ℝ) ^ j *
        (Cj + (Np : ℝ) * ((2 : ℝ) ^ j) * Γ * Cj) with hCstep_def
      refine ⟨max Cj ((Module.finrank ℝ E : ℝ) * Cstep), le_max_of_le_left hCj_nn, ?_⟩
      intro T l hl p hpl Idx Jdx y hy
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hl) with hlj | hlj
      · have hl' : l ≤ j := by omega
        have hbase := hCj T l hl' p (by omega) Idx Jdx y hy
        refine le_trans hbase ?_
        apply mul_le_mul_of_nonneg_right (le_max_left _ _)
        exact Finset.sum_nonneg (fun i _ => zeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _)
      · subst hlj
        have hy_mem : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hy
        set RHSsum : ℝ := ∑ i ∈ Finset.range ((j + 1) + 1),
          tensorComponentAbsSum (I := I) (M := M) g r (s + (p + i))
            (iteratedCovGrad g r s (p + i) T) α y with hRHSsum_def
        have hRHSsum_nn : 0 ≤ RHSsum :=
          Finset.sum_nonneg (fun i _ => zeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _)
        set Cm : ℝ := Cj + (Np : ℝ) * ((2 : ℝ) ^ j) * Γ * Cj with hCm_def
        have h_perm : ∀ m : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ j
                (fun z => euclidPartial (E := E) m
                  (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
                    (iteratedCovGrad g r s p T) α Idx Jdx) z) y‖ ≤
              Cm * RHSsum := by
          intro m
          simpa only [hCm_def, hNp_def, hRHSsum_def] using
            iteratedFDeriv_euclidPartial_le_of_order_bounds (I := I) (M := M)
              g r s α P K hK_sub Γ hΓ_nn hΓ j Cj hCj_nn hCj T p (by omega)
              Idx Jdx y hy m
        have h_peel := iteratedFDeriv_succ_norm_le_sum_euclidPartial (E := E)
          (u := tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
            (iteratedCovGrad g r s p T) α Idx Jdx)
          (O := chartTargetEuclid (I := I) (M := M) α)
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          (rawPullR_contDiffOn (I := I) (M := M) g r (s + p)
            (iteratedCovGrad g r s p T) α Idx Jdx) j hy_mem
        have h_sum_le : (∑ m : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ j
              (fun z => euclidPartial (E := E) m
                (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
                  (iteratedCovGrad g r s p T) α Idx Jdx) z) y‖) ≤
            (Module.finrank ℝ E : ℝ) * (Cm * RHSsum) := by
          calc (∑ m : Fin (Module.finrank ℝ E),
                ‖iteratedFDeriv ℝ j
                  (fun z => euclidPartial (E := E) m
                    (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
                      (iteratedCovGrad g r s p T) α Idx Jdx) z) y‖)
              ≤ ∑ _m : Fin (Module.finrank ℝ E), Cm * RHSsum :=
                Finset.sum_le_sum (fun m _ => h_perm m)
            _ = (Module.finrank ℝ E : ℝ) * (Cm * RHSsum) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h_final : ‖iteratedFDeriv ℝ (j + 1)
            (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
              (iteratedCovGrad g r s p T) α Idx Jdx) y‖ ≤
            ((Module.finrank ℝ E : ℝ) * Cstep) * RHSsum := by
          calc ‖iteratedFDeriv ℝ (j + 1)
                (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
                  (iteratedCovGrad g r s p T) α Idx Jdx) y‖
              ≤ ((Module.finrank ℝ E) ^ j : ℝ) *
                  ∑ m : Fin (Module.finrank ℝ E),
                    ‖iteratedFDeriv ℝ j
                      (fun z => euclidPartial (E := E) m
                        (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
                          (iteratedCovGrad g r s p T) α Idx Jdx) z) y‖ := h_peel
            _ ≤ ((Module.finrank ℝ E) ^ j : ℝ) *
                  ((Module.finrank ℝ E : ℝ) * (Cm * RHSsum)) := by
                apply mul_le_mul_of_nonneg_left h_sum_le (by positivity)
            _ = ((Module.finrank ℝ E : ℝ) * Cstep) * RHSsum := by
                rw [hCstep_def, hCm_def]; ring
        refine le_trans h_final ?_
        apply mul_le_mul_of_nonneg_right (le_max_right _ _) hRHSsum_nn

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorChartComponentRaw_sq_le_const_mul_tensorInner_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M : IsCompact K_M)
    (hK_M_sub : K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M), b ∈ K_M →
        (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx b) ^ 2 ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact
      (I := I) (M := M) (E := E) g r s α hK_M hK_M_sub
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b hb
  set T : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α b with hT_def
  set P_IJ : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx with hP_def
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hK_M_sub hb
  have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hraw_eq : tensorChartComponentRaw (I := I) (M := M)
      g r s S α Idx Jdx b = P_IJ T := rfl
  have h_proj_le : ‖P_IJ T‖ ≤ C_proj * ‖T‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
        (norm_nonneg _))
  have h_proj_sq_le : (P_IJ T) ^ 2 ≤ C_proj ^ 2 * ‖T‖ ^ 2 := by
    have h_abs : (P_IJ T) ^ 2 = ‖P_IJ T‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_abs]
    have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
    have h_rhs : (C_proj * ‖T‖) * (C_proj * ‖T‖) = C_proj ^ 2 * ‖T‖ ^ 2 := by ring
    have h_lhs : ‖P_IJ T‖ * ‖P_IJ T‖ = ‖P_IJ T‖ ^ 2 := by rw [sq]
    linarith [hsq, h_lhs.symm.le, h_rhs.symm.le, h_lhs.le, h_rhs.le]
  have h_chart_sq_le : ‖T‖ ^ 2 ≤
      K * chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T :=
    h_norm b hb T
  have h_chart_eq : chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T =
      tensorInnerPointwise (I := I) (M := M) g r s b (S.toFun b) (S.toFun b) := by
    rw [hT_def]
    exact chartTensorInner_tensorTrivProj_eq_tensorInner_toFun
      (I := I) (M := M) g r s α S hb_base
  have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := by
    rw [← h_chart_eq]; exact h_chart_sq_le
  have hC_proj_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
  have h_chain_sq : (P_IJ T) ^ 2 ≤
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
    h_proj_sq_le.trans (mul_le_mul_of_nonneg_left h_triv_sq_le hC_proj_sq_nn)
  rw [hraw_eq]
  have h_rhs_rearr :
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) =
        C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by ring
  linarith [h_chain_sq, h_rhs_rearr.le, h_rhs_rearr.symm.le]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
omit [I.Boundaryless] [T2Space M] in
lemma exists_zeroContentR_le_fiberNorm_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M : IsCompact K_M)
    (hK_M_sub : K_M ⊆ (chartAt H α).source) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace r s I b) :=
      fun b =>
        instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
          (E := fun z : M => TensorRSSpace r s I z) b
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M}, b ∈ K_M →
        tensorComponentAbsSum (I := I) (M := M) g r s S α
            (toEuclidean (E := E) (extChartAt I α b)) ≤
          C * ‖S.toSection b‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace r s I b) :=
    fun b =>
      instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun z : M => TensorRSSpace r s I z) b
  have hK_M_base : K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hK_M_sub
  obtain ⟨Craw, hCraw_nn, hCraw⟩ :=
    tensorChartComponentRaw_sq_le_const_mul_tensorInner_on_compact (I := I) (M := M)
      g r s α hK_M hK_M_base
  set Npair : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
    (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hNpair_def
  have hNpair_nn : 0 ≤ Npair := by positivity
  refine ⟨Npair * Real.sqrt Craw, by positivity, ?_⟩
  intro S b hb
  set y : EuclN := toEuclidean (E := E) (extChartAt I α b) with hy_def
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hK_M_sub hb
  have hb_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    rw [hy_def, (toEuclidean (E := E)).symm_apply_apply]
    exact (extChartAt I α).left_inv hb_src
  have hfib_eq : ‖S.toSection b‖ =
      Real.sqrt (tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) := by
    rw [show S.toFun b = TensorRSSpace.toModel (𝕜 := ℝ) (I := I) (S.toSection b) from rfl]
    exact DifferentialGeometry.Analysis.Elliptic.norm_eq_sqrt_tensorInnerPointwise
      (I := I) (M := M) g r s b (S.toSection b)
  have hInner_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hfib_nn : 0 ≤ ‖S.toSection b‖ := norm_nonneg _
  have h_raw_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      tensorComponentEuclideanChart (I := I) (M := M) g r s S α Idx Jdx y =
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
    intro Idx Jdx
    rw [tensorComponentEuclideanChart, Function.comp_apply, Function.comp_apply, hb_eq]
  have h_each : ∀ (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))),
      |tensorComponentEuclideanChart (I := I) (M := M) g r s S α q.1 q.2 y| ≤
        Real.sqrt Craw * ‖S.toSection b‖ := by
    intro q
    rw [h_raw_eq q.1 q.2]
    have hsq := hCraw S q.1 q.2 b hb
    have hroot :
        Real.sqrt
            ((tensorChartComponentRaw (I := I) (M := M) g r s S α q.1 q.2 b) ^ 2) ≤
          Real.sqrt (Craw * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs] at hroot
    refine hroot.trans (le_of_eq ?_)
    rw [Real.sqrt_mul hCraw_nn, hfib_eq]
  calc tensorComponentAbsSum (I := I) (M := M) g r s S α y
      = ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          |tensorComponentEuclideanChart (I := I) (M := M) g r s S α q.1 q.2 y| := rfl
    _ ≤ ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          Real.sqrt Craw * ‖S.toSection b‖ :=
        Finset.sum_le_sum (fun q _ => h_each q)
    _ = Npair * Real.sqrt Craw * ‖S.toSection b‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNpair_def]; ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma zeroContent_sum_le_sobolev_norm
    (g : SmoothRiemannianMetric I M) (r s m k : ℕ) (α : M)
    (K_M : Set M) (Czf : ℕ → ℝ) (Czmax Cemb : ℝ)
    (hCzmax_nn : 0 ≤ Czmax)
    (hCz_le : ∀ i ∈ Finset.range (m + 1), Czf i ≤ Czmax)
    (hCzf : ∀ i : ℕ, ∀ (S : SmoothCcTensor g r s) {b : M}, b ∈ K_M →
      tensorComponentAbsSum (I := I) (M := M) g r (s + i)
          (iteratedCovGrad g r s i S) α
          (toEuclidean (E := E) (extChartAt I α b)) ≤
        Czf i *
          (letI : Bundle.RiemannianBundle
              (fun z : M => TensorRSSpace r (s + i) I z) :=
            Tensor0SBundle.tensorRS_riemannianBundle
              (I := I) (M := M) g r (s + i)
           letI : ∀ z : M, NormedAddCommGroup (TensorRSSpace r (s + i) I z) :=
             fun z =>
               instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
                 (E := fun w : M => TensorRSSpace r (s + i) I w) z
           ‖(iteratedCovGrad g r s i S).toSection b‖))
    (hCemb : ∀ (S : SmoothCcTensor g r s) (b : M),
      ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle
              (fun z : M => TensorRSSpace r (s + i) I z) :=
            Tensor0SBundle.tensorRS_riemannianBundle
              (I := I) (M := M) g r (s + i)
           letI : ∀ z : M, NormedAddCommGroup (TensorRSSpace r (s + i) I z) :=
             fun z =>
               instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
                 (E := fun w : M => TensorRSSpace r (s + i) I w) z
           ‖(iteratedCovGrad g r s i S).toSection b‖) ≤
        Cemb * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S‖)
    (S : SmoothCcTensor g r s) {b : M} (hb : b ∈ K_M) :
    ∑ i ∈ Finset.range (m + 1),
        tensorComponentAbsSum (I := I) (M := M) g r (s + (0 + i))
          (iteratedCovGrad g r s (0 + i) S) α
          (toEuclidean (E := E) (extChartAt I α b)) ≤
      Czmax * (Cemb * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S‖) := by
  have hsum : ∑ i ∈ Finset.range (m + 1),
        tensorComponentAbsSum (I := I) (M := M) g r (s + (0 + i))
          (iteratedCovGrad g r s (0 + i) S) α
          (toEuclidean (E := E) (extChartAt I α b)) ≤
      Czmax * ∑ i ∈ Finset.range (m + 1),
        (letI : Bundle.RiemannianBundle
            (fun z : M => TensorRSSpace r (s + i) I z) :=
          Tensor0SBundle.tensorRS_riemannianBundle
            (I := I) (M := M) g r (s + i)
         letI : ∀ z : M, NormedAddCommGroup (TensorRSSpace r (s + i) I z) :=
           fun z =>
             instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
               (E := fun w : M => TensorRSSpace r (s + i) I w) z
         ‖(iteratedCovGrad g r s i S).toSection b‖) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Nat.zero_add]
    refine (hCzf i S hb).trans ?_
    letI : Bundle.RiemannianBundle
        (fun z : M => TensorRSSpace r (s + i) I z) :=
      Tensor0SBundle.tensorRS_riemannianBundle
        (I := I) (M := M) g r (s + i)
    letI : ∀ z : M, NormedAddCommGroup (TensorRSSpace r (s + i) I z) :=
      fun z =>
        instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
          (E := fun w : M => TensorRSSpace r (s + i) I w) z
    exact mul_le_mul_of_nonneg_right (hCz_le i hi) (norm_nonneg _)
  exact hsum.trans (mul_le_mul_of_nonneg_left (hCemb S b) hCzmax_nn)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
lemma rawPullR_jet_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (m k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g r s) (y : EuclN), y ∈ K →
      ‖iteratedFDeriv ℝ m
          (tensorComponentEuclideanChart (I := I) (M := M) g r s S α Idx Jdx) y‖ ≤
        C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S‖ := by
  classical
  set K_E : Set E := (toEuclidean (E := E)).symm '' K with hK_E_def
  have hK_E_compact : IsCompact K_E :=
    hK.image (toEuclidean (E := E)).symm.continuous
  have hK_E_sub : K_E ⊆ interior (extChartAt I α).target := by
    rw [hK_E_def]
    rintro z ⟨y, hy, rfl⟩
    have hy' := hK_sub hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy'
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy'
  set K_M : Set M := (extChartAt I α).symm '' K_E with hK_M_def
  have hK_M_compact : IsCompact K_M :=
    hK_E_compact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) α).mono
        (fun z hz => interior_subset (hK_E_sub hz)))
  have hK_M_sub : K_M ⊆ (chartAt H α).source := by
    rw [hK_M_def]
    rintro b ⟨z, hz, rfl⟩
    have hz' : z ∈ (extChartAt I α).target := interior_subset (hK_E_sub hz)
    have := (extChartAt I α).map_target hz'
    rwa [extChartAt_source (I := I)] at this
  obtain ⟨Cpeel, hCpeel_nn, hpeel⟩ :=
    iteratedFDeriv_rawPullR_le_zeroContent_sum_on_compact
      (I := I) (M := M) g r s α m hK hK_sub m (le_refl m)
  have hz_per : ∀ i : ℕ, ∃ Cz : ℝ, 0 ≤ Cz ∧
      ∀ (S : SmoothCcTensor g r s) {b : M}, b ∈ K_M →
        tensorComponentAbsSum (I := I) (M := M) g r (s + i)
            (iteratedCovGrad g r s i S) α
            (toEuclidean (E := E) (extChartAt I α b)) ≤
          Cz *
            (letI : Bundle.RiemannianBundle
                (fun z : M => TensorRSSpace r (s + i) I z) :=
              Tensor0SBundle.tensorRS_riemannianBundle
                (I := I) (M := M) g r (s + i)
             letI : ∀ z : M, NormedAddCommGroup (TensorRSSpace r (s + i) I z) :=
               fun z =>
                 instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
                   (E := fun w : M => TensorRSSpace r (s + i) I w) z
             ‖(iteratedCovGrad g r s i S).toSection b‖) := by
    intro i
    obtain ⟨Cz, hCz_nn, hCz⟩ :=
      exists_zeroContentR_le_fiberNorm_on_compact
        (I := I) (M := M) g r (s + i) α hK_M_compact hK_M_sub
    exact ⟨Cz, hCz_nn, fun S b hb => hCz (iteratedCovGrad g r s i S) hb⟩
  choose Czf hCzf_nn hCzf using hz_per
  set Czmax : ℝ :=
    (Finset.range (m + 1)).sup'
      (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m)) Czf with hCzmax_def
  have hCzmax_nn : 0 ≤ Czmax := by
    rw [hCzmax_def]
    exact le_trans (hCzf_nn 0)
      (Finset.le_sup' Czf (Finset.mem_range.mpr (Nat.succ_pos m)))
  have hCz_le : ∀ i ∈ Finset.range (m + 1), Czf i ≤ Czmax :=
    fun i hi => Finset.le_sup' Czf hi
  obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
    iteratedCovGrad_toSobolev_embedding_Cm_singleNorm
      (I := I) (M := M) g r s k m h_super
  refine ⟨Cpeel * (Czmax * Cemb), by positivity, fun S y hy => ?_⟩
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hyE : (toEuclidean (E := E)).symm y ∈ K_E := ⟨y, hy, rfl⟩
  have hb_mem : b ∈ K_M := ⟨(toEuclidean (E := E)).symm y, hyE, rfl⟩
  have hy_eq : toEuclidean (E := E) (extChartAt I α b) = y := by
    rw [hb_def]
    have hy_target : (toEuclidean (E := E)).symm y ∈
        (extChartAt I α).target := interior_subset (hK_E_sub hyE)
    rw [(extChartAt I α).right_inv hy_target,
      ContinuousLinearEquiv.apply_symm_apply]
  have hsum := zeroContent_sum_le_sobolev_norm (I := I) (M := M)
    g r s m k α K_M Czf Czmax Cemb hCzmax_nn hCz_le hCzf hCemb S hb_mem
  rw [hy_eq] at hsum
  have hpeel_y := hpeel S m (le_refl m) 0 (by omega) Idx Jdx y hy
  rw [iteratedCovGrad_zero] at hpeel_y
  calc
    ‖iteratedFDeriv ℝ m
        (tensorComponentEuclideanChart (I := I) (M := M) g r s S α Idx Jdx) y‖
        ≤ Cpeel * ∑ i ∈ Finset.range (m + 1),
            tensorComponentAbsSum (I := I) (M := M) g r (s + (0 + i))
              (iteratedCovGrad g r s (0 + i) S) α y := hpeel_y
    _ ≤ Cpeel * (Czmax *
        (Cemb * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S‖)) :=
      mul_le_mul_of_nonneg_left hsum hCpeel_nn
    _ = Cpeel * (Czmax * Cemb) *
        ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S‖ := by ring
end DifferentialGeometry.Analysis.Spectral
