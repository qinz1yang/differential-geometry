import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Ladder
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ParametricOperatorFieldApplicationJetBound

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem operatorFieldApplicationPerIdxL2 (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (Λ : ℕ → ℝ),
        (∀ (i : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
            ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x) ≤ Λ i ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q
            (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * ∑ i ∈ Finset.range (q + 1), Λ i ^ 2 *
            ∑ l ∈ Finset.range (q + 1 - i),
              ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by
  refine ⟨operatorFieldApplicationGdiag (E := E) q, operatorFieldApplicationGdiag_nonneg (E := E) q, ?_⟩
  intro Φ W Λ hsup
  exact app_jet_sq_le (I := I) (M := M) g₀ b₀ s₀ q Φ W (fun i => Λ i ^ 2)
    (fun i _ => sq_nonneg (Λ i)) (fun i _ x => hsup i x)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem iteratedCovGradWinShift (g : SmoothRiemannianMetric I M) (r s m p : ℕ)
    (Ψ : SmoothCcTensor g r s) :
    (∑ l ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g r (s + m) l
        (iteratedCovGrad (I := I) g r s m Ψ)‖ ^ 2) ≤
      ∑ j ∈ Finset.range (p + m + 1),
        ‖iteratedCovGrad (I := I) g r s j Ψ‖ ^ 2 := by
  classical
  rw [show (∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g r (s + m) l
          (iteratedCovGrad (I := I) g r s m Ψ)‖ ^ 2) =
      ∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g r s (m + l) Ψ‖ ^ 2 from
    Finset.sum_congr rfl (fun l _ => by
      rw [DifferentialGeometry.Integral.Connection.iteratedCovGrad_norm_comp
        (I := I) (M := M) g r s m l Ψ])]
  set f : ℕ → ℝ := fun j => ‖iteratedCovGrad (I := I) g r s j Ψ‖ ^ 2 with hf_def
  have hinj : ∀ l₁ ∈ Finset.range (p + 1), ∀ l₂ ∈ Finset.range (p + 1),
      m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
  have himg : (Finset.range (p + 1)).image (fun l => m + l) ⊆
      Finset.range (p + m + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    rw [Finset.mem_range] at hl ⊢
    omega
  calc (∑ l ∈ Finset.range (p + 1), f (m + l))
      = ∑ j ∈ (Finset.range (p + 1)).image (fun l => m + l), f j :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ j ∈ Finset.range (p + m + 1), f j :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => sq_nonneg _)

theorem sqrtAdd2 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hsq : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have hxx := Real.sq_sqrt hx
    have hyy := Real.sq_sqrt hy
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

theorem sqrtFinSum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine le_trans (sqrtAdd2 _ _ (hf a)
        (Finset.sum_nonneg (fun i _ => hf i))) ?_
      exact add_le_add le_rfl ih

private theorem c2SupJet (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Ks : ℕ → ℝ, (∀ i, 0 ≤ Ks i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g (2 + 2) (2 + i) x
            ((iteratedCovGrad (I := I) g (2 + 2) 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderCoefficient).toSection x) ≤
          Ks i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kc, hKc_nn, htower⟩ := secondOrderCoefficient_jet_tower_sharp (I := I) (M := M) g g_bg
  choose Csh hCsh_nn hCsh using fun i : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g (2 + 2) (2 + i)
  refine ⟨fun i => Csh i ^ 2 * ∑ j ∈ Finset.range 3, Kc (i + j),
    fun i => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg (fun j _ => hKc_nn (i + j))), ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i x
  set C₂ := (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
    (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderCoefficient with hC₂
  set J : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJ
  have hJ_nn : ∀ n, 0 ≤ J n := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hJ_mono : ∀ {a b : ℕ}, a ≤ b → J a ≤ J b := by
    intro a b hab
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hwin : Module.finrank ℝ E / 2 + 2 = 3 := by rw [hDim]
  have hemb := hCsh i (iteratedCovGrad (I := I) g (2 + 2) 2 i C₂) x
  rw [hwin] at hemb
  refine hemb.trans ?_
  have hstep : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (2 + 2) (2 + i) j
        (iteratedCovGrad (I := I) g (2 + 2) 2 i C₂)‖ ^ 2 ≤
        Kc (i + j) * (1 + J (i + 2)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [DifferentialGeometry.Integral.Connection.iteratedCovGrad_norm_comp
      (I := I) (M := M) g (2 + 2) 2 i j C₂]
    refine (htower T hT hδ0 hδ_le hδg hδZ (i + j)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKc_nn (i + j))
    have := hJ_mono (a := i + j) (b := i + 2) (by omega)
    linarith only [this]
  calc Csh i ^ 2 * ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (2 + 2) (2 + i) j
          (iteratedCovGrad (I := I) g (2 + 2) 2 i C₂)‖ ^ 2
      ≤ Csh i ^ 2 * ∑ j ∈ Finset.range 3, Kc (i + j) * (1 + J (i + 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) (sq_nonneg _)
    _ = Csh i ^ 2 * (∑ j ∈ Finset.range 3, Kc (i + j)) * (1 + J (i + 2)) := by
        rw [← Finset.sum_mul]; ring

theorem secondOrderAction_perIndex_jet_bound (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Cq K : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {Cδ : ℝ}
        (hfib : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (2 + 2) 2 x
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderCoefficient.toSection x) ≤
            Cδ ^ 2)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction
                (I := I) (M := M) T)‖ ^ 2 ≤
          Cq q * (Cδ ^ 2 * ∑ j ∈ Finset.range (q + 3),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 +
            ∑ i ∈ Finset.Icc 1 q, K i *
              (1 + ∑ j ∈ Finset.range (i + 3),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
              ∑ j ∈ Finset.range (q - i + 3),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Ks, hKs_nn, hsup⟩ := c2SupJet (I := I) (M := M) hDim g g_bg
  choose Cq hCq_nn hCq using fun q : ℕ => operatorFieldApplicationPerIdxL2 (I := I) (M := M) g (2 + 2) 2 q
  refine ⟨Cq, Ks, hCq_nn, hKs_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ Cδ hfib q
  set A := lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
    (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ with hA
  set J : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJ
  have hJ_nn : ∀ n, 0 ≤ J n := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set Λ : ℕ → ℝ := fun i =>
    if i = 0 then |Cδ| else Real.sqrt (Ks i * (1 + J (i + 2))) with hΛ
  have hΛsup : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g (2 + 2) (2 + i) x
        ((iteratedCovGrad (I := I) g (2 + 2) 2 i A.secondOrderCoefficient).toSection x) ≤ Λ i ^ 2 := by
    intro i x
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      have hΛ0 : Λ 0 ^ 2 = Cδ ^ 2 := by simp only [hΛ]; norm_num [sq_abs]
      rw [hΛ0]
      simpa only [iteratedCovGrad_zero] using hfib x
    · have hne : i ≠ 0 := by omega
      rw [hΛ]
      simp only [if_neg hne]
      rw [Real.sq_sqrt (mul_nonneg (hKs_nn i) (by linarith only [hJ_nn (i + 2)]))]
      exact hsup T hT hδ0 hδ_le hδg hδZ i x
  have hshape : A.secondOrderAction (I := I) (M := M) T =
      operatorFieldApply (I := I) (M := M) g (2 + 2) 2 A.secondOrderCoefficient
        (iteratedCovGrad (I := I) g 0 2 2 T) := rfl
  rw [hshape]
  refine (hCq q A.secondOrderCoefficient (iteratedCovGrad (I := I) g 0 2 2 T) Λ hΛsup).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (hCq_nn q)
  have hdata : ∀ i ∈ Finset.range (q + 1),
      (∑ l ∈ Finset.range (q + 1 - i),
        ‖iteratedCovGrad (I := I) g 0 (2 + 2) l
          (iteratedCovGrad (I := I) g 0 2 2 T)‖ ^ 2) ≤ J (q - i + 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hq : q + 1 - i = (q - i) + 1 := by omega
    rw [hq]
    simp only [hJ]
    exact iteratedCovGradWinShift (I := I) g 0 2 2 (q - i) T
  have hsplit : Finset.range (q + 1) = insert 0 (Finset.Icc 1 q) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 q := by simp
  rw [hsplit, Finset.sum_insert hnotmem]
  refine add_le_add ?_ ?_
  · have h0 : Λ 0 ^ 2 = Cδ ^ 2 := by simp only [hΛ]; norm_num [sq_abs]
    rw [h0]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hd := hdata 0 (Finset.mem_range.mpr (by omega))
    simp only [hJ] at hd
    rw [show q - 0 + 2 + 1 = q + 3 from by omega] at hd
    exact hd
  · refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    have hne : i ≠ 0 := by omega
    have hΛi : Λ i ^ 2 = Ks i * (1 + J (i + 2)) := by
      simp only [hΛ, if_neg hne]
      exact Real.sq_sqrt (mul_nonneg (hKs_nn i) (by linarith only [hJ_nn (i + 2)]))
    have hd := hdata i (Finset.mem_range.mpr (by omega))
    simp only [hJ] at hΛi hd
    rw [show i + 2 + 1 = i + 3 from by omega] at hΛi
    rw [show q - i + 2 + 1 = q - i + 3 from by omega] at hd
    rw [hΛi]
    refine mul_le_mul_of_nonneg_left hd ?_
    refine mul_nonneg (hKs_nn i) ?_
    have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 3),
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith only [this]

theorem secondOrderAction_perIndex_linear_bound (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Cq K : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {Cδ : ℝ} (hCδ : 0 ≤ Cδ)
        (hfib : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (2 + 2) 2 x
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderCoefficient.toSection x) ≤
            Cδ ^ 2)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction
                (I := I) (M := M) T)‖ ≤
          Cq q * (Cδ * Real.sqrt (∑ j ∈ Finset.range (q + 3),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
            ∑ i ∈ Finset.Icc 1 q, K i *
              (1 + Real.sqrt (∑ j ∈ Finset.range (i + 3),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
              Real.sqrt (∑ j ∈ Finset.range (q - i + 3),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Cq, K, hCq_nn, hK_nn, hsq⟩ := secondOrderAction_perIndex_jet_bound (I := I) (M := M) hDim g g_bg
  refine ⟨fun q => Real.sqrt (Cq q), fun i => Real.sqrt (K i),
    fun q => Real.sqrt_nonneg _, fun i => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ Cδ hCδ hfib q
  set J : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n + 3),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJ
  have hJ_nn : ∀ n, 0 ≤ J n := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hterm_nn : ∀ i, 0 ≤ K i * (1 + J i) * J (q - i) := fun i =>
    mul_nonneg (mul_nonneg (hK_nn i) (by linarith only [hJ_nn i])) (hJ_nn (q - i))
  have hsum_nn : (0 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 q, K i * (1 + J i) * J (q - i) :=
    Finset.sum_nonneg (fun i _ => hterm_nn i)
  have hbase_nn : (0 : ℝ) ≤ Cδ ^ 2 * J q := mul_nonneg (sq_nonneg _) (hJ_nn q)
  have h : ‖iteratedCovGrad (I := I) g 0 2 q
      ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction
          (I := I) (M := M) T)‖ ^ 2 ≤
      Cq q * (Cδ ^ 2 * J q +
        ∑ i ∈ Finset.Icc 1 q, K i * (1 + J i) * J (q - i)) :=
    hsq T hT hδ0 hδ_le hδg hδZ hfib q
  have hroot : ‖iteratedCovGrad (I := I) g 0 2 q
      ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction (I := I) (M := M) T)‖ ≤
      Real.sqrt (Cq q) * Real.sqrt (Cδ ^ 2 * J q +
        ∑ i ∈ Finset.Icc 1 q, K i * (1 + J i) * J (q - i)) := by
    have hs := Real.sqrt_le_sqrt h
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (hCq_nn q)] at hs
    exact hs
  refine hroot.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine le_trans (sqrtAdd2 _ _ hbase_nn hsum_nn) ?_
  have hbase : Real.sqrt (Cδ ^ 2 * J q) = Cδ * Real.sqrt (J q) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCδ]
  rw [hbase]
  refine add_le_add le_rfl ?_
  refine le_trans (sqrtFinSum (Finset.Icc 1 q)
    (fun i => K i * (1 + J i) * J (q - i)) hterm_nn) ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h1 : Real.sqrt (K i * (1 + J i) * J (q - i)) =
      Real.sqrt (K i) * Real.sqrt (1 + J i) * Real.sqrt (J (q - i)) := by
    rw [Real.sqrt_mul (mul_nonneg (hK_nn i) (by linarith only [hJ_nn i])),
      Real.sqrt_mul (hK_nn i)]
  rw [h1]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hle : (1 : ℝ) + J i ≤ (1 + Real.sqrt (J i)) ^ 2 := by
    have := Real.sq_sqrt (hJ_nn i)
    nlinarith [Real.sqrt_nonneg (J i)]
  calc Real.sqrt (1 + J i)
      ≤ Real.sqrt ((1 + Real.sqrt (J i)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 1 + Real.sqrt (J i) := Real.sqrt_sq (by positivity)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
