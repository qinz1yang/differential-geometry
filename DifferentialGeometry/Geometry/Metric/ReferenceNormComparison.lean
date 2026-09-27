import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Tensor.Metric.CompactBounds
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Comparison
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Bundle DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem exists_tensor_bound_on_open
    (R₀ R₁ : SmoothRiemannianMetric I M) {U : Set M} (hU : IsOpen U)
    (k : ℕ) (A D : ℝ) (hA : 1 ≤ A) (hD : 0 ≤ D)
    (heq : ∀ x ∈ U, ∀ v : TangentSpace I x,
      A⁻¹ * R₀.inner x v v ≤ R₁.inner x v v ∧ R₁.inner x v v ≤ A * R₀.inner x v v)
    (hjet : ∀ j ≤ k, ∀ x ∈ U,
      Real.sqrt (normSq0S R₀ x (2 + j)
        (iterCov R₀ 2 (metricTensorField R₁) j x)) ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Tensor0SField (I := I) (M := M) ∞ 2)
      (x : M), x ∈ U → ∀ (ε : ℝ), 0 ≤ ε →
      (∀ j ≤ k, Real.sqrt (normSq0S R₀ x (2 + j) (iterCov R₀ 2 T j x)) ≤ ε) →
      ∀ j ≤ k, Real.sqrt (normSq0S R₁ x (2 + j) (iterCov R₁ 2 T j x)) ≤ C * ε := by
  classical
  let L : ℝ := (2 * A) ^ (2 + k) * D
  have hL : 0 ≤ L := mul_nonneg (pow_nonneg (by linarith) _) hD
  let C0 : ℝ := Real.sqrt (Module.finrank ℝ E) * 2
  let B : ℕ → ℝ := fun c => inverseContractionRecurrenceConstant C0
    (|(1 / 2 : ℝ)| + |(1 / 2 : ℝ)| + |-(1 / 2 : ℝ)|) L c
  let Cr : ℝ := iteratedRecurrenceConstant B k 2
  have hCr : 0 ≤ Cr := iterated_recurrence_constant_nonneg
    (fun c => inverse_contraction_recurrence_constant_nonneg hL c) _ _
  let C : ℝ := A ^ (2 + k) * (1 + (k : ℝ) * Cr)
  have hC : 0 < C := mul_pos (pow_pos (by linarith) _) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro T x hx ε hε hT j hj
  have hsqrt : ∀ i ≤ k, Real.sqrt (A ^ (2 + i)) ≤ A ^ (2 + k) := by
    intro i hi
    exact (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hA))).trans
      (pow_le_pow_right₀ hA (by omega))
  have hbase : ∀ i ≤ k,
      Real.sqrt (normSq0S R₁ x (2 + i) (iterCov R₀ 2 T i x)) ≤
        A ^ (2 + k) * ε := by
    intro i hi
    exact (sqrt_normSq0S_le_of_metric_equiv R₀ R₁ x (2 + i) hA (heq x hx)
      (iterCov R₀ 2 T i x)).trans
      (mul_le_mul (hsqrt i hi) (hT i hi) (Real.sqrt_nonneg _) (by positivity))
  by_cases hj0 : j = 0
  · subst j
    have hb := hbase 0 (Nat.zero_le k)
    change Real.sqrt (normSq0S R₁ x 2 (T x)) ≤ _ at hb ⊢
    have hcoeff : A ^ (2 + k) ≤ C := by
      dsimp [C]
      have hp : 0 ≤ A ^ (2 + k) := pow_nonneg (by linarith) _
      nlinarith [mul_nonneg hp (mul_nonneg (Nat.cast_nonneg k) hCr)]
    exact hb.trans (mul_le_mul_of_nonneg_right hcoeff hε)
  let e₀ := trivializationAt E (TangentSpace I : M → Type _) x
  obtain ⟨basisE, u', η, hu', hxu', hsub, hη0, hsmall, hnear, hON, hcomp, _⟩ :=
    exists_goodFrame_compBound (I := I) R₁ x
  let frame : Fin (Module.finrank ℝ E) → (y : M) → TangentSpace I y :=
    fun a y => e₀.localFrame basisE a y
  let W : Set M := u' ∩ U
  have hW : IsOpen W := hu'.inter hU
  have hxW : x ∈ W := ⟨hxu', hx⟩
  have hWsub : W ⊆ e₀.baseSet := fun _ hz => hsub hz.1
  let hframe : IsLocalFrameOn I E 1 frame W :=
    (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hWsub
  have hframeS : ∀ a : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame a y)) W :=
    fun a => (frame_e_mdiffOn e₀ basisE a).mono hWsub
  have hchr₁ : ∀ a b c : Fin (Module.finrank ℝ E), ContMDiffOn I 𝓘(ℝ) ∞
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric R₁)
        frame hframe y a b c) W :=
    fun a b c => ((lcChrist_e_mdiffOn e₀ R₁ basisE a b c).mono hWsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric R₁)
        frame (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hWsub hz a b c)
  have hchr₀ : ∀ a b c : Fin (Module.finrank ℝ E), ContMDiffOn I 𝓘(ℝ) ∞
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric R₀)
        frame hframe y a b c) W :=
    fun a b c => ((lcChrist_e_mdiffOn e₀ R₀ basisE a b c).mono hWsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric R₀)
        frame (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hWsub hz a b c)
  have hGinv : ∀ z ∈ W, compL2 (ginvCompField e₀ R₁ basisE z) ≤ C0 := by
    intro z hz
    have hb := movingGinv_le e₀ R₁ R₁ basisE 1 zero_lt_one
      (fun v => by simp) η hη0 hsmall (fun a b => hnear z hz.1 a b)
    simpa only [C0, Fintype.card_fin, mul_one] using hb
  have hinv : ∀ z ∈ W, ∀ c e : Fin (Module.finrank ℝ E),
      (∑ l, frameComp0S (metricTensorField R₁) frame z (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField e₀ R₁ basisE z (Fin.snoc (fun _ : Fin 1 => e) l)) =
          if c = e then 1 else 0 := fun z hz c e => ginv_hinv e₀ R₁ basisE (hWsub hz) c e
  have hmetric : ∀ z ∈ W, ∀ i, 1 ≤ i → i ≤ k →
      compL2 (iterCovComp frame
        (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric R₀) frame hframe y)
        (frameComp0S (metricTensorField R₁) frame) i z) ≤ L * 1 := by
    intro z hz i _ hi
    have ht := compL2_tower_le R₀ R₁ (metricTensorField R₁) frame hframe hW hz
      (fun s V => hcomp z (hWsub hz) hz.1 s V) i
    have hc := sqrt_normSq0S_le_of_metric_equiv R₀ R₁ z (2 + i) hA (heq z hz.2)
      (iterCov R₀ 2 (metricTensorField R₁) i z)
    have hp : Real.sqrt (A ^ (2 + i)) ≤ A ^ (2 + i) :=
      Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hA))
    calc
      _ ≤ 2 ^ (2 + i) * (Real.sqrt (A ^ (2 + i)) * D) :=
        ht.trans (mul_le_mul_of_nonneg_left
          (hc.trans (mul_le_mul_of_nonneg_left (hjet i hi z hz.2) (Real.sqrt_nonneg _)))
          (by positivity))
      _ ≤ 2 ^ (2 + i) * (A ^ (2 + i) * D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hD) (by positivity)
      _ = (2 * A) ^ (2 + i) * D := by rw [mul_pow]; ring
      _ ≤ (2 * A) ^ (2 + k) * D :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by omega)) hD
      _ = L * 1 := by simp [L]
  have hc := iterated_covariant_derivative_comparison_bound hW R₁ R₀ frame hframe
    hframeS hchr₁ hchr₀ (fun v => (gCompField_mdiffOn e₀ R₁ basisE v).mono hWsub)
    (frameComp0S T frame) (fun v => (tensorComp_mdiffOn e₀ T basisE v).mono hWsub)
    (ginvCompField e₀ R₁ basisE) hinv C0 L 1 hL zero_le_one le_rfl hGinv k hmetric
  have hON' : ∀ a b, R₁.inner x (hframe.toBasisAt hxW a) (hframe.toBasisAt hxW b) =
      if a = b then 1 else 0 := by
    intro a b
    simpa only [IsLocalFrameOn.toBasisAt_coe] using hON a b
  have hf := sqrt_norm_sq_iter_cov_le_of_component_bound hW R₁ R₀ T frame hframe hxW
    (metricInverseInBasis_of_orthonormal R₁ (hframe.toBasisAt hxW) hON') 1 Cr j
    (by simpa only [Cr, B] using hc x hxW j (Nat.pos_of_ne_zero hj0) hj)
  have hsum : (∑ i ∈ Finset.range j,
      Real.sqrt (normSq0S R₁ x (2 + i) (iterCov R₀ 2 T i x))) ≤
      (k : ℝ) * (A ^ (2 + k) * ε) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range j, A ^ (2 + k) * ε :=
        Finset.sum_le_sum fun i hi => hbase i (le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hj)
      _ = (j : ℝ) * (A ^ (2 + k) * ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
  simp only [one_mul] at hf
  exact hf.trans (by dsimp [C]; nlinarith [hbase j hj, mul_le_mul_of_nonneg_left hsum hCr])

private theorem exists_fixed_jet_bound (R₀ R₁ : SmoothRiemannianMetric I M)
    {K : Set M} (hK : IsCompact K) (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ j ≤ k, ∀ x ∈ K,
      Real.sqrt (normSq0S R₀ x (2 + j)
        (iterCov R₀ 2 (metricTensorField R₁) j x)) ≤ D := by
  classical
  have hb := fun j => DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_on_compact
    R₀ (metricTensorField R₁) j hK
  choose D hDpos hD using hb
  have hn : (Finset.range (k + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩
  refine ⟨(Finset.range (k + 1)).sup' hn D,
    (hDpos 0).trans_le (Finset.le_sup' D (Finset.mem_range.mpr (Nat.zero_lt_succ k))), ?_⟩
  intro j hj x hx
  exact (hD j x hx).trans (Finset.le_sup' D (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

private theorem metricDerivNorm_eq_tensor_norm
    (g h R : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    metricDerivNorm j g h R x = Real.sqrt (normSq0S R x (2 + j)
      (iterCov R 2 (metricTensorField g - metricTensorField h) j x)) := by
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis R x
  have hinv : MetricInverseInBasis R x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have hb := metricInverseInBasis_of_orthonormal R basis hON
    intro i l
    simpa [identityInvMetric, diagonalInvMetric] using hb i l
  exact metricDerivNorm_eq_iterCov g h R j basis hinv

theorem exists_metricDerivENormSupOn_reference_comparison
    (R₀ R₁ : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g h : SmoothRiemannianMetric I M,
      metricDerivENormSupOn K k g h R₁ ≤
        ENNReal.ofReal C * metricDerivENormSupOn K k g h R₀ := by
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨A, hA, heq⟩ := equivOn_compact hK' R₀ R₁
  obtain ⟨D, hD, hjet⟩ := exists_fixed_jet_bound R₀ R₁ hK' k
  obtain ⟨C, hC, hbound⟩ := exists_tensor_bound_on_open R₀ R₁ isOpen_interior k A D hA hD.le
    (fun x hx => heq x (interior_subset hx))
    (fun j hj x hx => hjet j hj x (interior_subset hx))
  refine ⟨C, hC, ?_⟩
  intro g h
  let N := metricDerivENormSupOn K k g h R₀
  have hN : N ≠ ⊤ := by
    rw [show N = metricDerivENormSupOn K k g h R₀ from rfl,
      metricDerivENormSupOn_eq_ofReal_of_isCompact hK]
    exact ENNReal.ofReal_ne_top
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj x hx
  have hT : ∀ i ≤ k, Real.sqrt (normSq0S R₀ x (2 + i)
      (iterCov R₀ 2 (metricTensorField g - metricTensorField h) i x)) ≤ N.toReal := by
    intro i hi
    rw [← metricDerivNorm_eq_tensor_norm g h R₀ i x]
    exact (ENNReal.ofReal_le_iff_le_toReal hN).mp
      (ofReal_metricDerivNorm_le_sup K k g h R₀ hi hx)
  have hb := hbound (metricTensorField g - metricTensorField h) x (hKK' hx)
    N.toReal ENNReal.toReal_nonneg hT j hj
  rw [← metricDerivNorm_eq_tensor_norm g h R₁ j x] at hb
  calc
    ENNReal.ofReal _ ≤ ENNReal.ofReal (C * N.toReal) := ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal C * N := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hN]

end DifferentialGeometry.Geometry.Metric
