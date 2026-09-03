import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.ApplicationJetWindow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.PerOrderEnvelopes

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem iteratedCovGrad2_jet_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ n m : ℕ, n + 1 ≤ m → ∀ U : SmoothCcTensor g 0 s,
        ∑ l ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 0 (s + 2) l
              (iteratedCovGrad (I := I) g 0 s 2 U)‖ ≤
          C m * ‖ccTensorToHs (I := I) (M := M) g s (m : ℝ) U‖ := by
  classical
  choose C hC hjet using fun m : ℕ => hsJet_le (I := I) (M := M) g s m
  refine ⟨C, hC, ?_⟩
  intro n m hnm U
  refine le_trans ?_ (hjet m U)
  calc
    ∑ l ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g 0 (s + 2) l
          (iteratedCovGrad (I := I) g 0 s 2 U)‖
        = ∑ l ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 0 s (2 + l) U‖ :=
      Finset.sum_congr rfl
        (fun l _ => iteratedCovGrad_comp_norm (I := I) (M := M) g s 2 l U)
    _ ≤ ∑ i ∈ Finset.range (2 + n),
            ‖iteratedCovGrad (I := I) g 0 s i U‖ := by
      rw [Finset.sum_range_add
        (fun i => ‖iteratedCovGrad (I := I) g 0 s i U‖) 2 n]
      exact le_add_of_nonneg_left
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    _ ≤ ∑ i ∈ Finset.range (m + 1),
            ‖iteratedCovGrad (I := I) g 0 s i U‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega))
        (fun _ _ _ => norm_nonneg _)

theorem operatorFieldApplication_split_env
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (k : ℕ) (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 s)
        (A B Λ : ℝ), 0 ≤ A → 0 ≤ B → 0 ≤ Λ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
              (Φ.toSection x) ≤ A ^ 2) →
        (∑ i ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2) ≤ B ^ 2 →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
              ((iteratedCovGrad (I := I) g 0 s 2 U).toSection x) ≤ Λ ^ 2) →
        ‖ccTensorToHs (I := I) (M := M) g c ((k + 1 : ℕ) : ℝ)
            (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ
              (iteratedCovGrad (I := I) g 0 s 2 U))‖ ≤
          C k * (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 3 : ℕ) : ℝ) U‖ +
            B * Λ) := by
  classical
  choose Csp hCsp hsp using fun k : ℕ => hs_le_jet (I := I) (M := M) g c (k + 1)
  obtain ⟨Cin, hCin, hin⟩ := iteratedCovGrad2_jet_le (I := I) (M := M) g s
  choose Cg hCg hgrid using fun j : ℕ =>
    exists_integrated_iteratedCovGrad_diagonalProductGrid_twoTerm_rs_le
      (I := I) (M := M) g (s + 2) 0 c (s + 2) j
  refine ⟨fun k => Csp k *
    (∑ j ∈ Finset.range (k + 2),
      Real.sqrt (operatorFieldApplicationGdiag (E := E) j * Cg j)) * (Cin (k + 3) + 1), ?_, ?_⟩
  · intro k
    refine mul_nonneg (mul_nonneg (hCsp k)
      (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))) ?_
    linarith only [hCin (k + 3)]
  intro k Φ U A B Λ hA hB hΛ hΦsup hΦjet hWsup
  have hNnn : (0 : ℝ) ≤
      ‖ccTensorToHs (I := I) (M := M) g s ((k + 3 : ℕ) : ℝ) U‖ := norm_nonneg _
  have hWjet :
      ∑ l ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g 0 (s + 2) l
            (iteratedCovGrad (I := I) g 0 s 2 U)‖ ^ 2 ≤
        (Cin (k + 3) *
          ‖ccTensorToHs (I := I) (M := M) g s ((k + 3 : ℕ) : ℝ) U‖) ^ 2 := by
    refine (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (hin (k + 2) (k + 3) (by omega) U) 2
  set W : SmoothCcTensor g 0 (s + 2) :=
    iteratedCovGrad (I := I) g 0 s 2 U with hW_def
  set N : ℝ := ‖ccTensorToHs (I := I) (M := M) g s ((k + 3 : ℕ) : ℝ) U‖
    with hN_def
  have hXnn : (0 : ℝ) ≤ A * (Cin (k + 3) * N) + B * Λ :=
    add_nonneg (mul_nonneg hA (mul_nonneg (hCin (k + 3)) hNnn))
      (mul_nonneg hB hΛ)
  have hterm : ∀ j ∈ Finset.range (k + 2),
      ‖iteratedCovGrad (I := I) g 0 c j
          (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖ ≤
        Real.sqrt (operatorFieldApplicationGdiag (E := E) j * Cg j) *
          (A * (Cin (k + 3) * N) + B * Λ) := by
    intro j hj
    have hjk : j + 1 ≤ k + 2 := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    obtain ⟨hint, hbnd⟩ := hgrid j Φ W A Λ hA hΛ hΦsup hWsup
    have hΦj :
        ∑ i ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2 ≤ B ^ 2 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hjk) (fun _ _ _ => sq_nonneg _)) hΦjet
    have hWj :
        ∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 (s + 2) l W‖ ^ 2 ≤
          (Cin (k + 3) * N) ^ 2 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hjk) (fun _ _ _ => sq_nonneg _)) hWjet
    have hinner :
        Cg j * (Λ ^ 2 * ∑ i ∈ Finset.range (j + 1),
              ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2 +
            A ^ 2 * ∑ l ∈ Finset.range (j + 1),
              ‖iteratedCovGrad (I := I) g 0 (s + 2) l W‖ ^ 2) ≤
          Cg j * (A * (Cin (k + 3) * N) + B * Λ) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ (hCg j)
      have h1 := mul_le_mul_of_nonneg_left hΦj (sq_nonneg Λ)
      have h2 := mul_le_mul_of_nonneg_left hWj (sq_nonneg A)
      have hab : (0 : ℝ) ≤ (A * (Cin (k + 3) * N)) * (B * Λ) :=
        mul_nonneg (mul_nonneg hA (mul_nonneg (hCin (k + 3)) hNnn))
          (mul_nonneg hB hΛ)
      nlinarith only [h1, h2, hab]
    have hquad :
        ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖ ^ 2 ≤
          (operatorFieldApplicationGdiag (E := E) j * Cg j) *
            (A * (Cin (k + 3) * N) + B * Λ) ^ 2 := by
      refine le_trans ?_ (le_of_eq (by ring :
        operatorFieldApplicationGdiag (E := E) j * (Cg j * (A * (Cin (k + 3) * N) + B * Λ) ^ 2) =
          (operatorFieldApplicationGdiag (E := E) j * Cg j) *
            (A * (Cin (k + 3) * N) + B * Λ) ^ 2))
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (hbnd.trans hinner)
        (operatorFieldApplicationGdiag_nonneg (E := E) j))
      rw [← MeasureTheory.integral_const_mul]
      exact normSq_le_integral_of_pointwise_fiberNormSq_le_rs
        (I := I) (M := M) g 0 (c + j) _ _ (hint.const_mul _)
        (fun x => operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le
          (I := I) (M := M) g (s + 2) c Φ W j x)
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) hXnn)
    rw [mul_pow, Real.sq_sqrt
      (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) j) (hCg j))]
    exact hquad
  have hsum :
      ∑ j ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖ ≤
        (∑ j ∈ Finset.range (k + 2),
          Real.sqrt (operatorFieldApplicationGdiag (E := E) j * Cg j)) *
          (A * (Cin (k + 3) * N) + B * Λ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hspY :
      ‖ccTensorToHs (I := I) (M := M) g c ((k + 1 : ℕ) : ℝ)
          (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖ ≤
        Csp k * ∑ j ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖ := by
    have h := hsp k (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)
    rw [show k + 1 + 1 = k + 2 from by omega] at h
    exact h
  have hSnn : (0 : ℝ) ≤
      ∑ j ∈ Finset.range (k + 2),
        Real.sqrt (operatorFieldApplicationGdiag (E := E) j * Cg j) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hfin :
      (∑ j ∈ Finset.range (k + 2),
          Real.sqrt (operatorFieldApplicationGdiag (E := E) j * Cg j)) *
        (A * (Cin (k + 3) * N) + B * Λ) ≤
      (∑ j ∈ Finset.range (k + 2),
          Real.sqrt (operatorFieldApplicationGdiag (E := E) j * Cg j)) *
        ((Cin (k + 3) + 1) * (A * N + B * Λ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hSnn
    nlinarith only [mul_nonneg hA hNnn,
      mul_nonneg (hCin (k + 3)) (mul_nonneg hB hΛ)]
  calc
    ‖ccTensorToHs (I := I) (M := M) g c ((k + 1 : ℕ) : ℝ)
        (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖
        ≤ Csp k * ∑ j ∈ Finset.range (k + 2),
            ‖iteratedCovGrad (I := I) g 0 c j
              (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖ := hspY
    _ ≤ Csp k * ((∑ j ∈ Finset.range (k + 2),
          Real.sqrt (operatorFieldApplicationGdiag (E := E) j * Cg j)) *
        (A * (Cin (k + 3) * N) + B * Λ)) :=
      mul_le_mul_of_nonneg_left hsum (hCsp k)
    _ ≤ Csp k * ((∑ j ∈ Finset.range (k + 2),
          Real.sqrt (operatorFieldApplicationGdiag (E := E) j * Cg j)) *
        ((Cin (k + 3) + 1) * (A * N + B * Λ))) :=
      mul_le_mul_of_nonneg_left hfin (hCsp k)
    _ = Csp k * (∑ j ∈ Finset.range (k + 2),
          Real.sqrt (operatorFieldApplicationGdiag (E := E) j * Cg j)) * (Cin (k + 3) + 1) *
        (A * N + B * Λ) := by ring

theorem operatorFieldApplication_split_hs
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (k : ℕ) (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 s)
        (A B : ℝ), 0 ≤ A → 0 ≤ B →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
              (Φ.toSection x) ≤ A ^ 2) →
        (∑ i ∈ Finset.range (k + 4),
          ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2) ≤ B ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g c ((k + 3 : ℕ) : ℝ)
            (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ
              (iteratedCovGrad (I := I) g 0 s 2 U))‖ ≤
          C k * (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
            B * ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) := by
  classical
  obtain ⟨C0, hC0, hsplit⟩ := operatorFieldApplication_split_env (I := I) (M := M) g s c
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.Analysis.Sobolev.exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 (s + 2)
  obtain ⟨Cj, hCj, hjet⟩ := iteratedCovGrad2_jet_le (I := I) (M := M) g s
  refine ⟨fun k => C0 (k + 2) * (Cpt * Cj (k + 4) + 1), ?_, ?_⟩
  · intro k
    exact mul_nonneg (hC0 (k + 2))
      (by linarith only [mul_nonneg hCpt (hCj (k + 4))])
  intro k Φ U A B hA hB hΦsup hΦjet
  have hN4 : (0 : ℝ) ≤
      ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖ := norm_nonneg _
  have hN5 : (0 : ℝ) ≤
      ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ := norm_nonneg _
  have hΛnn : (0 : ℝ) ≤
      Cpt * Cj (k + 4) *
        ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖ :=
    mul_nonneg (mul_nonneg hCpt (hCj (k + 4))) hN4
  have hWsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
          ((iteratedCovGrad (I := I) g 0 s 2 U).toSection x) ≤
        (Cpt * Cj (k + 4) *
          ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ^ 2 := by
    intro x
    have h := hpt (iteratedCovGrad (I := I) g 0 s 2 U) x
    rw [show Module.finrank ℝ E / 2 + 2 = 3 by rw [hDim]] at h
    refine h.trans ?_
    have hsq :
        ∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 (s + 2) i
              (iteratedCovGrad (I := I) g 0 s 2 U)‖ ^ 2 ≤
          (Cj (k + 4) *
            ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ^ 2 :=
      (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
          (hjet 3 (k + 4) (by omega) U) 2)
    calc
      Cpt ^ 2 * ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 2) i
            (iteratedCovGrad (I := I) g 0 s 2 U)‖ ^ 2
          ≤ Cpt ^ 2 * (Cj (k + 4) *
              ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg Cpt)
      _ = (Cpt * Cj (k + 4) *
            ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ^ 2 := by
        ring
  have hΦjet' :
      ∑ i ∈ Finset.range (k + 2 + 2),
        ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2 ≤ B ^ 2 := by
    rw [show k + 2 + 2 = k + 4 from by omega]
    exact hΦjet
  have hmain := hsplit (k + 2) Φ U A B
    (Cpt * Cj (k + 4) *
      ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖)
    hA hB hΛnn hΦsup hΦjet' hWsup
  rw [show k + 2 + 1 = k + 3 from by omega,
    show k + 2 + 3 = k + 5 from by omega] at hmain
  refine hmain.trans ?_
  have hstep :
      A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
          B * (Cpt * Cj (k + 4) *
            ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ≤
        (Cpt * Cj (k + 4) + 1) *
          (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
            B * ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) := by
    nlinarith only [mul_nonneg (mul_nonneg hCpt (hCj (k + 4)))
        (mul_nonneg hA hN5), mul_nonneg hB hN4]
  calc
    C0 (k + 2) *
        (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
          B * (Cpt * Cj (k + 4) *
            ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖))
        ≤ C0 (k + 2) * ((Cpt * Cj (k + 4) + 1) *
            (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
              B * ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖)) :=
      mul_le_mul_of_nonneg_left hstep (hC0 (k + 2))
    _ = C0 (k + 2) * (Cpt * Cj (k + 4) + 1) *
        (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
          B * ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) := by
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
