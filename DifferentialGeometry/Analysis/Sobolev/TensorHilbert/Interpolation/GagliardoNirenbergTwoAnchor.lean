import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.PointwiseBounds
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Integration.L2.FiniteProductHolderFiberNorm

noncomputable section


open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral

private lemma rpowFlip {X Y a b : ℝ} (hX : 0 ≤ X) (hb : 0 ≤ b) (hab : a * b = 1)
    (h : X ^ a ≤ Y) : X ≤ Y ^ b := by
  have h1 : (0 : ℝ) ≤ X ^ a := Real.rpow_nonneg hX a
  calc X = (X ^ a) ^ b := by rw [← Real.rpow_mul hX, hab, Real.rpow_one]
    _ ≤ Y ^ b := Real.rpow_le_rpow h1 h hb

section RealCore

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

private lemma gnMixCore (F : α → ℝ) (hFnn : ∀ x, 0 ≤ F x)
    {pA pB θ lam Λ R KA KB : ℝ}
    (hpA : 0 < pA) (hpB : 0 < pB)
    (hIA : MeasureTheory.Integrable (fun x => F x ^ pA) μ)
    (hIB : MeasureTheory.Integrable (fun x => F x ^ pB) μ)
    (hθ0 : 0 < θ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hmix : 1 / θ = lam * pA + (1 - lam) * pB)
    (hθpA : θ * pA ≤ 1) (hθpB : θ * pB ≤ 2)
    (hΛ : 0 ≤ Λ) (hR : 0 ≤ R) (hKA : 1 ≤ KA) (hKB : 1 ≤ KB)
    (hEA : ∫ x, F x ^ pA ∂μ ≤ KA ^ pA * R ^ (2 : ℝ))
    (hEB : ∫ x, F x ^ pB ∂μ ≤ KB ^ pB * Λ ^ (2 * (pB - 1)) * R ^ (2 : ℝ)) :
    (∫ x, F x ^ (1 / θ) ∂μ) ^ θ ≤
      KA * KB ^ (2 : ℝ) * Λ ^ (2 * (pB - 1) * (1 - lam) * θ) * R ^ (2 * θ) := by
  have hKA0 : (0 : ℝ) ≤ KA := le_trans zero_le_one hKA
  have hKB0 : (0 : ℝ) ≤ KB := le_trans zero_le_one hKB
  have hR2 : (0 : ℝ) ≤ R ^ (2 : ℝ) := Real.rpow_nonneg hR _
  have hΛe : (0 : ℝ) ≤ Λ ^ (2 * (pB - 1)) := Real.rpow_nonneg hΛ _
  have hlam1' : (0 : ℝ) ≤ 1 - lam := by linarith
  have hIAnn : 0 ≤ ∫ x, F x ^ pA ∂μ :=
    MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hFnn x) _)
  have hIBnn : 0 ≤ ∫ x, F x ^ pB ∂μ :=
    MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hFnn x) _)
  have hIθnn : 0 ≤ ∫ x, F x ^ (1 / θ) ∂μ :=
    MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hFnn x) _)
  have e3 : (R ^ (2 : ℝ)) ^ lam * (R ^ (2 : ℝ)) ^ (1 - lam) = R ^ (2 : ℝ) := by
    rw [← Real.rpow_add' hR2 (by intro hcon; linarith)]
    norm_num
  have key : ∫ x, F x ^ (1 / θ) ∂μ ≤
      KA ^ (pA * lam) * KB ^ (pB * (1 - lam)) * Λ ^ (2 * (pB - 1) * (1 - lam)) *
        R ^ (2 : ℝ) := by
    have h1 := lyapunov_pow_le (μ := μ) F (Filter.Eventually.of_forall hFnn) hpA hpB
      hlam0 hlam1 hmix hIA hIB
    have h2 : (∫ x, F x ^ pA ∂μ) ^ lam * (∫ x, F x ^ pB ∂μ) ^ (1 - lam) ≤
        (KA ^ pA * R ^ (2 : ℝ)) ^ lam *
          (KB ^ pB * Λ ^ (2 * (pB - 1)) * R ^ (2 : ℝ)) ^ (1 - lam) := by
      refine mul_le_mul (Real.rpow_le_rpow hIAnn hEA hlam0)
        (Real.rpow_le_rpow hIBnn hEB hlam1') (Real.rpow_nonneg hIBnn _)
        (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hKA0 _) hR2) _)
    have e1 : (KA ^ pA * R ^ (2 : ℝ)) ^ lam = KA ^ (pA * lam) * (R ^ (2 : ℝ)) ^ lam := by
      rw [Real.mul_rpow (Real.rpow_nonneg hKA0 _) hR2, ← Real.rpow_mul hKA0]
    have e2 : (KB ^ pB * Λ ^ (2 * (pB - 1)) * R ^ (2 : ℝ)) ^ (1 - lam) =
        KB ^ (pB * (1 - lam)) * Λ ^ (2 * (pB - 1) * (1 - lam)) *
          (R ^ (2 : ℝ)) ^ (1 - lam) := by
      rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hKB0 _) hΛe) hR2,
        Real.mul_rpow (Real.rpow_nonneg hKB0 _) hΛe, ← Real.rpow_mul hKB0,
        ← Real.rpow_mul hΛ]
    refine le_trans h1 (le_trans h2 (le_of_eq ?_))
    rw [e1, e2]
    calc KA ^ (pA * lam) * (R ^ (2 : ℝ)) ^ lam *
          (KB ^ (pB * (1 - lam)) * Λ ^ (2 * (pB - 1) * (1 - lam)) *
            (R ^ (2 : ℝ)) ^ (1 - lam))
        = KA ^ (pA * lam) * KB ^ (pB * (1 - lam)) * Λ ^ (2 * (pB - 1) * (1 - lam)) *
            ((R ^ (2 : ℝ)) ^ lam * (R ^ (2 : ℝ)) ^ (1 - lam)) := by ring
      _ = KA ^ (pA * lam) * KB ^ (pB * (1 - lam)) * Λ ^ (2 * (pB - 1) * (1 - lam)) *
            R ^ (2 : ℝ) := by rw [e3]
  have hZ0 : (0 : ℝ) ≤ KA ^ (pA * lam) * KB ^ (pB * (1 - lam)) *
      Λ ^ (2 * (pB - 1) * (1 - lam)) * R ^ (2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hKA0 _) (Real.rpow_nonneg hKB0 _))
      (Real.rpow_nonneg hΛ _)) hR2
  have h5 : (∫ x, F x ^ (1 / θ) ∂μ) ^ θ ≤
      (KA ^ (pA * lam) * KB ^ (pB * (1 - lam)) * Λ ^ (2 * (pB - 1) * (1 - lam)) *
        R ^ (2 : ℝ)) ^ θ := Real.rpow_le_rpow hIθnn key hθ0.le
  have h6 : (KA ^ (pA * lam) * KB ^ (pB * (1 - lam)) * Λ ^ (2 * (pB - 1) * (1 - lam)) *
        R ^ (2 : ℝ)) ^ θ =
      KA ^ (pA * lam * θ) * KB ^ (pB * (1 - lam) * θ) *
        Λ ^ (2 * (pB - 1) * (1 - lam) * θ) * R ^ (2 * θ) := by
    rw [Real.mul_rpow (mul_nonneg (mul_nonneg (Real.rpow_nonneg hKA0 _)
        (Real.rpow_nonneg hKB0 _)) (Real.rpow_nonneg hΛ _)) hR2,
      Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hKA0 _) (Real.rpow_nonneg hKB0 _))
        (Real.rpow_nonneg hΛ _),
      Real.mul_rpow (Real.rpow_nonneg hKA0 _) (Real.rpow_nonneg hKB0 _),
      ← Real.rpow_mul hKA0, ← Real.rpow_mul hKB0, ← Real.rpow_mul hΛ, ← Real.rpow_mul hR]
  rw [h6] at h5
  refine le_trans h5 ?_
  have hcA : KA ^ (pA * lam * θ) ≤ KA := by
    have hθpA0 : 0 ≤ θ * pA := mul_nonneg hθ0.le hpA.le
    have hexp : pA * lam * θ ≤ 1 := by
      calc
        pA * lam * θ = lam * (θ * pA) := by ring
        _ ≤ 1 * (θ * pA) := mul_le_mul_of_nonneg_right hlam1 hθpA0
        _ ≤ 1 := by simpa using hθpA
    calc KA ^ (pA * lam * θ) ≤ KA ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hKA hexp
      _ = KA := Real.rpow_one KA
  have hcB : KB ^ (pB * (1 - lam) * θ) ≤ KB ^ (2 : ℝ) := by
    have hθpB0 : 0 ≤ θ * pB := mul_nonneg hθ0.le hpB.le
    have h1mlam_le : 1 - lam ≤ 1 := by linarith only [hlam0]
    have hexp : pB * (1 - lam) * θ ≤ 2 := by
      calc
        pB * (1 - lam) * θ = (1 - lam) * (θ * pB) := by ring
        _ ≤ 1 * (θ * pB) := mul_le_mul_of_nonneg_right h1mlam_le hθpB0
        _ ≤ 2 := by simpa using hθpB
    exact Real.rpow_le_rpow_of_exponent_le hKB hexp
  have hrest : (0 : ℝ) ≤ Λ ^ (2 * (pB - 1) * (1 - lam) * θ) * R ^ (2 * θ) :=
    mul_nonneg (Real.rpow_nonneg hΛ _) (Real.rpow_nonneg hR _)
  calc KA ^ (pA * lam * θ) * KB ^ (pB * (1 - lam) * θ) *
        Λ ^ (2 * (pB - 1) * (1 - lam) * θ) * R ^ (2 * θ)
      = (KA ^ (pA * lam * θ) * KB ^ (pB * (1 - lam) * θ)) *
          (Λ ^ (2 * (pB - 1) * (1 - lam) * θ) * R ^ (2 * θ)) := by ring
    _ ≤ (KA * KB ^ (2 : ℝ)) *
          (Λ ^ (2 * (pB - 1) * (1 - lam) * θ) * R ^ (2 * θ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcA hcB (Real.rpow_nonneg hKB0 _) hKA0) hrest
    _ = KA * KB ^ (2 : ℝ) * Λ ^ (2 * (pB - 1) * (1 - lam) * θ) * R ^ (2 * θ) := by ring

end RealCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem gnFam (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ A : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧
      ∀ (u : SmoothCcTensor g₀ r s) (Λ : ℝ), 0 ≤ Λ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (u.toSection x) ≤ Λ ^ 2) →
        ∀ k j : ℕ, 0 < j → j < k →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
                  ((iteratedCovGrad (I := I) g₀ r s j u).toSection x)) ^ ((k : ℝ) / (j : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (k : ℝ)) ≤
            A k * Λ ^ (2 * (1 - (j : ℝ) / (k : ℝ))) *
              tensorL2Norm (I := I) g₀ r (s + k)
                (iteratedCovGrad (I := I) g₀ r s k u).toFun ^ (2 * (j : ℝ) / (k : ℝ)) := by
  classical
  have h : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : SmoothCcTensor g₀ r s) (Λ : ℝ), 0 ≤ Λ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (u.toSection x) ≤ Λ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
                  ((iteratedCovGrad (I := I) g₀ r s j u).toSection x)) ^ ((k : ℝ) / (j : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (k : ℝ)) ≤
            C * Λ ^ (2 * (1 - (j : ℝ) / (k : ℝ))) *
              tensorL2Norm (I := I) g₀ r (s + k)
                (iteratedCovGrad (I := I) g₀ r s k u).toFun ^ (2 * (j : ℝ) / (k : ℝ)) := by
    intro k
    by_cases hk : 1 ≤ k
    · exact exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ r s k hk
    · exact ⟨0, le_refl 0, fun u Λ hΛ hsup j hj0 hjk => absurd hjk (by omega)⟩
  choose A hA0 hA using h
  exact ⟨A, hA0, fun u Λ hΛ hsup k j hj0 hjk => hA k u Λ hΛ hsup j hj0 hjk⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma gagliardoNirenbergTwoAnchor_EA
    (g₀ : SmoothRiemannianMetric I M) (F : M → ℝ) (hFnn : ∀ x, 0 ≤ F x)
    (pA tA R Λ₀ : ℝ) (A : ℕ → ℝ) (n : ℕ)
    (hpApos : 0 < pA) (htApA : tA * pA = 1) (htA1 : tA ≤ 1) (hRnn : 0 ≤ R)
    (hΛ₀0 : 0 ≤ Λ₀) (hΛ₀1 : Λ₀ ≤ 1) (hA0 : 0 ≤ A (1 + n))
    (hAraw : (∫ x, F x ^ pA ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ tA ≤
      A (1 + n) * Λ₀ ^ (2 * (1 - tA)) * R ^ (2 * tA)) :
    (∫ x, F x ^ pA ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      max 1 (A (1 + n)) ^ pA * R ^ (2 : ℝ) := by
  have hΛ₀e : Λ₀ ^ (2 * (1 - tA)) ≤ 1 := Real.rpow_le_one hΛ₀0 hΛ₀1 (by nlinarith)
  have hEA1 : (∫ x, F x ^ pA ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ tA ≤
      max 1 (A (1 + n)) * R ^ (2 * tA) := by
    refine le_trans hAraw ?_
    have hstep : A (1 + n) * Λ₀ ^ (2 * (1 - tA)) * R ^ (2 * tA) ≤
        A (1 + n) * 1 * R ^ (2 * tA) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ₀e hA0)
        (Real.rpow_nonneg hRnn _)
    refine le_trans hstep ?_
    rw [mul_one]
    exact mul_le_mul_of_nonneg_right (le_max_right 1 (A (1 + n))) (Real.rpow_nonneg hRnn _)
  have hX : 0 ≤ ∫ x, F x ^ pA ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hFnn x) _)
  refine le_trans (rpowFlip hX hpApos.le htApA hEA1) (le_of_eq ?_)
  rw [Real.mul_rpow (le_trans zero_le_one (le_max_left _ _)) (Real.rpow_nonneg hRnn _),
    ← Real.rpow_mul hRnn, show (2 : ℝ) * tA * pA = 2 by rw [mul_assoc, htApA, mul_one]]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma gagliardoNirenbergTwoAnchor_EB
    (g₀ : SmoothRiemannianMetric I M) (F : M → ℝ) (hFnn : ∀ x, 0 ≤ F x)
    (pB tB R Λ₁ : ℝ) (B : ℕ → ℝ) (n : ℕ)
    (hpBpos : 0 < pB) (htBpB : tB * pB = 1) (hRnn : 0 ≤ R) (hΛ₁0 : 0 ≤ Λ₁)
    (hBraw : (∫ x, F x ^ pB ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ tB ≤
      B n * Λ₁ ^ (2 * (1 - tB)) * R ^ (2 * tB)) :
    (∫ x, F x ^ pB ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      max 1 (B n) ^ pB * Λ₁ ^ (2 * (pB - 1)) * R ^ (2 : ℝ) := by
  have hEB1 : (∫ x, F x ^ pB ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ tB ≤
      max 1 (B n) * Λ₁ ^ (2 * (1 - tB)) * R ^ (2 * tB) := by
    refine le_trans hBraw ?_
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 (B n)) (Real.rpow_nonneg hΛ₁0 _))
      (Real.rpow_nonneg hRnn _)
  have hX : 0 ≤ ∫ x, F x ^ pB ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hFnn x) _)
  refine le_trans (rpowFlip hX hpBpos.le htBpB hEB1) (le_of_eq ?_)
  rw [Real.mul_rpow (mul_nonneg (le_trans zero_le_one (le_max_left _ _))
        (Real.rpow_nonneg hΛ₁0 _)) (Real.rpow_nonneg hRnn _),
      Real.mul_rpow (le_trans zero_le_one (le_max_left _ _)) (Real.rpow_nonneg hΛ₁0 _),
      ← Real.rpow_mul hΛ₁0, ← Real.rpow_mul hRnn,
      show (2 : ℝ) * tB * pB = 2 by rw [mul_assoc, htBpB, mul_one],
      show (2 : ℝ) * (1 - tB) * pB = 2 * (pB - 1) by
        nlinarith only [htBpB]]

theorem gagliardoNirenbergTwoAnchor (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ (Ψ : SmoothCcTensor g₀ r s) {Λ₀ Λ₁ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 → 0 ≤ Λ₁ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Ψ.toSection x) ≤ Λ₀ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + 1) x
            ((iteratedCovGrad (I := I) g₀ r s 1 Ψ).toSection x) ≤ Λ₁ ^ 2) →
        ∀ m c : ℕ, 2 ≤ c → c < m → ∀ θ : ℝ,
          ((c : ℝ) - 1) / ((m : ℝ) - 1) ≤ θ → θ ≤ (c : ℝ) / (m : ℝ) →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ r (s + c) x
                  ((iteratedCovGrad (I := I) g₀ r s c Ψ).toSection x)) ^ (1 / θ)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ θ ≤
            C m * Λ₁ ^ (2 * ((c : ℝ) - θ * (m : ℝ))) *
              ‖iteratedCovGrad (I := I) g₀ r s m Ψ‖ ^ (2 * θ) := by
  classical
  obtain ⟨A, hA0, hA⟩ := gnFam (I := I) (M := M) g₀ r s
  obtain ⟨B, hB0, hB⟩ := gnFam (I := I) (M := M) g₀ r (s + 1)
  refine ⟨fun m => max 1 (A m) * max 1 (B (m - 1)) ^ (2 : ℝ), fun m => ?_, ?_⟩
  · exact mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  intro Ψ Λ₀ Λ₁ hΛ₀0 hΛ₀1 hΛ₁0 hsup0 hsup1 m c hc2 hcm θ hθlo hθhi
  obtain ⟨d, rfl⟩ : ∃ d, c = 1 + d := ⟨c - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = 1 + n := ⟨m - 1, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hdn : d < n := by omega
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hdnR : (d : ℝ) < (n : ℝ) := by exact_mod_cast hdn
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hd1R
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans hdpos hdnR
  have hcast : ∀ k : ℕ, ((1 + k : ℕ) : ℝ) = 1 + (k : ℝ) := by intro k; push_cast; ring
  rw [hcast d, hcast n] at hθlo hθhi ⊢
  rw [show (1 + (d : ℝ)) - 1 = (d : ℝ) by ring, show (1 + (n : ℝ)) - 1 = (n : ℝ) by ring]
    at hθlo
  obtain ⟨F, hFapp⟩ : ∃ F : M → ℝ, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + (1 + d)) x
        ((iteratedCovGrad (I := I) g₀ r s (1 + d) Ψ).toSection x) = F x := ⟨_, fun _ => rfl⟩
  have hAraw := hA Ψ Λ₀ hΛ₀0 hsup0 (1 + n) (1 + d) (by omega) (by omega)
  have hBraw := hB (iteratedCovGrad (I := I) g₀ r s 1 Ψ) Λ₁ hΛ₁0 hsup1 n d (by omega) (by omega)
  rw [hcast d, hcast n] at hAraw
  simp only [hFapp] at hAraw
  rw [← SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ r s (1 + n) Ψ), mul_div_assoc] at hAraw
  simp only [riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ r s 1 d Ψ] at hBraw
  simp only [hFapp] at hBraw
  rw [← SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ r (s + 1) n (iteratedCovGrad (I := I) g₀ r s 1 Ψ)),
    iteratedCovGrad_norm_comp (I := I) (M := M) g₀ r s 1 n Ψ, mul_div_assoc] at hBraw
  have hFnn : ∀ x, 0 ≤ F x := by
    intro x
    rw [← hFapp x]
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r (s + (1 + d)) x _
  have hFcont : Continuous F := by
    have hc := SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ r s (1 + d) Ψ)
    refine hc.congr (fun x => ?_)
    rw [← hFapp x, riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r
        (s + (1 + d)) x ((iteratedCovGrad (I := I) g₀ r s (1 + d) Ψ).toSection x),
      ← SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ r s (1 + d) Ψ) x]
  have : MeasureTheory.IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g₀
  have hint : ∀ p : ℝ, 0 ≤ p → MeasureTheory.Integrable (fun x => F x ^ p)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    intro p hp
    exact (hFcont.rpow_const (fun _ => Or.inr hp)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  set R : ℝ := ‖iteratedCovGrad (I := I) g₀ r s (1 + n) Ψ‖ with hRdef
  set tA : ℝ := (1 + (d : ℝ)) / (1 + (n : ℝ)) with htAdef
  set pA : ℝ := (1 + (n : ℝ)) / (1 + (d : ℝ)) with hpAdef
  set tB : ℝ := (d : ℝ) / (n : ℝ) with htBdef
  set pB : ℝ := (n : ℝ) / (d : ℝ) with hpBdef
  have hRnn : (0 : ℝ) ≤ R := norm_nonneg _
  have h1dpos : (0 : ℝ) < 1 + (d : ℝ) := by linarith
  have h1npos : (0 : ℝ) < 1 + (n : ℝ) := by linarith
  have hpApos : 0 < pA := by rw [hpAdef]; exact div_pos h1npos h1dpos
  have htApos : 0 < tA := by rw [htAdef]; exact div_pos h1dpos h1npos
  have hpBpos : 0 < pB := by rw [hpBdef]; exact div_pos hnpos hdpos
  have htBpos : 0 < tB := by rw [htBdef]; exact div_pos hdpos hnpos
  have htApA : tA * pA = 1 := by rw [htAdef, hpAdef]; field_simp
  have htBpB : tB * pB = 1 := by rw [htBdef, hpBdef]; field_simp
  have htA1 : tA ≤ 1 := by rw [htAdef, div_le_one h1npos]; linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le htBpos hθlo
  have hθpA : θ * pA ≤ 1 := by
    calc θ * pA ≤ tA * pA := mul_le_mul_of_nonneg_right hθhi hpApos.le
      _ = 1 := htApA
  have htApB : tA * pB ≤ 2 := by
    rw [htAdef, hpBdef, div_mul_div_comm, div_le_iff₀ (by positivity)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hd1R) hnpos.le]
  have hθpB : θ * pB ≤ 2 := by
    calc θ * pB ≤ tA * pB := mul_le_mul_of_nonneg_right hθhi hpBpos.le
      _ ≤ 2 := htApB
  have hpApB : pA < pB := by
    rw [hpAdef, hpBdef, div_lt_div_iff₀ h1dpos hdpos]
    nlinarith only [hdnR]
  have hden : 0 < pB - pA := by linarith
  have hden_ne : pB - pA ≠ 0 := ne_of_gt hden
  have hθ_ne : θ ≠ 0 := ne_of_gt hθ0
  have hinvA : pA ≤ 1 / θ := by
    rw [le_div_iff₀ hθ0]; nlinarith only [hθpA]
  have hinvB : 1 / θ ≤ pB := by
    rw [div_le_iff₀ hθ0]
    nlinarith only [mul_le_mul_of_nonneg_left hθlo hpBpos.le, htBpB]
  set lam : ℝ := (pB - 1 / θ) / (pB - pA) with hlamdef
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef]; exact div_nonneg (by linarith) hden.le
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one hden]; linarith
  have hmix : 1 / θ = lam * pA + (1 - lam) * pB := by
    rw [hlamdef]; field_simp; ring
  have hEA := gagliardoNirenbergTwoAnchor_EA (I := I) (M := M) g₀ F hFnn pA tA R Λ₀ A n
    hpApos htApA htA1 hRnn hΛ₀0 hΛ₀1 (hA0 (1 + n)) hAraw
  have hEB := gagliardoNirenbergTwoAnchor_EB (I := I) (M := M) g₀ F hFnn pB tB R Λ₁ B n
    hpBpos htBpB hRnn hΛ₁0 hBraw
  have hnd_ne : ((n : ℝ) - (d : ℝ)) ≠ 0 := ne_of_gt (by linarith)
  have hlam' : 1 - lam = (1 / θ - pA) / (pB - pA) := by
    rw [hlamdef]; field_simp; ring
  have hq1 : pB - pA = ((n : ℝ) - (d : ℝ)) / ((d : ℝ) * (1 + (d : ℝ))) := by
    rw [hpAdef, hpBdef]; field_simp; ring
  have hq2 : pB - 1 = ((n : ℝ) - (d : ℝ)) / (d : ℝ) := by
    rw [hpBdef]; field_simp
  have hq3 : 1 / θ - pA = ((1 + (d : ℝ)) - θ * (1 + (n : ℝ))) / (θ * (1 + (d : ℝ))) := by
    rw [hpAdef]; field_simp
  have hexp : 2 * (pB - 1) * (1 - lam) * θ = 2 * ((1 + (d : ℝ)) - θ * (1 + (n : ℝ))) := by
    rw [hlam', hq1, hq2, hq3]
    field_simp
  have hcore := gnMixCore (μ := riemannianVolumeMeasure (I := I) (M := M) g₀) F hFnn
    hpApos hpBpos (hint pA hpApos.le) (hint pB hpBpos.le) hθ0 hlam0 hlam1 hmix hθpA hθpB
    hΛ₁0 hRnn (le_max_left 1 (A (1 + n))) (le_max_left 1 (B n)) hEA hEB
  simp only [hFapp]
  rw [show (1 + n) - 1 = n from by omega, ← hexp]
  exact hcore

private lemma gnExpSum {ι : Type*} (s : Finset ι) (cf θ : ι → ℝ) (mR : ℝ)
    (hsum : ∑ j ∈ s, cf j = mR + 1) (hθ : ∑ j ∈ s, θ j = 1) :
    ∑ j ∈ s, 2 * (cf j - θ j * mR) = 2 := by
  have h : ∑ j ∈ s, (cf j - θ j * mR) = 1 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, hθ]
    ring
  rw [← Finset.mul_sum, h, mul_one]

private lemma gnFreeWt {ι : Type*} (s : Finset ι) (cf : ι → ℝ) (mR : ℝ)
    (hm1 : 1 < mR) (hcm : ∀ j ∈ s, cf j ≤ mR)
    (hQ : 2 ≤ (s.card : ℝ)) (hsum : ∑ j ∈ s, cf j = mR + 1) :
    ∃ θ : ι → ℝ, ∑ j ∈ s, θ j = 1 ∧
      ∀ j ∈ s, (cf j - 1) / (mR - 1) ≤ θ j ∧ θ j ≤ cf j / mR := by
  have hm0 : (0 : ℝ) < mR := lt_trans zero_lt_one hm1
  have hm10 : (0 : ℝ) < mR - 1 := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = (mR + 1 - (s.card : ℝ)) / (mR - 1) := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = (mR + 1) / mR := ⟨_, rfl⟩
  have hLsum : ∑ j ∈ s, (cf j - 1) / (mR - 1) = L := by
    rw [hLdef, ← Finset.sum_div, Finset.sum_sub_distrib, hsum, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  have hUsum : ∑ j ∈ s, cf j / mR = U := by
    rw [hUdef, ← Finset.sum_div, hsum]
  have hL1 : L ≤ 1 := by
    rw [hLdef, div_le_one hm10]; linarith
  have hU1 : (1 : ℝ) < U := by
    rw [hUdef, lt_div_iff₀ hm0]; linarith
  have hUL : (0 : ℝ) < U - L := by linarith
  obtain ⟨tt, httdef⟩ : ∃ tt : ℝ, tt = (1 - L) / (U - L) := ⟨_, rfl⟩
  have htt0 : (0 : ℝ) ≤ tt := by rw [httdef]; exact div_nonneg (by linarith) hUL.le
  have htt1 : tt ≤ 1 := by rw [httdef, div_le_one hUL]; linarith
  have httUL : tt * (U - L) = 1 - L := by
    rw [httdef]; exact div_mul_cancel₀ _ (ne_of_gt hUL)
  refine ⟨fun j => (1 - tt) * ((cf j - 1) / (mR - 1)) + tt * (cf j / mR), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hLsum, hUsum]
    linear_combination httUL
  · intro j hj
    have hcj := hcm j hj
    have hab : (cf j - 1) / (mR - 1) ≤ cf j / mR := by
      rw [div_le_div_iff₀ hm10 hm0]
      nlinarith
    refine ⟨by nlinarith only [mul_nonneg htt0 (sub_nonneg.mpr hab)], ?_⟩
    nlinarith only [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - tt) (sub_nonneg.mpr hab)]

theorem gnProdJet (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ (Ψ : SmoothCcTensor g₀ r s) {Λ₀ Λ₁ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 → 0 ≤ Λ₁ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Ψ.toSection x) ≤ Λ₀ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + 1) x
            ((iteratedCovGrad (I := I) g₀ r s 1 Ψ).toSection x) ≤ Λ₁ ^ 2) →
        ∀ (m N : ℕ) (c : Fin N → ℕ) (t : Finset (Fin N)),
          (∀ j ∈ t, 2 ≤ c j) → (∀ j, j ∉ t → c j = 0) → 2 ≤ t.card →
          (∑ j ∈ t, c j) = m + 1 →
          (∫ x, ∏ j : Fin N, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + c j) x
                  ((iteratedCovGrad (I := I) g₀ r s (c j) Ψ).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            K m * Λ₁ ^ 2 * ‖iteratedCovGrad (I := I) g₀ r s m Ψ‖ ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := gagliardoNirenbergTwoAnchor (I := I) (M := M) g₀ r s
  refine ⟨fun m => max 1 (C m) ^ (m + 1),
    fun m => pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _, ?_⟩
  intro Ψ Λ₀ Λ₁ hΛ₀0 hΛ₀1 hΛ₁0 hsup0 hsup1 m N c t hc2 hc0 hQ2 hsum
  have hcard : 2 * t.card ≤ m + 1 := by
    have h1 : ∑ _j ∈ t, 2 ≤ ∑ j ∈ t, c j := Finset.sum_le_sum hc2
    rw [Finset.sum_const, smul_eq_mul, hsum] at h1
    omega
  have hcltm : ∀ j ∈ t, c j < m := by
    intro j hj
    have h1 : c j + ∑ i ∈ t.erase j, c i = m + 1 := by
      rw [Finset.add_sum_erase _ _ hj]; exact hsum
    have h2 : ∑ _i ∈ t.erase j, 2 ≤ ∑ i ∈ t.erase j, c i :=
      Finset.sum_le_sum (fun i hi => hc2 i (Finset.mem_of_mem_erase hi))
    rw [Finset.sum_const, smul_eq_mul] at h2
    have h3 : (t.erase j).card = t.card - 1 := Finset.card_erase_of_mem hj
    omega
  have hm1 : 1 < m := by omega
  have hmR1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hmR0 : (0 : ℝ) < (m : ℝ) := lt_trans zero_lt_one hmR1
  have hcfsum : ∑ j ∈ t, ((c j : ℝ)) = (m : ℝ) + 1 := by
    rw [← Nat.cast_sum, hsum]; push_cast; ring
  obtain ⟨θ, hθsum, hθband⟩ := gnFreeWt t (fun j => (c j : ℝ)) (m : ℝ) hmR1
    (fun j hj => by exact_mod_cast (hcltm j hj).le)
    (by exact_mod_cast hQ2) hcfsum
  have hθpos : ∀ j ∈ t, 0 < θ j := by
    intro j hj
    have h2 : (2 : ℝ) ≤ (c j : ℝ) := by exact_mod_cast hc2 j hj
    have hlo := (hθband j hj).1
    have hpos : (0 : ℝ) < ((c j : ℝ) - 1) / ((m : ℝ) - 1) :=
      div_pos (by linarith) (by linarith)
    linarith
  have hαnn : ∀ j ∈ t, 0 ≤ 2 * ((c j : ℝ) - θ j * (m : ℝ)) := by
    intro j hj
    have hhi := (le_div_iff₀ hmR0).mp (hθband j hj).2
    linarith
  have hθ2nn : ∀ j ∈ t, 0 ≤ 2 * θ j := fun j hj => by have := hθpos j hj; linarith
  have hΛone : ∀ j ∈ (Finset.univ : Finset (Fin N)) \ t, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + c j) x
        ((iteratedCovGrad (I := I) g₀ r s (c j) Ψ).toSection x) ≤ 1 := by
    have hgen : ∀ k : ℕ, k = 0 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + k) x
          ((iteratedCovGrad (I := I) g₀ r s k Ψ).toSection x) ≤ 1 := by
      rintro k rfl x
      have h2 : Λ₀ ^ 2 ≤ 1 := pow_le_one₀ hΛ₀0 hΛ₀1
      simpa using le_trans (hsup0 x) h2
    exact fun j hj x => hgen (c j) (hc0 j (Finset.mem_sdiff.mp hj).2) x
  have hsd : (Finset.univ : Finset (Fin N)) \ ((Finset.univ : Finset (Fin N)) \ t) = t :=
    Finset.sdiff_sdiff_eq_self (Finset.subset_univ t)
  have hhold := holder_integral_prod_riemannianFiberNormSq_le_of_sup_bound
    (I := I) (M := M) g₀ (Finset.univ : Finset (Fin N))
    ((Finset.univ : Finset (Fin N)) \ t) Finset.sdiff_subset (fun _ => r) (fun j => s + c j)
    (fun j => iteratedCovGrad (I := I) g₀ r s (c j) Ψ) (fun _ => (1 : ℝ))
    (fun _ _ => zero_le_one) hΛone θ (by rw [hsd]; exact hθpos) (by rw [hsd]; exact hθsum)
  rw [hsd, Finset.prod_const_one, one_mul] at hhold
  refine le_trans hhold ?_
  have hfacnn : ∀ j ∈ t, (0 : ℝ) ≤
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + c j) x
          ((iteratedCovGrad (I := I) g₀ r s (c j) Ψ).toSection x) ^ (1 / θ j)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ θ j := fun j _ =>
    Real.rpow_nonneg (MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r (s + c j) x _) _)) _
  have hfac : ∀ j ∈ t,
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + c j) x
          ((iteratedCovGrad (I := I) g₀ r s (c j) Ψ).toSection x) ^ (1 / θ j)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ θ j ≤
        C m * Λ₁ ^ (2 * ((c j : ℝ) - θ j * (m : ℝ))) *
          ‖iteratedCovGrad (I := I) g₀ r s m Ψ‖ ^ (2 * θ j) := fun j hj =>
    hC Ψ hΛ₀0 hΛ₀1 hΛ₁0 hsup0 hsup1 m (c j) (hc2 j hj) (hcltm j hj) (θ j)
      (hθband j hj).1 (hθband j hj).2
  refine le_trans (Finset.prod_le_prod hfacnn hfac) ?_
  have hαsum : ∑ j ∈ t, 2 * ((c j : ℝ) - θ j * (m : ℝ)) = 2 :=
    gnExpSum t (fun j => (c j : ℝ)) θ (m : ℝ) hcfsum hθsum
  have hθ2sum : ∑ j ∈ t, 2 * θ j = 2 := by rw [← Finset.mul_sum, hθsum, mul_one]
  have hR0 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ r s m Ψ‖ := norm_nonneg _
  have hprodeq : ∏ j ∈ t, (C m * Λ₁ ^ (2 * ((c j : ℝ) - θ j * (m : ℝ))) *
        ‖iteratedCovGrad (I := I) g₀ r s m Ψ‖ ^ (2 * θ j)) =
      C m ^ t.card * Λ₁ ^ (2 : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ r s m Ψ‖ ^ (2 : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      ← Real.rpow_sum_of_nonneg hΛ₁0 hαnn, ← Real.rpow_sum_of_nonneg hR0 hθ2nn,
      hαsum, hθ2sum]
  have hrp : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ 2 := by
    intro y; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hprodeq, hrp, hrp]
  have hCle : C m ^ t.card ≤ max 1 (C m) ^ (m + 1) :=
    le_trans (pow_le_pow_left₀ (hC0 m) (le_max_right _ _) _)
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCle (sq_nonneg Λ₁)) (sq_nonneg _)

end DifferentialGeometry.Integral.Connection
