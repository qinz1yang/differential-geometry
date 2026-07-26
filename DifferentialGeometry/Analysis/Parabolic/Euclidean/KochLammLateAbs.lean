import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateShell

/-!
# Absolute-integral bounds for late Koch--Lamm shells

The full terminal potential requires summability of the integrals of the
integrand norm, not merely summability of the norms of shell integrals.  This
file proves the corresponding one-piece, finite-cover, and shell estimates.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Absolute integral of the kernel/source product on one far selected
terminal piece. -/
theorem klLatePiece_abs {T R k : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x c : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    {S : Set V} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖
      ∂klTailMeasure (V := V) R S) ≤
      Real.exp (-(k ^ 2) / 4) * (klLateTailC V * (A_q : ℝ)) := by
  let μ := klTailMeasure (V := V) R S
  have hkMem : MemLp (klTermKernel (R ^ 2) x)
      (ENNReal.ofReal (klQDual V)) μ :=
    (klTermKernel_memLp (V := V) (sq_pos_of_pos hR) x).mono_measure
      (klTailTerm_le (V := V) R S)
  have hfMem : MemLp f (ENNReal.ofReal (klQReal V)) μ := by
    simpa only [klQReal_ofReal] using
      (klPieceSrc_mem (V := V) h c hR hRT hS)
  have hhold :
      (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖ ∂μ) ≤
        (klTermTailPow (V := V) R x S) ^ (1 / klQDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ klQReal V ∂μ) ^
            (1 / klQReal V) := by
    calc
      (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖ ∂μ) =
          ∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z‖ *
            ‖(fun w : ℝ × V ↦ ‖f w‖) z‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        simp only [norm_smul, norm_norm]
      _ ≤ (klTermTailPow (V := V) R x S) ^ (1 / klQDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ klQReal V ∂μ) ^
            (1 / klQReal V) := by
        simpa only [klTermTailPow, μ, norm_norm] using
          (integral_mul_norm_le_Lp_mul_Lq (klQ_holder (V := V))
            hkMem hfMem.norm)
  have hkern := klTailKern_fac (V := V) hR hk x hSm hfar
  have hsrc := klPieceSrc_fac (V := V) h c hR hRT hS
  have hs : 0 < klLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < klLateTailC V := by
    unfold klLateTailC klTailRoot
    exact Real.rpow_pos_of_pos (klTailCore_pos (V := V) one_pos) _
  calc
    (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖
        ∂klTailMeasure (V := V) R S) ≤
        (klTermTailPow (V := V) R x S) ^ (1 / klQDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ klQReal V
            ∂klTailMeasure (V := V) R S) ^ (1 / klQReal V) := hhold
    _ ≤ (Real.exp (-(k ^ 2) / 4) *
          (klLateTailC V * klLqScaleR (V := V) R)) *
        ((klLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) :=
      mul_le_mul hkern hsrc
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc.le hs.le))
    _ = Real.exp (-(k ^ 2) / 4) *
        (klLateTailC V * (A_q : ℝ)) := by
      calc
        Real.exp (-(k ^ 2) / 4) *
              (klLateTailC V * klLqScaleR (V := V) R) *
              ((klLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) =
            Real.exp (-(k ^ 2) / 4) * klLateTailC V *
              (klLqScaleR (V := V) R *
                (klLqScaleR (V := V) R)⁻¹) * (A_q : ℝ) := by ring
        _ = Real.exp (-(k ^ 2) / 4) *
            (klLateTailC V * (A_q : ℝ)) := by
          rw [mul_inv_cancel₀ hs.ne']
          ring

omit [CompleteSpace F] in
/-- Absolute-integral form of the arbitrary finite-cover estimate. -/
theorem klLateCover_abs {T R k : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    (s : Finset V) {S : Set V} (hSm : MeasurableSet S)
    (hcover : S ⊆ ⋃ c ∈ s, Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖
      ∂klTailMeasure (V := V) R S) ≤
      (s.card : ℝ) *
        (Real.exp (-(k ^ 2) / 4) * (klLateTailC V * (A_q : ℝ))) := by
  classical
  let D : ℝ :=
    Real.exp (-(k ^ 2) / 4) * (klLateTailC V * (A_q : ℝ))
  induction s using Finset.induction_on generalizing S with
  | empty =>
      have hS0 : S = ∅ := by
        simpa using hcover
      subst S
      simp [klTailMeasure]
  | @insert c s hc ih =>
      let S₀ : Set V := S ∩ Metric.ball c R
      let S₁ : Set V := S \ Metric.ball c R
      have hS₀m : MeasurableSet S₀ :=
        hSm.inter Metric.isOpen_ball.measurableSet
      have hS₁m : MeasurableSet S₁ :=
        hSm.diff Metric.isOpen_ball.measurableSet
      have hdisj : Disjoint S₀ S₁ := by
        apply Set.disjoint_left.mpr
        intro y hy₀ hy₁
        exact hy₁.2 hy₀.2
      have hsplit : S₀ ∪ S₁ = S := by
        ext y
        simp only [S₀, S₁, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
        tauto
      have hS₀ball : S₀ ⊆ Metric.ball c R := fun _ hy ↦ hy.2
      have hfar₀ : ∀ y ∈ S₀, k * R ≤ ‖x - y‖ :=
        fun y hy ↦ hfar y hy.1
      have hcover' : S ⊆
          Metric.ball c R ∪ ⋃ d ∈ s, Metric.ball d R := by
        simpa only [Finset.set_biUnion_insert] using hcover
      have hcover₁ : S₁ ⊆ ⋃ d ∈ s, Metric.ball d R := by
        intro y hy
        exact (hcover' hy.1).resolve_left hy.2
      have hfar₁ : ∀ y ∈ S₁, k * R ≤ ‖x - y‖ :=
        fun y hy ↦ hfar y hy.1
      have hint₀ := klLatePiece_int (V := V) h x c hR hRT hS₀ball
      have hint₁ :=
        (klLateCover_est (V := V) h x hR hk hRT s hS₁m hcover₁ hfar₁).1
      have hnorm₀ :
          (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖
            ∂klTailMeasure (V := V) R S₀) ≤ D := by
        simpa only [D] using
          (klLatePiece_abs (V := V) h x c hR hk hRT
            hS₀m hS₀ball hfar₀)
      have hnorm₁ := ih hS₁m hcover₁ hfar₁
      have hμ : klTailMeasure (V := V) R S =
          klTailMeasure (V := V) R S₀ + klTailMeasure (V := V) R S₁ := by
        rw [← hsplit]
        exact klTail_union (V := V) hdisj hS₁m
      rw [hμ, integral_add_measure hint₀.norm hint₁.norm]
      calc
        (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖
            ∂klTailMeasure (V := V) R S₀) +
            ∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖
              ∂klTailMeasure (V := V) R S₁ ≤
            D + (s.card : ℝ) * D := add_le_add hnorm₀ hnorm₁
        _ = ((insert c s).card : ℝ) * D := by
          rw [Finset.card_insert_of_notMem hc]
          norm_num
          ring

omit [CompleteSpace F] in
/-- Absolute-integral shell bound under the canonical parameterized finite
cover data. -/
theorem klLateShell_abs {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖
      ∂klTailMeasure (V := V) R (klLateShell x R k)) ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
        (Real.exp (-((k : ℝ) ^ 2) / 4) *
          (klLateTailC V * (A_q : ℝ))) := by
  have habs := klLateCover_abs (V := V) h x hR
    (Nat.cast_nonneg k) hRT s (klLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (klLateShell_sub (V := V) x R k hy))
    (klLateShell_far (V := V) x R k)
  have hc : 0 < klLateTailC V := by
    unfold klLateTailC klTailRoot
    exact Real.rpow_pos_of_pos (klTailCore_pos (V := V) one_pos) _
  have hD : 0 ≤ Real.exp (-((k : ℝ) ^ 2) / 4) *
      (klLateTailC V * (A_q : ℝ)) :=
    mul_nonneg (Real.exp_pos _).le
      (mul_nonneg hc.le (NNReal.coe_nonneg A_q))
  have hcardR : (s.card : ℝ) ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact habs.trans (mul_le_mul_of_nonneg_right hcardR hD)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
