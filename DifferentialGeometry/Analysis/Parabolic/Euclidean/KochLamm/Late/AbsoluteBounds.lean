import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Shell

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
theorem kochLammLatePiece_abs {T R k : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x c : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    {S : Set V} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖
      ∂kochLammTailMeasure (V := V) R S) ≤
      Real.exp (-(k ^ 2) / 4) * (kochLammLateTailC V * (A_q : ℝ)) := by
  let μ := kochLammTailMeasure (V := V) R S
  have hkMem : MemLp (kochLammTermKernel (R ^ 2) x)
      (ENNReal.ofReal (kochLammQDual V)) μ :=
    (kochLammTermKernel_memLp (V := V) (t := R ^ 2) x).mono_measure
      (kochLammTailTerm_le (V := V) R S)
  have hfMem : MemLp f (ENNReal.ofReal (kochLammQReal V)) μ := by
    simpa only [kochLammQReal_ofReal] using
      (kochLammPieceSource_memLp (V := V) h c hR hRT hS)
  have hhold :
      (∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖ ∂μ) ≤
        (kochLammTermTailPow (V := V) R x S) ^ (1 / kochLammQDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ kochLammQReal V ∂μ) ^
            (1 / kochLammQReal V) := by
    calc
      (∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖ ∂μ) =
          ∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z‖ *
            ‖(fun w : ℝ × V ↦ ‖f w‖) z‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        simp only [norm_smul, norm_norm]
      _ ≤ (kochLammTermTailPow (V := V) R x S) ^ (1 / kochLammQDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ kochLammQReal V ∂μ) ^
            (1 / kochLammQReal V) := by
        simpa only [kochLammTermTailPow, μ, norm_norm] using
          (integral_mul_norm_le_Lp_mul_Lq (kochLammQ_holder (V := V))
            hkMem hfMem.norm)
  have hkern := kochLammTailKernel_integral_rpow_le (V := V) hR hk x hSm hfar
  have hsrc := kochLammPieceSource_integral_rpow_le (V := V) h c hR hRT hS
  have hs : 0 < kochLammLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < kochLammLateTailC V := by
    unfold kochLammLateTailC kochLammTailRoot
    exact Real.rpow_pos_of_pos (kochLammTailCore_pos (V := V) one_pos) _
  calc
    (∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖
        ∂kochLammTailMeasure (V := V) R S) ≤
        (kochLammTermTailPow (V := V) R x S) ^ (1 / kochLammQDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ kochLammQReal V
            ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammQReal V) := hhold
    _ ≤ (Real.exp (-(k ^ 2) / 4) *
          (kochLammLateTailC V * kochLammLqScaleR (V := V) R)) *
        ((kochLammLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) :=
      mul_le_mul hkern hsrc
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc.le hs.le))
    _ = Real.exp (-(k ^ 2) / 4) *
        (kochLammLateTailC V * (A_q : ℝ)) := by
      calc
        Real.exp (-(k ^ 2) / 4) *
              (kochLammLateTailC V * kochLammLqScaleR (V := V) R) *
              ((kochLammLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) =
            Real.exp (-(k ^ 2) / 4) * kochLammLateTailC V *
              (kochLammLqScaleR (V := V) R *
                (kochLammLqScaleR (V := V) R)⁻¹) * (A_q : ℝ) := by ring
        _ = Real.exp (-(k ^ 2) / 4) *
            (kochLammLateTailC V * (A_q : ℝ)) := by
          rw [mul_inv_cancel₀ hs.ne']
          ring

omit [CompleteSpace F] in
theorem kochLammLateCover_abs {T R k : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    (s : Finset V) {S : Set V} (hSm : MeasurableSet S)
    (hcover : S ⊆ ⋃ c ∈ s, Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖
      ∂kochLammTailMeasure (V := V) R S) ≤
      (s.card : ℝ) *
        (Real.exp (-(k ^ 2) / 4) * (kochLammLateTailC V * (A_q : ℝ))) := by
  classical
  let D : ℝ :=
    Real.exp (-(k ^ 2) / 4) * (kochLammLateTailC V * (A_q : ℝ))
  induction s using Finset.induction_on generalizing S with
  | empty =>
      have hS0 : S = ∅ := by
        simpa using hcover
      subst S
      simp [kochLammTailMeasure]
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
        simp only [S₀, S₁, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
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
      have hint₀ := kochLammLatePiece_int (V := V) h x c hR hRT hS₀ball
      have hint₁ :=
        (kochLammLateCover_est (V := V) h x hR hk hRT s hS₁m hcover₁ hfar₁).1
      have hnorm₀ :
          (∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖
            ∂kochLammTailMeasure (V := V) R S₀) ≤ D := by
        simpa only [D] using
          (kochLammLatePiece_abs (V := V) h x c hR hk hRT
            hS₀m hS₀ball hfar₀)
      have hnorm₁ := ih hS₁m hcover₁ hfar₁
      have hμ : kochLammTailMeasure (V := V) R S =
          kochLammTailMeasure (V := V) R S₀ + kochLammTailMeasure (V := V) R S₁ := by
        rw [← hsplit]
        exact kochLammTail_union (V := V) hdisj hS₁m
      rw [hμ, integral_add_measure hint₀.norm hint₁.norm]
      calc
        (∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖
            ∂kochLammTailMeasure (V := V) R S₀) +
            ∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖
              ∂kochLammTailMeasure (V := V) R S₁ ≤
            D + (s.card : ℝ) * D := add_le_add hnorm₀ hnorm₁
        _ = ((insert c s).card : ℝ) * D := by
          rw [Finset.card_insert_of_notMem hc]
          norm_num
          ring

omit [CompleteSpace F] in
theorem kochLammLateShell_abs {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    (∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖
      ∂kochLammTailMeasure (V := V) R (kochLammLateShell x R k)) ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
        (Real.exp (-((k : ℝ) ^ 2) / 4) *
          (kochLammLateTailC V * (A_q : ℝ))) := by
  have habs := kochLammLateCover_abs (V := V) h x hR
    (Nat.cast_nonneg k) hRT s (kochLammLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (kochLammLateShell_sub (V := V) x R k hy))
    (kochLammLateShell_far (V := V) x R k)
  have hc : 0 < kochLammLateTailC V := by
    unfold kochLammLateTailC kochLammTailRoot
    exact Real.rpow_pos_of_pos (kochLammTailCore_pos (V := V) one_pos) _
  have hD : 0 ≤ Real.exp (-((k : ℝ) ^ 2) / 4) *
      (kochLammLateTailC V * (A_q : ℝ)) :=
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
