import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Shell

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
theorem kochLammFluxPiece_abs {T R k : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x c : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    {S : Set V} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
      ∂kochLammTailMeasure (V := V) R S) ≤
      ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (kochLammFluxTailC V * (Aₚ : ℝ)) := by
  let μ := kochLammTailMeasure (V := V) R S
  have hkMem : MemLp (kochLammFluxKernel (R ^ 2) w x)
      (ENNReal.ofReal (kochLammPDual V)) μ :=
    (kochLammFluxKernel_memLp (V := V) (t := R ^ 2) w x).mono_measure
      (kochLammTailTerm_le (V := V) R S)
  have hfMem : MemLp f (ENNReal.ofReal (kochLammPReal V)) μ := by
    simpa only [kochLammPReal_ofReal] using
      (kochLammFluxPiece_mem (V := V) h c hR hRT hS)
  have hhold :
      (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖ ∂μ) ≤
        (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V ∂μ) ^
            (1 / kochLammPDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ kochLammPReal V ∂μ) ^
            (1 / kochLammPReal V) := by
    calc
      (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖ ∂μ) =
          ∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z‖ *
            ‖(fun u : ℝ × V ↦ ‖f u‖) z‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        simp only [norm_smul, norm_norm]
      _ ≤ (∫ z : ℝ × V,
            ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V ∂μ) ^
            (1 / kochLammPDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ kochLammPReal V ∂μ) ^
            (1 / kochLammPReal V) := by
        simpa only [norm_norm] using
          (integral_mul_norm_le_Lp_mul_Lq (kochLammPDual_holder (V := V))
            hkMem hfMem.norm)
  have hkern := kochLammFluxTailKernel (V := V) hR hk w x hSm hfar
  have hsrc := kochLammFluxPiece_source (V := V) h c hR hRT hS
  have hs : 0 < kochLammLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ kochLammFluxTailC V := by
    unfold kochLammFluxTailC kochLammFluxHalfRoot
    exact Real.rpow_nonneg
      (kochLammFluxHalf_nonneg (V := V) one_pos) _
  calc
    (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
        ∂kochLammTailMeasure (V := V) R S) ≤
        (∫ z : ℝ × V,
            ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
            ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammPDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ kochLammPReal V
            ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammPReal V) := hhold
    _ ≤ (‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
          (kochLammFluxTailC V * kochLammLpScaleR (V := V) R))) *
        ((kochLammLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) :=
      mul_le_mul hkern hsrc
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (norm_nonneg w)
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc hs.le)))
    _ = ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (kochLammFluxTailC V * (Aₚ : ℝ)) := by
      calc
        (‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
              (kochLammFluxTailC V * kochLammLpScaleR (V := V) R))) *
              ((kochLammLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) =
            ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) * kochLammFluxTailC V *
              (kochLammLpScaleR (V := V) R *
                (kochLammLpScaleR (V := V) R)⁻¹) * (Aₚ : ℝ) := by ring
        _ = ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
            (kochLammFluxTailC V * (Aₚ : ℝ)) := by
          rw [mul_inv_cancel₀ hs.ne']
          ring

omit [CompleteSpace F] in
theorem kochLammFluxCover_abs {T R k : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    (s : Finset V) {S : Set V} (hSm : MeasurableSet S)
    (hcover : S ⊆ ⋃ c ∈ s, Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
      ∂kochLammTailMeasure (V := V) R S) ≤
      (s.card : ℝ) *
        (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
          (kochLammFluxTailC V * (Aₚ : ℝ))) := by
  classical
  let D : ℝ :=
    ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
      (kochLammFluxTailC V * (Aₚ : ℝ))
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
      have hint₀ := kochLammFluxPiece_int (V := V) h w x c hR hRT hS₀ball
      have hint₁ :=
        (kochLammFluxCover_est (V := V) h w x hR hk hRT s
          hS₁m hcover₁ hfar₁).1
      have hnorm₀ :
          (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
            ∂kochLammTailMeasure (V := V) R S₀) ≤ D := by
        simpa only [D] using
          (kochLammFluxPiece_abs (V := V) h w x c hR hk hRT
            hS₀m hS₀ball hfar₀)
      have hnorm₁ := ih hS₁m hcover₁ hfar₁
      have hμ : kochLammTailMeasure (V := V) R S =
          kochLammTailMeasure (V := V) R S₀ + kochLammTailMeasure (V := V) R S₁ := by
        rw [← hsplit]
        exact kochLammTail_union (V := V) hdisj hS₁m
      rw [hμ, integral_add_measure hint₀.norm hint₁.norm]
      calc
        (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
            ∂kochLammTailMeasure (V := V) R S₀) +
            ∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
              ∂kochLammTailMeasure (V := V) R S₁ ≤
            D + (s.card : ℝ) * D := add_le_add hnorm₀ hnorm₁
        _ = ((insert c s).card : ℝ) * D := by
          rw [Finset.card_insert_of_notMem hc]
          norm_num
          ring

omit [CompleteSpace F] in
theorem kochLammFluxShell_abs {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
      ∂kochLammTailMeasure (V := V) R (kochLammLateShell x R k)) ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
        (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
          (kochLammFluxTailC V * (Aₚ : ℝ))) := by
  have habs := kochLammFluxCover_abs (V := V) h w x hR
    (Nat.cast_nonneg k) hRT s (kochLammLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (kochLammLateShell_sub (V := V) x R k hy))
    (kochLammLateShell_far (V := V) x R k)
  have hc : 0 ≤ kochLammFluxTailC V := by
    unfold kochLammFluxTailC kochLammFluxHalfRoot
    exact Real.rpow_nonneg
      (kochLammFluxHalf_nonneg (V := V) one_pos) _
  have hD : 0 ≤ ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
      (kochLammFluxTailC V * (Aₚ : ℝ)) :=
    mul_nonneg
      (mul_nonneg (norm_nonneg w) (Real.exp_pos _).le)
      (mul_nonneg hc (NNReal.coe_nonneg Aₚ))
  have hcardR : (s.card : ℝ) ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact habs.trans (mul_le_mul_of_nonneg_right hcardR hD)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
