import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxShell

/-!
# Absolute-integral bounds for terminal Koch--Lamm flux shells

The full directional terminal potential requires summability of integrals of
the integrand norm, not merely of norms of shell integrals.  This file proves
the one-piece, finite-cover, and shell absolute estimates.
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
/-- Absolute integral of the directional kernel/source product on one far
selected terminal piece. -/
theorem klFluxPiece_abs {T R k : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x c : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    {S : Set V} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖
      ∂klTailMeasure (V := V) R S) ≤
      ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (klFluxTailC V * (Aₚ : ℝ)) := by
  let μ := klTailMeasure (V := V) R S
  have hkMem : MemLp (klFluxKernel (R ^ 2) w x)
      (ENNReal.ofReal (klPDual V)) μ :=
    (klFluxKernel_memLp (V := V) (sq_pos_of_pos hR) w x).mono_measure
      (klTailTerm_le (V := V) R S)
  have hfMem : MemLp f (ENNReal.ofReal (klPReal V)) μ := by
    simpa only [klPReal_ofReal] using
      (klFluxPiece_mem (V := V) h c hR hRT hS)
  have hhold :
      (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖ ∂μ) ≤
        (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V ∂μ) ^
            (1 / klPDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ klPReal V ∂μ) ^
            (1 / klPReal V) := by
    calc
      (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖ ∂μ) =
          ∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z‖ *
            ‖(fun u : ℝ × V ↦ ‖f u‖) z‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        simp only [norm_smul, norm_norm]
      _ ≤ (∫ z : ℝ × V,
            ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V ∂μ) ^
            (1 / klPDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ klPReal V ∂μ) ^
            (1 / klPReal V) := by
        simpa only [norm_norm] using
          (integral_mul_norm_le_Lp_mul_Lq (klP_holder (V := V))
            hkMem hfMem.norm)
  have hkern := klFluxTailKern (V := V) hR hk w x hSm hfar
  have hsrc := klFluxPiece_src (V := V) h c hR hRT hS
  have hs : 0 < klLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ klFluxTailC V := by
    unfold klFluxTailC klFluxHalfRoot
    exact Real.rpow_nonneg
      (klFluxHalf_nonneg (V := V) one_pos) _
  calc
    (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖
        ∂klTailMeasure (V := V) R S) ≤
        (∫ z : ℝ × V,
            ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
            ∂klTailMeasure (V := V) R S) ^ (1 / klPDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ klPReal V
            ∂klTailMeasure (V := V) R S) ^ (1 / klPReal V) := hhold
    _ ≤ (‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
          (klFluxTailC V * klLpScaleR (V := V) R))) *
        ((klLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) :=
      mul_le_mul hkern hsrc
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (norm_nonneg w)
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc hs.le)))
    _ = ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (klFluxTailC V * (Aₚ : ℝ)) := by
      calc
        (‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
              (klFluxTailC V * klLpScaleR (V := V) R))) *
              ((klLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) =
            ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) * klFluxTailC V *
              (klLpScaleR (V := V) R *
                (klLpScaleR (V := V) R)⁻¹) * (Aₚ : ℝ) := by ring
        _ = ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
            (klFluxTailC V * (Aₚ : ℝ)) := by
          rw [mul_inv_cancel₀ hs.ne']
          ring

omit [CompleteSpace F] in
/-- Absolute-integral form of the arbitrary finite-cover flux estimate. -/
theorem klFluxCover_abs {T R k : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    (s : Finset V) {S : Set V} (hSm : MeasurableSet S)
    (hcover : S ⊆ ⋃ c ∈ s, Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖
      ∂klTailMeasure (V := V) R S) ≤
      (s.card : ℝ) *
        (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
          (klFluxTailC V * (Aₚ : ℝ))) := by
  classical
  let D : ℝ :=
    ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
      (klFluxTailC V * (Aₚ : ℝ))
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
      have hint₀ := klFluxPiece_int (V := V) h w x c hR hRT hS₀ball
      have hint₁ :=
        (klFluxCover_est (V := V) h w x hR hk hRT s
          hS₁m hcover₁ hfar₁).1
      have hnorm₀ :
          (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖
            ∂klTailMeasure (V := V) R S₀) ≤ D := by
        simpa only [D] using
          (klFluxPiece_abs (V := V) h w x c hR hk hRT
            hS₀m hS₀ball hfar₀)
      have hnorm₁ := ih hS₁m hcover₁ hfar₁
      have hμ : klTailMeasure (V := V) R S =
          klTailMeasure (V := V) R S₀ + klTailMeasure (V := V) R S₁ := by
        rw [← hsplit]
        exact klTail_union (V := V) hdisj hS₁m
      rw [hμ, integral_add_measure hint₀.norm hint₁.norm]
      calc
        (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖
            ∂klTailMeasure (V := V) R S₀) +
            ∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖
              ∂klTailMeasure (V := V) R S₁ ≤
            D + (s.card : ℝ) * D := add_le_add hnorm₀ hnorm₁
        _ = ((insert c s).card : ℝ) * D := by
          rw [Finset.card_insert_of_notMem hc]
          norm_num
          ring

omit [CompleteSpace F] in
/-- Absolute-integral shell flux bound under parameterized canonical-cover
data. -/
theorem klFluxShell_abs {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖
      ∂klTailMeasure (V := V) R (klLateShell x R k)) ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
        (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
          (klFluxTailC V * (Aₚ : ℝ))) := by
  have habs := klFluxCover_abs (V := V) h w x hR
    (Nat.cast_nonneg k) hRT s (klLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (klLateShell_sub (V := V) x R k hy))
    (klLateShell_far (V := V) x R k)
  have hc : 0 ≤ klFluxTailC V := by
    unfold klFluxTailC klFluxHalfRoot
    exact Real.rpow_nonneg
      (klFluxHalf_nonneg (V := V) one_pos) _
  have hD : 0 ≤ ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
      (klFluxTailC V * (Aₚ : ℝ)) :=
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
