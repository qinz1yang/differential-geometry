import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.AbsoluteBounds
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Series
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Summation
import DifferentialGeometry.Analysis.Parabolic.Euclidean.Covering.Quantitative

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

def kochLammFluxPotential {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ) (w : V) (f : ℝ × V → F) (x : V) : F :=
  ∫ z : ℝ × V, kochLammFluxKernel (R ^ 2) w x z • f z
    ∂kochLammTermMeasure (V := V) (R ^ 2)

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem kochLammFluxSt_int {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    IntegrableOn (fun z : ℝ × V ↦ kochLammFluxKernel (R ^ 2) w x z • f z)
      (kochLammLateStShell x R k) (kochLammTailMeasure (V := V) R Set.univ) := by
  rw [IntegrableOn, kochLammLateStShell, kochLammTail_restrict]
  exact (kochLammFluxCover_est (V := V) h w x hR (Nat.cast_nonneg k) hRT s
    (kochLammLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (kochLammLateShell_sub (V := V) x R k hy))
    (kochLammLateShell_far (V := V) x R k)).1

omit [CompleteSpace F] in
theorem kochLammFluxSt_abs {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    (∫ z : ℝ × V in kochLammLateStShell x R k,
        ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
        ∂kochLammTailMeasure (V := V) R Set.univ) ≤
      kochLammFluxWeight (Module.finrank ℝ V) k *
        (‖w‖ * (kochLammFluxTailC V * (Aₚ : ℝ))) := by
  rw [kochLammLateStShell, kochLammTail_restrict]
  have habs := kochLammFluxShell_abs (V := V) h w x hR hRT k s hcard hcover
  calc
    (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
        ∂kochLammTailMeasure (V := V) R (kochLammLateShell x R k)) ≤
        (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
          (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
            (kochLammFluxTailC V * (Aₚ : ℝ))) := habs
    _ = kochLammFluxWeight (Module.finrank ℝ V) k *
        (‖w‖ * (kochLammFluxTailC V * (Aₚ : ℝ))) := by
      unfold kochLammFluxWeight
      norm_num [Nat.cast_pow, Nat.cast_mul]
      ring

omit [CompleteSpace F] in
theorem kochLammFluxAbs_sum {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    Summable (fun k : ℕ ↦
      ∫ z : ℝ × V in kochLammLateStShell x R k,
        ‖kochLammFluxKernel (R ^ 2) w x z • f z‖
        ∂kochLammTailMeasure (V := V) R Set.univ) := by
  let C : ℝ := ‖w‖ * (kochLammFluxTailC V * (Aₚ : ℝ))
  exact Summable.of_nonneg_of_le
    (fun k ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    (fun k ↦ by
      simpa only [C] using
        (kochLammFluxSt_abs (V := V) h w x hR hRT k (s k)
          (hcard k) (hcover k)))
    ((kochLammFluxWeight_sum (Module.finrank ℝ V)).mul_right C)

omit [CompleteSpace F] in
theorem kochLammFluxKernel_smul_integrable {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    Integrable (fun z : ℝ × V ↦ kochLammFluxKernel (R ^ 2) w x z • f z)
      (kochLammTermMeasure (V := V) (R ^ 2)) := by
  rw [kochLammTerm_eq_tail (V := V) R]
  have hU := integrableOn_iUnion_of_summable_integral_norm
    (fun k ↦ kochLammFluxSt_int (V := V) h w x hR hRT k (s k)
      (hcover k))
    (kochLammFluxAbs_sum (V := V) h w x hR hRT s hcard hcover)
  rw [kochLammLateSt_union (V := V) x hR] at hU
  simpa only [IntegrableOn, Measure.restrict_univ] using hU

omit [CompleteSpace F] in
theorem hasSum_klFluxPiece_klFluxPotential {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    HasSum (fun k : ℕ ↦
      kochLammFluxPiece1 R w f x (kochLammLateShell x R k))
      (kochLammFluxPotential R w f x) := by
  let μ := kochLammTailMeasure (V := V) R Set.univ
  let g : ℝ × V → F := fun z ↦ kochLammFluxKernel (R ^ 2) w x z • f z
  have hU : IntegrableOn g (⋃ k : ℕ, kochLammLateStShell x R k) μ := by
    rw [kochLammLateSt_union (V := V) x hR]
    simpa only [IntegrableOn, Measure.restrict_univ, μ, g,
      ← kochLammTerm_eq_tail (V := V) R] using
      (kochLammFluxKernel_smul_integrable (V := V) h w x hR hRT s hcard hcover)
  have hsum := hasSum_integral_iUnion
    (f := g) (μ := μ) (fun k ↦ kochLammLateSt_mble (V := V) x R k)
    (kochLammLateSt_disj (V := V) x hR) hU
  convert hsum using 1
  · funext k
    simp only [kochLammFluxPiece1, g, μ, kochLammLateStShell]
    rw [kochLammTail_restrict]
  · simp only [kochLammFluxPotential, g, μ]
    rw [kochLammLateSt_union (V := V) x hR, Measure.restrict_univ,
      kochLammTerm_eq_tail (V := V) R]

omit [CompleteSpace F] in
theorem norm_klFluxPotential_le_of_shellCover {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    ‖kochLammFluxPotential R w f x‖ ≤
      kochLammFluxSeries (Module.finrank ℝ V) *
        (‖w‖ * (kochLammFluxTailC V * (Aₚ : ℝ))) := by
  let μ := kochLammTailMeasure (V := V) R Set.univ
  let g : ℝ × V → F := fun z ↦ kochLammFluxKernel (R ^ 2) w x z • f z
  let C : ℝ := ‖w‖ * (kochLammFluxTailC V * (Aₚ : ℝ))
  have hint : Integrable g μ := by
    simpa only [μ, g, ← kochLammTerm_eq_tail (V := V) R] using
      (kochLammFluxKernel_smul_integrable (V := V) h w x hR hRT s hcard hcover)
  have habs := kochLammFluxAbs_sum (V := V) h w x hR hRT s hcard hcover
  have hmaj : Summable
      (fun k : ℕ ↦ kochLammFluxWeight (Module.finrank ℝ V) k * C) :=
    (kochLammFluxWeight_sum (Module.finrank ℝ V)).mul_right C
  have hnormU : IntegrableOn (fun z ↦ ‖g z‖)
      (⋃ k : ℕ, kochLammLateStShell x R k) μ := by
    rw [kochLammLateSt_union (V := V) x hR]
    simpa only [IntegrableOn, Measure.restrict_univ] using hint.norm
  have hdecomp := integral_iUnion
    (f := fun z ↦ ‖g z‖) (μ := μ)
    (fun k ↦ kochLammLateSt_mble (V := V) x R k)
    (kochLammLateSt_disj (V := V) x hR) hnormU
  rw [kochLammLateSt_union (V := V) x hR, Measure.restrict_univ] at hdecomp
  calc
    ‖kochLammFluxPotential R w f x‖ = ‖∫ z, g z ∂μ‖ := by
      simp only [kochLammFluxPotential, g, μ]
      rw [kochLammTerm_eq_tail (V := V) R]
    _ ≤ ∫ z, ‖g z‖ ∂μ := norm_integral_le_integral_norm g
    _ = ∑' k : ℕ, ∫ z in kochLammLateStShell x R k, ‖g z‖ ∂μ := hdecomp
    _ ≤ ∑' k : ℕ, kochLammFluxWeight (Module.finrank ℝ V) k * C :=
      habs.tsum_le_tsum
        (fun k ↦ by
          simpa only [g, μ, C] using
            (kochLammFluxSt_abs (V := V) h w x hR hRT k (s k)
              (hcard k) (hcover k))) hmaj
    _ = kochLammFluxSeries (Module.finrank ℝ V) * C := by
      rw [tsum_mul_right]
      rfl
    _ = kochLammFluxSeries (Module.finrank ℝ V) *
        (‖w‖ * (kochLammFluxTailC V * (Aₚ : ℝ))) := rfl

omit [CompleteSpace F] in
theorem norm_klFluxPotential_le {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖kochLammFluxPotential R w f x‖ ≤
      kochLammFluxSeries (Module.finrank ℝ V) *
        (‖w‖ * (kochLammFluxTailC V * (Aₚ : ℝ))) := by
  classical
  choose s hcard hcover using
    fun k : ℕ ↦ exists_shell_cover (V := V) x hR k
  exact norm_klFluxPotential_le_of_shellCover (V := V) h w x hR hRT s hcard hcover

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
