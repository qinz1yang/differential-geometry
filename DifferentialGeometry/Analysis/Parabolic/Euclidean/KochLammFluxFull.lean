import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxAbs
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxSeries
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateFull
import DifferentialGeometry.Analysis.Parabolic.Euclidean.QuantCover

/-!
# Full terminal-slab summation for the Koch--Lamm flux potential

The existing measurable half-open shell partition is reused for the
directional first-derivative kernel.  Absolute shell estimates imply full
Bochner integrability, identify the shell sum, and give a scale-free terminal
flux bound with a canonical quantitative cover.
-/

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

/-- The full directional terminal-slab flux potential. -/
def klFluxFull1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ) (w : V) (f : ℝ × V → F) (x : V) : F :=
  ∫ z : ℝ × V, klFluxKernel (R ^ 2) w x z • f z
    ∂klTermMeasure (V := V) (R ^ 2)

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- One parameterized shell is integrable as a set integral against the full
terminal measure. -/
theorem klFluxSt_int {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    IntegrableOn (fun z : ℝ × V ↦ klFluxKernel (R ^ 2) w x z • f z)
      (klLateStShell x R k) (klTailMeasure (V := V) R Set.univ) := by
  rw [IntegrableOn, klLateStShell, klTail_restrict]
  exact (klFluxCover_est (V := V) h w x hR (Nat.cast_nonneg k) hRT s
    (klLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (klLateShell_sub (V := V) x R k hy))
    (klLateShell_far (V := V) x R k)).1

omit [CompleteSpace F] in
/-- One shell's set integral of the integrand norm has the exact summable
Gaussian-polynomial flux majorant. -/
theorem klFluxSt_abs {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    (∫ z : ℝ × V in klLateStShell x R k,
        ‖klFluxKernel (R ^ 2) w x z • f z‖
        ∂klTailMeasure (V := V) R Set.univ) ≤
      klFluxWeight (Module.finrank ℝ V) k *
        (‖w‖ * (klFluxTailC V * (Aₚ : ℝ))) := by
  rw [klLateStShell, klTail_restrict]
  have habs := klFluxShell_abs (V := V) h w x hR hRT k s hcard hcover
  calc
    (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z • f z‖
        ∂klTailMeasure (V := V) R (klLateShell x R k)) ≤
        (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
          (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
            (klFluxTailC V * (Aₚ : ℝ))) := habs
    _ = klFluxWeight (Module.finrank ℝ V) k *
        (‖w‖ * (klFluxTailC V * (Aₚ : ℝ))) := by
      unfold klFluxWeight
      norm_num [Nat.cast_pow, Nat.cast_mul]
      ring

omit [CompleteSpace F] in
/-- The set integrals of the directional integrand norm over all shells are
summable. -/
theorem klFluxAbs_sum {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    Summable (fun k : ℕ ↦
      ∫ z : ℝ × V in klLateStShell x R k,
        ‖klFluxKernel (R ^ 2) w x z • f z‖
        ∂klTailMeasure (V := V) R Set.univ) := by
  let C : ℝ := ‖w‖ * (klFluxTailC V * (Aₚ : ℝ))
  exact Summable.of_nonneg_of_le
    (fun k ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    (fun k ↦ by
      simpa only [C] using
        (klFluxSt_abs (V := V) h w x hR hRT k (s k)
          (hcard k) (hcover k)))
    ((klFluxWeight_sum (Module.finrank ℝ V)).mul_right C)

omit [CompleteSpace F] in
/-- The local late-flux hypothesis makes the full directional terminal-slab
integrand Bochner integrable. -/
theorem klFluxFull_int {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    Integrable (fun z : ℝ × V ↦ klFluxKernel (R ^ 2) w x z • f z)
      (klTermMeasure (V := V) (R ^ 2)) := by
  rw [klTerm_eq_tail (V := V) R]
  have hU := integrableOn_iUnion_of_summable_integral_norm
    (fun k ↦ klFluxSt_int (V := V) h w x hR hRT k (s k)
      (hcover k))
    (klFluxAbs_sum (V := V) h w x hR hRT s hcard hcover)
  rw [klLateSt_union (V := V) x hR] at hU
  simpa only [IntegrableOn, Measure.restrict_univ] using hU

omit [CompleteSpace F] in
/-- The shell integrals sum to the full directional terminal-slab potential. -/
theorem klFluxFull_sum {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    HasSum (fun k : ℕ ↦
      klFluxPiece1 R w f x (klLateShell x R k))
      (klFluxFull1 R w f x) := by
  let μ := klTailMeasure (V := V) R Set.univ
  let g : ℝ × V → F := fun z ↦ klFluxKernel (R ^ 2) w x z • f z
  have hU : IntegrableOn g (⋃ k : ℕ, klLateStShell x R k) μ := by
    rw [klLateSt_union (V := V) x hR]
    simpa only [IntegrableOn, Measure.restrict_univ, μ, g,
      ← klTerm_eq_tail (V := V) R] using
      (klFluxFull_int (V := V) h w x hR hRT s hcard hcover)
  have hsum := hasSum_integral_iUnion
    (f := g) (μ := μ) (fun k ↦ klLateSt_mble (V := V) x R k)
    (klLateSt_disj (V := V) x hR) hU
  convert hsum using 1
  · funext k
    simp only [klFluxPiece1, g, μ, klLateStShell]
    rw [klTail_restrict]
  · simp only [klFluxFull1, g, μ]
    rw [klLateSt_union (V := V) x hR, Measure.restrict_univ,
      klTerm_eq_tail (V := V) R]

omit [CompleteSpace F] in
/-- The full directional terminal-slab flux has the summed scale-free
Koch--Lamm bound. -/
theorem klFluxFull_norm {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    ‖klFluxFull1 R w f x‖ ≤
      klFluxSeries (Module.finrank ℝ V) *
        (‖w‖ * (klFluxTailC V * (Aₚ : ℝ))) := by
  let μ := klTailMeasure (V := V) R Set.univ
  let g : ℝ × V → F := fun z ↦ klFluxKernel (R ^ 2) w x z • f z
  let C : ℝ := ‖w‖ * (klFluxTailC V * (Aₚ : ℝ))
  have hint : Integrable g μ := by
    simpa only [μ, g, ← klTerm_eq_tail (V := V) R] using
      (klFluxFull_int (V := V) h w x hR hRT s hcard hcover)
  have habs := klFluxAbs_sum (V := V) h w x hR hRT s hcard hcover
  have hmaj : Summable
      (fun k : ℕ ↦ klFluxWeight (Module.finrank ℝ V) k * C) :=
    (klFluxWeight_sum (Module.finrank ℝ V)).mul_right C
  have hnormU : IntegrableOn (fun z ↦ ‖g z‖)
      (⋃ k : ℕ, klLateStShell x R k) μ := by
    rw [klLateSt_union (V := V) x hR]
    simpa only [IntegrableOn, Measure.restrict_univ] using hint.norm
  have hdecomp := integral_iUnion
    (f := fun z ↦ ‖g z‖) (μ := μ)
    (fun k ↦ klLateSt_mble (V := V) x R k)
    (klLateSt_disj (V := V) x hR) hnormU
  rw [klLateSt_union (V := V) x hR, Measure.restrict_univ] at hdecomp
  calc
    ‖klFluxFull1 R w f x‖ = ‖∫ z, g z ∂μ‖ := by
      simp only [klFluxFull1, g, μ]
      rw [klTerm_eq_tail (V := V) R]
    _ ≤ ∫ z, ‖g z‖ ∂μ := norm_integral_le_integral_norm g
    _ = ∑' k : ℕ, ∫ z in klLateStShell x R k, ‖g z‖ ∂μ := hdecomp
    _ ≤ ∑' k : ℕ, klFluxWeight (Module.finrank ℝ V) k * C :=
      habs.tsum_le_tsum
        (fun k ↦ by
          simpa only [g, μ, C] using
            (klFluxSt_abs (V := V) h w x hR hRT k (s k)
              (hcard k) (hcover k))) hmaj
    _ = klFluxSeries (Module.finrank ℝ V) * C := by
      rw [tsum_mul_right]
      rfl
    _ = klFluxSeries (Module.finrank ℝ V) *
        (‖w‖ * (klFluxTailC V * (Aₚ : ℝ))) := rfl

omit [CompleteSpace F] in
/-- The terminal flux estimate with its covering family chosen canonically
from the finite-dimensional quantitative-cover theorem. -/
theorem klFluxFull_canon {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖klFluxFull1 R w f x‖ ≤
      klFluxSeries (Module.finrank ℝ V) *
        (‖w‖ * (klFluxTailC V * (Aₚ : ℝ))) := by
  classical
  choose s hcard hcover using
    fun k : ℕ ↦ exists_shell_cover (V := V) x hR k
  exact klFluxFull_norm (V := V) h w x hR hRT s hcard hcover

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
