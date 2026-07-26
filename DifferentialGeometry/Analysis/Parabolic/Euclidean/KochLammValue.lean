import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammEarly
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateFull
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammPotential

/-!
# The full ordinary Koch--Lamm value potential

This file joins the initial and terminal halves of the ordinary-source heat
potential at an arbitrary positive time.  The terminal radius is `sqrt t`, so
both source estimates are used on the same original horizon.
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

/-- The ordinary-source value potential, split at half of the observation
time.  The two terms are the already realized early and full terminal
potentials. -/
def klHeat0 (t : ℝ) (f : ℝ × V → F) (x : V) : F :=
  heatEarly0 t f x + klLateFull0 (Real.sqrt t) f x

/-- The ordinary heat integrand is Bochner integrable on the complete early
half-slab.  This is the integrability statement needed to identify the split
potential with the usual Duhamel integral. -/
theorem klEarly0_int {T t : ℝ} {A₁ A_q : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (h : KLSource0 T A₁ A_q f) :
    IntegrableOn
      (fun z : ℝ × V ↦ heatKernel (t - z.1) (x - z.2) • f z)
      (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V))
      (stVolume : Measure (ℝ × V)) := by
  let q : ℝ × V → ℝ≥0∞ := fun z ↦
    ‖heatKernel (t - z.1) (x - z.2) • f z‖₊
  have hsrc := kl0_to_srcCarl (V := V) h
  have hmass :
      (∫⁻ z in (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)), q z
          ∂(stVolume : Measure (ℝ × V))) ≤
        earlyHeatC V * (A₁ : ℝ≥0∞) := by
    calc
      (∫⁻ z in (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)), q z
          ∂(stVolume : Measure (ℝ × V))) ≤
          ∫⁻ z in (⋃ k : ℕ, shellCyl t x k), q z
            ∂(stVolume : Measure (ℝ × V)) :=
        lintegral_mono_set (earlySlab_sub ht x)
      _ ≤ ∑' k : ℕ, ∫⁻ z in shellCyl t x k, q z
          ∂(stVolume : Measure (ℝ × V)) :=
        lintegral_iUnion_le _ _
      _ = ∑' k : ℕ, shellMass t f x k := by rfl
      _ ≤ ∑' k : ℕ,
          nearHeatC V * (A₁ : ℝ≥0∞) *
            ENNReal.ofReal (shellWeight (Module.finrank ℝ V) k) := by
        exact ENNReal.tsum_le_tsum (shellMass_le ht htT f x hsrc)
      _ = earlyHeatC V * (A₁ : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_left]
        unfold earlyHeatC shellSeries
        ac_rfl
  have hfinite :
      (∫⁻ z in (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)), q z
          ∂(stVolume : Measure (ℝ × V))) < ∞ :=
    hmass.trans_lt (lt_top_iff_ne_top.2
      (ENNReal.mul_ne_top (earlyHeatC_ne_top V) ENNReal.coe_ne_top))
  have hk : Measurable
      (fun z : ℝ × V ↦ heatKernel (t - z.1) (x - z.2)) := by
    unfold heatKernel heatScale baseHeat baseHeatMass
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ × V ↦ heatKernel (t - z.1) (x - z.2) • f z)
      ((stVolume : Measure (ℝ × V)).restrict
        (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V))) :=
    (hk.aestronglyMeasurable.mono_measure Measure.restrict_le_self).smul
      (h.ae.mono_measure Measure.restrict_le_self)
  refine ⟨hmeas, hasFiniteIntegral_iff_enorm.2 ?_⟩
  simpa only [q] using hfinite

/-- The same ordinary heat integrand is Bochner integrable on the terminal
half-slab, with the terminal radius chosen as `sqrt t`. -/
theorem klLate0_int {T t : ℝ} {A₁ A_q : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (h : KLSource0 T A₁ A_q f) :
    Integrable (fun z : ℝ × V ↦ klTermKernel t x z • f z)
      (klTermMeasure (V := V) t) := by
  classical
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  choose s hcard hcover using
    fun k : ℕ ↦ exists_shell_cover (V := V) x hsqrt k
  have hi := klLateFull_int (V := V) h x hsqrt (by
    simpa only [Real.sq_sqrt ht.le] using htT) s hcard hcover
  simpa only [Real.sq_sqrt ht.le] using hi

/-- The split ordinary potential is exactly the original Duhamel heat
potential.  Thus the early/terminal estimates apply to the canonical linear
solution operator, rather than to a separately defined surrogate. -/
theorem klHeat0_eq_heatPot {T t : ℝ} {A₁ A_q : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (h : KLSource0 T A₁ A_q f) :
    klHeat0 t f x = heatPot0 t f x := by
  let g : ℝ × V → F := fun z ↦
    heatKernel (t - z.1) (x - z.2) • f z
  let E : Set (ℝ × V) := Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)
  let L : Set (ℝ × V) := Ioc (t / 2) t ×ˢ (Set.univ : Set V)
  have hearly : IntegrableOn g E (stVolume : Measure (ℝ × V)) := by
    simpa only [g, E] using klEarly0_int (V := V) ht htT f x h
  have hlateM := klLate0_int (V := V) ht htT f x h
  have hlate : IntegrableOn g L (stVolume : Measure (ℝ × V)) := by
    simpa only [IntegrableOn, g, L, klTermKernel, klTermMeasure, stVolume,
      Measure.restrict_prod_eq_prod_univ] using hlateM
  have hdisj : Disjoint E L := by
    exact (Ioc_disjoint_Ioc_of_le (a := 0) (d := t) le_rfl).set_prod_left
      Set.univ Set.univ
  have hLm : MeasurableSet L := by
    exact measurableSet_Ioc.prod MeasurableSet.univ
  have hsplit := setIntegral_union hdisj hLm hearly hlate
  have hEL : E ∪ L = Ioc 0 t ×ˢ (Set.univ : Set V) := by
    unfold E L
    rw [← Set.union_prod, Ioc_union_Ioc_eq_Ioc]
    all_goals linarith
  rw [hEL] at hsplit
  have hfull : IntegrableOn g
      (Ioc 0 t ×ˢ (Set.univ : Set V))
      (stVolume : Measure (ℝ × V)) := by
    rw [← hEL]
    exact hearly.union hlate
  have hprod :
      (∫ z in Ioc 0 t ×ˢ (Set.univ : Set V), g z
          ∂(stVolume : Measure (ℝ × V))) =
        ∫ s in Ioc 0 t, ∫ y : V, g (s, y) := by
    unfold stVolume at hfull ⊢
    simpa only [setIntegral_univ] using
      (setIntegral_prod (f := g) hfull)
  have hlateEq :
      (∫ z in L, g z ∂(stVolume : Measure (ℝ × V))) =
        klLateFull0 (V := V) (Real.sqrt t) f x := by
    unfold L g klLateFull0 klTermKernel klTermMeasure stVolume
    rw [Real.sq_sqrt ht.le, Measure.restrict_prod_eq_prod_univ]
  change
    (∫ z in E, g z ∂(stVolume : Measure (ℝ × V))) +
        klLateFull0 (V := V) (Real.sqrt t) f x =
      ∫ s in 0..t, ∫ y : V, g (s, y)
  rw [intervalIntegral.integral_of_le ht.le, ← hprod, hsplit, hlateEq]

/-- The full ordinary-source value potential is bounded by the sum of the
local `L¹` and terminal `L^((n+4)/2)` Koch--Lamm radii. -/
theorem klHeat0_norm {T t : ℝ} {A₁ A_q : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (h : KLSource0 T A₁ A_q f) :
    (↑‖klHeat0 t f x‖₊ : ℝ≥0∞) ≤
      earlyHeatC V * (A₁ : ℝ≥0∞) +
        ENNReal.ofReal
          (klLateSeries (Module.finrank ℝ V) *
            (klLateTailC V * (A_q : ℝ))) := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hlate := klLateFull_canon (V := V) h x hsqrt (by
    simpa only [Real.sq_sqrt ht.le] using htT)
  have hlateE :
      (↑‖klLateFull0 (V := V) (Real.sqrt t) f x‖₊ : ℝ≥0∞) ≤
        ENNReal.ofReal
          (klLateSeries (Module.finrank ℝ V) *
            (klLateTailC V * (A_q : ℝ))) := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal hlate
  have hearly := kl0_early_norm (V := V) ht htT f x h
  unfold klHeat0
  calc
    (↑‖heatEarly0 t f x + klLateFull0 (V := V) (Real.sqrt t) f x‖₊ :
        ℝ≥0∞) ≤
        (↑‖heatEarly0 t f x‖₊ : ℝ≥0∞) +
          (↑‖klLateFull0 (V := V) (Real.sqrt t) f x‖₊ : ℝ≥0∞) := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        ← ofReal_norm_eq_enorm,
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ ≤ earlyHeatC V * (A₁ : ℝ≥0∞) +
        ENNReal.ofReal
          (klLateSeries (Module.finrank ℝ V) *
            (klLateTailC V * (A_q : ℝ))) :=
      add_le_add hearly hlateE

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
