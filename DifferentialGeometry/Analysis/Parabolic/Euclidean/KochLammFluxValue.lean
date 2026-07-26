import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammEarlyFlux
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxFull
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammPotential

/-!
# The full directional Koch--Lamm flux value potential

This file joins the initial and terminal halves of one directional
divergence-source heat potential at an arbitrary positive observation time.
The terminal radius is `sqrt t`.  Both halves are proved integrable and their
sum is identified exactly with the canonical Duhamel potential `heatPot1`.
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

/-- The directional flux value potential, split at half of the observation
time into the existing early and full terminal potentials. -/
def klHeat1 (t : ℝ) (w : V) (f : ℝ × V → F) (x : V) : F :=
  heatEarly1 t w f x + klFluxFull1 (Real.sqrt t) w f x

/-- The directional heat integrand is Bochner integrable on the complete
early half-slab under the local `L²` arm of `KLSource1`. -/
theorem klEarly1_int {T t : ℝ} {A₂ Aₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f : ℝ × V → F) (x : V)
    (h : KLSource1 T A₂ Aₚ f) :
    IntegrableOn
      (fun z : ℝ × V ↦ heatD1 (t - z.1) w (x - z.2) • f z)
      (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V))
      (stVolume : Measure (ℝ × V)) := by
  let q : ℝ × V → ℝ≥0∞ := fun z ↦
    ‖heatD1 (t - z.1) w (x - z.2) • f z‖ₑ
  have hsrc := kl1_to_gradCarl (V := V) h
  have hsqrt :
      (((A₂ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) = (A₂ : ℝ≥0∞) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hmass :
      (∫⁻ z in (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)), q z
          ∂(stVolume : Measure (ℝ × V))) ≤
        ENNReal.ofReal ‖w‖ * earlyFluxC V * (A₂ : ℝ≥0∞) *
          fluxShellSeries (Module.finrank ℝ V) := by
    calc
      (∫⁻ z in (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)), q z
          ∂(stVolume : Measure (ℝ × V))) ≤
          ∫⁻ z in (⋃ k : ℕ, fluxShellCyl t x k), q z
            ∂(stVolume : Measure (ℝ × V)) :=
        lintegral_mono_set (earlyFluxSlab_sub ht x)
      _ ≤ ∑' k : ℕ, ∫⁻ z in fluxShellCyl t x k, q z
          ∂(stVolume : Measure (ℝ × V)) :=
        lintegral_iUnion_le _ _
      _ = ∑' k : ℕ, fluxShellMass t w f x k := by rfl
      _ ≤ ∑' k : ℕ,
          (ENNReal.ofReal ‖w‖ * earlyFluxC V *
            ((A₂ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) *
            ENNReal.ofReal (fluxShellWeight (Module.finrank ℝ V) k) := by
        apply ENNReal.tsum_le_tsum
        intro k
        obtain ⟨s, hcard, hcover⟩ := fluxShell_cover (V := V) ht x k
        exact fluxShellMass_le ht htT w f x k s hcard hcover hsrc
      _ = (ENNReal.ofReal ‖w‖ * earlyFluxC V *
            ((A₂ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) *
          fluxShellSeries (Module.finrank ℝ V) := by
        rw [ENNReal.tsum_mul_left]
        rfl
      _ = ENNReal.ofReal ‖w‖ * earlyFluxC V * (A₂ : ℝ≥0∞) *
          fluxShellSeries (Module.finrank ℝ V) := by
        rw [hsqrt]
  have hEC : earlyFluxC V ≠ ∞ := by
    unfold earlyFluxC heatBallVol
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  have hbound_ne :
      ENNReal.ofReal ‖w‖ * earlyFluxC V * (A₂ : ℝ≥0∞) *
          fluxShellSeries (Module.finrank ℝ V) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEC)
        ENNReal.coe_ne_top)
      (fluxShellSeries_ne_top (Module.finrank ℝ V))
  have hfinite :
      (∫⁻ z in (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)), q z
          ∂(stVolume : Measure (ℝ × V))) < ∞ :=
    hmass.trans_lt (lt_top_iff_ne_top.2 hbound_ne)
  have hk : Measurable
      (fun z : ℝ × V ↦ heatD1 (t - z.1) w (x - z.2)) := by
    unfold heatD1 heatScale baseD1 baseHeat baseHeatMass
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ × V ↦ heatD1 (t - z.1) w (x - z.2) • f z)
      ((stVolume : Measure (ℝ × V)).restrict
        (Ioc 0 (t / 2) ×ˢ (Set.univ : Set V))) :=
    (hk.aestronglyMeasurable.mono_measure Measure.restrict_le_self).smul
      (h.ae.mono_measure Measure.restrict_le_self)
  refine ⟨hmeas, hasFiniteIntegral_iff_enorm.2 ?_⟩
  simpa only [q] using hfinite

/-- The same directional heat integrand is Bochner integrable on the
terminal half-slab, with terminal radius `sqrt t`. -/
theorem klLate1_int {T t : ℝ} {A₂ Aₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f : ℝ × V → F) (x : V)
    (h : KLSource1 T A₂ Aₚ f) :
    Integrable (fun z : ℝ × V ↦ klFluxKernel t w x z • f z)
      (klTermMeasure (V := V) t) := by
  classical
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  choose s hcard hcover using
    fun k : ℕ ↦ exists_shell_cover (V := V) x hsqrt k
  have hi := klFluxFull_int (V := V) h w x hsqrt (by
    simpa only [Real.sq_sqrt ht.le] using htT) s hcard hcover
  simpa only [Real.sq_sqrt ht.le] using hi

/-- The early/terminal split directional potential is exactly the canonical
Duhamel potential `heatPot1`, with the same direction `w` in both halves. -/
theorem klHeat1_eq_heatPot {T t : ℝ} {A₂ Aₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f : ℝ × V → F) (x : V)
    (h : KLSource1 T A₂ Aₚ f) :
    klHeat1 t w f x = heatPot1 t w f x := by
  let g : ℝ × V → F := fun z ↦
    heatD1 (t - z.1) w (x - z.2) • f z
  let E : Set (ℝ × V) := Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)
  let L : Set (ℝ × V) := Ioc (t / 2) t ×ˢ (Set.univ : Set V)
  have hearly : IntegrableOn g E (stVolume : Measure (ℝ × V)) := by
    simpa only [g, E] using klEarly1_int (V := V) ht htT w f x h
  have hlateM := klLate1_int (V := V) ht htT w f x h
  have hlate : IntegrableOn g L (stVolume : Measure (ℝ × V)) := by
    simpa only [IntegrableOn, g, L, klFluxKernel, klTermMeasure, stVolume,
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
    · exact le_rfl
    · linarith
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
        klFluxFull1 (V := V) (Real.sqrt t) w f x := by
    unfold L g klFluxFull1 klFluxKernel klTermMeasure stVolume
    rw [Real.sq_sqrt ht.le, Measure.restrict_prod_eq_prod_univ]
  change
    (∫ z in E, g z ∂(stVolume : Measure (ℝ × V))) +
        klFluxFull1 (V := V) (Real.sqrt t) w f x =
      ∫ s in 0..t, ∫ y : V, g (s, y)
  rw [intervalIntegral.integral_of_le ht.le, ← hprod, hsplit, hlateEq]

/-- The full directional flux value is bounded by the sum of its local `L²`
and terminal `L^(n+4)` Koch--Lamm radii. -/
theorem klHeat1_norm {T t : ℝ} {A₂ Aₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f : ℝ × V → F) (x : V)
    (h : KLSource1 T A₂ Aₚ f) :
    (↑‖klHeat1 t w f x‖₊ : ℝ≥0∞) ≤
      ENNReal.ofReal ‖w‖ * earlyFluxC V * (A₂ : ℝ≥0∞) *
          fluxShellSeries (Module.finrank ℝ V) +
        ENNReal.ofReal
          (klFluxSeries (Module.finrank ℝ V) *
            (‖w‖ * (klFluxTailC V * (Aₚ : ℝ)))) := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hlate := klFluxFull_canon (V := V) h w x hsqrt (by
    simpa only [Real.sq_sqrt ht.le] using htT)
  have hlateE :
      (↑‖klFluxFull1 (V := V) (Real.sqrt t) w f x‖₊ : ℝ≥0∞) ≤
        ENNReal.ofReal
          (klFluxSeries (Module.finrank ℝ V) *
            (‖w‖ * (klFluxTailC V * (Aₚ : ℝ)))) := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal hlate
  have hearly := kl1_early_norm (V := V) ht htT w f x h
  unfold klHeat1
  calc
    (↑‖heatEarly1 t w f x +
        klFluxFull1 (V := V) (Real.sqrt t) w f x‖₊ : ℝ≥0∞) ≤
        (↑‖heatEarly1 t w f x‖₊ : ℝ≥0∞) +
          (↑‖klFluxFull1 (V := V) (Real.sqrt t) w f x‖₊ : ℝ≥0∞) := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        ← ofReal_norm_eq_enorm,
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ ≤ ENNReal.ofReal ‖w‖ * earlyFluxC V * (A₂ : ℝ≥0∞) *
          fluxShellSeries (Module.finrank ℝ V) +
        ENNReal.ofReal
          (klFluxSeries (Module.finrank ℝ V) *
            (‖w‖ * (klFluxTailC V * (Aₚ : ℝ)))) :=
      add_le_add hearly hlateE

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
