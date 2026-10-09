import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalCGTInjectivity


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private local instance selectedInjMeasurableE : MeasurableSpace E := borel E
private local instance selectedInjBorelE : BorelSpace E := ⟨rfl⟩

def selectedCGTDenominator (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (R : ℝ) : ℝ :=
  1 + ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
      Set.univ).toReal * hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8) +
    ((volume : Measure E).toSphere Set.univ).toReal *
      hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4)


def selectedCGTInjRadius (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (kappa R : ℝ) : ℝ :=
  (R / 16) * (kappa * (R / 8) ^ Module.finrank ℝ E) / selectedCGTDenominator E R

theorem selectedCGTDenominator_pos {R : ℝ} (hR : 0 < R) :
    0 < selectedCGTDenominator E R := by
  have hsmall : 0 ≤ hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8) :=
    (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  have hlarge : 0 ≤ hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4) :=
    (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  unfold selectedCGTDenominator
  positivity

theorem selectedCGTInjRadius_pos {kappa R : ℝ} (hκ : 0 < kappa) (hR : 0 < R) :
    0 < selectedCGTInjRadius E kappa R := by
  unfold selectedCGTInjRadius
  exact div_pos (mul_pos (by positivity) (mul_pos hκ (pow_pos (by positivity) _)))
    (selectedCGTDenominator_pos (E := E) hR)

variable [NeZero (Module.finrank ℝ E)]

theorem selectedCGTInjRadius_le_quotient {kappa R : ℝ}
    (hκ : 0 ≤ kappa) (hR : 0 < R) :
    ENNReal.ofReal (selectedCGTInjRadius E kappa R) ≤
      ENNReal.ofReal (R / 16) *
        (ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E) /
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
            Set.univ * ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8)) +
          (volume : Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4))) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  have hfin : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  let _ : Nontrivial (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    Module.nontrivial_of_finrank_pos hfin
  let b : ℝ := ((volume : Measure (EuclideanSpace ℝ
    (Fin (Module.finrank ℝ E)))).toSphere Set.univ).toReal
  let p : ℝ := ((volume : Measure E).toSphere Set.univ).toReal
  let m : ℝ := hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8)
  let l : ℝ := hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4)
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hm : 0 ≤ m := (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  have hl : 0 ≤ l := (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  have hbeq : (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
      Set.univ = ENNReal.ofReal b :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hpeq : (volume : Measure E).toSphere Set.univ = ENNReal.ofReal p :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hden :
      (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ *
          ENNReal.ofReal m + (volume : Measure E).toSphere Set.univ * ENNReal.ofReal l ≤
        ENNReal.ofReal (selectedCGTDenominator E R) := by
    rw [hbeq, hpeq, ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul hp,
      ← ENNReal.ofReal_add (mul_nonneg hb hm) (mul_nonneg hp hl)]
    apply ENNReal.ofReal_le_ofReal
    change b * m + p * l ≤ 1 + b * m + p * l
    linarith
  rw [selectedCGTInjRadius,
    ENNReal.ofReal_div_of_pos (selectedCGTDenominator_pos (E := E) hR),
    ENNReal.ofReal_mul (by positivity : 0 ≤ R / 16), ENNReal.ofReal_mul hκ,
    ENNReal.ofReal_pow (by positivity : 0 ≤ R / 8)]
  exact ENNReal.div_le_div le_rfl hden


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
