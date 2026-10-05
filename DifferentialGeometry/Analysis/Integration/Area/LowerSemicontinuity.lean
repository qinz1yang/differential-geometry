import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section

open MeasureTheory Set Filter
open DifferentialGeometry.Topology (closedDisk)
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuous_euclideanAreaDensity_fderiv :
    Continuous fun A : ℂ →L[ℝ] E => twoJacobian (A 1) (A Complex.I) := by
  unfold twoJacobian
  fun_prop

theorem tendsto_euclideanAreaDensity_of_tendsto_fderiv {u : ℂ → E} {v : ℕ → ℂ → E} {z : ℂ}
    (h : Tendsto (fun j => fderiv ℝ (v j) z) atTop (𝓝 (fderiv ℝ u z))) :
    Tendsto (fun j => euclideanAreaDensity (v j) z) atTop (𝓝 (euclideanAreaDensity u z)) :=
  (continuous_euclideanAreaDensity_fderiv.tendsto (fderiv ℝ u z)).comp h

section FiniteDimensional

variable [FiniteDimensional ℝ E]

theorem lintegral_euclideanAreaDensity_le_liminf {u : ℂ → E} {v : ℕ → ℂ → E} {s : Set ℂ}
    (h : ∀ᵐ z ∂(volume.restrict s),
      Tendsto (fun j => euclideanAreaDensity (v j) z) atTop (𝓝 (euclideanAreaDensity u z))) :
    ∫⁻ z in s, ENNReal.ofReal (euclideanAreaDensity u z) ≤
      liminf (fun j => ∫⁻ z in s, ENNReal.ofReal (euclideanAreaDensity (v j) z)) atTop := by
  have hlim : ∀ᵐ z ∂(volume.restrict s),
      liminf (fun j => ENNReal.ofReal (euclideanAreaDensity (v j) z)) atTop =
        ENNReal.ofReal (euclideanAreaDensity u z) :=
    h.mono fun _ hz => ((ENNReal.continuous_ofReal.tendsto _).comp hz).liminf_eq
  calc
    ∫⁻ z in s, ENNReal.ofReal (euclideanAreaDensity u z)
        = ∫⁻ z in s,
            liminf (fun j => ENNReal.ofReal (euclideanAreaDensity (v j) z)) atTop :=
          (lintegral_congr_ae hlim).symm
    _ ≤ liminf (fun j => ∫⁻ z in s,
            ENNReal.ofReal (euclideanAreaDensity (v j) z)) atTop :=
          lintegral_liminf_le fun j => (measurable_euclideanAreaDensity (v j)).ennreal_ofReal

theorem euclideanArea_le_of_tendsto {u : ℂ → E} {v : ℕ → ℂ → E} {s : Set ℂ} {a : ℝ}
    (hint : ∀ j, IntegrableOn (euclideanAreaDensity (v j)) s)
    (h : ∀ᵐ z ∂(volume.restrict s),
      Tendsto (fun j => euclideanAreaDensity (v j) z) atTop (𝓝 (euclideanAreaDensity u z)))
    (ha : Tendsto (fun j => euclideanArea (v j) s) atTop (𝓝 a)) :
    euclideanArea u s ≤ a := by
  have hle := lintegral_euclideanAreaDensity_le_liminf (u := u) (v := v) (s := s) h
  have hfin : ∀ j, ∫⁻ z in s, ENNReal.ofReal (euclideanAreaDensity (v j) z) =
      ENNReal.ofReal (euclideanArea (v j) s) := fun j => by
    rw [euclideanArea]
    exact (ofReal_integral_eq_lintegral_ofReal (hint j)
      (ae_of_all _ fun z => euclideanAreaDensity_nonneg (v j) z)).symm
  have hlim : liminf (fun j => ∫⁻ z in s, ENNReal.ofReal (euclideanAreaDensity (v j) z))
      atTop = ENNReal.ofReal a := by
    simp only [hfin]
    exact ((ENNReal.continuous_ofReal.tendsto a).comp ha).liminf_eq
  have ha0 : 0 ≤ a :=
    le_of_tendsto_of_tendsto tendsto_const_nhds ha
      (Eventually.of_forall fun j => euclideanArea_nonneg (v j) s)
  calc
    euclideanArea u s
        = (∫⁻ z in s, ENNReal.ofReal (euclideanAreaDensity u z)).toReal :=
          integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => euclideanAreaDensity_nonneg u z)
            (measurable_euclideanAreaDensity u).aestronglyMeasurable
    _ ≤ (ENNReal.ofReal a).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hle.trans_eq hlim)
    _ = a := ENNReal.toReal_ofReal ha0

theorem euclideanArea_le_of_tendsto_fderiv {u : ℂ → E} {v : ℕ → ℂ → E} {s : Set ℂ} {a : ℝ}
    (hint : ∀ j, IntegrableOn (euclideanAreaDensity (v j)) s)
    (h : ∀ᵐ z ∂(volume.restrict s),
      Tendsto (fun j => fderiv ℝ (v j) z) atTop (𝓝 (fderiv ℝ u z)))
    (ha : Tendsto (fun j => euclideanArea (v j) s) atTop (𝓝 a)) :
    euclideanArea u s ≤ a :=
  euclideanArea_le_of_tendsto hint
    (h.mono fun _ hz => tendsto_euclideanAreaDensity_of_tendsto_fderiv hz) ha

theorem euclideanArea_le_of_tendsto_fderiv_of_lipschitz {u : ℂ → E} {v : ℕ → ℂ → E} {s : Set ℂ}
    {a : ℝ} {C : ℝ≥0} [IsFiniteMeasure (volume.restrict s)] (hv : ∀ j, LipschitzWith C (v j))
    (h : ∀ᵐ z ∂(volume.restrict s),
      Tendsto (fun j => fderiv ℝ (v j) z) atTop (𝓝 (fderiv ℝ u z)))
    (ha : Tendsto (fun j => euclideanArea (v j) s) atTop (𝓝 a)) :
    euclideanArea u s ≤ a :=
  euclideanArea_le_of_tendsto_fderiv (fun j => integrableOn_euclideanAreaDensity (hv j) s) h ha

theorem euclideanArea_le_liminf {u : ℂ → E} {v : ℕ → ℂ → E} {s : Set ℂ}
    (hint : ∀ j, IntegrableOn (euclideanAreaDensity (v j)) s)
    (hbdd : ∃ B : ℝ, ∀ j, euclideanArea (v j) s ≤ B)
    (h : ∀ᵐ z ∂(volume.restrict s),
      Tendsto (fun j => euclideanAreaDensity (v j) z) atTop (𝓝 (euclideanAreaDensity u z))) :
    euclideanArea u s ≤ liminf (fun j => euclideanArea (v j) s) atTop := by
  obtain ⟨B, hB⟩ := hbdd
  have hcob : IsCoboundedUnder (· ≥ ·) (atTop : Filter ℕ)
      fun j => euclideanArea (v j) s :=
    isCoboundedUnder_ge_of_le (atTop : Filter ℕ) hB
  have hlow : IsBoundedUnder (· ≥ ·) (atTop : Filter ℕ)
      fun j => euclideanArea (v j) s :=
    isBoundedUnder_of ⟨0, fun j => euclideanArea_nonneg (v j) s⟩
  obtain ⟨φ, hφ, hφ'⟩ := exists_seq_tendsto_liminf hcob hlow
  exact euclideanArea_le_of_tendsto (fun j => hint (φ j))
    (h.mono fun _ hz => hz.comp hφ') hφ

section Disk

local instance : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
  isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne

theorem euclideanDiskArea_le_of_tendsto_fderiv {u : closedDisk → E} {v : ℕ → closedDisk → E}
    {a : ℝ}
    (hint : ∀ j, IntegrableOn (euclideanAreaDensity (diskExtension (v j)))
      (Metric.closedBall 0 1))
    (h : ∀ᵐ z ∂(volume.restrict (Metric.closedBall (0 : ℂ) 1)),
      Tendsto (fun j => fderiv ℝ (diskExtension (v j)) z) atTop
        (𝓝 (fderiv ℝ (diskExtension u) z)))
    (ha : Tendsto (fun j => euclideanDiskArea (v j)) atTop (𝓝 a)) :
    euclideanDiskArea u ≤ a :=
  euclideanArea_le_of_tendsto_fderiv hint h ha

theorem euclideanDiskArea_le_of_tendsto_fderiv_of_lipschitz {u : closedDisk → E}
    {v : ℕ → closedDisk → E} {a : ℝ} {C : ℝ≥0} (hv : ∀ j, LipschitzWith C (v j))
    (h : ∀ᵐ z ∂(volume.restrict (Metric.closedBall (0 : ℂ) 1)),
      Tendsto (fun j => fderiv ℝ (diskExtension (v j)) z) atTop
        (𝓝 (fderiv ℝ (diskExtension u) z)))
    (ha : Tendsto (fun j => euclideanDiskArea (v j)) atTop (𝓝 a)) :
    euclideanDiskArea u ≤ a :=
  euclideanArea_le_of_tendsto_fderiv_of_lipschitz (s := Metric.closedBall 0 1)
    (fun j => diskExtension_lipschitz (hv j)) h ha

end Disk

end FiniteDimensional

end DifferentialGeometry.Geometry
