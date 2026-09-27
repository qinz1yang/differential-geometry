import DifferentialGeometry.Topology.Manifold.AddCircle
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Integration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace (AddCircle (1 : ℝ)) := borel _
private local instance : BorelSpace (AddCircle (1 : ℝ)) := ⟨rfl⟩

private theorem circle_paramDensity_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (x : ℝ) :
    0 < paramDensity g (fun t : ℝ => (t : AddCircle (1 : ℝ))) x := by
  unfold paramDensity paramGramMatrix
  have hdim : Module.finrank ℝ ℝ = 1 := by simp
  let _ : Unique (Fin (Module.finrank ℝ ℝ)) := Equiv.unique (finCongr hdim)
  rw [Matrix.det_unique]
  apply Real.sqrt_pos.mpr
  apply g.pos
  exact fun h => (Tensor.Coordinates.chartModelBasis ℝ).ne_zero default
    ((AddCircle.bijective_mfderiv_coe x).1 (h.trans (map_zero _).symm))

theorem exists_integral_comp_coe_le_mul_riemannianVolumeMeasure
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : AddCircle (1 : ℝ) → ℝ,
      Continuous φ → (∀ z, 0 ≤ φ z) →
      (∫ x in Icc (0 : ℝ) 1, φ (x : AddCircle (1 : ℝ))) ≤
        C * ∫ z, φ z ∂riemannianVolumeMeasure (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) g := by
  let J := paramDensity g (fun t : ℝ => (t : AddCircle (1 : ℝ)))
  have hJ : Continuous J := by
    exact continuousOn_univ.mp (continuousOn_paramDensity g isOpen_univ
      (AddCircle.contMDiff_coe.of_le (by decide)).contMDiffOn)
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hJ.continuousOn
  have hm : 0 < J x₀ := circle_paramDensity_pos g x₀
  let c := Measure.addHaarScalarFactor (modelHaar (E := ℝ)) (volume : Measure ℝ)
  have hc : (0 : ℝ) < c := by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (modelHaar (E := ℝ)) (volume : Measure ℝ)
  refine ⟨((c : ℝ) * J x₀)⁻¹, inv_pos.mpr (mul_pos hc hm), ?_⟩
  intro φ hφ hφ0
  have hφq : Continuous (fun x : ℝ => φ (x : AddCircle (1 : ℝ))) :=
    hφ.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hJi : IntegrableOn (fun x : ℝ => J x * φ (x : AddCircle (1 : ℝ)))
      (Ioc 0 1) := (hJ.mul hφq).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hφi : IntegrableOn (fun x : ℝ => φ (x : AddCircle (1 : ℝ))) (Ioc 0 1) :=
    hφq.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have heq : (∫ z, φ z ∂riemannianVolumeMeasure (I := 𝓘(ℝ, ℝ))
      (M := AddCircle (1 : ℝ)) g) =
      (c : ℝ) * ∫ x in Ioc (0 : ℝ) 1, J x * φ (x : AddCircle (1 : ℝ)) := by
    have he := integral_image_eq_integral_paramDensity_smul g isOpen_univ
      measurableSet_Ioc (subset_univ _)
      (AddCircle.contMDiff_coe.of_le (by decide)).contMDiffOn
      (show InjOn (fun t : ℝ => (t : AddCircle (1 : ℝ))) (Ioc 0 1) from by
        intro x hx y hy hxy
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := (1 : ℝ)) (a := 0)
          (by simpa using hx) (by simpa using hy)).mp hxy)
      φ hφ.aestronglyMeasurable
    rw [show (fun t : ℝ => (t : AddCircle (1 : ℝ))) '' Ioc 0 1 = univ by
      simpa only [zero_add] using AddCircle.coe_image_Ioc_eq (1 : ℝ) (0 : ℝ),
      Measure.restrict_univ] at he
    rw [(modelHaar (E := ℝ)).isAddLeftInvariant_eq_smul (volume : Measure ℝ),
      Measure.restrict_smul, integral_smul_nnreal_measure] at he
    exact he
  have hb : J x₀ * (∫ x in Ioc (0 : ℝ) 1, φ (x : AddCircle (1 : ℝ))) ≤
      ∫ x in Ioc (0 : ℝ) 1, J x * φ (x : AddCircle (1 : ℝ)) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hφi.const_mul _) hJi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_le_mul_of_nonneg_right (hmin (Ioc_subset_Icc_self hx)) (hφ0 _)
  rw [← restrict_Ioc_eq_restrict_Icc]
  rw [heq]
  have hb' := mul_le_mul_of_nonneg_left hb hc.le
  calc
    (∫ x in Ioc (0 : ℝ) 1, φ (x : AddCircle (1 : ℝ))) =
        ((c : ℝ) * J x₀)⁻¹ * ((c : ℝ) *
          (J x₀ * ∫ x in Ioc (0 : ℝ) 1, φ (x : AddCircle (1 : ℝ)))) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr (mul_pos hc hm).le)

end DifferentialGeometry.Integral.Measure
