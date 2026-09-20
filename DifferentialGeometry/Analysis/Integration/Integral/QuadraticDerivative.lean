import DifferentialGeometry.Analysis.Integration.Lp.QuadraticDomination
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import DifferentialGeometry.Analysis.Integration.Lp.QuadraticConvergence
import DifferentialGeometry.Analysis.Integration.Lp.Compact
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [SecondCountableTopology F]

theorem tendsto_integral_quadratic_fderiv_of_eventually_lipschitz
    (f : ℕ → ℂ → F) (S : ℕ → Set ℂ) (hS : ∀ n, IsCompact (S n))
    {K : Set F} (hK : IsCompact K) (A : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hA : ContinuousOn A K)
    (hf : ∀ᶠ n in atTop, (∃ C : ℝ≥0, LipschitzWith C (f n)) ∧ MapsTo (f n) (S n) K)
    (hlim : Tendsto (fun n => ∫ z in S n,
      (‖fderiv ℝ (f n) z 1‖ ^ 2 + ‖fderiv ℝ (f n) z Complex.I‖ ^ 2) / 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z in S n,
      (A (f n z) (fderiv ℝ (f n) z 1) (fderiv ℝ (f n) z 1) +
        A (f n z) (fderiv ℝ (f n) z Complex.I) (fderiv ℝ (f n) z Complex.I)) / 2)
      atTop (𝓝 0) := by
  borelize F
  have hnorm : ContinuousOn (fun x => ‖A x‖) K := by
    exact (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnorm
  apply squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hlim.const_mul C)
  filter_upwards [hf] with n hn
  obtain ⟨⟨J, hJ⟩, hmap⟩ := hn
  let μ : Measure ℂ := volume.restrict (S n)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (hS n).measure_ne_top
  have hm (w : ℂ) : MemLp (fun z => fderiv ℝ (f n) z w) 2 μ := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ (f n) w).aestronglyMeasurable
      ((J : ℝ) * ‖w‖)
    exact Eventually.of_forall fun z => ((fderiv ℝ (f n) z).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hJ) (norm_nonneg w))
  have hAc : ContinuousOn (fun z => A (f n z)) (S n) :=
    hA.comp hJ.continuous.continuousOn hmap
  have hAm (v w : F) : AEStronglyMeasurable (fun z => A (f n z) v w) μ :=
    ((hAc.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      (hS n).measurableSet
  have hAb : ∀ᵐ z ∂μ, ‖A (f n z)‖ ≤ C := by
    filter_upwards [ae_restrict_mem (hS n).measurableSet] with z hz
    exact hC (mem_image_of_mem (fun x => ‖A x‖) (hmap hz))
  exact norm_integral_quadratic_add_div_two_le (fun z => A (f n z)) hAm hAb (hm 1) (hm Complex.I)

end Normed

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem tendsto_integral_target_metric_energy_of_strong_approximation
    {S T : Set E} (hT : MeasurableSet T) (hTS : T ⊆ S)
    {K : Set F} (hK : IsCompact K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K)
    (f : E → F) (u : ℕ → E → F)
    (hu : ∀ n, ContDiffOn ℝ 1 (u n) S)
    (huK : ∀ n, MapsTo (u n) S K)
    (hfK : ∀ᵐ x ∂volume.restrict T, f x ∈ K)
    (hae : ∀ᵐ x ∂volume.restrict T, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    (G : Fin d → E → F) (hG : ∀ j, MemLp (G j) 2 (volume.restrict T))
    (hdu : ∀ n j, MemLp (fun x => fderiv ℝ (u n) x (EuclideanSpace.single j 1))
      2 (volume.restrict T))
    (hder : ∀ j, Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (u n) x (EuclideanSpace.single j 1) - G j x) 2 (volume.restrict T))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∑ j : Fin d, ∫ x in T,
      A (u n x) (fderiv ℝ (u n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (u n) x (EuclideanSpace.single j 1))) atTop
      (𝓝 (∑ j : Fin d, ∫ x in T, A (f x) (G j x) (G j x))) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => A (u n x)) (volume.restrict T) :=
    ((hA.comp (hu n).continuousOn (huK n)).mono hTS).aestronglyMeasurable hT
  have hAnorm : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hAnorm
  have hb (n : ℕ) : ∀ᵐ x ∂volume.restrict T, ‖A (u n x)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hT] with x hx
    exact (le_abs_self _).trans (hC _ (huK n (hTS hx)))
  have hc : ∀ᵐ x ∂volume.restrict T, Tendsto (fun n => A (u n x)) atTop (𝓝 (A (f x))) := by
    filter_upwards [hae, hfK, ae_restrict_mem hT] with x hx hxK hxT
    exact (hA (f x) hxK).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hx, Filter.Eventually.of_forall fun n => huK n (hTS hxT)⟩)
  apply tendsto_finsetSum
  intro j _
  exact tendsto_integral_quadratic_of_tendsto_eLpNorm_of_ae_tendsto
    (fun n x => A (u n x)) (fun x => A (f x)) hm hb hc
    (fun n x => fderiv ℝ (u n) x (EuclideanSpace.single j 1)) (G j)
    (fun n => hdu n j) (hG j) (hder j)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
