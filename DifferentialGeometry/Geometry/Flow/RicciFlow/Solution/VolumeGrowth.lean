import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeVariation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (compact_ricciFlow_volumeVariation_on_regular)
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

namespace SolutionOn

theorem hasDerivAt_volume (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {t : ℝ} (ht : t ∈ D.regular) :
    HasDerivAt
      (fun s : ℝ => (riemannianVolumeMeasure I M (S.family.metric s) univ).toReal)
      (-(∫ x, S.scalar t x ∂riemannianVolumeMeasure I M (S.family.metric t))) t := by
  have h := compact_ricciFlow_volumeVariation_on_regular S hS
    (fun _ _ => (1 : ℝ)) contMDiffOn_const ht
  simpa only [deriv_const, mul_one, zero_sub, integral_neg, integral_const,
    smul_eq_mul, Measure.real_def] using h

theorem hasDerivAt_exp_mul_volume (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (K : ℝ) {t : ℝ} (ht : t ∈ D.regular) :
    HasDerivAt
      (fun s : ℝ => Real.exp (-K * s) *
        (riemannianVolumeMeasure I M (S.family.metric s) univ).toReal)
      (∫ x, (Real.exp (-K * t) * (-K) - S.scalar t x * Real.exp (-K * t))
        ∂riemannianVolumeMeasure I M (S.family.metric t)) t := by
  have hweight : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (fun s : ℝ => Real.exp (-K * s)) := by
    rw [contMDiff_iff_contDiff]
    exact Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hweight' : HasDerivAt (fun s : ℝ => Real.exp (-K * s))
      (Real.exp (-K * t) * (-K)) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (-K)).exp
  have h := compact_ricciFlow_volumeVariation_on_regular S hS
    (fun s _ => Real.exp (-K * s)) (hweight.comp contMDiff_fst).contMDiffOn ht
  simp only [hweight'.deriv, integral_const, smul_eq_mul, Measure.real_def] at h
  convert h using 1
  funext s
  exact mul_comm _ _

theorem antitoneOn_exp_mul_volume (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (K : ℝ) {J : Set ℝ} (hJ : Convex ℝ J)
    (hregular : J ⊆ D.regular) (hscalar : ∀ t ∈ J, ∀ x : M, -K ≤ S.scalar t x) :
    AntitoneOn
      (fun t : ℝ => Real.exp (-K * t) *
        (riemannianVolumeMeasure I M (S.family.metric t) univ).toReal) J := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos hJ
  · intro t ht
    exact (S.hasDerivAt_exp_mul_volume hS K (hregular ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (S.hasDerivAt_exp_mul_volume hS K
      (hregular (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    apply integral_nonpos
    intro x
    have hbound := hscalar t (interior_subset ht) x
    have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-K * t)).le
    change Real.exp (-K * t) * (-K) - S.scalar t x * Real.exp (-K * t) ≤ 0
    nlinarith

end SolutionOn

end DifferentialGeometry.PDE.RicciFlow
