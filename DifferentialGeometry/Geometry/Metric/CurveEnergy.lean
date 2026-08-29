import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Metric.DistanceScaling
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def curveEnergy (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b,
    g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))

theorem curveEnergy_mono (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    {a s t b : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hE : IntegrableOn (fun u =>
      g.inner (γ u)
        (mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ))) (Set.Icc a b)) :
    curveEnergy (I := I) g γ s t ≤ curveEnergy (I := I) g γ a b := by
  apply intervalIntegral.integral_mono_interval has hst htb
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    let v := mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ)
    rcases eq_or_ne v 0 with hv | hv
    · simp only [v, hv, map_zero]
      exact le_rfl
    · exact (g.pos (γ u) v hv).le
  · apply MeasureTheory.IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le (has.trans (hst.trans htb))] using hE

private lemma int_sqrt_le {q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hq0 : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (hq : IntegrableOn q (Set.Icc a b)) :
    ∫ t in a..b, Real.sqrt (q t) ≤
      Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, q t) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hqIoc : Integrable q μ := hq.mono_set Set.Ioc_subset_Icc_self
  have hqae : 0 ≤ᵐ[μ] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hq0 t ⟨ht.1.le, ht.2⟩
  have hsqrt_meas : AEStronglyMeasurable (fun t => Real.sqrt (q t)) μ :=
    (hqIoc.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hsqrt_mem_two : MemLp (fun t => Real.sqrt (q t)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hsqrt_meas]
    exact hqIoc.congr (hqae.mono fun t ht => (Real.sq_sqrt ht).symm)
  have hsqrt_mem : MemLp (fun t => Real.sqrt (q t)) (ENNReal.ofReal 2) μ := by
    norm_num at hsqrt_mem_two ⊢
    exact hsqrt_mem_two
  have hone_mem : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    simpa using (memLp_const (p := (2 : ℝ≥0∞)) (1 : ℝ) :
      MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (ae_of_all _ fun t => Real.sqrt_nonneg (q t))
    (ae_of_all _ fun _ => zero_le_one) hsqrt_mem hone_mem
  have hsquares : ∫ t, Real.sqrt (q t) ^ (2 : ℝ) ∂μ = ∫ t, q t ∂μ := by
    exact integral_congr_ae (hqae.mono fun t ht => by
      change Real.sqrt (q t) ^ (2 : ℝ) = q t
      rw [Real.rpow_two, Real.sq_sqrt ht])
  have hone : ∫ _ : ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ = b - a := by
    simp [μ, hab]
  rw [hsquares, hone, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  change ∫ t, Real.sqrt (q t) ∂μ ≤
    Real.sqrt (b - a) * Real.sqrt (∫ t, q t ∂μ)
  calc
    ∫ t, Real.sqrt (q t) ∂μ = ∫ t, Real.sqrt (q t) * 1 ∂μ := by simp
    _ ≤ Real.sqrt (∫ t, q t ∂μ) * Real.sqrt (b - a) := hholder
    _ = Real.sqrt (b - a) * Real.sqrt (∫ t, q t ∂μ) := mul_comm _ _

theorem arcLength_le_energy (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hE : IntegrableOn (fun t =>
      g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (Set.Icc a b)) :
    Variation.arcLength (I := I) g γ a b ≤
      Real.sqrt (b - a) * Real.sqrt (curveEnergy (I := I) g γ a b) := by
  exact int_sqrt_le hab
    (fun t _ => by
      let v := mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)
      rcases eq_or_ne v 0 with hv | hv
      · simp only [v, hv, map_zero]
        exact le_rfl
      · exact (g.pos (γ t) v hv).le) hE

theorem edistOf_le_energy (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b))
    (hE : IntegrableOn (fun t =>
      g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (Set.Icc a b)) :
    riemannianEDistOf (I := I) g (γ a) (γ b) ≤
      ENNReal.ofReal
        (Real.sqrt (b - a) * Real.sqrt (curveEnergy (I := I) g γ a b)) := by
  let rb : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdist := Geodesic.riemannianEDist_le_arcLength (I := I) g hab hγ
    (fun t _ => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
  have hlength := arcLength_le_energy (I := I) g hab hE
  simpa only [riemannianEDistOf] using
    hdist.trans (ENNReal.ofReal_le_ofReal hlength)

theorem edistOf_le_budget (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b C : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b))
    (hE : IntegrableOn (fun t =>
      g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (Set.Icc a b))
    (hEC : curveEnergy (I := I) g γ a b ≤ C) :
    riemannianEDistOf (I := I) g (γ a) (γ b) ≤
      ENNReal.ofReal (Real.sqrt (b - a) * Real.sqrt C) := by
  refine (edistOf_le_energy (I := I) g hab hγ hE).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEC) (Real.sqrt_nonneg _)

end Riemannian
end Geometry
end DifferentialGeometry
