import DifferentialGeometry.Analysis.Sobolev.Euclidean.Mollification
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Locality
import DifferentialGeometry.Analysis.Integration.Convolution.Approximation
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff Convolution Pointwise

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem tsupport_normed_convolution_subset_cthickening
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ψ : ContDiffBump (0 : E)) (f : E → F) :
    tsupport (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) ⊆
      Metric.cthickening ψ.rOut (tsupport f) := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp
    (support_convolution_subset_swap (ContinuousLinearMap.lsmul ℝ ℝ) hx)
  have hb' : ‖b‖ ≤ ψ.rOut := by
    have hbb : b ∈ Metric.ball (0 : E) ψ.rOut := by
      simpa only [ψ.support_normed_eq] using hb
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hbb : ‖b‖ < ψ.rOut).le
  apply Metric.mem_cthickening_of_dist_le (a + b) a ψ.rOut (tsupport f)
    (subset_tsupport f ha)
  simpa only [dist_eq_norm, add_sub_cancel_left] using hb'

private theorem eLpNorm_restrict_eq_of_ae_zero_on_sdiff
    {F : Type*} [NormedAddCommGroup F] {Ω S : Set E}
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    {f : E → F} {p : ℝ≥0∞}
    (hf : f =ᵐ[volume.restrict (Ω \ S)] (fun _ => 0)) :
    eLpNorm f p (volume.restrict Ω) = eLpNorm f p (volume.restrict S) := by
  classical
  have hz : ∀ᵐ x ∂volume, x ∈ Ω \ S → f x = 0 :=
    (ae_restrict_iff' (hΩ.diff hS)).mp hf
  have heq : f =ᵐ[volume.restrict Ω] S.indicator f := by
    apply (ae_restrict_iff' hΩ).mpr
    filter_upwards [hz] with x hx hxΩ
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
    · rw [Set.indicator_of_notMem hxS]
      exact hx ⟨hxΩ, hxS⟩
  rw [eLpNorm_congr_ae heq, eLpNorm_indicator_eq_eLpNorm_restrict hS,
    Measure.restrict_restrict_of_subset hSΩ]

private theorem weakGrad_columns_ae_zero_on_sdiff
    {ι : Type*} [Finite ι] {Ω S : Set E}
    (hΩ : IsOpen Ω) (hS : IsClosed S)
    {f : E → EuclideanSpace ℝ ι} (hfS : tsupport f ⊆ S)
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω) :
    ∀ᵐ x ∂volume.restrict (Ω \ S), ∀ j : Fin d,
      WithLp.toLp 2 (fun i => (hf i).weakGrad x j) = (0 : EuclideanSpace ℝ ι) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let hz : DeGiorgi.MemW1pWitness 2 (fun _ : E => (0 : ℝ)) Ω :=
    { memLp := MemLp.zero
      weakGrad := fun _ => 0
      weakGrad_component_memLp := fun _ => by
        simpa only [PiLp.zero_apply] using
          (MemLp.zero' : MemLp (fun _ : E => (0 : ℝ)) 2 (volume.restrict Ω))
      isWeakGrad := by intro j φ hφ hφc hφs; simp }
  have heq (i : ι) : (hf i).weakGrad =ᵐ[volume.restrict (Ω \ S)] (fun _ => 0) := by
    apply DeGiorgi.MemW1pWitness.weakGrad_ae_eq_of_ae_eq (by norm_num)
      (hΩ.sdiff hS) sdiff_subset (hf i) hz
    filter_upwards [ae_restrict_mem (hΩ.measurableSet.diff hS.measurableSet)] with x hx
    have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx.2 (hfS h))
    simp only [hfx, PiLp.zero_apply]
  filter_upwards [ae_all_iff.mpr heq] with x hx
  intro j
  ext i
  simp only [PiLp.zero_apply, hx i]

theorem exists_contDiff_compactSupport_tendstoUniformly_weakGrad
    {ι : Type*} [Fintype ι] {Ω : Set E} (hΩ : IsOpen Ω)
    {φ : E → EuclideanSpace ℝ ι} (hφ : Continuous φ) (hφs : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω)
    (hφw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => φ x i) Ω) :
    ∃ (S : Set E) (φn : ℕ → E → EuclideanSpace ℝ ι),
      IsCompact S ∧ S ⊆ Ω ∧ tsupport φ ⊆ S ∧
      (∀ n, ContDiff ℝ ∞ (φn n)) ∧
      (∀ n, HasCompactSupport (φn n)) ∧
      (∀ n, tsupport (φn n) ⊆ S) ∧
      TendstoUniformly φn φ atTop ∧
      ∀ j : Fin d, Tendsto (fun n => eLpNorm (fun x =>
        fderiv ℝ (φn n) x (EuclideanSpace.single j 1) -
          WithLp.toLp 2 (fun i => (hφw i).weakGrad x j))
        2 (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  obtain ⟨δ, hδ, hδΩ⟩ := hφs.isCompact.exists_cthickening_subset_open hΩ hφΩ
  let S : Set E := Metric.cthickening δ (tsupport φ)
  have hS : IsCompact S := hφs.isCompact.cthickening
  have hSΩ : S ⊆ Ω := hδΩ
  have hφS : tsupport φ ⊆ S := Metric.self_subset_cthickening _
  let ε (n : ℕ) : ℝ := δ / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  have hεδ (n : ℕ) : ε n ≤ δ := by
    apply div_le_self hδ.le
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  let ψ (n : ℕ) := mollifierBumpEps (d := d) (hε n)
  let φn (n : ℕ) := (ψ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ
  have hsm (n : ℕ) : ContDiff ℝ ∞ (φn n) :=
    (ψ n).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (ψ n).contDiff_normed hφ.locallyIntegrable
  have hcomp (n : ℕ) : HasCompactSupport (φn n) :=
    (ψ n).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hφs
  have hsupp (n : ℕ) : tsupport (φn n) ⊆ S :=
    (tsupport_normed_convolution_subset_cthickening (ψ n) φ).trans
      (Metric.cthickening_mono (hεδ n) (tsupport φ))
  have hunif : TendstoUniformly φn φ atTop :=
    ContDiffBump.tendstoUniformly_normed_convolution (φ := ψ) (μ := volume) hε0
      (hφs.uniformContinuous_of_continuous hφ)
  have hind : Ω.indicator φ = φ :=
    Set.indicator_eq_self.mpr ((subset_tsupport φ).trans hφΩ)
  have hzero := weakGrad_columns_ae_zero_on_sdiff hΩ hS.isClosed hφS hφw
  refine ⟨S, φn, hS, hSΩ, hφS, hsm, hcomp, hsupp, hunif, ?_⟩
  intro j
  have hlocal := tendsto_eLpNorm_partial_normed_convolution_indicator_sub_weakGrad
    hΩ hS hSΩ hφw hε hε0 j
  rw [hind] at hlocal
  have heq (n : ℕ) : eLpNorm (fun x =>
      fderiv ℝ (φn n) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hφw i).weakGrad x j)) 2 (volume.restrict Ω) =
      eLpNorm (fun x => fderiv ℝ (φn n) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hφw i).weakGrad x j)) 2 (volume.restrict S) := by
    apply eLpNorm_restrict_eq_of_ae_zero_on_sdiff hΩ.measurableSet hS.measurableSet hSΩ
    filter_upwards [hzero, ae_restrict_mem (hΩ.measurableSet.diff hS.measurableSet)] with x hx hxS
    have hxn : x ∉ tsupport (φn n) := fun h => hxS.2 (hsupp n h)
    rw [fderiv_of_notMem_tsupport ℝ hxn, zero_apply, hx j, sub_self]
  simpa only [heq] using hlocal

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
