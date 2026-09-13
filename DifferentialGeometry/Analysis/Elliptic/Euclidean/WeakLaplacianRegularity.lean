import DifferentialGeometry.Analysis.Elliptic.Euclidean.GradientEstimate
import DifferentialGeometry.Analysis.Integration.Convolution.Laplacian
import DifferentialGeometry.Analysis.Schauder.Holder.DerivativeLimit
import DifferentialGeometry.Analysis.Integration.Convolution.Approximation
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatSemigroup.Schauder
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Convolution NNReal
namespace DifferentialGeometry.Analysis
open Parabolic.Euclidean Schauder

theorem exists_holder_fderiv_of_bounded_weak_laplacian
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u g : V → F} (hu : Continuous u) (hcu : HasCompactSupport u)
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (hw : ∀ φ : V → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, Laplacian.laplacian φ y • u y) = ∫ y, φ y • g y)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ContDiff ℝ 1 u ∧ HolderWith C α (fderiv ℝ u) := by
  have hB0 : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  obtain ⟨M, hM⟩ := hcu.exists_bound_of_continuous hu
  have hM0 : 0 ≤ M := (norm_nonneg (u 0)).trans (hM 0)
  let φ (n : ℕ) : ContDiffBump (0 : V) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  let v (n : ℕ) : V → F := (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u
  have hvc (n : ℕ) : ContDiff ℝ ∞ (v n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hu.locallyIntegrable
  have hv2 (n : ℕ) : ContDiff ℝ 2 (v n) := (hvc n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hcs (n : ℕ) : HasCompactSupport (v n) :=
    (φ n).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcu
  have hconvnorm {f : V → F} {A : ℝ} (hf : AEStronglyMeasurable f volume)
      (hA : ∀ x, ‖f x‖ ≤ A) (n : ℕ) (x : V) :
      ‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ≤ A := by
    have hA0 : 0 ≤ A := (norm_nonneg (f 0)).trans (hA 0)
    simpa only [dist_zero_right] using
      dist_convolution_le (x₀ := x) (z₀ := 0) hA0 (φ n).support_normed_eq.subset (φ n).nonneg_normed
        (φ n).integral_normed hf (fun y _ => by simpa only [dist_zero_right] using hA y)
  have hvM (n : ℕ) (x : V) : ‖v n x‖ ≤ M := hconvnorm hu.aestronglyMeasurable hM n x
  have hvB (n : ℕ) (x : V) : ‖Laplacian.laplacian (v n) x‖ ≤ B := by
    change ‖Laplacian.laplacian ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u) x‖ ≤ B
    rw [laplacian_convolution_of_weak_laplacian hu.locallyIntegrable hw
      (φ n).contDiff_normed (φ n).hasCompactSupport_normed]
    exact hconvnorm hg hB n x
  have hC0 : 0 ≤ (heatC2 V + 2 * heatC1 V) * (M + 2 * B / (1 - (α : ℝ))) := by
    have h1 := heatC1_nonneg (V := V)
    have h2 := heatC2_nonneg (V := V)
    have ha : (α : ℝ) < 1 := hα1
    positivity
  let C : ℝ≥0 := ⟨(heatC2 V + 2 * heatC1 V) * (M + 2 * B / (1 - (α : ℝ))), hC0⟩
  have hvhold (n : ℕ) : HolderWith C α (fderiv ℝ (v n)) := by
    intro x y
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow]
    change dist (fderiv ℝ (v n) x) (fderiv ℝ (v n) y) ≤
      (heatC2 V + 2 * heatC1 V) * (M + 2 * B / (1 - (α : ℝ))) * dist x y ^ (α : ℝ)
    have hh := norm_fderiv_sub_le_of_laplacian_bound (hv2 n) (hcs n) hα1
      (t := 1) zero_lt_one (hvM n) (hvB n) x y
    simpa only [Real.one_rpow, mul_one, dist_eq_norm] using hh
  have hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hun : TendstoUniformly v u atTop :=
    ContDiffBump.tendstoUniformly_normed_convolution hr (hcu.uniformContinuous_of_continuous hu)
  have hd := differentiable_of_tendstoUniformly_of_holder_fderiv hα
    (fun n => (hv2 n).differentiable (by norm_num)) hvhold hun
  have hh := holder_fderiv_of_tendstoUniformly hα
    (fun n => (hv2 n).differentiable (by norm_num)) hvhold hun
  refine ⟨C, ?_, hh⟩
  exact contDiff_one_iff_fderiv.mpr ⟨hd, hh.continuous hα⟩

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem heatSup_lipschitzWith [Nontrivial V] {t : ℝ} (ht : 0 < t) (x : V) :
    LipschitzWith 1 (fun u : BoundedContinuousFunction V F => heatSup t u x) := by
  apply LipschitzWith.mk_one
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  change ‖supKernel (heatKernel t) u x - supKernel (heatKernel t) v x‖ ≤ ‖u - v‖
  rw [← supKernel_sub (heatKernel_int ht)]
  exact heatSup_contract ht (u - v) x

omit [CompleteSpace F] in
private theorem heatDuhamel_const_lipschitzWith [Nontrivial V] {t : ℝ} (ht : 0 < t) (x : V) :
    LipschitzWith ⟨t, ht.le⟩
      (fun u : BoundedContinuousFunction V F => heatDuhamel t (fun _ => u) x) := by
  have hmeas (u : BoundedContinuousFunction V F) :=
    heatSup_timeSource_aestronglyMeasurable_of_continuousOn ht.le (fun _ => u)
      (u.continuous.comp continuous_snd).continuousOn x
  have hint (u : BoundedContinuousFunction V F) :=
    heatDuhamel_int ht (fun _ => u) (K := ‖u‖₊) (fun _ _ => le_rfl) x (hmeas u)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  change ‖heatDuhamel t (fun _ => u) x - heatDuhamel t (fun _ => v) x‖ ≤ t * ‖u - v‖
  have he : heatDuhamel t (fun _ => u) x - heatDuhamel t (fun _ => v) x =
      heatDuhamel t (fun _ => u - v) x := by
    unfold heatDuhamel
    rw [← intervalIntegral.integral_sub (hint u) (hint v)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ s : ℝ ∂volume, s ≠ t by simp [ae_iff, measure_singleton]] with s hst hs
    rw [uIoc_of_le ht.le] at hs
    exact (supKernel_sub (heatKernel_int (sub_pos.mpr (lt_of_le_of_ne hs.2 hst))) u v x).symm
  rw [he]
  exact heatDuhamel_norm ht (fun _ => u - v) (K := ‖u - v‖₊) (fun _ _ => le_rfl) x (hmeas _)

private theorem eq_heatSup_sub_heatDuhamel_of_weak_laplacian [Nontrivial V]
    (u g : BoundedContinuousFunction V F) (hcu : HasCompactSupport (u : V → F))
    (hg : UniformContinuous (g : V → F))
    (hw : ∀ φ : V → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, Laplacian.laplacian φ y • u y) = ∫ y, φ y • g y)
    {t : ℝ} (ht : 0 < t) (x : V) :
    u x = heatSup t u x - heatDuhamel t (fun _ => g) x := by
  let φ (n : ℕ) : ContDiffBump (0 : V) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  let v (n : ℕ) : V → F := (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u
  have hvc (n : ℕ) : ContDiff ℝ ∞ (v n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      u.continuous.locallyIntegrable
  have hv2 (n : ℕ) : ContDiff ℝ 2 (v n) :=
    (hvc n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hcs (n : ℕ) : HasCompactSupport (v n) :=
    (φ n).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcu
  let un (n : ℕ) : BoundedContinuousFunction V F :=
    (⟨⟨v n, (hv2 n).continuous⟩, hcs n⟩ : CompactlySupportedContinuousMap V F).toBoundedContinuousFunction
  have hgc (n : ℕ) : Continuous (Laplacian.laplacian (v n)) :=
    continuous_iff_continuousAt.mpr (fun _ => (hv2 n).contDiffAt.continuousAt_laplacian)
  have hcg (n : ℕ) : HasCompactSupport (Laplacian.laplacian (v n)) :=
    (hcs n).of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset _)
  let gn (n : ℕ) : BoundedContinuousFunction V F :=
    (⟨⟨Laplacian.laplacian (v n), hgc n⟩, hcg n⟩ :
      CompactlySupportedContinuousMap V F).toBoundedContinuousFunction
  have hge (n : ℕ) : (gn n : V → F) =
      (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g := by
    funext y
    exact laplacian_convolution_of_weak_laplacian u.continuous.locallyIntegrable hw
      (φ n).contDiff_normed (φ n).hasCompactSupport_normed y
  have hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hun : Tendsto un atTop (𝓝 u) :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
      (ContDiffBump.tendstoUniformly_normed_convolution hr (hcu.uniformContinuous_of_continuous u.continuous))
  have hgn : Tendsto gn atTop (𝓝 g) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    simpa only [hge] using ContDiffBump.tendstoUniformly_normed_convolution hr hg
  have hid (n : ℕ) : un n x = heatSup t (un n) x - heatDuhamel t (fun _ => gn n) x :=
    eq_heatSup_sub_heatDuhamel_of_laplacian_eq (un n) (gn n) (hv2 n) (hcs n) (fun _ => rfl) ht x
  apply tendsto_nhds_unique
    ((BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hun).tendsto_at x)
  have htend := ((heatSup_lipschitzWith ht x).continuous.tendsto u |>.comp hun).sub
    ((heatDuhamel_const_lipschitzWith ht x).continuous.tendsto g |>.comp hgn)
  exact htend.congr (fun n => (hid n).symm)

theorem contDiff_two_of_holder_weak_laplacian
    {u g : V → F} (hu : Continuous u) (hcu : HasCompactSupport u)
    {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (hw : ∀ φ : V → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, Laplacian.laplacian φ y • u y) = ∫ y, φ y • g y)
    {α K : ℝ≥0} (hα : 0 < α) (hg : HolderWith K α g) : ContDiff ℝ 2 u := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · let : Subsingleton V := hV
    have he : u = fun _ : V => u 0 := funext (fun x => congrArg u (Subsingleton.elim x 0))
    rw [he]
    exact contDiff_const
  · let : Nontrivial V := hV
    let ub : BoundedContinuousFunction V F :=
      (⟨⟨u, hu⟩, hcu⟩ : CompactlySupportedContinuousMap V F).toBoundedContinuousFunction
    let gb : BoundedContinuousFunction V F :=
      ⟨⟨g, hg.continuous hα⟩, ⟨2 * B, fun x y => by
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans (by linarith [hB x, hB y])⟩⟩
    have he : u = (fun x => heatSup 1 ub x) - heatDuhamel 1 (fun _ => gb) := by
      funext x
      exact eq_heatSup_sub_heatDuhamel_of_weak_laplacian ub gb hcu
        (hg.uniformContinuous hα) hw zero_lt_one x
    rw [he]
    exact (heatSup_contDiff_two zero_lt_one ub).sub
      (heatDuhamel_const_contDiff_two hα zero_lt_one gb hg)


end DifferentialGeometry.Analysis
