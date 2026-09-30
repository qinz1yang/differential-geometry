import DifferentialGeometry.Topology.MetricSpace.LipschitzExtension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import DifferentialGeometry.Analysis.Calculus.Interpolation.RadialCone
import DifferentialGeometry.Topology.LoopSpace.ThinAnnulus
import DifferentialGeometry.Topology.MetricSpace.CompactInterpolation
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.MeanValue
import DifferentialGeometry.Analysis.Sobolev.Interpolation.AnnulusEnergy
import DifferentialGeometry.Analysis.Sobolev.Interpolation.Cylinder
import DifferentialGeometry.Analysis.Sobolev.Interpolation.MonotoneBoundary
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.RadialEnergy
import DifferentialGeometry.Analysis.Integration.Integral.ExhaustingBalls

section

noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_lipschitz_inner_disk_rescaling
    {f : ℂ → F} (hf : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ (v : ℂ → F) (L : ℝ≥0), LipschitzWith L v ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, v z = f (a • z) := by
  have hfa : ContDiffOn ℝ 1 f (closedBall (0 : ℂ) a) :=
    hf.mono (closedBall_subset_ball ha1)
  obtain ⟨K, hK⟩ := hfa.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : ℂ) a) (isCompact_closedBall (0 : ℂ) a)
  let e : ℂ →L[ℝ] ℂ := a • ContinuousLinearMap.id ℝ ℂ
  have he : MapsTo e (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) a) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    change ‖a • z‖ ≤ a
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    nlinarith
  have hfe : LipschitzOnWith (K * ‖e‖₊) (f ∘ e) (closedBall (0 : ℂ) 1) :=
    hK.comp e.lipschitzWith.lipschitzOnWith he
  obtain ⟨v, L, hv, heq⟩ := hfe.exists_lipschitz_extension
  exact ⟨v, L, hv, fun z hz => (heq hz).symm⟩

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Filter Metric
open DifferentialGeometry.Topology
open scoped NNReal Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem exists_circle_phase {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ t : ℝ, circleMap 0 1 (2 * Real.pi * t - Real.pi) = z := by
  refine ⟨(Complex.arg z + Real.pi) / (2 * Real.pi), ?_⟩
  have heq : 2 * Real.pi * ((Complex.arg z + Real.pi) / (2 * Real.pi)) - Real.pi =
      Complex.arg z := by field_simp; ring
  rw [heq]
  have h := Complex.norm_mul_exp_arg_mul_I z
  simpa only [circleMap, zero_add, Complex.ofReal_one, one_mul, hz] using h

private theorem shell_projection_distances {a : ℝ} {z : ℂ}
    (haz : a ≤ ‖z‖) (hz : ‖z‖ ≤ 1) :
    dist (thinAnnulusProjection 1 z) z ≤ 1 - a ∧
      dist (a • thinAnnulusProjection 1 z) z ≤ 1 - a := by
  have hp : ‖(radialDirection z : ℂ)‖ = 1 := Circle.norm_coe _
  have heq : z = ‖z‖ • (radialDirection z : ℂ) := (radialDirection_reconstruct z).symm
  have hsub1 : thinAnnulusProjection 1 z - z =
      (1 - ‖z‖) • (radialDirection z : ℂ) := by
    calc
      _ = (1 : ℝ) • (radialDirection z : ℂ) -
          ‖z‖ • (radialDirection z : ℂ) := congrArg₂ (fun x y : ℂ => x - y) rfl heq
      _ = _ := (sub_smul _ _ _).symm
  have hsub2 : a • thinAnnulusProjection 1 z - z =
      (a - ‖z‖) • (radialDirection z : ℂ) := by
    calc
      _ = a • (radialDirection z : ℂ) - ‖z‖ • (radialDirection z : ℂ) := by
        rw [thinAnnulusProjection, one_smul]
        exact congrArg (fun y : ℂ => a • (radialDirection z : ℂ) - y) heq
      _ = _ := (sub_smul _ _ _).symm
  have h1 : dist (thinAnnulusProjection 1 z) z = 1 - ‖z‖ := by
    rw [dist_eq_norm, hsub1, norm_smul,
      Real.norm_eq_abs, hp, mul_one, abs_of_nonneg (sub_nonneg.mpr hz)]
  have h2 : dist (a • thinAnnulusProjection 1 z) z = ‖z‖ - a := by
    rw [dist_eq_norm, hsub2, norm_smul, Real.norm_eq_abs, hp, mul_one,
      abs_of_nonpos (sub_nonpos.mpr haz), neg_sub]
  constructor <;> linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_thin_annulus_recovery_maps
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → F) (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hfD : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    (hfK : MapsTo f (closedBall (0 : ℂ) 1) K)
    (T : F → F) (hT : Differentiable ℝ T) {LT : ℝ≥0}
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hTK : ∀ y ∈ K, T y = y)
    (hTU : MapsTo T U K)
    (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Ioo (0 : ℝ) 1) (halim : Tendsto a atTop (𝓝 1))
    (b : ℕ → ℝ → F) (hb : ∀ n, Function.Periodic (b n) 1)
    (Lb : ℕ → ℝ≥0) (hbLip : ∀ n, LipschitzWith (Lb n) (b n))
    (hbK : ∀ n t, b n t ∈ K)
    (hblim : TendstoUniformly b (fun t => f (circleMap 0 1 (2 * Real.pi * t - Real.pi))) atTop)
    (p : F) :
    ∃ (v : ℕ → ℂ → F) (Lv : ℕ → ℝ≥0),
      (∀ n, LipschitzWith (Lv n) (v n)) ∧
      (∀ n z, z ∈ closedBall (0 : ℂ) 1 → v n z = f (a n • z)) ∧
      let u : ℕ → ℂ → F := fun n => periodicLoopCone p (hb n)
      let W : ℕ → ℂ → F := fun n => attachThinAnnulus (u n) (v n) T 1 (1 - a n)
      (∀ n, ∃ L : ℝ≥0, LipschitzWith L (W n)) ∧
      (∀ n z, ‖z‖ ≤ a n → W n z = f z) ∧
      (∀ n t, W n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = b n t) ∧
      (∀ᶠ n in atTop, MapsTo (W n) (closedBall (0 : ℂ) 1) K) ∧
      TendstoUniformlyOn W f atTop (closedBall (0 : ℂ) 1) := by
  choose v Lv hv hveq using fun n => exists_lipschitz_inner_disk_rescaling hfD (ha n).1 (ha n).2
  let u : ℕ → ℂ → F := fun n => periodicLoopCone p (hb n)
  let W : ℕ → ℂ → F := fun n => attachThinAnnulus (u n) (v n) T 1 (1 - a n)
  have hTLip : LipschitzWith LT T := lipschitzWith_of_nnnorm_fderiv_le hT hLT
  have hau (n : ℕ) : 0 < 1 - a n := sub_pos.mpr (ha n).2
  have hal (n : ℕ) : 1 - a n < 1 := by linarith [(ha n).1]
  have huLip (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (u n) :=
    exists_lipschitzWith_periodicLoopCone p (hb n) (hbLip n)
  have huK (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) : u n z ∈ K := by
    obtain ⟨t, rfl⟩ := exists_circle_phase hz
    rw [show u n = periodicLoopCone p (hb n) from rfl, periodicLoopCone_boundary]
    exact hbK n t
  have hvK (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) : v n z ∈ K := by
    rw [hveq n z (by simpa only [mem_closedBall, dist_zero_right] using hz)]
    apply hfK
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (ha n).1.le]
    exact (mul_le_mul_of_nonneg_left hz (ha n).1.le).trans (by simpa using (ha n).2.le)
  have hfixu (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : T (u n z) = u n z := hTK _ (huK n hz)
  have hfixv (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : T (v n z) = v n z := hTK _ (hvK n hz.le)
  have hWLip (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (W n) := by
    obtain ⟨L, hL⟩ := huLip n
    exact attachThinAnnulus_lipschitz (hau n) (hal n) hL (hv n) hTLip (hfixu n) (hfixv n)
  have hinner (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ a n) : W n z = f z := by
    have hin : ‖z‖ ≤ 1 - (1 - a n) := by linarith
    rw [show W n = attachThinAnnulus (u n) (v n) T 1 (1 - a n) from rfl,
      attachThinAnnulus_inner _ _ _ _ _ hin]
    have hcoef : 1 / (1 - (1 - a n)) = (a n)⁻¹ := by simp only [sub_sub_cancel, one_div]
    rw [hcoef, hveq]
    · congr 1
      rw [smul_smul, mul_inv_cancel₀ (ha n).1.ne', one_smul]
    · rw [mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (ha n).1.le)]
      exact (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (ha n).1.le)).trans_eq
        (inv_mul_cancel₀ (ha n).1.ne')
  have houter (n : ℕ) (t : ℝ) :
      W n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = b n t := by
    rw [show W n = attachThinAnnulus (u n) (v n) T 1 (1 - a n) from rfl,
      attachThinAnnulus_outer _ _ _ (hau n)
        (by simp only [norm_circleMap_zero, abs_one, le_refl])]
    exact periodicLoopCone_boundary p (hb n) t
  have husphere (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ = 1 → dist (u n z) (f z) < ε := by
    filter_upwards [(Metric.tendstoUniformly_iff.mp hblim) ε hε] with n hn z hz
    obtain ⟨t, rfl⟩ := exists_circle_phase hz
    rw [show u n = periodicLoopCone p (hb n) from rfl, periodicLoopCone_boundary, dist_comm]
    exact hn t
  have hfuc : UniformContinuousOn f (closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hf
  have hwidth : Tendsto (fun n => 1 - a n) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub halim
  have hnear (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ z : ℂ,
      a n ≤ ‖z‖ → ‖z‖ ≤ 1 →
      dist (thinAnnulusInterpolation (u n) (v n) 1 (1 - a n) z) (f z) < ε := by
    obtain ⟨δ, hδ, hfδ⟩ := (Metric.uniformContinuousOn_iff.mp hfuc) (ε / 2) (half_pos hε)
    filter_upwards [husphere (ε / 2) (half_pos hε), hwidth.eventually (gt_mem_nhds hδ)]
      with n hn hnδ z haz hz
    let y := thinAnnulusProjection 1 z
    have hy : ‖y‖ = 1 := thinAnnulusProjection_norm (by norm_num) z
    have hyD : y ∈ closedBall (0 : ℂ) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hy.le
    have hzD : z ∈ closedBall (0 : ℂ) 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hayD : a n • y ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (ha n).1.le, hy, mul_one]
      exact (ha n).2.le
    have hd := shell_projection_distances haz hz
    have hfyz : dist (f y) (f z) < ε / 2 := hfδ y hyD z hzD (hd.1.trans_lt hnδ)
    have hfayz : dist (f (a n • y)) (f z) < ε / 2 :=
      hfδ (a n • y) hayD z hzD (hd.2.trans_lt hnδ)
    have hvnear : v n y ∈ ball (f z) ε := by
      rw [mem_ball, hveq n y hyD]
      exact hfayz.trans (half_lt_self hε)
    have hunear : u n y ∈ ball (f z) ε :=
      (dist_triangle (u n y) (f y) (f z)).trans_lt
        ((add_lt_add (hn y hy) hfyz).trans_eq (add_halves ε))
    have ht : thinAnnulusParameter 1 (1 - a n) z ∈ Icc (0 : ℝ) 1 :=
      thinAnnulusParameter_mem_Icc (hau n) ⟨by linarith, hz⟩
    have hc := (convex_ball (f z) ε) hvnear hunear (sub_nonneg.mpr ht.2) ht.1
      (sub_add_cancel 1 (thinAnnulusParameter 1 (1 - a n) z))
    exact hc
  have htarget : ∀ᶠ n in atTop, MapsTo (W n) (closedBall (0 : ℂ) 1) K := by
    obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
    filter_upwards [hnear ε hε] with n hn z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    by_cases hzi : ‖z‖ ≤ a n
    · rw [hinner n z hzi]
      exact hfK hz
    · rw [show W n = attachThinAnnulus (u n) (v n) T 1 (1 - a n) from rfl,
        attachThinAnnulus_shell _ _ _ (hau n) (hal n) (hfixu n) (hfixv n)
          ⟨by linarith [lt_of_not_ge hzi], hz1⟩]
      apply hTU
      apply hεU
      exact Metric.mem_thickening_iff.mpr ⟨f z, hfK hz, hn z (lt_of_not_ge hzi).le hz1⟩
  have hlim : TendstoUniformlyOn W f atTop (closedBall (0 : ℂ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    let δ := ε / ((LT : ℝ) + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    filter_upwards [hnear δ hδ] with n hn z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    by_cases hzi : ‖z‖ ≤ a n
    · rw [hinner n z hzi, dist_self]
      exact hε
    · rw [show W n = attachThinAnnulus (u n) (v n) T 1 (1 - a n) from rfl,
        attachThinAnnulus_shell _ _ _ (hau n) (hal n) (hfixu n) (hfixv n)
          ⟨by linarith [lt_of_not_ge hzi], hz1⟩]
      have h := hTLip.dist_le_mul (f z)
        (thinAnnulusInterpolation (u n) (v n) 1 (1 - a n) z)
      rw [hTK _ (hfK hz)] at h
      have he := hn z (lt_of_not_ge hzi).le hz1
      rw [dist_comm] at he
      have hprod := mul_le_mul_of_nonneg_left he.le LT.coe_nonneg
      have hδeq : ((LT : ℝ) + 1) * δ = ε := by dsimp [δ]; field_simp
      exact h.trans_lt (by nlinarith)
  exact ⟨v, Lv, hv, hveq, hWLip, hinner, houter, htarget, hlim⟩

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis.Sobolev
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis

private theorem lipschitzWith_unit_circle_parameter :
    LipschitzWith ⟨2 * Real.pi, by positivity⟩
      (fun t : ℝ => circleMap 0 1 (2 * Real.pi * t - Real.pi)) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => circleMap 0 1 (2 * Real.pi * t - Real.pi))
      ((2 * Real.pi) • (circleMap 0 1 (2 * Real.pi * t - Real.pi) * Complex.I)) t := by
    have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t - Real.pi) (2 * Real.pi) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const Real.pi
    exact (hasDerivAt_circleMap 0 1 (2 * Real.pi * t - Real.pi)).scomp t hθ
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt)
  intro t
  change ‖deriv (fun t : ℝ => circleMap 0 1 (2 * Real.pi * t - Real.pi)) t‖ ≤ _
  rw [(hd t).deriv]
  simp [abs_of_pos Real.pi_pos]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem tendsto_annulus_energy_attachThinAnnulus_of_scaled_boundary_rates
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    (h : ℕ → ℝ) (hh : ∀ᶠ n in atTop, 0 < h n ∧ h n ≤ 1 / 2)
    (hgap : Tendsto (fun n => (h n)⁻¹ * ∫ t in Icc (0 : ℝ) 1,
      ‖v n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) -
        u n (circleMap 0 1 (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0))
    (hder : Tendsto (fun n => h n * ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => v n (circleMap 0 1 (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
        ‖deriv (fun t => u n (circleMap 0 1 (2 * Real.pi * t - Real.pi))) t‖ ^ 2)
      atTop (𝓝 0))
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L)
    (hTu : ∀ n z, ‖z‖ = 1 → T (u n z) = u n z)
    (hTv : ∀ n z, ‖z‖ = 1 → T (v n z) = v n z) :
    Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h n) 1},
      (‖fderiv ℝ (attachThinAnnulus (u n) (v n) T 1 (h n)) z 1‖ ^ 2 +
        ‖fderiv ℝ (attachThinAnnulus (u n) (v n) T 1 (h n)) z Complex.I‖ ^ 2) / 2)
      atTop (𝓝 0) := by
  let a (n : ℕ) (t : ℝ) := v n (circleMap 0 1 (2 * Real.pi * t - Real.pi))
  let b (n : ℕ) (t : ℝ) := u n (circleMap 0 1 (2 * Real.pi * t - Real.pi))
  have ha (n : ℕ) : LipschitzWith (Kv n * ⟨2 * Real.pi, by positivity⟩) (a n) :=
    (hv n).comp lipschitzWith_unit_circle_parameter
  have hb (n : ℕ) : LipschitzWith (Ku n * ⟨2 * Real.pi, by positivity⟩) (b n) :=
    (hu n).comp lipschitzWith_unit_circle_parameter
  let D (n : ℕ) := ∫ t in Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2
  let J (n : ℕ) := ∫ t in Icc (0 : ℝ) 1, ‖deriv (a n) t‖ ^ 2 + ‖deriv (b n) t‖ ^ 2
  let E (n : ℕ) := ∫ p in Icc (0 : ℝ) (h n) ×ˢ Icc (0 : ℝ) 1,
    (‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) p (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) p (0, 1)‖ ^ 2) / 2
  have hboundlim : Tendsto (fun n => ((h n)⁻¹ * D n + h n * J n) / 2) atTop (𝓝 0) := by
    simpa only [add_zero, zero_div] using (hgap.add hder).div_const 2
  have hE0 : Tendsto E atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun p => by positivity)
      ?_ hboundlim
    filter_upwards [hh] with n hn
    have hbase := integral_energy_affineCylinderInterpolation_le hn.1 (ha n) (hb n)
    apply hbase.trans_eq
    change 1 / (2 * h n) * D n + h n / 2 * J n = _
    ring
  have hTl : LipschitzWith (Real.toNNReal L) T := by
    apply lipschitzWith_of_nnnorm_fderiv_le hT
    intro x
    change ‖fderiv ℝ T x‖ ≤ _
    exact (hL x).trans (Real.le_coe_toNNReal L)
  let Er (n : ℕ) := ∫ p in Icc (0 : ℝ) (h n) ×ˢ Icc (0 : ℝ) 1,
    (‖fderiv ℝ (T ∘ affineCylinderInterpolation (h n) (a n) (b n)) p (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (T ∘ affineCylinderInterpolation (h n) (a n) (b n)) p (0, 1)‖ ^ 2) / 2
  let C : ℝ := (2 * Real.pi) * max 1 (((2 * Real.pi) ^ 2 * (1 / 2))⁻¹)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun n => C * (L ^ 2 * E n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hE0.const_mul (L ^ 2)).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun z => by positivity)
    ?_ hlim
  filter_upwards [hh] with n hn
  have hn1 : h n < 1 := by linarith [hn.2]
  have hAnn := integral_annulus_energy_attachThinAnnulus_le_of_lipschitz
    hn.1 hn1 (hu n) (hv n) hTl (hTu n) (hTv n)
  have hEr : Er n ≤ L ^ 2 * E n :=
    integral_energy_comp_affineCylinderInterpolation_le (h n) (ha n) (hb n) T hT hL
  have hcoef : (2 * Real.pi) * max 1 (((2 * Real.pi) ^ 2 * (1 - h n))⁻¹) ≤ C := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply max_le_max le_rfl
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left
      (by linarith [hn.2] : (1 / 2 : ℝ) ≤ 1 - h n) (sq_nonneg _))
  exact hAnn.trans ((mul_le_mul_of_nonneg_right hcoef
    (integral_nonneg fun p => by positivity)).trans (mul_le_mul_of_nonneg_left hEr hC))

theorem tendsto_annulus_energy_attachThinAnnulus_of_tendsto_width_and_scaled_boundary_rates
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    (h : ℕ → ℝ) (hh : ∀ᶠ n in atTop, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hgap : Tendsto (fun n => (h n)⁻¹ * ∫ t in Icc (0 : ℝ) 1,
      ‖v n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) -
        u n (circleMap 0 1 (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0))
    (hder : Tendsto (fun n => h n * ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => v n (circleMap 0 1 (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
        ‖deriv (fun t => u n (circleMap 0 1 (2 * Real.pi * t - Real.pi))) t‖ ^ 2)
      atTop (𝓝 0))
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L)
    (hTu : ∀ n z, ‖z‖ = 1 → T (u n z) = u n z)
    (hTv : ∀ n z, ‖z‖ = 1 → T (v n z) = v n z) :
    Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h n) 1},
      (‖fderiv ℝ (attachThinAnnulus (u n) (v n) T 1 (h n)) z 1‖ ^ 2 +
        ‖fderiv ℝ (attachThinAnnulus (u n) (v n) T 1 (h n)) z Complex.I‖ ^ 2) / 2)
      atTop (𝓝 0) := by
  apply tendsto_annulus_energy_attachThinAnnulus_of_scaled_boundary_rates u v Ku Kv hu hv h
    (hh.and (hh0.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)))
    hgap hder T hT hL hTu hTv

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Topology NNReal ENNReal ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
private theorem integrable_quadratic_of_compact_image_energy
    {f : ℂ → F} (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hfs : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    (hE : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (ball (0 : ℂ) 1))
    {K : Set F} (hK : IsCompact K) (hfK : MapsTo f (closedBall (0 : ℂ) 1) K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) :
    IntegrableOn (fun z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2)
      (closedBall (0 : ℂ) 1) := by
  have hAfc : ContinuousOn (fun z => A (f z)) (ball (0 : ℂ) 1) :=
    hA.comp (hf.mono ball_subset_closedBall) (hfK.mono_left ball_subset_closedBall)
  have hdfc : ContinuousOn (fderiv ℝ f) (ball (0 : ℂ) 1) :=
    hfs.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  have hc : ContinuousOn (fun z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2)
      (ball (0 : ℂ) 1) :=
    (((hAfc.clm_apply (hdfc.clm_apply continuousOn_const)).clm_apply
        (hdfc.clm_apply continuousOn_const)).add
      ((hAfc.clm_apply (hdfc.clm_apply continuousOn_const)).clm_apply
        (hdfc.clm_apply continuousOn_const))).div_const 2
  obtain ⟨C, hC⟩ := hK.bddAbove_image
    ((@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA)
  have hi : IntegrableOn (fun z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2)
      (ball (0 : ℂ) 1) := by
    apply Integrable.mono' (hE.const_mul (max C 0))
      (hc.aestronglyMeasurable isOpen_ball.measurableSet)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    have hAz : ‖A (f z)‖ ≤ max C 0 :=
      (hC (mem_image_of_mem _ (hfK (ball_subset_closedBall hz)))).trans (le_max_left _ _)
    have h1 : ‖fderiv ℝ f z 1‖ ≤ ‖fderiv ℝ f z‖ := by
      simpa using (fderiv ℝ f z).le_opNorm (1 : ℂ)
    have hI : ‖fderiv ℝ f z Complex.I‖ ≤ ‖fderiv ℝ f z‖ := by
      simpa using (fderiv ℝ f z).le_opNorm Complex.I
    have hbil (v : F) : ‖A (f z) v v‖ ≤ max C 0 * ‖v‖ ^ 2 := by
      have hb := (A (f z)).le_opNorm₂ v v
      have hm := mul_le_mul_of_nonneg_right hAz (sq_nonneg ‖v‖)
      nlinarith
    rw [norm_div, Real.norm_ofNat]
    apply (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    have hb1 := hbil (fderiv ℝ f z 1)
    have hbI := hbil (fderiv ℝ f z Complex.I)
    have hs1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (le_max_right C 0)
    have hsI := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hI 2) (le_max_right C 0)
    nlinarith
  apply hi.mono_set_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : ℂ) 1)]
    with z hz hzc
  exact lt_of_le_of_ne hzc hz

theorem exists_periodic_boundary_energy_recovery
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → F) (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hfs : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    (hfK : MapsTo f (closedBall (0 : ℂ) 1) K)
    (hE : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (ball (0 : ℂ) 1))
    (Γ : ℝ → F) {KΓ : ℝ≥0} (hΓ : LipschitzWith KΓ Γ)
    (hΓper : Function.Periodic Γ 1)
    (ψ : CircleDeg1Lift) (hψ : Continuous ψ)
    (htrace : ∀ s : ℝ, f (circleMap 0 1 (2 * Real.pi * s)) = Γ (ψ s))
    (T : F → F) (hT : Differentiable ℝ T) {LT : ℝ≥0}
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hfix : ∀ y ∈ K, T y = y)
    (hmap : MapsTo T U K) :
    ∃ (fn : ℕ → ℂ → F) (ψn : ℕ → CircleDeg1Lift) (a : ℕ → ℝ),
      (∀ n, ∃ L : ℝ≥0, LipschitzWith L (fn n)) ∧
      (∀ n, LipschitzWith ((3 * (n + 1) : ℕ) : ℝ≥0) (ψn n)) ∧
      (∀ (n i : ℕ), i < 3 * (n + 1) → ∀ t ∈ Icc (i / ((3 * (n + 1) : ℕ) : ℝ))
        ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)),
        ψn n t = ψ (i / ((3 * (n + 1) : ℕ) : ℝ)) +
          (ψ ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)) -
            ψ (i / ((3 * (n + 1) : ℕ) : ℝ))) * (((3 * (n + 1) : ℕ) : ℝ) * t - i)) ∧
      (∀ n, ψn n 0 = ψ 0 ∧ ψn n (1 / 3) = ψ (1 / 3) ∧ ψn n (2 / 3) = ψ (2 / 3)) ∧
      TendstoUniformly (fun n t => ψn n t) ψ atTop ∧
      (∀ n s, fn n (circleMap 0 1 (2 * Real.pi * s)) = Γ (ψn n s)) ∧
      (∀ n, a n ∈ Ioo (0 : ℝ) 1) ∧ Tendsto a atTop (𝓝 1) ∧
      (∀ n, EqOn (fn n) f (closedBall (0 : ℂ) (a n))) ∧
      (∀ᶠ n in atTop, MapsTo (fn n) (closedBall (0 : ℂ) 1) K) ∧
      TendstoUniformlyOn fn f atTop (closedBall (0 : ℂ) 1) ∧
      ∀ (A : F → F →L[ℝ] F →L[ℝ] ℝ), ContinuousOn A K →
        Tendsto (fun n => ∫ z in closedBall (0 : ℂ) 1,
          (A (fn n z) (fderiv ℝ (fn n) z 1) (fderiv ℝ (fn n) z 1) +
            A (fn n z) (fderiv ℝ (fn n) z Complex.I) (fderiv ℝ (fn n) z Complex.I)) / 2)
          atTop (𝓝 (∫ z in closedBall (0 : ℂ) 1,
            (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
              A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2)) := by
  classical
  have hΓK (t : ℝ) : Γ t ∈ K := by
    obtain ⟨s, rfl⟩ := (ψ.continuous_iff_surjective.mp hψ) t
    rw [← htrace s]
    apply hfK
    simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_one, le_refl]
  obtain ⟨ψn, hψLip, hcell, hknots, hmarks, hψconv, hsum⟩ :=
    ψ.exists_uniform_piecewise_affine_sequence hψ
  let N : ℕ → ℕ := fun n => 3 * (n + 1)
  let h : ℕ → ℝ := fun n => (N n : ℝ)⁻¹
  have hNp (n : ℕ) : 0 < (N n : ℝ) := by dsimp only [N]; positivity
  have hh (n : ℕ) : 0 < h n ∧ h n < 1 / 2 := by
    refine ⟨inv_pos.mpr (hNp n), ?_⟩
    dsimp only [h, N]
    rw [inv_eq_one_div, div_lt_iff₀ (by positivity : (0 : ℝ) < ↑(3 * (n + 1)))]
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hNlim : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ N n by dsimp only [N]; omega) tendsto_id
  have hh0 : Tendsto h atTop (𝓝 0) := by
    simpa only [h, one_div, Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hNlim
  let b := fun n t => Γ (ψn n (t - 1 / 2))
  let Kb := fun n => KΓ * (N n : ℝ≥0)
  have hbper (n : ℕ) : Function.Periodic (b n) 1 := by
    intro t
    change Γ (ψn n (t + 1 - 1 / 2)) = Γ (ψn n (t - 1 / 2))
    rw [show t + 1 - 1 / 2 = (t - 1 / 2) + 1 by ring, (ψn n).map_add_one, hΓper]
  have hb (n : ℕ) : LipschitzWith (Kb n) (b n) := by
    have hx := (hΓ.comp (hψLip n)).comp (isometry_add_right (-(1 / 2 : ℝ))).lipschitzWith
    simpa only [b, Kb, N, mul_one, Function.comp_def, sub_eq_add_neg] using hx
  have hbK (n : ℕ) (t : ℝ) : b n t ∈ K := hΓK _
  have hphase (t : ℝ) : f (circleMap 0 1 (2 * Real.pi * t - Real.pi)) =
      Γ (ψ (t - 1 / 2)) := by
    rw [show 2 * Real.pi * t - Real.pi = 2 * Real.pi * (t - 1 / 2) by ring, htrace]
  have hbconv : TendstoUniformly b
      (fun t => f (circleMap 0 1 (2 * Real.pi * t - Real.pi))) atTop := by
    have hc := (hΓ.uniformContinuous.comp_tendstoUniformly hψconv).comp (fun t : ℝ => t - 1 / 2)
    simpa only [Function.comp_def, b, hphase] using hc
  have hb0per (n : ℕ) : Function.Periodic (Γ ∘ ψn n) 1 := by
    intro t
    change Γ (ψn n (t + 1)) = Γ (ψn n t)
    rw [(ψn n).map_add_one, hΓper]
  have hsum0 := hsum.const_mul ((KΓ : ℝ) ^ 2)
  simp only [mul_zero] at hsum0
  have hder0 : Tendsto (fun n => h n * ∫ t in Icc (0 : ℝ) 1, ‖deriv (b n) t‖ ^ 2)
      atTop (𝓝 0) := by
    have he (n : ℕ) := integral_deriv_comp_sub_sq_eq_of_periodic (hb0per n) (1 / 2)
    have hbnd (n : ℕ) := integral_deriv_comp_piecewise_affine_lift_sq_le ψ (ψn n)
      (show 0 < N n by dsimp only [N]; omega) (hcell n) (hψLip n) hΓ
    apply squeeze_zero (fun n => mul_nonneg (hh n).1.le (integral_nonneg fun t => sq_nonneg _))
      (fun n => ?_) hsum0
    change h n * _ ≤ _
    rw [show (∫ t in Icc (0 : ℝ) 1, ‖deriv (b n) t‖ ^ 2) =
        ∫ t in Icc (0 : ℝ) 1, ‖deriv (Γ ∘ ψn n) t‖ ^ 2 from he n]
    exact hbnd n
  have hgap0 : Tendsto (fun n => (h n)⁻¹ * ∫ t in Icc (0 : ℝ) 1,
      ‖f (circleMap 0 1 (2 * Real.pi * t - Real.pi)) - b n t‖ ^ 2) atTop (𝓝 0) := by
    have he (n : ℕ) : (∫ t in Icc (0 : ℝ) 1,
        ‖f (circleMap 0 1 (2 * Real.pi * t - Real.pi)) - b n t‖ ^ 2) =
        ∫ t in Icc (0 : ℝ) 1, ‖Γ (ψn n t) - Γ (ψ t)‖ ^ 2 := by
      simp only [hphase, b, norm_sub_rev (Γ (ψ _))]
      apply integral_Icc_comp_sub_eq_of_periodic
        (f := fun t => ‖Γ (ψn n t) - Γ (ψ t)‖ ^ 2) (d := 1 / 2)
      intro t
      change ‖Γ (ψn n (t + 1)) - Γ (ψ (t + 1))‖ ^ 2 = _
      rw [(ψn n).map_add_one, ψ.map_add_one, hΓper, hΓper]
    have hbnd (n : ℕ) := integral_comp_monotone_lift_sub_sq_le_of_grid_knots ψ (ψn n) hψ
      (show 0 < N n by dsimp only [N]; omega) (hknots n) (hψLip n) hΓ
    apply squeeze_zero (fun n => mul_nonneg (inv_nonneg.mpr (hh n).1.le)
      (integral_nonneg fun t => sq_nonneg _)) (fun n => ?_) hsum0
    rw [he n]
    simpa only [h, inv_inv] using hbnd n
  obtain ⟨a, ha, halim, hgap, hder⟩ := exists_inner_radii_tendsto_scaled_boundary_rates
    hf hfs hE h hh hh0 b Kb hb hgap0 hder0
  have ha01 (n : ℕ) : a n ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [(ha n).1, (ha n).2, (hh n).1, (hh n).2]
  obtain ⟨v, Lv, hv, hveq, hWLip, hcore, hWtrace, hWK, hWlim⟩ :=
    exists_thin_annulus_recovery_maps hK hU hKU f hf hfs hfK T hT hLT hfix hmap
      a ha01 halim b hbper Kb hb hbK hbconv (f 0)
  let u := fun n => periodicLoopCone (f 0) (hbper n)
  let W := fun n => attachThinAnnulus (u n) (v n) T 1 (1 - a n)
  have huLip (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (u n) :=
    exists_lipschitzWith_periodicLoopCone (f 0) (hbper n) (hb n)
  choose Ku hKu using huLip
  have huBoundary (n : ℕ) (t : ℝ) : u n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = b n t :=
    periodicLoopCone_boundary _ _ _
  have hvBoundary (n : ℕ) (t : ℝ) : v n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) =
      f (circleMap 0 (a n) (2 * Real.pi * t - Real.pi)) := by
    rw [hveq n _ (by
      simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_one, le_refl])]
    congr 1
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.real_smul]
  have hfixu (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : T (u n z) = u n z := by
    obtain ⟨t, ht⟩ : ∃ t : ℝ, circleMap 0 1 (2 * Real.pi * t - Real.pi) = z := by
      refine ⟨(Complex.arg z + Real.pi) / (2 * Real.pi), ?_⟩
      have he := Complex.norm_mul_exp_arg_mul_I z
      have heq : 2 * Real.pi * ((Complex.arg z + Real.pi) / (2 * Real.pi)) - Real.pi =
          Complex.arg z := by field_simp; ring
      rw [heq]
      simpa only [circleMap, zero_add, Complex.ofReal_one, one_mul, hz] using he
    rw [← ht, huBoundary]
    exact hfix _ (hbK n t)
  have hfixv (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : T (v n z) = v n z := by
    apply hfix
    rw [hveq n z (by simpa only [mem_closedBall, dist_zero_right, hz] using (le_refl (1 : ℝ)))]
    apply hfK
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (ha01 n).1.le, hz, mul_one]
    exact (ha01 n).2.le
  have hwidth (n : ℕ) : 0 < 1 - a n ∧ 1 - a n ≤ 1 / 2 := by
    constructor <;> linarith [(ha n).1, (ha n).2, (hh n).1, (hh n).2]
  have hgap' : Tendsto (fun n => (1 - a n)⁻¹ * ∫ t in Icc (0 : ℝ) 1,
      ‖v n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) -
        u n (circleMap 0 1 (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0) := by
    simpa only [huBoundary, hvBoundary] using hgap
  have hder' : Tendsto (fun n => (1 - a n) * ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => v n (circleMap 0 1 (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
        ‖deriv (fun t => u n (circleMap 0 1 (2 * Real.pi * t - Real.pi))) t‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [huBoundary, hvBoundary] using hder
  have hshell := tendsto_annulus_energy_attachThinAnnulus_of_scaled_boundary_rates
    u v Ku Lv hKu hv (fun n => 1 - a n) (Eventually.of_forall hwidth) hgap' hder'
    T hT hLT hfixu hfixv
  refine ⟨W, ψn, a, hWLip, hψLip, hcell, hmarks, hψconv, ?_, ha01, halim, ?_, hWK, hWlim, ?_⟩
  · intro n s
    have hh := hWtrace n (s + 1 / 2)
    have heq : 2 * Real.pi * (s + 1 / 2) - Real.pi = 2 * Real.pi * s := by ring
    simpa only [heq, b, add_sub_cancel_right] using hh
  · intro n z hz
    exact hcore n z (by simpa only [mem_closedBall, dist_zero_right] using hz)
  · intro A hA
    apply tendsto_integral_quadratic_fderiv_of_eqOn_exhausting_closedBall halim
      (Eventually.of_forall fun n => (ha01 n).2.le) f W hK A hA
      (hWK.mono fun n hn => ⟨hWLip n, hn⟩)
      (Eventually.of_forall fun n z hz => hcore n z (by
        simpa only [mem_closedBall, dist_zero_right] using hz))
      (integrable_quadratic_of_compact_image_energy hf hfs hE hK hfK A hA)
    simpa only [sub_sub_cancel, dist_zero_right, W] using hshell

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open Set Filter Metric
open DifferentialGeometry.Topology
open scoped NNReal Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_thin_annulus_recovery_maps_in_compact_neighborhood
    {K K' U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → F) (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hfD : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    (hfK : MapsTo f (closedBall (0 : ℂ) 1) K)
    (T : F → F) (hT : Differentiable ℝ T) {LT : ℝ≥0}
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hTK : ∀ y ∈ K, T y = y)
    (hTU : MapsTo T U K')
    (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Ioo (0 : ℝ) 1) (halim : Tendsto a atTop (𝓝 1))
    (b : ℕ → ℝ → F) (hb : ∀ n, Function.Periodic (b n) 1)
    (Lb : ℕ → ℝ≥0) (hbLip : ∀ n, LipschitzWith (Lb n) (b n))
    (hbK : ∀ n t, b n t ∈ K)
    (hblim : TendstoUniformly b (fun t => f (circleMap 0 1 (2 * Real.pi * t - Real.pi))) atTop)
    (p : F) :
    ∃ (v : ℕ → ℂ → F) (Lv : ℕ → ℝ≥0),
      (∀ n, LipschitzWith (Lv n) (v n)) ∧
      (∀ n z, z ∈ closedBall (0 : ℂ) 1 → v n z = f (a n • z)) ∧
      let u : ℕ → ℂ → F := fun n => periodicLoopCone p (hb n)
      let W : ℕ → ℂ → F := fun n => attachThinAnnulus (u n) (v n) T 1 (1 - a n)
      (∀ n, ∃ L : ℝ≥0, LipschitzWith L (W n)) ∧
      (∀ n z, ‖z‖ ≤ a n → W n z = f z) ∧
      (∀ n t, W n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = b n t) ∧
      (∀ᶠ n in atTop, MapsTo (W n) (closedBall (0 : ℂ) 1) K') ∧
      TendstoUniformlyOn W f atTop (closedBall (0 : ℂ) 1) := by
  have hKK' : K ⊆ K' := fun y hy => by
    have hh := hTU (hKU hy)
    rwa [hTK y hy] at hh
  choose v Lv hv hveq using fun n => exists_lipschitz_inner_disk_rescaling hfD (ha n).1 (ha n).2
  let u : ℕ → ℂ → F := fun n => periodicLoopCone p (hb n)
  let W : ℕ → ℂ → F := fun n => attachThinAnnulus (u n) (v n) T 1 (1 - a n)
  have hTLip : LipschitzWith LT T := lipschitzWith_of_nnnorm_fderiv_le hT hLT
  have hau (n : ℕ) : 0 < 1 - a n := sub_pos.mpr (ha n).2
  have hal (n : ℕ) : 1 - a n < 1 := by linarith [(ha n).1]
  have huLip (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (u n) :=
    exists_lipschitzWith_periodicLoopCone p (hb n) (hbLip n)
  have huK (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) : u n z ∈ K := by
    obtain ⟨t, rfl⟩ := exists_circle_phase hz
    rw [show u n = periodicLoopCone p (hb n) from rfl, periodicLoopCone_boundary]
    exact hbK n t
  have hvK (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) : v n z ∈ K := by
    rw [hveq n z (by simpa only [mem_closedBall, dist_zero_right] using hz)]
    apply hfK
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (ha n).1.le]
    exact (mul_le_mul_of_nonneg_left hz (ha n).1.le).trans (by simpa using (ha n).2.le)
  have hfixu (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : T (u n z) = u n z := hTK _ (huK n hz)
  have hfixv (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : T (v n z) = v n z := hTK _ (hvK n hz.le)
  have hWLip (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (W n) := by
    obtain ⟨L, hL⟩ := huLip n
    exact attachThinAnnulus_lipschitz (hau n) (hal n) hL (hv n) hTLip (hfixu n) (hfixv n)
  have hinner (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ a n) : W n z = f z := by
    have hin : ‖z‖ ≤ 1 - (1 - a n) := by linarith
    rw [show W n = attachThinAnnulus (u n) (v n) T 1 (1 - a n) from rfl,
      attachThinAnnulus_inner _ _ _ _ _ hin]
    have hcoef : 1 / (1 - (1 - a n)) = (a n)⁻¹ := by simp only [sub_sub_cancel, one_div]
    rw [hcoef, hveq]
    · congr 1
      rw [smul_smul, mul_inv_cancel₀ (ha n).1.ne', one_smul]
    · rw [mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (ha n).1.le)]
      exact (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (ha n).1.le)).trans_eq
        (inv_mul_cancel₀ (ha n).1.ne')
  have houter (n : ℕ) (t : ℝ) :
      W n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = b n t := by
    rw [show W n = attachThinAnnulus (u n) (v n) T 1 (1 - a n) from rfl,
      attachThinAnnulus_outer _ _ _ (hau n)
        (by simp only [norm_circleMap_zero, abs_one, le_refl])]
    exact periodicLoopCone_boundary p (hb n) t
  have husphere (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ = 1 → dist (u n z) (f z) < ε := by
    filter_upwards [(Metric.tendstoUniformly_iff.mp hblim) ε hε] with n hn z hz
    obtain ⟨t, rfl⟩ := exists_circle_phase hz
    rw [show u n = periodicLoopCone p (hb n) from rfl, periodicLoopCone_boundary, dist_comm]
    exact hn t
  have hfuc : UniformContinuousOn f (closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hf
  have hwidth : Tendsto (fun n => 1 - a n) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub halim
  have hnear (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ z : ℂ,
      a n ≤ ‖z‖ → ‖z‖ ≤ 1 →
      dist (thinAnnulusInterpolation (u n) (v n) 1 (1 - a n) z) (f z) < ε := by
    obtain ⟨δ, hδ, hfδ⟩ := (Metric.uniformContinuousOn_iff.mp hfuc) (ε / 2) (half_pos hε)
    filter_upwards [husphere (ε / 2) (half_pos hε), hwidth.eventually (gt_mem_nhds hδ)]
      with n hn hnδ z haz hz
    let y := thinAnnulusProjection 1 z
    have hy : ‖y‖ = 1 := thinAnnulusProjection_norm (by norm_num) z
    have hyD : y ∈ closedBall (0 : ℂ) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hy.le
    have hzD : z ∈ closedBall (0 : ℂ) 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hayD : a n • y ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (ha n).1.le, hy, mul_one]
      exact (ha n).2.le
    have hd := shell_projection_distances haz hz
    have hfyz : dist (f y) (f z) < ε / 2 := hfδ y hyD z hzD (hd.1.trans_lt hnδ)
    have hfayz : dist (f (a n • y)) (f z) < ε / 2 :=
      hfδ (a n • y) hayD z hzD (hd.2.trans_lt hnδ)
    have hvnear : v n y ∈ ball (f z) ε := by
      rw [mem_ball, hveq n y hyD]
      exact hfayz.trans (half_lt_self hε)
    have hunear : u n y ∈ ball (f z) ε :=
      (dist_triangle (u n y) (f y) (f z)).trans_lt
        ((add_lt_add (hn y hy) hfyz).trans_eq (add_halves ε))
    have ht : thinAnnulusParameter 1 (1 - a n) z ∈ Icc (0 : ℝ) 1 :=
      thinAnnulusParameter_mem_Icc (hau n) ⟨by linarith, hz⟩
    have hc := (convex_ball (f z) ε) hvnear hunear (sub_nonneg.mpr ht.2) ht.1
      (sub_add_cancel 1 (thinAnnulusParameter 1 (1 - a n) z))
    exact hc
  have htarget : ∀ᶠ n in atTop, MapsTo (W n) (closedBall (0 : ℂ) 1) K' := by
    obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
    filter_upwards [hnear ε hε] with n hn z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    by_cases hzi : ‖z‖ ≤ a n
    · rw [hinner n z hzi]
      exact hKK' (hfK hz)
    · rw [show W n = attachThinAnnulus (u n) (v n) T 1 (1 - a n) from rfl,
        attachThinAnnulus_shell _ _ _ (hau n) (hal n) (hfixu n) (hfixv n)
          ⟨by linarith [lt_of_not_ge hzi], hz1⟩]
      apply hTU
      apply hεU
      exact Metric.mem_thickening_iff.mpr ⟨f z, hfK hz, hn z (lt_of_not_ge hzi).le hz1⟩
  have hlim : TendstoUniformlyOn W f atTop (closedBall (0 : ℂ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    let δ := ε / ((LT : ℝ) + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    filter_upwards [hnear δ hδ] with n hn z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    by_cases hzi : ‖z‖ ≤ a n
    · rw [hinner n z hzi, dist_self]
      exact hε
    · rw [show W n = attachThinAnnulus (u n) (v n) T 1 (1 - a n) from rfl,
        attachThinAnnulus_shell _ _ _ (hau n) (hal n) (hfixu n) (hfixv n)
          ⟨by linarith [lt_of_not_ge hzi], hz1⟩]
      have h := hTLip.dist_le_mul (f z)
        (thinAnnulusInterpolation (u n) (v n) 1 (1 - a n) z)
      rw [hTK _ (hfK hz)] at h
      have he := hn z (lt_of_not_ge hzi).le hz1
      rw [dist_comm] at he
      have hprod := mul_le_mul_of_nonneg_left he.le LT.coe_nonneg
      have hδeq : ((LT : ℝ) + 1) * δ = ε := by dsimp [δ]; field_simp
      exact h.trans_lt (by nlinarith)
  exact ⟨v, Lv, hv, hveq, hWLip, hinner, houter, htarget, hlim⟩

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Topology NNReal ENNReal ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_periodic_boundary_energy_recovery_in_compact_neighborhood
    {K K' U : Set F} (hK : IsCompact K) (hK' : IsCompact K') (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → F) (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hfs : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    (hfK : MapsTo f (closedBall (0 : ℂ) 1) K)
    (hE : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (ball (0 : ℂ) 1))
    (Γ : ℝ → F) {KΓ : ℝ≥0} (hΓ : LipschitzWith KΓ Γ)
    (hΓper : Function.Periodic Γ 1)
    (ψ : CircleDeg1Lift) (hψ : Continuous ψ)
    (htrace : ∀ s : ℝ, f (circleMap 0 1 (2 * Real.pi * s)) = Γ (ψ s))
    (T : F → F) (hT : Differentiable ℝ T) {LT : ℝ≥0}
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hfix : ∀ y ∈ K, T y = y)
    (hmap : MapsTo T U K') :
    ∃ (fn : ℕ → ℂ → F) (ψn : ℕ → CircleDeg1Lift) (a : ℕ → ℝ),
      (∀ n, ∃ L : ℝ≥0, LipschitzWith L (fn n)) ∧
      (∀ n, LipschitzWith ((3 * (n + 1) : ℕ) : ℝ≥0) (ψn n)) ∧
      (∀ (n i : ℕ), i < 3 * (n + 1) → ∀ t ∈ Icc (i / ((3 * (n + 1) : ℕ) : ℝ))
        ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)),
        ψn n t = ψ (i / ((3 * (n + 1) : ℕ) : ℝ)) +
          (ψ ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)) -
            ψ (i / ((3 * (n + 1) : ℕ) : ℝ))) * (((3 * (n + 1) : ℕ) : ℝ) * t - i)) ∧
      (∀ n, ψn n 0 = ψ 0 ∧ ψn n (1 / 3) = ψ (1 / 3) ∧ ψn n (2 / 3) = ψ (2 / 3)) ∧
      TendstoUniformly (fun n t => ψn n t) ψ atTop ∧
      (∀ n s, fn n (circleMap 0 1 (2 * Real.pi * s)) = Γ (ψn n s)) ∧
      (∀ n, a n ∈ Ioo (0 : ℝ) 1) ∧ Tendsto a atTop (𝓝 1) ∧
      (∀ n, EqOn (fn n) f (closedBall (0 : ℂ) (a n))) ∧
      (∀ᶠ n in atTop, MapsTo (fn n) (closedBall (0 : ℂ) 1) K') ∧
      TendstoUniformlyOn fn f atTop (closedBall (0 : ℂ) 1) ∧
      ∀ (A : F → F →L[ℝ] F →L[ℝ] ℝ), ContinuousOn A K' →
        Tendsto (fun n => ∫ z in closedBall (0 : ℂ) 1,
          (A (fn n z) (fderiv ℝ (fn n) z 1) (fderiv ℝ (fn n) z 1) +
            A (fn n z) (fderiv ℝ (fn n) z Complex.I) (fderiv ℝ (fn n) z Complex.I)) / 2)
          atTop (𝓝 (∫ z in closedBall (0 : ℂ) 1,
            (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
              A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2)) := by
  classical
  have hKK' : K ⊆ K' := fun y hy => by
    have hh := hmap (hKU hy)
    rwa [hfix y hy] at hh
  have hΓK (t : ℝ) : Γ t ∈ K := by
    obtain ⟨s, rfl⟩ := (ψ.continuous_iff_surjective.mp hψ) t
    rw [← htrace s]
    apply hfK
    simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_one, le_refl]
  obtain ⟨ψn, hψLip, hcell, hknots, hmarks, hψconv, hsum⟩ :=
    ψ.exists_uniform_piecewise_affine_sequence hψ
  let N : ℕ → ℕ := fun n => 3 * (n + 1)
  let h : ℕ → ℝ := fun n => (N n : ℝ)⁻¹
  have hNp (n : ℕ) : 0 < (N n : ℝ) := by dsimp only [N]; positivity
  have hh (n : ℕ) : 0 < h n ∧ h n < 1 / 2 := by
    refine ⟨inv_pos.mpr (hNp n), ?_⟩
    dsimp only [h, N]
    rw [inv_eq_one_div, div_lt_iff₀ (by positivity : (0 : ℝ) < ↑(3 * (n + 1)))]
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hNlim : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ N n by dsimp only [N]; omega) tendsto_id
  have hh0 : Tendsto h atTop (𝓝 0) := by
    simpa only [h, one_div, Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hNlim
  let b := fun n t => Γ (ψn n (t - 1 / 2))
  let Kb := fun n => KΓ * (N n : ℝ≥0)
  have hbper (n : ℕ) : Function.Periodic (b n) 1 := by
    intro t
    change Γ (ψn n (t + 1 - 1 / 2)) = Γ (ψn n (t - 1 / 2))
    rw [show t + 1 - 1 / 2 = (t - 1 / 2) + 1 by ring, (ψn n).map_add_one, hΓper]
  have hb (n : ℕ) : LipschitzWith (Kb n) (b n) := by
    have hx := (hΓ.comp (hψLip n)).comp (isometry_add_right (-(1 / 2 : ℝ))).lipschitzWith
    simpa only [b, Kb, N, mul_one, Function.comp_def, sub_eq_add_neg] using hx
  have hbK (n : ℕ) (t : ℝ) : b n t ∈ K := hΓK _
  have hphase (t : ℝ) : f (circleMap 0 1 (2 * Real.pi * t - Real.pi)) =
      Γ (ψ (t - 1 / 2)) := by
    rw [show 2 * Real.pi * t - Real.pi = 2 * Real.pi * (t - 1 / 2) by ring, htrace]
  have hbconv : TendstoUniformly b
      (fun t => f (circleMap 0 1 (2 * Real.pi * t - Real.pi))) atTop := by
    have hc := (hΓ.uniformContinuous.comp_tendstoUniformly hψconv).comp (fun t : ℝ => t - 1 / 2)
    simpa only [Function.comp_def, b, hphase] using hc
  have hb0per (n : ℕ) : Function.Periodic (Γ ∘ ψn n) 1 := by
    intro t
    change Γ (ψn n (t + 1)) = Γ (ψn n t)
    rw [(ψn n).map_add_one, hΓper]
  have hsum0 := hsum.const_mul ((KΓ : ℝ) ^ 2)
  simp only [mul_zero] at hsum0
  have hder0 : Tendsto (fun n => h n * ∫ t in Icc (0 : ℝ) 1, ‖deriv (b n) t‖ ^ 2)
      atTop (𝓝 0) := by
    have he (n : ℕ) := integral_deriv_comp_sub_sq_eq_of_periodic (hb0per n) (1 / 2)
    have hbnd (n : ℕ) := integral_deriv_comp_piecewise_affine_lift_sq_le ψ (ψn n)
      (show 0 < N n by dsimp only [N]; omega) (hcell n) (hψLip n) hΓ
    apply squeeze_zero (fun n => mul_nonneg (hh n).1.le (integral_nonneg fun t => sq_nonneg _))
      (fun n => ?_) hsum0
    change h n * _ ≤ _
    rw [show (∫ t in Icc (0 : ℝ) 1, ‖deriv (b n) t‖ ^ 2) =
        ∫ t in Icc (0 : ℝ) 1, ‖deriv (Γ ∘ ψn n) t‖ ^ 2 from he n]
    exact hbnd n
  have hgap0 : Tendsto (fun n => (h n)⁻¹ * ∫ t in Icc (0 : ℝ) 1,
      ‖f (circleMap 0 1 (2 * Real.pi * t - Real.pi)) - b n t‖ ^ 2) atTop (𝓝 0) := by
    have he (n : ℕ) : (∫ t in Icc (0 : ℝ) 1,
        ‖f (circleMap 0 1 (2 * Real.pi * t - Real.pi)) - b n t‖ ^ 2) =
        ∫ t in Icc (0 : ℝ) 1, ‖Γ (ψn n t) - Γ (ψ t)‖ ^ 2 := by
      simp only [hphase, b, norm_sub_rev (Γ (ψ _))]
      apply integral_Icc_comp_sub_eq_of_periodic
        (f := fun t => ‖Γ (ψn n t) - Γ (ψ t)‖ ^ 2) (d := 1 / 2)
      intro t
      change ‖Γ (ψn n (t + 1)) - Γ (ψ (t + 1))‖ ^ 2 = _
      rw [(ψn n).map_add_one, ψ.map_add_one, hΓper, hΓper]
    have hbnd (n : ℕ) := integral_comp_monotone_lift_sub_sq_le_of_grid_knots ψ (ψn n) hψ
      (show 0 < N n by dsimp only [N]; omega) (hknots n) (hψLip n) hΓ
    apply squeeze_zero (fun n => mul_nonneg (inv_nonneg.mpr (hh n).1.le)
      (integral_nonneg fun t => sq_nonneg _)) (fun n => ?_) hsum0
    rw [he n]
    simpa only [h, inv_inv] using hbnd n
  obtain ⟨a, ha, halim, hgap, hder⟩ := exists_inner_radii_tendsto_scaled_boundary_rates
    hf hfs hE h hh hh0 b Kb hb hgap0 hder0
  have ha01 (n : ℕ) : a n ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [(ha n).1, (ha n).2, (hh n).1, (hh n).2]
  obtain ⟨v, Lv, hv, hveq, hWLip, hcore, hWtrace, hWK, hWlim⟩ :=
    exists_thin_annulus_recovery_maps_in_compact_neighborhood hK hU hKU
      f hf hfs hfK T hT hLT hfix hmap
      a ha01 halim b hbper Kb hb hbK hbconv (f 0)
  let u := fun n => periodicLoopCone (f 0) (hbper n)
  let W := fun n => attachThinAnnulus (u n) (v n) T 1 (1 - a n)
  have huLip (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (u n) :=
    exists_lipschitzWith_periodicLoopCone (f 0) (hbper n) (hb n)
  choose Ku hKu using huLip
  have huBoundary (n : ℕ) (t : ℝ) : u n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = b n t :=
    periodicLoopCone_boundary _ _ _
  have hvBoundary (n : ℕ) (t : ℝ) : v n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) =
      f (circleMap 0 (a n) (2 * Real.pi * t - Real.pi)) := by
    rw [hveq n _ (by
      simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_one, le_refl])]
    congr 1
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.real_smul]
  have hfixu (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : T (u n z) = u n z := by
    obtain ⟨t, ht⟩ : ∃ t : ℝ, circleMap 0 1 (2 * Real.pi * t - Real.pi) = z := by
      refine ⟨(Complex.arg z + Real.pi) / (2 * Real.pi), ?_⟩
      have he := Complex.norm_mul_exp_arg_mul_I z
      have heq : 2 * Real.pi * ((Complex.arg z + Real.pi) / (2 * Real.pi)) - Real.pi =
          Complex.arg z := by field_simp; ring
      rw [heq]
      simpa only [circleMap, zero_add, Complex.ofReal_one, one_mul, hz] using he
    rw [← ht, huBoundary]
    exact hfix _ (hbK n t)
  have hfixv (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : T (v n z) = v n z := by
    apply hfix
    rw [hveq n z (by simpa only [mem_closedBall, dist_zero_right, hz] using (le_refl (1 : ℝ)))]
    apply hfK
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (ha01 n).1.le, hz, mul_one]
    exact (ha01 n).2.le
  have hwidth (n : ℕ) : 0 < 1 - a n ∧ 1 - a n ≤ 1 / 2 := by
    constructor <;> linarith [(ha n).1, (ha n).2, (hh n).1, (hh n).2]
  have hgap' : Tendsto (fun n => (1 - a n)⁻¹ * ∫ t in Icc (0 : ℝ) 1,
      ‖v n (circleMap 0 1 (2 * Real.pi * t - Real.pi)) -
        u n (circleMap 0 1 (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0) := by
    simpa only [huBoundary, hvBoundary] using hgap
  have hder' : Tendsto (fun n => (1 - a n) * ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => v n (circleMap 0 1 (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
        ‖deriv (fun t => u n (circleMap 0 1 (2 * Real.pi * t - Real.pi))) t‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [huBoundary, hvBoundary] using hder
  have hshell := tendsto_annulus_energy_attachThinAnnulus_of_scaled_boundary_rates
    u v Ku Lv hKu hv (fun n => 1 - a n) (Eventually.of_forall hwidth) hgap' hder'
    T hT hLT hfixu hfixv
  refine ⟨W, ψn, a, hWLip, hψLip, hcell, hmarks, hψconv, ?_, ha01, halim, ?_, hWK, hWlim, ?_⟩
  · intro n s
    have hh := hWtrace n (s + 1 / 2)
    have heq : 2 * Real.pi * (s + 1 / 2) - Real.pi = 2 * Real.pi * s := by ring
    simpa only [heq, b, add_sub_cancel_right] using hh
  · intro n z hz
    exact hcore n z (by simpa only [mem_closedBall, dist_zero_right] using hz)
  · intro A hA
    apply tendsto_integral_quadratic_fderiv_of_eqOn_exhausting_closedBall halim
      (Eventually.of_forall fun n => (ha01 n).2.le) f W hK' A hA
      (hWK.mono fun n hn => ⟨hWLip n, hn⟩)
      (Eventually.of_forall fun n z hz => hcore n z (by
        simpa only [mem_closedBall, dist_zero_right] using hz))
      (integrable_quadratic_of_compact_image_energy hf hfs hE hK' (hfK.mono_right hKK') A hA)
    simpa only [sub_sub_cancel, dist_zero_right, W] using hshell

end DifferentialGeometry.Analysis

end

end
