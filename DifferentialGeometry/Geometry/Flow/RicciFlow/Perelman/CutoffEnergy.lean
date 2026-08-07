import DifferentialGeometry.Geometry.Metric.DistanceTent
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.LipschitzApprox
import DifferentialGeometry.Analysis.Integration.Measure.Properties
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

/-!
# Smooth cutoff energy

This file turns the intrinsic distance tent into a smooth cutoff.  The output
keeps a definite amount of the half-ball `L²` mass and has the scale-sharp
outer-ball gradient bound needed by the Perelman cutoff argument.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Geometry
namespace Flow
namespace RicciFlow
namespace Perelman

open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  [I.Boundaryless] [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A radius-`r` ball admits a smooth cutoff whose `L²` mass sees the
half-radius ball and whose metric-gradient `L²` norm is at most the outer-ball
volume scale times `5 / r`. -/
theorem exists_cutoff_energy
    (g : SmoothRiemannianMetric I M) (a : M) {r : ℝ} (hr : 0 < r) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ φ ∧
      tsupport φ ⊆
        {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r} ∧
      (riemannianVolumeMeasure I M g
          {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal (r / 2)}) ^
          (1 / 2 : ℝ) / 2 ≤
        eLpNorm φ 2 (riemannianVolumeMeasure I M g) ∧
      eLpNorm (fun x : M => Real.sqrt (g.inner x
          (gradFun (I := I) g φ x) (gradFun (I := I) g φ x))) 2
          (riemannianVolumeMeasure I M g) ≤
        ENNReal.ofReal (5 / r) *
          (riemannianVolumeMeasure I M g
            {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r}) ^
              (1 / 2 : ℝ) := by
  classical
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let A : Set M :=
    {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal (r / 2)}
  let U : Set M :=
    {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r}
  let u : M → ℝ := riemDistTent g a hr
  have hU : IsOpen U := by
    dsimp only [U]
    exact isOpen_lt
      (by
        unfold riemannianEDistOf
        exact DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g a)
      continuous_const
  have hA : IsOpen A := by
    dsimp only [A]
    exact isOpen_lt
      (by
        unfold riemannianEDistOf
        exact DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g a)
      continuous_const
  have hAne : A.Nonempty := by
    refine ⟨a, ?_⟩
    simp only [A, mem_setOf_eq, riemannianEDistOf,
      Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  letI : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hμA : 0 < μ A := hA.measure_pos μ hAne
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let m : ENNReal := (μ A) ^ (1 / 2 : ℝ)
  let q : ENNReal := ENNReal.ofReal (1 / r) * (μ U) ^ (1 / 2 : ℝ)
  have hm_pos : 0 < m := ENNReal.rpow_pos_of_nonneg hμA (by positivity)
  have hμU : 0 < μ U := measure_pos_of_superset
    (show A ⊆ U by
      intro x hx
      exact hx.trans (ENNReal.ofReal_lt_ofReal_iff hr |>.2 (by linarith))) hμA.ne'
  have hq_pos : 0 < q := ENNReal.mul_pos
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    (ENNReal.rpow_pos_of_nonneg hμU (by positivity)).ne'
  have hm_top : m ≠ (⊤ : ENNReal) := by
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ A)
  have hq_top : q ≠ (⊤ : ENNReal) := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ U))
  let ε : ℝ := min m.toReal q.toReal / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    exact half_pos (lt_min (ENNReal.toReal_pos hm_pos.ne' hm_top)
      (ENNReal.toReal_pos hq_pos.ne' hq_top))
  obtain ⟨φ, hφ, hφsupp, herr, hgraderr⟩ :=
    exists_smooth_supp (I := I) (M := M) g
      (B := 1)
      (riemTent_lip g a hr) (fun x => by
        rw [← NNReal.coe_le_coe]
        simpa only [coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs,
          abs_of_nonneg (riemTent_mem_Icc g a hr x).1]
            using (riemTent_mem_Icc g a hr x).2)
      hU (riemTent_tsupport g a hr) hε
  refine ⟨φ, hφ, hφsupp, ?_, ?_⟩
  · have hu_aesm : AEStronglyMeasurable u μ :=
      (intrinsic_lip_cont (I := I) g (riemTent_lip g a hr)).aestronglyMeasurable
    have hφ_aesm : AEStronglyMeasurable φ μ :=
      hφ.continuous.aestronglyMeasurable
    have hind : eLpNorm (A.indicator fun _ : M => (1 : ℝ)) 2 μ = m := by
      rw [eLpNorm_indicator_const (p := (2 : ENNReal))
        hA.measurableSet (by norm_num) (by norm_num)]
      simp only [enorm_one, one_mul, ENNReal.toReal_ofNat]
      norm_num [m]
    have hind_le : eLpNorm (A.indicator fun _ : M => (1 : ℝ)) 2 μ ≤
        eLpNorm u 2 μ := by
      apply eLpNorm_mono_ae_real
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ A
        · rw [Set.indicator_of_mem hx, norm_one]
          rw [show u x = 1 from riemTent_eq_one g a hr hx.le]
        · rw [Set.indicator_of_notMem hx, norm_zero]
          exact (riemTent_mem_Icc g a hr x).1
    have htri : eLpNorm u 2 μ ≤
        eLpNorm (fun x => u x - φ x) 2 μ + eLpNorm φ 2 μ := by
      have heq : u = (fun x => u x - φ x) + φ := by
        funext x
        simp only [Pi.add_apply]
        ring
      calc
        eLpNorm u 2 μ = eLpNorm ((fun x => u x - φ x) + φ) 2 μ :=
          congrArg (fun f => eLpNorm f 2 μ) heq
        _ ≤ eLpNorm (fun x => u x - φ x) 2 μ + eLpNorm φ 2 μ := by
          simpa only [Pi.sub_apply] using
            eLpNorm_add_le (p := (2 : ENNReal))
              (hu_aesm.sub hφ_aesm) hφ_aesm (by norm_num)
    have hεm : ENNReal.ofReal ε ≤ m / 2 := by
      calc
        ENNReal.ofReal ε ≤ ENNReal.ofReal (m.toReal / 2) := by
          apply ENNReal.ofReal_le_ofReal
          dsimp only [ε]
          exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        _ = m / 2 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal hm_top]
          norm_num
    have hsum : m ≤ m / 2 + eLpNorm φ 2 μ := by
      calc
        m = eLpNorm (A.indicator fun _ : M => (1 : ℝ)) 2 μ := hind.symm
        _ ≤ eLpNorm u 2 μ := hind_le
        _ ≤ eLpNorm (fun x => u x - φ x) 2 μ + eLpNorm φ 2 μ := htri
        _ ≤ m / 2 + eLpNorm φ 2 μ :=
          add_le_add (herr.trans hεm) (le_refl _)
    have hhalf_top : m / 2 ≠ (∞ : ENNReal) := by
      exact ENNReal.div_ne_top hm_top (by norm_num)
    have hhalves : m / 2 + m / 2 ≤ m / 2 + eLpNorm φ 2 μ := by
      rw [ENNReal.add_halves]
      exact hsum
    exact (ENNReal.add_le_add_iff_left hhalf_top).1 hhalves
  · have hu_diff : ∀ᵐ x ∂μ, MDifferentiableAt I 𝓘(ℝ, ℝ) u x :=
      DifferentialGeometry.Analysis.Sobolev.Chart.ae_mdiff_of_lip
        (I := I) g (B := 1) (riemTent_lip g a hr) (fun x => by
          rw [← NNReal.coe_le_coe]
          simpa only [u, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs,
            abs_of_nonneg (riemTent_mem_Icc g a hr x).1]
              using (riemTent_mem_Icc g a hr x).2)
    have hφ_diff : ∀ᵐ x ∂μ, MDifferentiableAt I 𝓘(ℝ, ℝ) φ x :=
      Filter.Eventually.of_forall fun x => hφ.mdifferentiableAt (by norm_num)
    have he_diff : ∀ᵐ x ∂μ,
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => u y - φ y) x := by
      filter_upwards [hu_diff, hφ_diff] with x hux hφx
      exact hux.sub hφx
    let gu : M → ℝ := fun x => Real.sqrt (g.inner x
      (gradFun (I := I) g u x) (gradFun (I := I) g u x))
    let ge : M → ℝ := fun x => Real.sqrt (g.inner x
      (gradFun (I := I) g (fun y => u y - φ y) x)
      (gradFun (I := I) g (fun y => u y - φ y) x))
    let gp : M → ℝ := fun x => Real.sqrt (g.inner x
      (gradFun (I := I) g φ x) (gradFun (I := I) g φ x))
    have hgu_aesm : AEStronglyMeasurable gu μ :=
      grad_norm_aesm (I := I) g hu_diff
    have hge_aesm : AEStronglyMeasurable ge μ :=
      grad_norm_aesm (I := I) g he_diff
    have hgp_aesm : AEStronglyMeasurable gp μ :=
      grad_norm_aesm (I := I) g hφ_diff
    have hgu_point : ∀ x, gu x ≤ U.indicator (fun _ : M => 4 / r) x := by
      intro x
      by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx]
        exact DifferentialGeometry.Geometry.Riemannian.grad_norm_le_lip_all
          (I := I) g (riemTent_lip g a hr)
      · rw [Set.indicator_of_notMem hx]
        have hzero : gradFun (I := I) g u x = (0 : TangentSpace I x) := by
          by_contra hn
          exact hx (riemTent_tsupport g a hr
            (support_gradFun_subset (I := I) g u hn))
        have hinnerzero : g.inner x (0 : TangentSpace I x) 0 = 0 := by
          calc
            g.inner x (0 : TangentSpace I x) 0 =
                (0 : TangentSpace I x →L[ℝ] ℝ) 0 := by
              rw [(g.inner x).map_zero]
            _ = 0 := rfl
        change Real.sqrt (g.inner x (gradFun (I := I) g u x)
          (gradFun (I := I) g u x)) ≤ 0
        rw [hzero, hinnerzero, Real.sqrt_zero]
    have hgu_l2 : eLpNorm gu 2 μ ≤
        ENNReal.ofReal (4 / r) * (μ U) ^ (1 / 2 : ℝ) := by
      calc
        eLpNorm gu 2 μ ≤
            eLpNorm (U.indicator fun _ : M => 4 / r) 2 μ := by
          apply eLpNorm_mono_ae_real
          exact Filter.Eventually.of_forall fun x => by
            simpa only [gu, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)] using hgu_point x
        _ = ENNReal.ofReal (4 / r) * (μ U) ^ (1 / 2 : ℝ) := by
          rw [eLpNorm_indicator_const hU.measurableSet (by norm_num) (by norm_num)]
          simp only [ENNReal.toReal_ofNat]
          rw [Real.enorm_eq_ofReal (div_nonneg (by norm_num) hr.le)]
    have hgp_point : ∀ᵐ x ∂μ, gp x ≤ gu x + ge x := by
      filter_upwards [hu_diff, hφ_diff] with x hux hφx
      have hsub := gradFun_sub (I := I) g hux hφx
      have hvec : gradFun (I := I) g φ x =
          gradFun (I := I) g u x +
            -(gradFun (I := I) g (fun y => u y - φ y) x) := by
        rw [hsub]
        abel
      dsimp only [gp, gu, ge]
      rw [hvec]
      calc
        Real.sqrt (g.inner x
            (gradFun (I := I) g u x +
              -(gradFun (I := I) g (fun y => u y - φ y) x))
            (gradFun (I := I) g u x +
              -(gradFun (I := I) g (fun y => u y - φ y) x))) ≤
          Real.sqrt (g.inner x (gradFun (I := I) g u x)
              (gradFun (I := I) g u x)) + Real.sqrt (g.inner x
            (-(gradFun (I := I) g (fun y => u y - φ y) x))
            (-(gradFun (I := I) g (fun y => u y - φ y) x))) := by
          exact DifferentialGeometry.Analysis.Laplacian.gNorm_add_le g x _ _
        _ = Real.sqrt (g.inner x (gradFun (I := I) g u x)
              (gradFun (I := I) g u x)) +
            Real.sqrt (g.inner x
              (gradFun (I := I) g (fun y => u y - φ y) x)
              (gradFun (I := I) g (fun y => u y - φ y) x)) := by
          congr 1
          simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
    have hgp_l2 : eLpNorm gp 2 μ ≤
        eLpNorm gu 2 μ + eLpNorm ge 2 μ := by
      calc
        eLpNorm gp 2 μ ≤ eLpNorm (fun x => gu x + ge x) 2 μ :=
          eLpNorm_mono_ae_real (hgp_point.mono fun x hx => by
            simpa only [gp, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)] using hx)
        _ ≤ eLpNorm gu 2 μ + eLpNorm ge 2 μ :=
          eLpNorm_add_le (p := (2 : ENNReal)) hgu_aesm hge_aesm (by norm_num)
    have hεq : ENNReal.ofReal ε ≤ q := by
      calc
        ENNReal.ofReal ε ≤ ENNReal.ofReal q.toReal := by
          apply ENNReal.ofReal_le_ofReal
          dsimp only [ε]
          exact (div_le_self (by positivity)
            (show (1 : ℝ) ≤ 2 by norm_num)).trans
            (min_le_right _ _)
        _ = q := ENNReal.ofReal_toReal hq_top
    have hfive :
        ENNReal.ofReal (4 / r) * (μ U) ^ (1 / 2 : ℝ) + q =
          ENNReal.ofReal (5 / r) * (μ U) ^ (1 / 2 : ℝ) := by
      dsimp only [q]
      rw [← add_mul, ← ENNReal.ofReal_add (div_nonneg (by norm_num) hr.le)
        (div_nonneg (by norm_num) hr.le)]
      congr 2
      ring
    calc
      eLpNorm gp 2 μ ≤ eLpNorm gu 2 μ + eLpNorm ge 2 μ := hgp_l2
      _ ≤ ENNReal.ofReal (4 / r) * (μ U) ^ (1 / 2 : ℝ) + q :=
        add_le_add hgu_l2 (hgraderr.trans (hεq))
      _ = ENNReal.ofReal (5 / r) * (μ U) ^ (1 / 2 : ℝ) := hfive

end Perelman
end RicciFlow
end Flow
end Geometry
end DifferentialGeometry
