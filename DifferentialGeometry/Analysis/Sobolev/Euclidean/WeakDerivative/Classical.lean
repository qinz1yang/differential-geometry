import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Local
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Dual
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology Convolution ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

private theorem hasFDerivAt_of_continuous_weak_partials_global
    {u : V → ℝ} {G : V → V} {Ω : Set V} (hΩ : IsOpen Ω)
    (hu : Continuous u) (hG : Continuous G)
    (hweak : ∀ j, DeGiorgi.HasWeakPartialDeriv j (fun x => G x j) u Ω)
    {x : V} (hx : x ∈ Ω) : HasFDerivAt u (innerSL ℝ (G x)) x := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f := fun n => mollifyEps (hε n) u
  let Gε := fun n y => (WithLp.toLp 2 (fun j => mollifyEps (hε n) (fun z => G z j) y) : V)
  let D := fun n y => innerSL ℝ (Gε n y)
  have hcomponent (j : Fin d) : Tendsto
      (fun q : ℕ × V => mollifyEps (hε q.1) (fun z => G z j) q.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (G x j)) := by
    have hc : Continuous (fun z => G z j) := (PiLp.continuous_apply 2 _ j).comp hG
    exact ContDiffBump.convolution_tendsto_right
      (φ := fun q : ℕ × V => mollifierBumpEps (hε q.1))
      (hεlim.comp tendsto_fst)
      (Eventually.of_forall fun _ => hc.aestronglyMeasurable)
      (hc.continuousAt.tendsto.comp tendsto_snd) tendsto_snd
  have hGε : Tendsto (fun q : ℕ × V => Gε q.1 q.2) (atTop ×ˢ 𝓝 x) (𝓝 (G x)) := by
    exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hcomponent)
  have hD : TendstoUniformlyOnFilter D (fun y => innerSL ℝ (G y)) atTop (𝓝 x) := by
    rw [tendstoUniformlyOnFilter_iff_tendsto, tendsto_uniformity_iff_dist_tendsto_zero]
    have hleft : Tendsto (fun q : ℕ × V => innerSL ℝ (G q.2))
        (atTop ×ˢ 𝓝 x) (𝓝 (innerSL ℝ (G x))) :=
      (innerSL ℝ).continuous.continuousAt.tendsto.comp
      (hG.continuousAt.tendsto.comp tendsto_snd)
    have hright := (innerSL ℝ).continuous.continuousAt.tendsto.comp hGε
    simpa only [D, Function.comp_def, dist_self] using hleft.dist hright
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hderiv : ∀ᶠ q : ℕ × V in atTop ×ˢ 𝓝 x, HasFDerivAt (f q.1) (D q.1 q.2) q.2 := by
    have hn : ∀ᶠ n in atTop, ε n < r / 2 := hεlim.eventually (gt_mem_nhds (half_pos hr))
    filter_upwards [hn.prod_mk (Metric.ball_mem_nhds x (half_pos hr))] with q hq
    have hb : closedBall q.2 (ε q.1) ⊆ Ω := by
      apply Subset.trans _ hball
      intro y hy
      exact mem_ball.mpr (by
        linarith [mem_closedBall.mp hy, mem_ball.mp hq.2, dist_triangle y q.2 x])
    have hf := (mollifyEps_contDiff (hε q.1) hu.locallyIntegrable).differentiable
      (by simp) q.2
    have heq : fderiv ℝ (f q.1) q.2 = D q.1 q.2 := by
      apply ContinuousLinearMap.ext
      intro z
      rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr z]
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      simp only [EuclideanSpace.basisFun_apply]
      change fderiv ℝ (mollifyEps (hε q.1) u) q.2 (EuclideanSpace.single j 1) =
        innerSL ℝ (Gε q.1 q.2) (EuclideanSpace.single j 1)
      rw [mollifyEps_partial_eq_mollifyEps_weakPartial_of_closedBall_subset
        (hε q.1) hu.locallyIntegrable (hweak j) q.2 hb]
      simp only [innerSL_apply_apply, EuclideanSpace.inner_single_right, Gε,
        conj_trivial, one_mul]
    exact heq ▸ hf.hasFDerivAt
  exact hasFDerivAt_of_tendstoUniformlyOnFilter hD hderiv
    (Eventually.of_forall fun y => tendsto_mollifyEps_of_continuous hε hεlim hu y)

theorem hasFDerivAt_of_continuousOn_weak_partials
    {u : V → ℝ} {G : V → V} {Ω : Set V} (hΩ : IsOpen Ω)
    (hu : ContinuousOn u Ω) (hG : ContinuousOn G Ω)
    (hweak : ∀ j, DeGiorgi.HasWeakPartialDeriv j (fun x => G x j) u Ω)
    {x : V} (hx : x ∈ Ω) : HasFDerivAt u (innerSL ℝ (G x)) x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  let β : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsupp : tsupport β ⊆ Ω := by
    rw [β.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp only [β]; linarith)).trans hball
  let u₁ : V → ℝ := fun y => β y * u y
  let G₁ : V → V := fun y => β y • G y
  have hu₁ : Continuous u₁ :=
    (β.continuous.continuousOn.mul hu).continuous_of_tsupport_subset hΩ
      ((tsupport_mul_subset_left).trans hsupp)
  have hG₁ : Continuous G₁ :=
    (β.continuous.continuousOn.smul hG).continuous_of_tsupport_subset hΩ
      ((tsupport_smul_subset_left _ _).trans hsupp)
  have hsmall : ball x (r / 4) ⊆ Ω := (ball_subset_ball (by linarith)).trans hball
  have heq (y : V) (hy : y ∈ ball x (r / 4)) : β y = 1 :=
    β.one_of_mem_closedBall (ball_subset_closedBall hy)
  have huAE : u =ᵐ[volume.restrict (ball x (r / 4))] u₁ := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
    simp only [u₁, heq y hy, one_mul]
  have hGAE (j : Fin d) : (fun y => G y j) =ᵐ[volume.restrict (ball x (r / 4))]
      (fun y => G₁ y j) := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
    simp only [G₁, heq y hy, one_smul]
  have hweak₁ (j : Fin d) : DeGiorgi.HasWeakPartialDeriv j (fun y => G₁ y j) u₁
      (ball x (r / 4)) :=
    (DeGiorgi.HasWeakPartialDeriv.restrict isOpen_ball hsmall (hweak j)).congr_ae huAE (hGAE j)
  have hxsmall : x ∈ ball x (r / 4) := mem_ball_self (by positivity)
  have hh := hasFDerivAt_of_continuous_weak_partials_global isOpen_ball hu₁ hG₁ hweak₁ hxsmall
  have hux : u₁ =ᶠ[𝓝 x] u := by
    filter_upwards [ball_mem_nhds x (by positivity : 0 < r / 4)] with y hy
    simp only [u₁, heq y hy, one_mul]
  have hGx : G₁ x = G x := by simp only [G₁, heq x hxsmall, one_smul]
  rw [hGx] at hh
  exact hh.congr_of_eventuallyEq hux.symm

theorem contDiffOn_one_of_continuousOn_weak_partials
    {u : V → ℝ} {G : V → V} {Ω : Set V} (hΩ : IsOpen Ω)
    (hu : ContinuousOn u Ω) (hG : ContinuousOn G Ω)
    (hweak : ∀ j, DeGiorgi.HasWeakPartialDeriv j (fun x => G x j) u Ω) :
    ContDiffOn ℝ 1 u Ω := by
  have hderiv (x : V) (hx : x ∈ Ω) : HasFDerivAt u (innerSL ℝ (G x)) x :=
    hasFDerivAt_of_continuousOn_weak_partials hΩ hu hG hweak hx
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact ((innerSL ℝ).continuous.comp_continuousOn hG).congr fun x hx => (hderiv x hx).fderiv

end DifferentialGeometry.Analysis.Sobolev.Euclidean

namespace DeGiorgi

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem MemW1pWitness.hasFDerivAt_of_continuousOn_weakGrad
    {p : ℝ≥0∞} {u : V → ℝ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hu : MemW1pWitness p u Ω) (huc : ContinuousOn u Ω)
    {G : V → V} (hGc : ContinuousOn G Ω) (hG : G =ᵐ[volume.restrict Ω] hu.weakGrad)
    {x : V} (hx : x ∈ Ω) : HasFDerivAt u (innerSL ℝ (G x)) x := by
  apply DifferentialGeometry.Analysis.Sobolev.Euclidean.hasFDerivAt_of_continuousOn_weak_partials
    hΩ huc hGc _ hx
  intro j
  exact (hu.isWeakGrad j).congr_ae Filter.EventuallyEq.rfl
    (hG.symm.mono fun y hy => congrArg (fun a : V => a j) hy)

theorem MemW1pWitness.contDiffOn_one_of_continuousOn_weakGrad
    {p : ℝ≥0∞} {u : V → ℝ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hu : MemW1pWitness p u Ω) (huc : ContinuousOn u Ω)
    {G : V → V} (hGc : ContinuousOn G Ω) (hG : G =ᵐ[volume.restrict Ω] hu.weakGrad) :
    ContDiffOn ℝ 1 u Ω := by
  apply DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_one_of_continuousOn_weak_partials
    hΩ huc hGc
  intro j
  exact (hu.isWeakGrad j).congr_ae Filter.EventuallyEq.rfl
    (hG.symm.mono fun y hy => congrArg (fun a : V => a j) hy)

end DeGiorgi

end

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem exists_memW1pWitness_of_contDiffOn_closedBall
    {u : V → ℝ} {Ω : Set V} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω)
    {c : V} {R : ℝ} (hball : Metric.closedBall c R ⊆ Ω) (p : ℝ≥0∞) :
    ∃ hw : DeGiorgi.MemW1pWitness p u (Metric.ball c R),
      ∀ x j, hw.weakGrad x j = fderiv ℝ u x (EuclideanSpace.single j 1) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hLp {f : V → ℝ} (hf : ContinuousOn f (Metric.closedBall c R)) :
      MemLp f p (volume.restrict (Metric.ball c R)) := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hf
    apply MemLp.of_bound ((hf.mono Metric.ball_subset_closedBall).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet) B
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hB x (Metric.ball_subset_closedBall hx)
  let G (x : V) : V := WithLp.toLp 2 fun j => fderiv ℝ u x (EuclideanSpace.single j 1)
  let hw : DeGiorgi.MemW1pWitness p u (Metric.ball c R) :=
    { memLp := hLp (hu.continuousOn.mono hball)
      weakGrad := G
      weakGrad_component_memLp := fun j => hLp
        (((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const).mono hball)
      isWeakGrad := fun j => hasWeakPartialDeriv_of_contDiffOn Metric.isOpen_ball
        (hu.mono (Metric.ball_subset_closedBall.trans hball)) j }
  exact ⟨hw, fun _ _ => rfl⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem MemW1pWitness.weakGrad_ae_eq_smoothGradField_on_ball
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u : V → ℝ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hu : MemW1pWitness p u Ω) (hc : ContDiffOn ℝ 1 u Ω)
    {c : V} {R : ℝ} (hball : Metric.closedBall c R ⊆ Ω) :
    hu.weakGrad =ᵐ[volume.restrict (Metric.ball c R)] smoothGradField u := by
  have hsub : Metric.ball c R ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  have hcomp (j : Fin d) : (fun x => hu.weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball c R)] (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) := by
    have hfirst := HasWeakPartialDeriv.restrict Metric.isOpen_ball hsub (hu.isWeakGrad j)
    have hsecond := hasWeakPartialDeriv_of_contDiffOn Metric.isOpen_ball (hc.mono hsub) j
    have hDc : ContinuousOn (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) Ω :=
      (hc.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
    have hDi : IntegrableOn (fun x => fderiv ℝ u x (EuclideanSpace.single j 1))
        (Metric.ball c R) :=
      ((hDc.mono hball).integrableOn_compact (isCompact_closedBall _ _)).mono_set
        Metric.ball_subset_closedBall
    exact HasWeakPartialDeriv.ae_eq Metric.isOpen_ball hfirst hsecond
      (((hu.weakGrad_component_memLp j).mono_measure
        (Measure.restrict_mono_set volume hsub)).locallyIntegrable hp) hDi.locallyIntegrable
  filter_upwards [ae_all_iff.mpr hcomp] with x hx
  ext j
  exact hx j

end DeGiorgi

end
