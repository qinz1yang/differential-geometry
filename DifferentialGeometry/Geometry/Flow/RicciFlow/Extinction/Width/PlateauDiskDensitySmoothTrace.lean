import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Plateau
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauDensityBridge
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
private theorem contMDiff_diskBoundary_coe :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (diskBoundary (t : Surgery.Topology.Circle) : ℂ)) := by
  let _ := (Complex.finrank_real_complex_fact : Fact (Module.finrank ℝ ℂ = 1 + 1))
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
      (fun t : ℝ => _root_.Circle.exp (2 * Real.pi * t)) :=
    contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff
  have h2 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => ((_root_.Circle.exp (2 * Real.pi * t) : _root_.Circle) : ℂ)) :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).comp h1
  exact h2.congr fun t => diskBoundary_coe t

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem SmoothDisk.contMDiff_trace (u : SmoothDisk (I := I) (Q := Q)) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => u.map (diskBoundary (t : Surgery.Topology.Circle))) := by
  have h := (u.contMDiffOn_extension).comp_contMDiff contMDiff_diskBoundary_coe
    (fun t => (diskBoundary (t : Surgery.Topology.Circle)).property)
  exact h.congr fun t =>
    (diskExtension_coe u.map (diskBoundary (t : Surgery.Topology.Circle))).symm

omit [FiniteDimensional ℝ E] in
theorem contMDiff_loopLift_of_plateauDiskDensity
    (g : SmoothRiemannianMetric I Q) (γ : Surgery.Topology.ContinuousFreeLoop Q)
    (v : DiskCompetitor g γ) (h : PlateauDiskDensity (I := I) (Q := Q) g γ) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ) := by
  obtain ⟨w, hw, _⟩ := h v
  exact (SmoothDisk.contMDiff_trace (w 0)).congr fun t =>
    (hw 0 (t : Surgery.Topology.Circle)).symm

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem DiskSmoothExtension.contMDiff_trace {u : C(Disk, Q)} {U : ℂ → Q}
    (h : DiskSmoothExtension I u U) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => u (diskBoundary (t : Surgery.Topology.Circle))) := by
  obtain ⟨heq, N, _hN, hDN, hU⟩ := h
  have hcomp := hU.comp_contMDiff contMDiff_diskBoundary_coe
    (fun t => hDN (diskBoundary (t : Surgery.Topology.Circle)).property)
  exact hcomp.congr fun t =>
    (heq (diskBoundary (t : Surgery.Topology.Circle))).symm

omit [FiniteDimensional ℝ E] in
theorem not_hasDiskSmoothExtensionDensity_of_not_contMDiff
    (g : SmoothRiemannianMetric I Q) (γ : Surgery.Topology.ContinuousFreeLoop Q)
    (v : DiskCompetitor g γ) (hγ : ¬ ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ)) :
    ¬ HasDiskSmoothExtensionDensity (I := I) (Q := Q) g γ := by
  intro h
  obtain ⟨vj, Uj, hdata, _⟩ := h v
  exact hγ ((DiskSmoothExtension.contMDiff_trace (hdata 0).1).congr fun t =>
    ((hdata 0).2 (t : Surgery.Topology.Circle)).symm)

omit [FiniteDimensional ℝ E] in
theorem not_plateauDiskDensity_of_not_contMDiff
    (g : SmoothRiemannianMetric I Q) (γ : Surgery.Topology.ContinuousFreeLoop Q)
    (v : DiskCompetitor g γ) (hγ : ¬ ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ)) :
    ¬ PlateauDiskDensity (I := I) (Q := Q) g γ :=
  fun h => hγ (contMDiff_loopLift_of_plateauDiskDensity g γ v h)

omit [FiniteDimensional ℝ E] in
def HasSmoothLoopDiskSmoothExtensionDensity (g : SmoothRiemannianMetric I Q) : Prop :=
  ∀ γ : Surgery.Topology.ContinuousFreeLoop Q, ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ) →
    HasDiskSmoothExtensionDensity (I := I) (Q := Q) g γ

omit [FiniteDimensional ℝ E] in
theorem plateauDiskDensity_of_hasSmoothLoopDiskSmoothExtensionDensity
    (g : SmoothRiemannianMetric I Q)
    (h : HasSmoothLoopDiskSmoothExtensionDensity (I := I) (Q := Q) g)
    {γ : Surgery.Topology.ContinuousFreeLoop Q}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ)) :
    PlateauDiskDensity (I := I) (Q := Q) g γ :=
  plateauDiskDensity_of_hasDiskSmoothExtensionDensity (I := I) (Q := Q) g γ (h γ hγ)

omit [FiniteDimensional ℝ E] in
theorem hasDiskSmoothExtensionDensity_of_subsingleton [Subsingleton Q] [Nonempty Q]
    (g : SmoothRiemannianMetric I Q) (γ : Surgery.Topology.ContinuousFreeLoop Q) :
    HasDiskSmoothExtensionDensity (I := I) (Q := Q) g γ := by
  intro v
  let q : Q := Classical.arbitrary Q
  refine ⟨fun _ => ContinuousMap.const Disk q, fun _ => fun _ => q, ?_, ?_⟩
  · intro j
    exact ⟨⟨fun z => Subsingleton.elim _ _, Set.univ, isOpen_univ, subset_univ _,
      contMDiffOn_const⟩, fun θ => Subsingleton.elim _ _⟩
  · have hv : diskArea g v.1.map = 0 := by
      have hmap : ⇑v.1.map = fun _ : Disk => q := funext fun z => Subsingleton.elim _ _
      rw [hmap, diskArea_const]
    have hw : diskArea g (⇑(ContinuousMap.const Disk q)) = 0 := by
      have hmap : ⇑(ContinuousMap.const Disk q) = fun _ : Disk => q := rfl
      rw [hmap, diskArea_const]
    simpa only [hw, hv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

omit [FiniteDimensional ℝ E] in
theorem hasSmoothLoopDiskSmoothExtensionDensity_of_subsingleton [Subsingleton Q] [Nonempty Q]
    (g : SmoothRiemannianMetric I Q) :
    HasSmoothLoopDiskSmoothExtensionDensity (I := I) (Q := Q) g :=
  fun γ _ => hasDiskSmoothExtensionDensity_of_subsingleton g γ

end General

section EuclideanLine

open Surgery.Topology

private def chordLineCurve (t : ℝ) : ℂ := (2 * Real.pi : ℂ) * (t : ℂ)

private def chordCurve (t : ℝ) : ℂ := Complex.exp (chordLineCurve t * Complex.I)

private theorem norm_chordLineCurve (t : ℝ) :
    ‖chordLineCurve t * Complex.I‖ = 2 * Real.pi * |t| := by
  simp only [chordLineCurve, norm_mul, Complex.norm_I, mul_one]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
    show ‖(Real.pi : ℂ)‖ = Real.pi by simp [abs_of_pos Real.pi_pos],
    show ‖(t : ℂ)‖ = |t| by simp]

private theorem smul_inv_chordLineCurve {t : ℝ} (ht : t ≠ 0) :
    t⁻¹ • (chordLineCurve t * Complex.I) = (2 * Real.pi : ℂ) * Complex.I := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [chordLineCurve, Complex.real_smul, Complex.ofReal_inv]
  field_simp

private theorem norm_two_pi_I : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
  rw [norm_mul, Complex.norm_I, mul_one]
  simp [abs_of_pos Real.pi_pos]

private theorem tendsto_inv_smul_chordCurve :
    Tendsto (fun t : ℝ => t⁻¹ • (chordCurve t - 1)) (𝓝[≠] (0 : ℝ))
      (𝓝 ((2 * Real.pi : ℂ) * Complex.I)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun t : ℝ => (2 * Real.pi) ^ 2 * |t|)
    (Eventually.of_forall fun t => norm_nonneg _) ?_ ?_
  · have hball : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |t| ≤ 1 / (2 * Real.pi) := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (ε := 1 / (2 * Real.pi))
        (by positivity)] with t ht _
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using ht
    filter_upwards [self_mem_nhdsWithin, hball] with t ht hmem
    have hzle : ‖chordLineCurve t * Complex.I‖ ≤ 1 := by
      rw [norm_chordLineCurve]
      calc 2 * Real.pi * |t| ≤ 2 * Real.pi * (1 / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hmem (by positivity)
        _ = 1 := by field_simp
    have htaylor := Complex.norm_exp_sub_one_sub_id_le hzle
    have hsmul := smul_inv_chordLineCurve ht
    have hdiff : t⁻¹ • (chordCurve t - 1) - (2 * Real.pi : ℂ) * Complex.I =
        t⁻¹ • (Complex.exp (chordLineCurve t * Complex.I) - 1 -
          chordLineCurve t * Complex.I) := by
      rw [chordCurve, ← hsmul, ← smul_sub]
    rw [hdiff]
    calc ‖t⁻¹ • (Complex.exp (chordLineCurve t * Complex.I) - 1 -
            chordLineCurve t * Complex.I)‖
        = |t⁻¹| * ‖Complex.exp (chordLineCurve t * Complex.I) - 1 -
            chordLineCurve t * Complex.I‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |t⁻¹| * ‖chordLineCurve t * Complex.I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left htaylor (abs_nonneg _)
      _ = (2 * Real.pi) ^ 2 * |t| := by
          rw [norm_chordLineCurve]
          have htne : |t| ≠ 0 := abs_ne_zero.mpr ht
          rw [abs_inv, inv_mul_eq_div]
          field_simp
  · have hc : Continuous fun t : ℝ => (2 * Real.pi) ^ 2 * |t| :=
      continuous_const.mul continuous_abs
    have hcont : Tendsto (fun t : ℝ => (2 * Real.pi) ^ 2 * |t|) (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by
      have h := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ) (a := (0 : ℝ)))
      simpa using h
    exact hcont

private theorem not_differentiableAt_chordCurveNorm :
    ¬ DifferentiableAt ℝ (fun t : ℝ => ‖chordCurve t - 1‖) 0 := by
  intro hd
  have hzero : ‖chordCurve 0 - 1‖ = 0 := by simp [chordCurve, chordLineCurve]
  have hright : Tendsto (fun t : ℝ => t⁻¹ * ‖chordCurve t - 1‖) (𝓝[>] (0 : ℝ))
      (𝓝 (deriv (fun t : ℝ => ‖chordCurve t - 1‖) 0)) :=
    (hd.hasDerivAt.tendsto_slope_zero_right).congr'
      (Eventually.of_forall fun t => by simp [hzero])
  have hleft : Tendsto (fun t : ℝ => t⁻¹ * ‖chordCurve t - 1‖) (𝓝[<] (0 : ℝ))
      (𝓝 (deriv (fun t : ℝ => ‖chordCurve t - 1‖) 0)) :=
    (hd.hasDerivAt.tendsto_slope_zero_left).congr'
      (Eventually.of_forall fun t => by simp [hzero])
  have hnormRight : Tendsto (fun t : ℝ => ‖t⁻¹ • (chordCurve t - 1)‖) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * Real.pi)) := by
    have h := (continuous_norm.tendsto ((2 * Real.pi : ℂ) * Complex.I)).comp
      (tendsto_inv_smul_chordCurve.mono_left (nhdsGT_le_nhdsNE 0))
    rw [Function.comp_def, norm_two_pi_I] at h
    exact h
  have hnormLeft : Tendsto (fun t : ℝ => ‖t⁻¹ • (chordCurve t - 1)‖) (𝓝[<] (0 : ℝ))
      (𝓝 (2 * Real.pi)) := by
    have h := (continuous_norm.tendsto ((2 * Real.pi : ℂ) * Complex.I)).comp
      (tendsto_inv_smul_chordCurve.mono_left (nhdsLT_le_nhdsNE 0))
    rw [Function.comp_def, norm_two_pi_I] at h
    exact h
  have heqRight : (fun t : ℝ => ‖t⁻¹ • (chordCurve t - 1)‖) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t⁻¹ * ‖chordCurve t - 1‖) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  have heqLeft : (fun t : ℝ => -‖t⁻¹ • (chordCurve t - 1)‖) =ᶠ[𝓝[<] (0 : ℝ)]
      (fun t : ℝ => t⁻¹ * ‖chordCurve t - 1‖) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hneg : t⁻¹ < 0 := inv_neg''.mpr ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg hneg]
    ring
  have hright2 : Tendsto (fun t : ℝ => t⁻¹ * ‖chordCurve t - 1‖) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * Real.pi)) := hnormRight.congr' heqRight
  have hleft2 : Tendsto (fun t : ℝ => t⁻¹ * ‖chordCurve t - 1‖) (𝓝[<] (0 : ℝ))
      (𝓝 (-(2 * Real.pi))) := hnormLeft.neg.congr' heqLeft
  have h1 : deriv (fun t : ℝ => ‖chordCurve t - 1‖) 0 = 2 * Real.pi :=
    tendsto_nhds_unique hright hright2
  have h2 : deriv (fun t : ℝ => ‖chordCurve t - 1‖) 0 = -(2 * Real.pi) :=
    tendsto_nhds_unique hleft hleft2
  have hsum : (2 : ℝ) * Real.pi = -(2 * Real.pi) := h1.symm.trans h2
  linarith [Real.pi_pos]

def chordLengthLoop : Surgery.Topology.ContinuousFreeLoop ℝ :=
  ⟨fun θ : Surgery.Topology.Circle => ‖(AddCircle.toCircle θ : ℂ) - 1‖,
    continuous_norm.comp
      ((continuous_subtype_val.comp AddCircle.continuous_toCircle).sub continuous_const)⟩

def chordLengthDiskMap : C(Disk, ℝ) :=
  ⟨fun z : Disk => ‖(z : ℂ) - 1‖,
    continuous_norm.comp (continuous_subtype_val.sub continuous_const)⟩

theorem chordLengthDiskMap_lipschitz :
    ∃ L : ℝ≥0, ∀ z w : Disk,
      riemannianEDistOf (Geometry.standardEuclideanMetric ℝ) (chordLengthDiskMap z)
        (chordLengthDiskMap w) ≤ (L : ℝ≥0∞) * edist z w := by
  refine ⟨1, fun z w => ?_⟩
  rw [Geometry.riemannianEDistOf_standardEuclideanMetric, ENNReal.coe_one, one_mul, edist_dist,
    edist_dist, Real.dist_eq, Subtype.dist_eq, dist_eq_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  calc |‖(z : ℂ) - 1‖ - ‖(w : ℂ) - 1‖| ≤ ‖((z : ℂ) - 1) - ((w : ℂ) - 1)‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖(z : ℂ) - (w : ℂ)‖ := by ring_nf

def chordLengthDiskCompetitor :
    DiskCompetitor (Geometry.standardEuclideanMetric ℝ) chordLengthLoop :=
  ⟨⟨chordLengthDiskMap, chordLengthDiskMap_lipschitz⟩, fun _ => rfl⟩

private theorem loopLift_chordLengthLoop :
    loopLift chordLengthLoop = fun t : ℝ => ‖chordCurve t - 1‖ := by
  funext t
  change ‖((AddCircle.toCircle (t : Surgery.Topology.Circle) : _root_.Circle) : ℂ) - 1‖ =
    ‖chordCurve t - 1‖
  rw [chordCurve, chordLineCurve, AddCircle.toCircle_apply_mk t, Circle.coe_exp]
  norm_num

private theorem not_differentiableAt_loopLift_chordLengthLoop :
    ¬ DifferentiableAt ℝ (loopLift chordLengthLoop) 0 := by
  rw [loopLift_chordLengthLoop]
  exact not_differentiableAt_chordCurveNorm

theorem not_contMDiff_loopLift_chordLengthLoop :
    ¬ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (loopLift chordLengthLoop) := by
  intro h
  have h1 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (loopLift chordLengthLoop) 0 :=
    h.contMDiffAt (x := 0)
  have h2 : ContDiffAt ℝ ∞ (loopLift chordLengthLoop) 0 :=
    contMDiffAt_iff_contDiffAt.mp h1
  exact not_differentiableAt_loopLift_chordLengthLoop (h2.differentiableAt (by simp))

theorem not_hasDiskSmoothExtensionDensity_chordLengthLoop :
    ¬ HasDiskSmoothExtensionDensity (I := 𝓘(ℝ, ℝ)) (Q := ℝ)
      (Geometry.standardEuclideanMetric ℝ) chordLengthLoop :=
  not_hasDiskSmoothExtensionDensity_of_not_contMDiff (Geometry.standardEuclideanMetric ℝ)
    chordLengthLoop chordLengthDiskCompetitor not_contMDiff_loopLift_chordLengthLoop

theorem not_plateauDiskDensity_chordLengthLoop :
    ¬ PlateauDiskDensity (I := 𝓘(ℝ, ℝ)) (Q := ℝ)
      (Geometry.standardEuclideanMetric ℝ) chordLengthLoop :=
  not_plateauDiskDensity_of_not_contMDiff (Geometry.standardEuclideanMetric ℝ) chordLengthLoop
    chordLengthDiskCompetitor not_contMDiff_loopLift_chordLengthLoop

end EuclideanLine

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
