import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Topology.FiberBundle.Separation

/-!
# Distances of smooth approximants of a finite-regularity metric

Lane CM-A (package CM5 of the D-FOUND design, `docs/geometrization/chapter13/
design-finite-surface-foundations-20261004.md` §C1). The distance of a finite-regularity metric
`g` is the length distance of the ambient Riemannian bundle (`IsRiemannianManifold I M`) whose
norm is the `g`-norm (`hnorm`, the inline finite form of `IsMetricNorm`); it is defined for
continuous metrics. A smooth metric `h` with `c₁² g ≤ h ≤ c₂² g` pointwise has length distance
`riemannianEDistOf h` between `c₁ d` and `c₂ d`.

For such an `h` the extended metric `inducedEMetricSpace h` has the given topology definitionally,
so with the finiteness of its distance it is a metric space structure `m` on `M` to which the
smooth comparison kernels apply (`ChartedSpace`, `IsManifold`, `SigmaCompactSpace` transfer by
definitional equality). It is complete when the ambient distance is, and then closed balls of the
ambient distance are compact (Hopf–Rinow for `h`).

## Main declarations
* `riemannianEDistOf_le_ofReal_mul_edist`, `ofReal_mul_edist_le_riemannianEDistOf`: the
  two-sided distance comparison.
* `riemannianMetricComplete_of_bilipschitz`: completeness of the approximant.
* `properSpace_of_bilipschitz_smooth`: the ambient distance is proper.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.FiniteComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- **Upper distance comparison.** If `h ≤ c² g` pointwise, the length distance of the smooth
metric `h` is at most `c` times the length distance of `g`. -/
theorem riemannianEDistOf_le_ofReal_mul_edist {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (h : SmoothRiemannianMetric I M) {c : ℝ} (hc : 0 < c)
    (hup : ∀ (x : M) (w : TangentSpace I x), h.inner x w w ≤ c ^ 2 * g.inner x w w)
    (x y : M) :
    riemannianEDistOf (I := I) h x y ≤ ENNReal.ofReal c * edist x y := by
  have ha0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hatop : ENNReal.ofReal c ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  rw [IsRiemannianManifold.out (I := I) x y, edistOf_iInf, Manifold.riemannianEDist,
    ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_mono fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_mono fun hγ => ?_
  rw [← lintegral_const_mul' _ _ hatop]
  refine lintegral_mono fun t => ?_
  rw [hnorm, ← ENNReal.ofReal_mul hc.le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt (h.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))
      ≤ Real.sqrt (c ^ 2 * g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1)) :=
        Real.sqrt_le_sqrt (hup _ _)
    _ = c * Real.sqrt (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1)) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]

/-- **Lower distance comparison.** If `c² g ≤ h` pointwise, the length distance of the smooth
metric `h` is at least `c` times the length distance of `g`. -/
theorem ofReal_mul_edist_le_riemannianEDistOf {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (h : SmoothRiemannianMetric I M) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ (x : M) (w : TangentSpace I x), c ^ 2 * g.inner x w w ≤ h.inner x w w)
    (x y : M) :
    ENNReal.ofReal c * edist x y ≤ riemannianEDistOf (I := I) h x y := by
  have ha0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hatop : ENNReal.ofReal c ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  rw [IsRiemannianManifold.out (I := I) x y, edistOf_iInf, Manifold.riemannianEDist,
    ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_mono fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_mono fun hγ => ?_
  rw [← lintegral_const_mul' _ _ hatop]
  refine lintegral_mono fun t => ?_
  rw [hnorm, ← ENNReal.ofReal_mul hc.le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc c * Real.sqrt (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))
      = Real.sqrt (c ^ 2 * g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1)) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
    _ ≤ Real.sqrt (h.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1)) :=
        Real.sqrt_le_sqrt (hlow _ _)

/-- A pseudo-extended-metric structure `m₂` with the topology of a complete one `m₁` and with
`edist₁ ≤ K · edist₂` is complete. -/
theorem completeSpace_of_edist_le_mul {X : Type*} (m₁ m₂ : PseudoEMetricSpace X)
    (h₁ : @CompleteSpace X m₁.toUniformSpace)
    (htop : m₂.toUniformSpace.toTopologicalSpace = m₁.toUniformSpace.toTopologicalSpace)
    (K : NNReal) (hle : ∀ a b : X, @edist X m₁.toEDist a b ≤ K * @edist X m₂.toEDist a b) :
    @CompleteSpace X m₂.toUniformSpace := by
  refine @CompleteSpace.mk X m₂.toUniformSpace fun {f} hf => ?_
  have hlip : @LipschitzWith X X m₂ m₁ K id := fun a b => hle a b
  have huc := @LipschitzWith.uniformContinuous X X m₂ m₁ K id hlip
  have hf₁ : @Cauchy X m₁.toUniformSpace f := by
    have h := @Cauchy.map X X m₂.toUniformSpace m₁.toUniformSpace f id hf huc
    rwa [Filter.map_id] at h
  obtain ⟨x, hx⟩ := @CompleteSpace.complete X m₁.toUniformSpace h₁ f hf₁
  refine ⟨x, ?_⟩
  rw [htop]
  exact hx

/-- The length distance of a smooth metric `h ≤ c² g` is finite. -/
theorem riemannianEDistOf_ne_top_of_le {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (h : SmoothRiemannianMetric I M) {c : ℝ} (hc : 0 < c)
    (hup : ∀ (x : M) (w : TangentSpace I x), h.inner x w w ≤ c ^ 2 * g.inner x w w) (x y : M) :
    riemannianEDistOf (I := I) h x y ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top x y))
    (riemannianEDistOf_le_ofReal_mul_edist g hnorm h hc hup x y)

/-- **Completeness of an approximant.** If the ambient distance is complete and `c² g ≤ h`, the
length distance of `h` is complete. -/
theorem completeSpace_inducedEMetricSpace_of_le [CompleteSpace M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (h : SmoothRiemannianMetric I M) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ (x : M) (w : TangentSpace I x), c ^ 2 * g.inner x w w ≤ h.inner x w w) :
    @CompleteSpace M (inducedEMetricSpace h).toPseudoEMetricSpace.toUniformSpace := by
  refine completeSpace_of_edist_le_mul (inferInstance : PseudoEMetricSpace M)
    (inducedEMetricSpace h).toPseudoEMetricSpace inferInstance rfl (Real.toNNReal c⁻¹)
    fun a b => ?_
  change edist a b ≤ (Real.toNNReal c⁻¹ : ℝ≥0∞) * riemannianEDistOf (I := I) h a b
  have hlow' := ofReal_mul_edist_le_riemannianEDistOf g hnorm h hc hlow a b
  have hcoe : ((Real.toNNReal c⁻¹ : NNReal) : ℝ≥0∞) = ENNReal.ofReal c⁻¹ := rfl
  rw [hcoe]
  calc edist a b = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * edist a b) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), inv_mul_cancel₀ hc.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal c⁻¹ * riemannianEDistOf (I := I) h a b := by gcongr

/-- **Properness.** If the ambient distance is complete and `c₁² g ≤ h ≤ c₂² g` for a smooth
metric `h`, the ambient distance is proper: its closed balls lie in closed `h`-balls, which are
compact by Hopf–Rinow for the complete smooth metric `h`. -/
theorem properSpace_of_bilipschitz_smooth [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [CompleteSpace M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (h : SmoothRiemannianMetric I M) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlow : ∀ (x : M) (w : TangentSpace I x), c₁ ^ 2 * g.inner x w w ≤ h.inner x w w)
    (hup : ∀ (x : M) (w : TangentSpace I x), h.inner x w w ≤ c₂ ^ 2 * g.inner x w w) :
    ProperSpace M := by
  have hRC : RiemannianMetricComplete (I := I) h :=
    ⟨completeSpace_inducedEMetricSpace_of_le g hnorm h hc₁ hlow⟩
  refine ProperSpace.of_isCompact_closedBall_of_le 0 fun p r hr => ?_
  refine (hRC.closedEBall_isCompact p (c₂ * r)).of_isClosed_subset Metric.isClosed_closedBall
    fun y hy => ?_
  change riemannianEDistOf (I := I) h p y ≤ ENNReal.ofReal (c₂ * r)
  have hpy : edist p y ≤ ENNReal.ofReal r := by
    rw [edist_dist, dist_comm]
    exact ENNReal.ofReal_le_ofReal (Metric.mem_closedBall.mp hy)
  calc riemannianEDistOf (I := I) h p y ≤ ENNReal.ofReal c₂ * edist p y :=
        riemannianEDistOf_le_ofReal_mul_edist g hnorm h hc₂ hup p y
    _ ≤ ENNReal.ofReal c₂ * ENNReal.ofReal r := by gcongr
    _ = ENNReal.ofReal (c₂ * r) := (ENNReal.ofReal_mul hc₂.le).symm

end DifferentialGeometry.Geometry.FiniteComparison
