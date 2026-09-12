import DifferentialGeometry.Geometry.Measure.Area.ManifoldDensity
import DifferentialGeometry.Topology.LoopSpace.Lipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import DifferentialGeometry.Geometry.Measure.Area.CylinderArea
import DifferentialGeometry.Geometry.Measure.Area.AttachmentArea
import DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors
import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter Function MeasureTheory
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem periodic_lift_continuous {f : ℝ → ℝ}
    (hf : Function.Periodic f 1) (hc : Continuous f) : Continuous hf.lift := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (fun x : ℝ => hf.lift (x : loopCircle))
  simpa only [Function.Periodic.lift_coe] using hc

private theorem exists_short_circle_lifts (x y : loopCircle) :
    ∃ a d : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ -(1 / 2 : ℝ) ≤ d ∧ d ≤ 1 / 2 ∧
      (a : loopCircle) = y ∧ ((a + d : ℝ) : loopCircle) = x ∧
      dist x y = |d| := by
  let a := AddCircle.equivIco (1 : ℝ) 0 y
  let d := AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (x - y)
  have ha : 0 ≤ a.1 ∧ a.1 < 1 := by simpa using a.2
  have hd : -(1 / 2 : ℝ) ≤ d.1 ∧ d.1 < 1 / 2 := by convert d.2 using 1; norm_num
  have haq : (a.1 : loopCircle) = y := AddCircle.coe_equivIco
  have hdq : (d.1 : loopCircle) = x - y := AddCircle.coe_equivIco
  have hadq : ((a.1 + d.1 : ℝ) : loopCircle) = x := by
    rw [AddCircle.coe_add, haq, hdq]
    abel
  have hdabs : |d.1| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one, abs_le]
    exact ⟨hd.1, hd.2.le⟩
  have hnorm : ‖(d.1 : loopCircle)‖ = |d.1| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hdabs
  refine ⟨a.1, d.1, ha.1, ha.2.le, hd.1, hd.2.le, haq, hadq, ?_⟩
  rw [dist_eq_norm, ← hdq]
  exact hnorm

private theorem periodic_smooth_lift_lipschitz {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃ L : ℝ≥0, LipschitzWith L hp.lift := by
  have hderiv := hf.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2)).exists_bound_of_continuousOn
    hderiv.continuousOn
  refine ⟨NNReal.mk (max 0 C) (le_max_left _ _), ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨a, d, ha0, ha1, hd0, hd1, hay, hadx, hdist⟩ := exists_short_circle_lifts x y
  have ha : a ∈ Icc (-1 : ℝ) 2 := by constructor <;> linarith
  have had : a + d ∈ Icc (-1 : ℝ) 2 := by constructor <;> linarith
  have hconv : Convex ℝ (Icc (-1 : ℝ) 2) := convex_Icc _ _
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hf.differentiable (by simp) x)
    (fun x hx => (hC x hx).trans (le_max_right 0 C)) hconv ha had
  have hx : hp.lift x = f (a + d) := by rw [← hadx]; rfl
  have hy : hp.lift y = f a := by rw [← hay]; rfl
  rw [hx, hy, hdist, dist_eq_norm]
  simpa only [NNReal.coe_mk, add_sub_cancel_left, Real.norm_eq_abs] using hb

omit [FiniteDimensional ℝ E] in
theorem tangentTwoJacobian_smul_smul (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {x : M}
    (v : TangentSpace 𝓘(ℝ, E) x) (a b : ℝ) :
    tangentTwoJacobian g (a • v) (b • v) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [tangentTwoJacobian]
  · have h : b • v = (b / a) • (a • v) := by rw [smul_smul, div_mul_cancel₀ b ha]
    rw [h, tangentTwoJacobian_smul_self]

omit [FiniteDimensional ℝ E] in
theorem riemannianAreaDensity_comp_curve_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : ℝ → M} {φ : ℂ → ℝ} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) f (φ z))
    (hφ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) φ z) :
    riemannianAreaDensity g (f ∘ φ) z = 0 := by
  let A : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (f (φ z)) := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) f (φ z)
  let B : ℂ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) φ z
  have hchain : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (f ∘ φ) z = A.comp B := by
    rw [mfderiv_comp z hf hφ]
    rfl
  have hval (v : ℂ) : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (f ∘ φ) z v = (B v) • A 1 := by
    rw [hchain]
    change A (B v) = (B v) • A 1
    simpa using ContinuousLinearMap.map_smul A (B v) (1 : ℝ)
  rw [riemannianAreaDensity, hval 1, hval Complex.I, tangentTwoJacobian_smul_smul]

theorem IsSmoothPositiveCircleMap.exists_lipschitz_displacement {σ : C(loopCircle, loopCircle)}
    (h : IsSmoothPositiveCircleMap σ) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧ (∀ t : ℝ, ψ (t + 1) = ψ t + 1) ∧
      (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧
      ∃ δ : loopCircle → ℝ,
        (∀ t : ℝ, δ (t : loopCircle) = ψ t - t) ∧ ∃ L : ℝ≥0, LipschitzWith L δ := by
  obtain ⟨ψ, hψ, hm, hp, hl⟩ := h
  refine ⟨ψ, hψ, hm, hp, hl, ?_⟩
  have hper : Function.Periodic (fun t : ℝ => ψ t - t) 1 := by
    intro t
    change ψ (t + 1) - (t + 1) = ψ t - t
    rw [hp t]
    ring
  refine ⟨hper.lift, ?_, ?_⟩
  · intro t
    exact hper.lift_coe t
  · exact periodic_smooth_lift_lipschitz (hψ.sub contDiff_id) hper

omit [FiniteDimensional ℝ E] in
theorem riemannianAreaDensity_phaseLift_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (z : ℂ) :
    riemannianAreaDensity g
      (fun w : ℂ => γ ((((1 - w.re) * ψ w.im + w.re * w.im : ℝ)) : loopCircle)) z = 0 := by
  let φ : ℂ → ℝ := fun w => (1 - w.re) * ψ w.im + w.re * w.im
  have hphase : ContDiff ℝ ∞ φ :=
    ((contDiff_const.sub Complex.reCLM.contDiff).mul
      (hψ.comp Complex.imCLM.contDiff)).add
      (Complex.reCLM.contDiff.mul Complex.imCLM.contDiff)
  have hfun : (fun w : ℂ => γ ((((1 - w.re) * ψ w.im + w.re * w.im : ℝ)) : loopCircle)) =
      (fun t : ℝ => γ (t : loopCircle)) ∘ φ := rfl
  rw [hfun]
  exact riemannianAreaDensity_comp_curve_eq_zero g
    (hγ.mdifferentiable (by simp) (φ z)) (hphase.contMDiff.mdifferentiable (by simp) z)

def tracePhaseAnnulus (γ : loopCircle → M) (δ : loopCircle → ℝ) : ℝ × loopCircle → M :=
  fun p => γ (p.2 + (((1 - p.1) * δ p.2 : ℝ) : loopCircle))

omit [FiniteDimensional ℝ E] [TopologicalSpace M] in
theorem cylinderLift_tracePhaseAnnulus {γ : loopCircle → M} {δ : loopCircle → ℝ}
    {ψ : ℝ → ℝ} (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t) (z : ℂ) :
    cylinderLift (tracePhaseAnnulus γ δ) z =
      γ ((((1 - z.re) * ψ z.im + z.re * z.im : ℝ)) : loopCircle) := by
  simp only [cylinderLift, tracePhaseAnnulus]
  refine congrArg γ ?_
  rw [← AddCircle.coe_add, hδ]
  exact congrArg (fun r : ℝ => (r : loopCircle)) (by ring)

omit [FiniteDimensional ℝ E] in
theorem cylinderArea_tracePhaseAnnulus_eq_zero [CompactSpace M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {δ : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t) :
    cylinderArea g (tracePhaseAnnulus γ δ) = 0 := by
  have hfun : cylinderLift (tracePhaseAnnulus γ δ) =
      fun z : ℂ => γ ((((1 - z.re) * ψ z.im + z.re * z.im : ℝ)) : loopCircle) :=
    funext fun z => cylinderLift_tracePhaseAnnulus hδ z
  rw [cylinderArea, hfun, riemannianArea]
  calc
    ∫ z in unitSquare, riemannianAreaDensity g
        (fun z : ℂ => γ ((((1 - z.re) * ψ z.im + z.re * z.im : ℝ)) : loopCircle)) z
        = ∫ _z in unitSquare, (0 : ℝ) :=
      setIntegral_congr_fun isCompact_unitSquare.measurableSet
        (fun z _ => riemannianAreaDensity_phaseLift_eq_zero g hγ hψ z)
    _ = 0 := integral_zero _ _

omit [FiniteDimensional ℝ E] [TopologicalSpace M] in
theorem tracePhaseAnnulus_zero {γ : loopCircle → M} {δ : loopCircle → ℝ} {ψ : ℝ → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t) {σ : C(loopCircle, loopCircle)}
    (hl : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) (θ : loopCircle) :
    tracePhaseAnnulus γ δ (0, θ) = γ (σ θ) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  simp only [tracePhaseAnnulus]
  refine congrArg γ ?_
  rw [hδ t, ← AddCircle.coe_add]
  exact (congrArg (fun r : ℝ => (r : loopCircle)) (by ring)).trans (hl t)

omit [FiniteDimensional ℝ E] [TopologicalSpace M] in
theorem tracePhaseAnnulus_one {γ : loopCircle → M} {δ : loopCircle → ℝ} (θ : loopCircle) :
    tracePhaseAnnulus γ δ (1, θ) = γ θ := by
  simp [tracePhaseAnnulus]

theorem exists_spanningDiskCompetitor_of_tracePhase_lipschitz [CompactSpace M] [T3Space M]
    [PreconnectedSpace M] (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {σ : C(loopCircle, loopCircle)} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hl : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) {δ : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {u : C(closedDisk, M)} (htrace : diskTrace u = γ.comp σ)
    (hLip : ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hHlip : ∃ K : ℝ≥0, ∀ p q : ℝ × loopCircle,
      riemannianEDistOf g (tracePhaseAnnulus γ δ p) (tracePhaseAnnulus γ δ q) ≤
        (K : ℝ≥0∞) * edist p q) :
    ∃ v ∈ spanningDiskCompetitors g γ, riemannianDiskArea g v = riemannianDiskArea g u := by
  obtain ⟨L, hL⟩ := hLip
  obtain ⟨K, hK⟩ := hHlip
  let U : ℂ → M := diskExtension u
  let H : ℝ × loopCircle → M := tracePhaseAnnulus γ δ
  have hUlip : ∀ z w : ℂ, riemannianEDistOf g (U z) (U w) ≤ (L : ℝ≥0∞) * edist z w :=
    diskExtension_riemannian_lipschitz g hL
  have hglue (θ : loopCircle) : U (AddCircle.toCircle θ : ℂ) = H (0, θ) := by
    have ht : u (diskBoundary θ) = γ (σ θ) :=
      congrArg (fun f : freeLoop M => f θ) htrace
    change diskExtension u (diskBoundary θ) = tracePhaseAnnulus γ δ (0, θ)
    rw [diskExtension_coe]
    exact ht.trans (tracePhaseAnnulus_zero hδ hl θ).symm
  obtain ⟨Ka, hKa⟩ := attachDiskAnnulus_riemannian_lipschitz g hUlip hK hglue
  let v : C(closedDisk, M) := ⟨fun z => attachDiskAnnulus U H z,
    (continuous_of_riemannian_lipschitz g hKa).comp continuous_subtype_val⟩
  have hvtrace : diskTrace v = γ := by
    ext θ
    change attachDiskAnnulus U H (AddCircle.toCircle θ : ℂ) = γ θ
    rw [attachDiskAnnulus_boundary]
    exact tracePhaseAnnulus_one θ
  refine ⟨v, ⟨hvtrace, Ka, fun z w => hKa z w⟩, ?_⟩
  rw [riemannianDiskArea_eq_of_extension g v (attachDiskAnnulus U H) (fun _ => rfl),
    attachDiskAnnulus_area g hUlip hK hglue,
    cylinderArea_tracePhaseAnnulus_eq_zero g hγ hψ hδ]
  simp [riemannianDiskArea, U]

end DifferentialGeometry.Geometry
