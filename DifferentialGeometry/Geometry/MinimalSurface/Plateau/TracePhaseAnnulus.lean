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


def tracePhaseAnnulusStrip (γ : loopCircle → M) (δ : loopCircle → ℝ) (p : ℝ × loopCircle) : M :=
  tracePhaseAnnulus γ δ (projIcc 0 1 zero_le_one p.1, p.2)

omit [FiniteDimensional ℝ E] [TopologicalSpace M] in
theorem tracePhaseAnnulusStrip_eq_of_mem {γ : loopCircle → M} {δ : loopCircle → ℝ}
    {p : ℝ × loopCircle} (hp : p.1 ∈ Icc 0 1) :
    tracePhaseAnnulusStrip γ δ p = tracePhaseAnnulus γ δ p := by
  simp only [tracePhaseAnnulusStrip, projIcc_of_mem zero_le_one hp]

omit [FiniteDimensional ℝ E] [TopologicalSpace M] in
theorem tracePhaseAnnulusStrip_zero {γ : loopCircle → M} {δ : loopCircle → ℝ} {ψ : ℝ → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t) {σ : C(loopCircle, loopCircle)}
    (hl : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) (θ : loopCircle) :
    tracePhaseAnnulusStrip γ δ (0, θ) = γ (σ θ) :=
  (tracePhaseAnnulusStrip_eq_of_mem (left_mem_Icc.mpr zero_le_one)).trans
    (tracePhaseAnnulus_zero hδ hl θ)

omit [FiniteDimensional ℝ E] [TopologicalSpace M] in
theorem tracePhaseAnnulusStrip_one {γ : loopCircle → M} {δ : loopCircle → ℝ} (θ : loopCircle) :
    tracePhaseAnnulusStrip γ δ (1, θ) = γ θ :=
  (tracePhaseAnnulusStrip_eq_of_mem (right_mem_Icc.mpr zero_le_one)).trans
    (tracePhaseAnnulus_one θ)

omit [FiniteDimensional ℝ E] in
theorem tracePhaseAnnulus_lipschitzOn_strip (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : loopCircle → M} {δ : loopCircle → ℝ} {Lγ Lδ : ℝ≥0}
    (hγ : ∀ s t : loopCircle, riemannianEDistOf g (γ s) (γ t) ≤ (Lγ : ℝ≥0∞) * edist s t)
    (hδ : LipschitzWith Lδ δ) :
    ∃ K : ℝ≥0, ∀ p q : ℝ × loopCircle, p.1 ∈ Icc 0 1 → q.1 ∈ Icc 0 1 →
      riemannianEDistOf g (tracePhaseAnnulus γ δ p) (tracePhaseAnnulus γ δ q) ≤
        (K : ℝ≥0∞) * edist p q := by
  have hM0 : 0 ≤ (Lδ : ℝ) * (1 / 2) + |δ 0| := by positivity
  set Mδ : ℝ≥0 := ⟨(Lδ : ℝ) * (1 / 2) + |δ 0|, hM0⟩ with hMδdef
  have hMδcoe : (Mδ : ℝ) = (Lδ : ℝ) * (1 / 2) + |δ 0| := rfl
  have hbdd (θ : loopCircle) : |δ θ| ≤ (Mδ : ℝ) := by
    have h1 : ‖δ θ - δ 0‖ ≤ (Lδ : ℝ) * dist θ 0 := by
      simpa only [dist_eq_norm] using hδ.dist_le_mul θ 0
    have h2 : dist θ (0 : loopCircle) ≤ 1 / 2 := by
      rw [dist_eq_norm, sub_zero]
      simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := θ) one_ne_zero
    have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 Lδ.coe_nonneg)
    calc
      |δ θ| = ‖δ θ - δ 0 + δ 0‖ := by rw [sub_add_cancel]; exact (Real.norm_eq_abs _).symm
      _ ≤ ‖δ θ - δ 0‖ + ‖δ 0‖ := norm_add_le _ _
      _ ≤ (Mδ : ℝ) := by
        have h0 : ‖δ 0‖ = |δ 0| := Real.norm_eq_abs _
        rw [hMδcoe, h0]
        linarith
  have hΦ : ∀ p : ℝ × loopCircle,
      tracePhaseAnnulus γ δ p = γ (p.2 + (((1 - p.1) * δ p.2 : ℝ) : loopCircle)) := fun p => rfl
  have hreal : ∀ p q : ℝ × loopCircle, p.1 ∈ Icc 0 1 → q.1 ∈ Icc 0 1 →
      dist (p.2 + (((1 - p.1) * δ p.2 : ℝ) : loopCircle))
        (q.2 + (((1 - q.1) * δ q.2 : ℝ) : loopCircle)) ≤
        ((1 + Lδ + Mδ : ℝ≥0) : ℝ) * dist p q := by
    intro p q hp hq
    obtain ⟨a, d, ha0, ha1, hd0, hd1, haq, had, hdist⟩ := exists_short_circle_lifts p.2 q.2
    have hpp : p.2 + (((1 - p.1) * δ p.2 : ℝ) : loopCircle) =
        (((a + d) + (1 - p.1) * δ p.2 : ℝ) : loopCircle) := by
      rw [← had, ← AddCircle.coe_add]
    have hqq : q.2 + (((1 - q.1) * δ q.2 : ℝ) : loopCircle) =
        (((a) + (1 - q.1) * δ q.2 : ℝ) : loopCircle) := by
      rw [← haq, ← AddCircle.coe_add]
    rw [hpp, hqq, dist_eq_norm]
    have hsub : (((a + d) + (1 - p.1) * δ p.2 : ℝ) : loopCircle) -
        (((a) + (1 - q.1) * δ q.2 : ℝ) : loopCircle) =
        ((d + (1 - p.1) * δ p.2 - (1 - q.1) * δ q.2 : ℝ) : loopCircle) := by
      rw [← AddCircle.coe_sub]
      congr 1
      ring
    rw [hsub]
    refine (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ))).trans ?_
    rw [Real.norm_eq_abs]
    have hd_le : |d| ≤ dist p q := by
      rw [Prod.dist_eq, ← hdist]
      exact le_max_right _ _
    have hr_le : |p.1 - q.1| ≤ dist p q := by
      rw [← Real.dist_eq, Prod.dist_eq]
      exact le_max_left _ _
    have hr1 : |1 - p.1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
    have hδd : |δ p.2 - δ q.2| ≤ (Lδ : ℝ) * |d| := by
      have h := hδ.dist_le_mul p.2 q.2
      rw [Real.dist_eq] at h
      rw [hdist] at h
      exact h
    have hδb : |δ q.2| ≤ (Mδ : ℝ) := hbdd q.2
    have hdiff : (1 - p.1) * δ p.2 - (1 - q.1) * δ q.2 =
        (1 - p.1) * (δ p.2 - δ q.2) + (q.1 - p.1) * δ q.2 := by ring
    have hcd : |(1 - p.1) * δ p.2 - (1 - q.1) * δ q.2| ≤
        (Lδ : ℝ) * dist p q + (Mδ : ℝ) * dist p q := by
      rw [hdiff]
      have h4 : |(1 - p.1) * (δ p.2 - δ q.2)| ≤ (Lδ : ℝ) * dist p q := by
        rw [abs_mul]
        have h41 : |1 - p.1| * |δ p.2 - δ q.2| ≤ 1 * |δ p.2 - δ q.2| :=
          mul_le_mul_of_nonneg_right hr1 (abs_nonneg _)
        have h42 : (1 : ℝ) * |δ p.2 - δ q.2| ≤ (Lδ : ℝ) * |d| := by
          rw [one_mul]
          exact hδd
        have h44 : (Lδ : ℝ) * |d| ≤ (Lδ : ℝ) * dist p q :=
          mul_le_mul_of_nonneg_left hd_le Lδ.coe_nonneg
        linarith [h41, h42, h44]
      have h5 : |(q.1 - p.1) * δ q.2| ≤ (Mδ : ℝ) * dist p q := by
        rw [abs_mul, abs_sub_comm]
        have h51 : |p.1 - q.1| * |δ q.2| ≤ dist p q * |δ q.2| :=
          mul_le_mul_of_nonneg_right hr_le (abs_nonneg _)
        have h52 : dist p q * |δ q.2| ≤ dist p q * (Mδ : ℝ) :=
          mul_le_mul_of_nonneg_left hδb (dist_nonneg)
        linarith [h51, h52]
      exact (abs_add_le _ _).trans (add_le_add h4 h5)
    have htot : |d + ((1 - p.1) * δ p.2 - (1 - q.1) * δ q.2)| ≤
        ((1 + Lδ + Mδ : ℝ≥0) : ℝ) * dist p q := by
      have h1 : |d + ((1 - p.1) * δ p.2 - (1 - q.1) * δ q.2)| ≤
          |d| + |(1 - p.1) * δ p.2 - (1 - q.1) * δ q.2| := abs_add_le _ _
      have h2 : |d| + ((Lδ : ℝ) * dist p q + (Mδ : ℝ) * dist p q) ≤
          ((1 + Lδ + Mδ : ℝ≥0) : ℝ) * dist p q := by
        push_cast
        nlinarith [dist_nonneg (x := p) (y := q)]
      have h3 : |d + ((1 - p.1) * δ p.2 - (1 - q.1) * δ q.2)| ≤
          |d| + ((Lδ : ℝ) * dist p q + (Mδ : ℝ) * dist p q) :=
        h1.trans (add_le_add le_rfl hcd)
      exact h3.trans h2
    have hre : d + (1 - p.1) * δ p.2 - (1 - q.1) * δ q.2 =
        d + ((1 - p.1) * δ p.2 - (1 - q.1) * δ q.2) := by ring
    rw [hre]
    exact htot
  refine ⟨Lγ * (1 + Lδ + Mδ), fun p q hp hq => ?_⟩
  have hstep : edist (p.2 + (((1 - p.1) * δ p.2 : ℝ) : loopCircle))
      (q.2 + (((1 - q.1) * δ q.2 : ℝ) : loopCircle)) ≤
      ((1 + Lδ + Mδ : ℝ≥0) : ℝ≥0∞) * edist p q := by
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal (p := (1 + Lδ + Mδ : ℝ≥0)),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((1 + Lδ + Mδ : ℝ≥0) : ℝ))]
    exact ENNReal.ofReal_le_ofReal (hreal p q hp hq)
  rw [hΦ p, hΦ q]
  calc riemannianEDistOf g (γ (p.2 + (((1 - p.1) * δ p.2 : ℝ) : loopCircle)))
        (γ (q.2 + (((1 - q.1) * δ q.2 : ℝ) : loopCircle)))
      ≤ (Lγ : ℝ≥0∞) * edist (p.2 + (((1 - p.1) * δ p.2 : ℝ) : loopCircle))
          (q.2 + (((1 - q.1) * δ q.2 : ℝ) : loopCircle)) := hγ _ _
    _ ≤ (Lγ : ℝ≥0∞) * (((1 + Lδ + Mδ : ℝ≥0) : ℝ≥0∞) * edist p q) :=
        mul_le_mul' le_rfl hstep
    _ = ((Lγ * (1 + Lδ + Mδ) : ℝ≥0) : ℝ≥0∞) * edist p q := by
        rw [ENNReal.coe_mul, mul_assoc]

omit [FiniteDimensional ℝ E] in
theorem tracePhaseAnnulusStrip_lipschitz_of_strip (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : loopCircle → M} {δ : loopCircle → ℝ} {K : ℝ≥0}
    (hK : ∀ p q : ℝ × loopCircle, p.1 ∈ Icc 0 1 → q.1 ∈ Icc 0 1 →
      riemannianEDistOf g (tracePhaseAnnulus γ δ p) (tracePhaseAnnulus γ δ q) ≤
        (K : ℝ≥0∞) * edist p q) :
    ∃ C : ℝ≥0, ∀ p q : ℝ × loopCircle,
      riemannianEDistOf g (tracePhaseAnnulusStrip γ δ p) (tracePhaseAnnulusStrip γ δ q) ≤
        (C : ℝ≥0∞) * edist p q := by
  have h1 : ∀ p q : ℝ × loopCircle,
      edist ((projIcc 0 1 zero_le_one p.1 : ℝ), p.2)
        ((projIcc 0 1 zero_le_one q.1 : ℝ), q.2) ≤ edist p q := by
    intro p q
    have hp : edist (projIcc 0 1 zero_le_one p.1) (projIcc 0 1 zero_le_one q.1) ≤
        edist p.1 q.1 := by
      simpa only [ENNReal.coe_one, one_mul] using
        (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1)).edist_le_mul p.1 q.1
    rw [Prod.edist_eq (x := ((projIcc 0 1 zero_le_one p.1 : ℝ), p.2))
        (y := ((projIcc 0 1 zero_le_one q.1 : ℝ), q.2)), Prod.edist_eq (x := p) (y := q)]
    exact max_le (hp.trans (le_max_left _ _)) (le_max_right _ _)
  refine ⟨K, fun p q => ?_⟩
  exact (hK _ _ (projIcc 0 1 zero_le_one p.1).property
    (projIcc 0 1 zero_le_one q.1).property).trans (mul_le_mul' le_rfl (h1 p q))

omit [FiniteDimensional ℝ E] in
theorem cylinderArea_tracePhaseAnnulusStrip_eq_zero [CompactSpace M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {δ : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t) :
    cylinderArea g (tracePhaseAnnulusStrip γ δ) = 0 := by
  have hdens : ∀ᵐ z ∂(volume.restrict unitSquare),
      riemannianAreaDensity g (cylinderLift (tracePhaseAnnulusStrip γ δ)) z =
        riemannianAreaDensity g (cylinderLift (tracePhaseAnnulus γ δ)) z := by
    have hmem : ∀ᵐ z ∂(volume.restrict unitSquare), z.re ∈ Ioo (0 : ℝ) 1 := by
      filter_upwards [ae_restrict_mem isCompact_unitSquare.measurableSet,
        ae_restrict_of_ae (ae_complex_re_ne 0), ae_restrict_of_ae (ae_complex_re_ne 1)]
        with z hz h0 h1
      exact ⟨lt_of_le_of_ne hz.1.1 h0.symm, lt_of_le_of_ne hz.1.2 h1⟩
    filter_upwards [hmem] with z hz
    exact riemannianAreaDensity_congr g (by
      filter_upwards [(isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hz] with w hw
      simp only [cylinderLift, tracePhaseAnnulusStrip,
        projIcc_of_mem zero_le_one (Ioo_subset_Icc_self hw)])
  calc cylinderArea g (tracePhaseAnnulusStrip γ δ)
      = ∫ z in unitSquare, riemannianAreaDensity g (cylinderLift (tracePhaseAnnulus γ δ)) z := by
        rw [cylinderArea, riemannianArea]
        exact integral_congr_ae hdens
    _ = cylinderArea g (tracePhaseAnnulus γ δ) := by rw [cylinderArea, riemannianArea]
    _ = 0 := cylinderArea_tracePhaseAnnulus_eq_zero g hγ hψ hδ

theorem exists_spanningDiskCompetitor_of_tracePhase_lipschitz [CompactSpace M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {σ : C(loopCircle, loopCircle)} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hl : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) {δ : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {u : C(closedDisk, M)} (htrace : diskTrace u = γ.comp σ)
    (hLip : ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hHlip : ∃ K : ℝ≥0, ∀ p q : ℝ × loopCircle, p.1 ∈ Icc 0 1 → q.1 ∈ Icc 0 1 →
      riemannianEDistOf g (tracePhaseAnnulus γ δ p) (tracePhaseAnnulus γ δ q) ≤
        (K : ℝ≥0∞) * edist p q) :
    ∃ v ∈ spanningDiskCompetitors g γ, riemannianDiskArea g v = riemannianDiskArea g u := by
  obtain ⟨L, hL⟩ := hLip
  obtain ⟨K, hK⟩ := hHlip
  obtain ⟨C, hC⟩ := tracePhaseAnnulusStrip_lipschitz_of_strip g hK
  let U : ℂ → M := diskExtension u
  let H : ℝ × loopCircle → M := tracePhaseAnnulusStrip γ δ
  have hUlip : ∀ z w : ℂ, riemannianEDistOf g (U z) (U w) ≤ (L : ℝ≥0∞) * edist z w :=
    diskExtension_riemannian_lipschitz g hL
  have hHlipC : ∀ p q : ℝ × loopCircle,
      riemannianEDistOf g (H p) (H q) ≤ (C : ℝ≥0∞) * edist p q := hC
  have hglue (θ : loopCircle) : U (AddCircle.toCircle θ : ℂ) = H (0, θ) := by
    have ht : u (diskBoundary θ) = γ (σ θ) :=
      congrArg (fun f : freeLoop M => f θ) htrace
    change diskExtension u (diskBoundary θ) = tracePhaseAnnulusStrip γ δ (0, θ)
    rw [diskExtension_coe]
    exact ht.trans (tracePhaseAnnulusStrip_zero hδ hl θ).symm
  obtain ⟨Ka, hKa⟩ := attachDiskAnnulus_riemannian_lipschitz g hUlip hHlipC hglue
  let v : C(closedDisk, M) := ⟨fun z => attachDiskAnnulus U H z,
    (continuous_of_riemannian_lipschitz g hKa).comp continuous_subtype_val⟩
  have hvtrace : diskTrace v = γ := by
    ext θ
    change attachDiskAnnulus U H (AddCircle.toCircle θ : ℂ) = γ θ
    rw [attachDiskAnnulus_boundary]
    exact tracePhaseAnnulusStrip_one θ
  refine ⟨v, ⟨hvtrace, Ka, fun z w => hKa z w⟩, ?_⟩
  rw [riemannianDiskArea_eq_of_extension g v (attachDiskAnnulus U H) (fun _ => rfl),
    attachDiskAnnulus_area g hUlip hHlipC hglue,
    cylinderArea_tracePhaseAnnulusStrip_eq_zero g hγ hψ hδ]
  simp [riemannianDiskArea, U]


end DifferentialGeometry.Geometry
