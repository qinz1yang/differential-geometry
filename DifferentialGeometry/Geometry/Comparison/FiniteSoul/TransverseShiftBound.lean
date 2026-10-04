import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftInitial
import DifferentialGeometry.Analysis.ODE.ScalarJacobiComparison
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetricBounded
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness
import DifferentialGeometry.Geometry.Metric.Path.Speed

/-!
# S-SHIFT2: the transverse shift bound in dimension two

For a complete `C^(r+1)` metric, `r ≥ 3`, with `sec ≥ 0` on a surface, and a point `x`, `L > 0`, there is
`ρ > 0` such that for every unit geodesic `γ` starting within `ρ` of `x` and every continuous unit normal
`ξ` along it, the shifted curves `t ↦ exp_{γ t}(h ξ t)`, `0 ≤ h < ρ`, are `1`-Lipschitz on `[0, L]`
(`dist_transverse_shift_le_dim_two`, the finite form of the smooth `HasParallelShiftBound`).

Route: the transverse speed `G = |∂ₜα|²` of `α(t, h) = exp_{γ t}(h ξ t)` has `√G(t, ·)` solving
`j'' = -K j`, `j(0) = 1`, `j'(0) = 0` (`transverseShift_jacobi`, `deriv_sqrt_transverseSpeedSq_zero`)
with `0 ≤ K ≤ Λ`, `Λ` a bound of `|sec|` on the compact ball `closedBall x (L + 2)`; the scalar
comparison `DifferentialGeometry.Analysis.scalarJacobi_mem_Icc` gives `G ≤ 1` for `Λ ρ² ≤ 1`, uniformly
in the geodesic and the normal; a curve of speed `≤ 1` is `1`-Lipschitz.

Deviation from the frozen interface (a strengthening): the hypotheses on `ξ` are only required on
`Ioo (-1) (L + 1)` (`dist_transverse_shift_le_dim_two_of_Ioo`); the frozen name carries the verbatim
`∀ t` form; the hypothesis `0 < L` is not needed (dropped, `L` explicit); the unused instance arguments `[NeZero (finrank ℝ E)]`, `[SigmaCompactSpace M]` of the
interface block are dropped (the verbatim statement is an `example` in the consumer file).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- **The transverse speed is at most one** on `[0, ρ)` when `Λ ρ² ≤ 1` and `0 ≤ K ≤ Λ` along the
`h`-line. -/
theorem transverseSpeedSq_le_one (hr : 3 ≤ r) (hdim : Module.finrank ℝ E = 2)
    (hdom : g.geodesicFlowDomain = univ) (p : TangentBundle I M)
    (hp : g.inner p.proj p.snd p.snd = 1) {ξ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J)
    (hcont : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) J)
    (hunit : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1)
    (hperp : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0)
    {t : ℝ} (ht : t ∈ J) {ρ Λ : ℝ} (hΛ : 0 ≤ Λ) (hρΛ : Λ * ρ ^ 2 ≤ 1)
    (hK : ∀ h ∈ Ico 0 ρ, 0 ≤ g.sectionalCurvature (transverseShift g p ξ (t, h))
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, h)) t 1)
        (g.geodesicFlow (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M) h).snd ∧
      g.sectionalCurvature (transverseShift g p ξ (t, h))
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, h)) t 1)
        (g.geodesicFlow (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M) h).snd ≤ Λ) :
    ∀ h ∈ Ico 0 ρ, transverseSpeedSq g p ξ (t, h) ≤ 1 := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t := fun t ht =>
    contMDiffAt_unitNormal_dim_two g hr1 hdim p (fun t => by rw [hdom]; exact mem_univ _) hp hJ
      hcont hunit hperp ht
  obtain ⟨hGc, hode⟩ := transverseShift_jacobi g hr hdim hdom p hp hJ hcont hunit hperp ht
  obtain ⟨hj0, hj0'⟩ := deriv_sqrt_transverseSpeedSq_zero g hr2 hdom p hp hJ hV hperp ht
  have hb := DifferentialGeometry.Analysis.scalarJacobi_mem_Icc
    (j := fun h => Real.sqrt (transverseSpeedSq g p ξ (t, h))) hΛ hρΛ
    (Real.continuous_sqrt.comp hGc).continuousOn hj0 hj0'
    (fun h _ hpos => hode h (Real.sqrt_pos.mp hpos)) hK
  intro h hh
  obtain ⟨hlow, hup⟩ := hb h hh
  have hpos : 0 < transverseSpeedSq g p ξ (t, h) :=
    Real.sqrt_pos.mp (lt_of_lt_of_le (by norm_num) hlow)
  have hsq := Real.sq_sqrt hpos.le
  nlinarith [Real.sqrt_nonneg (transverseSpeedSq g p ξ (t, h))]

end General

section Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

omit [CompleteSpace M] in
/-- A shifted curve whose transverse speed is at most one is `1`-Lipschitz. -/
theorem dist_transverseShift_le (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdom : g.geodesicFlowDomain = univ) (p : TangentBundle I M) {ξ : ℝ → E} {J : Set ℝ}
    (hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    {L h : ℝ} (hLJ : Icc 0 L ⊆ J) (hG : ∀ t ∈ Icc 0 L, transverseSpeedSq g p ξ (t, h) ≤ 1) :
    ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
      dist (transverseShift g p ξ (t₁, h)) (transverseShift g p ξ (t₂, h)) ≤ |t₁ - t₂| := by
  have key : ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L, t₁ ≤ t₂ →
      dist (transverseShift g p ξ (t₁, h)) (transverseShift g p ξ (t₂, h)) ≤ t₂ - t₁ := by
    intro t₁ ht₁ t₂ ht₂ hle
    have hsub : Icc t₁ t₂ ⊆ Icc 0 L := fun t ht => ⟨le_trans ht₁.1 ht.1, le_trans ht.2 ht₂.2⟩
    have hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t => transverseShift g p ξ (t, h)) (Icc t₁ t₂) := by
      intro t ht
      have h1 := (contMDiffAt_transverseShift g hr hdom p (z := (t, h))
        (hV t (hLJ (hsub ht)))).comp t
          ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt (x := t))
      exact (h1.of_le (by exact_mod_cast hr)).contMDiffWithinAt
    have hspeed : ∀ t ∈ Ioo t₁ t₂,
        ‖mfderiv 𝓘(ℝ, ℝ) I (fun t => transverseShift g p ξ (t, h)) t 1‖ₑ ≤ 1 := by
      intro t ht
      rw [hnorm]
      have h1 := hG t (hsub (Ioo_subset_Icc_self ht))
      have h2 : Real.sqrt (transverseSpeedSq g p ξ (t, h)) ≤ 1 := by
        rw [Real.sqrt_le_one]; exact h1
      calc ENNReal.ofReal (Real.sqrt (g.inner _
            (mfderiv 𝓘(ℝ, ℝ) I (fun t => transverseShift g p ξ (t, h)) t 1)
            (mfderiv 𝓘(ℝ, ℝ) I (fun t => transverseShift g p ξ (t, h)) t 1)))
          = ENNReal.ofReal (Real.sqrt (transverseSpeedSq g p ξ (t, h))) := rfl
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h2
        _ = 1 := ENNReal.ofReal_one
    have hle' := Manifold.riemannianEDist_le_of_curve_speed_bound hle hc hspeed
    rw [← IsRiemannianManifold.out (I := I), edist_dist, one_mul] at hle'
    exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hle)).mp hle'
  intro t₁ ht₁ t₂ ht₂
  rcases le_total t₁ t₂ with hle | hle
  · rw [abs_of_nonpos (by linarith), neg_sub]
    exact key t₁ ht₁ t₂ ht₂ hle
  · rw [abs_of_nonneg (by linarith), dist_comm]
    exact key t₂ ht₂ t₁ ht₁ hle

omit [CompleteSpace M] in
/-- The shifted points stay in a fixed ball: `d(x, α(t, h)) ≤ d(x, γ 0) + t + h`. -/
theorem dist_transverseShift_le_add (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdom : g.geodesicFlowDomain = univ) (x : M) (p : TangentBundle I M)
    (hp : g.inner p.proj p.snd p.snd = 1) {ξ : ℝ → E} {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h)
    (hunit : g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1) :
    dist x (transverseShift g p ξ (t, h)) ≤ dist x p.proj + t + h := by
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  have h1 := g.dist_proj_geodesicFlow_le hr hnorm (p := p) (s := 0) (t := t)
    (fun τ _ => hmem _)
  rw [g.geodesicFlow_zero hr, hp, Real.sqrt_one, one_mul, sub_zero, abs_of_nonneg ht] at h1
  have h2 := g.dist_proj_geodesicFlow_le hr hnorm
    (p := (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) (s := 0) (t := h)
    (fun τ _ => hmem _)
  rw [g.geodesicFlow_zero hr] at h2
  change dist (g.geodesicFlow p t).proj (transverseShift g p ξ (t, h)) ≤
    Real.sqrt (g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t)) * |h - 0| at h2
  rw [hunit, Real.sqrt_one, one_mul, sub_zero, abs_of_nonneg hh] at h2
  calc dist x (transverseShift g p ξ (t, h))
      ≤ dist x p.proj + dist p.proj (g.geodesicFlow p t).proj +
          dist (g.geodesicFlow p t).proj (transverseShift g p ξ (t, h)) :=
        dist_triangle4 _ _ _ _
    _ ≤ dist x p.proj + t + h := by linarith

/-- **S-SHIFT2, strengthened form** (hypotheses on `ξ` only on `Ioo (-1) (L + 1)`). -/
theorem dist_transverse_shift_le_dim_two_of_Ioo (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (x : M) (L : ℝ) :
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ ξ : ℝ → E,
        ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M))
          (Ioo (-1) (L + 1)) →
        (∀ t ∈ Ioo (-1) (L + 1), g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1) →
        (∀ t ∈ Ioo (-1) (L + 1),
          g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) →
        ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
          dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
            (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤
              |t₁ - t₂| := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hdom := g.geodesicFlowDomain_eq_univ hr2 hnorm
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨Λ, hΛ0, hΛ⟩ := g.exists_abs_sectionalCurvature_le_of_isCompact hr2
    (isCompact_closedBall x (L + 2))
  have hΛ' : (1 : ℝ) ≤ max Λ 1 := le_max_right _ _
  have hΛ'0 : 0 < max Λ 1 := lt_of_lt_of_le one_pos hΛ'
  refine ⟨1 / max Λ 1, by positivity, ?_⟩
  intro p hxp hp ξ hcont hunit hperp h hh t₁ ht₁ t₂ ht₂
  have hρ1 : 1 / max Λ 1 ≤ 1 := by rw [div_le_one hΛ'0]; exact hΛ'
  have hρΛ : max Λ 1 * (1 / max Λ 1) ^ 2 ≤ 1 := by
    rw [show max Λ 1 * (1 / max Λ 1) ^ 2 = 1 / max Λ 1 by field_simp]
    exact hρ1
  have hJ : IsOpen (Ioo (-1 : ℝ) (L + 1)) := isOpen_Ioo
  have hLJ : Icc 0 L ⊆ Ioo (-1 : ℝ) (L + 1) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hV : ∀ t ∈ Ioo (-1 : ℝ) (L + 1), ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t := fun t ht =>
    contMDiffAt_unitNormal_dim_two g hr1 hdim p (fun t => hmem _) hp hJ hcont hunit hperp ht
  have hG : ∀ t ∈ Icc 0 L, transverseSpeedSq g p ξ (t, h) ≤ 1 := by
    intro t ht
    refine transverseSpeedSq_le_one g hr hdim hdom p hp hJ hcont hunit hperp (hLJ ht)
      (le_of_lt hΛ'0) hρΛ ?_ h hh
    intro h' hh'
    refine ⟨hsec _ _ _, ?_⟩
    have hball : transverseShift g p ξ (t, h') ∈ closedBall x (L + 2) := by
      rw [mem_closedBall, dist_comm]
      have hd := dist_transverseShift_le_add g hr1 hnorm hdom x p hp ht.1 hh'.1
        (hunit t (hLJ ht))
      have : h' < 1 := lt_of_lt_of_le hh'.2 hρ1
      linarith [ht.2, lt_of_lt_of_le hxp hρ1]
    exact (le_abs_self _).trans ((hΛ _ hball _ _).trans (le_max_left _ _))
  have hdist := dist_transverseShift_le g hr1 hnorm hdom p hV hLJ hG t₁ ht₁ t₂ ht₂
  have e1 : g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M) =
      transverseShift g p ξ (t₁, h) :=
    g.expMap_smul_eq_proj_geodesicFlow hr1 _ (ξ t₁) h (hmem _)
  have e2 : g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M) =
      transverseShift g p ξ (t₂, h) :=
    g.expMap_smul_eq_proj_geodesicFlow hr1 _ (ξ t₂) h (hmem _)
  rw [e1, e2]
  exact hdist

/-- **S-SHIFT2** (frozen interface `dist_transverse_shift_le_dim_two`, design §4.2): in dimension
two, for a complete `C^(r+1)` metric with `sec ≥ 0`, `r ≥ 3`, the curves `t ↦ exp_{γ t}(h ξ t)` are
`1`-Lipschitz on `[0, L]` for `0 ≤ h < ρ`, uniformly for unit geodesics starting near `x` and continuous
unit normals `ξ`. -/
theorem dist_transverse_shift_le_dim_two (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (x : M) (L : ℝ) :
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ ξ : ℝ → E,
        Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) →
        (∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1) →
        (∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) →
        ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
          dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
            (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤
              |t₁ - t₂| := by
  obtain ⟨ρ, hρ, hbound⟩ := dist_transverse_shift_le_dim_two_of_Ioo g hr hnorm hsec hdim x L
  exact ⟨ρ, hρ, fun p hxp hp ξ hcont hunit hperp => hbound p hxp hp ξ hcont.continuousOn
    (fun t _ => hunit t) (fun t _ => hperp t)⟩

end Metric

end DifferentialGeometry.Geometry.FiniteSoul
