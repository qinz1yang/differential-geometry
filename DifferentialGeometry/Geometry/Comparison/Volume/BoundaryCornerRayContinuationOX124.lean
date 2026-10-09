import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCornerRayFrameOX124
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Continuation of a parallel normal frame along a geodesic flow curve (O-X124 G2)

On a boundaryless manifold `N` modelled on `E` (in BSA02: the true interior `U` with the original
metric `k`), the projection `Γ r = (g.geodesicFlow w r).proj` of a geodesic flow line is smooth
and geodesic on its open flow interval. A parallel orthonormal normal frame given on an open time
interval `(lo, r₁)` around `0` continues, by parallel transport along `Γ`, to any `(lo, T)` with
`[0, T]` inside the flow interval, agreeing with the given frame on `(lo, min r₁ T)`.

* `exists_smooth_clamp_OX124`: a smooth map `ℝ → ℝ` equal to the identity near `[c, d]` with
  values in `[c - 2ε, d + 2ε]` (built from a smooth bump function).
* `flowCurve_contMDiffAt_OX124`, `flowCurve_geodesic_OX124`: smoothness and the geodesic equation
  of the flow curve on its flow interval.
* `exists_flowCurve_clamp_OX124`: a globally smooth curve agreeing with the flow curve near
  `[0, T]` and geodesic on `[0, T]`.
* `flowCurve_frame_continuation_OX124`: the continuation of the frame.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

/-- A smooth map of the line that is the identity on a neighbourhood of `[c, d]` and takes values
in `[c - 2ε, d + 2ε]`. -/
theorem exists_smooth_clamp_OX124 {c d ε : ℝ} (hcd : c ≤ d) (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ t ∈ Ioo (c - ε) (d + ε), φ t = t) ∧
      ∀ t, φ t ∈ Icc (c - 2 * ε) (d + 2 * ε) := by
  let m : ℝ := (c + d) / 2
  let h : ℝ := (d - c) / 2
  have hh : 0 ≤ h := by dsimp [h]; linarith
  let f : ContDiffBump m := ⟨h + ε, h + 2 * ε, by linarith, by linarith⟩
  refine ⟨fun t => m + f t * (t - m), ?_, ?_, ?_⟩
  · exact contDiff_const.add (f.contDiff.mul (contDiff_id.sub contDiff_const))
  · intro t ht
    have hball : t ∈ Metric.closedBall m f.rIn := by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      change -(h + ε) ≤ t - m ∧ t - m ≤ h + ε
      dsimp [m, h]
      constructor <;> linarith [ht.1, ht.2]
    change m + f t * (t - m) = t
    rw [f.one_of_mem_closedBall hball]
    ring
  · intro t
    have hbound : |f t * (t - m)| ≤ h + 2 * ε := by
      by_cases hsupp : t ∈ Metric.ball m f.rOut
      · rw [Metric.mem_ball, Real.dist_eq] at hsupp
        rw [abs_mul, abs_of_nonneg f.nonneg]
        calc
          f t * |t - m| ≤ 1 * |t - m| :=
            mul_le_mul_of_nonneg_right f.le_one (abs_nonneg _)
          _ ≤ h + 2 * ε := by
            rw [one_mul]
            exact hsupp.le
      · have hzero : f t = 0 := by
          have hnot : t ∉ Function.support f := by
            rw [f.support_eq]
            exact hsupp
          simpa [Function.mem_support] using hnot
        rw [hzero, zero_mul, abs_zero]
        linarith
    rw [abs_le] at hbound
    change c - 2 * ε ≤ m + f t * (t - m) ∧ m + f t * (t - m) ≤ d + 2 * ε
    dsimp [m, h] at hbound ⊢
    constructor <;> linarith [hbound.1, hbound.2]

section FlowCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

/-- The projected geodesic flow line is smooth on its flow interval. -/
theorem flowCurve_contMDiffAt_OX124 (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (w : TangentBundle 𝓘(ℝ, E) N) {r : ℝ} (hr : (w, r) ∈ g.geodesicFlowDomain) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s => (g.geodesicFlow w s).proj) r := by
  have hphase : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, E)).tangent.prod 𝓘(ℝ, ℝ)) ∞
      (fun s : ℝ => (w, s)) := contMDiff_const.prodMk contMDiff_id
  have hflow := (g.contMDiffOn_geodesicFlow (r := ⊤) le_top).contMDiffAt
    ((g.isOpen_geodesicFlowDomain (r := ⊤) le_top).mem_nhds hr)
  have hproj : ContMDiff (𝓘(ℝ, E)).tangent 𝓘(ℝ, E) ∞
      (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) N → N) :=
    contMDiff_proj (TangentSpace 𝓘(ℝ, E) : N → Type _)
  exact hproj.contMDiffAt.comp r (hflow.comp r hphase.contMDiffAt)

/-- The projected geodesic flow line satisfies the geodesic equation on its flow interval. -/
theorem flowCurve_geodesic_OX124 (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (w : TangentBundle 𝓘(ℝ, E) N) {r : ℝ} (hr : (w, r) ∈ g.geodesicFlowDomain) :
    HasGeodesicEquationAt g (fun s => (g.geodesicFlow w s).proj) r := by
  obtain ⟨x, u⟩ := w
  exact ((g.isGeodesicOnWithInitial_geodesicFlow x u).isGeodesicAt
    (isOpen_maximalIntegralCurveInterval.mem_nhds hr)).hasGeodesicEquationAt

/-- A globally smooth curve agreeing with the flow curve near `[0, T]`, geodesic on `[0, T]`. -/
theorem exists_flowCurve_clamp_OX124 (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (w : TangentBundle 𝓘(ℝ, E) N) {T : ℝ} (hT : 0 ≤ T)
    (hdom : ∀ r ∈ Icc (0 : ℝ) T, (w, r) ∈ g.geodesicFlowDomain) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Γ : ℝ → N, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ Γ ∧
      (∀ r ∈ Ioo (-ε) (T + ε), Γ r = (g.geodesicFlow w r).proj) ∧
      IsGeodesicOn (I := 𝓘(ℝ, E)) g Γ (Icc 0 T) := by
  let S : Set ℝ := {r | (w, r) ∈ g.geodesicFlowDomain}
  have hSopen : IsOpen S := (g.isOpen_geodesicFlowDomain (r := ⊤) le_top).preimage
    (continuous_const.prodMk continuous_id)
  have hSconn : S.OrdConnected := by
    have hpre : IsPreconnected S := by
      obtain ⟨x, u⟩ := w
      exact isPreconnected_maximalIntegralCurveInterval
    exact hpre.ordConnected
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.mp hSopen 0 (hdom 0 ⟨le_rfl, hT⟩)
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp hSopen T (hdom T ⟨hT, le_rfl⟩)
  let ε : ℝ := min ε₀ ε₁ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεle₀ : 2 * ε < ε₀ := by
    dsimp [ε]; linarith [min_le_left ε₀ ε₁, lt_min hε₀ hε₁]
  have hεle₁ : 2 * ε < ε₁ := by
    dsimp [ε]; linarith [min_le_right ε₀ ε₁, lt_min hε₀ hε₁]
  have hleft : -(2 * ε) ∈ S := hball₀ (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]
    exact hεle₀)
  have hright : T + 2 * ε ∈ S := hball₁ (by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    exact hεle₁)
  have hIcc : Icc (0 - 2 * ε) (T + 2 * ε) ⊆ S := by
    rw [zero_sub]
    exact hSconn.out hleft hright
  obtain ⟨φ, hφ, hφid, hφrange⟩ := exists_smooth_clamp_OX124 hT hε
  let Γ₀ : ℝ → N := fun s => (g.geodesicFlow w s).proj
  refine ⟨ε, hε, fun s => Γ₀ (φ s), ?_, ?_, ?_⟩
  · intro s
    have hmem : φ s ∈ S := hIcc (hφrange s)
    exact (flowCurve_contMDiffAt_OX124 g w hmem).comp s
      (hφ.contMDiff.contMDiffAt (x := s))
  · intro s hs
    change Γ₀ (φ s) = Γ₀ s
    rw [hφid s (by simpa only [zero_sub] using hs)]
  · intro s hs
    have hsmem : s ∈ Ioo (0 - ε) (T + ε) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have heq : (fun q => Γ₀ (φ q)) =ᶠ[𝓝 s] Γ₀ := by
      filter_upwards [isOpen_Ioo.mem_nhds hsmem] with q hq
      rw [hφid q hq]
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at heq.eq_of_nhds heq
      (flowCurve_geodesic_OX124 g w (hdom s hs))

/-- A parallel orthonormal normal frame along the flow curve on `(lo, r₁) ∋ 0` continues to
`(lo, T)` whenever `[0, T]` lies in the flow interval; it is unchanged on `(lo, min r₁ T)`. -/
theorem flowCurve_frame_continuation_OX124 (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (w : TangentBundle 𝓘(ℝ, E) N) {ι : Type*} [DecidableEq ι] {lo r₁ T : ℝ}
    (hlo : lo < 0) (hr₁ : 0 < r₁) (hT : 0 < T)
    (hdom : ∀ r ∈ Icc (0 : ℝ) T, (w, r) ∈ g.geodesicFlowDomain)
    (F₀ : ι → ∀ r : ℝ, TangentSpace 𝓘(ℝ, E) ((g.geodesicFlow w r).proj))
    (hF₀sm : ∀ i r, r ∈ Ioo lo r₁ →
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
        (fun q => (⟨(g.geodesicFlow w q).proj, F₀ i q⟩ : TangentBundle 𝓘(ℝ, E) N)) r)
    (hF₀par : ∀ i r, r ∈ Ioo lo r₁ →
      covDerivAlong g (fun q => (g.geodesicFlow w q).proj) (F₀ i) r = 0)
    (hF₀ON : ∀ r, r ∈ Ioo lo r₁ → ∀ i j,
      g.inner ((g.geodesicFlow w r).proj) (F₀ i r) (F₀ j r) = if i = j then 1 else 0)
    (hF₀perp : ∀ r, r ∈ Ioo lo r₁ → ∀ i,
      g.inner ((g.geodesicFlow w r).proj) (F₀ i r)
        (curveVelocity (I := 𝓘(ℝ, E)) (fun q => (g.geodesicFlow w q).proj) r) = 0) :
    ∃ F : ι → ∀ r : ℝ, TangentSpace 𝓘(ℝ, E) ((g.geodesicFlow w r).proj),
      (∀ i r, r ∈ Ioo lo (min r₁ T) → F i r = F₀ i r) ∧
      (∀ i r, r ∈ Ioo lo T →
        ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun q => (⟨(g.geodesicFlow w q).proj, F i q⟩ : TangentBundle 𝓘(ℝ, E) N)) r) ∧
      (∀ i r, r ∈ Ioo lo T →
        covDerivAlong g (fun q => (g.geodesicFlow w q).proj) (F i) r = 0) ∧
      (∀ r, r ∈ Ioo lo T → ∀ i j,
        g.inner ((g.geodesicFlow w r).proj) (F i r) (F j r) = if i = j then 1 else 0) ∧
      (∀ r, r ∈ Ioo lo T → ∀ i,
        g.inner ((g.geodesicFlow w r).proj) (F i r)
          (curveVelocity (I := 𝓘(ℝ, E)) (fun q => (g.geodesicFlow w q).proj) r) = 0) := by
  classical
  obtain ⟨ε, hε, Γ, hΓ, hΓeq, hΓgeo⟩ := exists_flowCurve_clamp_OX124 g w hT.le hdom
  set Γ₀ : ℝ → N := fun q => (g.geodesicFlow w q).proj with hΓ₀
  have hbase : ∀ {x x' : N}, x = x' → ∀ u u' : E, g.inner x u u' = g.inner x' u u' := by
    intro x x' h u u'
    subst h
    rfl
  have hev (r : ℝ) (hr : r ∈ Ioo (-ε) (T + ε)) : Γ =ᶠ[𝓝 r] Γ₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with q hq
    exact hΓeq q hq
  have hvel (r : ℝ) (hr : r ∈ Ioo (-ε) (T + ε)) :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) Γ r 1 : E) =
        (curveVelocity (I := 𝓘(ℝ, E)) Γ₀ r : E) := by
    unfold curveVelocity
    rw [(hev r hr).mfderiv_eq]
    rfl
  have h0ε : (0 : ℝ) ∈ Ioo (-ε) (T + ε) := ⟨by linarith, by linarith⟩
  have h0r : (0 : ℝ) ∈ Ioo lo r₁ := ⟨hlo, hr₁⟩
  have hfields : ∀ i : ι, ∃ d : ℝ, ∃ V : ∀ t, TangentSpace 𝓘(ℝ, E) (Γ t),
      0 < d ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
        (fun t => (⟨Γ t, V t⟩ : TangentBundle 𝓘(ℝ, E) N)) (Ioo (-d) (T + d)) ∧
      V 0 = F₀ i 0 ∧
      (∀ t, t ∈ Icc (0 : ℝ) T → covDerivAlong g Γ V t = 0) ∧
      (∀ t, t ∈ Icc (0 : ℝ) T → g.inner (Γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) Γ t 1) (V t) = 0) := by
    intro i
    have hunit : g.inner (Γ 0) (F₀ i 0) (F₀ i 0) = 1 := by
      have h := hF₀ON 0 h0r i i
      simp only [↓reduceIte] at h
      exact (hbase (hΓeq 0 h0ε) _ _).trans h
    have hnormal : g.inner (Γ 0) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) Γ 0 1) (F₀ i 0) = 0 := by
      have h := hF₀perp 0 h0r i
      rw [← hvel 0 h0ε] at h
      exact (hbase (hΓeq 0 h0ε) _ _).trans ((g.symm _ _ _).trans h)
    obtain ⟨d, V, hd, hVsm, hV0, hVpar, _hVunit, hVperp, _hVpt⟩ :=
      exists_smooth_parallel_unit_normal_field g Γ hΓ hT hΓgeo (F₀ i 0) hunit hnormal
    exact ⟨d, V, hd, hVsm, hV0, hVpar, hVperp⟩
  choose d V hd hVsm hV0 hVpar hVperp using hfields
  have hIcc (i : ι) : Icc (0 : ℝ) T ⊆ Ioo (-d i) (T + d i) := by
    intro t ht
    exact ⟨by linarith [hd i, ht.1], by linarith [hd i, ht.2]⟩
  have hVdiff (i : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      DifferentiableAt ℝ (chartRepAt (I := 𝓘(ℝ, E)) Γ (V i) t) t :=
    chartRepAt_differentiableAt_of_total_contMDiffAt
      (((hVsm i).contMDiffAt (isOpen_Ioo.mem_nhds (hIcc i ht))).of_le (by norm_num))
  let s₁ : ℝ := min r₁ T
  have hs₁ : 0 < s₁ := lt_min hr₁ hT
  have hs₁r : s₁ ≤ r₁ := min_le_left _ _
  have hs₁T : s₁ ≤ T := min_le_right _ _
  -- the given frame along the clamped curve on `[0, s₁)`
  have hF₀bundleΓ (i : ι) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) s₁) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
        (fun q => (⟨Γ q, F₀ i q⟩ : TangentBundle 𝓘(ℝ, E) N)) t := by
    have htε : t ∈ Ioo (-ε) (T + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine (hF₀sm i t ⟨by linarith [ht.1], by linarith [ht.2]⟩).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds htε] with q hq
    exact congrArg (fun x : N => (⟨x, (F₀ i q : E)⟩ : TangentBundle 𝓘(ℝ, E) N)) (hΓeq q hq)
  have hagree (i : ι) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) s₁) : V i t = F₀ i t := by
    have hsub : ∀ q ∈ Icc (0 : ℝ) t, q ∈ Ico (0 : ℝ) s₁ :=
      fun q hq => ⟨hq.1, lt_of_le_of_lt hq.2 ht.2⟩
    have hsubT : ∀ q ∈ Icc (0 : ℝ) t, q ∈ Icc (0 : ℝ) T :=
      fun q hq => ⟨hq.1, by linarith [hq.2, ht.2]⟩
    have hF₀diff : ∀ q ∈ Icc (0 : ℝ) t,
        DifferentiableAt ℝ (chartRepAt (I := 𝓘(ℝ, E)) Γ (F₀ i) q) q := fun q hq =>
      chartRepAt_differentiableAt_of_total_contMDiffAt
        ((hF₀bundleΓ i q (hsub q hq)).of_le (by norm_num))
    have hF₀parΓ : ∀ q ∈ Icc (0 : ℝ) t, covDerivAlong g Γ (F₀ i) q = 0 := by
      intro q hq
      have hqε : q ∈ Ioo (-ε) (T + ε) :=
        ⟨by linarith [hq.1], by linarith [hq.2, ht.2]⟩
      have h := covDerivAlong_congr_curve g (γ := Γ) (γ' := Γ₀) (F₀ i) (F₀ i) (hev q hqε)
        (Eventually.of_forall fun _ => rfl)
      rw [hF₀par i q ⟨by linarith [hq.1], by linarith [hq.2, ht.2]⟩] at h
      exact h
    exact parallel_transport_unique_of_eq_at_point g Γ (N := 2) le_rfl
      (hΓ.of_le (by norm_num)) (V i) (F₀ i) (fun q hq => hVdiff i q (hsubT q hq)) hF₀diff
      (fun q hq => hVpar i q (hsubT q hq)) hF₀parΓ ⟨le_rfl, ht.1⟩ (hV0 i) t ⟨ht.1, le_rfl⟩
  let F : ι → ∀ r : ℝ, TangentSpace 𝓘(ℝ, E) (Γ₀ r) := fun i r =>
    if r < s₁ / 2 then (F₀ i r : E) else (V i r : E)
  have hFA (i : ι) (r : ℝ) (hr : r ∈ Ioo lo s₁) : F i r = F₀ i r := by
    change (if r < s₁ / 2 then (F₀ i r : E) else (V i r : E)) = F₀ i r
    by_cases hrs : r < s₁ / 2
    · simp only [hrs, ↓reduceIte]
    · simp only [hrs, ↓reduceIte]
      exact hagree i r ⟨by linarith [not_lt.mp hrs], hr.2⟩
  have hFB (i : ι) (r : ℝ) (hr : r ∈ Ioo (s₁ / 2) T) : F i r = V i r := by
    change (if r < s₁ / 2 then (F₀ i r : E) else (V i r : E)) = V i r
    simp only [not_lt.mpr hr.1.le, ↓reduceIte]
    rfl
  have hcases (r : ℝ) (hr : r ∈ Ioo lo T) : r ∈ Ioo lo s₁ ∨ r ∈ Ioo (s₁ / 2) T := by
    by_cases hrs : r < s₁
    · exact Or.inl ⟨hr.1, hrs⟩
    · exact Or.inr ⟨by linarith [not_lt.mp hrs], hr.2⟩
  have hBε (r : ℝ) (hr : r ∈ Ioo (s₁ / 2) T) : r ∈ Ioo (-ε) (T + ε) :=
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hBT (r : ℝ) (hr : r ∈ Ioo (s₁ / 2) T) : r ∈ Icc (0 : ℝ) T :=
    ⟨by linarith [hr.1], hr.2.le⟩
  have hVON (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) (i j : ι) :
      g.inner (Γ r) (V i r) (V j r) = if i = j then 1 else 0 := by
    have hconst := parallel_transport_preserves_inner_product g Γ (N := 2) le_rfl
      (hΓ.of_le (by norm_num)) (V i) (V j) (fun q hq => hVdiff i q hq)
      (fun q hq => hVdiff j q hq) (fun q hq => hVpar i q hq) (fun q hq => hVpar j q hq)
    rw [hconst r hr, hV0 i, hV0 j]
    exact (hbase (hΓeq 0 h0ε) _ _).trans (hF₀ON 0 h0r i j)
  refine ⟨F, fun i r hr => hFA i r hr, ?_, ?_, ?_, ?_⟩
  · intro i r hr
    rcases hcases r hr with hA | hB
    · refine (hF₀sm i r ⟨hA.1, lt_of_lt_of_le hA.2 hs₁r⟩).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hA] with q hq
      rw [hFA i q hq]
    · have hVat : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun q => (⟨Γ q, V i q⟩ : TangentBundle 𝓘(ℝ, E) N)) r :=
        (hVsm i).contMDiffAt (isOpen_Ioo.mem_nhds (hIcc i (hBT r hB)))
      refine hVat.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hB, isOpen_Ioo.mem_nhds (hBε r hB)] with q hq hqε
      rw [hFB i q hq]
      exact congrArg (fun x : N => (⟨x, (V i q : E)⟩ : TangentBundle 𝓘(ℝ, E) N))
        (hΓeq q hqε).symm
  · intro i r hr
    rcases hcases r hr with hA | hB
    · rw [covDerivAlong_congr_of_eventuallyEq g Γ₀ (W := F₀ i) (by
        filter_upwards [isOpen_Ioo.mem_nhds hA] with q hq
        exact hFA i q hq)]
      exact hF₀par i r ⟨hA.1, lt_of_lt_of_le hA.2 hs₁r⟩
    · have h := covDerivAlong_congr_curve g (γ := Γ₀) (γ' := Γ) (F i) (V i)
        (hev r (hBε r hB)).symm (by
          filter_upwards [isOpen_Ioo.mem_nhds hB] with q hq
          rw [hFB i q hq])
      rw [hVpar i r (hBT r hB)] at h
      exact h
  · intro r hr i j
    rcases hcases r hr with hA | hB
    · rw [hFA i r hA, hFA j r hA]
      exact hF₀ON r ⟨hA.1, lt_of_lt_of_le hA.2 hs₁r⟩ i j
    · rw [hFB i r hB, hFB j r hB]
      exact (hbase (hΓeq r (hBε r hB)) _ _).symm.trans (hVON r (hBT r hB) i j)
  · intro r hr i
    rcases hcases r hr with hA | hB
    · rw [hFA i r hA]
      exact hF₀perp r ⟨hA.1, lt_of_lt_of_le hA.2 hs₁r⟩ i
    · rw [hFB i r hB]
      have h := hVperp i r (hBT r hB)
      rw [hvel r (hBε r hB)] at h
      exact (hbase (hΓeq r (hBε r hB)) _ _).symm.trans ((g.symm _ _ _).trans h)

end FlowCurve

section Binding

open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  [ambientDimension : NeZero (Module.finrank ℝ E)]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem cornerRayCont_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

/-- `exists_boundary_corner_ray_pole_frame_OX124` with, in addition, the continuation of the pole
frame along the actual phase curve to every `(-a, T)` with `[0, T]` in the original interior
flow interval of `σ v`; the continued frame is the pole frame on `(-a, min (L - a) T)`. -/
theorem exists_boundary_corner_ray_frame_OX124 (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      cornerRayCont_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E, RiemannianMetricComplete G ∧
      ∃ O : Opens E, extChartAt I p p ∈ O ∧
        (∀ y ∈ (O : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
            g p y z w) ∧
        ∃ V : Opens (E × ℝ), ∃ ρ : E × ℝ → U,
          ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V ∧
          (∀ q ∈ V,
            ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
              G.geodesicFlowDomain ∧
            boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
              (O : Set E) ∩ interior (extChartAt I p).target ∧
            (ρ q : M) = (extChartAt I p).symm
              (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2) ∧
            HasGeodesicEquationAt k (fun t => ρ (q.1, t)) q.2) ∧
          ∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            ∃ δ : ℝ, 0 < δ ∧ ∃ a ∈ Ioo 0 δ,
              ∃ σ : E → TangentBundle 𝓘(ℝ, E) U,
              ∃ W : Opens E, ∃ ε : ℝ, v ∈ W ∧ 0 < ε ∧
                ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
                (∀ u ∈ W, (u, a) ∈ V ∧ (σ u).proj = ρ (u, a)) ∧
                (∀ u ∈ W, ∀ r ∈ Metric.ball (0 : ℝ) ε,
                  (σ u, r) ∈ k.geodesicFlowDomain ∧
                  boundaryPhasePoint k σ u r = ρ (u, r + a) ∧
                  ∀ w : E, (boundaryPhaseJacobiLinear k σ u r w : E) =
                    boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) w) ∧
                (∀ t ∈ Ioo 0 δ, (v, t) ∈ V) ∧
                Tendsto (fun t : ℝ => ((boundaryPhasePoint k σ v (t - a) : U) : M))
                  (𝓝[>] (0 : ℝ)) (𝓝 p) ∧
                (∀ u ∈ W, σ u = DifferentialGeometry.velocityLift
                  (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) a) ∧
                (∀ t ∈ Ioo 0 δ, (σ v, t - a) ∈ k.geodesicFlowDomain ∧
                  boundaryPhasePoint k σ v (t - a) = ρ (v, t) ∧
                  ∀ w : E, (boundaryPhaseJacobiLinear k σ v (t - a) w : E) =
                    boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v t w) ∧
                (∀ e : Fin 2 → E,
                  (∀ i j, G.inner (extChartAt I p p) (e i) (e j) = if i = j then 1 else 0) →
                  Tendsto (fun t : ℝ => curveDensity k
                    (fun r => boundaryPhasePoint k σ v (r - a))
                    (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t / t ^ 2)
                    (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))) ∧
                (∀ u ∈ W, ∀ t : ℝ, (σ u, t) ∈ k.geodesicFlowDomain →
                  k.inner (boundaryPhasePoint k σ u t)
                      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t)
                      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t) =
                    G.inner (extChartAt I p p) u u ∧
                  (∀ w : E, G.inner (extChartAt I p p) w u = 0 →
                    k.inner (boundaryPhasePoint k σ u t) (boundaryPhaseJacobiLinear k σ u t w)
                        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t) = 0 ∧
                      k.inner (boundaryPhasePoint k σ u t)
                        (covDerivAlong k (fun r => boundaryPhasePoint k σ u r)
                          (fun r => boundaryPhaseJacobiLinear k σ u r w) t)
                        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t)
                        = 0) ∧
                  (∀ w z : E, jacobiWronskian k (fun r => boundaryPhasePoint k σ u r)
                    (fun r => boundaryPhaseJacobiLinear k σ u r w)
                    (fun r => boundaryPhaseJacobiLinear k σ u r z) t = 0) ∧
                  ∀ w : E, IsJacobiAt k (fun r => boundaryPhasePoint k σ u r)
                      (fun r => boundaryPhaseJacobiLinear k σ u r w) t ∧
                    ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
                      (fun r => (⟨boundaryPhasePoint k σ u r, boundaryPhaseJacobiLinear k σ u r w⟩ :
                        TangentBundle 𝓘(ℝ, E) U)) t) ∧
                (G.inner (extChartAt I p p) v v = 1 →
                  ∀ e : Fin (Module.finrank ℝ E - 1) → E,
                  (∀ i j, G.inner (extChartAt I p p) (e i) (e j) = if i = j then 1 else 0) →
                  (∀ i, G.inner (extChartAt I p p) v (e i) = 0) →
                  ∃ L : ℝ, a < L ∧ L < δ ∧
                  ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U E ∞,
                  ∃ Z : Fin (Module.finrank ℝ E - 1) → ∀ t : ℝ,
                    TangentSpace 𝓘(ℝ, E) (boundaryPoleFlowFamily G (extChartAt I p p) v t),
                    Φ.source = {z : U | (z : M) ∈
                      (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
                        extChartAt I p (z : M) ∈ O} ∧
                    (∀ z ∈ Φ.source, Φ z = extChartAt I p (z : M)) ∧
                    (∀ z ∈ Φ.source, ∀ x w : TangentSpace 𝓘(ℝ, E) z,
                      k.inner z x w = G.inner (Φ z)
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z x)
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z w)) ∧
                    (∀ i, Z i 0 = e i) ∧
                    (∀ i t, t ∈ Icc (0 : ℝ) L →
                      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
                        (fun s => (⟨boundaryPoleFlowFamily G (extChartAt I p p) v s, Z i s⟩ :
                          TangentBundle 𝓘(ℝ, E) E)) t) ∧
                    (∀ i t, t ∈ Icc (0 : ℝ) L →
                      covDerivAlong G (boundaryPoleFlowFamily G (extChartAt I p p) v)
                        (Z i) t = 0) ∧
                    (∀ t, t ∈ Icc (0 : ℝ) L → ∀ i j,
                      G.inner (boundaryPoleFlowFamily G (extChartAt I p p) v t)
                        (Z i t) (Z j t) = if i = j then 1 else 0) ∧
                    (∀ r ∈ Ioo (-a) (L - a), (σ v, r) ∈ k.geodesicFlowDomain ∧
                      Φ.symm (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a)) =
                        boundaryPhasePoint k σ v r) ∧
                    (∀ i r, r ∈ Ioo (-a) (L - a) →
                      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
                        (fun q => (⟨boundaryPhasePoint k σ v q,
                          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                            (boundaryPoleFlowFamily G (extChartAt I p p) v (q + a))
                            (Z i (q + a))⟩ : TangentBundle 𝓘(ℝ, E) U)) r) ∧
                    (∀ i r, r ∈ Ioo (-a) (L - a) →
                      covDerivAlong k (fun q => boundaryPhasePoint k σ v q)
                        (fun q => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                          (boundaryPoleFlowFamily G (extChartAt I p p) v (q + a))
                          (Z i (q + a))) r = 0) ∧
                    (∀ r, r ∈ Ioo (-a) (L - a) → ∀ i j,
                      k.inner (boundaryPhasePoint k σ v r)
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                          (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a)) (Z i (r + a)))
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                          (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a)) (Z j (r + a))) =
                        if i = j then 1 else 0) ∧
                    (∀ r, r ∈ Ioo (-a) (L - a) → ∀ i,
                      k.inner (boundaryPhasePoint k σ v r)
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                          (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a)) (Z i (r + a)))
                        (curveVelocity (I := 𝓘(ℝ, E)) (fun q => boundaryPhasePoint k σ v q) r) =
                        0) ∧
                    (∀ T : ℝ, 0 < T →
                      (∀ r ∈ Icc (0 : ℝ) T, (σ v, r) ∈ k.geodesicFlowDomain) →
                      ∃ F : Fin (Module.finrank ℝ E - 1) → ∀ r : ℝ,
                        TangentSpace 𝓘(ℝ, E) (boundaryPhasePoint k σ v r),
                        (∀ i r, r ∈ Ioo (-a) (min (L - a) T) →
                          F i r = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                            (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a))
                            (Z i (r + a))) ∧
                        (∀ i r, r ∈ Ioo (-a) T →
                          ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
                            (fun q => (⟨boundaryPhasePoint k σ v q, F i q⟩ :
                              TangentBundle 𝓘(ℝ, E) U)) r) ∧
                        (∀ i r, r ∈ Ioo (-a) T →
                          covDerivAlong k (fun q => boundaryPhasePoint k σ v q) (F i) r = 0) ∧
                        (∀ r, r ∈ Ioo (-a) T → ∀ i j,
                          k.inner (boundaryPhasePoint k σ v r) (F i r) (F j r) =
                            if i = j then 1 else 0) ∧
                        (∀ r, r ∈ Ioo (-a) T → ∀ i,
                          k.inner (boundaryPhasePoint k σ v r) (F i r)
                            (curveVelocity (I := 𝓘(ℝ, E))
                              (fun q => boundaryPhasePoint k σ v q) r) = 0))) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    cornerRayCont_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hbirth⟩ :=
    exists_boundary_corner_ray_pole_frame_OX124 g p b hb
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_⟩
  intro v hv
  obtain ⟨δ, hδ, a, ha, σ, W, ε, hvW, hε, hσ, hWV, hflow, hvV, hpole, hσvel, hphase, hdens,
    hphys, hframe⟩ := hbirth v hv
  refine ⟨δ, hδ, a, ha, σ, W, ε, hvW, hε, hσ, hWV, hflow, hvV, hpole, hσvel, hphase, hdens,
    hphys, ?_⟩
  intro hunit e heON heperp
  obtain ⟨L, haL, hLδ, Φ, Z, hsrc, hmap, hmet, hZ0, hZsm, hZpar, hZON, hdom, hFsm, hFpar,
    hFON, hFperp⟩ := hframe hunit e heON heperp
  refine ⟨L, haL, hLδ, Φ, Z, hsrc, hmap, hmet, hZ0, hZsm, hZpar, hZON, hdom, hFsm, hFpar,
    hFON, hFperp, ?_⟩
  intro T hT hdomT
  exact flowCurve_frame_continuation_OX124 k (σ v) (lo := -a) (r₁ := L - a) (T := T)
    (by linarith [ha.1]) (by linarith) hT hdomT
    (fun i r => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
      (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a)) (Z i (r + a)))
    hFsm hFpar hFON hFperp

end Binding

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
