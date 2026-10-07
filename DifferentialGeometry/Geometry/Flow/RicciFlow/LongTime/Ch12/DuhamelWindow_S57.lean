import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialMetricTimeBounds
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm

set_option autoImplicit false

/-!
# CH12-S57 / G1: Duhamel step of the `hLTF04` window (connection variation integrated over `[t, s]`)

For a Ricci flow `S` on a fixed manifold `M` and a reference metric `h`, the rescaled family
`q s = s⁻¹ • g s` satisfies `∂_s ∇_h^N q_s = -s⁻² ∇_h^N (g_s + 2 s Ric g_s)`
(`defectJet_S57`).  A bound `η r` on the defect jet gives
`|∇_h^N (q s - q t)|_h ≤ (η/t) |s - t|` (`rescaled_metricDerivNorm_duhamel_S57`), hence
`ckErr` at `s` is at most `ckErr` at `t` plus `η` on a window `u ≤ 2 t`.
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- parabolic rescaling `s⁻¹ • g s` of a metric family on `[t, ∞)` (defined for all `s` via `max s t`). -/
def rescaledMetric_S57 (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (ht : 0 < t) (s : ℝ) :
    SmoothRiemannianMetric I M :=
  scaleMetric (max s t)⁻¹ (inv_pos.2 (lt_max_of_lt_right ht)) (g s)

/-- the Ricci-defect jet `∇_h^N (g + 2 r Ric g)` at time `r` (in the reference connection `∇_h`). -/
def defectJet_S57 {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (h : SmoothRiemannianMetric I M) (N : ℕ) (r : ℝ) (x : M) :
    Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (N + 2) x :=
  metricCovDeriv (S.base.metric r) h N x +
    (2 * r) • nablaRicReal (fun _ s => S.base.metric s) h N 0 r x

/-- public copy of the (private) interior evolution of `∇_h^N g_r` along a Ricci flow. -/
theorem metricCovDeriv_hasDerivAt_S57 {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) {s : ℝ} (hs : s ∈ D.regular)
    (x : M) (v : Fin (a + 2) → TangentSpace I x) :
    HasDerivAt (fun r => metricCovDeriv (S.base.metric r) gRef a x v)
      (((-2 : ℝ) • nablaRicReal (fun _ t => S.base.metric t) gRef a 0 s x) v) s := by
  have hwin : ∀ _i : ℕ, Icc s s ⊆ D.regular := by
    intro _ r hr
    have he : r = s := le_antisymm hr.2 hr.1
    exact he ▸ hs
  exact hevComp_of_solutions (I := I) (N := a) (gRef := gRef)
    (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl) hwin
    (fun _ => solutionTowerSwap_regularity gRef S hS a (fun {t} ht => D.regular_isOpen.mem_nhds ht))
    0 x s ⟨le_rfl, le_rfl⟩ v

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] in
/-- joint smoothness of the Gram matrices passes to the rescaled family on `Icc t u`. -/
theorem rescaled_hgram_S57 (g : ℝ → SmoothRiemannianMetric I M) {t u : ℝ} (ht : 0 < t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (g p.1) x₀ p.2 i j)
        (Icc t u ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
        (rescaledMetric_S57 g t ht p.1) x₀ p.2 i j)
      (Icc t u ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hinv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => (p.1)⁻¹)
      (Icc t u ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    have h1 : ContDiffOn ℝ ∞ (fun s : ℝ => s⁻¹) (Ioi 0) :=
      (contDiffOn_inv ℝ).mono (fun s hs => ne_of_gt hs)
    have h2 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s⁻¹) (Ioi 0) :=
      h1.contMDiffOn
    exact h2.comp contMDiff_fst.contMDiffOn
      (fun p hp => lt_of_lt_of_le ht hp.1.1)
  refine (hinv.mul (hgram x₀ i j)).congr ?_
  intro p hp
  have hmax : max p.1 t = p.1 := max_eq_left hp.1.1
  simp only [rescaledMetric_S57, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
    scaleMetric_inner, hmax]
  rfl

/-- W-B1: Duhamel bound for the connection variation of the rescaled flow. -/
theorem rescaled_metricDerivNorm_duhamel_S57 {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (h : SmoothRiemannianMetric I M) {t u : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hreg : Icc t u ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric p.1) x₀ p.2 i j)
        (Icc t u ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (N : ℕ) (K : Set M) {η : ℝ} (hη : 0 ≤ η)
    (hdef : ∀ x ∈ K, ∀ r ∈ Ioo t u,
      Real.sqrt (normSq0S h x (N + 2) (defectJet_S57 S h N r x)) ≤ η * r) :
    ∀ s ∈ Icc t u, ∀ x ∈ K,
      metricDerivNorm N (rescaledMetric_S57 S.base.metric t ht s)
        (rescaledMetric_S57 S.base.metric t ht t) h x ≤ (η / t) * |s - t| := by
  let Ev : ℝ → (x : M) → Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (N + 2) x :=
    fun r x => (-(r⁻¹ ^ 2)) • defectJet_S57 S h N r x
  have hev : ∀ x ∈ K, ∀ s ∈ Ioo t u, ∀ v : Fin (N + 2) → TangentSpace I x,
      HasDerivAt (fun r => metricCovDeriv (rescaledMetric_S57 S.base.metric t ht r) h N x v)
        (Ev s x v) s := by
    intro x _ s hs v
    have hs0 : 0 < s := lt_trans ht hs.1
    have hF := metricCovDeriv_hasDerivAt_S57 S hS h N (hreg (Ioo_subset_Icc_self hs)) x v
    have hmaxev : (fun r : ℝ => (max r t)⁻¹) =ᶠ[𝓝 s] fun r => r⁻¹ := by
      filter_upwards [Ioi_mem_nhds hs.1] with r hr
      rw [max_eq_left (le_of_lt hr)]
    have hI : HasDerivAt (fun r : ℝ => (max r t)⁻¹) (-(s ^ 2)⁻¹) s := by
      refine HasDerivAt.congr_of_eventuallyEq ?_ hmaxev
      simpa using (hasDerivAt_inv (ne_of_gt hs0))
    have hfun : (fun r => metricCovDeriv (rescaledMetric_S57 S.base.metric t ht r) h N x v) =
        fun r => (max r t)⁻¹ * metricCovDeriv (S.base.metric r) h N x v := by
      funext r
      simp only [rescaledMetric_S57, DifferentialGeometry.Geometry.Metric.metricCovDeriv_scaleMetric_left]
      rfl
    rw [hfun]
    have hP := hI.mul hF
    convert hP using 1
    simp only [Ev, defectJet_S57, smul_apply, add_apply,
      smul_eq_mul, max_eq_left (le_of_lt hs.1)]
    field_simp
    ring
  have hb : ∀ x ∈ K, ∀ s ∈ Ioo t u,
      Real.sqrt (normSq0S h x (N + 2) (Ev s x)) ≤ η / t := by
    intro x hx s hs
    have hs0 : 0 < s := lt_trans ht hs.1
    have hd := hdef x hx s hs
    simp only [Ev]
    rw [sqrt_normSq0S_smul, abs_neg, abs_of_nonneg (by positivity)]
    calc (s⁻¹ ^ 2) * Real.sqrt (normSq0S h x (N + 2) (defectJet_S57 S h N s x))
        ≤ (s⁻¹ ^ 2) * (η * s) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = η / s := by field_simp
      _ ≤ η / t := div_le_div_of_nonneg_left hη ht hs.1.le
  intro s hs x hx
  exact metricDerivNorm_le_of_closed_evolution (rescaledMetric_S57 S.base.metric t ht) t u
    (rescaled_hgram_S57 S.base.metric ht hgram) h N Ev K (η / t) (div_nonneg hη ht.le)
    hev hb s hs t ⟨le_rfl, htu⟩ x hx

omit [I.Boundaryless] in
/-- triangle inequality for `metricDerivNorm` in the middle metric. -/
theorem metricDerivNorm_triangle_S57 (a : ℕ) (g₁ g₂ g₃ gRef : SmoothRiemannianMetric I M) (x : M) :
    metricDerivNorm a g₁ g₃ gRef x ≤
      metricDerivNorm a g₁ g₂ gRef x + metricDerivNorm a g₂ g₃ gRef x := by
  unfold metricDerivNorm metricDiffCovDerivAt
  have e : metricCovDeriv g₁ gRef a x - metricCovDeriv g₃ gRef a x =
      (metricCovDeriv g₁ gRef a x - metricCovDeriv g₂ gRef a x) +
        (metricCovDeriv g₂ gRef a x - metricCovDeriv g₃ gRef a x) := by abel
  rw [e]
  exact sqrt_normSq0S_add_le gRef x (a + 2) _ _

/-- `ckErr`-type conclusion: on a window `[t, u] ⊆ [t, 2t]` the order-`N` pullback error against `h`
grows by at most `η` (the defect jet bound being `η r`). -/
theorem rescaled_metricDerivNorm_window_S57 {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (h : SmoothRiemannianMetric I M) {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) (hu : u ≤ 2 * t)
    (hreg : Icc t u ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric p.1) x₀ p.2 i j)
        (Icc t u ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (N : ℕ) (K : Set M) {η : ℝ} (hη : 0 ≤ η)
    (hdef : ∀ x ∈ K, ∀ r ∈ Ioo t u,
      Real.sqrt (normSq0S h x (N + 2) (defectJet_S57 S h N r x)) ≤ η * r) :
    ∀ s ∈ Icc t u, ∀ x ∈ K,
      metricDerivNorm N (rescaledMetric_S57 S.base.metric t ht s) h h x ≤
        metricDerivNorm N (rescaledMetric_S57 S.base.metric t ht t) h h x + η := by
  intro s hs x hx
  have h1 := rescaled_metricDerivNorm_duhamel_S57 S hS h ht htu hreg hgram N K hη hdef s hs x hx
  have h2 := metricDerivNorm_triangle_S57 N (rescaledMetric_S57 S.base.metric t ht s)
    (rescaledMetric_S57 S.base.metric t ht t) h h x
  have h3 : (η / t) * |s - t| ≤ η := by
    have : |s - t| ≤ t := by
      rw [abs_of_nonneg (by linarith [hs.1])]
      linarith [hs.2]
    calc (η / t) * |s - t| ≤ (η / t) * t :=
          mul_le_mul_of_nonneg_left this (div_nonneg hη ht.le)
      _ = η := by field_simp
  linarith

end GC.LongTime.Ch12
