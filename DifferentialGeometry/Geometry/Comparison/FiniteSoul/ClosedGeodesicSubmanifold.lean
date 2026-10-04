import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicCircle
import Mathlib.Topology.Instances.ZMultiples

/-!
# The closed geodesic as a totally geodesic `C^r` circle (S-SOUL2 adapters SA3–SA5)

Review of the finite soul design, §5: the circle output of S-SHAPE2 / S-SOUL2 ("a periodic curve")
must be shown to be an actual embedded, boundaryless, connected, totally geodesic `C^r` curve. For a
complete metric of class `C^{r+1}`, `r ≥ 2`, and `γ t = π Φ_t p`, `V t = (Φ_t p).snd`:
* SA3 `contMDiff_proj_geodesicFlow_of_complete` (`γ` is `C^r`),
  `hasMFDerivAt_proj_geodesicFlow_of_complete` (`γ' = V`), `inner_snd_geodesicFlow_eq_one`
  (unit speed, so `γ` is an immersion), and, for a closed geodesic of least period `ℓ`,
  `injOn_proj_geodesicFlow_Ico_add` (injective on every interval of length `ℓ`);
* SA4 `proj_geodesicFlow_smul_snd` (totally geodesic: the geodesic with initial velocity
  `c • γ'(t₀)` is `s ↦ γ (t₀ + c s)`) and `proj_geodesicFlow_smul_snd_mem_range`;
* SA5 `isConnected_range_proj_geodesicFlow` and the local arc charts
  `isOpenEmbedding_restrict_proj_geodesicFlow` (`γ` restricted to any open interval of length `ℓ`
  is an open embedding into its trace: no boundary). Compactness is CMS-T's
  `isCompact_range_geodesicFlow`, the global circle is SA1.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **SA3 (regularity).** On a complete manifold every geodesic `t ↦ π Φ_t p` of a `C^{r+1}`
metric is `C^r`. -/
theorem contMDiff_proj_geodesicFlow_of_complete
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) :
    ContMDiff 𝓘(ℝ, ℝ) I r (fun t => (g.geodesicFlow p t).proj) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have h := g.contMDiffOn_geodesicFlow hr1
  rw [hD] at h
  have h2 : ContMDiff 𝓘(ℝ, ℝ) I.tangent r (fun t => g.geodesicFlow p t) :=
    (contMDiffOn_univ.1 h).comp (contMDiff_const.prodMk contMDiff_id)
  exact (Bundle.contMDiff_proj (TangentSpace I)).comp h2

/-- **SA3 (velocity).** On a complete manifold, `γ' (t) = (Φ_t p).snd` at every time. -/
theorem hasMFDerivAt_proj_geodesicFlow_of_complete
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow p s).proj) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p t).snd) := by
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  exact g.hasMFDerivAt_geodesicFlow_proj (one_le_two.trans hr) (by rw [hD]; exact mem_univ _)

/-- **SA3 (unit speed).** A unit geodesic of a complete metric has unit speed at every time; in
particular it is an immersion. -/
theorem inner_snd_geodesicFlow_eq_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} (hunit : g.inner p.proj p.snd p.snd = 1) (t : ℝ) :
    g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd (g.geodesicFlow p t).snd = 1 := by
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  rw [g.inner_geodesicFlow_eq (one_le_two.trans hr) p t (by rw [hD]; exact mem_univ _), hunit]

/-- **SA3 (injectivity).** A closed geodesic of least period `ℓ` (injective on `[0, ℓ)`) is
injective on every interval `[a, a + ℓ)`. -/
theorem injOn_proj_geodesicFlow_Ico_add
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} (hℓ : 0 < ℓ) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) (a : ℝ) :
    InjOn (fun t => (g.geodesicFlow p t).proj) (Ico a (a + ℓ)) := by
  intro s hs t ht hst
  obtain ⟨k, hk⟩ := (proj_geodesicFlow_eq_iff_of_closed g hr hnorm hℓ hper hinj).1 hst
  have h1 : (k : ℝ) * ℓ < ℓ := by rw [← hk]; linarith [hs.2, ht.1]
  have h2 : -ℓ < (k : ℝ) * ℓ := by rw [← hk]; linarith [hs.1, ht.2]
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk2 : (-1 : ℝ) < k := by nlinarith
  have hk0 : k = 0 := by
    have : k < 1 := by exact_mod_cast hk1
    have : -1 < k := by exact_mod_cast hk2
    omega
  rw [hk0, Int.cast_zero, zero_mul] at hk
  linarith

/-- **SA4 (totally geodesic).** The geodesic with initial velocity `c • γ'(t₀)` at `γ t₀` is
`s ↦ γ (t₀ + c s)`. -/
theorem proj_geodesicFlow_smul_snd
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) (t₀ c s : ℝ) :
    (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, c • (g.geodesicFlow p t₀).snd⟩ :
      TangentBundle I M) s).proj = (g.geodesicFlow p (t₀ + c * s)).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hmem : ∀ (Q : TangentBundle I M) (τ : ℝ), (Q, τ) ∈ g.geodesicFlowDomain := fun Q τ => by
    rw [hD]; exact mem_univ _
  rw [g.geodesicFlow_smul_eq hr1 (g.geodesicFlow p t₀) c s (hmem _ _),
    ← g.geodesicFlow_add hr1 (hmem p t₀) (hmem p (t₀ + c * s))]

/-- **SA4 (trace form).** Geodesics tangent to `γ` stay on its trace. -/
theorem proj_geodesicFlow_smul_snd_mem_range
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) (t₀ c s : ℝ) :
    (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, c • (g.geodesicFlow p t₀).snd⟩ :
      TangentBundle I M) s).proj ∈ range (fun t => (g.geodesicFlow p t).proj) := by
  rw [proj_geodesicFlow_smul_snd g hr hnorm p t₀ c s]
  exact mem_range_self _

/-- **SA5 (connected).** The trace of a geodesic of a complete metric is connected. -/
theorem isConnected_range_proj_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) :
    IsConnected (range (fun t => (g.geodesicFlow p t).proj)) :=
  isConnected_range (contMDiff_proj_geodesicFlow_of_complete g hr hnorm p).continuous

/-- **SA5 (no boundary: local arc charts).** For a closed unit geodesic of least period `ℓ`,
`γ` restricted to any open interval of length `ℓ` is an open embedding into its trace. -/
theorem isOpenEmbedding_restrict_proj_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} (hℓ : 0 < ℓ) (hunit : g.inner p.proj p.snd p.snd = 1)
    (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) (a : ℝ) :
    IsOpenEmbedding (fun t : Ioo a (a + ℓ) =>
      (⟨(g.geodesicFlow p t).proj, mem_range_self (t : ℝ)⟩ :
        range (fun t => (g.geodesicFlow p t).proj))) := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  obtain ⟨e, he⟩ := exists_homeomorph_addCircle_range_geodesicFlow g hr hnorm hunit hper hinj
  have hc := (AddCircle.openPartialHomeomorphCoe ℓ a).isOpenEmbedding_restrict
  have heq : (fun t : Ioo a (a + ℓ) =>
      (⟨(g.geodesicFlow p t).proj, mem_range_self (t : ℝ)⟩ :
        range (fun t => (g.geodesicFlow p t).proj))) =
      e ∘ (fun t : (AddCircle.openPartialHomeomorphCoe ℓ a).source =>
        AddCircle.openPartialHomeomorphCoe ℓ a t) := by
    funext t
    apply Subtype.ext
    exact (he t).symm
  rw [heq]
  exact e.isOpenEmbedding.comp hc

end DifferentialGeometry.Geometry.FiniteSoul
