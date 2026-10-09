import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointBandBinding
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointLevelKernels

/-!
# LFR23 (ii) and the distance levels: field, frontier, connectivity

Row LFR23 (master207A:26745), on a complete finite metric `g : C^{r+1}` (`2 ≤ r`), `sec ≥ 0`, with
the endpoint model `q` (`δ ≤ 1/9600`):
* `exists_endpoint_field` (LFR23 (ii)): ONE smooth outward field `V`, `|V| < 2`, pairing `< -3/4`
  with EVERY inward direction on an open `O ⊇ {1/2 ≤ r ≤ 37/4}`, its complete flow `Φ`, the rate
  `3/4`, the unique continuous hitting time and the band product
  `{r = 5} × [1/2, 37/4] ≃ₜ {1/2 ≤ r ≤ 37/4}` — CMS-T's `exists_endpoint_band_field` with `S = {z₀}`
  and the inward unit vectors negated;
* `frontier_closedBall_eq_sphere_of_endpoint`: `∂B̄(z₀, a) = {r = a}` for `a ∈ [1/2, 37/4]`;
* `isPathConnected_sphere_of_endpoint`: every level `{r = a}`, `a ∈ [1, 9]`, is path connected
  (blueprint: two level points are `3δ`-close; project a short segment by the hitting time).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.FiniteSoul

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {r : ℕ∞}

/-- **LFR23 (ii).** The endpoint model gives one smooth outward field near the closed band, with
norm `< 2` and pairing `< -3/4` against EVERY inward unit direction, its complete flow, and the
hitting-time band product of the same flow. -/
theorem exists_endpoint_field
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 9600) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (V x) (V x) < 2 ^ 2) ∧
      ∃ O : Set M, IsOpen O ∧ (fun x => infDist x ({z₀} : Set M)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4) ⊆ O ∧
        (∀ x ∈ O, ∀ u ∈ g.finiteMinimizingDirectionsTo ({z₀} : Set M) x, g.inner x (V x) u < -(3 / 4)) ∧
      ∃ Φ : ℝ → M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) ∧ (∀ x, Φ 0 x = x) ∧
        (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
        (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x)))) ∧
        (∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ O ∩ ({z₀} : Set M)ᶜ) →
          infDist x ({z₀} : Set M) + 3 / 4 * t ≤ infDist (Φ t x) ({z₀} : Set M)) ∧
        ContinuousOn (fun p : M × ℝ => hittingTime Φ (fun x => infDist x ({z₀} : Set M)) p.1 p.2)
          (((fun x => infDist x ({z₀} : Set M)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4)) ×ˢ Icc (1 / 2 : ℝ) (37 / 4)) ∧
        (∀ x, infDist x ({z₀} : Set M) ∈ Icc (1 / 2 : ℝ) (37 / 4) → ∀ s ∈ Icc (1 / 2 : ℝ) (37 / 4),
          infDist (Φ (hittingTime Φ (fun x => infDist x ({z₀} : Set M)) x s) x) ({z₀} : Set M) = s ∧
          (∀ u ∈ uIcc 0 (hittingTime Φ (fun x => infDist x ({z₀} : Set M)) x s),
            infDist (Φ u x) ({z₀} : Set M) ∈ uIcc (infDist x ({z₀} : Set M)) s) ∧
          3 / 4 * |hittingTime Φ (fun x => infDist x ({z₀} : Set M)) x s| ≤ |s - infDist x ({z₀} : Set M)| ∧
          ∀ t, (∀ u ∈ uIcc 0 t, Φ u x ∈ O ∩ ({z₀} : Set M)ᶜ) → infDist (Φ t x) ({z₀} : Set M) = s →
            hittingTime Φ (fun x => infDist x ({z₀} : Set M)) x s = t) ∧
        ∃ e : ({x : M // infDist x ({z₀} : Set M) = 5} × Icc (1 / 2 : ℝ) (37 / 4)) ≃ₜ {x : M // infDist x ({z₀} : Set M) ∈ Icc (1 / 2 : ℝ) (37 / 4)},
          (∀ p, (e p : M) = Φ (hittingTime Φ (fun x => infDist x ({z₀} : Set M)) p.1 p.2) p.1) ∧
          (∀ y, ((e.symm y).1 : M) = Φ (hittingTime Φ (fun x => infDist x ({z₀} : Set M)) y 5) y) ∧
          (∀ y, ((e.symm y).2 : ℝ) = infDist (y : M) ({z₀} : Set M)) ∧
          (∀ p, infDist (e p : M) ({z₀} : Set M) = p.2) ∧
          ∀ x : {x : M // infDist x ({z₀} : Set M) = 5}, (e (x, ⟨5, by norm_num, by norm_num⟩) : M) = x := by
  have hA : IsClosed ((fun x => infDist x ({z₀} : Set M)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4)) :=
    isClosed_Icc.preimage (continuous_infDist_pt _)
  have hne : ∀ x, (g.finiteMinimizingDirectionsTo ({z₀} : Set M) x).Nonempty := fun x =>
    (g.finiteMinimizingDirectionsTo_nonempty_isCompact hr hnorm isClosed_singleton
      (singleton_nonempty z₀) x).1
  choose v hv using hne
  have hwunit : ∀ x ∈ (fun x => infDist x ({z₀} : Set M)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4),
      g.inner x (-(v x : E)) (-(v x : E)) = 1 := fun x _ => by
    have h1 := g.inner_smul_self_smul x (-1) (v x)
    rw [neg_one_sq, one_mul, (hv x).1] at h1
    rw [← neg_one_smul ℝ (v x : E)]
    exact h1
  have hwout : ∀ x ∈ (fun x => infDist x ({z₀} : Set M)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4),
      ∀ u ∈ g.finiteMinimizingDirectionsTo ({z₀} : Set M) x,
        g.inner x (-(v x : E)) u < -(7 / 8) := fun x hx u hu => by
    have hx' : dist z₀ x ∈ Icc (1 / 2 : ℝ) (37 / 4) := by
      have h := hx
      simp only [mem_preimage, infDist_singleton] at h
      rwa [dist_comm] at h
    exact inner_neg_lt_of_endpoint_band g hr hnorm hsec hδ hδ' hq0 hqnn hdist hdense hx'.1 hx'.2
      (hv x) hu
  exact exists_endpoint_band_field g hr hnorm isClosed_singleton (singleton_nonempty z₀) hA
    (by norm_num) ⟨by norm_num, by norm_num⟩ subset_rfl (fun x => (-(v x : E) : E)) hwunit hwout

/-- **LFR23, the frontier of a ball in the band.** For `a ∈ [1/2, 37/4]`, `∂B̄(z₀, a) = {r = a}`:
the distance increases along the outward flow. -/
theorem frontier_closedBall_eq_sphere_of_endpoint
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 9600) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) {a : ℝ}
    (ha : a ∈ Icc (1 / 2 : ℝ) (37 / 4)) :
    frontier (closedBall z₀ a) = sphere z₀ a := by
  obtain ⟨V, -, -, O, hO, hAO, -, Φ, hΦ, hΦ0, -, -, hrate, -⟩ :=
    exists_endpoint_field g hr hnorm hsec hδ hδ' hq0 hqnn hdist hdense
  refine Subset.antisymm frontier_closedBall_subset_sphere fun x hx => ?_
  have hxa : infDist x ({z₀} : Set M) = a := by rw [infDist_singleton]; exact hx
  have hxU : x ∈ O ∩ ({z₀} : Set M)ᶜ := by
    refine ⟨hAO (show infDist x ({z₀} : Set M) ∈ Icc (1 / 2 : ℝ) (37 / 4) by rw [hxa]; exact ha),
      fun hxz => ?_⟩
    rw [mem_singleton_iff] at hxz
    rw [hxz, infDist_singleton, dist_self] at hxa
    linarith [ha.1]
  have h := mem_frontier_le_of_rate hΦ.continuous hΦ0 (hO.inter isClosed_singleton.isOpen_compl)
    (by norm_num : (0 : ℝ) < 3 / 4) hrate hxU hxa
  have hset : {y : M | infDist y ({z₀} : Set M) ≤ a} = closedBall z₀ a := by
    ext y
    change infDist y ({z₀} : Set M) ≤ a ↔ _
    rw [infDist_singleton, mem_closedBall]
  rwa [hset] at h

/-- **LFR23, the levels are connected.** For `a ∈ [1, 9]` the level `{r = a}` is path connected
(two of its points are `3δ`-close; a short segment between them stays in the band and is projected
to the level by the hitting time of the outward flow). -/
theorem isPathConnected_sphere_of_endpoint
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 9600) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) {a : ℝ}
    (ha : a ∈ Icc (1 : ℝ) 9) :
    IsPathConnected (sphere z₀ a) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have h0E : ∀ (x : M) (u : E), g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x := by
    intro x u
    have h3 := g.expMap_smul_eq_proj_geodesicFlow hr1 x u 0 (by rw [hD]; exact mem_univ _)
    rw [g.geodesicFlow_zero hr1] at h3
    exact h3
  obtain ⟨V, -, -, O, -, hAO, -, Φ, hΦ, hΦ0, -, -, -, hcont, hspec, -⟩ :=
    exists_endpoint_field g hr hnorm hsec hδ hδ' hq0 hqnn hdist hdense
  have ha' : a ∈ Icc (1 / 2 : ℝ) (37 / 4) := ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hset : {x : M | infDist x ({z₀} : Set M) = a} = sphere z₀ a := by
    ext y
    change infDist y ({z₀} : Set M) = a ↔ _
    rw [infDist_singleton, mem_sphere]
  rw [← hset]
  refine isPathConnected_level_of_hittingTime hΦ.continuous hΦ0 ha' hcont
    (fun x hx => (hspec x hx a ha').1) (fun x hx => ?_) ?_ (fun x y hx hy => ?_)
  · have hx' : infDist x ({z₀} : Set M) ∈ Icc (1 / 2 : ℝ) (37 / 4) := by rw [hx]; exact ha'
    refine (hspec x hx' a ha').2.2.2 0 (fun u hu => ?_) (by rw [hΦ0]; exact hx)
    rw [uIcc_self, mem_singleton_iff] at hu
    rw [hu, hΦ0]
    refine ⟨hAO hx', fun hxz => ?_⟩
    rw [mem_singleton_iff] at hxz
    rw [hxz, infDist_singleton, dist_self] at hx
    linarith [ha.1]
  · obtain ⟨u, -, hiso, hz⟩ := exists_endpoint_far_segment g hr hnorm (by linarith) hq0 hqnn hdist
      hdense
    refine ⟨g.expMap (⟨z₀, a • u⟩ : TangentBundle I M), ?_⟩
    have h1 := hiso 0 ⟨le_rfl, by norm_num⟩ a ⟨by linarith [ha.1], by linarith [ha.2]⟩
    rw [hz, zero_sub, abs_neg, abs_of_nonneg (by linarith [ha.1])] at h1
    change infDist _ ({z₀} : Set M) = a
    rw [infDist_singleton, dist_comm, h1]
  · have hxa : dist z₀ x = a := by
      have h := hx
      change infDist x ({z₀} : Set M) = a at h
      rwa [infDist_singleton, dist_comm] at h
    have hya : dist z₀ y = a := by
      have h := hy
      change infDist y ({z₀} : Set M) = a at h
      rwa [infDist_singleton, dist_comm] at h
    have hxy := dist_le_three_mul_of_level hq0 hqnn hdist (by linarith [ha.2]) hxa hya
    obtain ⟨u, -, hiso, hend⟩ :=
      Bundle.ContMDiffRiemannianMetric.exists_unit_segment_expMap g hr hnorm x y
    set d := dist x y with hd
    have hmk : Continuous (fun w : TangentSpace I x => (⟨x, w⟩ : TangentBundle I M)) :=
      (FiberBundle.totalSpaceMk_isInducing E (TangentSpace I) x).continuous
    have hexp := g.continuous_expMap_of_completeSpace hr hnorm
    have hfc : Continuous (fun t : ℝ => g.expMap (⟨x, (t * d) • u⟩ : TangentBundle I M)) :=
      have hs : Continuous (fun t : ℝ => ((t * d) • u : E)) :=
        (continuous_id.mul continuous_const).smul continuous_const
      hexp.comp (hmk.comp hs)
    refine JoinedIn.ofLine hfc.continuousOn (by simp only [zero_mul]; exact h0E x u)
      (by simp only [one_mul]; exact hend) ?_
    rintro _ ⟨t, ht, rfl⟩
    beta_reduce
    have hd0 : 0 ≤ d := dist_nonneg
    have htd : t * d ∈ Icc 0 d := ⟨mul_nonneg ht.1 hd0, by nlinarith [ht.2]⟩
    have h1 := hiso 0 ⟨le_rfl, hd0⟩ (t * d) htd
    rw [h0E, zero_sub, abs_neg, abs_of_nonneg htd.1] at h1
    have h2 : dist x (g.expMap (⟨x, (t * d) • u⟩ : TangentBundle I M)) ≤ 3 * δ :=
      h1.le.trans (htd.2.trans hxy)
    change infDist _ ({z₀} : Set M) ∈ Icc (1 / 2 : ℝ) (37 / 4)
    rw [infDist_singleton]
    have h3 := dist_triangle z₀ x (g.expMap (⟨x, (t * d) • u⟩ : TangentBundle I M))
    have h4 : dist z₀ x ≤ dist z₀ (g.expMap (⟨x, (t * d) • u⟩ : TangentBundle I M)) +
        dist x (g.expMap (⟨x, (t * d) • u⟩ : TangentBundle I M)) := by
      have := dist_triangle z₀ (g.expMap (⟨x, (t * d) • u⟩ : TangentBundle I M)) x
      rwa [dist_comm (g.expMap (⟨x, (t * d) • u⟩ : TangentBundle I M)) x] at this
    rw [dist_comm]
    constructor <;> linarith [ha.1, ha.2]

end DifferentialGeometry.Geometry.Collapse
