import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.FlowLemmas
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.ShortSegment

/-!
# Unit-speed segments of a finite metric are geodesics (CM2.a)

For a `C^{r+1}` metric, `r ≥ 2`, every unit-speed metric segment `c : [0, ℓ] → M` is an orbit of
the ported geodesic flow (`exists_geodesicFlow_eq_of_segment`), equivalently
`c t = exp_{c 0} (t • u)` with `|u| = 1` (`exists_expMap_eq_of_segment`). The short case is CM1.e
(`eq_expMap_of_short_segment`); the general case continues along the segment with one uniform
normal-chart radius over its compact image.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-! ## CM2.a: unit-speed segments are geodesics -/

section Segments

variable [NeZero (Module.finrank ℝ E)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- A short segment from the centre of a normal chart is an orbit of the geodesic flow. -/
theorem exists_geodesicFlow_eq_of_short_segment (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {x : M} {ρ : ℝ} (e : OpenPartialHomeomorph E M)
    (he : e.source = {v : E | g.inner x v v < ρ ^ 2} ∧ e.target = ball x ρ ∧
      (∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
        e v = g.expMap (⟨x, v⟩ : TangentBundle I M)) ∧
      ContMDiffOn 𝓘(ℝ, E) I r e e.source ∧ ContMDiffOn I 𝓘(ℝ, E) r e.symm e.target ∧
      ∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v))
    {c : ℝ → M} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hℓρ : ℓ < ρ) (hc0 : c 0 = x)
    (hseg : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ, dist (c s) (c t) = |s - t|) :
    ∃ u : E, g.inner x u u = 1 ∧ ∀ t ∈ Icc 0 ℓ,
      ((⟨x, u⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain ∧
        c t = (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨u, hu, hc⟩ := eq_expMap_of_short_segment g hr hnorm e he hℓ hℓρ hc0 hseg
  refine ⟨u, hu, fun t ht => ?_⟩
  have hsrc : t • u ∈ e.source := by
    rw [he.1, mem_ofPred_eq]
    refine (inner_smul_self_smul g x t u).trans_lt ?_
    rw [hu, mul_one]
    exact pow_lt_pow_left₀ (ht.2.trans_lt hℓρ) ht.1 (by norm_num)
  have hD : ((⟨x, u⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain :=
    (g.mem_expDomain_smul_iff hr1 (x := x) (v := u) (t := t)).mp (he.2.2.1 _ hsrc).1
  exact ⟨hD, (hc t ht).trans (g.expMap_smul_eq_proj_geodesicFlow hr1 x u t hD)⟩

/-- **CM2.a** Every unit-speed metric segment of a finite metric (`C^{r+1}`, `r ≥ 2`) is an orbit
of the ported geodesic flow. (Frozen form minus the unused `0 ≤ ℓ`.) -/
theorem exists_geodesicFlow_eq_of_segment (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {c : ℝ → M} {ℓ : ℝ}
    (hseg : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ, dist (c s) (c t) = |s - t|) :
    ∃ u : E, g.inner (c 0) u u = 1 ∧ ∀ t ∈ Icc 0 ℓ,
      ((⟨c 0, u⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain ∧
      c t = (g.geodesicFlow (⟨c 0, u⟩ : TangentBundle I M) t).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  rcases lt_or_ge ℓ 0 with hneg | hℓ
  · obtain ⟨u, hu⟩ := exists_inner_self_eq_one g (c 0)
    exact ⟨u, hu, fun t ht => absurd (ht.1.trans ht.2) (not_le.mpr hneg)⟩
  have hlip : LipschitzOnWith 1 c (Icc 0 ℓ) := LipschitzOnWith.of_dist_le_mul fun s hs t ht => by
    rw [hseg s hs t ht, NNReal.coe_one, one_mul, Real.dist_eq]
  have hK : IsCompact (c '' Icc 0 ℓ) := isCompact_Icc.image_of_continuousOn hlip.continuousOn
  obtain ⟨ρ, hρ, hcharts⟩ := exists_uniform_normal_charts g hr hnorm hK
  set h : ℝ := ρ / 4 with hh_def
  have hh : 0 < h := by positivity
  have hwin : ∀ a ∈ Icc 0 ℓ, ∃ u : E, g.inner (c a) u u = 1 ∧
      ∀ τ ∈ Icc 0 (min (2 * h) (ℓ - a)),
        ((⟨c a, u⟩ : TangentBundle I M), τ) ∈ g.geodesicFlowDomain ∧
          c (a + τ) = (g.geodesicFlow (⟨c a, u⟩ : TangentBundle I M) τ).proj := by
    intro a ha
    obtain ⟨e, he⟩ := hcharts (c a) (mem_image_of_mem c ha)
    have hL0 : 0 ≤ min (2 * h) (ℓ - a) := le_min (by positivity) (by linarith [ha.2])
    have hLρ : min (2 * h) (ℓ - a) < ρ := (min_le_left _ _).trans_lt (by linarith)
    refine exists_geodesicFlow_eq_of_short_segment g hr hnorm e he (c := fun τ => c (a + τ))
      hL0 hLρ (by simp) ?_
    intro s hs t ht
    have hs' : a + s ∈ Icc 0 ℓ :=
      ⟨by linarith [ha.1, hs.1], by linarith [hs.2, min_le_right (2 * h) (ℓ - a)]⟩
    have ht' : a + t ∈ Icc 0 ℓ :=
      ⟨by linarith [ha.1, ht.1], by linarith [ht.2, min_le_right (2 * h) (ℓ - a)]⟩
    change dist (c (a + s)) (c (a + t)) = |s - t|
    rw [hseg _ hs' _ ht']
    congr 1
    ring
  have hinj : ∀ a ∈ Icc 0 ℓ, ∀ τ : ℝ, 0 < τ → τ < ρ → ∀ w u : E, g.inner (c a) w w = 1 →
      g.inner (c a) u u = 1 →
      g.expMap (⟨c a, τ • w⟩ : TangentBundle I M) = g.expMap (⟨c a, τ • u⟩ : TangentBundle I M) →
      w = u := by
    intro a ha τ hτ hτρ w u hw hu heq
    obtain ⟨e, he⟩ := hcharts (c a) (mem_image_of_mem c ha)
    exact eq_of_expMap_smul_eq g e he.1 he.2.2.1 hτ hτρ hw hu heq
  obtain ⟨u₀, hu₀, hwin₀⟩ := hwin 0 ⟨le_rfl, hℓ⟩
  set P₀ : TangentBundle I M := ⟨c 0, u₀⟩ with hP₀
  have key : ∀ k : ℕ, (k : ℝ) * h ≤ ℓ → ∀ τ ∈ Icc 0 (min (2 * h) (ℓ - k * h)),
      (P₀, k * h + τ) ∈ g.geodesicFlowDomain ∧ c (k * h + τ) = (g.geodesicFlow P₀ (k * h + τ)).proj := by
    intro k
    induction k with
    | zero =>
      intro _ τ hτ
      simp only [Nat.cast_zero, zero_mul, zero_add, sub_zero] at hτ ⊢
      simpa only [zero_add] using hwin₀ τ (by rwa [sub_zero])
    | succ k ih =>
      intro hk τ hτ
      set a : ℝ := (k : ℝ) * h with ha_def
      have hcast : ((k + 1 : ℕ) : ℝ) * h = a + h := by push_cast; ring
      rw [hcast] at hk hτ ⊢
      have ha0 : 0 ≤ a := by positivity
      have hak : a ≤ ℓ := by linarith
      have hhwin : h ∈ Icc 0 (min (2 * h) (ℓ - a)) := ⟨hh.le, le_min (by linarith) (by linarith)⟩
      obtain ⟨hDa, hca⟩ := ih hak h hhwin
      have ha' : a + h ∈ Icc 0 ℓ := ⟨by linarith, hk⟩
      obtain ⟨u', hu', hwin'⟩ := hwin (a + h) ha'
      have hqunit := g.inner_geodesicFlow_eq hr1 P₀ (a + h) hDa
      have hshift := fun σ : ℝ => mem_geodesicFlowDomain_geodesicFlow_iff hr1 (s := σ) hDa
      have hadd := fun σ : ℝ => fun hσ : (P₀, a + h + σ) ∈ g.geodesicFlowDomain =>
        g.geodesicFlow_add hr1 hDa hσ
      generalize hq : g.geodesicFlow P₀ (a + h) = q at hca hqunit hshift hadd
      obtain ⟨y, w⟩ := q
      change c (a + h) = y at hca
      subst hca
      change g.inner (c (a + h)) w w = g.inner (c 0) u₀ u₀ at hqunit
      rw [hu₀] at hqunit
      rcases eq_or_lt_of_le (sub_nonneg.mpr hk) with hzero | hpos
      · have hτ0 : τ = 0 := le_antisymm
          (hτ.2.trans ((min_le_right _ _).trans (le_of_eq hzero.symm))) hτ.1
        subst hτ0
        rw [add_zero, hq]
        exact ⟨hDa, rfl⟩
      · set τ₀ : ℝ := min h (ℓ - (a + h)) with hτ₀_def
        have hτ₀ : 0 < τ₀ := lt_min hh hpos
        have hτ₀h : τ₀ ≤ h := min_le_left _ _
        have hτ₀ℓ : τ₀ ≤ ℓ - (a + h) := min_le_right _ _
        have hwin1 : h + τ₀ ∈ Icc 0 (min (2 * h) (ℓ - a)) :=
          ⟨by linarith, le_min (by linarith) (by linarith)⟩
        obtain ⟨hD1, hc1⟩ := ih hak (h + τ₀) hwin1
        rw [← add_assoc] at hD1 hc1
        have hqD : ((⟨c (a + h), w⟩ : TangentBundle I M), τ₀) ∈ g.geodesicFlowDomain :=
          (hshift τ₀).mpr hD1
        have h1 : c (a + h + τ₀) = g.expMap (⟨c (a + h), τ₀ • w⟩ : TangentBundle I M) := by
          rw [g.expMap_smul_eq_proj_geodesicFlow hr1 (c (a + h)) w τ₀ hqD, ← hadd τ₀ hD1]
          exact hc1
        obtain ⟨hD2, hc2⟩ := hwin' τ₀ ⟨hτ₀.le, le_min (by linarith) hτ₀ℓ⟩
        have h2 : c (a + h + τ₀) = g.expMap (⟨c (a + h), τ₀ • u'⟩ : TangentBundle I M) := by
          rw [hc2]
          exact (g.expMap_smul_eq_proj_geodesicFlow hr1 (c (a + h)) u' τ₀ hD2).symm
        have hwu : w = u' :=
          hinj (a + h) ha' τ₀ hτ₀ (by linarith) w u' hqunit hu' (h1.symm.trans h2)
        subst hwu
        obtain ⟨hD3, hc3⟩ := hwin' τ hτ
        have hD4 : (P₀, a + h + τ) ∈ g.geodesicFlowDomain := (hshift τ).mp hD3
        refine ⟨hD4, ?_⟩
        rw [hadd τ hD4]
        exact hc3
  refine ⟨u₀, hu₀, fun t ht => ?_⟩
  set k : ℕ := ⌊t / h⌋₊ with hk_def
  have hkt : (k : ℝ) * h ≤ t := by
    have := Nat.floor_le (div_nonneg ht.1 hh.le)
    rwa [le_div_iff₀ hh] at this
  have htk : t < ((k : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one (t / h)
    rwa [div_lt_iff₀ hh] at this
  have hτ : t - k * h ∈ Icc 0 (min (2 * h) (ℓ - k * h)) :=
    ⟨by linarith, le_min (by linarith) (by linarith [ht.2])⟩
  have hres := key k (hkt.trans ht.2) (t - k * h) hτ
  rwa [add_sub_cancel] at hres

/-- The frozen form of CM2.a (with the unused `0 ≤ ℓ`). -/
example (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {c : ℝ → M} {ℓ : ℝ} (_hℓ : 0 ≤ ℓ)
    (hseg : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ, dist (c s) (c t) = |s - t|) :
    ∃ u : E, g.inner (c 0) u u = 1 ∧ ∀ t ∈ Icc 0 ℓ,
      ((⟨c 0, u⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain ∧
      c t = (g.geodesicFlow (⟨c 0, u⟩ : TangentBundle I M) t).proj :=
  exists_geodesicFlow_eq_of_segment g hr hnorm hseg

/-- CM2.a, exponential form: a unit-speed segment is `t ↦ exp_{c 0} (t u)`. -/
theorem exists_expMap_eq_of_segment (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {c : ℝ → M} {ℓ : ℝ}
    (hseg : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ, dist (c s) (c t) = |s - t|) :
    ∃ u : E, g.inner (c 0) u u = 1 ∧ ∀ t ∈ Icc 0 ℓ,
      (⟨c 0, t • u⟩ : TangentBundle I M) ∈ g.expDomain ∧
      c t = g.expMap (⟨c 0, t • u⟩ : TangentBundle I M) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨u, hu, hflow⟩ := exists_geodesicFlow_eq_of_segment g hr hnorm hseg
  refine ⟨u, hu, fun t ht => ⟨?_, ?_⟩⟩
  · exact (g.mem_expDomain_smul_iff hr1 (x := c 0) (v := u) (t := t)).mpr (hflow t ht).1
  · exact (hflow t ht).2.trans (g.expMap_smul_eq_proj_geodesicFlow hr1 (c 0) u t (hflow t ht).1).symm

end Segments

end Bundle.ContMDiffRiemannianMetric
