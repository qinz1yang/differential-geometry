import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TotallyConvexSegments
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.PlanarCone
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts

/-!
# Local collinearity of totally convex sets with empty interior in a surface (S-SHAPE2, local part)

Setting: a complete metric `g` of class `C^{r+1}`, `r ≥ 2`, with the length distance (`hnorm`),
and a normal chart `e = exp_z` at `z` from the `g_z`-ball of radius `ρ` onto `ball z ρ` with
`dist z (e v) = |v|_{g_z}` (CM1.d).

* `not_linearIndependent_of_segment_through_center` (any dimension): a unit segment from
  `exp_z v` to `exp_z w` that passes through `z` forces `v, w` to be linearly dependent. This is
  the equality case of the triangle inequality: both halves of the segment are radial (the chart
  is injective), the backward half by reversal of the geodesic flow (`geodesicFlow_smul_eq`,
  `s = -1`), so `v = -s₀ ξ` and `w = (d - s₀) ξ`.
* `not_linearIndependent_of_expMap_mem_dim_two`: in dimension two, two chart vectors at a point
  `z` of a totally convex `C` with empty interior whose images lie in `C` are linearly dependent.
  Route (review of the finite soul design, §5): the connecting segment avoids `z`, so its chart
  curve avoids `0`; radial arcs from `z` stay in `C`; the planar cone lemma gives an open set.
* `exists_radius_not_linearIndependent_dim_two`: the same with one radius on a compact `C`,
  packaged with the normal charts.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M] in
/-- `g_z(s ξ, s ξ) = s² g_z(ξ, ξ)`. -/
theorem inner_smul_smul_self_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) (z : M) (s : ℝ) (ξ : E) :
    g.inner z (s • ξ) (s • ξ) = s ^ 2 * g.inner z ξ ξ := by
  exact g.inner_smul_self_smul z s ξ

omit [NeZero (Module.finrank ℝ E)] in
/-- **Equality case of the triangle inequality at the centre of a normal chart.** If a unit
segment from `exp_z v` to `exp_z w` (`v, w` in the chart domain) passes through `z`, then `v` and
`w` are linearly dependent. -/
theorem not_linearIndependent_of_segment_through_center
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {z : M} {ρ : ℝ} {e : OpenPartialHomeomorph E M}
    (hsrc : e.source = {v : E | g.inner z v v < ρ ^ 2})
    (hexp : ∀ v ∈ e.source, (⟨z, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
      e v = g.expMap (⟨z, v⟩ : TangentBundle I M))
    (hdist : ∀ v ∈ e.source, dist z (e v) = Real.sqrt (g.inner z v v))
    {v w : E} (hv : v ∈ e.source) (hw : w ∈ e.source) {u : E} (hu : g.inner (e v) u u = 1)
    {d : ℝ}
    (hseg : ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d,
      dist (g.expMap (⟨e v, s • u⟩ : TangentBundle I M))
        (g.expMap (⟨e v, t • u⟩ : TangentBundle I M)) = |s - t|)
    (hend : g.expMap (⟨e v, d • u⟩ : TangentBundle I M) = e w)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc 0 d) (hz : g.expMap (⟨e v, s₀ • u⟩ : TangentBundle I M) = z) :
    ¬ LinearIndependent ℝ ![v, w] := by
  intro hind
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hmem : ∀ (Q : TangentBundle I M) (τ : ℝ), (Q, τ) ∈ g.geodesicFlowDomain := fun Q τ => by
    rw [hD]; exact mem_univ _
  set x : M := e v with hxdef
  set p : TangentBundle I M := ⟨x, u⟩ with hpdef
  have hflow : ∀ (y : M) (ζ : E) (τ : ℝ), g.expMap (⟨y, τ • ζ⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, ζ⟩ : TangentBundle I M) τ).proj := fun y ζ τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 y ζ τ (hmem _ τ)
  set P : TangentBundle I M := g.geodesicFlow p s₀ with hPdef
  have hPz : P.proj = z := by rw [hPdef, ← hflow]; exact hz
  set ξ : E := P.snd with hξdef
  have hPeta : (⟨z, ξ⟩ : TangentBundle I M) = P := by rw [← hPz]
  have hξ : g.inner z ξ ξ = 1 := by
    have h := g.inner_geodesicFlow_eq hr1 p s₀ (hmem p s₀)
    rw [← hPz]
    exact h.trans hu
  have hx0 : g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x := by
    rw [zero_smul]; exact g.expMap_zero hr1 x
  -- the two distances along the segment
  have hd1 : dist z x = s₀ := by
    have h := hseg s₀ hs₀ 0 (left_mem_Icc.2 (hs₀.1.trans hs₀.2))
    rw [hz, hx0, sub_zero, abs_of_nonneg hs₀.1] at h
    exact h
  have hd2 : dist z (e w) = d - s₀ := by
    have h := hseg s₀ hs₀ d (right_mem_Icc.2 (hs₀.1.trans hs₀.2))
    rw [hz, hend, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hs₀.2)] at h
    exact h
  have hsq : ∀ y ∈ e.source, dist z (e y) ^ 2 = g.inner z y y := fun y hy => by
    rw [hdist y hy]; exact Real.sq_sqrt (g.inner_self_nonneg' z y)
  have hsrcξ : ∀ τ : ℝ, τ ^ 2 < ρ ^ 2 → τ • ξ ∈ e.source := fun τ hτ => by
    rw [hsrc]
    change g.inner z (τ • ξ) (τ • ξ) < ρ ^ 2
    rw [inner_smul_smul_self_finite, hξ, mul_one]
    exact hτ
  have hvsrc : g.inner z v v < ρ ^ 2 := by
    have := hv; rw [hsrc] at this; exact this
  have hwsrc : g.inner z w w < ρ ^ 2 := by
    have := hw; rw [hsrc] at this; exact this
  -- forward half: `w = (d - s₀) ξ`
  have hw' : (d - s₀) • ξ = w := by
    have hsrc1 : (d - s₀) • ξ ∈ e.source := hsrcξ _ (by rw [← hd2, hsq w hw]; exact hwsrc)
    apply e.injOn hsrc1 hw
    rw [(hexp _ hsrc1).2, hflow, hPeta, hPdef,
      ← g.geodesicFlow_add hr1 (hmem p s₀) (hmem p (s₀ + (d - s₀))), ← hflow,
      show s₀ + (d - s₀) = d by ring]
    exact hend
  -- backward half (reversal): `v = s₀ (-ξ)`
  have hv' : s₀ • ((-1 : ℝ) • ξ) = v := by
    have hsrc1 : s₀ • ((-1 : ℝ) • ξ) ∈ e.source := by
      rw [smul_smul]
      exact hsrcξ _ (by rw [mul_neg_one, neg_sq, ← hd1, hsq v hv]; exact hvsrc)
    apply e.injOn hsrc1 hv
    rw [(hexp _ hsrc1).2, hflow]
    have hrev : g.geodesicFlow (⟨z, (-1 : ℝ) • ξ⟩ : TangentBundle I M) s₀ =
        ⟨(g.geodesicFlow P (-1 * s₀)).proj, (-1 : ℝ) • (g.geodesicFlow P (-1 * s₀)).snd⟩ := by
      have h := g.geodesicFlow_smul_eq hr1 P (-1) s₀ (hmem P _)
      rw [hPz] at h
      exact h
    rw [hrev]
    change (g.geodesicFlow P (-1 * s₀)).proj = x
    rw [neg_one_mul, hPdef, ← g.geodesicFlow_add hr1 (hmem p s₀) (hmem p (s₀ + -s₀)),
      add_neg_cancel, g.geodesicFlow_zero hr1]
  have hcomb : (d - s₀) • v + s₀ • w = 0 := by
    rw [← hv', ← hw', smul_smul, smul_smul, smul_smul, ← add_smul]
    have : (d - s₀) * s₀ * -1 + s₀ * (d - s₀) = 0 := by ring
    rw [this, zero_smul]
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hind _ _ hcomb
  have hv0 : v = 0 := by
    rw [← hv', h2, zero_smul]
  exact hind.ne_zero 0 (by simpa using hv0)

/-- **Local collinearity in a surface.** At a point `z` of a totally convex set `C` with empty
interior, two vectors of a normal chart at `z` whose images lie in `C` are linearly dependent. -/
theorem not_linearIndependent_of_expMap_mem_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hconv : IsTotallyConvexFinite g C)
    (hint : interior C = ∅) {z : M} (hzC : z ∈ C) {ρ : ℝ} {e : OpenPartialHomeomorph E M}
    (hsrc : e.source = {v : E | g.inner z v v < ρ ^ 2}) (htgt : e.target = ball z ρ)
    (hexp : ∀ v ∈ e.source, (⟨z, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
      e v = g.expMap (⟨z, v⟩ : TangentBundle I M))
    (hdist : ∀ v ∈ e.source, dist z (e v) = Real.sqrt (g.inner z v v))
    {v w : E} (hv : v ∈ e.source) (hw : w ∈ e.source) (hvC : e v ∈ C) (hwC : e w ∈ C) :
    ¬ LinearIndependent ℝ ![v, w] := by
  intro hind
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hρ : 0 < ρ := by
    have h := e.map_source hv
    rw [htgt, mem_ball] at h
    exact dist_nonneg.trans_lt h
  -- shrink both vectors by `1/3`
  have hsmall : ∀ y ∈ e.source, e y ∈ C →
      (3 : ℝ)⁻¹ • y ∈ e.source ∧ e ((3 : ℝ)⁻¹ • y) ∈ C ∧
        Real.sqrt (g.inner z ((3 : ℝ)⁻¹ • y) ((3 : ℝ)⁻¹ • y)) < ρ / 3 := by
    intro y hy hyC
    have hy' : g.inner z y y < ρ ^ 2 := by
      have := hy; rw [hsrc] at this; exact this
    have hq : g.inner z ((3 : ℝ)⁻¹ • y) ((3 : ℝ)⁻¹ • y) = g.inner z y y / 9 := by
      rw [inner_smul_smul_self_finite]; ring
    have h0 := g.inner_self_nonneg' z y
    have hmem : (3 : ℝ)⁻¹ • y ∈ e.source := by
      rw [hsrc]
      change g.inner z ((3 : ℝ)⁻¹ • y) ((3 : ℝ)⁻¹ • y) < ρ ^ 2
      rw [hq]; nlinarith
    refine ⟨hmem, ?_, ?_⟩
    · rw [(hexp _ hmem).2]
      refine hconv.expMap_mem hr hnorm zero_le_one hzC ?_ _ ⟨by norm_num, by norm_num⟩
      rw [one_smul, ← (hexp y hy).2]
      exact hyC
    · rw [hq, Real.sqrt_lt' (by positivity)]
      nlinarith
  obtain ⟨hv3, hv3C, hv3n⟩ := hsmall v hv hvC
  obtain ⟨hw3, hw3C, hw3n⟩ := hsmall w hw hwC
  set v' : E := (3 : ℝ)⁻¹ • v with hv'def
  set w' : E := (3 : ℝ)⁻¹ • w with hw'def
  have hind' : LinearIndependent ℝ ![v', w'] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    have h := LinearIndependent.pair_iff.1 hind (s * 3⁻¹) (t * 3⁻¹)
      (by rw [← smul_smul, ← smul_smul]; exact hst)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  -- the connecting segment
  set x : M := e v' with hxdef
  set y : M := e w' with hydef
  obtain ⟨u, hu, hseg, hend, hmemC⟩ := hconv.exists_unit_segment_mem hr hnorm hv3C hw3C
  set d : ℝ := dist x y with hddef
  set σ : ℝ → M := fun s => g.expMap (⟨x, s • u⟩ : TangentBundle I M) with hσdef
  have hσ0 : σ 0 = x := by
    simp only [σ]; rw [zero_smul]; exact g.expMap_zero hr1 x
  have hσcont : ContinuousOn σ (Icc 0 d) := by
    refine Metric.continuousOn_iff.2 fun b hb ε hε => ⟨ε, hε, fun a ha hab => ?_⟩
    exact (hseg a ha b hb).trans_lt (by rw [← Real.dist_eq]; exact hab)
  have hdx : dist z x = Real.sqrt (g.inner z v' v') := hdist v' hv3
  have hdy : dist z y = Real.sqrt (g.inner z w' w') := hdist w' hw3
  have hσball : ∀ s ∈ Icc 0 d, σ s ∈ e.target := by
    intro s hs
    rw [htgt, mem_ball, dist_comm]
    have h1 : dist x (σ s) = s := by
      have h := hseg 0 (left_mem_Icc.2 (hs.1.trans hs.2)) s hs
      rw [show g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x from hσ0, zero_sub, abs_neg,
        abs_of_nonneg hs.1] at h
      exact h
    have h2 : d ≤ dist z x + dist z y := by
      rw [hddef, dist_comm z x]; exact dist_triangle x z y
    have h3 := dist_triangle z x (σ s)
    linarith [hs.2]
  -- the chart curve avoids the origin
  set c : ℝ → E := fun s => e.symm (σ s) with hcdef
  have hccont : ContinuousOn c (Icc 0 d) :=
    e.continuousOn_symm.comp hσcont (fun s hs => hσball s hs)
  have hcne : ∀ s ∈ Icc 0 d, c s ≠ 0 := by
    intro s hs hc0
    have hz' : σ s = z := by
      have h1 : e (c s) = σ s := e.right_inv (hσball s hs)
      have h0src : (0 : E) ∈ e.source := by
        rw [hsrc]; change g.inner z 0 0 < ρ ^ 2; simpa using pow_pos hρ 2
      rw [← h1, hc0, (hexp 0 h0src).2]
      exact g.expMap_zero hr1 z
    exact not_linearIndependent_of_segment_through_center g hr hnorm hsrc hexp hdist hv3 hw3 hu
      hseg hend hs hz' hind'
  have hc0 : c 0 = v' := by simp only [c]; rw [hσ0]; exact e.left_inv hv3
  have hcd : c d = w' := by simp only [c, σ]; rw [hend]; exact e.left_inv hw3
  -- the cone over the chart curve lies in `e⁻¹ C`
  obtain ⟨U, hUo, hUne, hUsub⟩ := exists_isOpen_subset_cone_of_finrank_two hdim dist_nonneg
    hccont hcne (by rw [hc0, hcd]; exact hind')
  have hcone : ∀ q ∈ U, q ∈ e.source ∧ e q ∈ C := by
    intro q hq
    obtain ⟨s, hs, t, ht, rfl⟩ := hUsub hq
    have hcs : c s ∈ e.source := e.map_target (hσball s hs)
    have hcs' : g.inner z (c s) (c s) < ρ ^ 2 := by
      have := hcs; rw [hsrc] at this; exact this
    have hts : t • c s ∈ e.source := by
      rw [hsrc]
      change g.inner z (t • c s) (t • c s) < ρ ^ 2
      rw [inner_smul_smul_self_finite]
      have h0 := g.inner_self_nonneg' z (c s)
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      nlinarith
    refine ⟨hts, ?_⟩
    rw [(hexp _ hts).2]
    refine hconv.expMap_mem hr hnorm zero_le_one hzC ?_ t ht
    rw [one_smul, ← (hexp _ hcs).2, e.right_inv (hσball s hs)]
    exact hmemC s hs
  have hUsrc : U ⊆ e.source := fun q hq => (hcone q hq).1
  have hopen : IsOpen (e '' U) := e.isOpen_image_of_subset_source hUo hUsrc
  have hsubC : e '' U ⊆ C := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hcone q hq).2
  have hint' : e '' U ⊆ interior C := interior_maximal hsubC hopen
  rw [hint] at hint'
  obtain ⟨q, hq⟩ := hUne
  exact hint' (mem_image_of_mem e hq)

/-- **Local collinearity with one radius on a compact set.** -/
theorem exists_radius_not_linearIndependent_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCc : IsCompact C)
    (hconv : IsTotallyConvexFinite g C) (hint : interior C = ∅) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ C, ∃ e : OpenPartialHomeomorph E M,
      e.source = {v : E | g.inner z v v < ρ ^ 2} ∧ e.target = ball z ρ ∧
      (∀ v ∈ e.source, (⟨z, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
        e v = g.expMap (⟨z, v⟩ : TangentBundle I M)) ∧
      (∀ v ∈ e.source, dist z (e v) = Real.sqrt (g.inner z v v)) ∧
      ∀ v ∈ e.source, ∀ w ∈ e.source, e v ∈ C → e w ∈ C → ¬ LinearIndependent ℝ ![v, w] := by
  obtain ⟨ρ, hρ, hch⟩ := g.exists_uniform_normal_charts hr hnorm hCc
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  obtain ⟨e, hsrc, htgt, hexp, -, -, hdist⟩ := hch z hz
  exact ⟨e, hsrc, htgt, hexp, hdist, fun v hv w hw hvC hwC =>
    not_linearIndependent_of_expMap_mem_dim_two g hr hnorm hdim hconv hint hz hsrc htgt hexp hdist
      hv hw hvC hwC⟩

end DifferentialGeometry.Geometry.FiniteSoul
