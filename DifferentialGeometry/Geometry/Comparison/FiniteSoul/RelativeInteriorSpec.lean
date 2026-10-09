import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeInteriorLocal

/-!
# S3-SLICE: the relative interior of a totally convex set (lane CMS3-SLICE, group G3)

For a complete metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`) and a nonempty totally convex `C`:

* `IsTotallyConvexFinite.proj_geodesicFlow_mem_maxSliceLocusOfOrder` (relative open-core
  propagation): a geodesic arc of `C` that meets the relative interior at one time lies in it at all
  interior times. Short steps by the relative radial cone, always at the midpoint, and connectedness of
  `(a, b)`; the relative interior is `C ∩ O` with `O` open (the CMS-B R1(i) proof with `int C` replaced
  by `relint C`).
* `subset_closure_maxSliceLocusOfOrder` (density): every point of `C` is the limit of a segment of `C`
  ending at a fixed relative interior point; only that endpoint needs local structure (risk R1).
* `maxSliceLocusOfOrder_eq_interior`: in full relative dimension the relative interior is `interior C`.
* `maxSliceLocusOfOrder_spec` (frozen interface S3-SLICE): all eight clauses. The frozen hypothesis
  `hCcl : IsClosed C` is not used by any clause and is dropped (linter-forced strengthening); the
  verbatim frozen statement is checked as an `example` in `RelativeInteriorApplications.lean`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- A convex combination towards the midpoint stays in the open interval. -/
theorem add_mul_midpoint_sub_mem_Ioo {a b s θ : ℝ} (hab : a < b) (hs : s ∈ Icc a b)
    (hθ : θ ∈ Ioc (0 : ℝ) 1) : s + θ * ((a + b) / 2 - s) ∈ Ioo a b := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  constructor <;> nlinarith [hs.1, hs.2]

/-- **Relative open-core propagation.** If `γ = π ∘ φ_·(p)` maps `[a, b]` into the totally convex `C`
and `γ s` lies in the relative interior for one `s ∈ [a, b]`, then `γ t` lies in it for every
`t ∈ (a, b)`. -/
theorem IsTotallyConvexFinite.proj_geodesicFlow_mem_maxSliceLocusOfOrder
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) (p : TangentBundle I M) {a b : ℝ}
    (hmaps : ∀ t ∈ Icc a b, (g.geodesicFlow p t).proj ∈ C) {s : ℝ} (hs : s ∈ Icc a b)
    (hsC : (g.geodesicFlow p s).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    ∀ t ∈ Ioo a b, (g.geodesicFlow p t).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  obtain ⟨O, hO, hCO⟩ := exists_isOpen_inter_eq_maxSliceLocusOfOrder g hr hnorm hC
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  have hZO : Z ⊆ O := fun x hx => by rw [← hCO] at hx; exact hx.2
  set γ : ℝ → M := fun t => (g.geodesicFlow p t).proj with hγ
  set σ : ℝ := Real.sqrt (g.inner p.proj p.snd p.snd) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hlip : ∀ s t : ℝ, dist (γ s) (γ t) ≤ σ * |t - s| := fun s t =>
    g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => by rw [hD]; exact mem_univ _)
  have hγc : Continuous γ := by
    refine Metric.continuous_iff.2 fun t ε hε => ⟨ε / (σ + 1), by positivity, fun z hz => ?_⟩
    refine (hlip z t).trans_lt ?_
    rw [Real.dist_eq] at hz
    calc σ * |t - z| = σ * |z - t| := by rw [abs_sub_comm]
      _ ≤ σ * (ε / (σ + 1)) := mul_le_mul_of_nonneg_left hz.le hσ0
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  obtain ⟨ρ, hρ, hcone⟩ := exists_expMap_smul_mem_maxSliceLocusOfOrder g hr hnorm
    (isCompact_Icc.image hγc : IsCompact (γ '' Icc a b))
  -- the short step
  have hstep : ∀ s₁ ∈ Icc a b, ∀ s₂ ∈ Icc a b, σ * |s₁ - s₂| < ρ → γ s₁ ∈ Z →
      ∀ c ∈ Ioc (0 : ℝ) 1, γ (s₂ + c * (s₁ - s₂)) ∈ Z := by
    intro s₁ hs₁ s₂ hs₂ hlt hint c hc
    have hspeed : g.inner (g.geodesicFlow p s₂).proj (g.geodesicFlow p s₂).snd
        (g.geodesicFlow p s₂).snd = σ ^ 2 := by
      rw [g.inner_geodesicFlow_eq hr1 p s₂ (by rw [hD]; exact mem_univ _), hσ,
        Real.sq_sqrt (DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g _ _)]
    have hv : g.inner (g.geodesicFlow p s₂).proj ((s₁ - s₂) • (g.geodesicFlow p s₂).snd)
        ((s₁ - s₂) • (g.geodesicFlow p s₂).snd) < ρ ^ 2 := by
      rw [DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self, hspeed]
      have h1 : (σ * |s₁ - s₂|) ^ 2 < ρ ^ 2 := by
        have h0 : 0 ≤ σ * |s₁ - s₂| := mul_nonneg hσ0 (abs_nonneg _)
        nlinarith
      calc (s₁ - s₂) ^ 2 * σ ^ 2 = (σ * |s₁ - s₂|) ^ 2 := by rw [mul_pow, sq_abs]; ring
        _ < ρ ^ 2 := h1
    have hend : g.expMap (⟨(g.geodesicFlow p s₂).proj, (s₁ - s₂) • (g.geodesicFlow p s₂).snd⟩ :
        TangentBundle I M) ∈ Z := by
      rw [← proj_geodesicFlow_add_eq_expMap g hr hnorm, add_sub_cancel]
      exact hint
    have h := hcone hC (γ s₂) ⟨s₂, hs₂, rfl⟩ (hmaps s₂ hs₂) _ hv hend c hc
    have heq : γ (s₂ + c * (s₁ - s₂)) = g.expMap (⟨(g.geodesicFlow p s₂).proj,
        c • (s₁ - s₂) • (g.geodesicFlow p s₂).snd⟩ : TangentBundle I M) := by
      change (g.geodesicFlow p (s₂ + c * (s₁ - s₂))).proj = _
      rw [proj_geodesicFlow_add_eq_expMap g hr hnorm p s₂, mul_smul]
    rw [heq]
    exact h
  intro t ht
  have hab : a < b := ht.1.trans ht.2
  -- connectedness of `(a, b)`
  set u : Set ℝ := γ ⁻¹' O with hu
  set v : Set ℝ := {t | ∃ δ > 0, ∀ z ∈ Ioo a b, |z - t| < δ → γ z ∉ Z} with hv
  have huo : IsOpen u := hO.preimage hγc
  have hvo : IsOpen v := by
    rw [Metric.isOpen_iff]
    rintro x ⟨δ, hδ, hkey⟩
    refine ⟨δ / 2, by linarith, fun x' hx' => ⟨δ / 2, by linarith, fun z hz hzx' => hkey z hz ?_⟩⟩
    rw [mem_ball, Real.dist_eq] at hx'
    calc |z - x| = |(z - x') + (x' - x)| := by ring_nf
      _ ≤ |z - x'| + |x' - x| := abs_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add hzx' hx'
      _ = δ := by ring
  have hcover : Ioo a b ⊆ u ∪ v := by
    intro x hx
    by_cases hxu : γ x ∈ Z
    · exact Or.inl (hZO hxu)
    · right
      set δ : ℝ := min (min (x - a) (b - x)) (ρ / (2 * σ + 1)) with hδ
      have hδ0 : 0 < δ := lt_min (lt_min (by linarith [hx.1]) (by linarith [hx.2])) (by positivity)
      refine ⟨δ, hδ0, fun z hz hzx hzint => hxu ?_⟩
      have hzx1 : |z - x| < x - a := lt_of_lt_of_le hzx ((min_le_left _ _).trans (min_le_left _ _))
      have hzx2 : |z - x| < b - x := lt_of_lt_of_le hzx ((min_le_left _ _).trans (min_le_right _ _))
      have hzx3 : |z - x| < ρ / (2 * σ + 1) := lt_of_lt_of_le hzx (min_le_right _ _)
      rw [abs_lt] at hzx1 hzx2
      have hs₂ : 2 * x - z ∈ Icc a b := ⟨by linarith, by linarith⟩
      have hlt : σ * |z - (2 * x - z)| < ρ := by
        rw [show z - (2 * x - z) = 2 * (z - x) by ring, abs_mul, abs_two]
        have h1 : σ * (2 * |z - x|) ≤ (2 * σ + 1) * |z - x| := by nlinarith [abs_nonneg (z - x)]
        have h2 : (2 * σ + 1) * |z - x| < ρ := by
          rw [lt_div_iff₀ (by positivity)] at hzx3; linarith
        linarith
      have h := hstep z (Ioo_subset_Icc_self hz) (2 * x - z) hs₂ hlt hzint (1 / 2)
        ⟨by norm_num, by norm_num⟩
      rwa [show 2 * x - z + 1 / 2 * (z - (2 * x - z)) = x by ring] at h
  have hdisj : Ioo a b ∩ (u ∩ v) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    rintro hx hxu ⟨δ, hδ, hkey⟩
    have hxZ : γ x ∈ Z := by
      rw [← hCO]
      exact ⟨hmaps x (Ioo_subset_Icc_self hx), hxu⟩
    exact hkey x hx (by rw [sub_self, abs_zero]; exact hδ) hxZ
  -- a point of `(a, b)` in `u`
  have hne : (Ioo a b ∩ u).Nonempty := by
    set m : ℝ := (a + b) / 2 with hm
    set c : ℝ := min 1 (ρ / ((σ + 1) * (|m - s| + 1))) with hc
    have hc0 : 0 < c := lt_min one_pos (by positivity)
    have hc1 : c ≤ 1 := min_le_left _ _
    have hs₂ : s + c * (m - s) ∈ Icc a b :=
      Ioo_subset_Icc_self (add_mul_midpoint_sub_mem_Ioo hab hs ⟨hc0, hc1⟩)
    have hlt : σ * |s - (s + c * (m - s))| < ρ := by
      rw [show s - (s + c * (m - s)) = -(c * (m - s)) by ring, abs_neg, abs_mul, abs_of_pos hc0]
      have hcle : c * ((σ + 1) * (|m - s| + 1)) ≤ ρ := by
        have := min_le_right 1 (ρ / ((σ + 1) * (|m - s| + 1)))
        rw [← hc, le_div_iff₀ (by positivity)] at this
        exact this
      nlinarith [abs_nonneg (m - s)]
    have h := hstep s hs (s + c * (m - s)) hs₂ hlt hsC (1 / 2) ⟨by norm_num, by norm_num⟩
    refine ⟨s + c / 2 * (m - s), add_mul_midpoint_sub_mem_Ioo hab hs ⟨by positivity, by linarith⟩,
      hZO ?_⟩
    rwa [show s + c * (m - s) + 1 / 2 * (s - (s + c * (m - s))) = s + c / 2 * (m - s) by ring] at h
  rcases (isPreconnected_iff_subset_of_disjoint.1 isPreconnected_Ioo) u v huo hvo hcover hdisj with
    hsub | hsub
  · have htO : γ t ∈ O := hsub ht
    change γ t ∈ Z
    rw [← hCO]
    exact ⟨hmaps t (Ioo_subset_Icc_self ht), htO⟩
  · exfalso
    obtain ⟨x, hx, hxu⟩ := hne
    obtain ⟨δ, hδ, hkey⟩ := hsub hx
    have hxZ : γ x ∈ Z := by
      rw [← hCO]
      exact ⟨hmaps x (Ioo_subset_Icc_self hx), hxu⟩
    exact hkey x hx (by rw [sub_self, abs_zero]; exact hδ) hxZ

/-- **Density of the relative interior.** -/
theorem subset_closure_maxSliceLocusOfOrder
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCne : C.Nonempty) (hC : IsTotallyConvexFinite g C) :
    C ⊆ closure (maxSliceLocusOfOrder I (r : ℕ∞ω) C) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  obtain ⟨z, hzZ⟩ := maxSliceLocusOfOrder_nonempty (I := I) (k := r) hCne
  have hzC : z ∈ C := maxSliceLocusOfOrder_subset hzZ
  intro x hx
  rcases eq_or_ne (Module.finrank ℝ E) 0 with hE | hE
  · -- in dimension `0` every point of `C` is a top slice
    apply subset_closure
    refine subset_maxSliceLocusOfOrder (singleton_subset_iff.2 hx) ?_ rfl
    have h0 : maxSliceDimOfOrder I (r : ℕ∞ω) C = 0 :=
      Nat.eq_zero_of_le_zero ((maxSliceDimOfOrder_le C).trans hE.le)
    rw [h0]
    exact IsEmbeddedSliceOfOrder.singleton x
  have : NeZero (Module.finrank ℝ E) := ⟨hE⟩
  rcases eq_or_ne x z with rfl | hxz
  · exact subset_closure hzZ
  obtain ⟨u, -, -, hend, hseg⟩ := hC.exists_unit_segment_mem hr hnorm hx hzC
  set ℓ := dist x z with hℓ
  have hℓ0 : 0 < ℓ := dist_pos.2 hxz
  have hflow : ∀ τ : ℝ, g.expMap (⟨x, τ • u⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 x u τ (by rw [hD]; exact mem_univ _)
  have hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t).proj ∈ C :=
    fun t ht => by rw [← hflow]; exact hseg t ht
  have hendZ : (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) ℓ).proj ∈
      maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
    rw [← hflow, hend]; exact hzZ
  have hprop := hC.proj_geodesicFlow_mem_maxSliceLocusOfOrder hr hnorm _ hmaps
    ⟨hℓ0.le, le_rfl⟩ hendZ
  have hcont : Continuous fun t => (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t).proj :=
    continuous_iff_continuousAt.2 fun t =>
      (g.hasMFDerivAt_geodesicFlow_proj hr1 (by rw [hD]; exact mem_univ (_, t))).continuousAt
  have hlim : Tendsto (fun t => (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t).proj)
      (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have h := hcont.continuousAt (x := (0 : ℝ))
    rw [ContinuousAt, g.geodesicFlow_zero hr1] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hℓ0] with t ht
  exact hprop t ht

/-- In full relative dimension the relative interior is the interior. -/
theorem maxSliceLocusOfOrder_eq_interior
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C)
    (hd : maxSliceDimOfOrder I (r : ℕ∞ω) C = Module.finrank ℝ E) :
    maxSliceLocusOfOrder I (r : ℕ∞ω) C = interior C := by
  have hslice := isEmbeddedSliceOfOrder_maxSliceLocusOfOrder g hr hnorm hC
  rw [hd] at hslice
  apply Subset.antisymm
  · exact interior_maximal maxSliceLocusOfOrder_subset hslice.isOpen
  · apply subset_maxSliceLocusOfOrder interior_subset
    rw [hd]
    exact IsEmbeddedSliceOfOrder.of_isOpen isOpen_interior

/-- **S3-SLICE** (frozen interface `maxSliceLocusOfOrder_spec`, `2 ≤ r`), without the unused
hypothesis `IsClosed C`. For a nonempty totally convex `C`, its relative interior
`Z = maxSliceLocusOfOrder I r C` is a nonempty totally geodesic `C^r` slice of dimension
`d = maxSliceDimOfOrder I r C ≤ dim`, dense in `C` and relatively open, with relative open-core
propagation along geodesic arcs of `C`; for `d = dim` it is `interior C`. -/
theorem maxSliceLocusOfOrder_spec
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCne : C.Nonempty) (hconv : IsTotallyConvexFinite g C) :
    (maxSliceLocusOfOrder I (r : ℕ∞ω) C).Nonempty ∧
      maxSliceDimOfOrder I (r : ℕ∞ω) C ≤ Module.finrank ℝ E ∧
      IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C)
        (maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      IsTotallyGeodesicFinite g (maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      C ⊆ closure (maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      (∀ x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        C ∩ U ⊆ maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      (∀ (p : TangentBundle I M) (a b : ℝ), (∀ t ∈ Icc a b, (g.geodesicFlow p t).proj ∈ C) →
        ∀ s ∈ Icc a b, (g.geodesicFlow p s).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C →
          ∀ t ∈ Ioo a b, (g.geodesicFlow p t).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      (maxSliceDimOfOrder I (r : ℕ∞ω) C = Module.finrank ℝ E →
        maxSliceLocusOfOrder I (r : ℕ∞ω) C = interior C) := by
  obtain ⟨O, hO, hCO⟩ := exists_isOpen_inter_eq_maxSliceLocusOfOrder g hr hnorm hconv
  refine ⟨maxSliceLocusOfOrder_nonempty hCne, maxSliceDimOfOrder_le C,
    isEmbeddedSliceOfOrder_maxSliceLocusOfOrder g hr hnorm hconv,
    isTotallyGeodesicFinite_maxSliceLocusOfOrder g hr hnorm hconv,
    subset_closure_maxSliceLocusOfOrder g hr hnorm hCne hconv, ?_, ?_,
    maxSliceLocusOfOrder_eq_interior g hr hnorm hconv⟩
  · intro x hx
    refine ⟨O, hO, ?_, hCO.le⟩
    rw [← hCO] at hx
    exact hx.2
  · intro p a b hmaps s hs hsZ
    exact hconv.proj_geodesicFlow_mem_maxSliceLocusOfOrder hr hnorm p hmaps hs hsZ

end DifferentialGeometry.Geometry.FiniteSoul
