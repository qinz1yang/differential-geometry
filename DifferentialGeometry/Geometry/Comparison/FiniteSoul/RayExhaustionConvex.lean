import DifferentialGeometry.Geometry.Comparison.FiniteSoul.BusemannConvexity
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TotallyConvex
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.SquaredDistanceGeodesic
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.HopfRinow
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.ChartMetric

/-!
# The convex exhaustion of a complete finite metric with `sec ≥ 0` (S-BUS, finite part)

For a complete metric `g` of class `C^{r+1}` (`2 ≤ r`) with `sec ≥ 0` whose length distance is the
ambient distance (`hnorm`):

* `convexOn_busemann_geodesicFlow`: every Busemann function is convex along every geodesic (any
  speed; CM-CHAIN's squared-distance convexity and the metric kernel);
* `convexOn_rayExhaustion_geodesicFlow`: so is `f = rayExhaustion o` (the unit-speed hypothesis of
  the frozen interface is dropped; the verbatim form is an `example`);
* `isTotallyConvexFinite_rayExhaustion_sublevel`, `isCompact_rayExhaustion_sublevel` and the frozen
  `isCompact_isTotallyConvexFinite_rayExhaustion_sublevel`: the sublevels `C_t = {f ≤ t}` are compact
  and totally convex. Compactness: escaping points of `C_t` give unit segments from `o`; a limit of
  their initial vectors spans a ray inside `C_t` along which `f` grows without bound.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (busemann rayExhaustion busemann_ray
  busemann_le_rayExhaustion lipschitzWith_rayExhaustion rayExhaustion_self)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- Every Busemann function is convex along every geodesic of a complete finite metric with
`sec ≥ 0` (any speed). -/
theorem convexOn_busemann_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {c : ℝ≥0 → M} (hc : Isometry c) (p : TangentBundle I M) :
    ConvexOn ℝ univ (fun t => busemann c (g.geodesicFlow p t).proj) :=
  convexOn_busemann_comp_of_convexOn_mul_sq_sub_sq hc (a := g.inner p.proj p.snd p.snd)
    fun s => FiniteComparison.convexOn_inner_mul_sq_sub_sq_dist_geodesicFlow_finite g hr hnorm
      hsec p (c s)

/-- **S-BUS.** The convex exhaustion `f = rayExhaustion o` is convex along every geodesic of a
complete finite metric with `sec ≥ 0`. Strengthening of the frozen interface: no unit-speed
hypothesis. -/
theorem convexOn_rayExhaustion_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) (p : TangentBundle I M) :
    ConvexOn ℝ univ (fun t => rayExhaustion o (g.geodesicFlow p t).proj) :=
  convexOn_rayExhaustion_comp o convex_univ fun _ hc _ =>
    convexOn_busemann_geodesicFlow g hr hnorm hsec hc p

/-- The frozen interface form (unit speed), kept verbatim. -/
example
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) (p : TangentBundle I M) (_hp : g.inner p.proj p.snd p.snd = 1) :
    ConvexOn ℝ univ (fun t => rayExhaustion o (g.geodesicFlow p t).proj) :=
  convexOn_rayExhaustion_geodesicFlow g hr hnorm hsec o p

/-- The sublevels of the convex exhaustion are totally convex. -/
theorem isTotallyConvexFinite_rayExhaustion_sublevel
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) (t : ℝ) :
    IsTotallyConvexFinite g {x : M | rayExhaustion o x ≤ t} :=
  isTotallyConvexFinite_sublevel (one_le_two.trans hr)
    (fun p ℓ _ => (convexOn_rayExhaustion_geodesicFlow g hr hnorm hsec o p).subset
      (subset_univ _) (convex_Icc 0 ℓ)) t

/-- The sublevels of the convex exhaustion are compact. -/
theorem isCompact_rayExhaustion_sublevel
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) (t : ℝ) :
    IsCompact {x : M | rayExhaustion o x ≤ t} := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hclosed : ∀ k : ℝ, IsClosed {x : M | rayExhaustion o x ≤ k} := fun k =>
    isClosed_le (lipschitzWith_rayExhaustion o).continuous continuous_const
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hmem : ∀ (P : TangentBundle I M) (τ : ℝ), (P, τ) ∈ g.geodesicFlowDomain := fun P τ => by
    rw [hD]; exact mem_univ _
  have : ProperSpace M := (Bundle.ContMDiffRiemannianMetric.hopfRinow_finite g hr hnorm).1
  -- the case `0 ≤ k`
  have key : ∀ k : ℝ, 0 ≤ k → IsCompact {x : M | rayExhaustion o x ≤ k} := by
    intro k hk
    set C := {x : M | rayExhaustion o x ≤ k} with hC
    have hconv : IsTotallyConvexFinite g C :=
      isTotallyConvexFinite_rayExhaustion_sublevel g hr hnorm hsec o k
    have hoC : o ∈ C := by
      change rayExhaustion o o ≤ k
      rw [rayExhaustion_self]
      exact hk
    by_contra hnc
    have hex : ∀ n : ℕ, ∃ x ∈ C, (n : ℝ) + 1 < dist o x := by
      intro n
      by_contra h
      push Not at h
      apply hnc
      refine (isCompact_closedBall o ((n : ℝ) + 1)).of_isClosed_subset (hclosed k) ?_
      intro x hx
      rw [mem_closedBall, dist_comm]
      exact h x hx
    choose x hx hfar using hex
    have hseg := fun n => Bundle.ContMDiffRiemannianMetric.exists_unit_segment_expMap g hr hnorm
      o (x n)
    choose u hu hiso hend using hseg
    -- points of the segments lie in `C`
    have hsegC : ∀ n, ∀ s ∈ Icc 0 (dist o (x n)),
        g.expMap (⟨o, s • u n⟩ : TangentBundle I M) ∈ C := by
      intro n s hs
      have hflow : ∀ τ : ℝ, g.expMap (⟨o, τ • u n⟩ : TangentBundle I M) =
          (g.geodesicFlow (⟨o, u n⟩ : TangentBundle I M) τ).proj := fun τ =>
        g.expMap_smul_eq_proj_geodesicFlow hr1 o (u n) τ (hmem _ _)
      rw [hflow]
      refine hconv _ (dist o (x n)) dist_nonneg hoC ?_ s hs
      rw [← hflow, hend n]
      exact hx n
    -- a limit of the initial vectors
    have hS := DifferentialGeometry.Geometry.Collapse.isCompact_finite_unitSphere g o
    obtain ⟨u₀, -, φ, hφ, hlim⟩ := hS.tendsto_subseq (x := u) (fun n => hu n)
    have hcontE : Continuous (fun v : E => g.expMap (⟨o, v⟩ : TangentBundle I M)) := by
      have h := (Bundle.ContMDiffRiemannianMetric.contMDiffOn_expMap_fiber g hr1 o).continuousOn
      have hdom : {v : E | (⟨o, v⟩ : TangentBundle I M) ∈ g.expDomain} = univ := by
        ext v
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact hmem _ 1
      rw [hdom] at h
      exact continuousOn_univ.mp h
    set c₀ : ℝ → M := fun s => g.expMap (⟨o, s • u₀⟩ : TangentBundle I M) with hc₀
    have hpt : ∀ s : ℝ, Tendsto (fun n => g.expMap (⟨o, s • u (φ n)⟩ : TangentBundle I M))
        atTop (𝓝 (c₀ s)) := fun s =>
      ((hcontE.comp (continuous_const_smul s)).tendsto u₀).comp hlim
    have hdiv : Tendsto (fun n => dist o (x (φ n))) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
        hφ.tendsto_atTop)
      have := hfar (φ n)
      simp only [Function.comp_apply]
      linarith
    have hev : ∀ s : ℝ, ∀ᶠ n in atTop, s ≤ dist o (x (φ n)) := fun s =>
      hdiv.eventually (eventually_ge_atTop s)
    -- the limit curve is an isometric ray in `C`
    have hc₀C : ∀ s, 0 ≤ s → c₀ s ∈ C := fun s hs =>
      (hclosed k).mem_of_tendsto (hpt s) ((hev s).mono fun n hn => hsegC (φ n) s ⟨hs, hn⟩)
    have hc₀iso : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (c₀ s) (c₀ t) = |s - t| := by
      intro s hs t ht
      refine tendsto_nhds_unique ((hpt s).dist (hpt t)) ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev s, hev t] with n hns hnt
      exact (hiso (φ n) s ⟨hs, hns⟩ t ⟨ht, hnt⟩).symm
    set c : ℝ≥0 → M := fun s => c₀ s with hcdef
    have hcI : Isometry c := by
      refine Isometry.of_dist_eq fun s t => ?_
      rw [hcdef, hc₀iso s s.2 t t.2, NNReal.dist_eq]
    have hc0 : c 0 = o := by
      change g.expMap (⟨o, ((0 : ℝ≥0) : ℝ) • u₀⟩ : TangentBundle I M) = o
      rw [NNReal.coe_zero, zero_smul]
      exact g.expMap_zero hr1 o
    set T : ℝ≥0 := ⟨k + 1, by linarith⟩ with hT
    have hbound := (busemann_le_rayExhaustion hcI hc0 (c T)).trans (hc₀C T T.2)
    rw [busemann_ray hcI T] at hbound
    change k + 1 ≤ k at hbound
    linarith
  by_cases ht : 0 ≤ t
  · exact key t ht
  · exact (key 0 le_rfl).of_isClosed_subset (hclosed t) fun x hx =>
      (show rayExhaustion o x ≤ t from hx).trans (le_of_not_ge ht)

/-- **S-BUS (frozen interface).** The sublevels of the convex exhaustion are compact and totally
convex (the sets `C_t` of LFR21). -/
theorem isCompact_isTotallyConvexFinite_rayExhaustion_sublevel
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) (t : ℝ) :
    IsCompact {x : M | rayExhaustion o x ≤ t} ∧
      IsTotallyConvexFinite g {x : M | rayExhaustion o x ≤ t} :=
  ⟨isCompact_rayExhaustion_sublevel g hr hnorm hsec o t,
    isTotallyConvexFinite_rayExhaustion_sublevel g hr hnorm hsec o t⟩

end DifferentialGeometry.Geometry.FiniteSoul
