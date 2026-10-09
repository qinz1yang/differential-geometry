import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShapeLocal
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ExhaustionConsumers

/-!
# S-SHAPE2: compact totally convex sets with empty interior in a surface

`totallyConvex_point_or_arc_or_closedGeodesic_dim_two` (frozen interface of the finite soul
package, `build-logs/scratch/D-CMS/FiniteSoulInterfaces.lean`): a compact, nonempty, totally
convex set with empty interior in a complete surface with a metric of class `C^{r+1}`, `r ≥ 2`,
is a point, an injective unit geodesic arc, or a closed unit geodesic `Φ_ℓ p = p`, injective on
`[0, ℓ)`. No curvature hypothesis is used.

Route (review of the finite soul design, §5; no classification of compact 1-manifolds):
* local collinearity (`ShapeLocal.lean`): near every point of `C` the chart preimage of `C` lies on
  a line;
* along a unit geodesic `γ` starting in `C`, the set `A = {t | γ [0, t] ⊆ C}` is a closed interval;
  near each `γ t`, `t ∈ A`, the set `C` is the geodesic itself (interval filling); hence
  `C = γ '' A` by connectedness;
* a re-encounter `γ t₁ = γ t₂` (`t₁ ≠ t₂` in `A`) has equal velocities: opposite velocities would
  give a zero velocity at the midpoint (`geodesicFlow_ne_neg_of_unit`, reversal of the flow), so it
  is a phase-space period;
* an unbounded `A` forces a re-encounter (compactness), a bounded one is an injective arc; with a
  period, the least return time `ℓ ≥ ρ` is a period and `γ` is injective on `[0, ℓ)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology

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
/-- A unit vector is nonzero. -/
theorem ne_zero_of_inner_self_eq_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {z : M} {ξ : E} (h : g.inner z ξ ξ = 1) : ξ ≠ 0 := by
  intro h0
  have h1 := inner_smul_smul_self_finite g z 0 ξ
  rw [zero_smul, ← h0, h] at h1
  norm_num at h1

omit [NeZero (Module.finrank ℝ E)] in
/-- **No opposite-direction re-encounter.** Along a unit geodesic of a complete finite metric,
the state at time `t₂` is never the state at time `t₁` with reversed velocity: the midpoint
would have zero velocity. -/
theorem geodesicFlow_ne_neg_of_unit
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} (hp : g.inner p.proj p.snd p.snd = 1) (t₁ t₂ : ℝ) :
    g.geodesicFlow p t₂ ≠
      ⟨(g.geodesicFlow p t₁).proj, (-1 : ℝ) • (g.geodesicFlow p t₁).snd⟩ := by
  intro heq
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hmem : ∀ (Q : TangentBundle I M) (τ : ℝ), (Q, τ) ∈ g.geodesicFlowDomain := fun Q τ => by
    rw [hD]; exact mem_univ _
  have hadd : ∀ (Q : TangentBundle I M) (s t : ℝ),
      g.geodesicFlow (g.geodesicFlow Q s) t = g.geodesicFlow Q (s + t) := fun Q s t =>
    (g.geodesicFlow_add hr1 (hmem Q s) (hmem Q (s + t))).symm
  set h : ℝ := (t₂ - t₁) / 2 with hhdef
  set P : TangentBundle I M := g.geodesicFlow p (t₁ + h) with hPdef
  have h2 : g.geodesicFlow p t₂ = g.geodesicFlow P h := by
    rw [hPdef, hadd]; congr 1; rw [hhdef]; ring
  have h1 : g.geodesicFlow p t₁ = g.geodesicFlow P (-h) := by
    rw [hPdef, hadd]; congr 1; ring
  have hrev := g.geodesicFlow_smul_eq hr1 P (-1) h (hmem P _)
  rw [neg_one_mul, ← h1, ← heq, h2] at hrev
  have hback : ∀ Q : TangentBundle I M, g.geodesicFlow (g.geodesicFlow Q h) (-h) = Q := fun Q => by
    rw [hadd, add_neg_cancel, g.geodesicFlow_zero hr1]
  have hPP : (⟨P.proj, (-1 : ℝ) • P.snd⟩ : TangentBundle I M) = P := by
    rw [← hback ⟨P.proj, (-1 : ℝ) • P.snd⟩, hrev, hback P]
  set ξ : E := P.snd with hξdef
  have hsnd : (-1 : ℝ) • ξ = ξ := congrArg (fun Q : TangentBundle I M => (Q.snd : E)) hPP
  have hzero : ξ = 0 := by
    have h3 : (2 : ℝ) • ξ = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hsnd]
      rw [neg_one_smul, neg_add_cancel]
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
  have hunit : g.inner P.proj ξ ξ = 1 :=
    (g.inner_geodesicFlow_eq hr1 p (t₁ + h) (hmem p _)).trans hp
  exact ne_zero_of_inner_self_eq_one g hunit hzero

/-- **S-SHAPE2.** A compact, nonempty, totally convex set with empty interior in a complete
surface is a point, an injective unit geodesic arc, or a closed unit geodesic of least period
`ℓ` (injective on `[0, ℓ)`). Verbatim frozen interface; `[SigmaCompactSpace M]` of the interface
file is not needed. -/
theorem totallyConvex_point_or_arc_or_closedGeodesic_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCc : IsCompact C) (hCne : C.Nonempty)
    (hconv : IsTotallyConvexFinite g C) (hint : interior C = ∅) :
    (∃ x, C = {x}) ∨
      (∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
        InjOn (fun t => (g.geodesicFlow p t).proj) (Icc 0 ℓ) ∧
        C = (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ) ∨
      (∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
        g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
        C = range (fun t => (g.geodesicFlow p t).proj)) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hmem : ∀ (Q : TangentBundle I M) (τ : ℝ), (Q, τ) ∈ g.geodesicFlowDomain := fun Q τ => by
    rw [hD]; exact mem_univ _
  have hflow : ∀ (y : M) (ζ : E) (τ : ℝ), g.expMap (⟨y, τ • ζ⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, ζ⟩ : TangentBundle I M) τ).proj := fun y ζ τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 y ζ τ (hmem _ τ)
  have hadd : ∀ (Q : TangentBundle I M) (s t : ℝ),
      g.geodesicFlow (g.geodesicFlow Q s) t = g.geodesicFlow Q (s + t) := fun Q s t =>
    (g.geodesicFlow_add hr1 (hmem Q s) (hmem Q (s + t))).symm
  have hCcl : IsClosed C := hCc.isClosed
  /- local data: one radius `ρ` on `C` -/
  obtain ⟨ρ, hρ, hch⟩ :=
    exists_radius_not_linearIndependent_dim_two g hr hnorm hdim hCc hconv hint
  have hloc : ∀ z ∈ C, ∀ v w : E, g.inner z v v < ρ ^ 2 → g.inner z w w < ρ ^ 2 →
      g.expMap (⟨z, v⟩ : TangentBundle I M) ∈ C → g.expMap (⟨z, w⟩ : TangentBundle I M) ∈ C →
      ¬ LinearIndependent ℝ ![v, w] := by
    intro z hz v w hv hw hvC hwC
    obtain ⟨e, hsrc, -, hexp, -, hlin⟩ := hch z hz
    have hv' : v ∈ e.source := by rw [hsrc]; exact hv
    have hw' : w ∈ e.source := by rw [hsrc]; exact hw
    exact hlin v hv' w hw' (by rw [(hexp v hv').2]; exact hvC) (by rw [(hexp w hw').2]; exact hwC)
  have hcov : ∀ z ∈ C, ∀ y : M, dist z y < ρ → ∃ v : E, g.inner z v v < ρ ^ 2 ∧
      g.expMap (⟨z, v⟩ : TangentBundle I M) = y := by
    intro z hz y hy
    obtain ⟨e, hsrc, htgt, hexp, -, -⟩ := hch z hz
    have hyt : y ∈ e.target := by rw [htgt, mem_ball, dist_comm]; exact hy
    have hvs : e.symm y ∈ e.source := e.map_target hyt
    refine ⟨e.symm y, ?_, ?_⟩
    · have := hvs; rw [hsrc] at this; exact this
    · rw [← (hexp _ hvs).2]; exact e.right_inv hyt
  have hdz : ∀ z ∈ C, ∀ v : E, g.inner z v v < ρ ^ 2 →
      dist z (g.expMap (⟨z, v⟩ : TangentBundle I M)) = Real.sqrt (g.inner z v v) := by
    intro z hz v hv
    obtain ⟨e, hsrc, -, hexp, hdist, -⟩ := hch z hz
    have hv' : v ∈ e.source := by rw [hsrc]; exact hv
    rw [← (hexp v hv').2]; exact hdist v hv'
  /- the point case -/
  by_cases hsing : ∃ x, C = {x}
  · exact Or.inl hsing
  right
  obtain ⟨x, hx⟩ := hCne
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ C, y ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hsing ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨hx, hcon⟩⟩
  /- a unit geodesic starting in `C` -/
  obtain ⟨u, hu, -, -, hmemC⟩ := hconv.exists_unit_segment_mem hr hnorm hx hy
  set a₀ : ℝ := dist x y with ha₀def
  have ha₀ : 0 < a₀ := dist_pos.2 (Ne.symm hyx)
  set p₀ : TangentBundle I M := ⟨x, u⟩ with hp₀def
  have hp₀ : g.inner p₀.proj p₀.snd p₀.snd = 1 := hu
  set γ : ℝ → M := fun t => (g.geodesicFlow p₀ t).proj with hγdef
  set V : ℝ → E := fun t => (g.geodesicFlow p₀ t).snd with hVdef
  have hspeed : ∀ t, g.inner (γ t) (V t) (V t) = 1 := fun t =>
    (g.inner_geodesicFlow_eq hr1 p₀ t (hmem p₀ t)).trans hp₀
  have hγlip : ∀ s t, dist (γ s) (γ t) ≤ |t - s| := by
    intro s t
    have h := g.dist_proj_geodesicFlow_le hr1 hnorm (p := p₀) (s := s) (t := t)
      (fun τ _ => hmem p₀ τ)
    rwa [hp₀, Real.sqrt_one, one_mul] at h
  have hγcont : Continuous γ := by
    refine Metric.continuous_iff.2 fun b ε hε => ⟨ε, hε, fun a hab => ?_⟩
    refine (hγlip a b).trans_lt ?_
    rw [abs_sub_comm, ← Real.dist_eq]; exact hab
  have hγ0 : γ 0 = x := by
    change (g.geodesicFlow p₀ 0).proj = x
    rw [g.geodesicFlow_zero hr1]
  have hγC0 : ∀ s ∈ Icc 0 a₀, γ s ∈ C := by
    intro s hs
    have h := hmemC s hs
    rw [hflow] at h
    exact h
  /- the time set `A = {t | γ [0, t] ⊆ C}` -/
  set A : Set ℝ := {t | ∀ μ ∈ Icc (0 : ℝ) 1, γ (μ * t) ∈ C} with hAdef
  have hAiff : ∀ t, t ∈ A ↔ ∀ s ∈ uIcc 0 t, γ s ∈ C := by
    intro t
    constructor
    · intro h s hs
      rcases eq_or_ne t 0 with rfl | ht
      · rw [uIcc_self, mem_singleton_iff] at hs
        have := h 0 ⟨le_rfl, zero_le_one⟩
        rwa [zero_mul, ← hs] at this
      · have hμ : s / t ∈ Icc (0 : ℝ) 1 := by
          rcases lt_or_gt_of_ne ht with htn | htp
          · rw [uIcc_of_ge htn.le] at hs
            exact ⟨div_nonneg_of_nonpos hs.2 htn.le, (div_le_one_of_neg htn).2 hs.1⟩
          · rw [uIcc_of_le htp.le] at hs
            exact ⟨div_nonneg hs.1 htp.le, (div_le_one htp).2 hs.2⟩
        have := h (s / t) hμ
        rwa [div_mul_cancel₀ s ht] at this
    · intro h μ hμ
      apply h
      rcases le_total 0 t with ht | ht
      · rw [uIcc_of_le ht]
        exact ⟨mul_nonneg hμ.1 ht, by nlinarith [hμ.1, hμ.2]⟩
      · rw [uIcc_of_ge ht]
        exact ⟨by nlinarith [hμ.1, hμ.2], mul_nonpos_of_nonneg_of_nonpos hμ.1 ht⟩
  have hAγ : ∀ t ∈ A, γ t ∈ C := fun t ht => (hAiff t).1 ht t right_mem_uIcc
  have hA0 : ∀ s ∈ Icc 0 a₀, s ∈ A := by
    intro s hs
    refine (hAiff s).2 fun s' hs' => hγC0 s' ?_
    rw [uIcc_of_le hs.1] at hs'
    exact ⟨hs'.1, hs'.2.trans hs.2⟩
  have hAconn : ∀ t ∈ A, ∀ t' ∈ uIcc 0 t, t' ∈ A := by
    intro t ht t' ht'
    exact (hAiff t').2 fun s hs => (hAiff t).1 ht s (uIcc_subset_uIcc left_mem_uIcc ht' hs)
  have hAext : ∀ t ∈ A, ∀ t', (∀ s ∈ uIcc t t', γ s ∈ C) → t' ∈ A := by
    intro t ht t' h
    refine (hAiff t').2 fun s hs => ?_
    rcases uIcc_subset_uIcc_union_uIcc (b := t) hs with h1 | h1
    · exact (hAiff t).1 ht s h1
    · exact h s h1
  have hAord : ∀ a ∈ A, ∀ b ∈ A, ∀ τ ∈ Icc a b, τ ∈ A := by
    intro a ha b hb τ hτ
    rcases le_total 0 τ with h0 | h0
    · exact hAconn b hb τ (by rw [uIcc_of_le (h0.trans hτ.2)]; exact ⟨h0, hτ.2⟩)
    · exact hAconn a ha τ (by rw [uIcc_of_ge (hτ.1.trans h0)]; exact ⟨hτ.1, h0⟩)
  have hAcl : IsClosed A := by
    have hAeq : A = ⋂ μ ∈ Icc (0 : ℝ) 1, (fun t => γ (μ * t)) ⁻¹' C := by
      ext t; simp [A]
    rw [hAeq]
    exact isClosed_biInter fun μ _ =>
      hCcl.preimage (hγcont.comp (continuous_const.mul continuous_id))
  have hAnb : ∀ t ∈ A, ∃ s : ℝ, s ≠ 0 ∧ s ^ 2 < ρ ^ 2 ∧ t + s ∈ A := by
    intro t ht
    rcases le_or_gt t 0 with ht0 | ht0
    · set δ : ℝ := min (ρ / 2) a₀ with hδdef
      have hδ : 0 < δ := lt_min (by positivity) ha₀
      have hδρ : δ ≤ ρ / 2 := min_le_left _ _
      have hδa : δ ≤ a₀ := min_le_right _ _
      refine ⟨δ, hδ.ne', by nlinarith, ?_⟩
      rcases le_or_gt (t + δ) 0 with h1 | h1
      · exact hAconn t ht _ (by rw [uIcc_of_ge ht0]; exact ⟨by linarith, h1⟩)
      · exact hA0 _ ⟨h1.le, by linarith⟩
    · have hs1 : 0 < min (ρ / 2) t := lt_min (by positivity) ht0
      have hs2 : min (ρ / 2) t ≤ ρ / 2 := min_le_left _ _
      have hs3 : min (ρ / 2) t ≤ t := min_le_right _ _
      refine ⟨-min (ρ / 2) t, neg_ne_zero.2 hs1.ne', by rw [neg_sq]; nlinarith, ?_⟩
      exact hAconn t ht _ (by rw [uIcc_of_le ht0.le]; exact ⟨by linarith, by linarith⟩)
  /- velocity lemma: at `t ∈ A`, chart vectors with image in `C` are multiples of `γ' t` -/
  have hvel : ∀ t ∈ A, ∀ v : E, g.inner (γ t) v v < ρ ^ 2 →
      g.expMap (⟨γ t, v⟩ : TangentBundle I M) ∈ C →
      ∃ c : ℝ, v = c • V t := by
    intro t ht v hv hvC
    set ξ : E := V t with hξdef
    obtain ⟨s, hs0, hsρ, hsA⟩ := hAnb t ht
    have hξ1 : g.inner (γ t) ξ ξ = 1 := hspeed t
    have hξ0 : ξ ≠ 0 := ne_zero_of_inner_self_eq_one g hξ1
    have hsξC : g.expMap (⟨γ t, s • ξ⟩ : TangentBundle I M) ∈ C := by
      rw [hflow]
      change (g.geodesicFlow (g.geodesicFlow p₀ t) s).proj ∈ C
      rw [hadd]
      exact hAγ _ hsA
    have hsξρ : g.inner (γ t) (s • ξ) (s • ξ) < ρ ^ 2 := by
      rw [inner_smul_smul_self_finite, hξ1, mul_one]; exact hsρ
    have hdep := hloc (γ t) (hAγ t ht) (s • ξ) v hsξρ hv hsξC hvC
    rw [LinearIndependent.pair_iff' (smul_ne_zero hs0 hξ0)] at hdep
    push Not at hdep
    obtain ⟨a, ha⟩ := hdep
    exact ⟨a * s, by rw [← ha, smul_smul]⟩
  /- interval filling -/
  have hIF : ∀ t ∈ A, ∀ y ∈ C, dist (γ t) y < ρ →
      ∃ c : ℝ, c ^ 2 < ρ ^ 2 ∧ t + c ∈ A ∧ γ (t + c) = y := by
    intro t ht y hy hdist
    obtain ⟨v, hvρ, hvy⟩ := hcov (γ t) (hAγ t ht) y hdist
    have hvC : g.expMap (⟨γ t, v⟩ : TangentBundle I M) ∈ C := by rw [hvy]; exact hy
    obtain ⟨c, hc⟩ := hvel t ht v hvρ hvC
    set ξ : E := V t with hξdef
    have hξ1 : g.inner (γ t) ξ ξ = 1 := hspeed t
    have hexpc : ∀ τ : ℝ, g.expMap (⟨γ t, τ • ξ⟩ : TangentBundle I M) = γ (t + τ) := by
      intro τ
      rw [hflow]
      change (g.geodesicFlow (g.geodesicFlow p₀ t) τ).proj = (g.geodesicFlow p₀ (t + τ)).proj
      rw [hadd]
    have hc2 : c ^ 2 < ρ ^ 2 := by
      rw [hc, inner_smul_smul_self_finite, hξ1, mul_one] at hvρ; exact hvρ
    refine ⟨c, hc2, ?_, ?_⟩
    · refine hAext t ht (t + c) fun s hs => ?_
      have harc := hconv.expMap_mem hr hnorm zero_le_one (hAγ t ht) (u := v)
        (by rw [one_smul]; exact hvC)
      rcases eq_or_ne c 0 with hc0 | hc0
      · rw [hc0, add_zero, uIcc_self, mem_singleton_iff] at hs
        rw [hs]; exact hAγ t ht
      · have hμ : (s - t) / c ∈ Icc (0 : ℝ) 1 := by
          rcases lt_or_gt_of_ne hc0 with hcn | hcp
          · rw [uIcc_of_ge (by linarith)] at hs
            exact ⟨div_nonneg_of_nonpos (by linarith [hs.2]) hcn.le,
              (div_le_one_of_neg hcn).2 (by linarith [hs.1])⟩
          · rw [uIcc_of_le (by linarith)] at hs
            exact ⟨div_nonneg (by linarith [hs.1]) hcp.le,
              (div_le_one hcp).2 (by linarith [hs.2])⟩
        have h := harc _ hμ
        rw [hc, smul_smul, hexpc, div_mul_cancel₀ _ hc0, add_sub_cancel] at h
        exact h
    · rw [← hexpc, ← hc]; exact hvy
  /- connectedness: `C = γ '' A` -/
  have hCsub : C ⊆ γ '' A := by
    set O : Set M := ⋃ t ∈ A, ball (γ t) (ρ / 2) with hOdef
    have hOopen : IsOpen O := isOpen_biUnion fun t _ => isOpen_ball
    have hpre : IsPreconnected C := hconv.isPreconnected_of_finite hr hnorm
    have hCO : C ⊆ O := by
      refine hpre.subset_of_closure_inter_subset hOopen ⟨x, hx, ?_⟩ ?_
      · exact mem_biUnion (hA0 0 ⟨le_rfl, ha₀.le⟩)
          (by rw [mem_ball, hγ0, dist_self]; positivity)
      · rintro z ⟨hzcl, hzC⟩
        obtain ⟨b, hbO, hzb⟩ := Metric.mem_closure_iff.1 hzcl (ρ / 2) (by positivity)
        obtain ⟨t, ht, hbt⟩ := mem_iUnion₂.1 hbO
        rw [mem_ball] at hbt
        have hd : dist (γ t) z < ρ := by
          have h3 := dist_triangle (γ t) b z
          rw [dist_comm (γ t) b, dist_comm b z] at h3
          linarith
        obtain ⟨c, -, hcA, hcz⟩ := hIF t ht z hzC hd
        exact mem_biUnion hcA (by rw [mem_ball, hcz, dist_self]; positivity)
    intro z hz
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.1 (hCO hz)
    rw [mem_ball] at hzt
    obtain ⟨c, -, hcA, hcz⟩ := hIF t ht z hz (by rw [dist_comm]; linarith)
    exact ⟨t + c, hcA, hcz⟩
  have hCeq : C = γ '' A := hCsub.antisymm (by rintro _ ⟨t, ht, rfl⟩; exact hAγ t ht)
  /- re-encounters are phase-space periods -/
  have hmid := geodesicFlow_ne_neg_of_unit g hr hnorm hp₀
  have hRE : ∀ t₁ ∈ A, ∀ t₂ ∈ A, γ t₁ = γ t₂ →
      g.geodesicFlow p₀ t₁ = g.geodesicFlow p₀ t₂ := by
    intro t₁ ht₁ t₂ ht₂ heq
    set P₁ := g.geodesicFlow p₀ t₁ with hP₁
    set P₂ := g.geodesicFlow p₀ t₂ with hP₂
    set ξ₁ : E := P₁.snd with hξ₁def
    set ξ₂ : E := P₂.snd with hξ₂def
    have hproj : P₂.proj = P₁.proj := heq.symm
    obtain ⟨s, hs0, hsρ, hsA⟩ := hAnb t₂ ht₂
    have hξ₂ : g.inner P₁.proj ξ₂ ξ₂ = 1 := by rw [← hproj]; exact hspeed t₂
    have hξ₁ : g.inner P₁.proj ξ₁ ξ₁ = 1 := hspeed t₁
    have hsC : g.expMap (⟨P₁.proj, s • ξ₂⟩ : TangentBundle I M) ∈ C := by
      rw [← hproj, hflow]
      change (g.geodesicFlow (g.geodesicFlow p₀ t₂) s).proj ∈ C
      rw [hadd]; exact hAγ _ hsA
    have hsρ' : g.inner P₁.proj (s • ξ₂) (s • ξ₂) < ρ ^ 2 := by
      rw [inner_smul_smul_self_finite, hξ₂, mul_one]; exact hsρ
    obtain ⟨c, hc⟩ := hvel t₁ ht₁ (s • ξ₂) hsρ' hsC
    change s • ξ₂ = c • ξ₁ at hc
    have hc2 : s ^ 2 = c ^ 2 := by
      have h1 := inner_smul_smul_self_finite g P₁.proj s ξ₂
      rw [hc, inner_smul_smul_self_finite, hξ₁, hξ₂] at h1
      linarith
    have hcs : c = s ∨ c = -s := by
      have h3 : (c - s) * (c + s) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.1 h3 with h | h
      · left; linarith
      · right; linarith
    have h2 : P₂ = (⟨P₁.proj, ξ₂⟩ : TangentBundle I M) := by rw [← hproj]
    rcases hcs with rfl | rfl
    · have hξ : ξ₂ = ξ₁ := smul_right_injective E hs0 hc
      exact (h2.trans (congrArg (fun w : E => (⟨P₁.proj, w⟩ : TangentBundle I M)) hξ)).symm
    · exfalso
      have hξ : ξ₂ = (-1 : ℝ) • ξ₁ := by
        apply smul_right_injective E hs0
        change s • ξ₂ = s • ((-1 : ℝ) • ξ₁)
        rw [hc, smul_smul, mul_neg_one]
      apply hmid t₁ t₂
      exact h2.trans (congrArg (fun w : E => (⟨P₁.proj, w⟩ : TangentBundle I M)) hξ)
  by_cases hrep : ∃ t₁ ∈ A, ∃ t₂ ∈ A, t₁ ≠ t₂ ∧ γ t₁ = γ t₂
  · /- the closed geodesic -/
    right
    obtain ⟨a, ha, b, hb, hab, hγab⟩ : ∃ a ∈ A, ∃ b ∈ A, a < b ∧ γ a = γ b := by
      obtain ⟨t₁, ht₁, t₂, ht₂, hne, heq⟩ := hrep
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨t₁, ht₁, t₂, ht₂, h, heq⟩
      · exact ⟨t₂, ht₂, t₁, ht₁, h, heq.symm⟩
    set T : ℝ := b - a with hTdef
    have hT : 0 < T := sub_pos.2 hab
    have hPab := hRE a ha b hb hγab
    have hper : ∀ t, g.geodesicFlow p₀ (t + T) = g.geodesicFlow p₀ t := by
      intro t
      have h1 : g.geodesicFlow p₀ (t + T) = g.geodesicFlow (g.geodesicFlow p₀ b) (t - a) := by
        rw [hadd]; congr 1; rw [hTdef]; ring
      rw [h1, ← hPab, hadd]; congr 1; ring
    have hperZ : ∀ k : ℤ, ∀ t, g.geodesicFlow p₀ (t + k * T) = g.geodesicFlow p₀ t := by
      intro k
      refine Int.induction_on k ?_ ?_ ?_
      · intro t; simp
      · intro i ih t
        have h3 : t + (((i : ℤ) + 1 : ℤ) : ℝ) * T = (t + ((i : ℤ) : ℝ) * T) + T := by
          push_cast; ring
        rw [h3, hper, ih]
      · intro i ih t
        have h3 : t + ((-(i : ℤ) - 1 : ℤ) : ℝ) * T + T = t + ((-(i : ℤ) : ℤ) : ℝ) * T := by
          push_cast; ring
        rw [← hper (t + ((-(i : ℤ) - 1 : ℤ) : ℝ) * T), h3, ih]
    have hall : ∀ s, γ s ∈ C := by
      intro s
      set k : ℤ := ⌊(s - a) / T⌋ with hkdef
      set τ : ℝ := s - k * T with hτdef
      have h1 : (k : ℝ) ≤ (s - a) / T := Int.floor_le _
      have h2 : (s - a) / T < k + 1 := Int.lt_floor_add_one _
      rw [le_div_iff₀ hT] at h1
      rw [div_lt_iff₀ hT] at h2
      have hτa : a ≤ τ := by rw [hτdef]; linarith
      have hτb : τ ≤ b := by rw [hτdef]; nlinarith
      have hτs : τ + k * T = s := by rw [hτdef]; ring
      have hγs : γ s = γ τ := by
        change (g.geodesicFlow p₀ s).proj = (g.geodesicFlow p₀ τ).proj
        rw [← hperZ k τ, hτs]
      rw [hγs]; exact hAγ τ (hAord a ha b hb τ ⟨hτa, hτb⟩)
    have hAall : ∀ t, t ∈ A := fun t => (hAiff t).2 fun s _ => hall s
    have hrange : C = range γ := by
      apply Subset.antisymm
      · rw [hCeq]; exact image_subset_range _ _
      · rintro _ ⟨s, rfl⟩; exact hall s
    -- small return times are excluded by the normal chart at `x`
    have hlow : ∀ τ : ℝ, 0 < τ → τ < ρ → γ τ ≠ γ 0 := by
      intro τ hτ0 hτρ heq
      have hτ2 : g.inner x (τ • u) (τ • u) < ρ ^ 2 := by
        rw [inner_smul_smul_self_finite, hu, mul_one]; nlinarith
      have h := hdz x hx (τ • u) hτ2
      rw [inner_smul_smul_self_finite, hu, mul_one, Real.sqrt_sq hτ0.le, hflow] at h
      have h0 : dist x (γ τ) = 0 := by rw [heq, hγ0, dist_self]
      have h1 : dist x (γ τ) = τ := h
      linarith
    set S : Set ℝ := {τ | ρ ≤ τ ∧ γ τ = γ 0} with hSdef
    have hScl : IsClosed S :=
      (isClosed_le continuous_const continuous_id).inter (isClosed_eq hγcont continuous_const)
    have hγT : γ T = γ 0 := by
      change (g.geodesicFlow p₀ T).proj = (g.geodesicFlow p₀ 0).proj
      rw [← hper 0, zero_add]
    have hTρ : ρ ≤ T := by
      by_contra hlt
      push Not at hlt
      exact hlow T hT hlt hγT
    have hSne : S.Nonempty := ⟨T, hTρ, hγT⟩
    have hSbdd : BddBelow S := ⟨ρ, fun τ hτ => hτ.1⟩
    set ℓ : ℝ := sInf S with hℓdef
    have hℓS : ℓ ∈ S := hScl.csInf_mem hSne hSbdd
    have hℓpos : 0 < ℓ := hρ.trans_le hℓS.1
    have hΦℓ : g.geodesicFlow p₀ ℓ = p₀ := by
      rw [hRE ℓ (hAall ℓ) 0 (hAall 0) hℓS.2, g.geodesicFlow_zero hr1]
    refine ⟨p₀, ℓ, hℓpos, hp₀, hΦℓ, ?_, hrange⟩
    have hno : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ < ℓ → γ t₁ = γ t₂ → False := by
      intro t₁ t₂ h0 h12 h2ℓ heq
      have hP := hRE t₁ (hAall t₁) t₂ (hAall t₂) heq
      have hT'0 : 0 < t₂ - t₁ := sub_pos.2 h12
      have hγT' : γ (t₂ - t₁) = γ 0 := by
        change (g.geodesicFlow p₀ (t₂ - t₁)).proj = (g.geodesicFlow p₀ 0).proj
        have h1 : g.geodesicFlow p₀ (t₂ - t₁) = g.geodesicFlow (g.geodesicFlow p₀ t₂) (-t₁) := by
          rw [hadd, sub_eq_add_neg]
        rw [h1, ← hP, hadd, add_neg_cancel]
      rcases lt_or_ge (t₂ - t₁) ρ with hρ' | hρ'
      · exact hlow _ hT'0 hρ' hγT'
      · have h3 := csInf_le hSbdd (show t₂ - t₁ ∈ S from ⟨hρ', hγT'⟩)
        rw [← hℓdef] at h3
        linarith
    intro t₁ ht₁ t₂ ht₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hno t₁ t₂ ht₁.1 h ht₂.2 heq
    · exact hno t₂ t₁ ht₂.1 h ht₁.2 heq.symm
  · /- the injective arc -/
    left
    push Not at hrep
    have hinjA : InjOn γ A := by
      intro t₁ ht₁ t₂ ht₂ heq
      by_contra hne
      exact hrep t₁ ht₁ t₂ ht₂ hne heq
    have hnoray : ∀ σ : ℝ, σ ^ 2 = 1 → ¬ ∀ n : ℕ, σ * (2 * ρ * n) ∈ A := by
      intro σ hσ hallA
      obtain ⟨z, -, φ, hφ, hlim⟩ := hCc.tendsto_subseq
        (x := fun n : ℕ => γ (σ * (2 * ρ * n))) (fun n => hAγ _ (hallA n))
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ρ / 2) (by positivity)
      have h1 : dist (γ (σ * (2 * ρ * (φ N : ℝ)))) z < ρ / 2 := hN N le_rfl
      have h2 : dist (γ (σ * (2 * ρ * (φ (N + 1) : ℝ)))) z < ρ / 2 := hN (N + 1) (Nat.le_succ N)
      have hd : dist (γ (σ * (2 * ρ * (φ N : ℝ)))) (γ (σ * (2 * ρ * (φ (N + 1) : ℝ)))) < ρ := by
        have h3 := dist_triangle (γ (σ * (2 * ρ * (φ N : ℝ)))) z
          (γ (σ * (2 * ρ * (φ (N + 1) : ℝ))))
        rw [dist_comm z] at h3
        linarith
      obtain ⟨c, hc2, hcA, hcγ⟩ := hIF _ (hallA (φ N)) _ (hAγ _ (hallA (φ (N + 1)))) hd
      have heqt := hinjA hcA (hallA (φ (N + 1))) hcγ
      have hφlt : (φ N : ℝ) + 1 ≤ φ (N + 1) := by exact_mod_cast hφ (Nat.lt_succ_self N)
      have hc : c = σ * (2 * ρ * ((φ (N + 1) : ℝ) - φ N)) := by linarith
      have hΔ : 1 ≤ (φ (N + 1) : ℝ) - φ N := by linarith
      have hcsq : c ^ 2 = 4 * ρ ^ 2 * ((φ (N + 1) : ℝ) - φ N) ^ 2 := by
        rw [hc]
        have h4 : (σ * (2 * ρ * ((φ (N + 1) : ℝ) - φ N))) ^ 2 =
            σ ^ 2 * (4 * ρ ^ 2 * ((φ (N + 1) : ℝ) - φ N) ^ 2) := by ring
        rw [h4, hσ, one_mul]
      have hΔ2 : 1 ≤ ((φ (N + 1) : ℝ) - φ N) ^ 2 := by nlinarith
      have hρ2 : 0 < ρ ^ 2 := by positivity
      nlinarith
    have hbddA : BddAbove A := by
      by_contra hnb
      apply hnoray 1 (by norm_num)
      intro n
      rw [not_bddAbove_iff] at hnb
      obtain ⟨t, ht, hlt⟩ := hnb (1 * (2 * ρ * n))
      have h0 : 0 ≤ 1 * (2 * ρ * (n : ℝ)) := by positivity
      exact hAconn t ht _ (by rw [uIcc_of_le (by linarith)]; exact ⟨h0, hlt.le⟩)
    have hbddB : BddBelow A := by
      by_contra hnb
      apply hnoray (-1) (by norm_num)
      intro n
      rw [not_bddBelow_iff] at hnb
      obtain ⟨t, ht, hlt⟩ := hnb (-1 * (2 * ρ * n))
      have h0 : 0 ≤ 2 * ρ * (n : ℝ) := by positivity
      exact hAconn t ht _ (by rw [uIcc_of_ge (by linarith)]; exact ⟨hlt.le, by linarith⟩)
    have hAne : A.Nonempty := ⟨0, hA0 0 ⟨le_rfl, ha₀.le⟩⟩
    set α : ℝ := sInf A with hαdef
    set β : ℝ := sSup A with hβdef
    have hαA : α ∈ A := hAcl.csInf_mem hAne hbddB
    have hβA : β ∈ A := hAcl.csSup_mem hAne hbddA
    have hAIcc : A = Icc α β := by
      ext t
      constructor
      · intro ht; exact ⟨csInf_le hbddB ht, le_csSup hbddA ht⟩
      · intro ht; exact hAord α hαA β hβA t ht
    have hα0 : α ≤ 0 := csInf_le hbddB (hA0 0 ⟨le_rfl, ha₀.le⟩)
    have hβa : a₀ ≤ β := le_csSup hbddA (hA0 a₀ ⟨ha₀.le, le_rfl⟩)
    set p : TangentBundle I M := g.geodesicFlow p₀ α with hpdef
    have hpt : ∀ t, (g.geodesicFlow p t).proj = γ (α + t) := fun t => by
      change (g.geodesicFlow (g.geodesicFlow p₀ α) t).proj = (g.geodesicFlow p₀ (α + t)).proj
      rw [hadd]
    refine ⟨p, β - α, by linarith, hspeed α, ?_, ?_⟩
    · intro t₁ ht₁ t₂ ht₂ heq
      have heq' : γ (α + t₁) = γ (α + t₂) := by rw [← hpt, ← hpt]; exact heq
      have h1 : α + t₁ ∈ A := by
        rw [hAIcc]; exact ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
      have h2 : α + t₂ ∈ A := by
        rw [hAIcc]; exact ⟨by linarith [ht₂.1], by linarith [ht₂.2]⟩
      have h3 := hinjA h1 h2 heq'
      linarith
    · rw [hCeq, hAIcc]
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨t - α, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
        change (g.geodesicFlow p (t - α)).proj = γ t
        rw [hpt, add_sub_cancel]
      · rintro ⟨t, ht, rfl⟩
        exact ⟨α + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, (hpt t).symm⟩

end DifferentialGeometry.Geometry.FiniteSoul
