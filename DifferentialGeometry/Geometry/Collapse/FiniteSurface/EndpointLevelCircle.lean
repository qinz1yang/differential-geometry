import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointLevels
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.RegularLevelCircle
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.LocalizedDistanceSmoothing

/-!
# LFR23: every distance level `{r = a}`, `a ∈ [1, 9]`, is a Jordan circle

Blueprint LFR23 (master207A:26745): "each level is a compact one-manifold … this level, and every
level in `[1, 9]`, is one circle". Route (sheet-CMS-C, LFR23 (iii)): the distance `r` is not smooth,
so the circle structure comes from a smooth cross-section of the SAME outward flow:
* LFR02 (`exists_localized_distance_smoothing_lfr02`, `ε = 1`) gives `F`, smooth near
  `3/4 ≤ r ≤ 91/10`, `|F - r| < 1/100`, `dF ≈ -⟨v, ·⟩`; with `|V| < 2` and `⟨V, v⟩ < -3/4` this gives
  `dF(V) > 1/2` (`add_mul_le_comp_flow_of_mvfderiv`: `F` increases at rate `1/2` along the flow);
* in the band product `{r = 5} × [1, 9]` the function `F` is strictly increasing along every fibre,
  so `{F = 5}` is a cross-section homeomorphic to `{r = 5}` (`exists_embedding_level_of_band_product`);
* `{F = 5}` is a compact connected regular level, hence a Jordan circle (`exists_circle_of_regular_level`),
  and so is every level `{r = a}` (the band product moves `{r = 5}` onto it).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology Function
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.FiniteSoul

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Rate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
/-- **Rate of a smooth function along a flow.** If `F` is smooth on an open `W` and its derivative
along the field is at least `κ` on `W`, then `F` grows at rate `κ` along orbit segments in `W`. -/
theorem add_mul_le_comp_flow_of_mvfderiv {F : M → ℝ} {W : Set M} (hW : IsOpen W)
    (hF : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F W) {Φ : ℝ → M → M} (hΦ0 : ∀ x, Φ 0 x = x)
    {V : (x : M) → TangentSpace I x}
    (hder : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x))))
    {κ : ℝ} (hκ : ∀ y ∈ W, κ ≤ mvfderiv I F y (V y)) :
    ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ W) → F x + κ * t ≤ F (Φ t x) := by
  intro x t ht hmem
  have hd : ∀ τ ∈ Icc 0 t, HasDerivAt (fun s => F (Φ s x)) (mvfderiv I F (Φ τ x) (V (Φ τ x))) τ := by
    intro τ hτ
    have hFd : MDifferentiableAt I 𝓘(ℝ, ℝ) F (Φ τ x) :=
      ((hF _ (hmem τ hτ)).contMDiffAt (hW.mem_nhds (hmem τ hτ))).mdifferentiableAt (by simp)
    have hfd : HasFDerivAt (fun s => F (Φ s x))
        ((mfderiv I 𝓘(ℝ, ℝ) F (Φ τ x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ τ x)))) τ :=
      hasMFDerivAt_iff_hasFDerivAt.mp (hFd.hasMFDerivAt.comp τ (hder τ x))
    apply hasDerivAt_iff_hasFDerivAt.mpr
    apply hfd.congr_fderiv
    apply ContinuousLinearMap.ext
    intro u
    change mfderiv I 𝓘(ℝ, ℝ) F (Φ τ x) (u • V (Φ τ x)) = u • mvfderiv I F (Φ τ x) (V (Φ τ x))
    rw [map_smul]
    rfl
  have hcont : ContinuousOn (fun s => F (Φ s x)) (Icc 0 t) := fun τ hτ =>
    (hd τ hτ).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => F (Φ s x)) (interior (Icc 0 t)) := fun τ hτ =>
    (hd τ (interior_subset hτ)).differentiableAt.differentiableWithinAt
  have h := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0 t) hcont hdiff
    (C := κ) (fun τ hτ => by
      rw [(hd τ (interior_subset hτ)).deriv]
      exact hκ _ (hmem τ (interior_subset hτ))) 0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht
  simp only [hΦ0, sub_zero] at h
  linarith

end Rate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {r : ℕ∞}

/-- **LFR23: the distance levels are Jordan circles.** For `a ∈ [1, 9]` (and `δ ≤ 1/24000000`, a
universal threshold), the level `{r = a}` is the image of a continuous injective map of the
circle. -/
theorem exists_circle_sphere_of_endpoint
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 24000000) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) {a : ℝ}
    (ha : a ∈ Icc (1 : ℝ) 9) :
    ∃ c : Circle → M, Continuous c ∧ Injective c ∧ range c = sphere z₀ a := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have hδ1 : δ ≤ 1 / 9600 := hδ'.trans (by norm_num)
  set η : M → ℝ := fun x => infDist x ({z₀} : Set M) with hη
  have hηd : ∀ x, η x = dist x z₀ := fun x => infDist_singleton
  ---------------------------------------------------------------- the outward field and flow
  obtain ⟨V, -, hVR, O, hO, hAO, hOout, Φ, hΦ, hΦ0, hΦadd, hder, hrate, -, hspec, e, he1, -, he3,
    he4, -⟩ := exists_endpoint_field g hr hnorm hsec hδ hδ1 hq0 hqnn hdist hdense
  ---------------------------------------------------------------- LFR02
  set U : Set M := {x | 1 / 2 < dist x z₀ ∧ dist x z₀ < 37 / 4} with hU
  set C : Set M := {x | 3 / 4 ≤ dist x z₀ ∧ dist x z₀ ≤ 91 / 10} with hC
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
  have hUY : U ⊆ ({z₀} : Set M)ᶜ := fun x hx hxz => by
    rw [mem_singleton_iff] at hxz
    have := hx.1
    rw [hxz, dist_self] at this
    linarith
  have hCc : IsCompact C := (isCompact_closedBall z₀ (91 / 10)).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)) fun x hx => hx.2
  have hCU : C ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsqrt : 2 * Real.sqrt (600 * δ) ≤ min 1 1 / 100 := by
    have h1 : Real.sqrt (600 * δ) ≤ 1 / 200 := by
      rw [show (1 / 200 : ℝ) = Real.sqrt ((1 / 200) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [min_self]
    linarith
  obtain ⟨F, OF, hOF, hCOF, hFs, hFr, -, -, hFlip, -, -, hgrad⟩ :=
    exists_localized_distance_smoothing_lfr02 g hr hnorm one_pos isClosed_singleton
      (singleton_nonempty z₀) hUo hUY (fun x hx v hv v' hv' => by
        have hx₁ : 1 / 2 ≤ dist z₀ x := by rw [dist_comm]; exact hx.1.le
        have hx₂ : dist z₀ x ≤ 37 / 4 := by rw [dist_comm]; exact hx.2.le
        exact (sqrt_inner_sub_lt_of_endpoint_band g hr hnorm hsec hδ (by linarith) hq0 hqnn hdist
          hdense hx₁ hx₂ hv hv').trans_le hsqrt) hCc hCU (e := 1 / 100) (by norm_num)
  have hFr' : ∀ x, |F x - η x| < 1 / 100 := hFr
  ---------------------------------------------------------------- `dF(V) > 1/2`
  set W : Set M := OF ∩ O with hW
  have hWo : IsOpen W := hOF.inter hO
  have hdFV : ∀ y ∈ W, 1 / 2 ≤ mvfderiv I F y (V y) := by
    intro y hy
    obtain ⟨v, hv⟩ := (g.finiteMinimizingDirectionsTo_nonempty_isCompact hr hnorm isClosed_singleton
      (singleton_nonempty z₀) y).1
    have h1 := hgrad y hy.1 v hv (V y)
    have h2 : g.inner y (V y) v < -(3 / 4) := hOout y hy.2 v hv
    have h3 : g.inner y v (V y) = g.inner y (V y) v := g.symm y v (V y)
    have h4 : Real.sqrt (g.inner y (V y) (V y)) < 2 := by
      rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (g.inner_self_nonneg' y (V y)) (hVR y)
    have h5 := abs_le.1 h1
    rw [h3] at h5
    nlinarith [h5.1, Real.sqrt_nonneg (g.inner y (V y) (V y))]
  have hFrate := add_mul_le_comp_flow_of_mvfderiv hWo (hFs.mono inter_subset_left) hΦ0 hder hdFV
  ---------------------------------------------------------------- the band `1 ≤ r ≤ 9`
  have hC₀W : ∀ x, η x ∈ Icc (1 : ℝ) 9 → x ∈ W ∩ ({z₀} : Set M)ᶜ := by
    intro x hx
    have hxd : dist x z₀ ∈ Icc (1 : ℝ) 9 := by rw [← hηd]; exact hx
    refine ⟨⟨hCOF ⟨by linarith [hxd.1], by linarith [hxd.2]⟩, hAO ⟨by linarith [hx.1],
      by linarith [hx.2]⟩⟩, fun hxz => ?_⟩
    rw [mem_singleton_iff] at hxz
    rw [hxz, dist_self] at hxd
    linarith [hxd.1]
  have hIcc : ∀ s : ℝ, s ∈ Icc (1 : ℝ) 9 → s ∈ Icc (1 / 2 : ℝ) (37 / 4) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  set P := {x : M // infDist x ({z₀} : Set M) = 5}
  have hPc : CompactSpace P := by
    have hK : IsCompact {x : M | infDist x ({z₀} : Set M) = 5} := by
      refine (isCompact_closedBall z₀ 5).of_isClosed_subset (isClosed_eq (continuous_infDist_pt _)
        continuous_const) fun x hx => ?_
      have hx' : infDist x ({z₀} : Set M) = 5 := hx
      rw [infDist_singleton] at hx'
      exact hx'.le
    exact isCompact_iff_compactSpace.mp hK
  have hP5 : ∀ p : P, infDist (p : M) ({z₀} : Set M) ∈ Icc (1 / 2 : ℝ) (37 / 4) := fun p => by
    rw [p.2]; norm_num
  set e₁ : P × Icc (1 : ℝ) 9 → M :=
    fun q => (e (q.1, ⟨q.2.1, hIcc q.2.1 q.2.2⟩) : M) with he₁
  have he₁c : Continuous e₁ := by
    refine continuous_subtype_val.comp (e.continuous.comp (continuous_fst.prodMk ?_))
    exact (continuous_subtype_val.comp continuous_snd).subtype_mk _
  have he₁i : Injective e₁ := by
    intro q q' hqq'
    have h := e.injective (Subtype.ext hqq')
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    have h3 : ((q.2 : ℝ)) = q'.2 := by
      have h4 := congrArg (fun z : Icc (1 / 2 : ℝ) (37 / 4) => (z : ℝ)) h2
      exact h4
    exact Prod.ext h1 (Subtype.ext h3)
  -- along each fibre, `F` increases strictly
  have hmono : ∀ p, StrictMono (fun s : Icc (1 : ℝ) 9 => F (e₁ (p, s))) := by
    intro p s s' hss'
    have hs := hIcc s.1 s.2
    have hs' := hIcc s'.1 s'.2
    obtain ⟨hlev, hseg, -, -⟩ := hspec p (hP5 p) s hs
    obtain ⟨hlev', hseg', -, -⟩ := hspec p (hP5 p) s' hs'
    set t := hittingTime Φ η p s with ht
    set t' := hittingTime Φ η p s' with ht'
    have hband : ∀ u ∈ Icc (min t t') (max t t'), Φ u p ∈ W ∩ ({z₀} : Set M)ᶜ := by
      intro u hu
      have hmem : u ∈ uIcc 0 t ∨ u ∈ uIcc 0 t' := by
        rcases le_total 0 u with h0 | h0
        · by_cases h1 : u ≤ t
          · exact Or.inl (mem_uIcc.2 (Or.inl ⟨h0, h1⟩))
          · refine Or.inr (mem_uIcc.2 (Or.inl ⟨h0, ?_⟩))
            have h2 := hu.2
            rcases le_total t t' with h | h
            · rwa [max_eq_right h] at h2
            · rw [max_eq_left h] at h2
              exact absurd h2 h1
        · by_cases h1 : t ≤ u
          · exact Or.inl (mem_uIcc.2 (Or.inr ⟨h1, h0⟩))
          · refine Or.inr (mem_uIcc.2 (Or.inr ⟨?_, h0⟩))
            have h2 := hu.1
            rcases le_total t t' with h | h
            · rw [min_eq_left h] at h2
              exact absurd h2 h1
            · rwa [min_eq_right h] at h2
      apply hC₀W
      rcases hmem with h | h
      · have := hseg u h
        rw [p.2] at this
        rcases mem_uIcc.1 this with h' | h'
        · exact ⟨by linarith [h'.1], by linarith [h'.2, s.2.2]⟩
        · exact ⟨by linarith [h'.1, s.2.1], by linarith [h'.2]⟩
      · have := hseg' u h
        rw [p.2] at this
        rcases mem_uIcc.1 this with h' | h'
        · exact ⟨by linarith [h'.1], by linarith [h'.2, s'.2.2]⟩
        · exact ⟨by linarith [h'.1, s'.2.1], by linarith [h'.2]⟩
    have htt : t < t' := by
      by_contra hcon
      rcases (le_of_not_gt hcon).eq_or_lt with heq | hlt
      · have : (s : ℝ) = s' := by rw [← hlev, ← hlev', heq]
        exact absurd this (ne_of_lt hss')
      · have := lt_of_rate_of_lt hΦadd (by norm_num : (0 : ℝ) < 3 / 4) hrate hlt fun u hu =>
          have h := hband u ⟨by rw [min_eq_right hlt.le]; exact hu.1,
            by rw [max_eq_left hlt.le]; exact hu.2⟩
          ⟨h.1.2, h.2⟩
        rw [hlev, hlev'] at this
        exact absurd this (not_lt.2 hss'.le)
    have hF := lt_of_rate_of_lt hΦadd (by norm_num : (0 : ℝ) < 1 / 2) hFrate htt fun u hu =>
      (hband u ⟨by rw [min_eq_left htt.le]; exact hu.1, by rw [max_eq_right htt.le]; exact hu.2⟩).1
    change F (e (p, ⟨s.1, hs⟩) : M) < F (e (p, ⟨s'.1, hs'⟩) : M)
    rw [he1, he1]
    exact hF
  ---------------------------------------------------------------- the cross-section `{F = 5}`
  have hFc : Continuous F := hFlip.continuous
  have hkey : ∀ (p : P) (s : Icc (1 : ℝ) 9), η (e₁ (p, s)) = s := fun p s =>
    he4 (p, ⟨s.1, hIcc s.1 s.2⟩)
  have hlow : ∀ p : P, F (e₁ (p, ⟨1, left_mem_Icc.2 (by norm_num)⟩)) < 5 := fun p => by
    have h1 := hkey p ⟨1, left_mem_Icc.2 (by norm_num)⟩
    have h2 := abs_lt.1 (hFr' (e₁ (p, ⟨1, left_mem_Icc.2 (by norm_num)⟩)))
    rw [h1] at h2
    linarith [h2.2]
  have hhigh : ∀ p : P, 5 < F (e₁ (p, ⟨9, right_mem_Icc.2 (by norm_num)⟩)) := fun p => by
    have h1 := hkey p ⟨9, right_mem_Icc.2 (by norm_num)⟩
    have h2 := abs_lt.1 (hFr' (e₁ (p, ⟨9, right_mem_Icc.2 (by norm_num)⟩)))
    rw [h1] at h2
    linarith [h2.1]
  obtain ⟨c₀, hc₀c, hc₀i, hc₀r⟩ := exists_embedding_level_of_band_product (by norm_num)
    he₁c he₁i hFc hmono hlow hhigh
  have hlev19 : ∀ x, F x = 5 → η x ∈ Icc (1 : ℝ) 9 := fun x hx => by
    have h2 := abs_lt.1 (hFr' x)
    rw [hx] at h2
    exact ⟨by linarith [h2.2], by linarith [h2.1]⟩
  have hrange0 : range c₀ = {x | F x = 5} := by
    rw [hc₀r]
    ext x
    refine ⟨fun hx => hx.2, fun hx => ⟨?_, hx⟩⟩
    have hx19 := hlev19 x hx
    set y : {x : M // infDist x ({z₀} : Set M) ∈ Icc (1 / 2 : ℝ) (37 / 4)} :=
      ⟨x, hIcc _ hx19⟩ with hy
    refine ⟨((e.symm y).1, ⟨η x, hx19⟩), ?_⟩
    have hq : ((e.symm y).1, (⟨η x, hIcc _ hx19⟩ : Icc (1 / 2 : ℝ) (37 / 4))) = e.symm y :=
      Prod.ext rfl (Subtype.ext (he3 y).symm)
    change (e ((e.symm y).1, ⟨η x, hIcc _ hx19⟩) : M) = x
    rw [hq, e.apply_symm_apply]
  ---------------------------------------------------------------- `{F = 5}` is a Jordan circle
  have hPconn : ConnectedSpace P := by
    have h := (isPathConnected_sphere_of_endpoint g hr hnorm hsec hδ hδ1 hq0 hqnn hdist hdense
      (a := 5) ⟨by norm_num, by norm_num⟩).isConnected
    have hset : sphere z₀ 5 = {x : M | infDist x ({z₀} : Set M) = 5} := by
      ext y
      change dist y z₀ = 5 ↔ infDist y ({z₀} : Set M) = 5
      rw [infDist_singleton]
    rw [hset] at h
    exact isConnected_iff_connectedSpace.mp h
  have hcpt : IsCompact {x | F x = 5} := by rw [← hrange0]; exact isCompact_range hc₀c
  have hconn : IsConnected {x | F x = 5} := by rw [← hrange0]; exact isConnected_range hc₀c
  obtain ⟨c₁, hc₁c, hc₁i, hc₁r⟩ := exists_circle_of_regular_level (W := ⟨W, hWo⟩) hdim
    (hFs.mono inter_subset_left) (fun y hy => (hC₀W y (hlev19 y hy)).1)
    (fun y hy => ⟨V y, (lt_of_lt_of_le (by norm_num) (hdFV y (hC₀W y (hlev19 y hy)).1)).ne'⟩)
    hcpt hconn
  ---------------------------------------------------------------- transport to `{r = a}`
  have hemb := (hc₀c.isClosedEmbedding hc₀i).isEmbedding
  set h₀ : P ≃ₜ range c₀ := hemb.toHomeomorph with hh₀
  have hmem₁ : ∀ z, c₁ z ∈ range c₀ := fun z => by rw [hrange0, ← hc₁r]; exact mem_range_self z
  set ψ : Circle → P := fun z => h₀.symm ⟨c₁ z, hmem₁ z⟩ with hψ
  have hψc : Continuous ψ := h₀.symm.continuous.comp (hc₁c.subtype_mk _)
  have hψi : Injective ψ := fun z z' hzz' => hc₁i (congrArg Subtype.val (h₀.symm.injective hzz'))
  have hψs : Surjective ψ := by
    intro p
    have hp : c₀ p ∈ range c₁ := by rw [hc₁r, ← hrange0]; exact mem_range_self p
    obtain ⟨z, hz⟩ := hp
    refine ⟨z, ?_⟩
    change h₀.symm ⟨c₁ z, hmem₁ z⟩ = p
    rw [h₀.symm_apply_eq]
    exact Subtype.ext hz
  have ha' := hIcc a ha
  refine ⟨fun z => (e (ψ z, ⟨a, ha'⟩) : M), continuous_subtype_val.comp
    (e.continuous.comp (hψc.prodMk continuous_const)), fun z z' hzz' => ?_, ?_⟩
  · have h := e.injective (Subtype.ext hzz')
    exact hψi (Prod.ext_iff.1 h).1
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      have h := he4 (ψ z, ⟨a, ha'⟩)
      change infDist _ ({z₀} : Set M) = a at h
      rw [infDist_singleton] at h
      exact h
    · intro hy
      have hya : infDist y ({z₀} : Set M) = a := by rw [infDist_singleton]; exact hy
      set Y : {x : M // infDist x ({z₀} : Set M) ∈ Icc (1 / 2 : ℝ) (37 / 4)} :=
        ⟨y, by rw [hya]; exact ha'⟩ with hY
      obtain ⟨z, hz⟩ := hψs (e.symm Y).1
      refine ⟨z, ?_⟩
      have hq : (ψ z, (⟨a, ha'⟩ : Icc (1 / 2 : ℝ) (37 / 4))) = e.symm Y :=
        Prod.ext hz (Subtype.ext ((he3 Y).trans hya).symm)
      change (e (ψ z, ⟨a, ha'⟩) : M) = y
      rw [hq, e.apply_symm_apply]

end DifferentialGeometry.Geometry.Collapse
