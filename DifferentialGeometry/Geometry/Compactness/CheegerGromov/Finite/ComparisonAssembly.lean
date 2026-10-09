import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.StageComparison
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Exhaustion
import DifferentialGeometry.Analysis.Calculus.MapConvergence.DeterminantSign

/-!
# LFR14, assembly kernel: one sequence of comparison maps from the stage data

Blueprint LFR14 (master207A.tex:25869), step 5 ("exhaustion and one sequence"). The input is the
limit chart data of steps 1–3 (interface I-LIM, here as hypotheses on abstract data) together with
the stage construction I-STAGE (`exists_stage_comparison_maps_of_isCompact`), applied to the
closed balls `closedBall q (k + 1)`. A diagonal choice of stages
(`PartialDiffeomorph.exists_exhausting_restrictions`) gives ONE sequence of `C^K` partial
diffeomorphisms `j i : N → Y i`.

* `exhaustsByOpen_ball_add_one`: the balls `ball q (k + 1)` exhaust a metric space.
* `exists_compact_exhaustion_of_isOpen`: an increasing sequence of compact subsets of an open set
  of a proper space, cofinal in its compact subsets through interiors.
* `eventually_forall_exists_det_pos_of_chart_cover`: on a compact set covered by chart targets,
  `C¹` chart convergence to the identity makes the chart Jacobians eventually positive at a chart
  preimage of every point.
* `exists_comparison_maps_of_stage_data`: the assembly kernel. Pointed for EVERY index (a fallback
  chart map is used before a stage is available), sources exhaust compacts, `C^{K-1}` convergence
  of the pulled-back coefficients in every limit chart, distortion `→ 0` on balls, and positive
  Jacobians in the limit/source charts on the whole source (used for orientations).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry GC.MetricGeometry

/-- The balls `ball q (k + 1)` exhaust a metric space by open sets. -/
theorem exhaustsByOpen_ball_add_one {N : Type*} [MetricSpace N] (q : N) :
    ExhaustsByOpen (fun k : ℕ => ball q ((k : ℝ) + 1)) where
  isOpen _ := isOpen_ball
  mono_step k := ball_subset_ball (by push_cast; linarith)
  subset C hC := by
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_ball q).mp hC.isBounded
    obtain ⟨k₀, hk₀⟩ := exists_nat_ge r
    refine ⟨k₀, fun k hk => hr.trans (ball_subset_ball ?_)⟩
    have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    linarith

/-- **Cofinal compact exhaustion of an open set.** An open set `s` of a proper metric space carries
an increasing sequence of compact subsets `T m` that is cofinal in the compact subsets of `s`
THROUGH INTERIORS: every compact `S ⊆ s` lies in `interior (T m)` for all large `m`. Explicitly
`T m = closedBall z m \ thickening (1 / (m + 1)) sᶜ`. -/
theorem exists_compact_exhaustion_of_isOpen {E : Type*} [MetricSpace E] [ProperSpace E]
    (z : E) {s : Set E} (hs : IsOpen s) :
    ∃ T : ℕ → Set E, (∀ m, IsCompact (T m) ∧ T m ⊆ s) ∧ Monotone T ∧
      ∀ S : Set E, IsCompact S → S ⊆ s → ∃ m₀ : ℕ, ∀ m ≥ m₀, S ⊆ interior (T m) := by
  refine ⟨fun m => closedBall z m \ thickening (1 / ((m : ℝ) + 1)) sᶜ, fun m => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (isCompact_closedBall z _).diff isOpen_thickening
  · intro x hx
    by_contra hxs
    exact hx.2 (self_subset_thickening (by positivity) _ hxs)
  · intro m m' hmm' x hx
    have h1 : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    refine ⟨closedBall_subset_closedBall h1 hx.1, fun hxt => hx.2 ?_⟩
    refine thickening_mono ?_ _ hxt
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · intro S hS hSs
    obtain ⟨δ, hδ, hδs⟩ := hS.exists_thickening_subset_open hs hSs
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall z).mp hS.isBounded
    obtain ⟨m₀, hm₀⟩ := exists_nat_gt (max r (1 / δ))
    refine ⟨m₀, fun m hm => ?_⟩
    have hm' : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
    have hlt : 1 / ((m : ℝ) + 1) < δ := by
      have h1 : 1 / δ < (m : ℝ) + 1 := ((le_max_right _ _).trans_lt hm₀).trans (by linarith)
      exact (one_div_lt (by positivity) hδ).mpr h1
    -- an open set between `S` and `T m`
    let A : Set E := ball z m ∩ (cthickening (1 / ((m : ℝ) + 1)) sᶜ)ᶜ
    have hAo : IsOpen A := isOpen_ball.inter isClosed_cthickening.isOpen_compl
    have hAT : A ⊆ closedBall z m \ thickening (1 / ((m : ℝ) + 1)) sᶜ := fun x hx =>
      ⟨ball_subset_closedBall hx.1, fun hxt => hx.2 (thickening_subset_cthickening _ _ hxt)⟩
    refine fun x hx => interior_maximal hAT hAo ⟨?_, fun hxc => ?_⟩
    · exact mem_ball.mpr ((hr hx).trans_lt (((le_max_left _ _).trans_lt hm₀).trans_le hm'))
    · obtain ⟨y, hy, hxy⟩ :=
        mem_thickening_iff.mp (cthickening_subset_thickening' hδ hlt _ hxc)
      exact hy (hδs (mem_thickening_iff.mpr ⟨x, hx, by rw [dist_comm]; exact hxy⟩))

/-- **Positive chart Jacobians on a compact set.** Let `Fᵢ` be `C^K` (`1 ≤ K`) on an open `W` and
let its chart representations `(d a i)⁻¹ ∘ Fᵢ ∘ σ a` be eventually captured and converge to the
identity in `C¹` on the compacts of `σ a⁻¹ W`. On a compact `C ⊆ W` covered by the targets of the
`σ a`, eventually every point `x ∈ C` has a chart preimage `u` at which the chart representation
has positive Jacobian. -/
theorem eventually_forall_exists_det_pos_of_chart_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace E N] {K : ℕ} (hK : 1 ≤ K)
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)] {α : Type*}
    (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K)
    (d : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (F : ∀ i, N → Y i) {W : Set N} (hW : IsOpen W)
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) W)
    (hcoord : ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source ∩ σ a ⁻¹' W →
      (∀ᶠ i in atTop, MapsTo (F i ∘ σ a) L (d a i).target) ∧
      MapCPConvergenceOn L 1 (fun i x => (d a i).symm (F i (σ a x))) id)
    {C : Set N} (hC : IsCompact C) (hCW : C ⊆ W) (hCσ : C ⊆ ⋃ a, (σ a).target) :
    ∀ᶠ i in atTop, ∀ x ∈ C, ∃ a, ∃ u ∈ (σ a).source, σ a u = x ∧ F i x ∈ (d a i).target ∧
      0 < (fderiv ℝ (fun y => (d a i).symm (F i (σ a y))) u).det := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK
  obtain ⟨S, hS⟩ := hC.elim_finite_subcover (fun a => (σ a).target) (fun a => (σ a).open_target)
    hCσ
  obtain ⟨P, hPc, hPσ, hCP⟩ :=
    hC.finite_compact_cover S (fun a => (σ a).target) (fun a _ => (σ a).open_target) hS
  have hPC : ∀ a ∈ S, P a ⊆ C := fun a ha => by
    rw [hCP]
    exact subset_biUnion_of_mem (u := P) ha
  have hpiece : ∀ a ∈ S, ∀ᶠ i in atTop,
      MapsTo (F i ∘ σ a) ((σ a).symm '' P a) (d a i).target ∧
      ∀ u ∈ (σ a).symm '' P a,
        0 < (fderiv ℝ (fun y => (d a i).symm (F i (σ a y))) u).det := by
    intro a ha
    have hLc : IsCompact ((σ a).symm '' P a) :=
      (hPc a).image_of_continuousOn ((σ a).symm.contMDiffOn.continuousOn.mono (hPσ a))
    have hLW : (σ a).symm '' P a ⊆ (σ a).source ∩ σ a ⁻¹' W := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨(σ a).toPartialEquiv.map_target (hPσ a hx), ?_⟩
      have hr : σ a ((σ a).symm x) = x := (σ a).toPartialEquiv.right_inv (hPσ a hx)
      rw [mem_preimage, hr]
      exact hCW (hPC a ha hx)
    obtain ⟨hcap, hconv⟩ := hcoord a _ hLc hLW
    have hdiff : ∀ᶠ i in atTop, ∀ z ∈ (σ a).symm '' P a,
        DifferentiableAt ℝ (fun x => (d a i).symm (F i (σ a x))) z := by
      filter_upwards [hcap] with i hi z hz
      have hσz : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K (σ a) z :=
        (σ a).contMDiffOn_toFun.contMDiffAt ((σ a).open_source.mem_nhds (hLW hz).1)
      have hFz : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) (σ a z) :=
        (hF i).contMDiffAt (hW.mem_nhds (hLW hz).2)
      have hdz : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K (d a i).symm (F i (σ a z)) :=
        ((d a i).contMDiffOn_invFun.contMDiffAt ((d a i).open_target.mem_nhds (hi hz))).of_le
          (by exact_mod_cast le_top)
      exact mdifferentiableAt_iff_differentiableAt.mp
        ((hdz.comp z (hFz.comp z hσz)).mdifferentiableAt hK0)
    filter_upwards [hcap, MapCPConvergenceOn.eventually_det_fderiv_pos hconv hdiff] with i h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [(Finset.eventually_all S).mpr hpiece] with i hi x hx
  rw [hCP] at hx
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
  have hxt : x ∈ (σ a).target := hPσ a hxa
  have hu : (σ a).symm x ∈ (σ a).symm '' P a := mem_image_of_mem _ hxa
  have hσu : σ a ((σ a).symm x) = x := (σ a).toPartialEquiv.right_inv hxt
  refine ⟨a, (σ a).symm x, (σ a).toPartialEquiv.map_target hxt, hσu, ?_, (hi a ha).2 _ hu⟩
  have h := (hi a ha).1 hu
  simp only [Function.comp_apply, hσu] at h
  exact h

/-- **Assembly kernel (LFR14 step 5).** From the limit chart data (I-LIM, as hypotheses: chart
parametrizations `σ a` of order `K` covering the proper limit `N`, smooth source charts `d a i`,
convex buffers `D a`, `C^K` transition convergence, `C^{K-1}` coefficient limits `b a`, pointed
ball approximations `F i` with chart capture), there is ONE sequence of `C^K` partial
diffeomorphisms `j i : N → Y i` such that
* `j i q = p i` with `q` in the source, for EVERY `i`;
* every compact set eventually lies in the sources;
* the pulled-back coefficients converge in `C^{K-1}` to `b a` on the compacts of every `σ a`
  source;
* the distortion on every ball about `q` tends to zero;
* eventually, every point of the source has a chart preimage at which the chart representation
  `(d a i)⁻¹ ∘ j i ∘ σ a` has positive Jacobian. -/
theorem exists_comparison_maps_of_stage_data
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N]
    {K : ℕ} (hK : 1 ≤ K) [IsManifold 𝓘(ℝ, E) K N]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    {α : Type*} [Countable α] (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K)
    (d : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (D : α → Set E)
    (hD : ∀ a, IsOpen (D a) ∧ Convex ℝ (D a) ∧ (σ a).source ⊆ D a ∧ ∀ i, D a ⊆ (d a i).source)
    (htrans : ∀ a c (L : Set E), IsCompact L → L ⊆ ((σ a).trans (σ c).symm).source →
      MapCPConvergenceOn L K (fun i x => (d c i).symm (d a i x)) ((σ a).trans (σ c).symm) ∧
      ∀ᶠ i in atTop, L ⊆ ((d a i).trans (d c i).symm).source)
    (b : α → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (D a) ∧
      ∀ S : Set E, IsCompact S → S ⊆ D a →
        MapCPConvergenceOn S (K - 1) (fun i => pullbackMetricCoefficients (g i) (d a i)) (b a))
    (q : N) (p : ∀ i, Y i) (a₀ : α)
    (h₀ : 0 ∈ (σ a₀).source ∧ σ a₀ 0 = q ∧ ∀ i, d a₀ i 0 = p i)
    (R ε : ℕ → ℝ) (F : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0))
    (hchart : ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source →
      (∀ᶠ i in atTop, MapsTo (d a i) L (closedBall (p i) (R i))) ∧
      TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (d a i u)) (σ a) atTop L)
    (hcover : ∀ x : N, ∃ a, x ∈ (σ a).target) :
    ∃ j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) K,
      (∀ i, q ∈ (j i).source ∧ j i q = p i) ∧
      (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
      (∀ a (S : Set E), IsCompact S → S ⊆ (σ a).source →
        MapCPConvergenceOn S (K - 1)
          (fun i => pullbackMetricCoefficients (g i) ((j i : N → Y i) ∘ σ a)) (b a)) ∧
      (∀ r η : ℝ, 0 < η → ∀ᶠ i in atTop, ∀ x ∈ ball q r, ∀ y ∈ ball q r,
        |dist (j i x) (j i y) - dist x y| < η) ∧
      (∀ᶠ i in atTop, ∀ x ∈ (j i).source, ∃ a, ∃ u ∈ (σ a).source, σ a u = x ∧
        j i x ∈ (d a i).target ∧
        0 < (fderiv ℝ (fun y => (d a i).symm (j i (σ a y))) u).det) := by
  classical
  have : Nonempty α := ⟨a₀⟩
  have hq : q ∈ (σ a₀).target := h₀.2.1 ▸ (σ a₀).toPartialEquiv.map_source h₀.1
  have hKle : ((K : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  -- the stages: I-STAGE over `closedBall q (k + 1)`
  choose W Fm hW _ hBW hFm hpt hcoord hunif hemb using fun k : ℕ =>
    exists_stage_comparison_maps_of_isCompact hK g σ d D hD htrans b hb q p a₀ h₀ R ε F hε hchart
      (isCompact_closedBall q ((k : ℝ) + 1)) (fun x _ => mem_iUnion.mpr (hcover x))
  let O : ℕ → Set N := fun k : ℕ => ball q ((k : ℝ) + 1)
  have hclW : ∀ k : ℕ, closedBall q ((k : ℝ) + 1) ⊆ W k := fun k => subset_union_left.trans (hBW k)
  have hOcl : ∀ k : ℕ, closure (O k) ⊆ W k := fun k => closure_ball_subset_closedBall.trans (hclW k)
  have hOc : ∀ k : ℕ, IsCompact (closure (O k)) := fun k =>
    (isCompact_closedBall q _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hqO : ∀ k : ℕ, q ∈ O k := fun k => mem_ball_self (by positivity)
  -- the fallback chart map, pointed for every index
  let fb : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) K := fun i =>
    (σ a₀).symm.trans (DifferentialGeometry.PartialDiffeomorph.ofLE (d a₀ i) hKle)
  have h0 : (σ a₀).symm q = 0 := by
    rw [← h₀.2.1]
    exact (σ a₀).toPartialEquiv.left_inv h₀.1
  have hfb : ∀ i, q ∈ (fb i).source ∧ fb i q = p i := by
    intro i
    refine ⟨⟨hq, ?_⟩, ?_⟩
    · change (σ a₀).symm q ∈ (d a₀ i).source
      rw [h0]
      exact (hD a₀).2.2.2 i ((hD a₀).2.2.1 h₀.1)
    · change d a₀ i ((σ a₀).symm q) = p i
      rw [h0]
      exact h₀.2.2 i
  -- the stage maps
  let good : ℕ → ℕ → Prop := fun (k i : ℕ) =>
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) K,
      e.source = O k ∧ (e : N → Y i) = Fm k i ∧ Fm k i q = p i
  let st : ℕ → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) K := fun k i =>
    if h : good k i then h.choose else fb i
  have hstgood : ∀ k i, good k i →
      (st k i).source = O k ∧ (st k i : N → Y i) = Fm k i ∧ Fm k i q = p i := by
    intro k i h
    simp only [st, h, ↓reduceDIte]
    exact h.choose_spec
  have hstpt : ∀ k i, q ∈ (st k i).source ∧ st k i q = p i := by
    intro k i
    by_cases h : good k i
    · obtain ⟨hs, hf, hp⟩ := hstgood k i h
      rw [hs, hf]
      exact ⟨hqO k, hp⟩
    · simp only [st, h, ↓reduceDIte]
      exact hfb i
  -- the test compacts of the chart sources
  choose T hT _ hTex using fun a => exists_compact_exhaustion_of_isOpen (0 : E) (σ a).open_source
  obtain ⟨e, he⟩ := exists_surjective_nat α
  -- the stage predicate
  let P : ℕ → ℕ → Prop := fun (k i : ℕ) =>
    (st k i : N → Y i) = Fm k i ∧
    (∀ x ∈ closedBall q ((k : ℝ) + 1), ∀ y ∈ closedBall q ((k : ℝ) + 1),
      |dist (Fm k i x) (Fm k i y) - dist x y| < 1 / ((k : ℝ) + 1)) ∧
    (∀ t₁ ∈ Iic k, ∀ t₂ ∈ Iic k,
      T (e t₁) t₂ ⊆ (σ (e t₁)).source ∩ σ (e t₁) ⁻¹' W k →
      ∀ r ≤ K - 1, ∀ u ∈ T (e t₁) t₂,
        mapDerivNorm r (pullbackMetricCoefficients (g i) (Fm k i ∘ σ (e t₁))) (b (e t₁)) u ≤
          1 / ((k : ℝ) + 1)) ∧
    (∀ x ∈ O k, ∃ a, ∃ u ∈ (σ a).source, σ a u = x ∧ Fm k i x ∈ (d a i).target ∧
      0 < (fderiv ℝ (fun y => (d a i).symm (Fm k i (σ a y))) u).det)
  have hstage : ∀ k : ℕ, ∀ᶠ i in atTop, O k ⊆ (st k i).source ∧ st k i q = p i ∧ P k i := by
    intro k
    have hk1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hgood : ∀ᶠ i in atTop, good k i := by
      filter_upwards [hemb k (O k) isOpen_ball (hOc k) (hOcl k), hpt k] with i hi hpi
      obtain ⟨e', he's, he'f⟩ := hi
      exact ⟨e', he's, he'f, hpi⟩
    have hdist := (hunif k _ (isCompact_closedBall q ((k : ℝ) + 1)) (hclW k)).2 _ hk1
    have hcoef : ∀ᶠ i in atTop, ∀ t₁ ∈ Iic k, ∀ t₂ ∈ Iic k,
        T (e t₁) t₂ ⊆ (σ (e t₁)).source ∩ σ (e t₁) ⁻¹' W k →
        ∀ r ≤ K - 1, ∀ u ∈ T (e t₁) t₂,
          mapDerivNorm r (pullbackMetricCoefficients (g i) (Fm k i ∘ σ (e t₁))) (b (e t₁)) u ≤
            1 / ((k : ℝ) + 1) := by
      refine (finite_Iic k).eventually_all.mpr fun t₁ _ => ?_
      refine (finite_Iic k).eventually_all.mpr fun t₂ _ => ?_
      by_cases hTW : T (e t₁) t₂ ⊆ (σ (e t₁)).source ∩ σ (e t₁) ⁻¹' W k
      · obtain ⟨k₀, hk₀⟩ := (hcoord k (e t₁) _ (hT (e t₁) t₂).1 hTW).2.2 _ hk1
        filter_upwards [eventually_ge_atTop k₀] with i hi _ r hr u hu
        exact hk₀ i hi r hr u hu
      · exact Eventually.of_forall fun _ h => absurd h hTW
    have hdet := eventually_forall_exists_det_pos_of_chart_cover hK σ d (Fm k) (hW k) (hFm k)
      (fun a L hL hLW => ⟨(hcoord k a L hL hLW).1, (hcoord k a L hL hLW).2.1.mono_order hK⟩)
      (hOc k) (hOcl k) (fun x _ => mem_iUnion.mpr (hcover x))
    filter_upwards [hgood, hdist, hcoef, hdet] with i hg hd hc hdt
    obtain ⟨hs, hf, hp⟩ := hstgood k i hg
    refine ⟨hs.symm ▸ subset_rfl, ?_, hf, hd, hc, fun x hx => hdt x (subset_closure hx)⟩
    rw [hf]
    exact hp
  -- the diagonal
  obtain ⟨s, hs, ψ, hψf, -, hψsrc, -, htail, hexh⟩ :=
    DifferentialGeometry.PartialDiffeomorph.exists_exhausting_restrictions
      (exhaustsByOpen_ball_add_one q) st q p P hstage
  have hsi : ∀ k₀ : ℕ, ∀ᶠ i in atTop, P (s i) i ∧ (k₀ : ℝ) ≤ s i := by
    intro k₀
    filter_upwards [htail, hs.eventually_ge_atTop k₀] with i hi hik
    exact ⟨hi.2.2.2, by exact_mod_cast hik⟩
  refine ⟨ψ, fun i => ?_, hexh, ?_, ?_, ?_⟩
  · -- pointed, for every index
    refine ⟨?_, ?_⟩
    · rw [hψsrc i]
      exact ⟨(hstpt (s i) i).1, hqO (s i)⟩
    · rw [hψf i]
      exact (hstpt (s i) i).2
  · -- the coefficients in the limit charts
    intro a S hS hSs
    obtain ⟨m, hm⟩ := hTex a S hS hSs
    have hSm : S ⊆ T a m := (hm m le_rfl).trans interior_subset
    obtain ⟨t₁, rfl⟩ := he a
    have himg : IsCompact (σ (e t₁) '' T (e t₁) m) :=
      (hT (e t₁) m).1.image_of_continuousOn
        ((σ (e t₁)).contMDiffOn.continuousOn.mono (hT (e t₁) m).2)
    obtain ⟨r₀, hr₀⟩ := (isBounded_iff_subset_closedBall q).mp himg.isBounded
    obtain ⟨k₁, hk₁⟩ := exists_nat_ge r₀
    intro η hη
    obtain ⟨k₂, hk₂⟩ := exists_nat_gt (1 / η)
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp ((hsi (max (max t₁ m) (max k₁ k₂))).and
      (hs.eventually_ge_atTop (max (max t₁ m) (max k₁ k₂))))
    refine ⟨i₀, fun i hi r hr u hu => ?_⟩
    obtain ⟨⟨⟨hf, -, hc, -⟩, hle⟩, hle'⟩ := hi₀ i hi
    have hsk : (k₁ : ℝ) ≤ s i := by
      have : k₁ ≤ s i := (le_max_left _ _).trans ((le_max_right _ _).trans hle')
      exact_mod_cast this
    have hsk₂ : (k₂ : ℝ) ≤ s i := by
      have : k₂ ≤ s i := (le_max_right _ _).trans ((le_max_right _ _).trans hle')
      exact_mod_cast this
    have hTW : T (e t₁) m ⊆ (σ (e t₁)).source ∩ σ (e t₁) ⁻¹' W (s i) := by
      intro v hv
      refine ⟨(hT (e t₁) m).2 hv, hclW (s i) ?_⟩
      exact closedBall_subset_closedBall (by linarith) (hr₀ (mem_image_of_mem _ hv))
    have hb := hc t₁ ((le_max_left _ _).trans ((le_max_left _ _).trans hle'))
      m ((le_max_right _ _).trans ((le_max_left _ _).trans hle')) hTW r hr u (hSm hu)
    have hη' : 1 / ((s i : ℝ) + 1) ≤ η := by
      have h1 : 1 / η < (s i : ℝ) + 1 := hk₂.trans_le (by linarith)
      exact ((one_div_lt (by positivity) hη).mpr h1).le
    change mapDerivNorm r (pullbackMetricCoefficients (g i) ((ψ i : N → Y i) ∘ σ (e t₁)))
      (b (e t₁)) u ≤ η
    rw [hψf i, hf]
    exact hb.trans hη'
  · -- distortion on balls
    intro r η hη
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max r (1 / η))
    filter_upwards [hsi k₀] with i hi x hx y hy
    obtain ⟨⟨hf, hd, -, -⟩, hk⟩ := hi
    have hball : ball q r ⊆ closedBall q ((s i : ℝ) + 1) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by
        have := (le_max_left r (1 / η)).trans hk₀.le
        linarith))
    have hη' : 1 / ((s i : ℝ) + 1) < η := by
      have h1 : 1 / η < (s i : ℝ) + 1 := ((le_max_right r _).trans_lt hk₀).trans_le (by linarith)
      exact (one_div_lt (by positivity) hη).mpr h1
    rw [hψf i, hf]
    exact (hd x (hball hx) y (hball hy)).trans hη'
  · -- positive Jacobians on the whole source
    filter_upwards [htail] with i hi x hx
    obtain ⟨hsrc, -, -, hf, -, -, hdt⟩ := hi
    rw [hsrc] at hx
    obtain ⟨a, u, hu, hσu, ht, hdet⟩ := hdt x hx
    refine ⟨a, u, hu, hσu, ?_, ?_⟩
    · rw [hψf i, hf]
      exact ht
    · rw [hψf i, hf]
      exact hdet

end DifferentialGeometry.CheegerGromovCompactness
