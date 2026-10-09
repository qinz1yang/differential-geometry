import DifferentialGeometry.Geometry.Geodesic.Naturality.PullbackChartGeodesic
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.ShortGeodesicsManifold
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients

/-!
# LFR10, embedding clause: the comparison maps are buffered embeddings

Blueprint 207A, LFR10 (`prop:collapse-actual-buffered-embeddings`, A:25488–25555), embedding
clause. `(N, G, p)` complete with a `C^n` metric `G` (`2 ≤ n`) whose distance is its Riemannian
distance; `(X i, g i)` complete smooth manifolds carrying their Riemannian distance; `C^m` maps
`f i : N → X i` (`3 ≤ m`) on open sets `U i` that eventually contain every compact set, with
`f i p = q i`, chart `C²` convergence `f_i^* g_i → G` (in the extended charts of `N`), pointed
distortion `→ 0` on every ball, and an injectivity radius lower bound on every ball around `q i`.
Then for every `R`, eventually `f i` restricted to `B(p, R)` is a `C^m` diffeomorphism onto its
open image.

* `injective_mfderiv_of_pullback_pos`, `eventually_injective_mfderiv_of_chart_convergence`
  (**G10c input**): positive pulled-back chart coefficients give an injective differential;
  `C⁰` chart convergence to the positive definite `chartCoeff G` gives this eventually on every
  compact set.
* `eventually_exists_partialDiffeomorph_ball` (**LFR10, embedding clause, kernel**): the route of
  A:25520–25534 — local diffeomorphism by the finite-order inverse function theorem
  (`ContMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv`); injectivity: two points with
  the same image are `ε_i`-close, LFR09 (`exists_short_geodesics_of_contMDiffRiemannianMetric`)
  joins them by a short chart geodesic of `f_i^* g_i`, and the loop lemma G10b
  (`eq_of_pullback_geodesic_loop`) shows it is constant; an injective local diffeomorphism is a
  partial diffeomorphism onto its image (`exists_partialDiffeomorph_of_injOn`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.FiniteCategory

open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn
  tendstoUniformlyOn_of_cPConvergence)
open DifferentialGeometry.Geometry (pullbackMetricCoefficients pullbackMetricCoefficients_apply)
open DifferentialGeometry.Geometry.MetricSmoothing (chartCoeff chartCoeff_pos contDiffOn_chartCoeff
  injective_mfderiv_extChartAt_symm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- An injective endomorphism of a finite-dimensional space is invertible. -/
theorem isInvertible_of_injective_endo {T : E →L[ℝ] E} (hT : Injective T) : T.IsInvertible :=
  ⟨(LinearEquiv.ofInjectiveEndo (T : E →ₗ[ℝ] E) hT).toContinuousLinearEquiv, by ext a; rfl⟩

/-- **G10c, pointwise.** If the coefficients of `f^* g` in the chart at `z` are positive at `u`,
then the differential of `f` at the point `(extChartAt z)⁻¹ u` is injective. -/
theorem injective_mfderiv_of_pullback_pos {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    (g : SmoothRiemannianMetric I M) {f : N → M} (z : N) {u : E}
    (hu : u ∈ (extChartAt I z).target)
    (hf : MDifferentiableAt I I f ((extChartAt I z).symm u))
    (hpos : ∀ w : E, w ≠ 0 →
      0 < pullbackMetricCoefficients g (f ∘ (extChartAt I z).symm) u w w) :
    Injective (mfderiv I I f ((extChartAt I z).symm u)) := by
  set σ := (extChartAt I z).symm with hσ
  have hσd : MDifferentiableAt 𝓘(ℝ, E) I σ u :=
    ((contMDiffOn_extChartAt_symm (I := I) (n := 1) z).contMDiffAt
      ((isOpen_extChartAt_target z).mem_nhds hu)).mdifferentiableAt (by norm_num)
  have hcomp : mfderiv 𝓘(ℝ, E) I (f ∘ σ) u =
      (mfderiv I I f (σ u)).comp (mfderiv 𝓘(ℝ, E) I σ u) := mfderiv_comp u hf hσd
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I σ u
  have hDi : Injective D := injective_mfderiv_extChartAt_symm z hu
  have hsurj : Surjective D :=
    (LinearMap.injective_iff_surjective (f := (D : E →ₗ[ℝ] E))).mp hDi
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨w, rfl⟩ := hsurj a
  by_contra hne
  have hw : w ≠ 0 := fun h => hne (by rw [h]; exact map_zero D)
  have h := hpos w hw
  rw [pullbackMetricCoefficients_apply, hcomp] at h
  change 0 < (g.inner (f (σ u)) : E →L[ℝ] E →L[ℝ] ℝ)
    (mfderiv I I f (σ u) (mfderiv 𝓘(ℝ, E) I σ u w))
    (mfderiv I I f (σ u) (mfderiv 𝓘(ℝ, E) I σ u w)) at h
  change mfderiv I I f (σ u) (mfderiv 𝓘(ℝ, E) I σ u w) = 0 at ha
  rw [ha, map_zero] at h
  exact lt_irrefl _ h

/-- **G10c, eventual form.** `C⁰` convergence, in every extended chart of `N`, of the
coefficients of `f_i^* g_i` to the positive definite coefficients `chartCoeff G` gives,
eventually, an injective differential of `f i` at every point of a compact set. -/
theorem eventually_injective_mfderiv_of_chart_convergence
    {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
    [∀ i, IsManifold I ∞ (X i)] (g : ∀ i, SmoothRiemannianMetric I (X i))
    {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    {n : ℕ∞ω} (G : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) (f : ∀ i, N → X i) (U : ℕ → Set N) (hUo : ∀ i, IsOpen (U i))
    (hUK : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ U i)
    (hf : ∀ i, ContMDiffOn I I 1 (f i) (U i))
    (hconv : ∀ (z : N) (K : Set E), IsCompact K → K ⊆ (extChartAt I z).target →
      MapCPConvergenceOn K 0
        (fun i => pullbackMetricCoefficients (g i) (f i ∘ (extChartAt I z).symm))
        (chartCoeff G z))
    {C : Set N} (hC : IsCompact C) :
    ∀ᶠ i in atTop, ∀ x ∈ C, Injective (mfderiv I I (f i) x) := by
  classical
  have hloc : ∀ x₀ ∈ C, ∃ V ∈ 𝓝 x₀,
      ∀ᶠ i in atTop, ∀ x ∈ V, Injective (mfderiv I I (f i) x) := by
    intro x₀ _
    set e := extChartAt I x₀ with he
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target x₀) (e x₀)
      (mem_extChartAt_target x₀)
    set K : Set E := closedBall (e x₀) (ρ / 2) with hK_def
    have hKt : K ⊆ e.target := (closedBall_subset_ball (half_lt_self hρ)).trans hball
    have hK : IsCompact K := isCompact_closedBall _ _
    obtain ⟨c, hc, hcK⟩ :=
      DifferentialGeometry.Analysis.ODE.GeodesicLimits.exists_uniform_coercive_of_isCompact hK
        ((contDiffOn_chartCoeff G hn x₀).continuousOn.mono hKt)
        (fun u hu => ContinuousLinearMap.isCoercive_of_posDef _ fun _ hv =>
          chartCoeff_pos G x₀ (hKt hu) hv)
    have hunif := Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_of_cPConvergence (hconv x₀ K hK hKt)) (c / 2) (half_pos hc)
    have hσK : IsCompact (e.symm '' K) :=
      hK.image_of_continuousOn ((continuousOn_extChartAt_symm x₀).mono hKt)
    refine ⟨e.source ∩ e ⁻¹' ball (e x₀) (ρ / 2), ?_, ?_⟩
    · exact inter_mem (extChartAt_source_mem_nhds x₀)
        ((continuousAt_extChartAt x₀).preimage_mem_nhds (ball_mem_nhds _ (half_pos hρ)))
    · filter_upwards [hunif, hUK _ hσK] with i hi hiU x hx
      have hu : e x ∈ K := ball_subset_closedBall hx.2
      have hσx : e.symm (e x) = x := e.left_inv hx.1
      have hfd : MDifferentiableAt I I (f i) (e.symm (e x)) :=
        ((hf i).contMDiffAt ((hUo i).mem_nhds (hiU ⟨e x, hu, rfl⟩))).mdifferentiableAt
          (by norm_num)
      have hinj := injective_mfderiv_of_pullback_pos (g i) x₀ (hKt hu) hfd (fun w hw => by
        set A := chartCoeff G x₀ (e x) with hA
        set B := pullbackMetricCoefficients (g i) (f i ∘ e.symm) (e x) with hB
        have h1 : c * ‖w‖ * ‖w‖ ≤ A w w := hcK (e x) hu w
        have h2 : ‖A - B‖ < c / 2 := by
          have := hi (e x) hu
          rwa [dist_eq_norm] at this
        have h3 : |A w w - B w w| ≤ ‖A - B‖ * ‖w‖ * ‖w‖ := by
          have := (A - B).le_opNorm₂ w w
          rwa [sub_apply, sub_apply, Real.norm_eq_abs] at this
        have hw' : 0 < ‖w‖ * ‖w‖ := mul_pos (norm_pos_iff.mpr hw) (norm_pos_iff.mpr hw)
        have h4 : ‖A - B‖ * ‖w‖ * ‖w‖ ≤ c / 2 * (‖w‖ * ‖w‖) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right h2.le hw'.le
        have h5 := (abs_le.mp h3).2
        nlinarith)
      rwa [hσx] at hinj
  choose! V hV hVev using hloc
  obtain ⟨t, htC, hCt⟩ := hC.elim_nhds_subcover V hV
  filter_upwards [(Filter.eventually_all_finset t).2 fun z hz => hVev z (htC z hz)] with i hi x hx
  obtain ⟨z, hzt, hxz⟩ := mem_iUnion₂.mp (hCt hx)
  exact hi z hzt x hxz

/-- **LFR10, embedding clause (kernel).** `(N, G, p)`: a complete manifold whose distance is the
Riemannian distance of the `C^n` metric `G`, `2 ≤ n`. `(X i, g i)`: complete smooth manifolds
carrying their Riemannian distance. `f i : N → X i` is `C^m` (`3 ≤ m`) on the open set `U i`,
every compact set lies eventually in `U i`, `f i p = q i`, the chart coefficients of `f_i^* g_i`
converge in `C²` on compact subsets of every extended chart target of `N` to those of `G`, the
distortion of `f i` on every ball `B(p, S)` tends to `0`, and on every ball `B(q i, S)` the
exponential maps of `g i` are eventually injective on a common radius. Then for every `R`,
eventually `f i` restricted to `B(p, R)` is a `C^m` diffeomorphism onto its open image. -/
theorem eventually_exists_partialDiffeomorph_ball
    {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [CompleteSpace N]
    {n : ℕ∞ω} (G : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _))
    (hn : (2 : ℕ∞ω) ≤ n)
    (hG : letI : RiemannianBundle (fun x : N => TangentSpace I x) := ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold I N)
    {X : ℕ → Type*} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
    [∀ i, IsManifold I ∞ (X i)] [∀ i, CompleteSpace (X i)]
    [∀ i, T2Space (TangentBundle I (X i))]
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (f : ∀ i, N → X i) (p : N) (q : ∀ i, X i) (hp : ∀ i, f i p = q i)
    (U : ℕ → Set N) (hUo : ∀ i, IsOpen (U i))
    (hUK : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ U i)
    {m : ℕ} (hm : 3 ≤ m) (hf : ∀ i, ContMDiffOn I I m (f i) (U i))
    (hconv : ∀ (z : N) (K : Set E), IsCompact K → K ⊆ (extChartAt I z).target →
      MapCPConvergenceOn K 2
        (fun i => pullbackMetricCoefficients (g i) (f i ∘ (extChartAt I z).symm))
        (chartCoeff G z))
    (hdist : ∀ S ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball p S, ∀ y ∈ ball p S,
      |dist (f i x) (f i y) - dist x y| < ε)
    (hinjrad : ∀ S : ℝ, ∃ ι : ℝ, 0 < ι ∧ ∀ᶠ i in atTop, ∀ x ∈ ball (q i) S,
      InjOn (fun v : TangentSpace I x => Riemannian.Exponential.expMap (g i) x v)
        {v | Real.sqrt ((g i).inner x v v) < ι})
    (R : ℝ) :
    ∀ᶠ i in atTop, ∃ d : PartialDiffeomorph I I N (X i) m,
      d.source = ball p R ∧ d.target = f i '' ball p R ∧ (d : N → X i) = f i := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : ProperSpace N := by
    let _ : RiemannianBundle (fun x : N => TangentSpace I x) := ⟨G.toRiemannianMetric⟩
    have := hG
    exact Manifold.properSpace_of_isRiemannianManifold I
  have : Nonempty N := ⟨p⟩
  have hm1 : (1 : ℕ∞ω) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm2 : (2 : ℕ∞ω) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hm3 : (2 : ℕ∞ω) + 1 ≤ m := by exact_mod_cast (show 2 + 1 ≤ m by omega)
  have : IsManifold I m N := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have : ∀ i, IsManifold I m (X i) := fun i => IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  -- buffers
  set W : Set N := ball p (R + 1) with hW_def
  have hWsub : W ⊆ closedBall p (R + 2) :=
    (ball_subset_closedBall).trans (closedBall_subset_closedBall (by linarith))
  have hWsub1 : W ⊆ closedBall p (R + 1) := ball_subset_closedBall
  have hWU := hUK _ (isCompact_closedBall p (R + 2))
  -- injective differentials on the closed `(R + 1)`-ball (G10c)
  have hinjd := eventually_injective_mfderiv_of_chart_convergence g G hn f U hUo hUK
    (fun i => (hf i).of_le hm1) (fun z K hK hKt => (hconv z K hK hKt).mono_order (Nat.zero_le 2))
    (isCompact_closedBall p (R + 1))
  -- LFR09: short chart geodesics of `f_i^* g_i`
  have hb : ∀ z : N, ∀ᶠ i in atTop, ContDiffOn ℝ 2
      (pullbackMetricCoefficients (g i) (f i ∘ (extChartAt I z).symm))
      ((extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W) := by
    intro z
    filter_upwards [hWU] with i hi
    have hFm : ContMDiffOn 𝓘(ℝ, E) I m (f i ∘ (extChartAt I z).symm)
        ((extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W) :=
      (hf i).comp ((contMDiffOn_extChartAt_symm (n := m) z).mono inter_subset_left)
        (fun u hu => hi (hWsub hu.2))
    exact (g i).contDiffOn_pullback_inner (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) hm3
      (DifferentialGeometry.Analysis.ODE.GeodesicLimits.isOpen_extChartAt_target_inter_preimage
        isOpen_ball z) hFm
  obtain ⟨τ, L, hτ, hL, hgeo⟩ :=
    DifferentialGeometry.Analysis.ODE.GeodesicLimits.exists_short_geodesics_of_contMDiffRiemannianMetric
      G hn hG (fun i z => pullbackMetricCoefficients (g i) (f i ∘ (extChartAt I z).symm))
      isOpen_ball hb (fun z K hK hKs => hconv z K hK (hKs.trans inter_subset_left))
      (isCompact_closedBall p R) (closedBall_subset_ball (by linarith))
  -- a common injectivity radius on `B(q i, R + 2)`
  obtain ⟨ι, hι, hinjexp⟩ := hinjrad (R + 2)
  -- the distortion threshold
  set ε : ℝ := min (min τ 1) (ι / (L + 1)) with hε_def
  have hε : 0 < ε := lt_min (lt_min hτ one_pos) (div_pos hι (by linarith))
  have hετ : ε ≤ τ := (min_le_left _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hLε : L * ε < ι := by
    have h1 : ε ≤ ι / (L + 1) := min_le_right _ _
    have h2 : L * ε ≤ L * (ι / (L + 1)) := mul_le_mul_of_nonneg_left h1 hL.le
    have h3 : L * (ι / (L + 1)) < ι := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  filter_upwards [hWU, hinjd, hgeo, hinjexp, hdist (R + 1) ε hε] with i hWi hinji hgeoi hexpi
    hdisti
  have hRW : ball p R ⊆ W := ball_subset_ball (by linarith)
  -- injectivity on `B(p, R)` (LFR09 + G10a + G10b)
  have hinjOn : InjOn (f i) (ball p R) := by
    intro x hx y hy hxy
    have hpW : p ∈ W := mem_ball_self (by linarith [lt_of_le_of_lt dist_nonneg hx])
    have hd : dist x y < ε := by
      have h := hdisti x (hRW hx) y (hRW hy)
      rw [hxy, dist_self, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] at h
      exact h
    obtain ⟨z, γ, γ', hxs, hys, h0, h1, hγ⟩ :=
      hgeoi x (ball_subset_closedBall hx) y (hd.trans_le hετ)
    set e := extChartAt I z with he
    set UF : Set E := e.target ∩ e.symm ⁻¹' W with hUF
    have hUFo : IsOpen UF :=
      DifferentialGeometry.Analysis.ODE.GeodesicLimits.isOpen_extChartAt_target_inter_preimage
        isOpen_ball z
    have hFU : ContMDiffOn 𝓘(ℝ, E) I 2 (f i ∘ e.symm) UF :=
      ((hf i).comp ((contMDiffOn_extChartAt_symm (n := m) z).mono inter_subset_left)
        (fun u hu => hWi (hWsub hu.2))).of_le hm2
    have hFinj : ∀ u ∈ UF, Injective (mfderiv 𝓘(ℝ, E) I (f i ∘ e.symm) u) := by
      intro u hu
      have hσd : MDifferentiableAt 𝓘(ℝ, E) I e.symm u :=
        ((contMDiffOn_extChartAt_symm (I := I) (n := 1) z).contMDiffAt
          ((isOpen_extChartAt_target z).mem_nhds hu.1)).mdifferentiableAt (by norm_num)
      have hfd : MDifferentiableAt I I (f i) (e.symm u) :=
        (((hf i).of_le hm1).contMDiffAt ((hUo i).mem_nhds (hWi (hWsub hu.2)))).mdifferentiableAt
          (by norm_num)
      rw [mfderiv_comp u hfd hσd]
      exact (hinji _ (hWsub1 hu.2)).comp (injective_mfderiv_extChartAt_symm z hu.1)
    have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    obtain ⟨hγt, hγW, -, -, -, hsp⟩ := hγ (1 / 2) hhalf
    have hLd : L * dist x y < ι :=
      (mul_lt_mul_of_pos_left hd hL).trans hLε
    have hspeed : pullbackMetricCoefficients (g i) (f i ∘ e.symm) (γ (1 / 2)) (γ' (1 / 2))
        (γ' (1 / 2)) < (2 * ι) ^ 2 :=
      hsp.trans_lt (pow_lt_pow_left₀ (by linarith [mul_nonneg hL.le (dist_nonneg (x := x) (y := y))])
        (mul_nonneg hL.le dist_nonneg) (by norm_num))
    have hmid : (f i ∘ e.symm) (γ (1 / 2)) ∈ ball (q i) (R + 2) := by
      have h := hdisti _ hγW p hpW
      rw [hp i] at h
      have h2 : dist (e.symm (γ (1 / 2))) p < R + 1 := hγW
      change dist (f i (e.symm (γ (1 / 2)))) (q i) < R + 2
      linarith [(abs_lt.mp h).2]
    have hloop : (f i ∘ e.symm) (γ 0) = (f i ∘ e.symm) (γ 1) := by
      change f i (e.symm (γ 0)) = f i (e.symm (γ 1))
      rw [h0, h1, e.left_inv hxs, e.left_inv hys, hxy]
    have hγ01 := Riemannian.Geodesic.eq_of_pullback_geodesic_loop (g i) (hmetric i) hUFo hFU hFinj
      (γ := γ) (γ' := γ')
      (fun t ht => ⟨⟨(hγ t ht).1, (hγ t ht).2.1⟩, (hγ t ht).2.2.1, (hγ t ht).2.2.2.1⟩)
      hloop hι hspeed (hexpi _ hmid)
    rw [h0, h1] at hγ01
    exact e.injOn hxs hys hγ01
  -- local diffeomorphism on `B(p, R)` (finite-order inverse function theorem)
  have hloc : IsLocalDiffeomorphOn I I m (f i) (ball p R) :=
    ContMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv
      ((hf i).mono ((hRW.trans hWsub).trans hWi)) isOpen_ball hm1
      (fun x hx => isInvertible_of_injective_endo (hinji x (hWsub1 (hRW hx))))
  exact DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn isOpen_ball hloc
    hinjOn

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
