import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalDirectionLimit
import DifferentialGeometry.Geometry.Collapse.EdgeModelDirectionTransfer
import DifferentialGeometry.Geometry.Comparison.AdaptedStabilityRiemannian
import DifferentialGeometry.Geometry.Collapse.EdgeTangentialPinning

/-!
# LFR18 → LFR20 step 2 / (LFR28.3): the vertical derivative of a rank-one coordinate

Blueprint LFR20 step 2 (master207A:26437–26457) and (LFR28.3) (A:27338–27349); statement frozen by
lane F8-NEW2 (sheet-F8-NEW2.md §3). For LFR14-shaped data, a metric product structure `Φ`, the
vertical field `V` of LFR18 (`hVdir`, `hVcont`), source coordinates `η i` that are globally
`(1 + σ)`-Lipschitz and satisfy LFR19's all-direction estimate (LFR19.1) against coordinates `U i`
with `U i ∘ j i → t` uniformly on compact sets:

* `eventually_one_sub_lt_mvfderiv_vertical` (**bridge**): `D(η_i ∘ j_i)(V) > 1 - σ - ε` eventually,
  uniformly on `C`.

Route, by contradiction: along a bad sequence choose ANY source minimizing direction `w_k` to the
shifted point; LC50′ (compact endpoint) makes `d j⁻¹ w_k → V`, hence `|d j (V - d j⁻¹ w_k)|_{g} → 0`
(`tendsto_pullback_inner_of_tendsto`); the Lipschitz bound turns this into
`Dη(d j V) ≥ Dη(w_k) - o(1)`, LFR19.1 gives `Dη(w_k) > Q_k - σ`, and the quotient `Q_k → 1` by the
uniform coordinate convergence and the distortion clause.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M'] [CompleteSpace M']

section Bundle

variable [RiemannianBundle (fun z : M' => TangentSpace I z)] [IsRiemannianManifold I M']
  [IsContinuousRiemannianBundle E (fun z : M' => TangentSpace I z)]

private theorem abs_mvfderiv_le_of_lipschitzWith_aux (g : SmoothRiemannianMetric I M')
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) {f : M' → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hf : LipschitzWith (Real.toNNReal L) f) {z : M'}
    (hfz : MDifferentiableAt I 𝓘(ℝ, ℝ) f z) (X : TangentSpace I z) :
    |mvfderiv I f z X| ≤ L * Real.sqrt (g.inner z X X) := by
  have : ProperSpace M' := Manifold.properSpace_of_isRiemannianManifold I
  have hunit : ∀ w : TangentSpace I z, g.inner z w w = 1 → |mvfderiv (I := I) f z w| ≤ L :=
    fun w hw => DifferentialGeometry.Geometry.Comparison.abs_mvfderiv_le_of_lipschitzOn g hEnorm
      isOpen_univ (mem_univ z) hfz (fun y _ y' _ => by
        have h := hf.dist_le_mul y y'
        rwa [Real.coe_toNNReal _ hL, Real.dist_eq] at h) w hw
  exact DifferentialGeometry.Geometry.Collapse.abs_mvfderiv_le_mul_sqrt_of_unit g hEnorm hunit X

end Bundle

/-- **Lipschitz functions have bounded differentials** (T0's convention: the smooth metric carries
the distance of `M'`, no bundle instances): `|df(X)| ≤ L |X|_g`. -/
theorem abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf (g : SmoothRiemannianMetric I M')
    (hmetric : ∀ a b : M', riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {f : M' → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hf : LipschitzWith (Real.toNNReal L) f) {z : M'}
    (hfz : MDifferentiableAt I 𝓘(ℝ, ℝ) f z) (X : TangentSpace I z) :
    |mvfderiv I f z X| ≤ L * Real.sqrt (g.inner z X X) := by
  let hRB : RiemannianBundle (fun y : M' => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold I M' := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  have hcont : IsContinuousRiemannianBundle E (fun y : M' => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact @abs_mvfderiv_le_of_lipschitzWith_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRB hRM hcont g
    (isMetricNorm_of_riemannianBundle g) _ _ hL hf _ hfz X

end Lipschitz

section PerIndex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M'] [CompleteSpace M']

omit [IsManifold I ∞ N] in
/-- **Per-index comparison.** For a partial diffeomorphism `j : N → M'` (order `≥ 1`), a
`L`-Lipschitz function `f` on `M'` (differentiable at `j z`), a vector `a ∈ T_z N` and any
`w ∈ T_{j z} M'` with inverse lift `u = d j⁻¹ w`:
`df(w) - L |d j (a - u)|_g ≤ d(f ∘ j)(a)`. -/
theorem sub_le_mvfderiv_comp_of_lipschitzWith (g : SmoothRiemannianMetric I M')
    (hmetric : ∀ a b : M', riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 1 ≤ K) (j : PartialDiffeomorph I I N M' K) {z : N} (hz : z ∈ j.source)
    {f : M' → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : LipschitzWith (Real.toNNReal L) f)
    (hfz : MDifferentiableAt I 𝓘(ℝ, ℝ) f (j z)) (a : TangentSpace I z)
    (w : TangentSpace I (j z)) :
    let u : TangentSpace I z := mfderiv I I (j.symm : M' → N) (j z) w
    mvfderiv I f (j z) w - L * Real.sqrt (g.inner (j z) (mfderiv I I (j : N → M') z (a - u))
      (mfderiv I I (j : N → M') z (a - u))) ≤ mvfderiv I (fun y => f (j y)) z a := by
  intro u
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hjd : MDifferentiableAt I I (j : N → M') z := j.mdifferentiableAt hK0 hz
  have hchain : mvfderiv I (fun y => f (j y)) z a =
      mvfderiv I f (j z) (mfderiv I I (j : N → M') z a) := mvfderiv_comp_apply z hfz hjd a
  have hu : mfderiv I I (j : N → M') z u = w := mfderiv_apply_mfderiv_symm_of_mem_source hK j hz w
  have hdiff : mfderiv I I (j : N → M') z (a - u) = mfderiv I I (j : N → M') z a - w := by
    rw [map_sub, hu]
  have hlin : mvfderiv I f (j z) (mfderiv I I (j : N → M') z a) =
      mvfderiv I f (j z) w + mvfderiv I f (j z) (mfderiv I I (j : N → M') z (a - u)) := by
    rw [hdiff, map_sub]
    ring
  have hbound := abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf g hmetric hL hf hfz
    (mfderiv I I (j : N → M') z (a - u))
  rw [hchain, hlin]
  linarith [neg_abs_le (mvfderiv I f (j z) (mfderiv I I (j : N → M') z (a - u)))]

end PerIndex

/-- Uniform convergence on `s` gives convergence along sequences in `s` and indices `σ k → ∞`. -/
theorem tendsto_sub_of_tendstoUniformlyOn {α : Type*} {F : ℕ → α → ℝ} {f : α → ℝ} {s : Set α}
    (hF : TendstoUniformlyOn F f atTop s) {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop) {z : ℕ → α}
    (hz : ∀ k, z k ∈ s) : Tendsto (fun k => F (σ k) (z k) - f (z k)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp
    (hσ.eventually (Metric.tendstoUniformlyOn_iff.mp hF ε hε))
  refine ⟨k₀, fun k hk => ?_⟩
  have h := hk₀ k hk (z k) (hz k)
  rw [Real.dist_eq] at h
  rwa [Real.dist_eq, sub_zero, abs_sub_comm]

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

/-- **Uniform metric comparison on compact sets.** For LFR14-shaped data (exhaustion and `C⁰`
convergence of the pulled-back chart coefficients), eventually `|d j_i X|²_{g_i} ≤ (1 + ε) |X|²_G`
for all `x ∈ C` and `X ∈ T_x N`. -/
theorem eventually_pullback_inner_le_of_isCompact {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (g : ∀ i, SmoothRiemannianMetric I (M i)) {K : ℕ} (hK : 1 ≤ K)
    (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    {C : Set N} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x ∈ C, ∀ X : TangentSpace I x,
      (g i).inner (j i x) (mfderiv I I (j i : N → M i) x X) (mfderiv I I (j i : N → M i) x X) ≤
        (1 + ε) * G.inner x X X := by
  by_contra hbad
  rw [Filter.not_eventually] at hbad
  obtain ⟨ψ, hψ, hψbad⟩ := Filter.extraction_of_frequently_atTop hbad
  simp only [not_forall, not_le, exists_prop] at hψbad
  choose x hxC X hX using hψbad
  have hXpos : ∀ k, 0 < G.inner (x k) (X k) (X k) := fun k => by
    rcases (DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg G (x k) (X k)).lt_or_eq
      with h | h
    · exact h
    · exfalso
      have hX0 : X k = 0 := by
        by_contra hne
        exact (G.pos (x k) (X k) hne).ne' h.symm
      have h1 := hX k
      simp [hX0] at h1
  set c : ℕ → ℝ := fun k => (Real.sqrt (G.inner (x k) (X k) (X k)))⁻¹ with hc
  set Y : ∀ k, TangentSpace I (x k) := fun k => c k • X k with hY
  have hcsq : ∀ k, c k * c k * G.inner (x k) (X k) (X k) = 1 := fun k => by
    rw [hc]
    dsimp only
    rw [← mul_inv, Real.mul_self_sqrt (hXpos k).le, inv_mul_cancel₀ (hXpos k).ne']
  have hYunit : ∀ k, G.inner (x k) (Y k) (Y k) = 1 := fun k => by
    rw [hY]
    dsimp only
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← hcsq k]
    ring
  have hYbad : ∀ k, 1 + ε < (g (ψ k)).inner (j (ψ k) (x k))
      (mfderiv I I (j (ψ k) : N → M (ψ k)) (x k) (Y k))
      (mfderiv I I (j (ψ k) : N → M (ψ k)) (x k) (Y k)) := fun k => by
    rw [hY]
    dsimp only
    simp only [map_smul, smul_apply, smul_eq_mul]
    have h1 := hX k
    have h2 := hcsq k
    have hc0 : 0 < c k * c k := by
      have : 0 < c k := inv_pos.mpr (Real.sqrt_pos.mpr (hXpos k))
      positivity
    nlinarith
  obtain ⟨xI, -, φ₁, hφ₁, hx₁⟩ := hC.tendsto_subseq hxC
  obtain ⟨YI, φ₂, hφ₂, hYlim⟩ := exists_subseq_tendsto_tangentBundle_of_inner_le hr G hx₁
    (fun k => Y (φ₁ k)) (B := 1) (fun k => (hYunit _).le)
  have hσ : Tendsto (fun k => ψ (φ₁ (φ₂ k))) atTop atTop :=
    (hψ.comp (hφ₁.comp hφ₂)).tendsto_atTop
  have hT3 := tendsto_pullback_inner_of_tendsto hr G g hK j hexh hconv hσ hYlim hYlim
  have hT2 := tendsto_inner_of_tendsto_tangentBundle hr G hYlim hYlim
  have hunit : G.inner xI YI YI = 1 :=
    tendsto_nhds_unique hT2 (tendsto_const_nhds.congr fun k => (hYunit _).symm)
  rw [hunit] at hT3
  have hge := ge_of_tendsto' hT3 fun k => (hYbad (φ₁ (φ₂ k))).le
  linarith

end Comparison

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
  [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **LFR18 → LFR20 step 2 / (LFR28.3) bridge.** LFR18's vertical field `V` (`hVdir`, `hVcont`), source
coordinates `η i` that are globally `(1 + σ)`-Lipschitz, differentiable along `j i (C)` and satisfy
LFR19's all-direction estimate (LFR19.1) against coordinates `U i` with `U i ∘ j i → t` uniformly on
compact sets give `D(η_i ∘ j_i)(V) ≥ 1 - σ - o(1)` uniformly on `C`. -/
theorem eventually_one_sub_lt_mvfderiv_vertical [∀ i, CompleteSpace (M i)]
    {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσ : 0 < σ) {C : Set N} (hC : IsCompact C) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    (hVcont : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I N)))
    (η U : ∀ i, M i → ℝ) (hηlip : ∀ i, LipschitzWith (Real.toNNReal (1 + σ)) (η i))
    (hηsmooth : ∀ᶠ i in atTop, ∀ x ∈ C, MDifferentiableAt I 𝓘(ℝ, ℝ) (η i) (j i x))
    (h19 : ∀ᶠ i in atTop, ∀ x ∈ C,
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i)
        {j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))} (j i x),
        |mvfderiv I (η i) (j i x) w -
          (U i (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))) - U i (j i x)) /
            dist (j i x) (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))))| < σ)
    (hU : ∀ C' : Set N, IsCompact C' →
      TendstoUniformlyOn (fun i x => U i (j i x)) (fun x => (Φ x).fst) atTop C') :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ C,
      1 - σ - ε < mvfderiv I (fun y => η i (j i y)) x (V x) := by
  intro ε hε
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hK1 : 1 ≤ K := by omega
  set sh : N → N := fun x => Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)) with hsh
  have hshc : Continuous sh := (isometry_vertical_shift Φ ℓ).continuous
  have hdsh : ∀ x, dist x (sh x) = ℓ := fun x => by
    rw [hsh, dist_vertical_shift Φ ℓ x, abs_of_pos hℓ]
  have hVunit : ∀ y, G.inner y (V y) (V y) = 1 := fun y => by
    have h : V y ∈ G.finiteMinimizingDirectionsTo {sh y} y := by
      rw [hVdir y]
      exact mem_singleton _
    exact h.1
  by_contra hbad
  rw [Filter.not_eventually] at hbad
  obtain ⟨ψ, hψ, hψbad⟩ := Filter.extraction_of_frequently_atTop
    (hbad.and_eventually (hηsmooth.and (h19.and (hexh C hC))))
  choose hneg hfact using hψbad
  simp only [not_forall, not_lt, exists_prop] at hneg
  choose x hxC hbadk using hneg
  have hψt := hψ.tendsto_atTop
  have hEnt : Nontrivial E := ⟨⟨(V (x 0) : E), 0, fun h0 => by
    have h1 := hVunit (x 0)
    rw [show V (x 0) = (0 : TangentSpace I (x 0)) from h0, map_zero] at h1
    exact zero_ne_one h1⟩⟩
  have : NeZero (Module.finrank ℝ E) := ⟨Module.finrank_pos.ne'⟩
  have harm : ∀ k, ∃ w : TangentSpace I (j (ψ k) (x k)),
      w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g (ψ k)) {j (ψ k) (sh (x k))}
        (j (ψ k) (x k)) := fun k =>
    exists_mem_finiteMinimizingDirectionsTo_singleton_of_riemannianEDistOf (g (ψ k)) (hmetric _) _ _
  choose w hw using harm
  obtain ⟨yInf, -, v, -, hvdir, -, φ, hφ, hy, hlim⟩ :=
    exists_subseq_minimizing_direction_limit_finite_of_isCompact (M := fun k => M (ψ k)) hr1 G
      hGnorm (fun k => g (ψ k)) (fun k => hmetric _) hK q (fun k => j (ψ k))
      (fun C hC => hψt.eventually (hexh C hC))
      (fun z L hL hLt => (hconv z L hL hLt).comp_subseq hψ)
      (fun R ε hε => hψt.eventually (hdist R ε hε))
      (fun a b ha hab => hψt.eventually (hcover a b ha hab))
      hC x hxC (hC.image hshc) (fun k => sh (x k)) (fun k => mem_image_of_mem sh (hxC k)) w hw
  obtain ⟨x0, v0⟩ := v
  have hxlim : Tendsto (fun k => x (φ k)) atTop (𝓝 x0) :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).tendsto _).comp hlim
  have hyeq : yInf = sh x0 := tendsto_nhds_unique hy ((hshc.tendsto _).comp hxlim)
  rw [hyeq, hVdir, mem_singleton_iff] at hvdir
  subst hvdir
  have hVlim : Tendsto (fun k => (⟨x (φ k), V (x (φ k))⟩ : TangentBundle I N)) atTop
      (𝓝 ⟨x0, V x0⟩) := (hVcont.tendsto x0).comp hxlim
  have hd := tendsto_tangentBundle_sub hVlim hlim
  have hψφ : StrictMono (fun k => ψ (φ k)) := hψ.comp hφ
  have hT3 := tendsto_pullback_inner_of_tendsto hr1 G g hK1 j hexh hconv hψφ.tendsto_atTop hd hd
  simp only [sub_self, map_zero] at hT3
  -- the quotient tends to one
  have hshC : IsCompact (sh '' C) := hC.image hshc
  obtain ⟨R, hR⟩ := (hC.union hshC).isBounded.subset_ball q
  have hU1 := tendsto_sub_of_tendstoUniformlyOn (hU C hC) hψφ.tendsto_atTop
    (z := fun k => x (φ k)) (fun k => hxC _)
  have hU2 := tendsto_sub_of_tendstoUniformlyOn (hU _ hshC) hψφ.tendsto_atTop
    (z := fun k => sh (x (φ k))) (fun k => mem_image_of_mem sh (hxC _))
  have hshfst : ∀ y, (Φ (sh y)).fst = (Φ y).fst + ℓ := fun y => by
    rw [hsh]
    simp only [Φ.apply_symm_apply, WithLp.toLp_fst]
  have ht1 : Tendsto (fun k => (Φ (x (φ k))).fst) atTop (𝓝 (Φ x0).fst) :=
    ((lipschitzWith_heightCoord Φ).continuous.tendsto _).comp hxlim
  have hnum : Tendsto (fun k => U (ψ (φ k)) (j (ψ (φ k)) (sh (x (φ k)))) -
      U (ψ (φ k)) (j (ψ (φ k)) (x (φ k)))) atTop (𝓝 ℓ) := by
    have h := (hU2.add ((ht1.add_const ℓ))).sub (hU1.add ht1)
    rw [zero_add, zero_add, add_sub_cancel_left] at h
    refine h.congr fun k => ?_
    simp only [hshfst]
    ring
  have hden : Tendsto (fun k => dist (j (ψ (φ k)) (x (φ k))) (j (ψ (φ k)) (sh (x (φ k)))))
      atTop (𝓝 ℓ) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp (hψφ.tendsto_atTop.eventually (hdist R δ hδ))
    refine ⟨k₁, fun k hk => ?_⟩
    have h := hk₁ k hk (x (φ k)) (hR (Or.inl (hxC _))) (sh (x (φ k)))
      (hR (Or.inr (mem_image_of_mem sh (hxC _))))
    rwa [hdsh, ← Real.dist_eq] at h
  have hQ := hnum.div hden hℓ.ne'
  rw [div_self hℓ.ne'] at hQ
  -- the error term
  have hE := ((Real.continuous_sqrt.tendsto 0).comp hT3).const_mul (1 + σ)
  rw [Real.sqrt_zero, mul_zero] at hE
  have hlimL := (hQ.sub_const σ).sub hE
  rw [sub_zero] at hlimL
  have hfin : 1 - σ ≤ 1 - σ - ε := le_of_tendsto' hlimL fun k => by
    have hz := (hfact (φ k)).2.2 (hxC (φ k))
    have h19k := abs_lt.mp ((hfact (φ k)).2.1 (x (φ k)) (hxC _) (w (φ k)) (hw (φ k)))
    have hper := sub_le_mvfderiv_comp_of_lipschitzWith (g (ψ (φ k))) (hmetric _) hK1 (j (ψ (φ k)))
      hz (by linarith : (0 : ℝ) ≤ 1 + σ) (hηlip _) ((hfact (φ k)).1 (x (φ k)) (hxC _))
      (V (x (φ k))) (w (φ k))
    have hb := hbadk (φ k)
    dsimp only at hper
    simp only [Pi.div_apply, hsh]
    refine le_trans ?_ hb
    refine le_trans ?_ hper
    exact sub_le_sub (by linarith [h19k.1]) (le_of_eq rfl)
  linarith

/-- **(LFR20.1) and (LFR28.3) in norm form.** Under the hypotheses of the bridge, the differential of
`f_i = η_i ∘ j_i` is close to the covector `dt = G(V, ·)` of the vertical field:
`‖d f_i − dt‖_G ≤ √(4σ + σ²) + ε` eventually, uniformly on `C` (polarization with the Riesz vector
of `d f_i` in `(T_x N, G)`; a bound, not convergence to zero, for fixed `σ`). -/
theorem eventually_abs_mvfderiv_sub_inner_vertical_le [∀ i, CompleteSpace (M i)]
    {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσ : 0 < σ) {C : Set N} (hC : IsCompact C) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    (hVcont : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I N)))
    (η U : ∀ i, M i → ℝ) (hηlip : ∀ i, LipschitzWith (Real.toNNReal (1 + σ)) (η i))
    (hηsmooth : ∀ᶠ i in atTop, ∀ x ∈ C, MDifferentiableAt I 𝓘(ℝ, ℝ) (η i) (j i x))
    (h19 : ∀ᶠ i in atTop, ∀ x ∈ C,
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i)
        {j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))} (j i x),
        |mvfderiv I (η i) (j i x) w -
          (U i (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))) - U i (j i x)) /
            dist (j i x) (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))))| < σ)
    (hU : ∀ C' : Set N, IsCompact C' →
      TendstoUniformlyOn (fun i x => U i (j i x)) (fun x => (Φ x).fst) atTop C') :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ C, ∀ X : TangentSpace I x,
      |mvfderiv I (fun y => η i (j i y)) x X - G.inner x (V x) X| ≤
        (Real.sqrt (4 * σ + σ ^ 2) + ε) * Real.sqrt (G.inner x X X) := by
  intro ε hε
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hK1 : 1 ≤ K := by omega
  set δ : ℝ := min 1 (ε ^ 2 / (6 + 2 * σ)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε ^ 2 / (6 + 2 * σ) := min_le_right _ _
  set ρ : ℝ := δ / (1 + σ) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hbr := eventually_one_sub_lt_mvfderiv_vertical hr G hGnorm g hmetric hK q j hexh hconv hdist
    hcover Φ hℓ hσ hC V hVdir hVcont η U hηlip hηsmooth h19 hU δ hδ0
  have hcmp := eventually_pullback_inner_le_of_isCompact hr1 G g hK1 j hexh hconv hC hρ0
  filter_upwards [hbr, hcmp, hηsmooth, hexh C hC] with i hbri hcmpi hsmi hsrci
  intro x hx X
  set a : TangentSpace I x →L[ℝ] ℝ := mvfderiv I (fun y => η i (j i y)) x with ha
  have hnorm : ∀ Y : TangentSpace I x, ‖Y‖ = Real.sqrt (G.inner x Y Y) := fun Y => by
    have h := hGnorm x Y
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (Real.sqrt_nonneg _)).mp h
  have hGnn : ∀ Y : TangentSpace I x, 0 ≤ G.inner x Y Y := fun Y =>
    DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg G x Y
  -- the differential is bounded by `1 + σ + δ`
  have hVunit : G.inner x (V x) (V x) = 1 := by
    have h : V x ∈ G.finiteMinimizingDirectionsTo
        {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x := by
      rw [hVdir x]
      exact mem_singleton _
    exact h.1
  have hEnt : Nontrivial E := ⟨⟨(V x : E), 0, fun h0 => by
    have h1 := hVunit
    rw [show V x = (0 : TangentSpace I x) from h0, map_zero] at h1
    exact zero_ne_one h1⟩⟩
  have : NeZero (Module.finrank ℝ E) := ⟨Module.finrank_pos.ne'⟩
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hjd : MDifferentiableAt I I (j i : N → M i) x := (j i).mdifferentiableAt hK0 (hsrci hx)
  have hbound : ∀ Y : TangentSpace I x, |a Y| ≤ (1 + σ + δ) * ‖Y‖ := fun Y => by
    have hchain : a Y = mvfderiv I (η i) (j i x) (mfderiv I I (j i : N → M i) x Y) :=
      mvfderiv_comp_apply x (hsmi x hx) hjd Y
    have hlip := abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf (g i) (hmetric i)
      (by linarith : (0 : ℝ) ≤ 1 + σ) (hηlip i) (hsmi x hx) (mfderiv I I (j i : N → M i) x Y)
    have hc := hcmpi x hx Y
    have hsq : Real.sqrt ((g i).inner (j i x) (mfderiv I I (j i : N → M i) x Y)
        (mfderiv I I (j i : N → M i) x Y)) ≤ (1 + ρ) * Real.sqrt (G.inner x Y Y) := by
      rw [show (1 + ρ) * Real.sqrt (G.inner x Y Y) = Real.sqrt ((1 + ρ) ^ 2 * G.inner x Y Y) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
      refine Real.sqrt_le_sqrt (hc.trans ?_)
      exact mul_le_mul_of_nonneg_right (by nlinarith) (hGnn Y)
    rw [hchain, hnorm]
    calc _ ≤ (1 + σ) * Real.sqrt ((g i).inner (j i x) (mfderiv I I (j i : N → M i) x Y)
          (mfderiv I I (j i : N → M i) x Y)) := hlip
      _ ≤ (1 + σ) * ((1 + ρ) * Real.sqrt (G.inner x Y Y)) :=
          mul_le_mul_of_nonneg_left hsq (by linarith)
      _ = (1 + σ + δ) * Real.sqrt (G.inner x Y Y) := by
          rw [hρ]
          field_simp
  -- the bundle inner product of `T_x N` is `G`
  have hinner : ∀ Y Z : TangentSpace I x, inner ℝ Y Z = G.inner x Y Z := fun Y Z => by
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, hnorm, hnorm,
      hnorm, Real.mul_self_sqrt (hGnn _), Real.mul_self_sqrt (hGnn _), Real.mul_self_sqrt (hGnn _),
      DifferentialGeometry.Geometry.Riemannian.Geodesic.inner_add_self_eq_finite G x Y Z]
    ring
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ (TangentSpace I x)
  set A : TangentSpace I x := (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm a with hA
  have hAapp : ∀ Y : TangentSpace I x, inner ℝ A Y = a Y := fun Y =>
    InnerProductSpace.toDual_symm_apply
  have hAnorm : ‖A‖ ≤ 1 + σ + δ := by
    rw [hA, LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun Y => by
      rw [Real.norm_eq_abs]
      exact hbound Y
  have hV1 : ‖V x‖ = 1 := by rw [hnorm, hVunit, Real.sqrt_one]
  have hAV : 1 - (σ + δ) ≤ inner ℝ A (V x) := by
    rw [hAapp]
    linarith [hbri x hx]
  have hsq := DifferentialGeometry.Geometry.Collapse.norm_sub_sq_le_of_inner_ge
    (by linarith : ‖A‖ ≤ 1 + (σ + δ)) hV1 hAV
  have hdiff : a X - G.inner x (V x) X = inner ℝ (A - V x) X := by
    rw [inner_sub_left, hAapp, hinner]
  have hsqrt : ‖A - V x‖ ≤ Real.sqrt (4 * σ + σ ^ 2) + ε := by
    have h1 : ‖A - V x‖ ≤ Real.sqrt (4 * (σ + δ) + (σ + δ) ^ 2) :=
      Real.le_sqrt_of_sq_le hsq
    have h2 : 4 * (σ + δ) + (σ + δ) ^ 2 ≤ (4 * σ + σ ^ 2) + ε ^ 2 := by
      have h3 : δ * (6 + 2 * σ) ≤ ε ^ 2 := by
        rw [le_div_iff₀ (by positivity)] at hδε
        linarith
      nlinarith
    have h4 : Real.sqrt ((4 * σ + σ ^ 2) + ε ^ 2) ≤ Real.sqrt (4 * σ + σ ^ 2) + ε := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have h5 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * σ + σ ^ 2)
      nlinarith [Real.sqrt_nonneg (4 * σ + σ ^ 2)]
    exact h1.trans ((Real.sqrt_le_sqrt h2).trans h4)
  rw [hdiff, ← hnorm]
  calc |inner ℝ (A - V x) X| ≤ ‖A - V x‖ * ‖X‖ := abs_real_inner_le_norm _ _
    _ ≤ (Real.sqrt (4 * σ + σ ^ 2) + ε) * ‖X‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)


end Bridge

end DifferentialGeometry.Geometry.Riemannian.Geodesic
