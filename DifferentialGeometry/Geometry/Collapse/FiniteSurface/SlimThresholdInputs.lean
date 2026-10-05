import DifferentialGeometry.Geometry.Collapse.ComparisonImageContainment
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimCoordinateClauses

/-!
# Inputs of LFR20's compactness frame that are not in the L-CONS merge

Blueprint LFR20 (master207A:26358), proof, first paragraph ("The factor is compact with diameter at
most `D` by LFR16") and step 3 (LFR14's strict-radius coverage), for the data of the L-CONS merge
(a limit `N`, comparison maps `J i`, distance comparison, normalized splittings `Φ i` with factor
diameter `≤ D`, an exact splitting `e : N ≃ᵢ ℓ²(ℝ × W)` tracked by `u_i ∘ J_i → t`):

* `dist_le_of_splitting_limit`: points of `N` with the same `t` are at distance `≤ D`;
* `splitting_factor_dist_le_of_limit`, `compactSpace_splitting_factor_of_limit`: `diam W ≤ D` and,
  `W` proper, `W` compact;
* `eventually_ball_subset_image_of_partialDiffeomorph`: coverage `B(j_i q, a) ⊆ j_i(B(q, b))`
  for `a < b`, from exhaustion and distance comparison (LFR10's containment for local
  diffeomorphisms).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric WithLp
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry

section Factor

variable {N W : Type*} [MetricSpace N] [MetricSpace W]
  {X : ℕ → Type*} [∀ i, MetricSpace (X i)] {Z : ℕ → Type*} [∀ i, MetricSpace (Z i)]

/-- **The factor diameter passes to the limit.** Two points of `N` with the same `t` are at
distance at most `D`. -/
theorem dist_le_of_splitting_limit (q : N) (J : ∀ i, N → X i) (p : ∀ i, X i)
    (hp : ∀ i, J i q = p i)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (J i x) (J i y) - dist x y| < ε)
    {a : ℝ} {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) {D : ℝ} (hD : ∀ i, ∀ y z : Z i, dist y z ≤ D)
    (e : N ≃ᵢ WithLp 2 (ℝ × W))
    (hU : ∀ C : Set N, IsCompact C →
      TendstoUniformlyOn (fun i x => ((Φ i).toFun (J i x)).fst) (fun x => (e x).fst) atTop C)
    {x y : N} (hxy : (e x).fst = (e y).fst) : dist x y ≤ D := by
  have hD0 : 0 ≤ D := (dist_nonneg).trans (hD 0 (b 0) (b 0))
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set R : ℝ := max (dist x q) (dist y q) + 1 with hR
  have hxR : x ∈ ball q R := mem_ball.mpr (by rw [hR]; linarith [le_max_left (dist x q) (dist y q)])
  have hyR : y ∈ ball q R := mem_ball.mpr (by rw [hR]; linarith [le_max_right (dist x q) (dist y q)])
  have hqR : q ∈ ball q R := mem_ball_self (by rw [hR]; positivity)
  have hR0 : 0 < R := by rw [hR]; positivity
  have hδsmall : ∀ᶠ i in atTop, δ i < min (ε / 8) (1 / (R + ε + 2)) :=
    hδ.eventually (gt_mem_nhds (lt_min (by positivity) (by positivity)))
  have hUxy := Metric.tendstoUniformlyOn_iff.mp (hU {x, y} ((Set.finite_singleton y).insert x
    |>.isCompact)) (ε / 8) (by positivity)
  obtain ⟨i, hi1, hi2, hi3⟩ :=
    ((hdist R (ε / 8) (by positivity)).and (hδsmall.and hUxy)).exists
  have hδi := (Φ i).error_pos
  have hδε : δ i < ε / 8 := hi2.trans_le (min_le_left _ _)
  have hδR : δ i < 1 / (R + ε + 2) := hi2.trans_le (min_le_right _ _)
  have hinv : R + ε + 2 < (δ i)⁻¹ := by
    rw [one_div] at hδR
    exact (lt_inv_comm₀ (by positivity) hδi).mpr hδR
  have hJx : J i x ∈ ball (p i) (δ i)⁻¹ := by
    have h := abs_lt.mp (hi1 x hxR q hqR)
    rw [hp i] at h
    rw [mem_ball]
    linarith [mem_ball.mp hxR]
  have hJy : J i y ∈ ball (p i) (δ i)⁻¹ := by
    have h := abs_lt.mp (hi1 y hyR q hqR)
    rw [hp i] at h
    rw [mem_ball]
    linarith [mem_ball.mp hyR]
  have hfx := hi3 x (mem_insert x {y})
  have hfy := hi3 y (mem_insert_of_mem x rfl)
  rw [Real.dist_eq] at hfx hfy
  have hfst : |((Φ i).toFun (J i x)).fst - ((Φ i).toFun (J i y)).fst| ≤ ε / 4 := by
    have h1 := abs_sub_lt_iff.mp hfx
    have h2 := abs_sub_lt_iff.mp hfy
    rw [abs_le]
    constructor <;> linarith
  have hΦ : dist ((Φ i).toFun (J i x)) ((Φ i).toFun (J i y)) ≤ ε / 4 + D := by
    refine (dist_withLp_le_sqrt hfst (hD i _ _)).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hdis := abs_le.mp ((Φ i).distortion _ hJx _ hJy)
  have hxy' := abs_lt.mp (hi1 x hxR y hyR)
  linarith

/-- **`diam W ≤ D`.** -/
theorem splitting_factor_dist_le_of_limit (q : N) (J : ∀ i, N → X i) (p : ∀ i, X i)
    (hp : ∀ i, J i q = p i)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (J i x) (J i y) - dist x y| < ε)
    {a : ℝ} {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) {D : ℝ} (hD : ∀ i, ∀ y z : Z i, dist y z ≤ D)
    (e : N ≃ᵢ WithLp 2 (ℝ × W))
    (hU : ∀ C : Set N, IsCompact C →
      TendstoUniformlyOn (fun i x => ((Φ i).toFun (J i x)).fst) (fun x => (e x).fst) atTop C)
    (w₁ w₂ : W) : dist w₁ w₂ ≤ D := by
  have h := dist_le_of_splitting_limit q J p hp hdist Φ hδ hD e hU
    (x := e.symm (toLp 2 ((0 : ℝ), w₁))) (y := e.symm (toLp 2 ((0 : ℝ), w₂)))
    (by rw [e.apply_symm_apply, e.apply_symm_apply]; rfl)
  rw [e.symm.dist_eq] at h
  have hsq := WithLp.prod_dist_sq_eq_add_sq (toLp 2 ((0 : ℝ), w₁)) (toLp 2 ((0 : ℝ), w₂))
  have h1 : dist (toLp 2 ((0 : ℝ), w₁)).fst (toLp 2 ((0 : ℝ), w₂)).fst = 0 := dist_self _
  have h2 : dist (toLp 2 ((0 : ℝ), w₁)).snd (toLp 2 ((0 : ℝ), w₂)).snd = dist w₁ w₂ := rfl
  rw [h1, h2] at hsq
  have heq : dist (toLp 2 ((0 : ℝ), w₁)) (toLp 2 ((0 : ℝ), w₂)) = dist w₁ w₂ := by
    have := dist_nonneg (x := toLp 2 ((0 : ℝ), w₁)) (y := toLp 2 ((0 : ℝ), w₂))
    nlinarith [dist_nonneg (x := w₁) (y := w₂)]
  rw [heq] at h
  exact h

/-- **The factor is compact** (proper, of diameter `≤ D`). -/
theorem compactSpace_splitting_factor_of_limit [ProperSpace W] [Nonempty W] (q : N)
    (J : ∀ i, N → X i) (p : ∀ i, X i) (hp : ∀ i, J i q = p i)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (J i x) (J i y) - dist x y| < ε)
    {a : ℝ} {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) {D : ℝ} (hD : ∀ i, ∀ y z : Z i, dist y z ≤ D)
    (e : N ≃ᵢ WithLp 2 (ℝ × W))
    (hU : ∀ C : Set N, IsCompact C →
      TendstoUniformlyOn (fun i x => ((Φ i).toFun (J i x)).fst) (fun x => (e x).fst) atTop C) :
    CompactSpace W := by
  obtain ⟨w⟩ := ‹Nonempty W›
  refine ⟨(isCompact_closedBall w D).of_isClosed_subset isClosed_univ fun z _ => ?_⟩
  exact mem_closedBall.mpr (splitting_factor_dist_le_of_limit q J p hp hdist Φ hδ hD e hU z w)

end Factor

section Coverage

open DifferentialGeometry.Geometry.Metric

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type*} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (TangentBundle I (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Coverage from exhaustion and distance comparison** (LFR10 for the comparison maps of a
finite Cheeger–Gromov limit). -/
theorem eventually_ball_subset_image_of_partialDiffeomorph
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace H N] {K : ℕ} (q : N)
    (j : ∀ i, PartialDiffeomorph I I N (X i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε) :
    ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → X i) '' ball q b := by
  intro a b _ hab
  have hloc : ∀ᶠ i in atTop,
      IsLocalDiffeomorphOn I I (K : ℕ∞ω) (j i : N → X i) (ball q b) := by
    filter_upwards [hexh (closedBall q b) (isCompact_closedBall q b)] with i hi
    exact fun x => (j i).isLocalDiffeomorphAt I I (K : ℕ∞ω) (hi (ball_subset_closedBall x.2))
  exact eventually_riemannian_ball_subset_image_of_localDiffeomorph g hmetric
    (fun i => (j i : N → X i)) q (fun i => j i q) (fun _ => rfl) hloc (hdist b) hab

end Coverage

end DifferentialGeometry.Geometry.Collapse
