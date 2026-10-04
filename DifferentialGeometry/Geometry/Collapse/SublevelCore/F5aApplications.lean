import DifferentialGeometry.Geometry.Collapse.SublevelCore.GradientBand
import DifferentialGeometry.Geometry.Collapse.SublevelCore.DirectionMargin
import DifferentialGeometry.Geometry.Collapse.SublevelCore.CompactTransfer
import DifferentialGeometry.Geometry.Metric.Comparison.BufferedEmbedding
import DifferentialGeometry.Analysis.InnerProductSpace.BilinearConormalStability
import DifferentialGeometry.Geometry.Collapse.SublevelCore.RadialGraphIsotopy

/-!
# Consumers of the first half of family F5 (LC32–LC46)

* `conormal_scalar_regression` (LC40 binding): the bilinear-form conormal test on `ℝ` with the
  metric `h = (1 + δ) g`, `δ = 1/2`, and the exact budget `σ = 0`.
* `radial_inner_gradient_pos_of_direction_margin` (LC44 applied to an LC30 radial function):
  smoothness on an open set gives differentiability, so the radial gradient pairs positively
  with any field obeying a strict point-direction margin. The blueprint-shaped LC44 statement
  (open `W`, `F` smooth on `W`) is replayed as an `example`; continuity of `Z` is not needed.
* `buffered_embedding_of_complete` (LC39 with completeness of the source instead of compactness
  of the closed ball, PC setting on `N`).
* `radialSublevel_band_package` (LC32 + LC33 for the same radial function).
* `radialSublevels_isotopic` (LC33 + LC35): for the LC30 radial function all sublevels
  `A_ρ`, `ρ ∈ [1/5, 2]`, are smoothly ambient isotopic, through the gradient-product flow.
* `compact_alternative_sublevel_type` (LC43 + LC38, compact alternative): under the LC43
  hypotheses every radial sublevel `A_ρ`, `ρ ≥ 1/5`, is the whole manifold and the model
  embedding is a diffeomorphism.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Collapse

/-- LC40 binding regression on `ℝ`: `g(u,v) = uv`, `h = (3/2) g`, `β = ξ = id`. -/
theorem conormal_scalar_regression :
    0 < (ContinuousLinearMap.id ℝ ℝ) (2 / 3) := by
  have hG : (ContinuousLinearMap.mul ℝ ℝ) 1 = ContinuousLinearMap.id ℝ ℝ := by
    ext; simp
  have hH : ((3 / 2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ) (2 / 3) = ContinuousLinearMap.id ℝ ℝ := by
    ext; norm_num
  exact BilinearConormal.apply_representer_pos (V := ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    ((3 / 2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ)
    (fun u v => by simp [mul_comm]) (fun u v => by simp [mul_comm])
    (fun v hv => by simpa using mul_self_pos.mpr hv) (δ := 1 / 2) (σ := 0) (m := 1)
    (by norm_num) (by norm_num)
    (fun v => by simp; nlinarith [mul_self_nonneg v])
    (fun v => by simp; nlinarith [mul_self_nonneg v])
    (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) (b := 1) hG hH (by norm_num)
    (by simp) (fun v => by simp) (by norm_num)

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

section PC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- LC44 for the LC30 radial function: on its smooth region away from `p`, the radial gradient
pairs positively with any vector of length `≤ B` making the margin `a` with every inward unit
minimizing direction, as soon as `εB < a`. -/
theorem radial_inner_gradient_pos_of_direction_margin (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0}
    (hlip : LipschitzWith ε (fun x => η x - dist p x)) {W : Set M} (hW : IsOpen W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {q : M} (hq : q ∈ W) (hpq : p ≠ q)
    {Z : TangentSpace I q} {a B : ℝ} (hZB : √(g.inner q Z Z) ≤ B)
    (hdir : ∀ u ∈ inwardMinimizingDirections (I := I) g hEnorm p q, g.inner q Z u ≤ -a)
    (hmargin : ε * B < a) :
    0 < g.inner q (gradientFun (I := I) g η q) Z :=
  inner_gradientFun_pos_of_lipschitz_sub_dist g hEnorm hpq
    ((hηW.contMDiffAt (hW.mem_nhds hq)).mdifferentiableAt (by simp)) hlip hZB hdir hmargin

/-- LC44 in the blueprint's form (open `W ⊆ M \ {p}`, `F` smooth on `W`, a field `Z` on `W`).
The blueprint's continuity of `Z` is not needed and is omitted. -/
example (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (W : Set M) (hW : IsOpen W) (hpW : p ∉ W) (F : M → ℝ) (hF : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F W)
    (ε : ℝ≥0) (hlip : LipschitzWith ε (fun x => F x - dist p x))
    (Z : (x : M) → TangentSpace I x) (a B : ℝ)
    (hZB : ∀ q ∈ W, √(g.inner q (Z q) (Z q)) ≤ B)
    (hdir : ∀ q ∈ W, ∀ u ∈ inwardMinimizingDirections (I := I) g hEnorm p q,
      g.inner q (Z q) u ≤ -a) :
    ∀ q ∈ W, a - ε * B ≤ mvfderiv (I := I) F q (Z q) := fun q hq =>
  sub_mul_le_mvfderiv_of_lipschitz_sub_dist g hEnorm (fun h => hpW (by rw [h]; exact hq))
    ((hF.contMDiffAt (hW.mem_nhds hq)).mdifferentiableAt (by simp)) hlip (hZB q hq) (hdir q hq)

/-- LC32 and LC33 for one LC30 radial function: the band is compact, the product coordinates
over `η⁻¹(1)` exist, and the distance grows along them. -/
theorem radialSublevel_band_package (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x)) :
    IsCompact (η ⁻¹' Icc (1 / 8 : ℝ) 3) ∧
      ∃ Φ : ℝ → Diffeomorph I I M M ∞, ∀ x, η x = 1 → ∀ s t, 1 / 8 ≤ s → s ≤ t → t ≤ 3 →
        η (Φ (t - 1) x) = t ∧
        (1 - 2 * (ε : ℝ)) / (1 - ε) * (t - s) ≤
          dist p (Φ (t - 1) x) - dist p (Φ (s - 1) x) := by
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  have : ProperSpace M :=
    ⟨fun x r => DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall
      (I := I) g hEnorm x r⟩
  obtain ⟨Φ, -, -, -, -, hval, -, -, -, htrack, -⟩ :=
    radialBand_gradient_product g hEnorm hε1 he hclose hlip hW hCW hηW hgrad
  refine ⟨isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc, Φ, ?_⟩
  intro x hx s t hs hst ht
  refine ⟨?_, htrack x hx s t hs hst ht⟩
  have h := hval x (by rw [hx]; norm_num) t ⟨hs.trans hst, ht⟩
  rwa [hx] at h

/-- LC33 + LC35: all radial sublevels `A_ρ`, `ρ ∈ [1/5, 2]`, of an LC30 radial function are
smoothly ambient isotopic, by isotopies supported in one compact subset of `η⁻¹(1/8, 3)`. -/
theorem radialSublevels_isotopic (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {ρ ρ' : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) (hρ' : ρ' ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ G : ℝ → Diffeomorph I I M M ∞,
      G 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G q.1 q.2) ∧
      (∃ T : Set M, IsCompact T ∧ T ⊆ η ⁻¹' Ioo (1 / 8) 3 ∧
        ∀ t x, x ∉ T → G t x = x ∧ (G t).symm x = x) ∧
      G 1 '' {x | η x ≤ ρ'} = {x | η x ≤ ρ} := by
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  have : ProperSpace M :=
    ⟨fun x r => DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall
      (I := I) g hEnorm x r⟩
  have hK : IsCompact (η ⁻¹' Icc (1 / 8 : ℝ) 3) :=
    isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc
  have hKann := radialBand_subset_annulus hclose he
  obtain ⟨Φ, hΦ0, hΦc, -, hΦadd, hval, -⟩ :=
    radialBand_gradient_product g hEnorm hε1 he hclose hlip hW hCW hηW hgrad
  obtain ⟨G, hG0, hGc, -, hT, himg⟩ := exists_band_sublevel_isotopy_of_contMDiffOn hη hW hηW
    (by norm_num : (1 / 8 : ℝ) < 3) (⟨by norm_num, by norm_num⟩ : (1 : ℝ) ∈ Icc (1 / 8 : ℝ) 3)
    (⟨by linarith [hρ.1], by linarith [hρ.2]⟩ : ρ ∈ Ioo (1 / 8 : ℝ) 3)
    (⟨by linarith [hρ'.1], by linarith [hρ'.2]⟩ : ρ' ∈ Ioo (1 / 8 : ℝ) 3) hK
    (fun x hx => hCW x (hKann hx).1.le (hKann hx).2.le) Φ hΦc hΦadd
    (fun x => by rw [hΦ0]; rfl) hval
  exact ⟨G, hG0, hGc, hT, himg⟩

end PC

section Buffered

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsRiemannianManifold I N] [CompleteSpace N]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]

/-- LC39 for a complete source (compactness of the closed `L`-ball by Hopf–Rinow). -/
theorem buffered_embedding_of_complete (h : SmoothRiemannianMetric I N)
    (hEnorm : IsMetricNorm (I := I) (M := N) h) (g : SmoothRiemannianMetric I M)
    (j : PartialDiffeomorph I I N M ∞) (n : N) {L lam : ℝ} (hL : 0 < L) (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1) (hsrc : riemannianClosedBallOf h n L ⊆ j.source)
    (hlower : ∀ z ∈ riemannianClosedBallOf h n L, ∀ v : TangentSpace I z,
      (1 - lam) ^ 2 * h.inner z v v ≤
        g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v))
    (hupper : ∀ z ∈ riemannianClosedBallOf h n L, ∀ v : TangentSpace I z,
      g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v) ≤
        (1 + lam) ^ 2 * h.inner z v v) :
    riemannianBallOf g (j n) ((1 - lam) * L) ⊆ (j : N → M) '' riemannianBallOf h n L ∧
      ∀ x, riemannianEDistOf h n x < ENNReal.ofReal L →
        ENNReal.ofReal (1 - lam) * riemannianEDistOf h n x ≤ riemannianEDistOf g (j n) (j x) ∧
        riemannianEDistOf g (j n) (j x) ≤ ENNReal.ofReal (1 + lam) * riemannianEDistOf h n x := by
  have hball : riemannianClosedBallOf h n L = Metric.closedBall n L := by
    ext y
    change riemannianEDistOf h n y ≤ ENNReal.ofReal L ↔ y ∈ Metric.closedBall n L
    rw [riemannianEDistOf_eq_riemannianEDist h hEnorm, ← IsRiemannianManifold.out (I := I),
      edist_dist, ENNReal.ofReal_le_ofReal_iff hL.le, Metric.mem_closedBall, dist_comm]
  have hcpt : IsCompact (riemannianClosedBallOf h n L) := by
    rw [hball]
    exact DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall (I := I) h hEnorm n L
  exact ⟨riemannianBallOf_subset_image_ball_of_buffered h g j n hlam1 hcpt hsrc hlower,
    fun x hx => ⟨le_riemannianEDistOf_map_of_buffered h g j n hlam1 hcpt hsrc hlower hx,
      riemannianEDistOf_map_le_of_buffered h g j n hL hlam0 hsrc hupper hx⟩⟩

end Buffered

section Compact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N M : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- LC43 + LC38 (compact alternative): every radial sublevel `A_ρ`, `ρ ≥ 1/5`, is all of `M`,
and the model embedding is a diffeomorphism `N ≃ M`. -/
theorem compact_alternative_sublevel_type [CompactSpace N] [Nonempty N] [ConnectedSpace M]
    [T2Space M] (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (j : PartialDiffeomorph I I N M ∞) (hsrc : j.source = univ)
    (hupper : ∀ z (v : TangentSpace I z),
      g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v) ≤
        4 * h.inner z v v)
    (n : N) {D R e : ℝ} (hR : 0 < R) (hD0 : 0 ≤ D)
    (hD : ∀ x, riemannianEDistOf h n x ≤ ENNReal.ofReal D)
    {η : M → ℝ} (hη : ∀ y, |η y - (riemannianEDistOf g (j n) y).toReal / R| < e)
    (hsmall : 2 * D / R + e < 1 / 5) :
    (∀ ρ : ℝ, 1 / 5 ≤ ρ → {y | η y ≤ ρ} = univ) ∧
      ∃ d : Diffeomorph I I N M ∞, ∀ x, d x = j x :=
  ⟨fun _ hρ => sublevel_eq_univ_of_lt_fifth
      (radial_lt_fifth_of_compact_model h g j hsrc hupper n hR hD0 hD hη hsmall) hρ,
    exists_diffeomorph_of_compactSpace j hsrc⟩

end Compact

end DifferentialGeometry.Geometry.Collapse
