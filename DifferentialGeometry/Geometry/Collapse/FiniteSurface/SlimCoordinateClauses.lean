import DifferentialGeometry.Geometry.Collapse.RankOneValueCoordinates
import DifferentialGeometry.Geometry.Collapse.RiemannianOutwardPoint
import DifferentialGeometry.Geometry.Comparison.Soul.SoulAngles
import DifferentialGeometry.Geometry.Metric.L2Product

/-!
# LFR20: the clauses that hold for EVERY coordinate `η` of LFR19

Blueprint LFR20 (master207A:26358), items 2 and 4 and the enclosure (LFR20.2) of step 3. Let
`α = (u, v) : M → ℝ × Y` be a normalized `(1, β)`-splitting (`KleinerLottApprox`) with
`d(v, y₀) ≤ D`, and let `η` be any function with LFR19's displayed estimates on `B(p, L)`:
`|η - u| < e` and the all-direction estimate (LFR19.1). Then, with no limit argument:

* `dist_le_of_abs_fst_le`, `dist_le_of_abs_coord_le`: (LFR20.2) `|η x| ≤ c` forces
  `d(p, x) ≤ √((c + e)² + D²) + β`;
* `exists_unit_lt_mvfderiv_of_rankOne`: at every `x ∈ B(p, r)` some unit `w` has
  `dη_x(w) > (2L - 2β)/(2L + 3β) - σ` (the shifted test point `α(x) + (2L, 0)` and (LFR19.1));
* `isPreconnected_ball_of_complete`, `Icc_subset_image_ball_of_rankOne`: `η(B(p, L))` contains
  `[-(c - 2β - e), c - 2β - e]` whenever `c + 3β < L`;
* `isProperMap_slabCoord`: `η : {x ∈ B(p, L) | |η x| < a} → (-a, a)` is proper once the slab is
  enclosed in a compact ball `B̄(p, r)`, `r < L`;
* `contMDiff_indicator_comp_of_enclosure`: item 4, a smooth profile `ψ` of `η` vanishing for
  `|s| > c` extends by zero from `B(p, L)` to a smooth compactly supported function on `M`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

section L2

variable {Y : Type*} [MetricSpace Y]

/-- The first coordinate of an `ℓ²` product with `ℝ` is `1`-Lipschitz. -/
theorem abs_fst_sub_le_dist_withLp (u v : WithLp 2 (ℝ × Y)) : |u.fst - v.fst| ≤ dist u v := by
  have h := WithLp.prod_dist_sq_eq_add_sq u v
  rw [← Real.dist_eq]
  have h0 : 0 ≤ dist u.snd v.snd ^ 2 := sq_nonneg _
  nlinarith [dist_nonneg (x := u) (y := v), dist_nonneg (x := u.fst) (y := v.fst)]

/-- An `ℓ²` distance bound from bounds on the two coordinates. -/
theorem dist_withLp_le_sqrt {u v : WithLp 2 (ℝ × Y)} {c D : ℝ} (hc : |u.fst - v.fst| ≤ c)
    (hD : dist u.snd v.snd ≤ D) : dist u v ≤ Real.sqrt (c ^ 2 + D ^ 2) := by
  have h := WithLp.prod_dist_sq_eq_add_sq u v
  rw [← Real.sqrt_sq (dist_nonneg (x := u) (y := v)), h]
  apply Real.sqrt_le_sqrt
  have h1 : dist u.fst v.fst ^ 2 ≤ c ^ 2 := by
    rw [Real.dist_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have h2 : dist u.snd v.snd ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ dist_nonneg hD 2
  linarith

end L2

section Metric

variable {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y]

/-- **(LFR20.2), metric kernel.** For a normalized splitting `α` with factor within `D` of `y₀`,
`|u(x)| ≤ c` forces `d(x, p) ≤ √(c² + D²) + β`. -/
theorem dist_le_of_abs_fst_le {p : X} {y₀ : Y} {β D c : ℝ}
    (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β) (hD : ∀ y : Y, dist y y₀ ≤ D)
    {x : X} (hx : x ∈ ball p β⁻¹) (hc : |(α.toFun x).fst| ≤ c) :
    dist x p ≤ Real.sqrt (c ^ 2 + D ^ 2) + β := by
  have hrad := α.radial_error x hx
  have hq : dist (α.toFun x) (WithLp.toLp 2 ((0 : ℝ), y₀)) ≤ Real.sqrt (c ^ 2 + D ^ 2) := by
    apply dist_withLp_le_sqrt
    · simpa using hc
    · simpa using hD (α.toFun x).snd
  have := (abs_le.mp hrad).1
  linarith

/-- **(LFR20.2) for a coordinate `η` with value error `e`.** -/
theorem dist_le_of_abs_coord_le {p : X} {y₀ : Y} {β D c e L : ℝ}
    (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β) (hD : ∀ y : Y, dist y y₀ ≤ D)
    {η : X → ℝ} (hval : ∀ x ∈ ball p L, |η x - (α.toFun x).fst| < e) (hLβ : L ≤ β⁻¹)
    {x : X} (hx : x ∈ ball p L) (hc : |η x| ≤ c) :
    dist x p ≤ Real.sqrt ((c + e) ^ 2 + D ^ 2) + β := by
  refine dist_le_of_abs_fst_le α hD (ball_subset_ball hLβ hx) ?_
  have h1 := hval x hx
  have h2 := abs_sub_abs_le_abs_sub (α.toFun x).fst (η x)
  rw [abs_sub_comm] at h2
  linarith

/-- **LFR20 properness, kernel.** If the slab `{x ∈ B(p, L) | |η x| < a}` lies in a compact ball
`B̄(p, r)`, `r < L`, then `η` restricted to it is a proper map onto `(-a, a)`. -/
theorem isProperMap_slabCoord {η : X → ℝ} (hη : Continuous η) {p : X} {L a r : ℝ}
    (hr : r < L) (hcpt : IsCompact (closedBall p r))
    (hencl : ∀ x ∈ ball p L, |η x| < a → dist x p ≤ r) :
    IsProperMap (fun x : {x // x ∈ ball p L ∧ |η x| < a} =>
      (⟨η x, abs_lt.mp x.2.2⟩ : Ioo (-a) a)) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(hη.comp continuous_subtype_val).subtype_mk _, fun K hK => ?_⟩
  rw [Subtype.isCompact_iff]
  have hK' : IsCompact ((Subtype.val : Ioo (-a) a → ℝ) '' K) := hK.image continuous_subtype_val
  have heq : (Subtype.val : {x // x ∈ ball p L ∧ |η x| < a} → X) ''
      ((fun x : {x // x ∈ ball p L ∧ |η x| < a} =>
        (⟨η x, abs_lt.mp x.2.2⟩ : Ioo (-a) a)) ⁻¹' K) =
      closedBall p r ∩ η ⁻¹' ((Subtype.val : Ioo (-a) a → ℝ) '' K) := by
    ext y
    constructor
    · rintro ⟨⟨y, hy⟩, hyK, rfl⟩
      exact ⟨mem_closedBall.mpr (hencl y hy.1 hy.2), ⟨_, hyK, rfl⟩⟩
    · rintro ⟨hyr, ⟨k, hk, hky⟩⟩
      have hya : |η y| < a := by rw [← hky]; exact abs_lt.mpr k.2
      have hyL : y ∈ ball p L := mem_ball.mpr ((mem_closedBall.mp hyr).trans_lt hr)
      refine ⟨⟨y, hyL, hya⟩, ?_, rfl⟩
      change (⟨η y, abs_lt.mp hya⟩ : Ioo (-a) a) ∈ K
      have hk' : (⟨η y, abs_lt.mp hya⟩ : Ioo (-a) a) = k := Subtype.ext hky.symm
      rw [hk']
      exact hk
  rw [heq]
  exact hcpt.inter_right (hK'.isClosed.preimage hη)

end Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- **Item 4, kernel.** A smooth profile `ψ` vanishing for `|s| > c`, composed with a coordinate
`η` smooth on a neighbourhood of `B(p, L)` whose `c`-slab is enclosed in a compact ball
`B̄(p, r)`, `r < L`, extends by zero to a smooth compactly supported function on `M`, with
topological support in the enclosed slab. -/
theorem contMDiff_indicator_comp_of_enclosure {η : M → ℝ} {O : Set M} (hO : IsOpen O)
    {p : M} {L c r : ℝ} (hLO : ball p L ⊆ O) (hη : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O)
    (hηc : Continuous η) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : ∀ s, c < |s| → ψ s = 0)
    (hr : r < L) (hcpt : IsCompact (closedBall p r))
    (hencl : ∀ x ∈ ball p L, |η x| ≤ c → dist x p ≤ r) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ ((ball p L).indicator (ψ ∘ η)) ∧
      HasCompactSupport ((ball p L).indicator (ψ ∘ η)) ∧
      tsupport ((ball p L).indicator (ψ ∘ η)) ⊆ {x | dist x p ≤ r ∧ |η x| ≤ c} := by
  set χ := (ball p L).indicator (ψ ∘ η) with hχ
  have hS : IsClosed {x : M | dist x p ≤ r ∧ |η x| ≤ c} :=
    (isClosed_le (continuous_id.dist continuous_const) continuous_const).inter
      (isClosed_le (continuous_abs.comp hηc) continuous_const)
  have hsupp : Function.support χ ⊆ {x | dist x p ≤ r ∧ |η x| ≤ c} := by
    intro x hx
    by_cases hxL : x ∈ ball p L
    · have hne : ψ (η x) ≠ 0 := by
        rw [Function.mem_support, hχ, Set.indicator_of_mem hxL] at hx
        exact hx
      have hle : |η x| ≤ c := by
        by_contra h
        exact hne (hψc _ (not_le.mp h))
      exact ⟨hencl x hxL hle, hle⟩
    · exact absurd (Set.indicator_of_notMem hxL _) hx
  have hts : tsupport χ ⊆ {x | dist x p ≤ r ∧ |η x| ≤ c} := closure_minimal hsupp hS
  refine ⟨contMDiff_of_tsupport fun x hx => ?_, ?_, hts⟩
  · have hxL : x ∈ ball p L := mem_ball.mpr ((hts hx).1.trans_lt hr)
    have hev : ψ ∘ η =ᶠ[𝓝 x] χ := by
      filter_upwards [isOpen_ball.mem_nhds hxL] with y hy
      rw [hχ, Set.indicator_of_mem hy]
    have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (ψ ∘ η) x :=
      hψ.contMDiff.contMDiffAt.comp x
        ((hη x (hLO hxL)).contMDiffAt (hO.mem_nhds (hLO hxL)))
    exact hcomp.congr_of_eventuallyEq hev.symm
  · exact IsCompact.of_isClosed_subset hcpt (isClosed_tsupport χ)
      (hts.trans fun x hx => mem_closedBall.mpr hx.1)

/-- A metric ball of a complete Riemannian manifold is preconnected (radial geodesics). -/
theorem isPreconnected_ball_of_complete (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (L : ℝ) : IsPreconnected (ball p L) := by
  refine isPreconnected_of_forall p fun y hy => ?_
  have hpL : p ∈ ball p L := mem_ball_self ((dist_nonneg).trans_lt (mem_ball'.mp hy))
  by_cases hyp : y = p
  · subst hyp
    exact ⟨{y}, singleton_subset_iff.mpr hy, rfl, rfl, isPreconnected_singleton⟩
  have hd : 0 < dist p y := dist_pos.mpr (Ne.symm hyp)
  obtain ⟨w, hw, hwend⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm p y
    (by rw [toReal_riemannianEDist_eq_dist]; exact hd)
  rw [toReal_riemannianEDist_eq_dist] at hwend
  set γ := intrinsicGeodesic g hEnorm p w with hγ
  have hγc : Continuous γ := intrinsicGeodesic_continuous g hEnorm p w
  refine ⟨γ '' Icc 0 (dist p y), ?_, ⟨0, ⟨le_rfl, hd.le⟩, intrinsicGeodesic_zero g hEnorm p w⟩,
    ⟨dist p y, ⟨hd.le, le_rfl⟩, hwend⟩, isPreconnected_Icc.image _ hγc.continuousOn⟩
  rintro _ ⟨t, ht, rfl⟩
  have h := dist_intrinsicGeodesic_le_mul g hEnorm p w ht.1
  rw [intrinsicGeodesic_zero, hw, Real.sqrt_one, one_mul, sub_zero] at h
  rw [mem_ball, dist_comm]
  exact h.trans_lt ((ht.2.trans_eq (dist_comm p y)).trans_lt (mem_ball.mp hy))

/-- **LFR20, the derivative clause.** For any `η` with LFR19's all-direction estimate (LFR19.1)
(tested segments from `B(p, L)` to `B(p, T)` of length `> L`), every `x ∈ B(p, r)`, `r ≤ L`, has a
unit direction `w` (towards a source point over `α(x) + (2L, 0)`) with
`dη_x(w) > (2L - 2β)/(2L + 3β) - σ`. -/
theorem exists_unit_lt_mvfderiv_of_rankOne (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β L T σ r : ℝ}
    (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β) {η : M → ℝ}
    (h19 : ∀ x ∈ ball p L, ∀ x' ∈ ball p T, L < dist x x' →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x x') = x' →
      |mvfderiv (I := I) η x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ)
    (hrL : r ≤ L) (hL3 : 3 * β < L) (hT : r + 2 * L + 3 * β < T)
    (hβ : r + 2 * L + 2 * β < β⁻¹) {x : M} (hx : x ∈ ball p r) :
    ∃ w : TangentSpace I x, g.inner x w w = 1 ∧
      (2 * L - 2 * β) / (2 * L + 3 * β) - σ < mvfderiv (I := I) η x w := by
  have hβ0 := α.error_pos
  have hr0 : 0 ≤ r := dist_nonneg.trans (mem_ball.mp hx).le
  have hxβ : x ∈ ball p β⁻¹ := ball_subset_ball (by linarith) hx
  set y : WithLp 2 (ℝ × Y) :=
    WithLp.toLp 2 ((α.toFun x).fst + 2 * L, (α.toFun x).snd) with hy
  have hyx : dist y (α.toFun x) ≤ 2 * L := by
    have h := dist_withLp_le_sqrt (u := y) (v := α.toFun x) (c := 2 * L) (D := 0)
      (by simp [hy, abs_of_pos (show 0 < 2 * L by linarith)]) (by simp [hy])
    rwa [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (by linarith)] at h
  have hxq : dist (α.toFun x) (WithLp.toLp 2 ((0 : ℝ), y₀)) ≤ dist x p + β := by
    have := α.radial_error x hxβ
    have := (abs_le.mp this).2
    linarith
  have hyq : dist y (WithLp.toLp 2 ((0 : ℝ), y₀)) < β⁻¹ - β := by
    have := dist_triangle y (α.toFun x) (WithLp.toLp 2 ((0 : ℝ), y₀))
    have := mem_ball.mp hx
    linarith
  obtain ⟨x', hx'β, hyx'⟩ := α.coverage_witness y hyq
  have hdistort := abs_le.mp (α.distortion x hxβ x' hx'β)
  have hfst : |y.fst - (α.toFun x').fst| ≤ dist y (α.toFun x') := abs_fst_sub_le_dist_withLp _ _
  have hyfst : y.fst = (α.toFun x).fst + 2 * L := by simp [hy]
  rw [hyfst] at hfst
  have hnum : 2 * L - 2 * β ≤ (α.toFun x').fst - (α.toFun x).fst := by
    linarith [(abs_le.mp (hfst.trans hyx'.le)).2]
  have hαα : dist (α.toFun x) (α.toFun x') ≤ 2 * L + 2 * β := by
    have := dist_triangle (α.toFun x) y (α.toFun x')
    rw [dist_comm] at hyx
    linarith
  have hαα' : 2 * L - 2 * β ≤ dist (α.toFun x) (α.toFun x') := by
    have := abs_fst_sub_le_dist_withLp (α.toFun x') (α.toFun x)
    rw [dist_comm] at this
    linarith [le_abs_self ((α.toFun x').fst - (α.toFun x).fst)]
  have hdup : dist x x' ≤ 2 * L + 3 * β := by linarith [hdistort.2]
  have hdlo : L < dist x x' := by linarith [hdistort.1]
  have hx'T : x' ∈ ball p T := by
    rw [mem_ball]
    have := dist_triangle x' x p
    rw [dist_comm x' x] at this
    linarith [mem_ball.mp hx]
  have hdpos : 0 < dist x x' := by linarith
  obtain ⟨w, hw, hwend⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm x x'
    (by rw [toReal_riemannianEDist_eq_dist]; exact hdpos)
  rw [toReal_riemannianEDist_eq_dist] at hwend
  have h := h19 x (ball_subset_ball hrL hx) x' hx'T hdlo w hw hwend
  refine ⟨w, hw, ?_⟩
  have hratio : (2 * L - 2 * β) / (2 * L + 3 * β) ≤
      ((α.toFun x').fst - (α.toFun x).fst) / dist x x' := by
    calc (2 * L - 2 * β) / (2 * L + 3 * β) ≤ (2 * L - 2 * β) / dist x x' := by
          gcongr
          linarith
      _ ≤ ((α.toFun x').fst - (α.toFun x).fst) / dist x x' := by gcongr
  linarith [(abs_lt.mp h).1]

/-- **LFR20, surjectivity.** For any continuous `η` within `e` of `u` on `B(p, L)`, the image
`η(B(p, L))` contains `[-(c - 2β - e), c - 2β - e]` once `c + 3β < L`. -/
theorem Icc_subset_image_ball_of_rankOne (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β L c e : ℝ}
    (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β) {η : M → ℝ} (hηc : Continuous η)
    (hval : ∀ x ∈ ball p L, |η x - (α.toFun x).fst| < e) (hc : 0 ≤ c) (hcL : c + 3 * β < L)
    (hcβ : c + β < β⁻¹) :
    Icc (-(c - 2 * β - e)) (c - 2 * β - e) ⊆ η '' ball p L := by
  have hβ0 := α.error_pos
  have hpt : ∀ c' : ℝ, |c'| = c → ∃ x ∈ ball p L, |(α.toFun x).fst - c'| < 2 * β := by
    intro c' hc'
    set y : WithLp 2 (ℝ × Y) := WithLp.toLp 2 (c', y₀) with hy
    have hyq : dist y (WithLp.toLp 2 ((0 : ℝ), y₀)) < β⁻¹ - β := by
      have h := dist_withLp_le_sqrt (u := y) (v := WithLp.toLp 2 ((0 : ℝ), y₀)) (c := c) (D := 0)
        (by simp [hy, hc']) (by simp [hy])
      rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hc] at h
      linarith
    obtain ⟨x, hxβ, hyx⟩ := α.coverage_witness y hyq
    have hrad := (abs_le.mp (α.radial_error x hxβ)).1
    have h1 := dist_triangle (α.toFun x) y (WithLp.toLp 2 ((0 : ℝ), y₀))
    have h2 : dist y (WithLp.toLp 2 ((0 : ℝ), y₀)) ≤ c := by
      have h := dist_withLp_le_sqrt (u := y) (v := WithLp.toLp 2 ((0 : ℝ), y₀)) (c := c) (D := 0)
        (by simp [hy, hc']) (by simp [hy])
      rwa [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hc] at h
    have hfst := abs_fst_sub_le_dist_withLp (α.toFun x) y
    have hyfst : y.fst = c' := by simp [hy]
    rw [hyfst] at hfst
    refine ⟨x, mem_ball.mpr ?_, hfst.trans_lt ?_⟩
    · rw [dist_comm] at hyx
      linarith
    · rw [dist_comm]; exact hyx
  obtain ⟨xp, hxp, hxpc⟩ := hpt c (abs_of_nonneg hc)
  obtain ⟨xm, hxm, hxmc⟩ := hpt (-c) (by rw [abs_neg, abs_of_nonneg hc])
  have hpre := (isPreconnected_ball_of_complete g hEnorm p L).image η hηc.continuousOn
  have hsub := hpre.Icc_subset (mem_image_of_mem η hxm) (mem_image_of_mem η hxp)
  refine (Icc_subset_Icc ?_ ?_).trans hsub
  · have := (abs_lt.mp (hval xm hxm)).2
    have := (abs_lt.mp hxmc).2
    linarith
  · have := (abs_lt.mp (hval xp hxp)).1
    have := (abs_lt.mp hxpc).1
    linarith

end DifferentialGeometry.Geometry.Collapse
