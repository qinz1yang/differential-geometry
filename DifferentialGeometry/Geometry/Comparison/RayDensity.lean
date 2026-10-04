import DifferentialGeometry.Geometry.Comparison.RayChord
import DifferentialGeometry.Geometry.Metric.Ray
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

/-!
# Density of rays and uniform chord convergence under nonnegative four-point comparison

Tier T2 ("RayDensity") of the Tits-cone producer of chapter 13: steps I5–I7 of the design
`docs/geometrization/chapter13/design-tits-cone-20261004.md` (§2, frozen interface §4), the metric
form of the blueprint's LFR56 (uniform distance limits) and of the "long hinge" step of LFR58
(`docs/geometrization/blueprint/master207A.tex:29719–29926`, hinge at 29827–29840).

A ray from `q` is a map `γ : ℝ≥0 → Y` with `Isometry γ ∧ γ 0 = q`, written inline. `Y` is proper,
satisfies `fourPointComparison 0 univ`, and (for I5) has segments. Compactness of closed balls is the
only compactness used: no precompactness of the blow-downs, no dimension bound.

* I7 `isClosed_rayUnion`: the union of the rays from `q` is closed (any proper metric space).
* I5 `exists_ray_near`: every far point `x` lies within `η |qx|` of the point at radius `|qx|` of
  some ray. Proof by contradiction: unit segments to bad points cluster to a ray
  (`exists_isometry_mapClusterPt_of_dist_min`), and I1 applied at the actual long length `|qx|` gives
  `|x γ(|qx|)| ≤ |qx| · |c(1) γ(1)|`.
* I6 `exists_uniform_rayChord`: the chord quotients `d(γ t, σ t) / t` converge to `rayChordLimit`
  uniformly over all pairs of rays: a finite net of ray points at radius `1` controls every larger
  radius because the quotient is antitone (I2).
* `exists_uniform_dist_le_of_ray`: the error budget of the design (consequence of I6), in
  multiplied-out form: `d(γ s, σ u) ≤ √((s - u)² + s u ρ∞²) + ω R` uniformly for all rays and all
  `s, u ≤ S R`, once `R` is large. Together with T1's
  `sub_sq_add_mul_rayChordLimit_sq_le_dist_sq` this is uniform convergence of the cosine law on
  bounded radii.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {Y : Type*} [MetricSpace Y]

/-! ## I7: the ray union is closed -/

/-- I7: the union of the rays from `q` is closed. -/
theorem isClosed_rayUnion [ProperSpace Y] (q : Y) :
    IsClosed {x : Y | ∃ γ : ℝ≥0 → Y, (Isometry γ ∧ γ 0 = q) ∧ x ∈ range γ} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  choose γ hγ hmem using hu
  choose t ht using hmem
  let r : ℝ≥0 := ⟨dist q x, dist_nonneg⟩
  let σ : ℕ → ℝ≥0 → Y := fun n s => γ n (min s n)
  have hL : Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop := tendsto_natCast_atTop_atTop
  have hzero : ∀ n, σ n 0 = q := fun n => by simp [σ, (hγ n).2]
  have hdist : ∀ n s s', dist (σ n s) (σ n s') = dist (min s (n : ℝ≥0)) (min s' (n : ℝ≥0)) :=
    fun n s s' => (hγ n).1.dist_eq _ _
  obtain ⟨ρ, hρ0, hρ, hclus⟩ := DifferentialGeometry.Geometry.exists_isometry_mapClusterPt_of_dist_min
    q σ (fun n => (n : ℝ≥0)) hL hzero hdist
  refine ⟨ρ, ⟨hρ, hρ0⟩, r, ?_⟩
  apply dist_le_zero.mp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  have hclosed : IsClosed {f : ℝ≥0 → Y | dist (f r) x ≤ ε} :=
    isClosed_le ((continuous_apply r).dist continuous_const) continuous_const
  apply hclosed.mem_of_mapClusterPt hclus
  filter_upwards [hL.eventually (eventually_ge_atTop r),
    Metric.tendsto_nhds.mp hux (ε / 2) (by positivity)] with n hn hux'
  change dist (γ n (min r n)) x ≤ ε
  rw [min_eq_left hn]
  have htn : (t n : ℝ) = dist q (u n) := by rw [← ht n, dist_of_ray (hγ n)]
  have h1 : dist (γ n r) (γ n (t n)) = |(r : ℝ) - t n| := by
    rw [(hγ n).1.dist_eq, NNReal.dist_eq]
  have h2 : |(r : ℝ) - t n| ≤ dist (u n) x := by
    rw [htn]
    change |dist q x - dist q (u n)| ≤ dist (u n) x
    have h3 := dist_triangle q x (u n)
    have h4 := dist_triangle q (u n) x
    rw [dist_comm x (u n)] at h3
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  calc dist (γ n r) x ≤ dist (γ n r) (γ n (t n)) + dist (γ n (t n)) x := dist_triangle _ _ _
    _ ≤ dist (u n) x + dist (u n) x := by rw [h1, ht n]; linarith
    _ ≤ ε := by linarith

/-! ## I5: density of rays -/

/-- I5: every far point is relatively close to a ray from `q` (vacuous for bounded `Y`). -/
theorem exists_ray_near (hcomp : fourPointComparison 0 (univ : Set Y)) [ProperSpace Y]
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (q : Y) {η : ℝ} (hη : 0 < η) :
    ∃ r₀ : ℝ, ∀ x : Y, r₀ ≤ dist q x → ∃ γ : ℝ≥0 → Y, (Isometry γ ∧ γ 0 = q) ∧
      dist x (γ ⟨dist q x, dist_nonneg⟩) ≤ η * dist q x := by
  by_contra hcon
  push Not at hcon
  choose x hx hbad using fun n : ℕ => hcon ((n : ℝ) + 1)
  choose f hfc hf0 hf1 hfd using fun n => hsegments q (x n)
  choose c hc hc0 hcend using fun n =>
    Metric.exists_isometric_segment_of_dist_eq_mul (hf0 n) (hf1 n) (hfd n)
  let L : ℕ → ℝ≥0 := fun n => ⟨dist q (x n), dist_nonneg⟩
  let σ : ℕ → ℝ≥0 → Y := fun n s =>
    c n ⟨min (s : ℝ) (dist q (x n)), le_min s.2 dist_nonneg, min_le_right _ _⟩
  have hL : Tendsto L atTop atTop := by
    apply NNReal.tendsto_coe_atTop.mp
    refine tendsto_atTop_mono (fun n => hx n) ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hzero : ∀ n, σ n 0 = q := by
    intro n
    rw [← hc0 n]
    exact congrArg (c n) (Subtype.ext (show min ((0 : ℝ≥0) : ℝ) (dist q (x n)) = 0 by
      rw [NNReal.coe_zero]; exact min_eq_left dist_nonneg))
  have hdist : ∀ n s t, dist (σ n s) (σ n t) = dist (min s (L n)) (min t (L n)) := by
    intro n s t
    rw [(hc n).dist_eq, Subtype.dist_eq, NNReal.dist_eq, NNReal.coe_min, NNReal.coe_min]
    rfl
  obtain ⟨γ, hγ0, hγ, hclus⟩ := DifferentialGeometry.Geometry.exists_isometry_mapClusterPt_of_dist_min
    q σ L hL hzero hdist
  -- some segment passes close to `γ 1` at radius `1`
  have hnear : ∃ n, dist (σ n 1) (γ 1) < η := by
    by_contra hno
    push Not at hno
    have hclosed : IsClosed {g : ℝ≥0 → Y | η ≤ dist (g 1) (γ 1)} :=
      isClosed_le continuous_const ((continuous_apply 1).dist continuous_const)
    have hmem := hclosed.mem_of_mapClusterPt hclus (Eventually.of_forall hno)
    change η ≤ dist (γ 1) (γ 1) at hmem
    rw [dist_self] at hmem
    linarith
  obtain ⟨n, hn⟩ := hnear
  set Lr : ℝ := dist q (x n) with hLr
  have hL1 : (1 : ℝ) ≤ Lr := by
    have := hx n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hLpos : (0 : ℝ) < Lr := by linarith
  have hL1' : (1 : ℝ≥0) ≤ L n := by
    change ((1 : ℝ≥0) : ℝ) ≤ Lr
    simpa using hL1
  -- the point at radius `1` on the segment and its distances
  have hz0 : dist q (σ n 1) = 1 := by
    rw [← hzero n, hdist, min_eq_left (zero_le : (0 : ℝ≥0) ≤ L n), min_eq_left hL1', NNReal.dist_eq]
    simp
  have hσend : σ n (L n) = x n := by
    rw [← hcend n]
    exact congrArg (c n) (Subtype.ext (show min (dist q (x n)) (dist q (x n)) = dist q (x n) from
      min_self _))
  have hz1 : dist (σ n 1) (x n) = Lr - 1 := by
    rw [← hσend, hdist, min_eq_left hL1', min_self, NNReal.dist_eq]
    change |(1 : ℝ) - Lr| = Lr - 1
    rw [abs_of_nonpos (by linarith)]
    ring
  -- I1 along the segment, at fraction `1 / Lr`
  have hfrac : 1 / Lr ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hLpos).mpr hL1⟩
  have hK1 := radialConeKernel_le_mul_of_segment hcomp (γ 1) hfrac (q := q) (b := x n)
    (z := σ n 1) (by rw [hz0, ← hLr]; field_simp)
    (by rw [hz1, ← hLr]; field_simp)
  -- I1 along the ray, from radius `1` to radius `Lr`
  have hK2 := mul_radialConeKernel_le_of_ray hcomp ⟨hγ, hγ0⟩ (x n) hL1'
  rw [radialConeKernel_comm q (γ 1) (x n)] at hK2
  -- expand the kernels
  have hd1 : dist q (γ 1) = 1 := by rw [dist_of_ray ⟨hγ, hγ0⟩]; simp
  have hdL : dist q (γ (L n)) = Lr := dist_of_ray ⟨hγ, hγ0⟩ (L n)
  have hLn : ((L n : ℝ≥0) : ℝ) = Lr := rfl
  rw [hLn, NNReal.coe_one, one_mul] at hK2
  have hbadn := hbad n γ ⟨hγ, hγ0⟩
  change η * Lr < dist (x n) (γ (L n)) at hbadn
  unfold radialConeKernel at hK1 hK2
  rw [hz0, hd1] at hK1
  rw [hdL, hd1, ← hLr, dist_comm (γ (L n)) (x n)] at hK2
  set d1 := dist (σ n 1) (γ 1) with hd1def
  set dL := dist (x n) (γ (L n)) with hdLdef
  set K := (Lr ^ 2 + 1 ^ 2 - dist (x n) (γ 1) ^ 2) / 2 with hKdef
  -- `Lr² K(z, γ 1) ≤ Lr K(x, γ 1) ≤ K(x, γ Lr)`
  have hA : Lr * ((1 ^ 2 + 1 ^ 2 - d1 ^ 2) / 2) ≤ K := by
    have := mul_le_mul_of_nonneg_left hK1 hLpos.le
    rwa [← mul_assoc, mul_one_div_cancel hLpos.ne', one_mul] at this
  have hB : Lr * (Lr * ((1 ^ 2 + 1 ^ 2 - d1 ^ 2) / 2)) ≤ (Lr ^ 2 + Lr ^ 2 - dL ^ 2) / 2 :=
    (mul_le_mul_of_nonneg_left hA hLpos.le).trans hK2
  have hsq : dL ^ 2 < (η * Lr) ^ 2 := by
    have hd1sq : d1 ^ 2 < η ^ 2 := by
      have h0 : 0 ≤ d1 := dist_nonneg
      nlinarith
    have hLsq : 0 < Lr ^ 2 := by positivity
    nlinarith
  have hlt := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  linarith

/-! ## I6: uniform convergence of the chord quotients -/

/-- I6: chords converge to their limit uniformly over all pairs of rays from `q`. -/
theorem exists_uniform_rayChord (hcomp : fourPointComparison 0 (univ : Set Y)) [ProperSpace Y]
    (q : Y) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ≥0, 0 < T ∧ ∀ t : ℝ≥0, T ≤ t → ∀ γ σ : ℝ≥0 → Y, (Isometry γ ∧ γ 0 = q) →
      (Isometry σ ∧ σ 0 = q) → dist (γ t) (σ t) / (t : ℝ) ≤ rayChordLimit γ σ + η := by
  -- the points at radius `1` of the rays form a totally bounded set
  let S₁ : Set Y := {y | ∃ γ : ℝ≥0 → Y, (Isometry γ ∧ γ 0 = q) ∧ γ 1 = y}
  have hsub : S₁ ⊆ closedBall q 1 := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [mem_closedBall, dist_comm, dist_of_ray hγ, NNReal.coe_one]
  have htb : TotallyBounded S₁ := (isCompact_closedBall q 1).totallyBounded.subset hsub
  obtain ⟨N, hNS, hNfin, hcover⟩ := finite_approx_of_totallyBounded htb (η / 5) (by positivity)
  -- a chosen ray through each point of `S₁`
  have hpick : ∀ y : Y, ∃ γ : ℝ≥0 → Y, y ∈ S₁ → (Isometry γ ∧ γ 0 = q) ∧ γ 1 = y := by
    intro y
    by_cases hy : y ∈ S₁
    · obtain ⟨γ, hγ, h1⟩ := hy
      exact ⟨γ, fun _ => ⟨hγ, h1⟩⟩
    · exact ⟨fun _ => q, fun h => absurd h hy⟩
  choose pick hpick using hpick
  -- convergence on the finitely many pairs of chosen rays
  have hev : ∀ᶠ t : ℝ≥0 in atTop, ∀ y ∈ N, ∀ y' ∈ N,
      dist (pick y t) (pick y' t) / (t : ℝ) ≤ rayChordLimit (pick y) (pick y') + η / 5 := by
    rw [eventually_all_finite hNfin]
    intro y hy
    rw [eventually_all_finite hNfin]
    intro y' hy'
    have hlim := tendsto_dist_div_rayChordLimit hcomp (hpick y (hNS hy)).1 (hpick y' (hNS hy')).1
    exact ((tendsto_order.mp hlim).2 _ (by linarith)).mono fun t ht => ht.le
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  refine ⟨max T₀ 1, lt_max_of_lt_right one_pos, fun t ht γ σ hγ hσ => ?_⟩
  have ht1 : (1 : ℝ≥0) ≤ t := (le_max_right _ _).trans ht
  have htpos : (0 : ℝ≥0) < t := one_pos.trans_le ht1
  -- net points near `γ 1` and `σ 1`
  obtain ⟨y, hy, hγy⟩ := mem_iUnion₂.mp (hcover (show γ 1 ∈ S₁ from ⟨γ, hγ, rfl⟩))
  obtain ⟨y', hy', hσy⟩ := mem_iUnion₂.mp (hcover (show σ 1 ∈ S₁ from ⟨σ, hσ, rfl⟩))
  obtain ⟨hγ', hγ'1⟩ := hpick y (hNS hy)
  obtain ⟨hσ', hσ'1⟩ := hpick y' (hNS hy')
  have hC := hT₀ t ((le_max_left _ _).trans ht) y hy y' hy'
  rw [mem_ball, ← hγ'1] at hγy
  rw [mem_ball, ← hσ'1] at hσy
  -- I2: closeness at radius `1` persists at every radius `t ≥ 1`
  have hA : dist (γ t) (pick y t) / (t : ℝ) < η / 5 := by
    have h := antitoneOn_dist_div_of_ray hcomp hγ hγ' (Set.mem_Ioi.mpr (one_pos : (0 : ℝ≥0) < 1))
      (show t ∈ Ioi 0 from htpos) ht1
    simp only [NNReal.coe_one, div_one] at h
    exact h.trans_lt hγy
  have hB : dist (pick y' t) (σ t) / (t : ℝ) < η / 5 := by
    have h := antitoneOn_dist_div_of_ray hcomp hσ' hσ (Set.mem_Ioi.mpr (one_pos : (0 : ℝ≥0) < 1))
      (show t ∈ Ioi 0 from htpos) ht1
    simp only [NNReal.coe_one, div_one] at h
    rw [dist_comm (pick y' 1)] at h
    exact h.trans_lt hσy
  -- and for the limit chords
  have hD1 : rayChordLimit (pick y) γ < η / 5 := by
    have h := rayChordLimit_le (pick y) γ (one_pos : (0 : ℝ≥0) < 1)
    rw [NNReal.coe_one, div_one, dist_comm] at h
    exact h.trans_lt hγy
  have hD2 : rayChordLimit σ (pick y') < η / 5 := by
    have h := rayChordLimit_le σ (pick y') (one_pos : (0 : ℝ≥0) < 1)
    rw [NNReal.coe_one, div_one] at h
    exact h.trans_lt hσy
  have hT1 := rayChordLimit_triangle hcomp hγ' hγ hσ'
  have hT2 := rayChordLimit_triangle hcomp hγ hσ hσ'
  have htri : dist (γ t) (σ t) / (t : ℝ) ≤ dist (γ t) (pick y t) / (t : ℝ) +
      dist (pick y t) (pick y' t) / (t : ℝ) + dist (pick y' t) (σ t) / (t : ℝ) := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (dist_triangle4 _ _ _ _) (NNReal.coe_nonneg t)
  linarith

/-! ## The error budget: uniform cosine law on bounded radii -/

/-- The error budget of the Tits-cone design (consequence of I6), multiplied out: for every
`ω > 0` and every bound `S`, once `R` is large, every two points `γ s`, `σ u` on rays from `q` with
`s, u ≤ S R` satisfy `d(γ s, σ u) ≤ √((s - u)² + s u ρ∞²) + ω R`. -/
theorem exists_uniform_dist_le_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    [ProperSpace Y] (q : Y) {ω : ℝ} (hω : 0 < ω) (S : ℝ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ γ σ : ℝ≥0 → Y, (Isometry γ ∧ γ 0 = q) →
      (Isometry σ ∧ σ 0 = q) → ∀ s u : ℝ≥0, (s : ℝ) ≤ S * R → (u : ℝ) ≤ S * R →
        dist (γ s) (σ u) ≤
          Real.sqrt (((s : ℝ) - u) ^ 2 + s * u * rayChordLimit γ σ ^ 2) + ω * R := by
  set S' : ℝ := max S 0 + 1 with hS'
  have hS'pos : 0 < S' := by have := le_max_right S 0; linarith
  have hSS' : S ≤ S' := by have := le_max_left S 0; linarith
  set η : ℝ := min 1 (ω ^ 2 / (5 * S' ^ 2)) with hηdef
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηS : 5 * S' ^ 2 * η ≤ ω ^ 2 := by
    have h := min_le_right 1 (ω ^ 2 / (5 * S' ^ 2))
    rw [← hηdef, le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨T, -, hT⟩ := exists_uniform_rayChord hcomp q hηpos
  set θ : ℝ := ω / 2 with hθ
  have hθpos : 0 < θ := by positivity
  refine ⟨max ((T : ℝ) / θ) 1, lt_max_of_lt_right one_pos,
    fun R hR γ σ hγ hσ s u hs hu => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR)
  have hTR : (T : ℝ) ≤ θ * R := by
    have h := (le_max_left _ _).trans hR
    rw [div_le_iff₀ hθpos] at h
    linarith
  set D := Real.sqrt (((s : ℝ) - u) ^ 2 + s * u * rayChordLimit γ σ ^ 2) with hD
  have hρ0 := rayChordLimit_nonneg γ σ
  have hρ2 := rayChordLimit_le_two hγ hσ
  have hDabs : |(s : ℝ) - u| ≤ D := by
    rw [hD, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have h : (0 : ℝ) ≤ s * u * rayChordLimit γ σ ^ 2 := by positivity
    linarith
  have hsu : dist (γ s) (σ u) ≤ s + u := by
    calc dist (γ s) (σ u) ≤ dist (γ s) q + dist q (σ u) := dist_triangle _ _ _
      _ = s + u := by rw [dist_comm, dist_of_ray hγ, dist_of_ray hσ]
  by_cases hsmall : (s : ℝ) < θ * R ∨ (u : ℝ) < θ * R
  · -- a short radius: the trivial bound `s + u` already suffices
    have h1 : (u : ℝ) - s ≤ D := by
      have h := le_abs_self ((u : ℝ) - s)
      rw [abs_sub_comm] at h
      linarith
    have h2 : (s : ℝ) - u ≤ D := (le_abs_self _).trans hDabs
    have hθR : θ * R = ω * R / 2 := by rw [hθ]; ring
    rcases hsmall with hs' | hu' <;> linarith
  · -- both radii are long: compare with the chord at radius `θ R ≥ T` (I6)
    push Not at hsmall
    obtain ⟨hs', hu'⟩ := hsmall
    let m : ℝ≥0 := ⟨θ * R, by positivity⟩
    have hmpos : 0 < m := by change (0 : ℝ) < θ * R; positivity
    have hdsq := dist_sq_le_of_ray hcomp hγ hσ hmpos (show m ≤ s from hs') (show m ≤ u from hu')
    have hρm := hT m (show (T : ℝ) ≤ θ * R from hTR) γ σ hγ hσ
    have hρm0 : 0 ≤ dist (γ m) (σ m) / (m : ℝ) := by positivity
    have hρmsq : (dist (γ m) (σ m) / (m : ℝ)) ^ 2 ≤ (rayChordLimit γ σ + η) ^ 2 :=
      pow_le_pow_left₀ hρm0 hρm 2
    have hext : (rayChordLimit γ σ + η) ^ 2 ≤ rayChordLimit γ σ ^ 2 + 5 * η := by nlinarith
    have hsS : (s : ℝ) ≤ S' * R := hs.trans (mul_le_mul_of_nonneg_right hSS' hRpos.le)
    have huS : (u : ℝ) ≤ S' * R := hu.trans (mul_le_mul_of_nonneg_right hSS' hRpos.le)
    have hsuS : (s : ℝ) * u ≤ (S' * R) ^ 2 := by
      rw [sq]
      exact mul_le_mul hsS huS (NNReal.coe_nonneg u) (by positivity)
    have hsu0 : (0 : ℝ) ≤ s * u := by positivity
    have hDsq : D ^ 2 = ((s : ℝ) - u) ^ 2 + s * u * rayChordLimit γ σ ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hD0 : 0 ≤ D := Real.sqrt_nonneg _
    have h1 : dist (γ s) (σ u) ^ 2 ≤ D ^ 2 + s * u * (5 * η) := by
      have h := mul_le_mul_of_nonneg_left (hρmsq.trans hext) hsu0
      rw [hDsq]
      nlinarith
    have h2 : (s : ℝ) * u * (5 * η) ≤ (ω * R) ^ 2 := by
      calc (s : ℝ) * u * (5 * η) ≤ (S' * R) ^ 2 * (5 * η) :=
            mul_le_mul_of_nonneg_right hsuS (by positivity)
        _ = (5 * S' ^ 2 * η) * R ^ 2 := by ring
        _ ≤ ω ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right hηS (by positivity)
        _ = (ω * R) ^ 2 := by ring
    have hωR : 0 ≤ ω * R := by positivity
    have h3 : dist (γ s) (σ u) ^ 2 ≤ (D + ω * R) ^ 2 := by nlinarith
    exact (sq_le_sq₀ dist_nonneg (by positivity)).mp h3

end GC.MetricGeometry
