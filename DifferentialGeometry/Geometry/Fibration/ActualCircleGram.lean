import DifferentialGeometry.Geometry.Fibration.ActualFirstComparisonList

/-!
# TCP01's Gram clause for the circle coordinate of packet (i)

Blueprint `master207B.tex`, TCP01 (`lem:fibration-first-comparison-list`, B:5250), last paragraph:
"`‖Dη_i(Dη_i)^* − I‖ < γ/4` in its own normalized metric on `B(p_i, 200)`", bound to the circle
adapted-coordinate packet (i) of `LocalChartPackets` (the SAME chosen chart, its `(1 + γ)`-Lipschitz
bound and its original long derivative tests against the SAME `(2, β₂)`-splitting).

* `circleAdapted_gram_upper_KA2`: `‖dη_j(w)‖ ≤ (1 + γ)|w|` for the normalized norm
  `|w| = √(ρ(j)⁻² g(w, w))`.
* `circleAdapted_gram_lower_KA2`: for `β₂ ≤ 10⁻⁷`, every unit `ξ ∈ ℝ²` has a normalized-unit `w`
  with `‖dη_j(w) − ξ‖ < γ + β₂` (the long test toward a coverage point of the splitting at distance
  `10⁶` in the direction `ξ`, reached by a minimizing geodesic of `ρ(j)⁻² g`).
* `tcp01_gram`: the two-sided singular-value form: `‖Dη‖ ≤ 1 + γ` and `⟨dη(w), ξ⟩ > 1 − (γ + β₂)`
  for some unit `w`, i.e. every singular value of `Dη` lies in `[1 − γ', 1 + γ]`, `γ' = γ + β₂`; hence
  `‖Dη(Dη)^* − I‖ ≤ 2γ' + γ'²`, which is `< γ_T/4` once the packet's `γ + β₂ ≤ γ_T/10` (a choice before
  `Δ`, as in the blueprint). The tangent space carries no norm instance here, so the Gram bound is
  stated in this equivalent singular-value form.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

theorem dist_toLp_same_snd_KA2 {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (u v : α) (y : β) :
    dist (WithLp.toLp 2 (u, y)) (WithLp.toLp 2 (v, y)) = dist u v := by
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hf : (WithLp.toLp 2 (u, y)).fst = u := rfl
  have hf' : (WithLp.toLp 2 (v, y)).fst = v := rfl
  have hs : (WithLp.toLp 2 (u, y)).snd = y := rfl
  have hs' : (WithLp.toLp 2 (v, y)).snd = y := rfl
  rw [h2, hf, hf', hs, hs', dist_self, Real.zero_rpow (by norm_num), add_zero,
    ← Real.rpow_mul dist_nonneg]
  norm_num

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNG_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNG_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCG_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The lower Gram bound of the circle coordinate** (TCP01): at every point of `B(j, 200ρ(j))` and
for every unit `ξ ∈ ℝ²` there is a unit vector `w` of the normalized metric `ρ(j)⁻² g` with
`‖dη_j(w) − ξ‖ < γ + β₂` (the long test of packet (i) toward a coverage point at distance `10⁶`
in the direction `ξ`). -/
theorem circleAdapted_gram_lower_KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hβ : β 2 ≤ 1 / 10000000) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) (ξ : ℝ²) (hξ : ‖ξ‖ = 1) :
    ∃ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 ∧
      ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w - ξ‖ < γ + β 2 := by
  have hrj := hρ j
  have hn : (ρ j)⁻¹ * dist x j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hc := P.circle.chart_center j hj
  set η := cgpCircleCoord P.toLocalChartFamily j hj with hηdef
  let A := P.circleAdapted j hj
  let c := P.circle.chart j hj
  have htest := A.test
  let Yt := A.Y
  let iY : MetricSpace Yt := A.instY
  let sp := A.split
  let a := A.a
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hβpos : 0 < β 2 := sp.error_pos
  have hc' : c.center = j := hc
  have hxj : dist x j < 200 := hn
  set t : ℝ := 1000000 with ht
  have hβinv : 10000000 ≤ (β 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hβpos]
    linarith
  have hxB : x ∈ ball j (β 2)⁻¹ := by
    rw [mem_ball]
    linarith
  have hjB : j ∈ ball j (β 2)⁻¹ := mem_ball_self (by positivity)
  have hbase : sp.toFun j = WithLp.toLp 2 ((0 : ℝ²), a) := sp.basepoint
  have hsx : dist (sp.toFun x) (sp.toFun j) ≤ dist x j + β 2 := by
    have := sp.distortion x hxB j hjB
    linarith [(abs_le.mp this).2]
  let ystar : WithLp 2 (ℝ² × Yt) :=
    WithLp.toLp 2 ((sp.toFun x).fst + t • ξ, (sp.toFun x).snd)
  have h1 : dist ((sp.toFun x).fst + t • ξ) (sp.toFun x).fst = t := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hξ, Real.norm_eq_abs,
      abs_of_pos (by norm_num), mul_one]
  have hy1 : dist ystar (sp.toFun x) = t :=
    (dist_toLp_same_snd_KA2 ((sp.toFun x).fst + t • ξ) (sp.toFun x).fst (sp.toFun x).snd).trans h1
  have hy0 : dist ystar (WithLp.toLp 2 ((0 : ℝ²), a)) < (β 2)⁻¹ - β 2 := by
    rw [← hbase]
    have := dist_triangle ystar (sp.toFun x) (sp.toFun j)
    nlinarith
  have hcov := sp.coverage ystar hy0
  have hlt : infDist ystar (sp.toFun '' ball j (β 2)⁻¹) < 2 * β 2 := by linarith
  obtain ⟨_, ⟨z, hzB, rfl⟩, hzd⟩ := (Metric.infDist_lt_iff sp.image_nonempty).mp hlt
  have hxz := sp.distortion x hxB z hzB
  have hdsx : |dist (sp.toFun x) (sp.toFun z) - t| ≤ 2 * β 2 := by
    have e1 := dist_triangle (sp.toFun x) ystar (sp.toFun z)
    have e2 := dist_triangle ystar (sp.toFun z) (sp.toFun x)
    have e3 := dist_comm ystar (sp.toFun x)
    have e4 := dist_comm (sp.toFun z) (sp.toFun x)
    rw [abs_le]
    constructor <;> linarith
  have hdxz : |dist x z - t| ≤ 3 * β 2 := by
    rw [abs_le] at hxz hdsx ⊢
    constructor <;> linarith [hxz.1, hxz.2, hdsx.1, hdsx.2]
  have hd0 : 201 < dist x z := by
    have := (abs_le.mp hdxz).1
    linarith
  have hzj : dist z j < 201 * 10000 := by
    have hzj' := sp.distortion z hzB j hjB
    have f1 := dist_triangle (sp.toFun z) ystar (sp.toFun j)
    have f2 := dist_triangle ystar (sp.toFun x) (sp.toFun j)
    have f3 := dist_comm (sp.toFun z) ystar
    have := (abs_le.mp hzj').1
    linarith
  have hzB' : z ∈ ball j (201 * 10000) := hzj
  have hxB200 : x ∈ ball j 200 := hxj
  have hfin : riemannianEDist 𝓘(ℝ, E3) x z ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨v, hv, hlen⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top gR hnR x z hfin
  have hdlen : (riemannianEDist 𝓘(ℝ, E3) x z).toReal = dist x z := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  rw [hdlen] at hlen
  have hdpos : 0 < dist x z := by linarith
  let w : TangentSpace 𝓘(ℝ, E3) x := (dist x z)⁻¹ • v
  have hvpos : 0 < gR.inner x v v := Real.sqrt_pos.mp (hlen ▸ hdpos)
  have hvv : gR.inner x v v = dist x z ^ 2 := by
    rw [← hlen, Real.sq_sqrt hvpos.le]
  have hw : gR.inner x w w = 1 := by
    rw [gInner_smul_self, hvv]
    field_simp
  have hgeo : intrinsicGeodesic gR hnR x w (dist x z) = z := by
    rw [← intrinsicGeodesic_smul gR hnR x w (dist x z)]
    have hdw : dist x z • w = v := by
      change dist x z • ((dist x z)⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
    rw [hdw]
    exact hv
  have hT := htest x hxB200 z hzB' hd0 w hw hgeo
  have hT' : ‖mvfderiv 𝓘(ℝ, E3) η x w -
      (dist x z)⁻¹ • ((sp.toFun z).fst - (sp.toFun x).fst)‖ < γ := hT
  refine ⟨w, hw, ?_⟩
  set e : ℝ² := (sp.toFun z).fst - ((sp.toFun x).fst + t • ξ) with he
  have hen : ‖e‖ < 2 * β 2 := by
    have h := WithLp.dist_fst_le (sp.toFun z) ystar
    have hz2 : dist (sp.toFun z) ystar < 2 * β 2 := by rw [dist_comm]; exact hzd
    rw [dist_eq_norm] at h
    exact lt_of_le_of_lt h hz2
  have hu : (sp.toFun z).fst - (sp.toFun x).fst = t • ξ + e := by
    rw [he]
    abel
  have hdec : (dist x z)⁻¹ • ((sp.toFun z).fst - (sp.toFun x).fst) - ξ =
      ((dist x z)⁻¹ * (t - dist x z)) • ξ + (dist x z)⁻¹ • e := by
    rw [hu, smul_add, smul_smul, mul_sub, inv_mul_cancel₀ hdpos.ne', sub_smul, one_smul]
    abel
  have hkey : ‖(dist x z)⁻¹ • ((sp.toFun z).fst - (sp.toFun x).fst) - ξ‖ ≤ 5 * β 2 / dist x z := by
    rw [hdec]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, hξ, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_inv, abs_of_pos hdpos]
    have h3 : |t - dist x z| ≤ 3 * β 2 := by
      rw [abs_sub_comm]
      exact hdxz
    rw [div_eq_mul_inv]
    have hi : 0 < (dist x z)⁻¹ := inv_pos.mpr hdpos
    nlinarith [norm_nonneg e]
  have hsmall : 5 * β 2 / dist x z ≤ β 2 := by
    rw [div_le_iff₀ hdpos]
    nlinarith
  calc ‖mvfderiv 𝓘(ℝ, E3) η x w - ξ‖
      ≤ ‖mvfderiv 𝓘(ℝ, E3) η x w - (dist x z)⁻¹ • ((sp.toFun z).fst - (sp.toFun x).fst)‖ +
          ‖(dist x z)⁻¹ • ((sp.toFun z).fst - (sp.toFun x).fst) - ξ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < γ + β 2 := by linarith

/-- **The upper Gram bound of the circle coordinate**: `‖dη_j(w)‖ ≤ (1 + γ)√(ρ(j)⁻² g(w, w))` on
`B(j, 200ρ(j))`. -/
theorem circleAdapted_gram_upper_KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hγ : 0 ≤ γ) {j : X} (hj : j ∈ P.circle.centres) {x : X} (hx : x ∈ ball j (200 * ρ j))
    (w : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w‖ ≤
      (1 + γ) * Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner x w w) := by
  have : CompleteSpace X := complete_of_compact
  have hrj := hρ j
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (cgpCircleCoord P.toLocalChartFamily j hj) x :=
    ((cgpCircleCoord_contMDiffOn P.toLocalChartFamily hj).contMDiffAt
      (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := norm_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx hηd
    (L := (1 + γ) / ρ j) (by positivity) (circleAdapted_physical_KA2 P hγ hj).2 w
  have hs : Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner x w w) = (ρ j)⁻¹ * Real.sqrt (g.inner x w w) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hrj).le]
  rw [hs]
  calc ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w‖
      ≤ (1 + γ) / ρ j * Real.sqrt (g.inner x w w) := h
    _ = (1 + γ) * ((ρ j)⁻¹ * Real.sqrt (g.inner x w w)) := by ring

/-- **TCP01, Gram clause** (singular-value form) for the circle coordinate of packet (i) at a circle
centre `j`, at every point of `B(j, 200ρ(j))`, in the normalized metric `ρ(j)⁻² g`: `‖Dη‖ ≤ 1 + γ`, and
for every unit `ξ ∈ ℝ²` some unit `w` has `‖dη(w) − ξ‖ < γ + β₂` and `⟨dη(w), ξ⟩ > 1 − (γ + β₂)`. -/
theorem tcp01_gram
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hγ : 0 ≤ γ) (hβ : β 2 ≤ 1 / 10000000) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) :
    (∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 →
      ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w‖ ≤ 1 + γ) ∧
    ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 ∧
      ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w - ξ‖ < γ + β 2 ∧
      1 - (γ + β 2) < inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w) ξ := by
  refine ⟨fun w hw => ?_, fun ξ hξ => ?_⟩
  · have h := circleAdapted_gram_upper_KA2 P hγ hj hx w
    rwa [hw, Real.sqrt_one, mul_one] at h
  · obtain ⟨w, hw, hlt⟩ := circleAdapted_gram_lower_KA2 P hβ hj hx ξ hξ
    refine ⟨w, hw, hlt, ?_⟩
    set u := mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w with hu
    have h1 : inner ℝ u ξ = inner ℝ (u - ξ) ξ + inner ℝ ξ ξ := by
      rw [inner_sub_left]
      ring
    have h2 : inner ℝ ξ ξ = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hξ]
      norm_num
    have h3 : |inner ℝ (u - ξ) ξ| ≤ ‖u - ξ‖ := by
      have := abs_real_inner_le_norm (u - ξ) ξ
      rwa [hξ, mul_one] at this
    rw [h1, h2]
    linarith [(abs_le.mp h3).1]

end DifferentialGeometry.Geometry.Collapse
