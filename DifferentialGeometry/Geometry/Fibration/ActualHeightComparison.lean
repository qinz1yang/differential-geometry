import DifferentialGeometry.Geometry.Fibration.ActualEdgeConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualSupportRows
import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportRows
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplittingBCP02
import DifferentialGeometry.Geometry.Collapse.EdgeReferenceChartApplications
import DifferentialGeometry.Geometry.Fibration.ActualZeroConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualRawAlignmentZeroApplications

/-!
# TCP04: binding the SAME high-height coordinate `t = P/ρ` to the reference circle chart

Blueprint `master207B.tex`, TCP04 (`lem:fibration-first-height-comparison`, B:5442–5516), on
`LocalChartPackets`: at a circle centre `p_i`, either no edge support meets `D_i` (the weak-edge
block vanishes), or the LOW branch `t < 3Δ/20` holds on `D_i` (FC14; the height factors are
exactly one), or the HIGH branch: `Δ/10 ≤ t ≤ 181Δ/20`, `t` smooth, `‖Dt‖ ≤ 2` and one unit row
`B` with `‖t − t(p_i) − B(η_i − η_i(p_i))‖_{C¹(D_i)}` small (TH).

The high branch uses only the HEIGHT row of the SAME collar pair of an actual edge chart `j` at
the point `p_i` itself (LFR38, field `EdgeChart.collar` at `x = p_i`): its `(2, β_c)` plane map,
whose second real coordinate `h` is a rank-one splitting at `p_i` compared with the circle
splitting by TCP02's kernel (`tcp02_pair_KA3`, displacement `0`), and the pair's long test.

* `planeSwap_KA5`: the coordinate swap of `ℓ²(ℝ × ℝ)`.
* `abs_sub_le_of_mvfderiv_le_ball_KA5`: the mean value inequality on a metric ball (paths of
  almost minimal length stay in the ball).
* `EdgeFamily.collar_height_KA5`: at a collar point `p` of the chart `j`, the height `h` of the
  collar plane map is the real coordinate of a rank-one `(1, β_c)`-splitting of `(X, ρ(p)⁻¹ d, p)`
  and `t` satisfies the long test `|ρ(p) dt(w₀) − (ρ(p)/d(y, z))(h(z) − h(y))| < γ_c` along physical
  minimizing directions (`y ∈ B(p, 100ρ(p))`, `z ∈ B(p, 100ρ(p)/γ_c)`, `d(y, z) > ρ(p)`).
* `height_component_saturation_KA5`, `height_derivative_comparison_KA5` (FC15, `k = 1`),
  `height_value_KA5` (integration on `D_i`), `tcp04_high_KA5`: the high-branch kernel.
* `height_raw_alignment_KA6`: TCP02's kernel (rank one, displacement `0`) for the height: (TR)
  of `h` against the circle splitting at `p_i`.
* `tcp04_row`: the row.

Only the HEIGHT row of the collar is used; the joint `0.9` margin of `(η_j, F/ρ)` is not.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The coordinate swap `(a, b) ↦ (b, a)` of `ℓ²(ℝ × ℝ)`, an isometry. -/
def planeSwap_KA5 : WithLp 2 (ℝ × ℝ) ≃ᵢ WithLp 2 (ℝ × ℝ) where
  toFun z := WithLp.toLp 2 (z.snd, z.fst)
  invFun z := WithLp.toLp 2 (z.snd, z.fst)
  left_inv z := by simp; rfl
  right_inv z := by simp; rfl
  isometry_toFun := Isometry.of_dist_eq fun a b => by
    rw [WithLp.prod_dist_eq_add (by norm_num), WithLp.prod_dist_eq_add (by norm_num)]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    ring_nf

theorem planeSwap_KA5_apply_fst (z : WithLp 2 (ℝ × ℝ)) : (planeSwap_KA5 z).fst = z.snd := rfl

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X]

omit [CompactSpace X] in
/-- **The mean value inequality on a metric ball**: a function differentiable on `B(p, r)` with
`|df(v)| ≤ M √(g(v, v))` there (`M > 0`) satisfies `|f(x) − f(p)| ≤ M d(p, x)` on `B(p, r)`. -/
theorem abs_sub_le_of_mvfderiv_le_ball_KA5 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {f : X → ℝ}
    {p : X} {r M : ℝ} (hM : 0 < M)
    (hf : ∀ z ∈ ball p r, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f z)
    (hb : ∀ z ∈ ball p r, ∀ v : TangentSpace 𝓘(ℝ, E3) z,
      |mvfderiv 𝓘(ℝ, E3) f z v| ≤ M * Real.sqrt (g.inner z v v))
    {x : X} (hx : x ∈ ball p r) :
    |f x - f p| ≤ M * dist p x := by
  let _ : RiemannianBundle (fun y : X => TangentSpace 𝓘(ℝ, E3) y) := ⟨g.toRiemannianMetric⟩
  have _ : IsRiemannianManifold 𝓘(ℝ, E3) X := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  have hxr : dist p x < r := by rw [dist_comm]; exact mem_ball.mp hx
  refine le_of_forall_pos_lt_add fun τ hτ => ?_
  set τ' : ℝ := min (τ / (2 * M)) ((r - dist p x) / 2) with hτ'
  have hτ'0 : 0 < τ' := lt_min (by positivity) (by linarith)
  have hτ'2 : τ' ≤ (r - dist p x) / 2 := min_le_right _ _
  have hlt : Manifold.riemannianEDist 𝓘(ℝ, E3) p x < ENNReal.ofReal (dist p x + τ') := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
  have hin : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ball p r := by
    intro t ht
    have h1 := Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
    have h2 : Manifold.pathELength 𝓘(ℝ, E3) γ 0 t ≤ Manifold.pathELength 𝓘(ℝ, E3) γ 0 1 :=
      Manifold.pathELength_mono le_rfl ht.2
    have h3 : Manifold.riemannianEDist 𝓘(ℝ, E3) p (γ t) < ENNReal.ofReal r :=
      (h1.trans h2).trans_lt (hlen.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist] at h3
    rw [mem_ball, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp h3
  have hcurve := ofReal_abs_sub_le_mul_pathELength g hγ (f := f)
    (fun t ht => hf _ (hin t ht)) hM
    (fun t ht v => hb _ (hin t (Ioo_subset_Icc_self ht)) v)
  rw [hγ0, hγ1] at hcurve
  have hfin := hcurve.trans (mul_le_mul' le_rfl hlen.le)
  rw [← ENNReal.ofReal_mul hM.le] at hfin
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfin
  have hτ2 : M * τ' ≤ τ / 2 := by
    have h1 : τ' ≤ τ / (2 * M) := min_le_left _ _
    calc M * τ' ≤ M * (τ / (2 * M)) := mul_le_mul_of_nonneg_left h1 hM.le
      _ = τ / 2 := by field_simp
  nlinarith

omit [CompactSpace X] [IsManifold 𝓘(ℝ, E3) ∞ X] in
/-- The second component of the derivative of `x ↦ (f₀ x, f₁ x)` is the derivative of `f₁`. -/
theorem mvfderiv_edgeRef_one_KA5 {f₀ f₁ : X → ℝ} {y : X}
    (hJ : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (edgeReferenceCoordinates ![f₀, f₁]) y)
    (v : TangentSpace 𝓘(ℝ, E3) y) :
    mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![f₀, f₁]) y v 1 = mvfderiv 𝓘(ℝ, E3) f₁ y v := by
  let projection : ℝ² →L[ℝ] ℝ := PiLp.proj 2 (fun _i : Fin 2 => ℝ) 1
  have hprojection : projection ∘ edgeReferenceCoordinates ![f₀, f₁] = f₁ := rfl
  have hh := _root_.mvfderiv_comp_apply y projection.differentiableAt.mdifferentiableAt hJ v
  rw [hprojection, mvfderiv_eq_fderiv, projection.fderiv] at hh
  exact hh.symm

variable {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- **The height row of the collar at a collar point, in physical form.** At a collar point `p`
of the edge chart `j` (`p ∈ B(j, 100Δρ(j))`, `|η_j(p)| ≤ 10Δ`, `Δ/10 ≤ t(p) ≤ 10Δ`, `t = F/ρ`), the
second real coordinate `h` of the collar's `(2, β_c)` plane map is the real coordinate of a
rank-one `(1, β_c)`-splitting of `(X, ρ(p)⁻¹ d, p)`, and `t` satisfies the long test
`|ρ(p) dt(w₀) − (ρ(p)/d(y, z))(h(z) − h(y))| < γ_c` along every physical unit minimizing direction
`w₀` from `y ∈ B(p, 100ρ(p))` to `z ∈ B(p, 100ρ(p)/γ_c)` with `d(y, z) > ρ(p)`. -/
theorem EdgeFamily.collar_height_KA5
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {j : X} (hj : j ∈ F.centres)
    {p : X} (hp : p ∈ ball j (100 * Δ * ρ j)) (hcoord : |F.coord j p| ≤ 10 * Δ)
    (h1 : Δ / 10 ≤ F.smoothing p / ρ p) (h2 : F.smoothing p / ρ p ≤ 10 * Δ) :
    ∃ hh : X → ℝ,
      (∃ φ : @KleinerLottApprox X (WithLp 2 (ℝ¹ × ℝ))
          (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 (0, (0 : ℝ))) βc,
        ∀ z, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ _ _ _
          φ z).fst = EuclideanSpace.single 0 (hh z)) ∧
      ∀ y ∈ ball p (100 * ρ p), ∀ z ∈ ball p (100 * ρ p / γc), ρ p < dist y z →
        ∀ w₀ : TangentSpace 𝓘(ℝ, E3) y, g.inner y w₀ w₀ = 1 →
        (∀ (R : ℝ) (hR : 0 < R),
          let hMc : CompleteSpace X := complete_of_compact
          letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
          letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
          letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
          let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
            scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
          have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
            isMetricNorm_of_riemannianBundle gR
          intrinsicGeodesic gR hnR y (R • w₀) (dist y z) = z) →
        |ρ p * mvfderiv 𝓘(ℝ, E3) (fun x => F.smoothing x / ρ x) y w₀ -
          ρ p / dist y z * (hh z - hh y)| < γc := by
  have hd : (ρ j)⁻¹ * dist p j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hp
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrp := hρ p
  let Fs := F.smoothing
  have hq : ∀ y, Fs y / ρ j / (ρ y / ρ j) = Fs y / ρ y := fun y => by
    have := hρ y
    field_simp
  have hqf : (fun y => Fs y / ρ j / (ρ y / ρ j)) = fun y => Fs y / ρ y := funext hq
  have hmetq := MetricSpace.rescale_inv_ratio mX hrj hrp
  unfold EdgeFamily.coord at hcoord
  rw [dite_eq_left hj] at hcoord
  have hWall : ∀ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) y), g.inner y w₀ w₀ = 1 →
      (scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hrj) 2) g).inner y (ρ j • w₀)
        (ρ j • w₀) = 1 := fun y w₀ hw₀ => by
    rw [scaleMetric_inner, gInner_smul_self, hw₀]
    field_simp
  have hlinall : ∀ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) y),
      mvfderiv 𝓘(ℝ, E3) (fun z => Fs z / ρ j / (ρ z / ρ j)) y (ρ j • w₀) =
        ρ j * mvfderiv 𝓘(ℝ, E3) (fun z => Fs z / ρ j / (ρ z / ρ j)) y w₀ := fun y w₀ => by
    rw [map_smul, smul_eq_mul]
  have e1all : ∀ a : ℝ, ρ p / ρ j * (ρ j * a) = ρ p * a := fun a => by field_simp
  have e2all : ∀ d : ℝ, ((ρ j)⁻¹ * d / (ρ p / ρ j))⁻¹ = ρ p / d := fun d => by
    by_cases hd0 : d = 0
    · simp [hd0]
    · field_simp
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  have hmem : p ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hd
  have hcoord' : |C.coord p| ≤ 10 * Δ := hcoord
  have h1' : Δ / 10 ≤ Fs p / ρ j / (ρ p / ρ j) := by rw [hq]; exact h1
  have h2' : Fs p / ρ j / (ρ p / ρ j) ≤ 10 * Δ := by rw [hq]; exact h2
  obtain ⟨hqq, ⟨Φ, hΦ⟩, hJsm, -, -, -, -, htest⟩ := C.collar p hmem hcoord' h1' h2'
  refine ⟨fun z => (@planeComparisonMap X mR C.Qn C.center p Δ (ρ p / ρ j) z).snd, ?_, ?_⟩
  · let Φs := @KleinerLottApprox.mapTargetIsometryAt X _ _
      ((mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).rescale (ρ p / ρ j)⁻¹ (inv_pos.mpr (div_pos hrp hrj)))
      _ _ _ _ _ Φ planeSwap_KA5 (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) rfl
    obtain ⟨φ', hφ'⟩ := exists_finOne_split_KA3 Φs
    obtain ⟨φ'', hφ''⟩ := exists_kla_transport_KA3 hmetq φ'
    refine ⟨φ'', fun z => ?_⟩
    rw [hφ'' z, hφ' z]
    congr 1
    change (@KleinerLottApprox.toFun X _
      ((mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).rescale (ρ p / ρ j)⁻¹ (inv_pos.mpr (div_pos hrp hrj)))
      _ _ _ _ Φ z).snd = _
    rw [hΦ z]
  · intro y hy z hz hsep w₀ hw₀ hgeo
    have hy1 : @dist X mX.toDist y p < 100 * ρ p := hy
    have hz1 : @dist X mX.toDist z p < 100 * ρ p / γc := hz
    have hy' : y ∈ ball p (100 * (ρ p / ρ j)) := by
      change (ρ j)⁻¹ * @dist X mX.toDist y p < 100 * (ρ p / ρ j)
      rw [inv_mul_lt_iff₀ hrj]
      field_simp
      linarith
    have hy300 : y ∈ ball p (300 * (ρ p / ρ j)) := by
      change (ρ j)⁻¹ * @dist X mX.toDist y p < 300 * (ρ p / ρ j)
      rw [inv_mul_lt_iff₀ hrj]
      field_simp
      linarith
    have hz' : z ∈ ball p (100 * (ρ p / ρ j) / γc) := by
      change (ρ j)⁻¹ * @dist X mX.toDist z p < 100 * (ρ p / ρ j) / γc
      have e : 100 * (ρ p / ρ j) / γc = (ρ j)⁻¹ * (100 * ρ p / γc) := by ring
      rw [e]
      exact mul_lt_mul_of_pos_left hz1 (inv_pos.mpr hrj)
    have hsep' : ρ p / ρ j < (ρ j)⁻¹ * @dist X mX.toDist y z := by
      have e : ρ p / ρ j = (ρ j)⁻¹ * ρ p := by ring
      rw [e]
      exact mul_lt_mul_of_pos_left hsep (inv_pos.mpr hrj)
    have hT := htest y hy' z hz' hsep' (ρ j • w₀) (hWall y w₀ hw₀) (hgeo (ρ j) hrj)
    have hJd := (hJsm.contMDiffAt (isOpen_ball.mem_nhds hy300)).mdifferentiableAt (by simp)
    have h1c := lt_of_le_of_lt (abs_euclid_one_sub_le_KA2 _ _) hT
    rw [PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply, planeReferenceIsometry_apply_one,
      planeReferenceIsometry_apply_one, smul_eq_mul, smul_eq_mul,
      mvfderiv_edgeRef_one_KA5 hJd, hlinall y w₀, hqf] at h1c
    have hdist : @dist X mR.toDist y z = (ρ j)⁻¹ * @dist X mX.toDist y z := rfl
    rw [hdist] at h1c
    rw [e1all, e2all] at h1c
    exact h1c

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP04_KA5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP04_KA5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP04_KA5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP04, height saturation.** At `x ∈ D_i`, for a height `h` with (TR)
`‖(h(z) − h(p_i)) e₀ − A u_i(z)‖ < E₀` on `B(i, 1000ρ(i))` and the collar's long height test at
`p_i` (`0 < γ_c ≤ 1/5`, `β₂ ≤ 1/1000`), some `g`-unit `w₀` has `ρ(i) dt(w₀) ≥ 1 − ε` and
`(A(ρ(i) dη_i(w₀)))₀ ≥ 1 − ε`, `ε = γ + γ_c + E₀ + β₂`. -/
theorem height_component_saturation_KA5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) {x : X} (hx : x ∈ ball i (10 * ρ i)) (hγc : 0 < γc)
    (hγc1 : γc ≤ 1 / 5) (hβ : β 2 ≤ 1 / 1000) {E₀ : ℝ} (hE : E₀ ≤ 1) {t hh : X → ℝ}
    (A : ℝ² →L[ℝ] ℝ¹) (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖EuclideanSpace.single 0 (hh z - hh i) - A (circleRaw_KA3 P i z)‖ < E₀)
    (htest : ∀ y ∈ ball i (100 * ρ i), ∀ z ∈ ball i (100 * ρ i / γc), ρ i < dist y z →
        ∀ w₀ : TangentSpace 𝓘(ℝ, E3) y, g.inner y w₀ w₀ = 1 →
        (∀ (R : ℝ) (hR : 0 < R),
          let hMc : CompleteSpace X := complete_of_compact
          letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
          letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
          letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
          let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
            scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
          have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
            isMetricNorm_of_riemannianBundle gR
          intrinsicGeodesic gR hnR y (R • w₀) (dist y z) = z) →
        |ρ i * mvfderiv 𝓘(ℝ, E3) t y w₀ - ρ i / dist y z * (hh z - hh y)| < γc) :
    ∃ w₀ : TangentSpace 𝓘(ℝ, E3) x, g.inner x w₀ w₀ = 1 ∧
      1 - (γ + γc + E₀ + β 2) ≤ ρ i * mvfderiv 𝓘(ℝ, E3) t x w₀ ∧
      1 - (γ + γc + E₀ + β 2) ≤
        A (ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w₀) 0 := by
  have hri := hρ i
  have hγ0 := circle_quality_nonneg_KA4 P hi
  have hE0 : 0 ≤ E₀ := by
    have := hTR i (by rw [dist_self]; positivity)
    exact (norm_nonneg _).trans this.le
  have hβ0 : 0 ≤ β 2 := by
    let Ai := P.circleAdapted i hi
    let _ := Ai.instY
    exact (@KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ _ _
      Ai.split).le
  obtain ⟨hξ1, hAξ, hin⟩ := coisometry_adjoint_single_KA4 A hA 0
  set ξ := ContinuousLinearMap.adjoint A (EuclideanSpace.single (0 : Fin 1) 1) with hξdef
  obtain ⟨y, hd1, hd2, hyi, hlift⟩ := circle_reference_lift_KA4 P hi hx hβ ξ hξ1
  have hdpos : 0 < dist x y := lt_of_lt_of_le (by positivity) hd1
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hdpos; exact lt_irrefl _ hdpos
  obtain ⟨w₀, hw₀, hseg⟩ := exists_scaled_minimizing_seg_KA4 g hmetric hxy
  obtain ⟨y', -, hy'y, hgy⟩ := hseg (dist x y) dist_nonneg le_rfl
  have hyy : y' = y := dist_le_zero.mp (by linarith)
  rw [hyy] at hgy
  have hxi : dist x i < 10 * ρ i := mem_ball.mp hx
  have hxi2 : x ∈ ball i (200 * ρ i) := by rw [mem_ball]; linarith
  have hyi2 : y ∈ ball i (201 * 10000 * ρ i) := by rw [mem_ball]; linarith
  have hT := circle_test_of_scaled_KA4 P hi hxi2 hyi2 (by linarith) w₀ hw₀ hgy
  have hq : 1 / (400 + 3 * β 2) ≤ ρ i / dist x y := by
    rw [div_le_div_iff₀ (by linarith) hdpos]
    linarith
  obtain ⟨r₁, hr₁, hc₁⟩ := reference_component_vector_KA4 hξ1 hlift hT
  have href : 1 - (γ + 0 + β 2) ≤
      A (ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w₀) 0 := by
    rw [hin]
    exact saturation_scalar_KA4 hq hβ0 hβ le_rfl zero_le_one (by linarith) hc₁
  have hx100 : x ∈ ball i (100 * ρ i) := by rw [mem_ball]; linarith
  have hy100 : y ∈ ball i (100 * ρ i / γc) := by
    rw [mem_ball, lt_div_iff₀ hγc]
    nlinarith
  have hown0 := htest x hx100 y hy100 (by linarith) w₀ hw₀ hgy
  have hg := zero_gain_KA5 A hA hAξ (hTR y (by linarith)) (hTR x (by linarith)) hlift
  set r₂ := hh y - hh i - (hh x - hh i) - 400 with hr₂
  have hratio : ρ i / dist x y * (hh y - hh x) = ρ i / dist x y * (400 + r₂) := by
    rw [hr₂]; ring
  rw [hratio] at hown0
  have hown := saturation_scalar_KA4 hq hβ0 hβ hE0 hE hg hown0.le
  exact ⟨w₀, hw₀, by linarith, by linarith⟩

/-- **TCP04, height derivative clause** (FC15 with `k = 1`): under the hypotheses of
`height_component_saturation_KA5`, with `t` differentiable at `x` and `(1 + γ_c)/ρ(i)`-Lipschitz on
`B(i, 100ρ(i))`, every tangent vector `w` at `x` has
`‖dt(w) e₀ − A dη_i(w)‖ ≤ 2√(4ε + ε²) · √(ρ(i)⁻² g(w, w))`, `ε = γ + γ_c + E₀ + β₂`. -/
theorem height_derivative_comparison_KA5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) {x : X} (hx : x ∈ ball i (10 * ρ i)) (hγc : 0 < γc)
    (hγc1 : γc ≤ 1 / 5) (hβ : β 2 ≤ 1 / 1000) {E₀ : ℝ} (hE : E₀ ≤ 1) {t hh : X → ℝ}
    (hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) t x)
    (hlip : ∀ y ∈ ball i (100 * ρ i), ∀ z ∈ ball i (100 * ρ i),
      |t y - t z| ≤ (1 + γc) / ρ i * dist y z)
    (A : ℝ² →L[ℝ] ℝ¹) (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖EuclideanSpace.single 0 (hh z - hh i) - A (circleRaw_KA3 P i z)‖ < E₀)
    (htest : ∀ y ∈ ball i (100 * ρ i), ∀ z ∈ ball i (100 * ρ i / γc), ρ i < dist y z →
        ∀ w₀ : TangentSpace 𝓘(ℝ, E3) y, g.inner y w₀ w₀ = 1 →
        (∀ (R : ℝ) (hR : 0 < R),
          let hMc : CompleteSpace X := complete_of_compact
          letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
          letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
          letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
          let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
            scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
          have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
            isMetricNorm_of_riemannianBundle gR
          intrinsicGeodesic gR hnR y (R • w₀) (dist y z) = z) →
        |ρ i * mvfderiv 𝓘(ℝ, E3) t y w₀ - ρ i / dist y z * (hh z - hh y)| < γc)
    (w : TangentSpace 𝓘(ℝ, E3) x) :
    ‖EuclideanSpace.single 0 (mvfderiv 𝓘(ℝ, E3) t x w) -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
      2 * Real.sqrt (4 * (γ + γc + E₀ + β 2) + (γ + γc + E₀ + β 2) ^ 2) *
        Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  let _ := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr hri)
  have hnorm : ∀ v : TangentSpace 𝓘(ℝ, E3) x, ‖v‖ = Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) :=
    norm_tangent_radialScaled_KA4 g hri x
  have hγ0 := circle_quality_nonneg_KA4 P hi
  have hE0 : 0 ≤ E₀ := by
    have := hTR i (by rw [dist_self]; positivity)
    exact (norm_nonneg _).trans this.le
  have hβ0 : 0 ≤ β 2 := by
    let Ai := P.circleAdapted i hi
    let _ := Ai.instY
    exact (@KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ _ _
      Ai.split).le
  set ε' := γ + γc + E₀ + β 2 with hε'
  have hε0 : 0 ≤ ε' := by positivity
  have hxi : x ∈ ball i (200 * ρ i) := by
    rw [mem_ball]; have := mem_ball.mp hx; linarith
  have hx100 : x ∈ ball i (100 * ρ i) := by
    rw [mem_ball]; have := mem_ball.mp hx; linarith
  set f : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ¹ :=
    (mvfderiv 𝓘(ℝ, E3) t x).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) with hfdef
  set gg : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ² :=
    mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x with hgdef
  have hfv : ∀ v, f v = EuclideanSpace.single 0 (mvfderiv 𝓘(ℝ, E3) t x v) := fun v => by
    rw [hfdef, smulRight_single_apply_KA4]
  have hlipd : ∀ v, |mvfderiv 𝓘(ℝ, E3) t x v| ≤ (1 + γc) / ρ i * Real.sqrt (g.inner x v v) :=
    fun v => abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx100 hdiff hlip v
  have hrows : ∀ a : Fin 1, ‖(EuclideanSpace.proj a : StrongDual ℝ ℝ¹).comp f‖ ≤ 1 + ε' := by
    intro a
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hfa : ((EuclideanSpace.proj a : StrongDual ℝ ℝ¹).comp f) v =
        mvfderiv 𝓘(ℝ, E3) t x v := by
      fin_cases a
      change (f v) 0 = _
      rw [hfv]
      simp
    rw [hfa, Real.norm_eq_abs, hnorm v]
    have hsq : (1 + γc) / ρ i * Real.sqrt (g.inner x v v) =
        (1 + γc) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hri).le]
      field_simp
    have hv0 := Real.sqrt_nonneg ((ρ i)⁻¹ ^ 2 * g.inner x v v)
    calc |mvfderiv 𝓘(ℝ, E3) t x v| ≤ (1 + γc) / ρ i * Real.sqrt (g.inner x v v) := hlipd v
      _ = (1 + γc) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := hsq
      _ ≤ (1 + ε') * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := by
          have : 1 + γc ≤ 1 + ε' := by linarith
          exact mul_le_mul_of_nonneg_right this hv0
  have hgb : ‖gg‖ ≤ 1 + ε' := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have h := circleAdapted_gram_upper_KA2 P hγ0 hi hxi v
    rw [hnorm v]
    have hv0 := Real.sqrt_nonneg ((ρ i)⁻¹ ^ 2 * g.inner x v v)
    calc ‖gg v‖ ≤ (1 + γ) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := h
      _ ≤ (1 + ε') * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := by
          have : 1 + γ ≤ 1 + ε' := by linarith
          exact mul_le_mul_of_nonneg_right this hv0
  have htests : ∀ a : Fin 1, ∃ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖w‖ = 1 ∧ 1 - ε' ≤ f w a ∧ 1 - ε' ≤ A (gg w) a := by
    intro a
    obtain ⟨w₀, hw₀, ho, hr⟩ := height_component_saturation_KA5 P hi hx hγc hγc1 hβ hE A hA hTR
      htest
    refine ⟨ρ i • w₀, ?_, ?_, ?_⟩
    · rw [hnorm, gInner_smul_self, hw₀]
      have : (ρ i)⁻¹ ^ 2 * (ρ i ^ 2 * 1) = 1 := by field_simp
      rw [this, Real.sqrt_one]
    · fin_cases a
      change 1 - ε' ≤ (f (ρ i • w₀)) 0
      rw [hfv, map_smul, smul_eq_mul]
      simpa using ho
    · fin_cases a
      have hge : gg (ρ i • w₀) =
          ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w₀ := map_smul _ _ _
      change 1 - ε' ≤ A (gg (ρ i • w₀)) 0
      rw [hge]
      exact hr
  have hR := DifferentialGeometry.Geometry.Fibration.norm_difference_of_common_directions f gg A hA
    hε0 hrows hgb htests
  have hw := (f - A.comp gg).le_opNorm w
  rw [hnorm w] at hw
  have hcast : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [hcast, one_mul] at hR
  have hfw : (f - A.comp gg) w = EuclideanSpace.single 0 (mvfderiv 𝓘(ℝ, E3) t x w) -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w) := by
    rw [sub_apply, hfv]
    rfl
  rw [← hfw]
  exact hw.trans (mul_le_mul_of_nonneg_right hR (Real.sqrt_nonneg _))

omit [CompactSpace X] in
/-- A vector of `ℝ¹` minus a vector of the form `e₀ a`: `‖e₀ a − v‖ = |a − v₀|`. -/
theorem norm_single_sub_eq_KA5 (a : ℝ) (v : ℝ¹) :
    ‖EuclideanSpace.single 0 a - v‖ = |a - v 0| := by
  have hv : v = EuclideanSpace.single 0 (v 0) := by
    ext m
    fin_cases m
    simp
  rw [hv, ← PiLp.single_sub, PiLp.norm_single, Real.norm_eq_abs]
  simp

/-- **TCP04, height value clause** (integration along near-minimal paths in `D_i`): if at every
`z ∈ D_i` the function `t` and the reference coordinate are differentiable and
`‖dt(w) e₀ − A dη_i(w)‖ ≤ (θ/20)√(ρ(i)⁻² g(w, w))`, then
`‖(t(x) − t(p_i)) e₀ − A(η_i(x) − η_i(p_i))‖ ≤ θ/2` on `D_i`. -/
theorem height_value_KA5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) {θ : ℝ} (hθ : 0 < θ) {t : X → ℝ}
    (A : ℝ² →L[ℝ] ℝ¹)
    (hdiff : ∀ z ∈ ball i (10 * ρ i), MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) t z)
    (hder : ∀ z ∈ ball i (10 * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) z,
      ‖EuclideanSpace.single 0 (mvfderiv 𝓘(ℝ, E3) t z w) -
          A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) z w)‖ ≤
        θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner z w w))
    {x : X} (hx : x ∈ ball i (10 * ρ i)) :
    ‖EuclideanSpace.single 0 (t x - t i) -
        A (cgpCircleCoord P.toLocalChartFamily i hi x -
          cgpCircleCoord P.toLocalChartFamily i hi i)‖ ≤
      θ / 2 := by
  have hri := hρ i
  set η := cgpCircleCoord P.toLocalChartFamily i hi with hηdef
  let L : ℝ² →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 1) : StrongDual ℝ ℝ¹).comp A
  set f : X → ℝ := fun z => t z - L (η z) with hfdef
  have hηd : ∀ z ∈ ball i (10 * ρ i), MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) η z := fun z hz =>
    ((cgpCircleCoord_contMDiffOn P.toLocalChartFamily hi).contMDiffAt
      (isOpen_ball.mem_nhds (by rw [mem_ball]; have := mem_ball.mp hz; linarith))).mdifferentiableAt
      (by simp)
  have hLd : ∀ z ∈ ball i (10 * ρ i), MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => L (η y)) z :=
    fun z hz => L.differentiableAt.mdifferentiableAt.comp z (hηd z hz)
  have hLder : ∀ z ∈ ball i (10 * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) z,
      mvfderiv 𝓘(ℝ, E3) (fun y => L (η y)) z w = L (mvfderiv 𝓘(ℝ, E3) η z w) := by
    intro z hz w
    have hh := _root_.mvfderiv_comp_apply z L.differentiableAt.mdifferentiableAt (hηd z hz) w
    have hc : L ∘ η = fun y => L (η y) := rfl
    rw [hc, mvfderiv_eq_fderiv, L.fderiv] at hh
    exact hh
  have hfd : ∀ z ∈ ball i (10 * ρ i), MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f z := fun z hz =>
    (hdiff z hz).sub (hLd z hz)
  have hfb : ∀ z ∈ ball i (10 * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) z,
      |mvfderiv 𝓘(ℝ, E3) f z w| ≤ θ / 20 * (ρ i)⁻¹ * Real.sqrt (g.inner z w w) := by
    intro z hz w
    have hsub : mvfderiv 𝓘(ℝ, E3) f z w =
        mvfderiv 𝓘(ℝ, E3) t z w - L (mvfderiv 𝓘(ℝ, E3) η z w) := by
      rw [hfdef, mvfderiv_fun_sub (hdiff z hz) (hLd z hz), sub_apply, hLder z hz w]
    rw [hsub]
    have h := hder z hz w
    rw [norm_single_sub_eq_KA5] at h
    have hsq : Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner z w w) = (ρ i)⁻¹ * Real.sqrt (g.inner z w w) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hri).le]
    rw [hsq] at h
    calc |mvfderiv 𝓘(ℝ, E3) t z w - L (mvfderiv 𝓘(ℝ, E3) η z w)| ≤
        θ / 20 * ((ρ i)⁻¹ * Real.sqrt (g.inner z w w)) := h
      _ = θ / 20 * (ρ i)⁻¹ * Real.sqrt (g.inner z w w) := by ring
  have hmv := abs_sub_le_of_mvfderiv_le_ball_KA5 g hmetric (by positivity) hfd hfb hx
  rw [norm_single_sub_eq_KA5, map_sub, PiLp.sub_apply]
  have hxi : dist i x < 10 * ρ i := by rw [dist_comm]; exact mem_ball.mp hx
  have hL : ∀ v, L v = (A v) 0 := fun v => rfl
  have he : t x - t i - ((A (η x)) 0 - (A (η i)) 0) = f x - f i := by
    simp only [hfdef, hL]
    ring
  rw [he]
  calc |f x - f i| ≤ θ / 20 * (ρ i)⁻¹ * dist i x := hmv
    _ ≤ θ / 20 * (ρ i)⁻¹ * (10 * ρ i) := by
        apply mul_le_mul_of_nonneg_left hxi.le
        positivity
    _ = θ / 2 := by field_simp; ring

/-- **TCP04, high branch kernel**: at a circle centre `i`, a height `t` smooth on `D_i` with
values in `[Δ/10, 181Δ/20]`, `(1 + γ_c)/ρ(i)`-Lipschitz on `B(i, 100ρ(i))`, with a rank-one
comparison height `h` ((TR) at `θ²/(2·10⁵)` for a coisometry `A`) and the collar's long test at
`p_i`, satisfies (TH) with `B = A` when `γ, γ_c ≤ θ²/10⁵`, `0 < γ_c`, `β₂ ≤ θ²/(2·10⁵)`. -/
theorem tcp04_high_KA5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hγ : γ ≤ θ ^ 2 / 100000) (hγc : 0 < γc) (hγcθ : γc ≤ θ ^ 2 / 100000)
    (hβ2 : β 2 ≤ θ ^ 2 / 200000) {t hh : X → ℝ}
    (hrange : ∀ x ∈ ball i (10 * ρ i), Δ / 10 ≤ t x ∧ t x ≤ 181 * Δ / 20)
    (hsmooth : ∀ x ∈ ball i (10 * ρ i), ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ t x)
    (hlip : ∀ y ∈ ball i (100 * ρ i), ∀ z ∈ ball i (100 * ρ i),
      |t y - t z| ≤ (1 + γc) / ρ i * dist y z)
    (A : ℝ² →L[ℝ] ℝ¹) (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖EuclideanSpace.single 0 (hh z - hh i) - A (circleRaw_KA3 P i z)‖ < θ ^ 2 / 200000)
    (htest : ∀ y ∈ ball i (100 * ρ i), ∀ z ∈ ball i (100 * ρ i / γc), ρ i < dist y z →
        ∀ w₀ : TangentSpace 𝓘(ℝ, E3) y, g.inner y w₀ w₀ = 1 →
        (∀ (R : ℝ) (hR : 0 < R),
          let hMc : CompleteSpace X := complete_of_compact
          letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
          letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
          letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
          let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
            scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
          have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
            isMetricNorm_of_riemannianBundle gR
          intrinsicGeodesic gR hnR y (R • w₀) (dist y z) = z) →
        |ρ i * mvfderiv 𝓘(ℝ, E3) t y w₀ - ρ i / dist y z * (hh z - hh y)| < γc) :
    ∀ x ∈ ball i (10 * ρ i),
      Δ / 10 ≤ t x ∧ t x ≤ 181 * Δ / 20 ∧ ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ t x ∧
      ‖EuclideanSpace.single 0 (t x - t i) -
          A (cgpCircleCoord P.toLocalChartFamily i hi x -
            cgpCircleCoord P.toLocalChartFamily i hi i)‖ ≤ θ / 2 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖EuclideanSpace.single 0 (mvfderiv 𝓘(ℝ, E3) t x w) -
            A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) ∧
        |mvfderiv 𝓘(ℝ, E3) t x w| ≤ 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hθ21 : θ ^ 2 < 1 := by nlinarith
  have hγc1 : γc ≤ 1 / 5 := by nlinarith
  have hβ1000 : β 2 ≤ 1 / 1000 := by nlinarith
  have hE1 : θ ^ 2 / 200000 ≤ 1 := by nlinarith
  have hγ0 := circle_quality_nonneg_KA4 P hi
  have hβ0 : 0 ≤ β 2 := by
    let Ai := P.circleAdapted i hi
    let _ := Ai.instY
    exact (@KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ _ _
      Ai.split).le
  have hder : ∀ x ∈ ball i (10 * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖EuclideanSpace.single 0 (mvfderiv 𝓘(ℝ, E3) t x w) -
          A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
        θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
    intro x hx w
    have hd := height_derivative_comparison_KA5 P hi hx hγc hγc1 hβ1000 hE1
      ((hsmooth x hx).mdifferentiableAt (by simp)) hlip A hA hTR htest w
    set ε' := γ + γc + θ ^ 2 / 200000 + β 2 with hε'
    have hε0 : 0 ≤ ε' := by positivity
    have hbud := riesz_budget_KA4 (θ := θ / 10) (by positivity) (by linarith) (ε := ε') hε0
      (by nlinarith)
    have hmono : 2 * Real.sqrt (4 * ε' + ε' ^ 2) ≤ 2 * Real.sqrt (2 * (4 * ε' + ε' ^ 2)) := by
      have : 4 * ε' + ε' ^ 2 ≤ 2 * (4 * ε' + ε' ^ 2) := by nlinarith
      have := Real.sqrt_le_sqrt this
      linarith
    have h20 : θ / 10 / 2 = θ / 20 := by ring
    rw [h20] at hbud
    exact hd.trans (mul_le_mul_of_nonneg_right (hmono.trans hbud) (Real.sqrt_nonneg _))
  intro x hx
  refine ⟨(hrange x hx).1, (hrange x hx).2, hsmooth x hx,
    height_value_KA5 P hi hθ A (fun z hz => (hsmooth z hz).mdifferentiableAt (by simp)) hder hx,
    fun w => ⟨hder x hx w, ?_⟩⟩
  have hx100 : x ∈ ball i (100 * ρ i) := by
    rw [mem_ball]; have := mem_ball.mp hx; linarith
  have hb := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx100
    ((hsmooth x hx).mdifferentiableAt (by simp)) hlip w
  have hsq : Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) = (ρ i)⁻¹ * Real.sqrt (g.inner x w w) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hri).le]
  rw [hsq]
  have hv0 := Real.sqrt_nonneg (g.inner x w w)
  calc |mvfderiv 𝓘(ℝ, E3) t x w|
      ≤ (1 + γc) / ρ i * Real.sqrt (g.inner x w w) := hb
    _ ≤ 2 * ((ρ i)⁻¹ * Real.sqrt (g.inner x w w)) := by
        rw [div_eq_mul_inv]
        have : (1 + γc) ≤ 2 := by linarith
        have h0 : 0 ≤ (ρ i)⁻¹ * Real.sqrt (g.inner x w w) := by positivity
        nlinarith

/-- **TCP04, the height (TR).** For a target error `E₀` and the exclusion quality `ν`
(`3ν ≤ β₃ < 1`) there are an early `σ` and a collar splitting bound `η_c` (independent of `Δ`,
TCP02's kernel with rank one and displacement `0`) such that, with `3β₂ ≤ σ`, `β_c ≤ η_c` and
`σ⁻¹ ≤ Lmax`: at every circle centre `i`, every height `h` that is the real coordinate of a
normalized rank-one `(1, β_c)`-splitting of `(X, ρ(i)⁻¹ d, p_i)` has one unit row `A : ℝ² → ℝ¹` with
(TR) `‖(h(z) − h(p_i)) e₀ − A u_i(z)‖ < E₀` on `B(p_i, 1000ρ(i))` (`u_i = circleRaw_KA3`). -/
theorem height_raw_alignment_KA6 {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ ηc : ℝ, 0 < ηc ∧
    ∀ {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → βc ≤ ηc → σ⁻¹ ≤ Lmax →
      ∀ i, i ∈ P.circle.centres → ∀ hh : X → ℝ,
      (∃ φ : @KleinerLottApprox X (WithLp 2 (ℝ¹ × ℝ))
          (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 (0, (0 : ℝ))) βc,
        ∀ z, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ _ _ _
          φ z).fst = EuclideanSpace.single 0 (hh z)) →
      ∃ A : ℝ² →L[ℝ] ℝ¹, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ z, dist z i < 1000 * ρ i →
          ‖EuclideanSpace.single 0 (hh z - hh i) - A (circleRaw_KA3 P i z)‖ < E₀ := by
  obtain ⟨σ₁, hσ₁, hσ₁1, h1⟩ := tcp02_pair_KA3 hE hν hν1 (j := 1) le_rfl one_le_two
  obtain ⟨ηc, hηc, hk1⟩ := h1 0 le_rfl
  refine ⟨σ₁, hσ₁, hσ₁1, ηc, hηc, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hν3
    hβ3 hβ2σ hβc hσL i hi hh ⟨φ, hφ⟩
  have hri := hρ i
  have hsec₁ := tcp02_sectional_KA3 P hσ₁ (by linarith) hσL i
  have hno := circle_no_three_KA3 P.circle hi hν3 hβ3
  let Ai := P.circleAdapted i hi
  have hc12 : (1 / 2 : ℝ) ≤ ρ i / ρ i := by rw [div_self hri.ne']; norm_num
  have hc2 : ρ i / ρ i ≤ 2 := by rw [div_self hri.ne']; norm_num
  have hd0 : dist i i ≤ 0 * ρ i := by rw [dist_self, zero_mul]
  obtain ⟨A, hA, hal⟩ := @hk1 X mX _ _ _ g hmetric i i (ρ i) (ρ i) hri hri hc12 hc2 hd0 hsec₁
    hno ℝ Ai.Y _ Ai.instY (0 : ℝ) Ai.a βc (β 2) hβc hβ2σ φ Ai.split
  refine ⟨A, hA, fun z hz => ?_⟩
  have hmain := hal z hz
  rw [hφ z, hφ i, div_self hri.ne', one_smul, one_smul, sub_right_comm, single_zero_sub_KA5]
    at hmain
  rw [circleRaw_KA3_eq P hi]
  exact hmain

/-- **TCP04** (`lem:fibration-first-height-comparison`, B:5442) on `LocalChartPackets`: for an
early `0 < θ < 1` (and `ν`, `3ν ≤ β₃ < 1`) there are an early `σ`, a circle quality bound `η₂`,
one adaptation bound `γ₀` (for the circle quality `γ` and the collar quality `γ_c`) and a collar
splitting bound `η_c` (all independent of `Δ`) such that, with FC07's ranges, `Δ ≥ 1200`,
`0 ≤ ε ≤ 1`, `0 ≤ σ_c ≤ 1`, `3β₂ ≤ σ`, `β₂ ≤ η₂`, `γ ≤ γ₀`, `0 < γ_c ≤ γ₀`, `β_c ≤ η_c` and
`σ⁻¹ ≤ Lmax`, at every circle centre `i` (`t = F/ρ`): if no edge support meets `D_i` every edge
cutoff vanishes on `D_i`; otherwise either the LOW branch holds on `D_i` (`t < 3Δ/20`, the edge
cutoffs are their coordinate profiles: height factor one) or the HIGH branch: one unit row
`B : ℝ² → ℝ¹` with, on `D_i`, `Δ/10 ≤ t ≤ 181Δ/20`, `t` smooth,
`‖(t − t(p_i)) e₀ − B(η_i − η_i(p_i))‖ ≤ θ/2`, `‖dt(w) e₀ − B dη_i(w)‖ ≤ (θ/20)|w|` and
`|dt(w)| ≤ 2|w|` in the norm of `ρ(i)⁻² g`. -/
theorem tcp04_row {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ ηc : ℝ, 0 < ηc ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → 1200 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ 1 → 3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ →
      γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres),
        ((∀ j ∈ P.edge.centres, ¬ (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty) →
          ∀ j, ∀ x ∈ ball i (10 * ρ i), P.edge.cutoff j x = 0) ∧
        ((∃ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty) →
          (∀ x ∈ ball i (10 * ρ i), P.edge.smoothing x / ρ x < 3 * Δ / 20 ∧
            ∀ j ∈ P.edge.centres, x ∈ ball j (100 * Δ * ρ j) →
              P.edge.cutoff j x = edgeCoordinateProfile (P.edge.coord j x / Δ)) ∨
          ∃ B : ℝ² →L[ℝ] ℝ¹, B.comp (ContinuousLinearMap.adjoint B) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x ∈ ball i (10 * ρ i),
              Δ / 10 ≤ P.edge.smoothing x / ρ x ∧ P.edge.smoothing x / ρ x ≤ 181 * Δ / 20 ∧
              ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => P.edge.smoothing y / ρ y) x ∧
              ‖EuclideanSpace.single 0 (P.edge.smoothing x / ρ x - P.edge.smoothing i / ρ i) -
                  B (cgpCircleCoord P.toLocalChartFamily i hi x -
                    cgpCircleCoord P.toLocalChartFamily i hi i)‖ ≤ θ / 2 ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                ‖EuclideanSpace.single 0
                      (mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x w) -
                    B (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                  θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) ∧
                |mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x w| ≤
                  2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) := by
  have hE₀ : (0 : ℝ) < θ ^ 2 / 200000 := by positivity
  obtain ⟨σ₁, hσ₁, hσ₁1, ηc, hηc, hk⟩ := height_raw_alignment_KA6 hE₀ hν hν1
  refine ⟨σ₁, hσ₁, hσ₁1, θ ^ 2 / 200000, hE₀, θ ^ 2 / 100000, by positivity, ηc, hηc, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hΛ hΔ
    hμ hτ hLΛ hLmax he hT hε hε1 hσc0 hσc1 hν3 hβ3 hβ2σ hβ2 hγ hγc hγcθ hβc hσL i hi
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hθ21 : θ ^ 2 < 1 := by nlinarith
  refine ⟨fun hnone j x hx => ?_, fun ⟨j, hj, hmeet⟩ => ?_⟩
  · by_contra hne
    have hjc := (P.edge.mem_of_cutoff_ne_zero hΔ0 hne).1
    exact hnone j hjc ⟨x, subset_tsupport _ hne, hx⟩
  obtain ⟨q, hqt, hqD⟩ := hmeet
  obtain ⟨q', hq'D, hq'⟩ := mem_closure_iff.mp hqt _ isOpen_ball hqD
  obtain ⟨-, hq'j, hq'η, hq't⟩ := P.edge.mem_of_cutoff_ne_zero hΔ0 hq'
  obtain ⟨-, -, -, hedge, -, -⟩ := fc07_input_packet P hΛ (by linarith) hμ hτ hLΛ hLmax he hT i
  obtain ⟨hratio, hdist, hsub1, -, -⟩ := hedge j hj ⟨q, hqt, hqD⟩
  have hΛ1 : Λ ≤ 1 / 100000000000 := by nlinarith
  have hnear : infDist i ({j} : Set X) ≤ 30 * Δ * ρ i := by
    rw [Metric.infDist_singleton, dist_comm]
    nlinarith
  rcases fc14_row P.toLocalChartFamily hΛ hε hε1 (R := 10) (by norm_num) (by linarith)
      (by nlinarith) (by nlinarith) hq'D hq't.le hnear with hlow | ⟨-, hhigh⟩
  · exact Or.inl hlow
  right
  have hrj := hρ j
  have hrj2 : 1 / 2 * ρ i ≤ ρ j := by have := hratio.1; rwa [le_div_iff₀ hri] at this
  have hball_j : ∀ x ∈ ball i (10 * ρ i), x ∈ ball j (100 * Δ * ρ j) := fun x hx => by
    have h := mem_ball.mp (hsub1 hx)
    rw [mem_ball]
    have h' : (14 * Δ + 4 * 10) * ρ j ≤ 100 * Δ * ρ j :=
      mul_le_mul_of_nonneg_right (by linarith) hrj.le
    linarith
  have hcoordx : ∀ x ∈ ball i (10 * ρ i), |P.edge.coord j x| ≤ 10 * Δ := by
    intro x hx
    have hl := EdgeFamily.coord_lipschitz_KA2 P.edge (by linarith) hj x q'
    have hxq : dist x q' < 20 * ρ i := by
      have := dist_triangle x i q'
      rw [dist_comm i q'] at this
      linarith [mem_ball.mp hx, mem_ball.mp hq'D]
    have h2 : (1 + σc) / ρ j * dist x q' ≤ 80 := by
      have ha : (1 + σc) / ρ j ≤ 2 / ρ j := div_le_div_of_nonneg_right (by linarith) hrj.le
      have hb : (1 + σc) / ρ j * dist x q' ≤ 2 / ρ j * (20 * ρ i) :=
        mul_le_mul ha hxq.le dist_nonneg (by positivity)
      have hc : 2 / ρ j * (20 * ρ i) ≤ 80 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hrj]
        linarith
      linarith
    have := abs_sub_abs_le_abs_sub (P.edge.coord j x) (P.edge.coord j q')
    linarith
  have hcol : ∀ x ∈ ball i (10 * ρ i), Δ / 10 ≤ P.edge.smoothing x / ρ x ∧
      P.edge.smoothing x / ρ x ≤ 10 * Δ := fun x hx => by
    obtain ⟨⟨h1, h2⟩, -⟩ := hhigh x hx
    exact ⟨h1, by linarith⟩
  have hii : i ∈ ball i (10 * ρ i) := mem_ball_self (by positivity)
  obtain ⟨hh, hφ, htest⟩ := P.edge.collar_height_KA5 hj (hball_j i hii) (hcoordx i hii)
    (hcol i hii).1 (hcol i hii).2
  obtain ⟨-, hlip⟩ := P.edge.height_lipschitz_of_collar_KA2 hj (hball_j i hii) (hcoordx i hii)
    (hcol i hii).1 (hcol i hii).2
  obtain ⟨A, hA, hTR⟩ := hk P hν3 hβ3 hβ2σ hβc hσL i hi hh hφ
  have hsmooth : ∀ x ∈ ball i (10 * ρ i),
      ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => P.edge.smoothing y / ρ y) x := fun x hx =>
    P.edge.contMDiffAt_height_of_collar hj (hball_j x hx) (hcoordx x hx) (hcol x hx).1
      (hcol x hx).2
  exact ⟨A, hA, tcp04_high_KA5 P hi hθ hθ1 hγ hγc hγcθ hβ2 (fun x hx => (hhigh x hx).1) hsmooth
    hlip A hA hTR htest⟩
end DifferentialGeometry.Geometry.Collapse
