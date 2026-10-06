import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceBasesV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Fibration.ActualCircleGram

/-!
# A4 / G11 (lane B-BASES-PORT), group G1 (PARTIAL): stage submersions on the boundary chain

Port of C14-BASES G5 (`Gaf02Chain.stage_submersion_circle_BAS`) to `C : BoundaryGaf02ChainE DP …`
by the CHART ROUTE (the V3 plane specs carry no (PP) surjectivity): on the original threshold-6
plateau of a chart, `κ_j ∘ F_∂ = η_j`, the native map is the smoothing map of the stage input, and
`D(κ_j ∘ f⁰)` is a small perturbation of `dη_j`, which is quantitatively onto (TCP01 long test /
LFR20.1).

* abstract kernels: `surjective_of_unit_approx_BBP`, `surjective_of_apply_ne_zero_BBP`,
  `kappa_error_BBP`, `kappa_error_gen_BBP`, `adjustmentMap_of_one_of_top_BBP`,
  `starProjection_adjustmentMap_of_one_BBP`;
* chart lemmas: `circleAdapted_gram_lower_BBP` (copy of B-PORT-A's undelivered
  `circleAdapted_gram_lower_KA2_BAUGP`), `SlimCentreOn.derivative_BBP`,
  `SlimCentreOn.enclosure_BBP`;
* supply level: `circleKappa_BBP`, `slimKappa_BBP`, plateau neighbourhoods, `κ_j ∘ F_∂ = η_j`,
  `D > 4` on the plateaus, `slim_derivative_lower_BBP`;
* chain level: `native_zero_eventuallyEq_BBP`, generic `native_eventuallyEq_BBP`,
  `native_mvfderiv_BBP`, `stage_tube_BBP`, `stage_deriv_close_BBP`, and
  **`BoundaryGaf02ChainE.stage_submersion_circle_BBP`** (register premises `β₂ ≤ 10⁻⁷`, `γ ≤ 1/2`).
  The slim and edge stage submersions are NOT in this file (handover: state-B-BASES-PORT.md).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section GramBBP

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNG_BBP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNG_BBP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCG_BBP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The lower Gram bound of the circle coordinate** (TCP01): at every point of `B(j, 200ρ(j))` and
for every unit `ξ ∈ ℝ²` there is a unit vector `w` of the normalized metric `ρ(j)⁻² g` with
`‖dη_j(w) − ξ‖ < γ + β₂` (the long test of packet (i) toward a coverage point at distance `10⁶`
in the direction `ξ`). -/
theorem circleAdapted_gram_lower_BBP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (hβ : β 2 ≤ 1 / 10000000) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) (ξ : ℝ²) (hξ : ‖ξ‖ = 1) :
    ∃ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 ∧
      ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P j hj) x w - ξ‖ < γ + β 2 := by
  have hrj := hρ j
  have hn : (ρ j)⁻¹ * dist x j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hc := P.circle.chart_center j hj
  set η := cgpCircleCoord_BAUGP P j hj with hηdef
  let A := P.circleAdapted j hj
  let c := P.circle.chart j hj
  have htest := A.test
  let Yt := A.Y
  let iY : MetricSpace Yt := A.instY
  let sp := A.split
  let a := A.a
  let hMc : CompleteSpace X := ‹CompleteSpace X›
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


/-- **LFR20.1 in physical form** (copy of `SlimCentre.derivative_GAFC` for `SlimCentreOn`): at
`x ∈ B(j, .91Lρ(j))` there is a unit vector `w` of `ρ(j)⁻²g` with `dη_j(w) > 3/4`. -/
theorem SlimCentreOn.derivative_BBP {β₁ : ℝ} {j : X} (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j)
    {x : X} (hx : dist x j < 91 / 100 * (10 ^ 6 * Δ) * ρ j) :
    ∃ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 ∧
      3 / 4 < mvfderiv 𝓘(ℝ, E3) c.coord_BCG2 x w := by
  have hr := hρ j
  have hd : (ρ j)⁻¹ * dist x j < 91 / 100 * (10 ^ 6 * Δ) := by
    rw [inv_mul_lt_iff₀ hr]
    linarith
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  obtain ⟨w, hw, hdw⟩ := P.derivative x hd
  refine ⟨w, ?_, hdw⟩
  rw [scaleMetric_inner] at hw
  exact hw

/-- **LFR20.2 in physical form**: a point of `B(j, Lρ(j))` with `|η_j| ≤ 905·10³Δ` lies in
`B(j, .91Lρ(j))`. -/
theorem SlimCentreOn.enclosure_BBP {β₁ : ℝ} {j : X} (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j)
    {x : X} (hx : dist x j < 10 ^ 6 * Δ * ρ j) (hc : |c.coord_BCG2 x| ≤ 905 * 10 ^ 3 * Δ) :
    dist x j < 91 / 100 * (10 ^ 6 * Δ) * ρ j := by
  have hr := hρ j
  have hd : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := by
    rw [inv_mul_lt_iff₀ hr]
    linarith
  have h' : (ρ j)⁻¹ * dist x j < 91 / 100 * (10 ^ 6 * Δ) := by
    let P := c.packet
    let iZ := c.instZ
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let kR : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    exact P.enclosure x hd hc
  rw [inv_mul_lt_iff₀ hr] at h'
  linarith

end GramBBP

/-- **Surjectivity from approximate unit preimages**: a linear map into a finite-dimensional
inner product space that comes within distance `< 1` of every unit vector is onto. -/
theorem surjective_of_unit_approx_BBP {V F : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (A : V →ₗ[ℝ] F)
    (h : ∀ ξ : F, ‖ξ‖ = 1 → ∃ v, ‖A v - ξ‖ < 1) : Surjective A := by
  by_contra hns
  have hne : LinearMap.range A ≠ ⊤ := fun h' => hns (LinearMap.range_eq_top.mp h')
  have hperp : (LinearMap.range A)ᗮ ≠ ⊥ := by
    intro hbot
    exact hne (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨ξ₀, hξ₀K, hξ₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  have hn0 : ‖ξ₀‖ ≠ 0 := norm_ne_zero_iff.mpr hξ₀
  set ξ : F := ‖ξ₀‖⁻¹ • ξ₀ with hξdef
  have hξ : ‖ξ‖ = 1 := by
    rw [hξdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn0]
  have hξK : ξ ∈ (LinearMap.range A)ᗮ := Submodule.smul_mem _ _ hξ₀K
  obtain ⟨v, hv⟩ := h ξ hξ
  have horth : inner ℝ (A v) ξ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).mp hξK (A v) (LinearMap.mem_range_self A v)
  have hsq : ‖A v - ξ‖ * ‖A v - ξ‖ = ‖A v‖ * ‖A v‖ + ‖ξ‖ * ‖ξ‖ :=
    norm_sub_sq_eq_norm_sq_add_norm_sq_real horth
  rw [hξ] at hsq
  have h0 : 0 ≤ ‖A v - ξ‖ := norm_nonneg _
  nlinarith [mul_self_nonneg ‖A v‖]

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The circle chart coordinate of `H^∂`: `κ_j = ρ_j⁻¹ u_j` (closed `ρ_j⁻¹ • gafCircleVector`). -/
def circleKappa_BBP (j : S.CircleIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ² :=
  (S.rho j.1)⁻¹ • S.circleVector_BAUGD j

/-- `‖κ_j‖ ≤ ρ_j⁻¹`. -/
theorem norm_circleKappa_le_BBP (j : S.CircleIdx_BAUGD) :
    ‖S.circleKappa_BBP j‖ ≤ (S.rho j.1)⁻¹ := by
  have hr := S.rho_pos j.1
  unfold circleKappa_BBP
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have h1 : ‖S.circleVector_BAUGD j‖ ≤ 1 := norm_blockVectorCLM_le _
  calc (S.rho j.1)⁻¹ * ‖S.circleVector_BAUGD j‖ ≤ (S.rho j.1)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hr).le
    _ = (S.rho j.1)⁻¹ := mul_one _

/-- The circle coordinate of BIFACE is the family's chart coordinate on `W°`. -/
theorem circleEta_eq_coord_BBP (j : S.CircleIdx_BAUGD) :
    S.circleEta_BIF j.1 =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.family.circle.coord_BAUGA j.1) := by
  funext q
  rw [S.circleEta_eq_circleCoordW_BAUGD, S.circleCoordW_val_BAUGD]

/-- **The original threshold-`6` circle plateau is a neighbourhood** of each of its points
(in `W°`). -/
theorem circle_plateau_mem_nhds_BBP (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    letI := inducedMetricSpace S.completion.metric
    {q' : W.pieceInterior ⊤ | dist q' j.1 < 200 * S.rho j.1 ∧
      ‖S.circleEta_BIF j.1 q'‖ < 6} ∈ 𝓝 q := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hball : ball j.1 (200 * S.rho j.1) ∈ 𝓝 q := isOpen_ball.mem_nhds hq
  have hcont : ContinuousAt (S.circleEta_BIF j.1) q := by
    rw [S.circleEta_eq_coord_BBP j]
    exact ((S.family.circle.contMDiffOn_coord_BAUGA hj).continuousOn.continuousAt hball)
  have hpre : S.circleEta_BIF j.1 ⁻¹' ball 0 6 ∈ 𝓝 q :=
    hcont.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; exact hη))
  filter_upwards [hball, hpre] with q' h1 h2
  exact ⟨h1, by simpa [mem_ball_zero_iff] using h2⟩

/-- **On the plateau the circle chart coordinate of `F_∂` is `η_j`**: `κ_j(F_∂ q') = η_j(q')` near
`q` (`ζ_j = 1` on `{‖η_j‖ ≤ 8}`). -/
theorem circleKappa_boundaryOriginalMap_eventuallyEq_BBP (j : S.CircleIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    (fun q' : W.pieceInterior ⊤ => S.circleKappa_BBP j (S.boundaryOriginalMap q'.val)) =ᶠ[𝓝 q]
      S.circleEta_BIF j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  filter_upwards [S.circle_plateau_mem_nhds_BBP j hq hη] with q' hq'
  obtain ⟨hd, hη'⟩ := hq'
  have hd' := inv_mul_dist_lt_of_mem_ball_LC87 (X := W.pieceInterior ⊤)
    (ρ := fun x : W.pieceInterior ⊤ => S.rho x) (S.rho_pos j.1) (mem_ball.mpr hd)
  have hcut : S.family.circle.cutoff j.1 q' = 1 := by
    have h8 : ‖S.family.circle.coord_BAUGA j.1 q'‖ ≤ 8 := by
      rw [← congrFun (S.circleEta_eq_coord_BBP j) q']
      linarith
    simp only [CircleFamilyOn.coord_BAUGA, hj, ↓reduceDIte] at h8
    exact S.family.circle.cutoff_eq_one j.1 hj q' hd' h8
  have hblk := (S.circleBlock_boundaryOriginalMap_BAUGD j q'.val).1
  rw [S.circleCutoffW_val_BAUGD, S.circleCoordW_val_BAUGD, hcut, mul_one] at hblk
  have hr := S.rho_pos j.1
  change (S.rho j.1)⁻¹ • S.circleVector_BAUGD j (S.boundaryOriginalMap q'.val) = _
  rw [hblk, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
    congrFun (S.circleEta_eq_coord_BBP j) q']

/-- **A plateau point is far from `∂W`**: `D(q) > 4` on the threshold-`6` circle plateau (the circle
slot of `F_int` is nonzero there; B-DFB: non-scale slots live in `{D > 4}`). -/
theorem four_le_distanceToBoundary_of_circle_plateau_BBP (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) (j : S.CircleIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hne : (.inl j : S.IntTag_BAUGA) ≠ S.scaleTag_BAUGA := by simp [scaleTag_BAUGA]
  have hd' := inv_mul_dist_lt_of_mem_ball_LC87 (X := W.pieceInterior ⊤)
    (ρ := fun x : W.pieceInterior ⊤ => S.rho x) (S.rho_pos j.1) (mem_ball.mpr hq)
  have hcut : S.family.circle.cutoff j.1 q = 1 := by
    have h8 : ‖S.family.circle.coord_BAUGA j.1 q‖ ≤ 8 := by
      rw [← congrFun (S.circleEta_eq_coord_BBP j) q]
      linarith
    simp only [CircleFamilyOn.coord_BAUGA, hj, ↓reduceDIte] at h8
    exact S.family.circle.cutoff_eq_one j.1 hj q hd' h8
  have hslot : S.boundaryOriginalMap q.val (Sum.inl (.inl j)) =
      S.interiorMapOn_BAUGA q (.inl j) := by
    change S.intSlotW_BAUGA (.inl j) q.val = _
    simp only [intSlotW_BAUGA, hne, ↓reduceIte]
    exact Subtype.val_injective.extend_apply _ _ q
  have hmk := (S.circleBlock_boundaryOriginalMap_BAUGD j q.val).2
  rw [S.circleCutoffW_val_BAUGD, hcut, mul_one] at hmk
  have hnz : S.interiorMapOn_BAUGA q (.inl j) ≠ 0 := by
    intro h0
    have h1 : S.circleMarker_BAUGD j (S.boundaryOriginalMap q.val) = 0 := by
      change (S.boundaryOriginalMap q.val (Sum.inl (.inl j))).snd = 0
      rw [hslot, h0]
      rfl
    rw [hmk] at h1
    exact (S.rho_pos j.1).ne' h1
  exact (S.four_lt_distanceToBoundary_of_mem_tsupport_slot_BDFB hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hne
    (subset_tsupport _ hnz)).le

/-- BIFACE's circle coordinate is the chart coordinate `cgpCircleCoord` of the family. -/
theorem circleEta_eq_cgpCircleCoord_BBP (j : S.CircleIdx_BAUGD) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    S.circleEta_BIF j.1 = cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB j.1
      ((Set.Finite.mem_toFinset _).mp j.2) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  funext q
  simp only [circleEta_BIF, hj, ↓reduceDIte]
  rfl

/-- The slim chart coordinate of `H^∂`: `κ_j = ρ_j⁻¹ proj₀ u_j` (closed `gaf07SlimCoord_GAFC`). -/
def slimKappa_BBP (j : S.SlimIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  (S.rho j.1)⁻¹ • ((EuclideanSpace.proj (0 : Fin 2)).comp (S.slimVector_BAUGD j))

/-- `‖κ_j‖ ≤ ρ_j⁻¹` (slim). -/
theorem norm_slimKappa_le_BBP (j : S.SlimIdx_BAUGD) : ‖S.slimKappa_BBP j‖ ≤ (S.rho j.1)⁻¹ := by
  have hr := S.rho_pos j.1
  unfold slimKappa_BBP
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have h1 : ‖(EuclideanSpace.proj (0 : Fin 2)).comp (S.slimVector_BAUGD j)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [one_mul, ContinuousLinearMap.comp_apply]
    refine (PiLp.norm_apply_le (S.slimVector_BAUGD j y) 0).trans ?_
    exact (S.slimVector_BAUGD j).le_opNorm y |>.trans (by
      have h2 : ‖S.slimVector_BAUGD j‖ ≤ 1 := norm_blockVectorCLM_le _
      nlinarith [norm_nonneg y])
  calc (S.rho j.1)⁻¹ * ‖(EuclideanSpace.proj (0 : Fin 2)).comp (S.slimVector_BAUGD j)‖
      ≤ (S.rho j.1)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hr).le
    _ = (S.rho j.1)⁻¹ := mul_one _

/-- The slim coordinate of BIFACE is the slim centre's chart coordinate on `W°`. -/
theorem slimEta_eq_coord_fun_BBP (j : S.SlimIdx_BAUGD) :
    S.slimEta_BIF j.1 =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       (S.family.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2) :=
  funext (S.slimEta_eq_coord_BAUGP2 j)

/-- **The original threshold-`6` slim plateau is a neighbourhood** of each of its points. -/
theorem slim_plateau_mem_nhds_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) :
    letI := inducedMetricSpace S.completion.metric
    {q' : W.pieceInterior ⊤ | dist q' j.1 < 1000000 * Δ * S.rho j.1 ∧
      |S.slimEta_BIF j.1 q'| < 6 * (10 ^ 5 * Δ)} ∈ 𝓝 q := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hball : ball j.1 (1000000 * Δ * S.rho j.1) ∈ 𝓝 q := isOpen_ball.mem_nhds hq
  have hball' : ball j.1 (10 ^ 6 * Δ * S.rho j.1) ∈ 𝓝 q := by
    have : (10 : ℝ) ^ 6 = 1000000 := by norm_num
    rw [this]
    exact hball
  have hcont : ContinuousAt (S.slimEta_BIF j.1) q := by
    rw [S.slimEta_eq_coord_fun_BBP j]
    exact ((S.family.slim.centre j.1 _).contMDiffOn_coord_BAUGA.continuousOn.continuousAt hball')
  have hpre : S.slimEta_BIF j.1 ⁻¹' {t | |t| < 6 * (10 ^ 5 * Δ)} ∈ 𝓝 q :=
    hcont.preimage_mem_nhds ((isOpen_lt continuous_abs continuous_const).mem_nhds hη)
  filter_upwards [hball, hpre] with q' h1 h2
  exact ⟨h1, h2⟩

/-- The slim cutoff is `1` on the threshold-`6` plateau. -/
theorem slim_cutoff_eq_one_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) (hΔ : 0 ≤ Δ) :
    S.slimCutoffW_BAUGP2 j q.val = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.slimCutoffW_val_BAUGP2, S.family.slim.cutoff_BCNT_of_mem hj]
  refine (S.family.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le_BAUGP2 ?_ ?_
  · rw [mem_ball]
    convert hq using 2
    norm_num
  · rw [← S.slimEta_eq_coord_BAUGP2 j q]
    have : 6 * (10 ^ 5 * Δ) ≤ 8 * 10 ^ 5 * Δ := by nlinarith
    linarith

/-- **On the plateau the slim chart coordinate of `F_∂` is `η_j`** near `q`. -/
theorem slimKappa_boundaryOriginalMap_eventuallyEq_BBP (j : S.SlimIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) (hΔ : 0 ≤ Δ) :
    (fun q' : W.pieceInterior ⊤ => S.slimKappa_BBP j (S.boundaryOriginalMap q'.val)) =ᶠ[𝓝 q]
      S.slimEta_BIF j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  filter_upwards [S.slim_plateau_mem_nhds_BBP j hq hη] with q' hq'
  have hcut := S.slim_cutoff_eq_one_BBP j hq'.1 hq'.2 hΔ
  have hblk := (S.slimBlock_boundaryOriginalMap_BAUGP2 j q'.val).1
  rw [hcut, mul_one, S.slimCoordW_val_BAUGP2] at hblk
  have hr := S.rho_pos j.1
  change (S.rho j.1)⁻¹ • (EuclideanSpace.proj (0 : Fin 2)) (S.slimVector_BAUGD j
    (S.boundaryOriginalMap q'.val)) = _
  rw [hblk, map_smul, planeAxis_apply, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    S.slimEta_eq_coord_BAUGP2 j q']
  have hp : (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 1 := by simp
  rw [hp]
  field_simp

/-- **A slim plateau point is far from `∂W`**: `D(q) > 4`. -/
theorem four_le_distanceToBoundary_of_slim_plateau_BBP (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) (j : S.SlimIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) :
    ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val := by
  have hne : (.inr (.inl j) : S.IntTag_BAUGA) ≠ S.scaleTag_BAUGA := by simp [scaleTag_BAUGA]
  have hcut := S.slim_cutoff_eq_one_BBP j hq hη hΔ.le
  have hslot : S.boundaryOriginalMap q.val (Sum.inl (.inr (.inl j))) =
      S.interiorMapOn_BAUGA q (.inr (.inl j)) := by
    change S.intSlotW_BAUGA (.inr (.inl j)) q.val = _
    simp only [intSlotW_BAUGA, hne, ↓reduceIte]
    exact Subtype.val_injective.extend_apply _ _ q
  have hmk := (S.slimBlock_boundaryOriginalMap_BAUGP2 j q.val).2
  rw [hcut, mul_one] at hmk
  have hnz : S.interiorMapOn_BAUGA q (.inr (.inl j)) ≠ 0 := by
    intro h0
    have h1 : S.slimMarker_BAUGD j (S.boundaryOriginalMap q.val) = 0 := by
      change (S.boundaryOriginalMap q.val (Sum.inl (.inr (.inl j)))).snd = 0
      rw [hslot, h0]
      rfl
    rw [hmk] at h1
    exact (S.rho_pos j.1).ne' h1
  exact (S.four_lt_distanceToBoundary_of_mem_tsupport_slot_BDFB hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hne
    (subset_tsupport _ hnz)).le

/-- **LFR20.1 at a slim plateau point**: a unit vector `u` of `ρ_j⁻²ĝ` with `dη_j(u) > 3/4`. -/
theorem slim_derivative_lower_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) (hΔ : 0 ≤ Δ) :
    ∃ u : TangentSpace (𝓡 3) q, (S.rho j.1)⁻¹ ^ 2 * S.completion.metric.inner q u u = 1 ∧
      3 / 4 < mvfderiv (𝓡 3) (S.slimEta_BIF j.1) q u := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hq' : dist q j.1 < 10 ^ 6 * Δ * S.rho j.1 := by
    have : (10 : ℝ) ^ 6 = 1000000 := by norm_num
    rw [this]
    exact hq
  have hc : |(S.family.slim.centre j.1 hj).coord_BCG2 q| ≤ 905 * 10 ^ 3 * Δ := by
    rw [← S.slimEta_eq_coord_BAUGP2 j q]
    have : 6 * (10 ^ 5 * Δ) ≤ 905 * 10 ^ 3 * Δ := by nlinarith
    linarith
  have hin := (S.family.slim.centre j.1 hj).enclosure_BBP hq' hc
  obtain ⟨u, hu1, hu2⟩ := (S.family.slim.centre j.1 hj).derivative_BBP hin
  refine ⟨u, hu1, ?_⟩
  rw [S.slimEta_eq_coord_fun_BBP j]
  exact hu2

end BoundarySupplyCore

/-- **The chart-error estimate** (abstract): `‖κ(Da w) − κ w‖ ≤ k(Ξ‖w‖ + ‖π_{L⊥} w‖)` for
`‖κ‖ ≤ k` and `‖Da − π_L‖ ≤ Ξ`. -/
theorem kappa_error_BBP {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (κ : H →L[ℝ] F) (L : Submodule ℝ H)
    [L.HasOrthogonalProjection] (Da : H →L[ℝ] H) {Ξ k : ℝ} (hk : ‖κ‖ ≤ k)
    (hD : ‖Da - L.starProjection‖ ≤ Ξ) (w : H) :
    ‖κ (Da w) - κ w‖ ≤ k * (Ξ * ‖w‖ + ‖Lᗮ.starProjection w‖) := by
  have hw : L.starProjection w + Lᗮ.starProjection w = w := by
    have h := congrArg (fun T : H →L[ℝ] H => T w)
      L.id_eq_sum_starProjection_self_orthogonalComplement
    simp only [ContinuousLinearMap.id_apply, add_apply] at h
    exact h.symm
  have hsplit : Da w - w = (Da - L.starProjection) w - Lᗮ.starProjection w := by
    calc Da w - w = Da w - (L.starProjection w + Lᗮ.starProjection w) := by rw [hw]
      _ = (Da - L.starProjection) w - Lᗮ.starProjection w := by
        rw [sub_apply]
        abel
  have hk0 : 0 ≤ k := (norm_nonneg _).trans hk
  rw [← map_sub, hsplit]
  calc ‖κ ((Da - L.starProjection) w - Lᗮ.starProjection w)‖
      ≤ ‖κ‖ * ‖(Da - L.starProjection) w - Lᗮ.starProjection w‖ := κ.le_opNorm _
    _ ≤ k * (Ξ * ‖w‖ + ‖Lᗮ.starProjection w‖) := by
      refine mul_le_mul hk ?_ (norm_nonneg _) hk0
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      exact ((Da - L.starProjection).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg w))

/-- **The chart-error estimate with a prior error and a stage projection** (abstract):
`‖κ(Da(Pa)) − κ(Pb)‖ ≤ k(Ξ‖a‖ + ‖a − b‖ + ‖π_{L⊥}(Pb)‖)` for a contraction `P`. -/
theorem kappa_error_gen_BBP {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (κ : H →L[ℝ] F) (L : Submodule ℝ H)
    [L.HasOrthogonalProjection] (P : H →L[ℝ] H) (hP : ∀ u, ‖P u‖ ≤ ‖u‖) (Da : H →L[ℝ] H)
    {Ξ k : ℝ} (hk : ‖κ‖ ≤ k) (hD : ‖Da - L.starProjection‖ ≤ Ξ) (a b : H) :
    ‖κ (Da (P a)) - κ (P b)‖ ≤ k * (Ξ * ‖a‖ + ‖a - b‖ + ‖Lᗮ.starProjection (P b)‖) := by
  have hw : L.starProjection (P b) + Lᗮ.starProjection (P b) = P b := by
    have h := congrArg (fun T : H →L[ℝ] H => T (P b))
      L.id_eq_sum_starProjection_self_orthogonalComplement
    simp only [ContinuousLinearMap.id_apply, add_apply] at h
    exact h.symm
  have hsplit : Da (P a) - P b = ((Da - L.starProjection) (P a) +
      L.starProjection (P a - P b)) - Lᗮ.starProjection (P b) := by
    calc Da (P a) - P b = Da (P a) - (L.starProjection (P b) + Lᗮ.starProjection (P b)) := by
          rw [hw]
      _ = ((Da - L.starProjection) (P a) + L.starProjection (P a - P b)) -
          Lᗮ.starProjection (P b) := by
        rw [sub_apply, map_sub]
        abel
  have hk0 : 0 ≤ k := (norm_nonneg _).trans hk
  have h1 : ‖(Da - L.starProjection) (P a)‖ ≤ Ξ * ‖a‖ :=
    ((Da - L.starProjection).le_opNorm _).trans (mul_le_mul hD (hP a) (norm_nonneg _)
      ((norm_nonneg _).trans hD))
  have h2 : ‖L.starProjection (P a - P b)‖ ≤ ‖a - b‖ := by
    refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
    rw [← map_sub]
    exact hP _
  rw [← map_sub, hsplit]
  calc ‖κ (((Da - L.starProjection) (P a) + L.starProjection (P a - P b)) -
        Lᗮ.starProjection (P b))‖
      ≤ ‖κ‖ * ‖((Da - L.starProjection) (P a) + L.starProjection (P a - P b)) -
          Lᗮ.starProjection (P b)‖ := κ.le_opNorm _
    _ ≤ k * (Ξ * ‖a‖ + ‖a - b‖ + ‖Lᗮ.starProjection (P b)‖) := by
      refine mul_le_mul hk ?_ (norm_nonneg _) hk0
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- An adjustment at cutoff value `1` projects to the smoothing map: `π_QΨ(y) = π_Q a(π_Q y)`. -/
theorem starProjection_adjustmentMap_of_one_BBP {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (a : H → H)
    (ψ : H → ℝ) (y : H) (hψ : ψ y = 1) :
    Q.starProjection (adjustmentMap Q (fun z => Q.starProjection (a z)) ψ y) =
      Q.starProjection (a (Q.starProjection y)) := by
  have hid : ∀ z, Q.starProjection (Q.starProjection z) = Q.starProjection z := fun z =>
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  rw [adjustmentMap_apply, hψ, one_smul, map_add, map_sub, hid, hid]
  abel

/-- A nonzero real-valued linear map is onto. -/
theorem surjective_of_apply_ne_zero_BBP {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : V →ₗ[ℝ] ℝ) {v : V} (hv : A v ≠ 0) : Surjective A := fun y =>
  ⟨(y / A v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩

/-- `π₀ = id` on the v2 slot (the stage-`0` tags are all tags). -/
theorem stageProj_zero_BBP (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ
    γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    (actualSlotsV2_BAUGD S).stageProj 0 y = y := by
  have h : (actualSlotsV2_BAUGD S).stageTagsAug 0 = Finset.univ := by
    change (S.stageTagsV2_BAUGD 0).disjSum Finset.univ = Finset.univ
    change (Finset.univ : Finset S.IntTag_BAUGA).disjSum Finset.univ = Finset.univ
    exact Finset.univ_disjSum_univ
  change blockRestrict ((actualSlotsV2_BAUGD S).stageTagsAug 0) y = y
  rw [h, blockRestrict_univ]
  rfl

/-- `π_{Q₀} = id` on the v2 slot. -/
theorem stageQ_zero_starProjection_BBP (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    ((actualSlotsV2_BAUGD S).stageQ 0).starProjection y = y :=
  (DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) 0) y).trans
    (stageProj_zero_BBP S y)

/-- An adjustment with `π_Q = id` and cutoff value `1` is the smoothing map. -/
theorem adjustmentMap_of_one_of_top_BBP {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (a : H → H) (ψ : H → ℝ) (x : H)
    (hQ : ∀ y, Q.starProjection y = y) (hψ : ψ x = 1) :
    adjustmentMap Q (fun y => Q.starProjection (a y)) ψ x = a x := by
  rw [adjustmentMap_apply, hψ, one_smul, hQ, hQ]
  abel

/-- A stage projection keeps the vector blocks of its stage tags. -/
theorem blockVector_stageProj_BBP (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) (st : Fin 3) {t : S.IntTag_BAUGA}
    (ht : t ∈ S.stageTagsV2_BAUGD st)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inl t)
        ((actualSlotsV2_BAUGD S).stageProj st y) =
      blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inl t)
        y := by
  have hiff : (Sum.inl t : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈
      (actualSlotsV2_BAUGD S).stageTagsAug st := Finset.inl_mem_disjSum.mpr ht
  simp only [blockVectorCLM_apply, BoundaryInteriorSlots_BIF.stageProj, blockRestrict_apply, hiff,
    ite_true]

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **On the circle plateau the native first-stage map is the smoothing map of `F_∂`**:
`f₀⁰ = π₀ g₁ = a₀ ∘ F_∂` near `q` (`ψ₀ = 1` there, `π₀ = id`). -/
theorem native_zero_eventuallyEq_BBP (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    (fun q' : W.pieceInterior ⊤ => C.toChain.nativeStageMap_BIFc 0 q'.val) =ᶠ[𝓝 q]
      fun q' => (C.toChain.slot 0).map (S.boundaryOriginalMap q'.val) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  filter_upwards [S.circle_plateau_mem_nhds_BBP j hq hη] with q' hq'
  have hψ : (actualSlotsV2_BAUGD S).cutoff 0 (S.boundaryOriginalMap q'.val) = 1 :=
    C.toChain.cutoff_bindings.1.2.2.1 q' ⟨j.1, hj, hq'.1, hq'.2⟩
  have e1 : C.toChain.nativeStageMap_BIFc 0 q'.val = C.toChain.g₁ q'.val := by
    simp only [BoundaryGaf02Chain.nativeStageMap_BIFc]
    rw [stageProj_zero_BBP]
    rfl
  have e3 : (actualSlotsV2_BAUGD S).adjust 0 (C.toChain.slot 0).map
      (S.boundaryOriginalMap q'.val) = (C.toChain.slot 0).map (S.boundaryOriginalMap q'.val) :=
    adjustmentMap_of_one_of_top_BBP _ _ _ _ (stageQ_zero_starProjection_BBP S) hψ
  exact e1.trans ((C.toChain.g₁_apply_V2_BAUGD q'.val).trans e3)

/-- A threshold-`6` circle plateau point is a stage-`0` core point. -/
theorem circle_plateau_mem_core_BBP (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) : q ∈ (actualSlotsV2_BAUGD S).stageCore 0 := by
  rw [actualSlotsV2_stageCore_BAUGD]
  exact Set.mem_biUnion (x := (.inl j : S.MarkerIdx_BAUGC)) rfl ⟨hq, hη.le.trans (by norm_num)⟩

include C in
/-- **The circle derivative error at a plateau point**: `‖κ_j(Da₀(F q)(DF v)) − κ_j(DF v)‖ ≤
ρ_j⁻¹(Ξ₀ b_der + e₀)|v|_g` (`‖Da₀ − π_L‖ ≤ Ξ₀`, V3 `normal`, `C.deriv_bound`). -/
theorem circle_native_deriv_close_BBP (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) (v : TangentSpace W.model q.val) :
    ‖S.circleKappa_BBP j (fderiv ℝ (C.toChain.slot 0).map (S.boundaryOriginalMap q.val)
        (mvfderiv W.model S.boundaryOriginalMap q.val v)) -
      S.circleKappa_BBP j (mvfderiv W.model S.boundaryOriginalMap q.val v)‖ ≤
      (S.rho j.1)⁻¹ * ((Ξ 0 * bder + eg 0) * Real.sqrt (g.inner q.val v v)) := by
  have hcore := circle_plateau_mem_core_BBP j hq hη
  have hx : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud 0 := ⟨q, hcore, rfl⟩
  have hΞ := (C.toChain.numbers.1 0).1
  have hsg := (C.toChain.numbers.1 0).2.1
  have hr := (stageRadius_bounds_V2_BAUGD DP hsg.le hcore).1
  have hρq := S.rho_pos q.val
  have h0 : dist (S.boundaryOriginalMap q.val)
      ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)) = 0 :=
    dist_eq_zero.mpr (stageProj_zero_BBP S _).symm
  have hball : S.boundaryOriginalMap q.val ∈ ball ((actualSlotsV2_BAUGD S).stageProj 0
      (S.boundaryOriginalMap q.val)) (DP.stageRadius 0 (Sg 0)
        ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))) := by
    rw [mem_ball, h0]
    have : 0 < 3 / 5 * (Sg 0 * S.rho q.val) := by positivity
    linarith
  have hD := (C.toChain.slot 0).map_deriv_BAUGD hx hball
  have hn : ‖(DP.stagePlane 0 ((actualSlotsV2_BAUGD S).stageProj 0
      (S.boundaryOriginalMap q.val)))ᗮ.starProjection
        (mvfderiv W.model S.boundaryOriginalMap q.val v)‖ ≤
      eg 0 * Real.sqrt (g.inner q.val v v) :=
    (congrArg (fun u => ‖(DP.stagePlane 0 ((actualSlotsV2_BAUGD S).stageProj 0
      (S.boundaryOriginalMap q.val)))ᗮ.starProjection u‖)
      (stageProj_zero_BBP S (mvfderiv W.model S.boundaryOriginalMap q.val v))).symm.trans_le
      (DP.normal_BAUGD 0 _ hx q rfl v)
  have hder := C.deriv_bound q.val v
  have hk := kappa_error_BBP (S.circleKappa_BBP j)
    (DP.stagePlane 0 ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)))
    (fderiv ℝ (C.toChain.slot 0).map (S.boundaryOriginalMap q.val))
    (S.norm_circleKappa_le_BBP j) hD (mvfderiv W.model S.boundaryOriginalMap q.val v)
  refine hk.trans (mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr (S.rho_pos j.1)).le)
  have h1 := mul_le_mul_of_nonneg_left hder hΞ.le
  calc Ξ 0 * ‖mvfderiv W.model S.boundaryOriginalMap q.val v‖ +
        ‖(DP.stagePlane 0 ((actualSlotsV2_BAUGD S).stageProj 0
          (S.boundaryOriginalMap q.val)))ᗮ.starProjection
          (mvfderiv W.model S.boundaryOriginalMap q.val v)‖
      ≤ Ξ 0 * (bder * Real.sqrt (g.inner q.val v v)) + eg 0 * Real.sqrt (g.inner q.val v v) :=
        add_le_add h1 hn
    _ = (Ξ 0 * bder + eg 0) * Real.sqrt (g.inner q.val v v) := by ring

/-- The native-map derivative at a circle plateau point, through the smoothing map:
`D(κ_j ∘ f₀⁰)(q) v = κ_j(Da₀(F q)(DF v))` for `v = dι u`. -/
theorem circle_native_mvfderiv_BBP (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) (u : TangentSpace (𝓡 3) q) :
    mvfderiv W.model (fun p => S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 p)) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u) =
      S.circleKappa_BBP j (fderiv ℝ (C.toChain.slot 0).map (S.boundaryOriginalMap q.val)
        (mvfderiv W.model S.boundaryOriginalMap q.val
          (mfderiv (𝓡 3) W.model Subtype.val q u))) := by
  have hcore := circle_plateau_mem_core_BBP j hq hη
  have hx : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud 0 := ⟨q, hcore, rfl⟩
  have hsg := (C.toChain.numbers.1 0).2.1
  have hr := (stageRadius_bounds_V2_BAUGD DP hsg.le hcore).1
  have hρq := S.rho_pos q.val
  have h0 : dist (S.boundaryOriginalMap q.val)
      ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)) = 0 :=
    dist_eq_zero.mpr (stageProj_zero_BBP S _).symm
  have hball : S.boundaryOriginalMap q.val ∈ ball ((actualSlotsV2_BAUGD S).stageProj 0
      (S.boundaryOriginalMap q.val)) (DP.stageRadius 0 (Sg 0)
        ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))) := by
    rw [mem_ball, h0]
    have : 0 < 3 / 5 * (Sg 0 * S.rho q.val) := by positivity
    linarith
  have hmap : DifferentiableAt ℝ (C.toChain.slot 0).map (S.boundaryOriginalMap q.val) :=
    ((C.toChain.slot 0).map_contDiffAt_BAUGD hx hball).differentiableAt (by simp)
  have hFd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      S.boundaryOriginalMap q.val :=
    ((C.stage_smooth_BAUGD 0) q.val).mdifferentiableAt (by simp)
  have hFv : MDifferentiableAt (𝓡 3)
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (fun q' : W.pieceInterior ⊤ => S.boundaryOriginalMap q'.val) q :=
    hFd.comp q (mdifferentiableAt_val_BCG7 W q)
  have h1d : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stage 1) q.val :=
    ((C.stage_smooth_BAUGD 1) q.val).mdifferentiableAt (by simp)
  have hhd : MDifferentiableAt W.model 𝓘(ℝ, ℝ²)
      (fun p => S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 p)) q.val :=
    ((S.circleKappa_BBP j).comp ((actualSlotsV2_BAUGD S).stageProj 0)).differentiableAt
      |>.comp_mdifferentiableAt h1d
  have hev : (fun q' : W.pieceInterior ⊤ =>
      S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 q'.val)) =ᶠ[𝓝 q]
      fun q' => S.circleKappa_BBP j ((C.toChain.slot 0).map (S.boundaryOriginalMap q'.val)) :=
    (C.native_zero_eventuallyEq_BBP j hq hη).fun_comp (S.circleKappa_BBP j)
  have hin : MDifferentiableAt (𝓡 3)
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (fun q' : W.pieceInterior ⊤ => (C.toChain.slot 0).map (S.boundaryOriginalMap q'.val)) q :=
    DifferentiableAt.comp_mdifferentiableAt (g := (C.toChain.slot 0).map)
      (f := fun q' : W.pieceInterior ⊤ => S.boundaryOriginalMap q'.val) hmap hFv
  have e1 := mvfderiv_comp_val_BCG7 W _ q hhd u
  have e2 := mvfderiv_congr_BDFB hev u
  have e3 := mvfderiv_clm_comp_BDFB (S.circleKappa_BBP j) hin u
  have e4 := mvfderiv_comp_apply_of_differentiableAt_GAF3 hFv hmap u
  have e5 := mvfderiv_comp_val_BCG7 W _ q hFd u
  exact e1.symm.trans (e2.trans (e3.trans (congrArg (S.circleKappa_BBP j)
    (e4.trans (congrArg (fderiv ℝ (C.toChain.slot 0).map (S.boundaryOriginalMap q.val)) e5)))))

include C in
/-- **The chart derivative of `F_∂` on the plateau is that of `η_j`**:
`κ_j(DF_∂(dι u)) = dη_j(u)` (chart coordinate `cgpCircleCoord` of the family). -/
theorem circleKappa_mvfderiv_eq_BBP (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) (u : TangentSpace (𝓡 3) q) :
    S.circleKappa_BBP j (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u)) =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       mvfderiv (𝓡 3) (cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB j.1
        ((Set.Finite.mem_toFinset _).mp j.2)) q u) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hFd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      S.boundaryOriginalMap q.val :=
    ((C.stage_smooth_BAUGD 0) q.val).mdifferentiableAt (by simp)
  have hFv : MDifferentiableAt (𝓡 3)
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (fun q' : W.pieceInterior ⊤ => S.boundaryOriginalMap q'.val) q :=
    hFd.comp q (mdifferentiableAt_val_BCG7 W q)
  have f1 := mvfderiv_comp_val_BCG7 W _ q hFd u
  have f2 := mvfderiv_clm_comp_BDFB (S.circleKappa_BBP j) hFv u
  have f3 := mvfderiv_congr_BDFB (S.circleKappa_boundaryOriginalMap_eventuallyEq_BBP j hq hη) u
  have f4 := congrArg (fun f => mvfderiv (𝓡 3) f q u) (S.circleEta_eq_cgpCircleCoord_BBP j)
  exact (congrArg (S.circleKappa_BBP j) f1).symm.trans (f2.symm.trans (f3.trans f4))

/-- **G1, circle: the stage submersion** (closed twin `Gaf02Chain.stage_submersion_circle_BAS`;
chart route): at every point `q` of the circle chart `j`'s ORIGINAL threshold-`6` plateau,
`D(κ_j ∘ f₀⁰)(q)` is onto `ℝ²` (`κ_j = ρ_j⁻¹u_j`, `f₀⁰` the native first-stage map). Inputs:
TCP01's long test (`circleAdapted_gram_lower_BBP`: every unit `ξ` is `γ + β₂`-close to some
`dη_j(u)`, `u` unit for `ρ_j⁻²ĝ`), `κ_j ∘ F_∂ = η_j` on the plateau, the CFS15 derivative
`‖Da₀ − π_L‖ ≤ Ξ₀`, V3 `normal`, `C.deriv_bound` and the CHOICE budget `Ξ₀b_der + e₀ < c₀ ≤
1/512`. Register premises: `β₂ ≤ 10⁻⁷`, `γ ≤ 1/2`. -/
theorem stage_submersion_circle_BBP (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    Surjective (mfderiv W.model 𝓘(ℝ, ℝ²)
      (fun p => S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 p)) q.val) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb, he, -⟩ := C.std
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hD4 := S.four_le_distanceToBoundary_of_circle_plateau_BBP hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he j
    hq hη
  have heq : ∀ y : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g y →
      S.completion.metric.inner y = (pieceInteriorMetric W g ⊤).inner y := fun y hy =>
    S.completion.inner_eq_on_agree y (S.completion.far_subset_agree hy)
  have hN := C.toChain.numbers
  have hΞ := (hN.1 0).1
  have hsg := (hN.1 0).2.1
  have hbcut := C.bcut_nonneg_BAUGD q.val
  have hbder := C.bder_nonneg_BAUGD q.val
  have hnum : Ξ 0 * bder + eg 0 < 1 / 512 := by
    have h1 : 0 ≤ 5 / 3 * Ξ 0 * Sg 0 * bcut * bder := by positivity
    linarith [hN.2.2.1, hN.2.2.2.1]
  have hr := S.rho_pos j.1
  have key : ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ v, ‖mvfderiv W.model
      (fun p => S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 p)) q.val v - ξ‖ < 1 := by
    intro ξ hξ
    obtain ⟨u, hu1, hu2⟩ := circleAdapted_gram_lower_BBP S.family.toLocalPacketsOnB hβ2 hj hq ξ hξ
    refine ⟨mfderiv (𝓡 3) W.model Subtype.val q u, ?_⟩
    have hgv := inner_mfderiv_val_BCG7 W g S.completion.metric heq q hD4 u u
    have hI : S.completion.metric.inner q u u = S.rho j.1 ^ 2 := by
      have hu1' : (S.rho j.1)⁻¹ ^ 2 * S.completion.metric.inner q u u = 1 := hu1
      field_simp at hu1'
      linarith
    have hsq : Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
        (mfderiv (𝓡 3) W.model Subtype.val q u)) = S.rho j.1 := by
      rw [hgv, hI, Real.sqrt_sq hr.le]
    have hcl := C.circle_native_deriv_close_BBP j hq hη (mfderiv (𝓡 3) W.model Subtype.val q u)
    have hcl' := hcl.trans (le_of_eq (show (S.rho j.1)⁻¹ * ((Ξ 0 * bder + eg 0) *
        Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
          (mfderiv (𝓡 3) W.model Subtype.val q u))) = Ξ 0 * bder + eg 0 by
      rw [hsq]; field_simp))
    rw [C.circle_native_mvfderiv_BBP j hq hη u]
    calc _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _ (S.circleKappa_BBP j
          (mvfderiv W.model S.boundaryOriginalMap q.val
            (mfderiv (𝓡 3) W.model Subtype.val q u))) ξ
      _ < (Ξ 0 * bder + eg 0) + (γ + β 2) := by
        refine add_lt_add_of_le_of_lt hcl' ?_
        rw [C.circleKappa_mvfderiv_eq_BBP j hq hη u]
        exact hu2
      _ ≤ 1 := by linarith
  exact surjective_of_unit_approx_BBP ((mvfderiv W.model
    (fun p => S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 p)) q.val :
      TangentSpace W.model q.val →L[ℝ] ℝ²) : TangentSpace W.model q.val →ₗ[ℝ] ℝ²) key

/-- **On a stage plateau the native map is the projected smoothing map**: if `ψ_st(g_st q') = 1`
on a neighbourhood `U` of `q`, then `f_st⁰ = π_st a_st(π_st g_st)` near `q`. -/
theorem native_eventuallyEq_BBP (st : Fin 3) {q : W.pieceInterior ⊤}
    {U : Set (W.pieceInterior ⊤)} (hU : U ∈ 𝓝 q)
    (hψ : ∀ q' ∈ U, (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc q'.val) = 1) :
    (fun q' : W.pieceInterior ⊤ => C.toChain.nativeStageMap_BIFc st q'.val) =ᶠ[𝓝 q]
      fun q' => (actualSlotsV2_BAUGD S).stageProj st ((C.toChain.slot st).map
        ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q'.val))) := by
  filter_upwards [hU] with q' hq'
  have hπ : ∀ y, ((actualSlotsV2_BAUGD S).stageQ st).starProjection y =
      (actualSlotsV2_BAUGD S).stageProj st y := fun y =>
    DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) y
  have e1 : C.toChain.nativeStageMap_BIFc st q'.val = (actualSlotsV2_BAUGD S).stageProj st
      ((actualSlotsV2_BAUGD S).adjust st (C.toChain.slot st).map
        (C.toChain.stage st.castSucc q'.val)) :=
    congrArg ((actualSlotsV2_BAUGD S).stageProj st) (C.toChain.stage_succ_eq_V2_BAUGD st q'.val)
  have e2 := starProjection_adjustmentMap_of_one_BBP ((actualSlotsV2_BAUGD S).stageQ st)
    (C.toChain.slot st).map ((actualSlotsV2_BAUGD S).cutoff st)
    (C.toChain.stage st.castSucc q'.val) (hψ q' hq')
  exact e1.trans ((hπ _).symm.trans (e2.trans ((hπ _).trans
    (congrArg (fun y => (actualSlotsV2_BAUGD S).stageProj st ((C.toChain.slot st).map y))
      (hπ _)))))

/-- **The native-map derivative on a stage plateau**: for a chart map `κ` with `κ ∘ π_st = κ`,
`D(κ ∘ f_st⁰)(q)(dι u) = κ(Da_st(π_st g_st q)(π_st Dg_st(dι u)))`. -/
theorem native_mvfderiv_BBP (st : Fin 3) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (κ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] F)
    (hκ : ∀ y, κ ((actualSlotsV2_BAUGD S).stageProj st y) = κ y) {q : W.pieceInterior ⊤}
    {U : Set (W.pieceInterior ⊤)} (hU : U ∈ 𝓝 q)
    (hψ : ∀ q' ∈ U, (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc q'.val) = 1)
    (hda : DifferentiableAt ℝ (C.toChain.slot st).map
      ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val)))
    (u : TangentSpace (𝓡 3) q) :
    mvfderiv W.model (fun p => κ (C.toChain.nativeStageMap_BIFc st p)) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u) =
      κ (fderiv ℝ (C.toChain.slot st).map
          ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val))
        ((actualSlotsV2_BAUGD S).stageProj st (mvfderiv W.model (C.toChain.stage st.castSucc)
          q.val (mfderiv (𝓡 3) W.model Subtype.val q u)))) := by
  have hgd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stage st.castSucc) q.val :=
    ((C.stage_smooth_BAUGD st.castSucc) q.val).mdifferentiableAt (by simp)
  have hgv : MDifferentiableAt (𝓡 3)
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (fun q' : W.pieceInterior ⊤ => C.toChain.stage st.castSucc q'.val) q :=
    hgd.comp q (mdifferentiableAt_val_BCG7 W q)
  have hsd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stage st.succ) q.val :=
    ((C.stage_smooth_BAUGD st.succ) q.val).mdifferentiableAt (by simp)
  have hhd : MDifferentiableAt W.model 𝓘(ℝ, F)
      (fun p => κ (C.toChain.nativeStageMap_BIFc st p)) q.val :=
    DifferentiableAt.comp_mdifferentiableAt (g := κ.comp ((actualSlotsV2_BAUGD S).stageProj st))
      (f := C.toChain.stage st.succ) (κ.comp _).differentiableAt hsd
  have hev := (C.native_eventuallyEq_BBP st hU hψ).fun_comp κ
  have hΨ : HasFDerivAt (fun y => κ ((actualSlotsV2_BAUGD S).stageProj st
      ((C.toChain.slot st).map ((actualSlotsV2_BAUGD S).stageProj st y))))
      ((κ.comp ((actualSlotsV2_BAUGD S).stageProj st)).comp
        ((fderiv ℝ (C.toChain.slot st).map ((actualSlotsV2_BAUGD S).stageProj st
          (C.toChain.stage st.castSucc q.val))).comp ((actualSlotsV2_BAUGD S).stageProj st)))
      (C.toChain.stage st.castSucc q.val) :=
    (κ.comp ((actualSlotsV2_BAUGD S).stageProj st)).hasFDerivAt.comp _
      (hda.hasFDerivAt.comp _ ((actualSlotsV2_BAUGD S).stageProj st).hasFDerivAt)
  have e1 := mvfderiv_comp_val_BCG7 W _ q hhd u
  have e2 := mvfderiv_congr_BDFB hev u
  have e3 := mvfderiv_comp_apply_of_differentiableAt_GAF3 hgv hΨ.differentiableAt u
  have e5 := mvfderiv_comp_val_BCG7 W _ q hgd u
  have e4 := hΨ.fderiv
  have e6 : fderiv ℝ (fun y => κ ((actualSlotsV2_BAUGD S).stageProj st
      ((C.toChain.slot st).map ((actualSlotsV2_BAUGD S).stageProj st y))))
      (C.toChain.stage st.castSucc q.val)
      (mvfderiv (𝓡 3) (fun q' : W.pieceInterior ⊤ => C.toChain.stage st.castSucc q'.val) q u) =
      κ ((actualSlotsV2_BAUGD S).stageProj st (fderiv ℝ (C.toChain.slot st).map
          ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val))
        ((actualSlotsV2_BAUGD S).stageProj st (mvfderiv W.model (C.toChain.stage st.castSucc)
          q.val (mfderiv (𝓡 3) W.model Subtype.val q u))))) := by
    rw [e4, e5]
    rfl
  exact e1.symm.trans (e2.trans (e3.trans (e6.trans (hκ _))))

/-- **The stage tube at a core point**: `π_st g_st q ∈ B(x, r_x)` for `x = π_st F_∂ q` when
`‖g_st q − F_∂ q‖ ≤ Eρ(q)`, `E ≤ 3Σ_st/10`. -/
theorem stage_tube_BBP (st : Fin 3) {q : W.pieceInterior ⊤}
    (hcore : q ∈ (actualSlotsV2_BAUGD S).stageCore st) {E : ℝ} (hE0 : 0 ≤ E)
    (hE : E ≤ 3 * Sg st / 10)
    (hyv : ‖C.toChain.stage st.castSucc q.val - S.boundaryOriginalMap q.val‖ ≤ E * S.rho q.val) :
    (actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val) ∈
      ball ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))
        (DP.stageRadius st (Sg st)
          ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))) := by
  have hΞ := (C.toChain.numbers.1 st).1
  have hsg := (C.toChain.numbers.1 st).2.1
  obtain ⟨-, hball, -⟩ := deriv_step_tube_BAUGD DP hΞ.le hsg (C.toChain.stage st.castSucc q.val)
    q hcore hE0 hE hyv
  have hπ : ((actualSlotsV2_BAUGD S).stageQ st).starProjection
      (C.toChain.stage st.castSucc q.val) =
      (actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val) :=
    DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) _
  exact mem_ball.mpr ((congrArg (fun z => dist z ((actualSlotsV2_BAUGD S).stageProj st
    (S.boundaryOriginalMap q.val))) hπ).symm.trans_lt (mem_ball.mp hball))

include C in
/-- **The stage derivative error at a core point** (generic stage): with the tube and the prior
derivative error `H₀` of `g_st`, `‖κ(Da(π g)(π Dg v)) − κ(π DF v)‖ ≤ k(Ξ_st(b_der + H₀) + H₀ +
e_st)|v|_g`. -/
theorem stage_deriv_close_BBP (st : Fin 3) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (κ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] F) {k : ℝ}
    (hk : ‖κ‖ ≤ k) {q : W.pieceInterior ⊤} (hcore : q ∈ (actualSlotsV2_BAUGD S).stageCore st)
    (hball : (actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val) ∈
      ball ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))
        (DP.stageRadius st (Sg st)
          ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))))
    {H₀ : ℝ} (hH : ∀ v : TangentSpace W.model q.val,
      ‖mvfderiv W.model (C.toChain.stage st.castSucc) q.val v -
        mvfderiv W.model S.boundaryOriginalMap q.val v‖ ≤ H₀ * Real.sqrt (g.inner q.val v v))
    (v : TangentSpace W.model q.val) :
    ‖κ (fderiv ℝ (C.toChain.slot st).map
          ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val))
        ((actualSlotsV2_BAUGD S).stageProj st
          (mvfderiv W.model (C.toChain.stage st.castSucc) q.val v))) -
      κ ((actualSlotsV2_BAUGD S).stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val v))‖ ≤
      k * ((Ξ st * (bder + H₀) + H₀ + eg st) * Real.sqrt (g.inner q.val v v)) := by
  have hx : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud st := ⟨q, hcore, rfl⟩
  have hΞ := (C.toChain.numbers.1 st).1
  have hD := (C.toChain.slot st).map_deriv_BAUGD hx hball
  have hn := DP.normal_BAUGD st _ hx q rfl v
  have hder := C.deriv_bound q.val v
  have hP : ∀ u, ‖(actualSlotsV2_BAUGD S).stageProj st u‖ ≤ ‖u‖ := fun u => by
    have h := norm_stageProj_sub_le_BAUGD (Φ := actualSlotsV2_BAUGD S) st u 0
    simpa using h
  have hgen := kappa_error_gen_BBP κ
    (DP.stagePlane st ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)))
    ((actualSlotsV2_BAUGD S).stageProj st) hP _ hk hD
    (mvfderiv W.model (C.toChain.stage st.castSucc) q.val v)
    (mvfderiv W.model S.boundaryOriginalMap q.val v)
  have hk0 : 0 ≤ k := (norm_nonneg _).trans hk
  refine hgen.trans (mul_le_mul_of_nonneg_left ?_ hk0)
  have ha : ‖mvfderiv W.model (C.toChain.stage st.castSucc) q.val v‖ ≤
      (bder + H₀) * Real.sqrt (g.inner q.val v v) := by
    have h1 := norm_le_insert' (mvfderiv W.model (C.toChain.stage st.castSucc) q.val v)
      (mvfderiv W.model S.boundaryOriginalMap q.val v)
    linarith [hH v]
  have h1 := mul_le_mul_of_nonneg_left ha hΞ.le
  calc Ξ st * ‖mvfderiv W.model (C.toChain.stage st.castSucc) q.val v‖ +
        ‖mvfderiv W.model (C.toChain.stage st.castSucc) q.val v -
          mvfderiv W.model S.boundaryOriginalMap q.val v‖ +
        ‖(DP.stagePlane st ((actualSlotsV2_BAUGD S).stageProj st
          (S.boundaryOriginalMap q.val)))ᗮ.starProjection ((actualSlotsV2_BAUGD S).stageProj st
            (mvfderiv W.model S.boundaryOriginalMap q.val v))‖
      ≤ Ξ st * ((bder + H₀) * Real.sqrt (g.inner q.val v v)) +
          H₀ * Real.sqrt (g.inner q.val v v) + eg st * Real.sqrt (g.inner q.val v v) :=
        add_le_add (add_le_add h1 (hH v)) hn
    _ = (Ξ st * (bder + H₀) + H₀ + eg st) * Real.sqrt (g.inner q.val v v) := by ring

/-- A threshold-`6` slim plateau point is a stage-`2` core point. -/
theorem slim_plateau_mem_core_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) (hΔ : 0 ≤ Δ) :
    q ∈ (actualSlotsV2_BAUGD S).stageCore 2 := by
  rw [actualSlotsV2_stageCore_BAUGD]
  refine Set.mem_biUnion (x := (.inr (.inl j) : S.MarkerIdx_BAUGC)) rfl ⟨hq, ?_⟩
  have : 6 * (10 ^ 5 * Δ) ≤ 7 * (100000 * Δ) := by nlinarith
  linarith

include C in
/-- **The slim chart derivative of `F_∂` on the plateau is that of `η_j`**. -/
theorem slimKappa_mvfderiv_eq_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) (u : TangentSpace (𝓡 3) q) :
    S.slimKappa_BBP j (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u)) =
      mvfderiv (𝓡 3) (S.slimEta_BIF j.1) q u := by
  have hΔ := C.std.2.1
  have hFd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      S.boundaryOriginalMap q.val :=
    ((C.stage_smooth_BAUGD 0) q.val).mdifferentiableAt (by simp)
  have hFv : MDifferentiableAt (𝓡 3)
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (fun q' : W.pieceInterior ⊤ => S.boundaryOriginalMap q'.val) q :=
    hFd.comp q (mdifferentiableAt_val_BCG7 W q)
  have f1 := mvfderiv_comp_val_BCG7 W _ q hFd u
  have f2 := mvfderiv_clm_comp_BDFB (S.slimKappa_BBP j) hFv u
  have f3 := mvfderiv_congr_BDFB
    (S.slimKappa_boundaryOriginalMap_eventuallyEq_BBP j hq hη hΔ.le) u
  exact (congrArg (S.slimKappa_BBP j) f1).symm.trans (f2.symm.trans f3)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
