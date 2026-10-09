import DifferentialGeometry.Geometry.Fibration.ActualSupportRows
import DifferentialGeometry.Geometry.Collapse.SlimGraphPacket
import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.ScaledRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyQuantitative
import DifferentialGeometry.Geometry.Collapse.RiemannianConeScale
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport

/-!
# SGP02: one affine alignment of each original raw slim coordinate (actual LC87 packets)

Blueprint `master207B.tex`, SGP02 (`lem:fibration-slim-raw-alignment`, B:4410–4481), on the actual
LC87 family with cutoff formulas and curvature buffer `Q : LocalChartFamilyQ` (`X : Type`).

* `sgpRaw S j`: the original real coordinate `u_j = (split_j ·).fst` of the actual normalized
  `(1, β₁)`-splitting at the slim centre `j` (zero off the centres).
* `sgpSlimList S i`: the list `J_i` of slim centres whose CLOSED cutoff support meets
  `D_i = B(i, .95Lρ(i))`, `L = 10⁶Δ`.
* `sgpSlimList_bounds`: SGP01's (SL) on the actual list (`i ∈ J_i`, `.99 < s_j < 1.01`,
  `d(i, j) < 2Lρ(i)`), from FC18's enclosure and `slim_comparison_list_bounds`.
* `sgp02_self`: `a_i = 1`, `c_i = 0`.
* `sgp02_row` (RA): thresholds chosen FIRST (the curvature radius `Lc` asked of LPA01's buffer and
  the raw quality `η₀`), then for EVERY actual family with `β 2 = β₂`, `β 1 ≤ η₀`, `Lc ≤ Lmax` and
  `Lρ`-slow variation: every listed `j` has a sign `a_j` with
  `|s_j u_j − a_j u_i − s_j u_j(i)| < E` on `B(i, 30Lρ(i))` (reference units `ρ(i)⁻¹ d`).
  Proof: Codex X125's `exists_scaled_raw_coisometry_parameter_riemannian` (MC10/MC11 + AC79 + AC76,
  ranks one) in the reference metric `ρ(i)⁻¹ d`, `ρ(i)⁻² g`, with `c = s_j`; the exclusion is the
  rank-one stratum of the slim centre, the curvature is LPA01's buffer at radius `Lc = σ⁻¹`; the
  coisometry `ℝ¹ → ℝ¹` is a sign (`coisometry_fin_one_SGP`).
* `sgp02_reference_tests`: the original tested ball contains `B(i, 100L)`, the distortion there is
  at most `δ`, and targets of radius `< 20L` lift into `B(i, 21L)` to error `< δ`.

Not here: the zero clause (R0) (NEEDS ROW: SGP01's zero clauses and LC73's shell splitting on the
actual packets).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E1" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Kernels

/-- The isometry `ℝ ≃ ℝ¹`. -/
def realFinOneIso_SGP : ℝ ≃ₗᵢ[ℝ] E1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr

theorem realFinOneIso_SGP_apply (t : ℝ) : realFinOneIso_SGP t = t • realFinOneIso_SGP 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

/-- `ℝ × Z ≃ ℝ¹ × Z` (the same residual). -/
def realProdIso_SGP (Z : Type*) [MetricSpace Z] : WithLp 2 (ℝ × Z) ≃ᵢ WithLp 2 (E1 × Z) :=
  realFinOneIso_SGP.toIsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl Z)

theorem realProdIso_SGP_fst {Z : Type*} [MetricSpace Z] (w : WithLp 2 (ℝ × Z)) :
    (realProdIso_SGP Z w).fst = realFinOneIso_SGP w.fst :=
  rfl

theorem realProdIso_SGP_zero {Z : Type*} [MetricSpace Z] (z : Z) :
    realProdIso_SGP Z (WithLp.toLp 2 ((0 : ℝ), z)) = WithLp.toLp 2 ((0 : E1), z) := by
  change WithLp.toLp 2 (realFinOneIso_SGP 0, z) = WithLp.toLp 2 ((0 : E1), z)
  rw [map_zero]

/-- A Kleiner–Lott map for one metric is one for an equal metric, with the same map. -/
theorem exists_kleinerLott_of_metric_eq_SGP {X Y : Type*} {m₁ m₂ : MetricSpace X} [MetricSpace Y]
    (h : m₁ = m₂) {p : X} {q : Y} {δ : ℝ} (f : @KleinerLottApprox X Y m₁ _ p q δ) :
    ∃ f' : @KleinerLottApprox X Y m₂ _ p q δ,
      @KleinerLottApprox.toFun X Y m₂ _ p q δ f' = @KleinerLottApprox.toFun X Y m₁ _ p q δ f := by
  subst h
  exact ⟨f, rfl⟩

/-- A coisometry of `ℝ¹` is a sign. -/
theorem coisometry_fin_one_SGP (Λ : E1 →L[ℝ] E1)
    (hΛ : Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ E1) :
    ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ t : ℝ, Λ (realFinOneIso_SGP t) = realFinOneIso_SGP (a * t) := by
  set e := realFinOneIso_SGP with he
  set a : ℝ := e.symm (Λ (e 1)) with ha
  have hΛa : Λ (e 1) = e a := by rw [ha, LinearIsometryEquiv.apply_symm_apply]
  have hlin : ∀ t : ℝ, Λ (e t) = e (a * t) := by
    intro t
    rw [he, realFinOneIso_SGP_apply t, map_smul, ← he, hΛa, ← map_smul, smul_eq_mul, mul_comm]
  set a' : ℝ := e.symm (ContinuousLinearMap.adjoint Λ (e 1)) with ha'
  have hadj : ContinuousLinearMap.adjoint Λ (e 1) = e a' := by
    rw [ha', LinearIsometryEquiv.apply_symm_apply]
  have hinner := ContinuousLinearMap.adjoint_inner_left Λ (e 1) (e 1)
  rw [hadj, hΛa, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map] at hinner
  have haa' : a' = a := by
    simpa [RCLike.inner_apply] using hinner
  have hid := congrArg (fun T : E1 →L[ℝ] E1 => T (e 1)) hΛ
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hid
  rw [hadj, haa', hlin] at hid
  have hsq : a * a = 1 := e.injective hid
  refine ⟨a, ?_, hlin⟩
  have h2 : (a - 1) * (a + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp h2 with h | h
  · left; linarith
  · right; linarith

/-- The parameters of SGP02's application of X125 (`H = 30L`, `a = H + 1`). -/
theorem sgp02_parameters_SGP {Δ E H τ : ℝ} (hΔ : 1 ≤ Δ) (hE : 0 < E)
    (hH : H = 30 * (1000000 * Δ)) (hτ : τ = min (E / 100) (1 / (2 * (H + 1)))) :
    0 < τ ∧ τ < 1 ∧ 0 < H + 1 ∧ 20 * ((1 : ℕ) : ℝ) * τ ≤ H + 1 ∧ 2 * (H + 1) ≤ τ⁻¹ ∧
      2 * (1 + 24 * ((1 : ℕ) : ℝ)) * τ < E ∧ H < τ⁻¹ := by
  have hH' : 30000000 ≤ H := by rw [hH]; nlinarith
  have hH1 : 0 < 2 * (H + 1) := by linarith
  have hτ0 : 0 < τ := by rw [hτ]; exact lt_min (by positivity) (by positivity)
  have hτ1 : τ ≤ 1 / (2 * (H + 1)) := by rw [hτ]; exact min_le_right _ _
  have hτE : τ ≤ E / 100 := by rw [hτ]; exact min_le_left _ _
  have hτsmall : τ ≤ 1 / 60000002 := hτ1.trans
    (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hinv : 2 * (H + 1) ≤ τ⁻¹ := by
    rw [le_inv_comm₀ hH1 hτ0]
    simpa only [one_div] using hτ1
  refine ⟨hτ0, by linarith, by linarith, ?_, hinv, ?_, by linarith⟩
  · push_cast
    nlinarith
  · push_cast
    linarith

/-- SGP02's side clauses for one Kleiner–Lott `β`-map with real factor: for
`β ≤ min(1/(1000L), δ/100)` the tested ball contains `B(p, 100L)`, the distortion there is at most
`δ`, and targets of radius `< 20L` lift into `B(p, 21L)` to error `< δ`. -/
theorem kl_reference_tests_SGP {X Z : Type*} [MetricSpace X] [MetricSpace Z] {p : X} {z : Z}
    {β δ L : ℝ} (hL : 1 ≤ L) (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β)
    (hβ : β ≤ min (1 / (1000 * L)) (δ / 100)) :
    100 * L ≤ β⁻¹ ∧
      (∀ x ∈ ball p (100 * L), ∀ x' ∈ ball p (100 * L),
        |dist (f.toFun x) (f.toFun x') - dist x x'| ≤ δ) ∧
      ∀ y, dist y (f.toFun p) < 20 * L → ∃ x ∈ ball p (21 * L), dist y (f.toFun x) < δ := by
  have hb0 : 0 < β := f.error_pos
  have hb1 : β ≤ 1 / (1000 * L) := hβ.trans (min_le_left _ _)
  have hbδ : β ≤ δ / 100 := hβ.trans (min_le_right _ _)
  have hinv : 1000 * L ≤ β⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hb0]
    simpa only [one_div] using hb1
  have hbL : β * (1000 * L) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hb1
    linarith
  have hball : ∀ x ∈ ball p (100 * L), x ∈ ball p β⁻¹ := fun x hx =>
    ball_subset_ball (by linarith) hx
  refine ⟨by linarith, fun x hx x' hx' => (f.distortion x (hball x hx) x' (hball x' hx')).trans
    (by linarith), fun y hy => ?_⟩
  have hβ1 : β ≤ 1 / 1000 := by
    have := mul_le_mul_of_nonneg_left hL hb0.le
    nlinarith
  have hy' : dist y (WithLp.toLp 2 ((0 : ℝ), z)) < β⁻¹ - β := by
    rw [← f.basepoint]
    linarith
  obtain ⟨x, hxB, hxy⟩ := f.coverage_witness y hy'
  have hd := f.distortion x hxB p (mem_ball_self (inv_pos.mpr hb0))
  have htri := dist_triangle (f.toFun x) y (f.toFun p)
  rw [dist_comm (f.toFun x) y] at htri
  refine ⟨x, ?_, hxy.trans_le (by linarith)⟩
  rw [mem_ball]
  have := (abs_le.mp hd).1
  nlinarith

end Kernels

section Actual

universe u

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}

/-- The actual normalized splitting map `X → ℝ × Z_j` of a slim centre (the map of
`SlimCentre.split`, read without the rescaled source metric). -/
def sgpSplitMap {β₁ : ℝ} {j : X} (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) :
    X → WithLp 2 (ℝ × c.Z) :=
  letI := c.instZ
  @KleinerLottApprox.toFun X (WithLp 2 (ℝ × c.Z)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
    (WithLp.toLp 2 ((0 : ℝ), c.z)) β₁ c.split

open Classical in
/-- The original real coordinate `u_j` of the actual normalized splitting at the slim centre `j`
(zero off the centres). -/
def sgpRaw (S : SlimFamily X g hmetric ρ hρ β Δ σs K) (j : X) (x : X) : ℝ :=
  if hj : j ∈ S.centres then (sgpSplitMap (S.centre j hj) x).fst else 0

/-- The list `J_i`: slim centres whose closed cutoff support meets `D_i = B(i, .95Lρ(i))`. -/
def sgpSlimList (S : SlimFamily X g hmetric ρ hρ β Δ σs K) (i : X) : Set X :=
  {j | j ∈ S.centres ∧ (tsupport (S.cutoff j) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty}

theorem sgpSplitMap_center {β₁ : ℝ} {j : X} (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) :
    sgpSplitMap c j = (letI := c.instZ; WithLp.toLp 2 ((0 : ℝ), c.z)) := by
  let _ := c.instZ
  exact @KleinerLottApprox.basepoint X (WithLp 2 (ℝ × c.Z))
    (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j _ β₁ c.split

theorem sgpRaw_of_mem (S : SlimFamily X g hmetric ρ hρ β Δ σs K) {j : X} (hj : j ∈ S.centres)
    (x : X) : sgpRaw S j x = (sgpSplitMap (S.centre j hj) x).fst := by
  unfold sgpRaw
  rw [dite_eq_left hj]

theorem sgpRaw_center (S : SlimFamily X g hmetric ρ hρ β Δ σs K) (j : X) : sgpRaw S j j = 0 := by
  by_cases hj : j ∈ S.centres
  · rw [sgpRaw_of_mem S hj, sgpSplitMap_center]
    rfl
  · unfold sgpRaw
    rw [dite_eq_right hj]

/-- SGP02: `a_i = 1`, `c_i = 0`. -/
theorem sgp02_self (S : SlimFamily X g hmetric ρ hρ β Δ σs K) (i x : X) :
    ρ i / ρ i * sgpRaw S i x - 1 * sgpRaw S i x - ρ i / ρ i * sgpRaw S i i = 0 := by
  rw [div_self (hρ i).ne', sgpRaw_center]
  ring

variable {Λ σc μ b s b' s' ε γc βc : ℝ}

/-- SGP01: the reference centre is in its own list (its cutoff is one at the centre). -/
theorem sgpSlimList_mem_self
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) {i : X} (hi : i ∈ L.slim.centres) :
    i ∈ sgpSlimList L.slim i := by
  refine ⟨hi, i, ?_, mem_ball_self (by have := hρ i; positivity)⟩
  apply subset_tsupport
  have h1 : L.slim.cutoff i i = 1 := by
    unfold SlimFamily.cutoff
    rw [dite_eq_left hi]
    exact (L.slim.centre i hi).cutoff_eq_one hΔ hσs hσs1
      (mem_ball_self (by have := hρ i; positivity))
  rw [Function.mem_support, h1]
  exact one_ne_zero

/-- **SGP01 (SL) on the actual list** (supplier of SGP02): every `j ∈ J_i` is a slim centre with
`.99 < ρ(j)/ρ(i) < 1.01` and `d(i, j) < 2Lρ(i)`. -/
theorem sgpSlimList_bounds (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {i j : X}
    (hj : j ∈ sgpSlimList L.slim i) :
    j ∈ L.slim.centres ∧ 99 / 100 < ρ j / ρ i ∧ ρ j / ρ i < 101 / 100 ∧
      dist i j < 2 * (1000000 * Δ) * ρ i := by
  have hΛc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  obtain ⟨hjc, x, hx1, hx2⟩ := hj
  obtain ⟨h1, -, -, -⟩ := fc18_slim_row L hΔ hjc
  have hxj : x ∈ closedBall j (95 / 100 * (1000000 * Δ) * ρ j) := by
    refine closedBall_subset_closedBall ?_ (h1 hx1)
    have := hρ j
    nlinarith
  obtain ⟨hs1, hs2, hd⟩ := slim_comparison_list_bounds L.lipschitz_scale (hρ i) (hρ j)
    (L := 1000000 * Δ) (by positivity) (by rw [hΛc]; linarith) ⟨x, hxj, hx2⟩
  exact ⟨hjc, hs1, hs2, hd⟩

/-- **SGP02's side clauses**: for `β₁ ≤ min(1/(1000L), δ/100)` the original tested ball of the
reference splitting contains `B(i, 100L)`, its distortion there is at most `δ`, and every target of
radius `< 20L` lifts into `B(i, 21L)` to error `< δ` (reference units). -/
theorem sgp02_reference_tests (S : SlimFamily X g hmetric ρ hρ β Δ σs K) {δ : ℝ} (hΔ : 1 ≤ Δ)
    (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δ / 100)) {i : X} (hi : i ∈ S.centres) :
    letI := (S.centre i hi).instZ
    100 * (1000000 * Δ) ≤ (β 1)⁻¹ ∧
      (∀ x ∈ ball i (100 * (1000000 * Δ) * ρ i), ∀ x' ∈ ball i (100 * (1000000 * Δ) * ρ i),
        |dist (sgpSplitMap (S.centre i hi) x) (sgpSplitMap (S.centre i hi) x') -
          (ρ i)⁻¹ * dist x x'| ≤ δ) ∧
      ∀ y, dist y (sgpSplitMap (S.centre i hi) i) < 20 * (1000000 * Δ) →
        ∃ x ∈ ball i (21 * (1000000 * Δ) * ρ i), dist y (sgpSplitMap (S.centre i hi) x) < δ := by
  let _ := (S.centre i hi).instZ
  have hri := hρ i
  obtain ⟨h1, h2, h3⟩ := @kl_reference_tests_SGP X (S.centre i hi).Z
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i (S.centre i hi).z (β 1) δ (1000000 * Δ)
    (by linarith) (S.centre i hi).split hβ
  have hball : ∀ r : ℝ, ∀ x, x ∈ ball i (r * ρ i) ↔
      x ∈ @ball X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toPseudoMetricSpace i r := by
    intro r x
    change dist x i < r * ρ i ↔ (ρ i)⁻¹ * dist x i < r
    rw [inv_mul_lt_iff₀ hri, mul_comm]
  refine ⟨h1, fun x hx x' hx' => h2 x ((hball _ x).mp hx) x' ((hball _ x').mp hx'),
    fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := h3 y hy
  exact ⟨x, (hball _ x).mpr hx, hxy⟩

end Actual

section Row

/-- **SGP02 (RA) on the actual LC87 packets.** Fix `Δ ≥ 1`, the exclusion quality `β₂` and `E > 0`.
There are a curvature radius `Lc` (asked of LPA01's buffer) and a raw quality `η₀` such that for
EVERY actual family `Q` with `β 2 = β₂`, `β 1 ≤ η₀`, `Lc ≤ Lmax` and `10⁶ΔΛ < 10⁻⁵`, every slim
reference centre `i` and every listed `j ∈ J_i` have a sign `a_j` with
`|s_j u_j − a_j u_i − s_j u_j(i)| < E` on `B(i, 30Lρ(i))`, `s_j = ρ(j)/ρ(i)`. -/
theorem sgp02_row {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax : ℝ)
        (Q : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        ∀ i ∈ Q.slim.centres, ∀ j ∈ sgpSlimList Q.slim i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
          ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
            |ρ j / ρ i * sgpRaw Q.slim j x - a * sgpRaw Q.slim i x -
              ρ j / ρ i * sgpRaw Q.slim j i| < E := by
  have hΔ0 : 0 < Δ := by linarith
  set H : ℝ := 30 * (1000000 * Δ) with hH
  set τ : ℝ := min (E / 100) (1 / (2 * (H + 1))) with hτ
  obtain ⟨hτ0, hτ1, ha0, ha, ha2, hτE, hHτ⟩ := sgp02_parameters_SGP hΔ hE hH hτ
  have hkn : (1 : ℕ) ≤ Module.finrank ℝ E3 := by rw [finrank_euclideanSpace_fin]; norm_num
  obtain ⟨σ, hσ, hσ1, hprop⟩ := exists_scaled_raw_coisometry_parameter_riemannian.{0}
    (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) (j := 1) (k := 1) le_rfl le_rfl hkn hτ0 hτ1 hβ₂ hβ₂1
    ha0 ha ha2
  obtain ⟨η, hη, hprop⟩ := hprop (2 * (1000000 * Δ)) (by positivity)
  have hH1 : 0 < 1 / (2 * (H + 1)) := by positivity
  refine ⟨σ⁻¹, min η (min (σ / 3) (1 / (2 * (H + 1)))), inv_pos.mpr hσ,
    lt_min hη (lt_min (by positivity) hH1), ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax Q hβ2 hβ1 hLc hΛ hLΛ
    i hi j hj
  have hri := hρ i
  have hrj := hρ j
  obtain ⟨hjc, hs1, hs2, hd⟩ := sgpSlimList_bounds Q.toLocalChartFamily hΔ0 hΛ hLΛ hj
  have hβη : β 1 ≤ η := hβ1.trans (min_le_left _ _)
  have hβσ : 3 * β 1 ≤ σ := by
    have := hβ1.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hβH : β 1 ≤ 1 / (2 * (H + 1)) :=
    hβ1.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- physical facts, before the reference metric is introduced
  have hmR := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale g hmetric hri
  set gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g with hgR
  have hsecR : ∀ y, (ρ i)⁻¹ * dist y i < σ⁻¹ → SectionalBoundedBelowAt gR y (-σ) := by
    intro y hy
    have hy' : y ∈ ball i (σ⁻¹ * ρ i) := by
      rw [mem_ball]
      rw [inv_mul_lt_iff₀ hri] at hy
      linarith
    have hb := Q.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hLc i y hy'
    rw [hgR, sectionalBoundedBelowAt_scaleMetric_iff]
    refine hb.mono ?_
    have hσ2 : σ ^ 2 ≤ σ := by nlinarith
    have he : -((σ⁻¹ * ρ i) ^ 2)⁻¹ = -(σ ^ 2 * (ρ i)⁻¹ ^ 2) := by
      rw [mul_pow, mul_inv, inv_pow, inv_inv, ← inv_pow]
    rw [he]
    have hr2 : 0 ≤ (ρ i)⁻¹ ^ 2 := by positivity
    nlinarith
  have hstrat := (Q.slim.centres_subset hi).1
  have hrank := (scaledSplittingRank_eq_iff.mp hstrat).2.2 2 (by norm_num) (by norm_num)
  rw [hβ2] at hrank
  have hdR : (ρ i)⁻¹ * dist i j ≤ 2 * (1000000 * Δ) := by
    rw [inv_mul_le_iff₀ hri]
    linarith
  set c : ℝ := ρ j / ρ i with hcdef
  have hc : 0 < c := div_pos hrj hri
  have hcmin : (1 / 2 : ℝ) ≤ c := by linarith
  have hcmax : c ≤ 2 := by linarith
  let Si := Q.slim.centre i hi
  let Sj := Q.slim.centre j hjc
  let _ := Si.instZ
  let _ := Sj.instZ
  -- the reference splitting with target `ℝ¹ × Z_i`
  let ψ := @KleinerLottApprox.mapTargetIsometryAt X (WithLp 2 (ℝ × Si.Z)) (WithLp 2 (E1 × Si.Z))
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ i (WithLp.toLp 2 ((0 : ℝ), Si.z)) (β 1) Si.split
    (realProdIso_SGP Si.Z) (WithLp.toLp 2 ((0 : E1), Si.z)) (realProdIso_SGP_zero Si.z)
  -- the listed splitting with target `ℝ¹ × Z_j`, read in the reference metric
  let φ₀ := @KleinerLottApprox.mapTargetIsometryAt X (WithLp 2 (ℝ × Sj.Z)) (WithLp 2 (E1 × Sj.Z))
    (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ j (WithLp.toLp 2 ((0 : ℝ), Sj.z)) (β 1) Sj.split
    (realProdIso_SGP Sj.Z) (WithLp.toLp 2 ((0 : E1), Sj.z)) (realProdIso_SGP_zero Sj.z)
  have hmetq : mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj) =
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).rescale c⁻¹ (inv_pos.mpr hc) :=
    (MetricSpace.rescale_inv_ratio mX hri hrj).symm
  obtain ⟨φ, hφ⟩ := exists_kleinerLott_of_metric_eq_SGP hmetq φ₀
  have hcpt :
      @CompactSpace X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toUniformSpace.toTopologicalSpace :=
    MetricSpace.rescale_compactSpace mX _ _
  have hcomp : @CompleteSpace X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toUniformSpace :=
    (mX.rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr hri)).mpr complete_of_compact
  have hsig : @SigmaCompactSpace X
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toUniformSpace.toTopologicalSpace :=
    @CompactSpace.sigmaCompact X _ hcpt
  obtain ⟨Λ₁, hΛ₁, hal⟩ := @hprop X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ hsig hcomp gR hmR i
    (fun y hy => hsecR y hy) hrank Sj.Z Si.Z _ _ Sj.z Si.z j (β 1) (β 1) c hc hcmin hcmax hdR hβη
    hβσ φ ψ
  obtain ⟨a, ha1, hlin⟩ := coisometry_fin_one_SGP Λ₁ hΛ₁
  refine ⟨a, ha1, fun x hx => ?_⟩
  have hxR : (ρ i)⁻¹ * dist x i < H := by
    rw [inv_mul_lt_iff₀ hri]
    have : dist x i < 30 * (1000000 * Δ) * ρ i := hx
    rw [hH]
    linarith
  have hb0 : 0 < β 1 := @KleinerLottApprox.error_pos X (WithLp 2 (ℝ × Si.Z))
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ (β 1) Si.split
  have hβinv : 2 * (H + 1) ≤ (β 1)⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hb0]
    simpa only [one_div] using hβH
  -- `|u_i(x)| ≤ H + 1`
  have hui : |sgpRaw Q.slim i x| ≤ H + 1 := by
    rw [sgpRaw_of_mem Q.slim hi]
    have hdist := @KleinerLottApprox.distortion X (WithLp 2 (ℝ × Si.Z))
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ (β 1) Si.split x
      (show (ρ i)⁻¹ * dist x i < (β 1)⁻¹ by linarith) i
      (show (ρ i)⁻¹ * dist i i < (β 1)⁻¹ by rw [dist_self, mul_zero]; positivity)
    have hdii : (ρ i)⁻¹ * dist i i = 0 := by rw [dist_self, mul_zero]
    change |dist (sgpSplitMap Si x) (sgpSplitMap Si i) - (ρ i)⁻¹ * dist x i| ≤ β 1 at hdist
    rw [sgpSplitMap_center] at hdist
    have hfst := WithLp.dist_fst_le (sgpSplitMap Si x) (WithLp.toLp 2 ((0 : ℝ), Si.z))
    rw [Real.dist_eq] at hfst
    change |(sgpSplitMap Si x).fst - 0| ≤ _ at hfst
    rw [sub_zero] at hfst
    have hb1 : β 1 ≤ 1 := by
      have : 1 / (2 * (H + 1)) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      linarith
    linarith [(abs_le.mp hdist).2]
  have hxτ : (ρ i)⁻¹ * dist x i < τ⁻¹ := hxR.trans hHτ
  have hψx : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ (β 1)
      ψ x).fst = realFinOneIso_SGP (sgpRaw Q.slim i x) := by
    rw [sgpRaw_of_mem Q.slim hi]
    rfl
  have hφx : ∀ y, (@KleinerLottApprox.toFun X _
      ((mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).rescale c⁻¹ (inv_pos.mpr hc)) _ j _ (β 1) φ y).fst =
        realFinOneIso_SGP (sgpRaw Q.slim j y) := by
    intro y
    rw [hφ, sgpRaw_of_mem Q.slim hjc]
    rfl
  have hnorm : ‖(@KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ (β 1)
      ψ x).fst‖ ≤ H + 1 := by
    rw [hψx, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    exact hui
  have hmain := hal x hxτ hnorm
  rw [hψx, hφx, hφx, hlin] at hmain
  have hrw : c • realFinOneIso_SGP (sgpRaw Q.slim j x) -
      realFinOneIso_SGP (a * sgpRaw Q.slim i x) - c • realFinOneIso_SGP (sgpRaw Q.slim j i) =
      realFinOneIso_SGP (c * sgpRaw Q.slim j x - a * sgpRaw Q.slim i x -
        c * sgpRaw Q.slim j i) := by
    rw [map_sub, map_sub, ← map_smul, ← map_smul, smul_eq_mul, smul_eq_mul]
  rw [hrw, LinearIsometryEquiv.norm_map, Real.norm_eq_abs] at hmain
  exact hmain.trans_lt hτE

end Row

end DifferentialGeometry.Geometry.Collapse
