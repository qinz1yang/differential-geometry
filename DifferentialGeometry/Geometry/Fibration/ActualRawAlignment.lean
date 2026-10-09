import DifferentialGeometry.Geometry.Fibration.ActualActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.ScaledRawAlignment
import DifferentialGeometry.Geometry.Collapse.RiemannianConeScale
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport

/-!
# TCP02: one raw alignment of every listed original coordinate with the reference circle chart

Blueprint `master207B.tex`, TCP02 (`lem:fibration-first-raw-alignment`, B:5311), on the final family
`LocalChartPackets`, with Codex X125's MC10/MC11 + AC79 + AC76 producer
`exists_scaled_raw_coisometry_parameter_riemannian` (accepted 81107ec40).

* `tcp02_pair_KA3` (kernel): the curvature buffer and the rank-two exclusion at the reference centre
  `p_i` (scale `r_i`) give, for an early `σ` and a later quality `η(C)`, one coisometry with (TR)
  `|s u_j − Λ u_i − s u_j(p_i)| < E₀` on `B(p_i, 1000 r_i)` for every original rank-`j` splitting at
  `p_j` (`s = r_j/r_i ∈ [1/2, 2]`, `d(p_i, p_j) ≤ C r_i`).
* The ORIGINAL raw coordinates: `circleRaw_KA3` (circle adapted packet), `slimRaw_KA3` (slim
  centre), `edgeRaw_KA3` (edge chart), each the Euclidean factor of the chart's own normalized
  splitting.
* `circle_no_three_KA3`: no normalized `(3, ν)`-splitting at a circle centre (`3ν ≤ β₃ < 1`).
* `tcp02_sectional_KA3`: the curvature buffer at a reference centre (`σ⁻¹ ≤ Lmax`).
* `tcp02_row`: TCP02's (TR) at every circle centre `i` for EVERY listed circle, slim and edge chart
  (closed support meeting `B(i, 10ρ(i))`), with `σ`, the circle bound `η₂` early and the rank-one
  bound `η₁(Δ)` later; the slim/edge real coordinate enters as `t e₀ ∈ ℝ¹`.
The zero clause (TR0) is not part of this module (it needs a radial splitting at the reference
point, see `sheet-C14-KA3.md`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section RealLine

variable (Y : Type*) [MetricSpace Y]

/-- The `ℓ²` products `ℝ × Y` and `ℝ¹ × Y` are isometric (`t ↦ t e₀`). -/
def realProdFinOneIsometry_KA3 : WithLp 2 (ℝ × Y) ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × Y) where
  toFun z := WithLp.toLp 2 (EuclideanSpace.single 0 z.fst, z.snd)
  invFun z := WithLp.toLp 2 (z.fst 0, z.snd)
  left_inv z := by simp; rfl
  right_inv z := by
    have h : EuclideanSpace.single (0 : Fin 1) (z.fst 0) = z.fst := by
      ext i
      fin_cases i
      simp
    simp [h]; rfl
  isometry_toFun := Isometry.of_dist_eq fun a b => by
    rw [WithLp.prod_dist_eq_add (by norm_num), WithLp.prod_dist_eq_add (by norm_num)]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [PiLp.dist_single_same]

theorem realProdFinOneIsometry_KA3_apply_fst (z : WithLp 2 (ℝ × Y)) :
    (realProdFinOneIsometry_KA3 Y z).fst = EuclideanSpace.single 0 z.fst := rfl

end RealLine

/-- A rank-one splitting with real factor `ℝ` is a rank-one splitting with factor `ℝ¹`, with the
SAME real coordinate (`t ↦ t e₀`). -/
theorem exists_finOne_split_KA3 {X Y : Type*} [MetricSpace Y] {m : MetricSpace X} {p : X}
    {q : Y} {δ : ℝ} (f : @KleinerLottApprox X (WithLp 2 (ℝ × Y)) m _ p (WithLp.toLp 2 (0, q)) δ) :
    ∃ f' : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Y)) m _ p
        (WithLp.toLp 2 (0, q)) δ,
      ∀ x, (@KleinerLottApprox.toFun X _ m _ _ _ _ f' x).fst =
        EuclideanSpace.single 0 (@KleinerLottApprox.toFun X _ m _ _ _ _ f x).fst := by
  have he : realProdFinOneIsometry_KA3 Y (WithLp.toLp 2 ((0 : ℝ), q)) =
      WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), q) := by
    change WithLp.toLp 2 (EuclideanSpace.single 0 (0 : ℝ), q) = _
    simp
  exact ⟨@KleinerLottApprox.mapTargetIsometryAt X _ _ m _ _ _ _ _ f (realProdFinOneIsometry_KA3 Y)
    _ he, fun x => rfl⟩

/-- A Kleiner–Lott approximation transported along an equality of source metrics keeps its map. -/
theorem exists_kla_transport_KA3 {X Y : Type*} [MetricSpace Y] {m₁ m₂ : MetricSpace X}
    (h : m₁ = m₂) {p : X} {q : Y} {δ : ℝ} (φ : @KleinerLottApprox X Y m₁ _ p q δ) :
    ∃ φ' : @KleinerLottApprox X Y m₂ _ p q δ, ∀ x,
      @KleinerLottApprox.toFun X Y m₂ _ p q δ φ' x =
        @KleinerLottApprox.toFun X Y m₁ _ p q δ φ x := by
  subst h
  exact ⟨φ, fun _ => rfl⟩

/-- **TCP02 kernel (one listed chart against the reference circle chart).** For a target error
`E₀`, an exclusion quality `ν` and ranks `1 ≤ j ≤ 2`, there is an early `σ` and, for every
displacement bound `C`, a later quality `η`: on a closed manifold, if the reference centre `p_i`
(scale `r_i`) has the curvature buffer `sec ≥ −σ/r_i²` on `B(p_i, σ⁻¹r_i)` and no normalized
`(3, ν)`-splitting, then any original rank-`j` splitting `φ` at `p_j` (own normalization `r_j`,
`1/2 ≤ r_j/r_i ≤ 2`, `d(p_i, p_j) ≤ C r_i`, quality `≤ η`) and the reference rank-two splitting `ψ`
(quality `≤ σ/3`) satisfy (TR) on `B(p_i, 1000 r_i)`: one coisometry `Λ` with
`|s u_j − Λ u_i − s u_j(p_i)| < E₀`, `s = r_j/r_i`. -/
theorem tcp02_pair_KA3 {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) {j : ℕ}
    (hj : 1 ≤ j) (hj2 : j ≤ 2) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∀ C : ℝ, 0 ≤ C → ∃ η : ℝ, 0 < η ∧
    ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
      ∀ (pi pj : X) (ri rj : ℝ) (hri : 0 < ri) (hrj : 0 < rj),
      (1 / 2 : ℝ) ≤ rj / ri → rj / ri ≤ 2 → dist pi pj ≤ C * ri →
      (∀ y, dist y pi < σ⁻¹ * ri → SectionalBoundedBelowAt g y (-(σ * (ri ^ 2)⁻¹))) →
      (¬ ∃ (W : Type) (mW : MetricSpace W), letI _w := mW
        ∃ w : W, Nonempty (@KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin (2 + 1)) × W))
          (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ pi (WithLp.toLp 2 (0, w)) ν)) →
      ∀ (A B : Type) [MetricSpace A] [MetricSpace B] (a₀ : A) (b₀ : B) {ε₁ ε₂ : ℝ},
      ε₁ ≤ η → 3 * ε₂ ≤ σ →
      ∀ (φ : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
          (mX.rescale rj⁻¹ (inv_pos.mpr hrj)) _ pj (WithLp.toLp 2 (0, a₀)) ε₁)
        (ψ : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin 2) × B))
          (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ pi (WithLp.toLp 2 (0, b₀)) ε₂),
      ∃ Λ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin j),
        Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x, dist x pi < 1000 * ri →
          ‖(rj / ri) • (@KleinerLottApprox.toFun X _ (mX.rescale rj⁻¹ (inv_pos.mpr hrj)) _ _ _ _
              φ x).fst -
            Λ (@KleinerLottApprox.toFun X _ (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ _ _ _ ψ x).fst -
            (rj / ri) • (@KleinerLottApprox.toFun X _ (mX.rescale rj⁻¹ (inv_pos.mpr hrj)) _ _ _ _
              φ pi).fst‖ < E₀ := by
  have hjpos : (0 : ℝ) < 1 + 24 * j := by positivity
  set τ : ℝ := min (1 / 4004) (E₀ / (4 * (1 + 24 * j))) with hτdef
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 / 4004 := min_le_left _ _
  have hτE : τ ≤ E₀ / (4 * (1 + 24 * j)) := min_le_right _ _
  have hjR : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
  have ha : 20 * (j : ℝ) * τ ≤ 1001 := by nlinarith
  have ha2 : 2 * (1001 : ℝ) ≤ τ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hτ]
    linarith
  have hbud : 2 * (1 + 24 * (j : ℝ)) * τ < E₀ := by
    have h := mul_le_mul_of_nonneg_left hτE (by positivity : (0 : ℝ) ≤ 2 * (1 + 24 * j))
    have h' : 2 * (1 + 24 * (j : ℝ)) * (E₀ / (4 * (1 + 24 * j))) = E₀ / 2 := by
      field_simp
      ring
    linarith
  obtain ⟨σ₀, hσ₀, hσ₀1, hprop⟩ :=
    exists_scaled_raw_coisometry_parameter_riemannian.{0} (E := E3) (H := E3)
      (I := 𝓘(ℝ, E3)) hj hj2 (by simp) hτ (by linarith) hν hν1 (by norm_num : (0 : ℝ) < 1001)
      ha ha2
  refine ⟨min σ₀ (1 / 1000), lt_min hσ₀ (by norm_num), min_le_right _ _, fun C hC => ?_⟩
  obtain ⟨η, hη, hη'⟩ := hprop C hC
  refine ⟨η, hη, ?_⟩
  intro X mX _ _ _ g hmetric pi pj ri rj hri hrj hs1 hs2 hd hsec hno A B _ _ a₀ b₀ ε₁ ε₂ hε₁
    hε₂ φ ψ
  have hσ : min σ₀ (1 / 1000) ≤ σ₀ := min_le_left _ _
  have hs : 0 < rj / ri := div_pos hrj hri
  have hmetR : ∀ a b, riemannianEDistOf (scaleMetric (ri⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g)
      a b = ENNReal.ofReal (@dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist a b) :=
    riemannianEDistOf_scaleMetric_inv_sq_eq_rescale g hmetric hri
  have hcR : @CompleteSpace X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toUniformSpace :=
    (mX.rescale_completeSpace_iff ri⁻¹ (inv_pos.mpr hri)).mpr complete_of_compact
  have hsecR : ∀ y ∈ @ball X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toPseudoMetricSpace pi σ₀⁻¹,
      SectionalBoundedBelowAt (scaleMetric (ri⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g) y
        (-σ₀) := by
    intro y hy
    have hy' : dist y pi < (min σ₀ (1 / 1000))⁻¹ * ri := by
      have h1 : @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist y pi < σ₀⁻¹ := hy
      rw [MetricSpace.rescale_dist] at h1
      have h2 : dist y pi < σ₀⁻¹ * ri := by
        rw [inv_mul_lt_iff₀ hri] at h1
        linarith
      have h3 : σ₀⁻¹ ≤ (min σ₀ (1 / 1000))⁻¹ := inv_anti₀ (lt_min hσ₀ (by norm_num)) hσ
      nlinarith
    apply (sectionalBoundedBelowAt_scaleMetric_iff (pow_pos (inv_pos.mpr hri) 2)).mpr
    refine (hsec y hy').mono ?_
    rw [inv_pow]
    have hr2 : 0 < (ri ^ 2)⁻¹ := by positivity
    nlinarith
  have hm : (mX.rescale ri⁻¹ (inv_pos.mpr hri)).rescale (rj / ri)⁻¹ (inv_pos.mpr hs) =
      mX.rescale rj⁻¹ (inv_pos.mpr hrj) :=
    MetricSpace.rescale_inv_ratio mX hri hrj
  obtain ⟨φ', hφ'⟩ := exists_kla_transport_KA3 hm.symm φ
  have hdR : @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist pi pj ≤ C := by
    rw [MetricSpace.rescale_dist, inv_mul_le_iff₀ hri]
    linarith
  obtain ⟨Λ, hΛ, hal⟩ := @hη' X (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ _ _ hcR
    (scaleMetric (ri⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g) hmetR pi hsecR hno A B _ _ a₀ b₀
    pj ε₁ ε₂ (rj / ri) hs hs1 hs2 hdR hε₁ (by linarith) φ' ψ
  refine ⟨Λ, hΛ, fun x hx => ?_⟩
  have hε₂pos := @KleinerLottApprox.error_pos X _ (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ _ _ _ ψ
  have hxR : @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist x pi < 1000 := by
    rw [MetricSpace.rescale_dist, inv_mul_lt_iff₀ hri]
    linarith
  have hxτ : x ∈ @ball X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toPseudoMetricSpace pi τ⁻¹ := by
    change @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist x pi < τ⁻¹
    linarith
  have hxψ : x ∈ @ball X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toPseudoMetricSpace pi ε₂⁻¹ := by
    change @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist x pi < ε₂⁻¹
    have h1 : (3000 : ℝ) ≤ ε₂⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hε₂pos]
      have := min_le_right σ₀ (1 / 1000)
      linarith
    linarith
  have hψx := @KleinerLottApprox.norm_euclidean_fst_le X B (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _
    pi b₀ 2 ε₂ ψ x hxψ
  have hmain := hal x hxτ (by
    have : ε₂ ≤ 1 := by have := min_le_right σ₀ (1 / 1000); linarith
    linarith)
  rw [hφ' x, hφ' pi] at hmain
  exact lt_of_le_of_lt hmain hbud

/-- A Kleiner–Lott approximation transported along an equality of base points keeps its map. -/
theorem exists_kla_basepoint_KA3 {X Y : Type*} [MetricSpace Y] {m : MetricSpace X} {p p' : X}
    (h : p = p') {q : Y} {δ : ℝ} (f : @KleinerLottApprox X Y m _ p q δ) :
    ∃ f' : @KleinerLottApprox X Y m _ p' q δ, ∀ x,
      @KleinerLottApprox.toFun X Y m _ p' q δ f' x =
        @KleinerLottApprox.toFun X Y m _ p q δ f x := by
  subst h
  exact ⟨f, fun _ => rfl⟩

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

section Raw

open Classical in
/-- TCP02's ORIGINAL raw circle coordinate `u_j`: the Euclidean factor of the circle adapted
packet's normalized `(2, β₂)`-splitting at `j` (zero off the circle centres). -/
def circleRaw_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : X) : X → ℝ² :=
  if hj : j ∈ P.circle.centres then fun x =>
    letI := (P.circleAdapted j hj).instY
    (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
      (P.circleAdapted j hj).split x).fst
  else 0

open Classical in
/-- TCP02's ORIGINAL raw slim coordinate `u_j`: the real factor of the slim centre's normalized
`(1, β₁)`-splitting at `j` (zero off the slim centres). -/
def slimRaw_KA3 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (j : X) : X → ℝ :=
  if hj : j ∈ L.slim.centres then fun x =>
    letI := (L.slim.centre j hj).instZ
    (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
      (L.slim.centre j hj).split x).fst
  else 0

open Classical in
/-- TCP02's ORIGINAL raw edge coordinate `u_j`: the real factor of the edge chart's normalized
`(1, b)`-splitting at `j` (zero off the edge centres). -/
def edgeRaw_KA3 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (j : X) : X → ℝ :=
  if hj : j ∈ L.edge.centres then
    let C := L.edge.chart j hj
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    letI := C.instY
    fun x => (C.split.toFun x).fst
  else 0

/-- The edge chart's splitting as a normalized rank-one splitting at `j` with the raw coordinate
`edgeRaw_KA3`. -/
theorem exists_edge_split_KA3
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) {j : X}
    (hj : j ∈ L.edge.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI _y := mY
      ∃ q : Y, ∃ f : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
          (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j (WithLp.toLp 2 (0, q)) b,
        ∀ x, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
          f x).fst = edgeRaw_KA3 L j x := by
  have hcen := L.edge.chart_center j hj
  unfold edgeRaw_KA3
  rw [dite_eq_left hj]
  let C := L.edge.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcen' : C.center = j := hcen
  let _ := C.instY
  obtain ⟨f, hf⟩ := exists_kla_basepoint_KA3 hcen' C.split
  exact ⟨C.Y, C.instY, C.q, f, fun x => by rw [hf x]⟩

theorem circleRaw_KA3_eq
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {j : X} (hj : j ∈ P.circle.centres) (x : X) :
    circleRaw_KA3 P j x = letI := (P.circleAdapted j hj).instY
      (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
        (P.circleAdapted j hj).split x).fst := by
  unfold circleRaw_KA3
  rw [dite_eq_left hj]

theorem slimRaw_KA3_eq (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    {j : X} (hj : j ∈ L.slim.centres) (x : X) :
    slimRaw_KA3 L j x = letI := (L.slim.centre j hj).instZ
      (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
        (L.slim.centre j hj).split x).fst := by
  unfold slimRaw_KA3
  rw [dite_eq_left hj]

end Raw

omit [CompactSpace X] in
/-- At a circle centre `i` (two-stratum), no normalized `(3, ν)`-splitting exists when
`3ν ≤ β₃ < 1` (the rank-two stratum excludes `(3, β₃)`-splittings). -/
theorem circle_no_three_KA3 (Cf : CircleFamily 𝓘(ℝ, E3) X ρ hρ β) {i : X}
    (hi : i ∈ Cf.centres) {ν : ℝ} (hν : 3 * ν ≤ β 3) (hβ3 : β 3 < 1) :
    ¬ ∃ (W : Type) (mW : MetricSpace W), letI _w := mW
      ∃ w : W, Nonempty (@KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin (2 + 1)) × W))
        (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 (0, w)) ν) := by
  rintro ⟨W, mW, w, ⟨f⟩⟩
  have hrank : scaledSplittingRank ρ hρ β i = ((2 : Fin 4) : ℕ) := Cf.centres_subset hi
  have h := (scaledSplittingRank_eq_iff.mp hrank).2.2 3 (by decide) le_rfl
  exact h ⟨W, mW, w, ⟨@KleinerLottApprox.weaken X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i)))
    _ _ _ _ _ _ f hν hβ3⟩⟩

/-- The curvature buffer of `LocalChartPackets` at a reference centre in the form of TCP02's
kernel: `sec ≥ −σ/ρ(i)²` on `B(i, σ⁻¹ρ(i))` when `σ⁻¹ ≤ Lmax`, `0 < σ ≤ 1`. -/
theorem tcp02_sectional_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hL : σ⁻¹ ≤ Lmax) (i : X) :
    ∀ y, dist y i < σ⁻¹ * ρ i → SectionalBoundedBelowAt g y (-(σ * (ρ i ^ 2)⁻¹)) := by
  intro y hy
  have h := P.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hL i y (by rw [mem_ball]; exact hy)
  refine h.mono ?_
  have hri := hρ i
  have he : ((σ⁻¹ * ρ i) ^ 2)⁻¹ = σ ^ 2 * (ρ i ^ 2)⁻¹ := by
    field_simp
  rw [he]
  have hr2 : 0 < (ρ i ^ 2)⁻¹ := by positivity
  nlinarith [mul_nonneg (mul_nonneg hσ.le hr2.le) (sub_nonneg.mpr hσ1)]

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP02_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP02_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP02_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP02** (`lem:fibration-first-raw-alignment`, B:5311) on `LocalChartPackets`: for a target
error `E₀` and the exclusion quality `ν` (`3ν ≤ β₃ < 1`), there is an early `σ` and an early circle
quality bound `η₂`, and for every `Δ ≥ 1` a later rank-one quality bound `η₁(Δ)`, such that, with
FC07's parameter ranges, `3β₂ ≤ σ`, `β₂ ≤ η₂`, `β₁, b ≤ η₁` and `σ⁻¹ ≤ Lmax`: at every circle centre
`i`, every listed circle, slim and edge chart `j` (closed support meeting `D_i = B(i, 10ρ(i))`) has
one constant coisometry `A_j : ℝ² → ℝ^{k_j}` with (TR)
`|s_j u_j − A_j u_i − s_j u_j(p_i)| < E₀` on `B(p_i, 1000ρ(i))`, `s_j = ρ(j)/ρ(i)`, for the ORIGINAL
raw coordinates `u_j` (the slim/edge real coordinate as `t e₀ ∈ ℝ¹`). -/
theorem tcp02_row {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → β 1 ≤ η₁ → b ≤ η₁ → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres,
        (∀ j ∈ P.circle.centres, (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • circleRaw_KA3 P j x - A (circleRaw_KA3 P i x) -
                (ρ j / ρ i) • circleRaw_KA3 P j i‖ < E₀) ∧
        (∀ j ∈ P.slim.centres, (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1),
            A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j x) -
                A (circleRaw_KA3 P i x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j i)‖ <
                E₀) ∧
        ∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1),
            A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j x) -
                A (circleRaw_KA3 P i x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j i)‖ <
                E₀ := by
  obtain ⟨σ₂, hσ₂, hσ₂1, h2⟩ := tcp02_pair_KA3 hE hν hν1 (j := 2) one_le_two le_rfl
  obtain ⟨σ₁, hσ₁, hσ₁1, h1⟩ := tcp02_pair_KA3 hE hν hν1 (j := 1) le_rfl one_le_two
  obtain ⟨η₂, hη₂, hk2⟩ := h2 214 (by norm_num)
  refine ⟨min σ₁ σ₂, lt_min hσ₁ hσ₂, (min_le_right _ _).trans hσ₂1, η₂, hη₂, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, hk1⟩ := h1 (10 + 2000000 * Δ) (by positivity)
  refine ⟨η₁, hη₁, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hΛ hμ hτ
    hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i hi
  have hσ₁' : min σ₁ σ₂ ≤ σ₁ := min_le_left _ _
  have hσ₂' : min σ₁ σ₂ ≤ σ₂ := min_le_right _ _
  have hL₁ : σ₁⁻¹ ≤ Lmax := (inv_anti₀ (lt_min hσ₁ hσ₂) hσ₁').trans hσL
  have hL₂ : σ₂⁻¹ ≤ Lmax := (inv_anti₀ (lt_min hσ₁ hσ₂) hσ₂').trans hσL
  have hsec₁ := tcp02_sectional_KA3 P hσ₁ (by linarith) hL₁ i
  have hsec₂ := tcp02_sectional_KA3 P hσ₂ (by linarith) hL₂ i
  have hno := circle_no_three_KA3 P.circle hi hν3 hβ3
  obtain ⟨-, hcirc, hslim, hedge, -, -⟩ := fc07_input_packet P hΛ hΔ hμ hτ hLΛ hLmax he hT i
  let Ai := P.circleAdapted i hi
  have hψ3 : 3 * β 2 ≤ σ₁ := hβ2σ.trans hσ₁'
  have hψ3' : 3 * β 2 ≤ σ₂ := hβ2σ.trans hσ₂'
  refine ⟨fun j hj hmeet => ?_, fun j hj hmeet => ?_, fun j hj hmeet => ?_⟩
  · obtain ⟨hratio, hdist, -⟩ := hcirc j hj hmeet
    let Aj := P.circleAdapted j hj
    obtain ⟨Λ', hΛ', hal⟩ := @hk2 X mX _ _ _ g hmetric i j (ρ i) (ρ j) (hρ i) (hρ j)
      hratio.1 hratio.2 (by rw [dist_comm]; linarith) hsec₂ hno Aj.Y Ai.Y Aj.instY Ai.instY
      Aj.a Ai.a (β 2) (β 2) hβ2 hψ3' Aj.split Ai.split
    refine ⟨Λ', hΛ', fun x hx => ?_⟩
    rw [circleRaw_KA3_eq P hj, circleRaw_KA3_eq P hi, circleRaw_KA3_eq P hj]
    exact hal x hx
  · obtain ⟨-, hratio, hdist, -⟩ := hslim j hj hmeet
    let Sj := P.slim.centre j hj
    let _ := Sj.instZ
    obtain ⟨f, hf⟩ := exists_finOne_split_KA3 Sj.split
    obtain ⟨Λ', hΛ', hal⟩ := @hk1 X mX _ _ _ g hmetric i j (ρ i) (ρ j) (hρ i) (hρ j)
      hratio.1 hratio.2 (by rw [dist_comm]; nlinarith [hρ i]) hsec₁ hno Sj.Z Ai.Y Sj.instZ
      Ai.instY Sj.z Ai.a (β 1) (β 2) hβ1 hψ3 f Ai.split
    refine ⟨Λ', hΛ', fun x hx => ?_⟩
    rw [circleRaw_KA3_eq P hi, slimRaw_KA3_eq P.toLocalChartFamily hj,
      slimRaw_KA3_eq P.toLocalChartFamily hj]
    have h := hal x hx
    rw [hf x, hf i] at h
    exact h
  · obtain ⟨hratio, hdist, -⟩ := hedge j hj hmeet
    obtain ⟨Y, mY, q, f, hf⟩ := exists_edge_split_KA3 P.toLocalChartFamily hj
    obtain ⟨f', hf'⟩ := exists_finOne_split_KA3 f
    obtain ⟨Λ', hΛ', hal⟩ := @hk1 X mX _ _ _ g hmetric i j (ρ i) (ρ j) (hρ i) (hρ j)
      hratio.1 hratio.2 (by rw [dist_comm]; nlinarith [hρ i]) hsec₁ hno Y Ai.Y mY Ai.instY
      q Ai.a b (β 2) hb hψ3 f' Ai.split
    refine ⟨Λ', hΛ', fun x hx => ?_⟩
    rw [circleRaw_KA3_eq P hi, ← hf x, ← hf i]
    have h := hal x hx
    rw [hf' x, hf' i] at h
    exact h

end DifferentialGeometry.Geometry.Collapse
