import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightBinding
import DifferentialGeometry.Geometry.Fibration.ActualEdgeRawAlignment

/-!
# BCG02, value clause at an edge reference, on the LC88 boundary data (lane BCG-1, G3)

Blueprint 207B, BCG02 (`B:8822–8889`), edge references: EGP01 supplies the absence of a
`(2, β₂)`-splitting at the strong-edge centre; AC76 and FC20 with ranks one and one give a SIGN
`a_b` and the raw comparison on the radius-`20Δ` domain; the edge chart value error `μΔ` (μ after Δ)
gives `|U_b − a_b(η_a − η_a(p_a))| < θ` on `D_a = B(p_a, 20ΔR_a)`.

* `exists_sign_raw_alignment_real_complete_BCG1`: EGP03's real-factor kernel
  (`exists_sign_raw_alignment_real_KC`) on a complete σ-compact carrier (same proof);
* `EdgeFamilyOn.coord_BCG1` (the edge chart coordinate `η_j` as a function on the carrier, packet
  projection) and `EdgeFamilyOn.exists_split_BCG1` (the chart's normalized `b`-splitting at `j`, with
  `η_j(j) = 0` and the value error `|η_j − u_j| < μΔ` on `B(j, 100Δρ(j))`);
* `bcg02_edge_value_of_split_BCG1` (abstract step on `LocalPacketsOn`, any rank-one KL at `j`);
* `bcg02_edge_value_BCG1` (on the LC88 data, per carrier, as `bcg02_circle_value_BCG1`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
  DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E1" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **EGP03's real-factor kernel on a complete σ-compact carrier** (`exists_sign_raw_alignment_real_KC`
with `[CompleteSpace M] [SigmaCompactSpace M]` in place of `[CompactSpace M]`; same proof). -/
theorem exists_sign_raw_alignment_real_complete_BCG1 {τ ν H : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hν : 0 < ν)
    (hν1 : ν < 1) (ha : 20 * τ ≤ H + 1) (ha2 : 2 * (H + 1) ≤ τ⁻¹) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∀ C : ℝ, 0 ≤ C → ∃ η : ℝ, 0 < η ∧
      ∀ (M : Type) [m : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [CompleteSpace M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M),
        (∀ x y, riemannianEDistOf g x y = ENNReal.ofReal (dist x y)) →
        ∀ (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (i j : M),
        (∀ y ∈ ball i (σ⁻¹ * ρ i), SectionalBoundedBelowAt g y (-((σ⁻¹ * ρ i) ^ 2)⁻¹)) →
        ¬ @HasEuclideanSplitting.{0, 0} M (m.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) i 2 ν →
        1 / 2 ≤ ρ j / ρ i → ρ j / ρ i ≤ 2 → dist i j ≤ C * ρ i →
        ∀ (A B : Type) [MetricSpace A] [MetricSpace B] (a : A) (b : B) {ε₁ ε₂ : ℝ},
        ε₁ ≤ η → 3 * ε₂ ≤ σ → ε₂ * (2 * (H + 1)) ≤ 1 →
        ∀ (φ : @KleinerLottApprox M (WithLp 2 (ℝ × A)) (m.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)))
            _ j (WithLp.toLp 2 ((0 : ℝ), a)) ε₁)
          (ψ : @KleinerLottApprox M (WithLp 2 (ℝ × B)) (m.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i)))
            _ i (WithLp.toLp 2 ((0 : ℝ), b)) ε₂),
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ x ∈ ball i (H * ρ i),
          |ρ j / ρ i * (@KleinerLottApprox.toFun M _ (m.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j _
              ε₁ φ x).fst -
            s * (@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i _
              ε₂ ψ x).fst -
            ρ j / ρ i * (@KleinerLottApprox.toFun M _ (m.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j _
              ε₁ φ i).fst| ≤ 50 * τ := by
  have hkn : (1 : ℕ) ≤ Module.finrank ℝ E3 := by rw [finrank_euclideanSpace_fin]; norm_num
  obtain ⟨σ, hσ, hσ1, hprop⟩ := exists_scaled_raw_coisometry_parameter_riemannian.{0}
    (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) (j := 1) (k := 1) le_rfl le_rfl hkn hτ hτ1 hν hν1
    (by linarith : (0 : ℝ) < H + 1) (by push_cast; linarith) ha2
  refine ⟨σ, hσ, hσ1, fun C hC => ?_⟩
  obtain ⟨η, hη, hprop⟩ := hprop C hC
  refine ⟨η, hη, ?_⟩
  intro M m _ _ hMc hMs g hmetric ρ hρ i j hsec hno hc1 hc2 hd A B _ _ a b ε₁ ε₂ hε₁ hε₂ hε₂H φ ψ
  have hri := hρ i
  have hrj := hρ j
  set c : ℝ := ρ j / ρ i with hcdef
  have hc : 0 < c := div_pos hrj hri
  -- physical facts, before the reference metric is introduced
  have hdR : (ρ i)⁻¹ * dist i j ≤ C := by
    rw [inv_mul_le_iff₀ hri]
    linarith
  have hmR := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale g hmetric hri
  set gR : SmoothRiemannianMetric 𝓘(ℝ, E3) M :=
    scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g with hgR
  have hsecR : ∀ y, (ρ i)⁻¹ * dist y i < σ⁻¹ → SectionalBoundedBelowAt gR y (-σ) := by
    intro y hy
    have hy' : y ∈ ball i (σ⁻¹ * ρ i) := by
      rw [mem_ball]
      rw [inv_mul_lt_iff₀ hri] at hy
      linarith
    have hb := hsec y hy'
    rw [hgR, sectionalBoundedBelowAt_scaleMetric_iff]
    refine hb.mono ?_
    have hσ2 : σ ^ 2 ≤ σ := by nlinarith
    have he : -((σ⁻¹ * ρ i) ^ 2)⁻¹ = -(σ ^ 2 * (ρ i)⁻¹ ^ 2) := by
      rw [mul_pow, mul_inv, inv_pow, inv_inv, ← inv_pow]
    rw [he]
    have hr2 : 0 ≤ (ρ i)⁻¹ ^ 2 := by positivity
    nlinarith
  -- the reference splitting with target `ℝ¹ × B`
  let ψ' := @KleinerLottApprox.mapTargetIsometryAt M (WithLp 2 (ℝ × B)) (WithLp 2 (E1 × B))
    (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ i (WithLp.toLp 2 ((0 : ℝ), b)) ε₂ ψ
    (realProdIso_SGP B) (WithLp.toLp 2 ((0 : E1), b)) (realProdIso_SGP_zero b)
  -- the other splitting with target `ℝ¹ × A`, read in the reference metric
  let φ₀ := @KleinerLottApprox.mapTargetIsometryAt M (WithLp 2 (ℝ × A)) (WithLp 2 (E1 × A))
    (m.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ j (WithLp.toLp 2 ((0 : ℝ), a)) ε₁ φ
    (realProdIso_SGP A) (WithLp.toLp 2 ((0 : E1), a)) (realProdIso_SGP_zero a)
  have hmetq : m.rescale (ρ j)⁻¹ (inv_pos.mpr hrj) =
      (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).rescale c⁻¹ (inv_pos.mpr hc) :=
    (MetricSpace.rescale_inv_ratio m hri hrj).symm
  obtain ⟨φ', hφ'⟩ := exists_kleinerLott_of_metric_eq_SGP hmetq φ₀
  have hcomp : @CompleteSpace M (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toUniformSpace :=
    (m.rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr hri)).mpr hMc
  have hsig : @SigmaCompactSpace M
      (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toUniformSpace.toTopologicalSpace := hMs
  obtain ⟨Λ₁, hΛ₁, hal⟩ := @hprop M (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ hsig hcomp gR hmR i
    (fun y hy => hsecR y hy) hno A B _ _ a b j ε₁ ε₂ c hc hc1 hc2 hdR hε₁ hε₂ φ' ψ'
  obtain ⟨s, hs, hlin⟩ := coisometry_fin_one_SGP Λ₁ hΛ₁
  refine ⟨s, hs, fun x hx => ?_⟩
  have hxR : (ρ i)⁻¹ * dist x i < H := by
    rw [inv_mul_lt_iff₀ hri]
    have : dist x i < H * ρ i := hx
    linarith
  have hb0 : 0 < ε₂ := @KleinerLottApprox.error_pos M (WithLp 2 (ℝ × B))
    (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ
  have hb1 : ε₂ < 1 := @KleinerLottApprox.error_lt_one M (WithLp 2 (ℝ × B))
    (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ
  have hεinv : 2 * (H + 1) ≤ ε₂⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hb0, inv_eq_one_div, le_div_iff₀ (by linarith)]
    linarith
  -- `|u_i(x)| ≤ H + 1`
  have hui : |(@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ x).fst| ≤ H + 1 := by
    have hdist := @KleinerLottApprox.radial_error M (WithLp 2 (ℝ × B))
      (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ x
      (show (ρ i)⁻¹ * dist x i < ε₂⁻¹ by linarith)
    change |dist (@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ x) (WithLp.toLp 2 ((0 : ℝ), b)) - (ρ i)⁻¹ * dist x i| ≤ ε₂ at hdist
    have hfst := WithLp.dist_fst_le (@KleinerLottApprox.toFun M _
      (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ x) (WithLp.toLp 2 ((0 : ℝ), b))
    rw [Real.dist_eq] at hfst
    change |(@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ x).fst - 0| ≤ _ at hfst
    rw [sub_zero] at hfst
    linarith [(abs_le.mp hdist).2]
  have hxτ : (ρ i)⁻¹ * dist x i < τ⁻¹ := by linarith
  have hψx : (@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ' x).fst = realFinOneIso_SGP (@KleinerLottApprox.toFun M _
        (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ x).fst := rfl
  have hφx : ∀ y, (@KleinerLottApprox.toFun M _
      ((m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).rescale c⁻¹ (inv_pos.mpr hc)) _ j _ ε₁ φ' y).fst =
        realFinOneIso_SGP (@KleinerLottApprox.toFun M _ (m.rescale (ρ j)⁻¹ (inv_pos.mpr hrj))
          _ j _ ε₁ φ y).fst := by
    intro y
    rw [hφ']
    rfl
  have hnorm : ‖(@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ' x).fst‖ ≤ H + 1 := by
    rw [hψx, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    exact hui
  have hmain := hal x hxτ hnorm
  rw [hψx, hφx, hφx, hlin] at hmain
  rw [← map_smul, ← map_smul, ← map_sub, ← map_sub, LinearIsometryEquiv.norm_map,
    Real.norm_eq_abs, smul_eq_mul, smul_eq_mul] at hmain
  have h50 : 2 * (1 + 24 * ((1 : ℕ) : ℝ)) * τ = 50 * τ := by push_cast; ring
  rw [h50] at hmain
  exact hmain


section EdgeCoord

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ} {U₁ U₂ : Set X}

/-- The edge chart coordinate `η_j` of a regional edge centre, as a function on the carrier. -/
def EdgeFamilyOn.coord_BCG1 (E : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂)
    (j : X) (hj : j ∈ E.centres) : X → ℝ :=
  let C := E.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  C.coord

/-- **The edge chart's normalized splitting at its centre**, with `η_j(j) = 0` and the value error
`|η_j − u_j| < μΔ` on `B(j, 100Δρ(j))`. -/
theorem EdgeFamilyOn.exists_split_BCG1
    (E : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X}
    (hj : j ∈ E.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI _y := mY
      ∃ q : Y, ∃ f : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
          (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j (WithLp.toLp 2 (0, q)) b,
        E.coord_BCG1 j hj j = 0 ∧
        ∀ x, dist x j < 100 * Δ * ρ j →
          |E.coord_BCG1 j hj x - (@KleinerLottApprox.toFun X _
            (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _ f x).fst| < μ * Δ := by
  have hcen := E.chart_center j hj
  have hρj := hρ j
  let C := E.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
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
  refine ⟨C.Y, C.instY, C.q, f, ?_, fun x hx => ?_⟩
  · change C.coord j = 0
    have h0 := C.coord_center
    rw [hcen'] at h0
    exact h0
  · rw [hf x]
    change |C.coord x - (C.split.toFun x).fst| < μ * Δ
    refine C.value x ?_
    rw [hcen']
    change @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toDist x j < 100 * Δ
    rw [MetricSpace.rescale_dist, inv_mul_lt_iff₀ hρj]
    linarith

end EdgeCoord

/-- **BCG02's value clause at an edge reference, abstract step.** For `θ > 0`, an exclusion quality
`ν < 10⁻⁶` and `Δ ≥ 1`: an early `σ` (strong quality `3b ≤ σ`) and a rank-one quality bound `η`; at every
strong-edge centre `j`, every rank-one Kleiner–Lott `ε₁`-approximation `φ` of `(X, ρ(j)⁻¹ d, j)` into
`ℝ ×₂ T` (`ε₁ ≤ η`) gives one sign `a` with `|u(y) − a(η_j(y) − η_j(j))| < θ` on `B(j, 20Δρ(j))`,
`u = (φ ·).fst`, `η_j` the edge chart coordinate (`μΔ ≤ θ/4`). -/
theorem bcg02_edge_value_of_split_BCG1 {θ ν Δ : ℝ} (hθ : 0 < θ) (hν : 0 < ν)
    (hν1 : ν < 1 / 1000000) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ} {U₁ U₂ : Set X}
      (F : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        U₁ U₂),
      σ⁻¹ ≤ Lmax → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 → b < 1 / 1000000 →
      s < 1 / 1000000 → μ * Δ ≤ θ / 4 →
      ∀ (j : X) (hj : j ∈ F.edge.centres) (Tm : Type) [MetricSpace Tm] (t₀ : Tm) {ε₁ : ℝ},
      ε₁ ≤ η →
      ∀ φ : @KleinerLottApprox X (WithLp 2 (ℝ × Tm)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
          (WithLp.toLp 2 (0, t₀)) ε₁,
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ y, dist y j < 20 * Δ * ρ j →
        |(@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _ φ y).fst -
          a * (F.edge.coord_BCG1 j hj y - F.edge.coord_BCG1 j hj j)| < θ := by
  set H : ℝ := 20 * Δ with hH
  have hH0 : 0 < H := by rw [hH]; linarith
  set τ' : ℝ := min (θ / 200) (1 / (2 * (H + 1))) with hτdef
  have hτ : 0 < τ' := lt_min (by positivity) (by positivity)
  have hτθ : τ' ≤ θ / 200 := min_le_left _ _
  have hτH : τ' ≤ 1 / (2 * (H + 1)) := min_le_right _ _
  have hτ1 : τ' < 1 := by
    have : 1 / (2 * (H + 1)) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have ha : 20 * τ' ≤ H + 1 := by linarith
  have ha2 : 2 * (H + 1) ≤ τ'⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hτ]
    rwa [one_div] at hτH
  obtain ⟨σ, hσ, hσ1, hk⟩ := exists_sign_raw_alignment_real_complete_BCG1 hτ hτ1 hν
    (by linarith) ha ha2
  obtain ⟨η, hη, hk⟩ := hk 0 le_rfl
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X mX _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁ U₂ F
    hσL h3b hbH hb6 hs6 hμ j hj Tm _ t₀ ε₁ hε₁ φ
  have hρj := hρ j
  have hjU : j ∈ U₁ := F.edge.centres_subset hj
  obtain ⟨Y, mY, q, f, hc0, hval⟩ := F.edge.exists_split_BCG1 hj
  have hsec := F.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hσL j hjU
  have hno : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) j 2 ν :=
    @not_hasEuclideanSplitting_two_of_isEdgePoint.{0, 0, 0} X
      (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) j Δ b s ν (F.edge.strong j hj) hb6 hs6 hν1
  have hr1 : ρ j / ρ j = 1 := div_self hρj.ne'
  obtain ⟨a, ha, hlin⟩ := hk X g hmetric ρ hρ j j hsec hno (by rw [hr1]; norm_num)
    (by rw [hr1]; norm_num) (by rw [dist_self, zero_mul]) Tm Y t₀ q hε₁ h3b hbH φ f
  refine ⟨a, ha, fun y hy => ?_⟩
  have hφj : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      φ j).fst = 0 := by
    rw [@KleinerLottApprox.basepoint X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ]
    rfl
  have hmain := hlin y (by rw [mem_ball]; exact hy)
  rw [hr1, hφj, one_mul, mul_zero, sub_zero] at hmain
  have hv := hval y (by nlinarith)
  have ha1 : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  rw [hc0, sub_zero]
  set u := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ y).fst
  set fy := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ f y).fst
  set cy := F.edge.coord_BCG1 j hj y
  have h2 : |a * (fy - cy)| < μ * Δ := by
    rw [abs_mul, ha1, one_mul, abs_sub_comm]
    exact hv
  have hsplit : u - a * cy = (u - a * fy) + a * (fy - cy) := by ring
  calc |u - a * cy| = |(u - a * fy) + a * (fy - cy)| := by rw [hsplit]
    _ ≤ |u - a * fy| + |a * (fy - cy)| := abs_add_le _ _
    _ < 50 * τ' + μ * Δ := by linarith
    _ ≤ θ := by linarith

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **BCG02's value clause at an edge reference on the LC88 boundary data.** If the `b`th closed
boundary support meets `D_a = B_g(j, 20Δρ(j))` at a strong-edge centre `j`: one sign `a_b` with
`|U_b − a_b(η_a − η_a(j))| < θ` on `B(j, 20Δρ(j))`, `U_b = (η_b − η_b(j))/ρ(j)`. -/
theorem bcg02_edge_value_BCG1 {θ ν Δ : ℝ} (hθ : 0 < θ) (hν : 0 < ν) (hν1 : ν < 1 / 1000000)
    (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
      (P : BoundaryCollarPacket W g K A w₀ εB) (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p)
      {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {Kf : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n : ℝ}
      (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)),
      1 ≤ K → 0 ≤ Λ →
      (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) →
      (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
      (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
        ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
      (∀ p, 0 < distanceToBoundary W g p →
        n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p) →
      32 * η⁻¹ ≤ n → 0 < β 1 → 2 * β 1 ≤ η → w₀ ≤ β 1 ^ 2 / 1000 → εB ≤ β 1 ^ 2 / 1000 →
      20 * Δ * Λ ≤ 1 / 2 → 22 * Δ * β 1 ^ 3 < 1 → σ⁻¹ ≤ Lmax → 3 * b ≤ σ →
      b * (2 * (20 * Δ + 1)) ≤ 1 → b < 1 / 1000000 → s < 1 / 1000000 → μ * Δ ≤ θ / 4 →
      letI := inducedMetricSpace ĝ
      ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ : Set (W.pieceInterior ⊤)),
      (∀ x ∈ U₁, ENNReal.ofReal 5 < distanceToBoundary W g x) →
      ∀ (F : LocalPacketsOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁ U₂)
        (j : W.pieceInterior ⊤) (hj : j ∈ F.edge.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb),
          riemannianEDistOf g j.val x < ENNReal.ofReal (20 * Δ * ρ j)) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        ∀ y : W.pieceInterior ⊤, dist y j < 20 * Δ * ρ j →
          |(P.height bb y - P.height bb j) / ρ j -
            a * (F.edge.coord_BCG1 j hj y - F.edge.coord_BCG1 j hj j)| < θ := by
  obtain ⟨σ, hσ, hσ1, η₀, hη₀, habs⟩ := bcg02_edge_value_of_split_BCG1 hθ hν hν1 hΔ
  refine ⟨σ, hσ, hσ1, min η₀ (1 / 2), lt_min hη₀ (by norm_num), min_le_right _ _, ?_⟩
  intro W _ g K A w₀ εB P ρ hρ Λ β σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n ĝ hK hΛ
    hlip hcol heq hbcp hn hβ1 hβη hwβ hεβ hΛ20 hβΔ hσL h3b hbH hb6 hs6 hμ hcN U₁ U₂ hU₁ F j hj bb
    hmeet
  let instM_BCG1 : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  set η : ℝ := min η₀ (1 / 2) with hηdef
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hη2 : η ≤ 1 / 2 := min_le_right _ _
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hρj : 0 < ρ j := hρ j
  have hβ14 : β 1 ≤ 1 / 4 := by linarith
  have hβ3pos : 0 < β 1 ^ 3 := pow_pos hβ1 3
  have hεB4 : εB ≤ 1 / 4 := by nlinarith
  -- BCG01.b: the reference centre is a band point of the `bb`th collar, `ρ(j) < 2 r_∂`
  have hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) < β 1 ^ 3 / 1000 := fun i q hq => by
    have := hcol i q hq
    linarith
  obtain ⟨hρ2, hband⟩ := P.bcg01_reference_domain hεB4 hρ hΛ hlip hsmall (L := 22 * Δ)
    (C := 20 * Δ) (by linarith) (by linarith) (by linarith only [hΛ20] : Λ * (20 * Δ) ≤ 1 / 2)
    (by linarith only [hβΔ] : β 1 ^ 3 / 1000 * (1000 * (22 * Δ)) < 1) hmeet
  have hjD : riemannianEDistOf g j.val j.val < ENNReal.ofReal (20 * Δ * ρ j) := by
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨q₀, -, hq₀j, hz19, hz91, hη19, hη91⟩ := hband j.val hjD
  -- BCP02 at `p_a = j` with coordinate EXACTLY `U_b`
  have hρη : ρ j ≤ η ^ 3 / 2000 := by
    have h8 : (2 * β 1) ^ 3 ≤ η ^ 3 := pow_le_pow_left₀ (by positivity) hβη 3
    nlinarith
  have hwη : w₀ ≤ η ^ 2 / 1000 := by
    have h4 : (2 * β 1) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hβη 2
    nlinarith
  have hεη : εB ≤ η ^ 2 / 1000 := by
    have h4 : (2 * β 1) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hβη 2
    nlinarith
  have hε1000 : εB ≤ 1 / 1000 := by nlinarith
  have hηj5 : 5 ≤ P.height bb ((P.cusp.collar bb).toFun q₀) := by rw [hq₀j]; linarith
  have hηj95 : P.height bb ((P.cusp.collar bb).toFun q₀) ≤ 95 := by rw [hq₀j]; linarith
  have hKL := P.exists_kleinerLott_height_BCG1 hK hε1000 bb q₀ hρj hη (by linarith) hwη hεη hρη
    (by linarith) (by linarith) hηj5 hηj95
  let mT : MetricSpace Torus := (inducedMetricSpace (P.cusp.collar bb).cusp.torusMetric).rescale
    ((ρ j)⁻¹ * Real.exp (-(q₀.2.val 0) / 2)) (mul_pos (inv_pos.mpr hρj) (Real.exp_pos _))
  obtain ⟨t₀, f, hf⟩ := hKL
  -- transport to `(W°, R_a⁻¹ d_ĝ)` on the consumer ball
  have hj5 : ENNReal.ofReal 5 < distanceToBoundary W g j := hU₁ j (F.edge.centres_subset hj)
  have hη0 : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
  obtain ⟨-, hdistC⟩ := consumer_domain_completion_BDRY5 W g ĝ heq ρ hρ hη0 hbcp hn j hj5
  obtain ⟨himgC, -⟩ := consumer_domain_completion_BDRY5 W g ĝ heq ρ hρ (C := η⁻¹ / 4)
    (by positivity) hbcp (by linarith) j hj5
  have h4 : 4 * (η⁻¹ / 4) * ρ j = η⁻¹ * ρ j := by ring
  rw [h4] at himgC
  have hballN : @ball (W.pieceInterior ⊤)
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹ =
      @ball (W.pieceInterior ⊤) (inducedMetricSpace ĝ).toPseudoMetricSpace j (η⁻¹ * ρ j) := by
    rw [← MetricSpace.rescale_ball (inducedMetricSpace ĝ) (ρ j)⁻¹ (inv_pos.mpr hρj) j
      (η⁻¹ * ρ j)]
    congr 1
    field_simp
  have hballW : @ball W.Carrier
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j.val η⁻¹ =
      riemannianBallOf g j.val (η⁻¹ * ρ j) := by
    rw [← inducedMetricSpace_ball g j.val (η⁻¹ * ρ j),
      ← MetricSpace.rescale_ball (inducedMetricSpace g) (ρ j)⁻¹ (inv_pos.mpr hρj) j.val
      (η⁻¹ * ρ j)]
    congr 1
    field_simp
  have hiso : ∀ x ∈ @ball (W.pieceInterior ⊤)
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹,
      ∀ y ∈ @ball (W.pieceInterior ⊤)
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹,
      @dist W.Carrier ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist
          x.val y.val =
        @dist (W.pieceInterior ⊤)
          ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist x y := by
    intro x hx y hy
    rw [hballN] at hx hy
    have he := hdistC x hx y hy
    rw [MetricSpace.rescale_dist, MetricSpace.rescale_dist]
    congr 1
    change (riemannianEDistOf g x.val y.val).toReal =
      @dist (W.pieceInterior ⊤) (inducedMetricSpace ĝ).toDist x y
    rw [he]
    rfl
  have himg : @ball W.Carrier
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j.val η⁻¹ ⊆
      Subtype.val '' @ball (W.pieceInterior ⊤)
        ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹ := by
    rw [hballW, hballN, ← himgC]
  have himg' : @ball W.Carrier
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace
        ((P.cusp.collar bb).toFun q₀) η⁻¹ ⊆
      Subtype.val '' @ball (W.pieceInterior ⊤)
        ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹ := by
    rw [hq₀j]
    exact himg
  let φ := @KleinerLottApprox.transportBall_BCG1 (W.pieceInterior ⊤) W.Carrier
    (WithLp 2 (ℝ × Torus)) ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj))
    ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ η f Subtype.val j
    hq₀j.symm hiso himg'
  obtain ⟨Ab, hAb, hval⟩ := @habs (W.pieceInterior ⊤) (inducedMetricSpace ĝ) _ _ hcN _ ĝ
    (inducedMetricSpace_hmetric ĝ) (fun x => ρ x) (fun x => hρ x) Λ β σs Kf σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V U₁ U₂ F hσL h3b hbH hb6 hs6 hμ j hj Torus mT t₀ η hηη₀ φ
  refine ⟨Ab, hAb, fun y hy => ?_⟩
  have hfy : (@KleinerLottApprox.toFun (W.pieceInterior ⊤) _
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ y).fst =
      (P.height bb y - P.height bb j) / ρ j := by
    change (@KleinerLottApprox.toFun W.Carrier _
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ f y.val).fst = _
    rw [hf, hq₀j]
  have h := hval y hy
  rw [hfy] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
