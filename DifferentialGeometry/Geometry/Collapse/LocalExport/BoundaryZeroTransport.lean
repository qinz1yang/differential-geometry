import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroProducerV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryTransport

/-!
# The boundary zero producer v2 with the original-metric transport (lane BZ-1, G3)

External review 51 (P0-B items A3/A5/A6, P0-C(i)). The certificates of
`eventually_zeroModelFamilyOn_certified_boundary_BZ1` live on the completion `((W n)°, d_ĝ)`.
Here they are identified with the ORIGINAL metric `g` of `W n` on the domains where they are
tested — never a global `d_g = d_ĝ` claim:

* `zero_ball_transport_BZ1`: at a point `c` with `D(c) > 5`, every radius `R ≤ V ρ(c)` with
  BCP04.a and `12800 V ≤ n`: `val '' B_ĝ(c, R) = B_g(c, R)`, `val '' B_ĝ(c, 400 R) = B_g(c, 400 R)`,
  the distances of `ĝ` on `B_ĝ(c, 400 R)` are those of `W`, and `D > 4` on `B_g(c, 400 R)`;
* `zero_curvature_transport_BZ1`: a sectional lower bound of `ĝ` on `B_ĝ(c, 400 R)` is one of `g`
  on `B_g(c, 400 R)` (`ĝ = g°` on `{D ≥ 4}`; sectional bounds are local);
* `zero_test_domains_BZ1` (metric): the Kleiner–Lott domain `B_{ρ(q)⁻¹ d}(q, β₁⁻¹)` of the shell
  splitting and the outer adapted test ball `B_{λ r⁻¹ d}(q, ζ⁻¹)` (`λ ≥ Λ'`) lie in `B(c, 11 r)`
  once `β₁⁻¹, ζ⁻¹ ≤ Λ' ≤ T/20` and LC62 holds;
* **final producer** `eventually_zeroModelFamilyOn_certified_gBalls_boundary_BZ1`: the
  replacement of `eventually_zeroModelFamilyOn_gBalls_boundary_BDRY3` (T2's zero step) with the
  requested cap and, for the SAME family, the zero balls as `g`-balls (T2 (iv)), LC62, the enlarged
  curvature of `ĝ` AND of `g`, X82, LC73, the identification of `ĝ` with `g` on `B(c, 400 r_c)`,
  the test domains inside `B(c, 11 r_c)`, and LC62 for points of `W` within `d_g`-distance
  `10 r_c`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Hyperbolic
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **The test domains of a zero shell (metric).** For a closed-shell point `q` (`d(c,q) ≤ 10 R`)
with LC62 `T/20 ≤ R/ρ(q)` and `β₁⁻¹, ζ⁻¹ ≤ Λ' ≤ T/20`: the Kleiner–Lott domain
`B_{ρ(q)⁻¹ d}(q, β₁⁻¹)` and, for every `λ ≥ Λ'`, the outer adapted test ball
`B_{λ R⁻¹ d}(q, ζ⁻¹)` lie in `B(c, 11 R)`. -/
theorem zero_test_domains_BZ1 {X : Type*} (m : MetricSpace X) {c q : X} {R ρq b ζ T Λ' : ℝ}
    (hR : 0 < R) (hρq : 0 < ρq) (hq : @dist X m.toDist c q ≤ 10 * R) (hloc : T / 20 ≤ R / ρq)
    (hΛT : 20 * Λ' ≤ T)
    (hbΛ : b⁻¹ ≤ Λ') (hζΛ : ζ⁻¹ ≤ Λ') :
    (∀ x ∈ @ball X (m.rescale ρq⁻¹ (inv_pos.mpr hρq)).toPseudoMetricSpace q b⁻¹,
      x ∈ @ball X m.toPseudoMetricSpace c (11 * R)) ∧
    ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
      ∀ x ∈ @ball X ((m.rescale R⁻¹ (inv_pos.mpr hR)).rescale lam hlam).toPseudoMetricSpace q
        ζ⁻¹, x ∈ @ball X m.toPseudoMetricSpace c (11 * R) := by
  have hT' : Λ' ≤ R / ρq := by linarith
  have hqx : ∀ x : X, @dist X m.toDist x q < R → @dist X m.toDist x c < 11 * R := by
    intro x hx
    have ht := @dist_triangle X m.toPseudoMetricSpace x q c
    rw [@dist_comm X m.toPseudoMetricSpace q c] at ht
    linarith
  refine ⟨fun x hx => ?_, fun lam hlam hlamΛ x hx => ?_⟩
  · change ρq⁻¹ * @dist X m.toDist x q < b⁻¹ at hx
    refine hqx x ?_
    have h1 : @dist X m.toDist x q < b⁻¹ * ρq := by
      rw [inv_mul_lt_iff₀ hρq] at hx
      linarith
    have h2 : b⁻¹ * ρq ≤ R := by
      have := (le_div_iff₀ hρq).mp (hbΛ.trans hT')
      linarith
    linarith
  · change lam * (R⁻¹ * @dist X m.toDist x q) < ζ⁻¹ at hx
    refine hqx x ?_
    have hζ1 : ζ⁻¹ ≤ lam := hζΛ.trans hlamΛ
    have h1 : lam * (R⁻¹ * @dist X m.toDist x q) < lam := hx.trans_le hζ1
    have h2 : R⁻¹ * @dist X m.toDist x q < 1 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    rw [inv_mul_lt_iff₀ hR] at h2
    linarith

section Transport

variable (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
  (g : SmoothRiemannianMetric W.model W.Carrier)
  (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

/-- **Zero balls in the original metric.** With `ĝ = g°` on `{D ≥ 4}`, BCP04.a and
`12800 V ≤ n`: at `c ∈ W°` with `D(c) > 5` and every `0 < R ≤ V ρ(c)`, the balls `B_ĝ(c, R)` and
`B_ĝ(c, 400 R)` are the `g`-balls of `W`, the distances of `ĝ` on `B_ĝ(c, 400 R)` are those of `W`,
and `D > 4` on `B_g(c, 400 R)`. -/
theorem zero_ball_transport_BZ1
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n V : ℝ} (hV : 0 ≤ V)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (hn : 12800 * V ≤ n) (c : W.pieceInterior ⊤)
    (hc : ENNReal.ofReal 5 < distanceToBoundary W g c) {R : ℝ} (hR : 0 < R)
    (hRV : R ≤ V * ρ c) :
    letI := inducedMetricSpace ĝ
    Subtype.val '' Metric.ball c R = riemannianBallOf g c.val R ∧
      Subtype.val '' Metric.ball c (400 * R) = riemannianBallOf g c.val (400 * R) ∧
      (∀ y ∈ Metric.ball c (400 * R), ∀ z ∈ Metric.ball c (400 * R),
        riemannianEDistOf g y.val z.val = edist y z) ∧
      ∀ y ∈ riemannianBallOf g c.val (400 * R), ENNReal.ofReal 4 < distanceToBoundary W g y := by
  let _ := inducedMetricSpace ĝ
  have hb := ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp (C := 1600 * V / 3)
    (by positivity) (by linarith) c hc
  have hbig : 1600 * R ≤ 3 * (1600 * V / 3) * ρ c := by
    have he : 3 * (1600 * V / 3) * ρ c = 1600 * (V * ρ c) := by ring
    rw [he]
    linarith
  have hq : ∀ r : ℝ, r ≤ 1600 * R → ENNReal.ofReal (r + 4) ≤ distanceToBoundary W g c :=
    fun r hr => le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hb.le
  refine ⟨?_, ?_, fun y hy z hz => ?_, ?_⟩
  · rw [inducedMetricSpace_ball ĝ c R]
    exact image_val_riemannianBallOf_cut_BDRY1 W g ĝ (by norm_num) heq c hR.le
      (hq R (by linarith))
  · rw [inducedMetricSpace_ball ĝ c (400 * R)]
    exact image_val_riemannianBallOf_cut_BDRY1 W g ĝ (by norm_num) heq c (by positivity)
      (hq (400 * R) (by linarith))
  · rw [inducedMetricSpace_ball ĝ c _] at hy hz
    have h4 : 400 * R = 1600 * R / 4 := by ring
    rw [h4] at hy hz
    rw [inducedMetricSpace_edist ĝ y z]
    exact (riemannianEDistOf_cut_eq_BDRY1 W g ĝ (by norm_num) heq c (by positivity)
      (hq (1600 * R) le_rfl) hy hz).symm
  · exact riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g (by positivity)
      (by norm_num) (hq (400 * R) (by linarith))

/-- **Enlarged zero curvature in the original metric.** If `ĝ = g°` on `{D ≥ 4}`,
`400 R + 4 ≤ D(c)` and `sec_ĝ ≥ κ` on `B_ĝ(c, 400 R)`, then `sec_g ≥ κ` on `B_g(c, 400 R)`. -/
theorem zero_curvature_transport_BZ1
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    {c : W.pieceInterior ⊤} {R κ : ℝ} (hR : 0 ≤ R)
    (hq : ENNReal.ofReal (400 * R + 4) ≤ distanceToBoundary W g c)
    (hsec : ∀ y ∈ @Metric.ball _ (inducedMetricSpace ĝ).toPseudoMetricSpace c (400 * R),
      SectionalBoundedBelowAt ĝ y κ) :
    ∀ y ∈ riemannianBallOf g c.val (400 * R), SectionalBoundedBelowAt g y κ := by
  intro y hy
  have hD := riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g (by positivity)
    (by norm_num) hq hy
  rw [← image_val_riemannianBallOf_cut_BDRY1 W g ĝ (by norm_num) heq c (by positivity) hq] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have hy'' : y' ∈ @Metric.ball _ (inducedMetricSpace ĝ).toPseudoMetricSpace c (400 * R) := by
    rw [inducedMetricSpace_ball ĝ c _]
    exact hy'
  exact ((completion_cut_local_data_BDRY1 W g ĝ (a := 4) (by norm_num) heq one_pos).1 y' hD
    κ).1.mp (hsec y' hy'')

end Transport

/-- **The boundary zero producer v2 (final; T2's zero step with the requested cap).** The
statement of `eventually_zeroModelFamilyOn_gBalls_boundary_BDRY3` with the cap
(`∀ ζ cap … ∃ εr δ' Λ', εr < min (1/4) cap …`, chosen before the joint witness and `V`),
returning on one tail, for every admissible scale, ONE regional zero family `F` on
`((W n)°, d_ĝ)` with, for THAT family:
(gB) the zero balls are actual `g`-balls (T2 (iv));
(A3) LC62 `d(c, q) ≤ 10 r_c ⟹ T/20 ≤ r_c/ρ(q)`;
(A6) `sec_ĝ ≥ -(1/60)² r_c⁻²` on `B_ĝ(c, 400 r_c)`;
(A5) X82's exact-coordinate splitting on the closed shells and LC73's ζ-adapted tests of the stored
radial functions for every `λ ≥ Λ'`;
(A6') `sec_g ≥ -(1/60)² r_c⁻²` on the ORIGINAL ball `B_g(c, 400 r_c)`;
(I) `val '' B_ĝ(c, 400 r_c) = B_g(c, 400 r_c)` with the distances of `W` on `B_ĝ(c, 400 r_c)`;
(TD) the shell splitting's Kleiner–Lott domain and the outer adapted test ball lie in
`B(c, 11 r_c)`;
(A3') LC62 for every point `q` of `W` with `d_g(c, q) ≤ 10 r_c`. -/
theorem eventually_zeroModelFamilyOn_certified_gBalls_boundary_BZ1 :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {β : ℕ → ℝ}, 0 < β 1 → β 1 < 1 → ∀ {ζ cap : ℝ}, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ {T : ℝ}, 0 < T → 20 * Λ' ≤ T →
      ∀ {e : ℝ}, 0 < e → e < 1 / 40 →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤))
        (hcomp : ∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)),
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
        (∀ n (x : (W n).pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ (ĝ n).inner x v v) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        (∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
          ρ (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
        ∃ (N C : (W n).pieceInterior ⊤ → Type) (_ : ∀ a, MetricSpace (N a))
          (_ : ∀ a, ChartedSpace E3 (N a)) (_ : ∀ a, MetricSpace (C a)) (o : ∀ a, C a),
          ∃ F : ZeroModelFamilyOn I3 ((W n).pieceInterior ⊤) (ĝ n) (fun x => ρ x)
            (fun x => hρ x) β N C o δ εr e T V
            {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x},
          -- (gB) the zero balls are actual `g`-balls of `W`
          (∀ z (hz : z ∈ F.centres),
            Subtype.val '' Metric.ball z (F.zero z hz).radius =
              riemannianBallOf (g n) z.val (F.zero z hz).radius) ∧
          -- (A3) LC62 on the selected balls
          (∀ c (hc : c ∈ F.centres), ∀ q, dist c q ≤ 10 * (F.zero c hc).radius →
            T / 20 ≤ (F.zero c hc).radius / ρ q) ∧
          -- (A6) the enlarged zero curvature of the completion
          (∀ c (hc : c ∈ F.centres), ∀ y ∈ ball c (400 * (F.zero c hc).radius),
            SectionalBoundedBelowAt (ĝ n) y (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2))) ∧
          -- (A5) X82 on the closed shell, exact distance coordinate
          (∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (F.zero c hc).radius →
            ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
              ∃ (z : Zf) (Fk : @KleinerLottApprox ((W n).pieceInterior ⊤)
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x : (W n).pieceInterior ⊤, (@KleinerLottApprox.toFun ((W n).pieceInterior ⊤)
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                  ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1) Fk x).fst = WithLp.toLp 2
                  (Function.const (Fin 1) ((ρ q)⁻¹ * (dist c x - dist c q)))) ∧
          -- (A5) LC73, ζ-adapted tests of the stored radial function, every ratio `λ ≥ Λ'`
          (∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (F.zero c hc).radius →
            ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
            let R := (F.zero c hc).radius
            let hR : 0 < R := (F.zero c hc).radius_pos
            let η := (F.zero c hc).radial
            let mr := (inducedMetricSpace (ĝ n)).rescale R⁻¹ (inv_pos.mpr hR)
            let gr := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (ĝ n)
            let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale
              (m := inducedMetricSpace (ĝ n)) (ĝ n) (inducedMetricSpace_hmetric (ĝ n)) hR
            let := mr.rescale lam hlam
            letI := (mr.rescale_completeSpace_iff lam hlam).mpr
              (((inducedMetricSpace (ĝ n)).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr
                (riemannianMetricComplete_iff_inducedMetricSpace.mp (hcomp n)))
            letI := radialScaledBundle gr lam hlam
            letI := radialScaledContinuous gr lam hlam
            letI := radialScaledManifold (m := mr) gr hmr lam hlam
            let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
            let ψ := fun x => lam * (η x - η q)
            ∃ hEnorm : IsMetricNorm h,
              ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
                ∃ (z : Zf) (κ : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
                (∀ x, (κ.toFun x).fst = lam *
                  (@dist ((W n).pieceInterior ⊤) mr.toDist c x -
                    @dist ((W n).pieceInterior ⊤) mr.toDist c q)) ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
                (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
                (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
                (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
                ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
                  ∀ u : TangentSpace I3 x, h.inner x u u = 1 →
                  intrinsicGeodesic h hEnorm x u (dist x y) = y →
                  |mvfderiv (I := I3) ψ x u -
                    ((κ.toFun y).fst - (κ.toFun x).fst) / dist x y| < ζ) ∧
          -- (A6') the enlarged zero curvature of the ORIGINAL metric
          (∀ c (hc : c ∈ F.centres),
            ∀ y ∈ riemannianBallOf (g n) c.val (400 * (F.zero c hc).radius),
            SectionalBoundedBelowAt (g n) y (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2))) ∧
          -- (I) `ĝ` is `g` on the enlarged zero balls
          (∀ c (hc : c ∈ F.centres),
            Subtype.val '' Metric.ball c (400 * (F.zero c hc).radius) =
              riemannianBallOf (g n) c.val (400 * (F.zero c hc).radius) ∧
            ∀ y ∈ Metric.ball c (400 * (F.zero c hc).radius),
              ∀ z ∈ Metric.ball c (400 * (F.zero c hc).radius),
                riemannianEDistOf (g n) y.val z.val = edist y z) ∧
          -- (TD) the test domains of the shell certificates lie in `B(c, 11 r_c)`
          (∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (F.zero c hc).radius →
            (∀ x ∈ @Metric.ball _ ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹
                (inv_pos.mpr (hρ q))).toPseudoMetricSpace q (β 1)⁻¹,
              x ∈ Metric.ball c (11 * (F.zero c hc).radius)) ∧
            ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
              ∀ x ∈ @Metric.ball _ (((inducedMetricSpace (ĝ n)).rescale
                  ((F.zero c hc).radius)⁻¹ (inv_pos.mpr (F.zero c hc).radius_pos)).rescale lam
                  hlam).toPseudoMetricSpace q ζ⁻¹,
                x ∈ Metric.ball c (11 * (F.zero c hc).radius)) ∧
          -- (A3') LC62 for the points of `W` within `d_g`-distance `10 r_c`
          ∀ c (hc : c ∈ F.centres), ∀ q : (W n).Carrier,
            riemannianEDistOf (g n) c.val q ≤ ENNReal.ofReal (10 * (F.zero c hc).radius) →
            T / 20 ≤ (F.zero c hc).radius / ρ q := by
  obtain ⟨δ1, hδ1, hprod⟩ := eventually_zeroModelFamilyOn_certified_boundary_BZ1
  obtain ⟨δ2, hδ2, hpair⟩ := bsa06_pair_BDRY2.{0}
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro K hK A hA β hβ hβ1 ζ cap hβζ hζone hcap
  obtain ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ', hζΛ, hβΛ, h⟩ :=
    hprod K hK A hA hβ hβ1 hβζ hζone hcap
  refine ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 Λ w hΛ hw hwc δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ hcomp heq hle
  obtain ⟨V, hTV, δ, hδ0, hδδ', hev⟩ := h hT hTΛ he he1 hΛ hw hwc hδ₀
    (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder ĝ hcomp heq hle
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  have hV0 : 0 ≤ V := by linarith
  have hw'0 : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by positivity
  have hw'c : w / (2 * (1 + 2 * Λ⁻¹) ^ 3) < euclideanThreeUnitBallVolume := by
    have h1 : 1 ≤ 1 + 2 * Λ⁻¹ := by have := inv_pos.mpr hΛ; linarith
    have h2 : 1 ≤ 2 * (1 + 2 * Λ⁻¹) ^ 3 := by nlinarith [one_le_pow₀ (n := 3) h1]
    calc w / (2 * (1 + 2 * Λ⁻¹) ^ 3) ≤ w := div_le_self hw.le h2
      _ < euclideanThreeUnitBallVolume := hwc
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hev, hnR.eventually_ge_atTop 3,
    hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹,
    hnR.eventually_ge_atTop (12800 * V)] with n hn hn3 hnw hn8
  let instM_BZ1 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace (ĝ n)
  intro ρ hρ hρc hρw hsmall
  obtain ⟨N, C, mN, cN, mC, o, F, hloc, hbuf, hsplit, hadapt⟩ := hn ρ hρ hρc hρw hsmall
  have h1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hbcp : ∀ p : (W n).Carrier, 0 < distanceToBoundary (W n) (g n) p →
      n * (distanceToBoundary (W n) (g n) p).toReal /
          ((distanceToBoundary (W n) (g n) p).toReal + 3) <
        (distanceToBoundary (W n) (g n) p).toReal / ρ p := fun p hp =>
    (hpair (W n) (g n) K _ (by omega) (boundaryCounterexampleRatio_pos hδ₀ h1).le
      ((boundaryCounterexampleRatio_le δ₀ n).trans (hδ₀S.trans (min_le_right _ _))) (B n)
      (hcoll n) (hder n) hA hn3 (boundaryCounterexampleRatio_mul_le δ₀ h1)
      ((inv_le_comm₀ hn0 hw'0).mpr hnw) hw'c p (hρ p) (hρw p).le).2.2.2 hp
  have h510 : ENNReal.ofReal 5 < ENNReal.ofReal 10 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have htr : ∀ c (hc : c ∈ F.centres), _ := fun c hc =>
    zero_ball_transport_BZ1 (W n) (g n) (ĝ n) (heq n) ρ hρ hV0 hbcp hn8 c
      (h510.trans (F.centres_subset hc)) (F.zero c hc).radius_pos (F.radius_mem c hc).2
  have hq400 : ∀ c (hc : c ∈ F.centres), ENNReal.ofReal (400 * (F.zero c hc).radius + 4) ≤
      distanceToBoundary (W n) (g n) c := by
    intro c hc
    have hb := ofReal_buffer_lt_distanceToBoundary_BDRY1 (W n) (g n) ρ hρ hbcp
      (C := 1600 * V / 3) (by positivity) (by linarith) c.val (h510.trans (F.centres_subset hc))
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hb.le
    have hR := (F.radius_mem c hc).2
    have hR0 := (F.zero c hc).radius_pos
    have he : 3 * (1600 * V / 3) * ρ c = 1600 * (V * ρ c) := by ring
    rw [he]
    linarith
  refine ⟨N, C, mN, cN, mC, o, F, fun z hz => (htr z hz).1, hloc, hbuf, hsplit, hadapt,
    fun c hc => zero_curvature_transport_BZ1 (W n) (g n) (ĝ n) (heq n)
      (F.zero c hc).radius_pos.le (hq400 c hc) (hbuf c hc),
    fun c hc => ⟨(htr c hc).2.1, (htr c hc).2.2.1⟩, fun c hc q hq1 hq2 => ?_, ?_⟩
  · exact zero_test_domains_BZ1 (inducedMetricSpace (ĝ n)) (F.zero c hc).radius_pos (hρ q) hq2
      (hloc c hc q hq2) hTΛ hβΛ hζΛ
  · intro c hc q hq
    have hR0 := (F.zero c hc).radius_pos
    have hqb : q ∈ riemannianBallOf (g n) c.val (400 * (F.zero c hc).radius) := by
      change riemannianEDistOf (g n) c.val q < ENNReal.ofReal (400 * (F.zero c hc).radius)
      exact lt_of_le_of_lt hq ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
    rw [← (htr c hc).2.1] at hqb
    obtain ⟨q', hq', rfl⟩ := hqb
    have hcc : c ∈ Metric.ball c (400 * (F.zero c hc).radius) := mem_ball_self (by positivity)
    have hd := (htr c hc).2.2.1 c hcc q' hq'
    rw [hd] at hq
    have hdist : dist c q' ≤ 10 * (F.zero c hc).radius := by
      rw [edist_dist] at hq
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hq
    exact hloc c hc q' hdist

end DifferentialGeometry.Geometry.Collapse
