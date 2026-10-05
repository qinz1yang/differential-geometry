import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroTransport

/-!
# Consumer of the final boundary zero producer v2 (lane BZ-1, G3)

`eventually_zero_shell_coordinate_original_BZ1`: on the tail of
`eventually_zeroModelFamilyOn_certified_gBalls_boundary_BZ1`, for the family it returns, X82's
splitting at every closed-shell point `q` has, on its whole Kleiner–Lott domain
`B_{ρ(q)⁻¹ d_ĝ}(q, β₁⁻¹)`, the real coordinate `ρ(q)⁻¹ (d_g(c, x) − d_g(c, q))` of the ORIGINAL
metric of `W` (combining the shell certificate, the test-domain certificate and the
identification of `ĝ` with `g` on `B(c, 400 r_c)`), and the enlarged curvature of `g` holds on
`B_g(c, 400 r_c)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **Consumer of the final producer v2.** On its tail, for the returned family: X82's splitting
at every closed-shell point has, on its Kleiner–Lott domain, the ORIGINAL-metric coordinate
`ρ(q)⁻¹ (d_g(c, x) − d_g(c, q))`; and `sec_g ≥ -(1/60)² r_c⁻²` on `B_g(c, 400 r_c)`. -/
theorem eventually_zero_shell_coordinate_original_BZ1 :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {β : ℕ → ℝ}, 0 < β 1 → β 1 < 1 → ∀ {ζ cap : ℝ}, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ {T : ℝ}, 0 < T → 20 * Λ' ≤ T →
      ∀ {e : ℝ}, 0 < e → e < 1 / 40 →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
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
          (∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (F.zero c hc).radius →
            ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
              ∃ (z : Zf) (Fk : @KleinerLottApprox ((W n).pieceInterior ⊤)
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x ∈ @Metric.ball _ ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹
                    (inv_pos.mpr (hρ q))).toPseudoMetricSpace q (β 1)⁻¹,
                  (@KleinerLottApprox.toFun ((W n).pieceInterior ⊤)
                    (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                    ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q)))
                    inferInstance q (WithLp.toLp 2 (0, z)) (β 1) Fk x).fst = WithLp.toLp 2
                    (Function.const (Fin 1) ((ρ q)⁻¹ *
                      ((riemannianEDistOf (g n) c.val x.val).toReal -
                        (riemannianEDistOf (g n) c.val q.val).toReal)))) ∧
          ∀ c (hc : c ∈ F.centres),
            ∀ y ∈ riemannianBallOf (g n) c.val (400 * (F.zero c hc).radius),
              SectionalBoundedBelowAt (g n) y
                (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2)) := by
  obtain ⟨δStar, hδStar, h⟩ := eventually_zeroModelFamilyOn_certified_gBalls_boundary_BZ1
  refine ⟨δStar, hδStar, fun K hK A hA β hβ hβ1 ζ cap hβζ hζ1 hcap => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, -, hεrcap, hδ', hΛ', h⟩ := h K hK A hA hβ hβ1 hβζ hζ1 hcap
  refine ⟨εr, δ', Λ', hεr, hεrcap, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 Λ w hΛ hw hwc δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ hcomp heq hle
  obtain ⟨V, hTV, δ, hδ, hδδ', hev⟩ := h hT hTΛ he he1 hΛ hw hwc hδ₀ hδ₀S W g B hcoll hder ĝ
    hcomp heq hle
  refine ⟨V, hTV, δ, hδ, hδδ', ?_⟩
  filter_upwards [hev] with n hn
  let instM_BZ1 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace (ĝ n)
  intro ρ hρ hρc hρw hsmall
  obtain ⟨N, C, mN, cN, mC, o, F, -, -, -, hsplit, -, hcurv, hid, htd, -⟩ :=
    hn ρ hρ hρc hρw hsmall
  refine ⟨N, C, mN, cN, mC, o, F, fun c hc q hq1 hq2 => ?_, hcurv⟩
  obtain ⟨Zf, mZ, z, Fk, hFk⟩ := hsplit c hc q hq1 hq2
  refine ⟨Zf, mZ, z, Fk, fun x hx => ?_⟩
  have hR0 := (F.zero c hc).radius_pos
  have hsub : Metric.ball c (11 * (F.zero c hc).radius) ⊆
      Metric.ball c (400 * (F.zero c hc).radius) := ball_subset_ball (by linarith)
  have hx400 := hsub ((htd c hc q hq1 hq2).1 x hx)
  have hq400 : q ∈ Metric.ball c (400 * (F.zero c hc).radius) := by
    rw [mem_ball, dist_comm]
    linarith
  have hc400 : c ∈ Metric.ball c (400 * (F.zero c hc).radius) := mem_ball_self (by positivity)
  have hdx := (hid c hc).2 c hc400 x hx400
  have hdq := (hid c hc).2 c hc400 q hq400
  rw [hFk x, hdx, hdq, ← dist_edist, ← dist_edist]

end DifferentialGeometry.Geometry.Collapse
