import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroTransportIdx
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroSublevelTypesBFZD

/-!
# The final boundary zero producer keeping the sublevel types (lane BFAM-ZD)

`eventually_zeroModelFamilyOn_certified_gBalls_boundary_types_BFZD` is the index-corrected final
boundary zero producer `eventually_zeroModelFamilyOn_certified_gBalls_boundary_BZ1_IDX2` (same
prefix, same tail, same transport lemmas, same ONE family `F`) on the producer v2 that keeps the
carrier witness (`eventually_zeroModelFamilyOn_certified_boundary_types_BFZD`): the conclusion
carries, first, the types of the actual sublevels `{η_c ≤ t}`, `t ∈ [1/5, 2]`, of the stored radial
functions of `F` (review 53 §4.1), for every orientation of the completed interior; the balls of
`F` are the original `g`-balls with the distances of `W` on `B(c, 400 r_c)` (clauses (gB), (I)), so
these are statements about the SAME subsets of the original carrier.
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

/-- **The final boundary zero producer keeping the sublevel types** (lane BFAM-ZD): the statement
of `eventually_zeroModelFamilyOn_certified_gBalls_boundary_BZ1_IDX2` whose ONE family `F` carries,
first, the types of the actual sublevels of its stored radial functions (every orientation `oM` of
the completed interior, every `t ∈ [1/5, 2]`). -/
theorem eventually_zeroModelFamilyOn_certified_gBalls_boundary_types_BFZD :
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
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
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
          -- (A-Z) the types of the actual sublevels of the SAME radial functions
          (∀ oM : ManifoldOrientation I3 ((W n).pieceInterior ⊤) 3, ∀ c (hc : c ∈ F.centres),
            ∀ t ∈ Icc (1 / 5 : ℝ) 2,
              CompactModelSublevel oM (N (F.zero c hc).model) {x | (F.zero c hc).radial x ≤ t} ∨
              PointSoulCoreSublevel (N (F.zero c hc).model) {x | (F.zero c hc).radial x ≤ t} ∨
              CircleSoulCoreSublevel (N (F.zero c hc).model) {x | (F.zero c hc).radial x ≤ t} ∨
              ProjectiveSoulCoreSublevel (N (F.zero c hc).model)
                {x | (F.zero c hc).radial x ≤ t} ∨
              KleinSoulCoreSublevel (N (F.zero c hc).model) {x | (F.zero c hc).radial x ≤ t}) ∧
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
  obtain ⟨δ1, hδ1, hprod⟩ := eventually_zeroModelFamilyOn_certified_boundary_types_BFZD
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
  obtain ⟨N, C, mN, cN, mC, o, F, htypes, hloc, hbuf, hsplit, hadapt⟩ := hn ρ hρ hρc hρw hsmall
  have hn0 : (0 : ℝ) < n := by linarith
  have hbcp : ∀ p : (W n).Carrier, 0 < distanceToBoundary (W n) (g n) p →
      n * (distanceToBoundary (W n) (g n) p).toReal /
          ((distanceToBoundary (W n) (g n) p).toReal + 3) <
        (distanceToBoundary (W n) (g n) p).toReal / ρ p := fun p hp =>
    (hpair (W n) (g n) K _ (by omega)
      (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)).le
      ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans (hδ₀S.trans (min_le_right _ _)))
      (B n) (hcoll n) (hder n) hA hn3 (boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n)
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
  refine ⟨N, C, mN, cN, mC, o, F, htypes, fun z hz => (htr z hz).1, hloc, hbuf, hsplit, hadapt,
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
