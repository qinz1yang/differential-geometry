import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCoarseKernels
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeFullCollarFamilyQF

/-!
# LFR44 and the LC84 edge charts with LFR27's clauses of the shared smoothing (QF re-chain)

LC87's `exists_strong_edge_full_collar_cover_Q` and `exists_edgeCharts_of_strong_edge_family_Q`
(`EdgeCoarseKernels.lean`, frozen) re-chained over `exists_edge_full_collar_family_QF`: same binders,
same parameter order, same proofs; the per-centre conclusions also carry LC87's clauses L1–L5 of the
ONE shared smoothing `F` at normalized scale (`F_p = F/ρ(p)`, `ρ_p = ρ/ρ(p)`):

* `exists_strong_edge_full_collar_cover_QF`;
* `exists_edgeCharts_of_strong_edge_family_QF`: at every strong edge centre `p`,
  `∃ c : EdgeChart gR hnR Δ σ μ b γ β A ρ_p F_p, c.center = p ∧ (Qn clauses) ∧ L1 ∧ … ∧ L5` in the
  same normalized let-block (the input of `exists_edgeDiskPacket_threshold`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

universe u w uE uH uM

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **LFR44 with the coarse-border composite and LFR27's clauses (QF).** `exists_strong_edge_full_collar_cover_Q`
(LC87, same binders and proof) with LC87's clauses L1–L5 of the shared smoothing at every centre. -/
theorem exists_strong_edge_full_collar_cover_QF {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ → 1 ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b s b' s' : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ → b < 1 / 100 → 100 * Δ < b⁻¹ →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
        (Λ : ℝ) < 1 / (1000000 * Δ) → (Λ : ℝ) < s' / (100000000 * Δ ^ 2) →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 →
        s < b' / 100000 → s < s' / 100000 → b < s / 100000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [hM : CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (ρ : M → ℝ) (hρpos : ∀ x, 0 < ρ x) (J : Finset M),
      J.Nonempty →
      (∀ p ∈ J, @isEdgePoint.{uM, w} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p Δ b s) →
      (∀ p ∈ J, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2)) →
      (∀ p ∈ J, ∀ z ∈ ball p (b⁻¹ * ρ p), SectionalBoundedBelowAt g z (-(b / ρ p) ^ 2)) →
      LipschitzWith Λ ρ → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      let A : Set M := closure
        {x | @isEdgePoint.{uM, w} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
      ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        ∀ p ∈ J, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
        letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
          radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsRiemannianManifold I M :=
          radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : CompleteSpace M :=
          (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
        let gR : SmoothRiemannianMetric I M :=
          scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
        (∀ x, |F x / ρ p - infDist x A| < μ * Δ) ∧
        (∃ OF : Set M, IsOpen OF ∧
          closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} ⊆ OF ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => F x / ρ p) OF) ∧
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
          ∀ u ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo gR A y,
            Real.sqrt (gR.inner y (gradFun gR (fun x => F x / ρ p) y + u)
              (gradFun gR (fun x => F x / ρ p) y + u)) < ε) ∧
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
          Real.sqrt (gR.inner y
            (gradFun gR (fun z => F z / ρ p / (ρ z / ρ p)) y - gradFun gR (fun x => F x / ρ p) y)
            (gradFun gR (fun z => F z / ρ p / (ρ z / ρ p)) y - gradFun gR (fun x => F x / ρ p) y))
            ≤ 100 * Δ * Λ) ∧
        ∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
          ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ (fun x => F x / ρ p) (fun x => ρ x / ρ p)) x) ∧
        ∃ (Y : Type w) (mY : MetricSpace Y), letI := mY
          ∃ (q : Y) (Fp : @KleinerLottApprox M (WithLp 2 (ℝ × Y))
              (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), q)) b)
            (Qn : M → WithLp 2 (ℝ × ℝ)),
          (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            ∀ z, (Qn z).fst = (Fp.toFun z).fst) ∧
          (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p));
            (Qn p = 0 ∧
            (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
              (|dist (Qn x) (Qn y) - dist x y| ≤ τ * Δ)) ∧
            (∀ x ∈ ball p (200 * Δ), 0 ≤ (Qn x).snd) ∧
            (∀ z : WithLp 2 (ℝ × ℝ), (|z.fst| ≤ 100 * Δ) → z.snd ∈ Icc 0 (100 * Δ) →
              ∃ x ∈ ball p (200 * Δ), dist (Qn x) z ≤ τ * Δ) ∧
            (∀ a ∈ A ∩ ball p (190 * Δ), (Qn a).snd ≤ τ * Δ) ∧
            (∀ t : ℝ, (|t| ≤ 100 * Δ) → ∃ a ∈ A ∩ ball p (190 * Δ),
              dist (Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ))) ∧
          (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
          letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
            radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : IsRiemannianManifold I M :=
            radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : CompleteSpace M :=
            (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
          let gR : SmoothRiemannianMetric I M :=
            scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
          have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
          ∀ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
          LipschitzWith (Real.toNNReal (1 + σ)) f →
          (∀ x ∈ ball p (100 * Δ), |f x - (Fp.toFun x).fst| ≤ μ * Δ) →
          (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
            ∀ w : TangentSpace I x, gR.inner x w w = 1 →
            intrinsicGeodesic gR hnR x w (dist x x') = x' →
            |mvfderiv (I := I) f x w - ((Fp.toFun x').fst - (Fp.toFun x).fst) / dist x x'| < σ) →
          (ball p (3 * Δ) ⊆ edgeDiskDomain p Δ (fun x => f x.val)
              (fun x => F x / ρ p) (fun x => ρ x / ρ p) ∧
            EqOn ((Subtype.val : ball p (100 * Δ) → M).extend
              (fun x => edgeCoordinateProfile (f x.val / Δ) *
                edgeHeightProfile (F x.val / ρ p / (Δ * (ρ x.val / ρ p)))) 0) 1
              (ball p (3 * Δ))) ∧
          ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
            Δ / 10 ≤ F x / ρ p / (ρ x / ρ p) → F x / ρ p / (ρ x / ρ p) ≤ 10 * Δ →
          ∃ hq : 99 / 100 ≤ ρ x / ρ p ∧ ρ x / ρ p ≤ 101 / 100,
            (letI := (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).rescale (ρ x / ρ p)⁻¹
              (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq.1));
              ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
                ∀ y, Φ.toFun y = @planeComparisonMap M
                  (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) Qn p x Δ (ρ x / ρ p) y) ∧
            let J := edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)]
            ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x (300 * (ρ x / ρ p))) ∧
            (∀ y ∈ ball x (100 * (ρ x / ρ p)), Function.Surjective (mvfderiv (I := I) J y)) ∧
            (∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p)),
              ‖J y - J z‖ ≤ (1 + γ) * (dist y z / (ρ x / ρ p))) ∧
            (∀ y ∈ ball x (100 * (ρ x / ρ p)), infDist (J y) (ball (J x) 100) < 100 * γ) ∧
            (∀ v ∈ ball (J x) 100, ∃ y ∈ ball x (100 * (ρ x / ρ p)), ‖J y - v‖ < 100 * γ) ∧
            ∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p) / γ),
              ρ x / ρ p < dist y z →
              ∀ W : TangentSpace I y, gR.inner y W W = 1 →
              intrinsicGeodesic gR hnR y W (dist y z) = z →
              ‖(ρ x / ρ p) • mvfderiv (I := I) J y W - (dist y z / (ρ x / ρ p))⁻¹ •
                (planeReferenceIsometry (planeComparisonMap Qn p x Δ (ρ x / ρ p) z) -
                  planeReferenceIsometry (planeComparisonMap Qn p x Δ (ρ x / ρ p) y))‖ < γ) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hfam⟩ := exists_edge_full_collar_family_QF.{uE, uH, uM, w}
    hβ hβγ hγ hγ1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ hΔ1 => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔfam⟩ := hfam Δ hΔ
  refine ⟨min τ₀ (1 / 20000), lt_min hτ₀ (by norm_num), κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b s b' s' Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb hbb₀ hb100 hsource
    hlam hbudget hscale hend hb'domain hs'domain hb'error hs'error hsb' hss' hbs
    E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm ρ hρpos J hJ hJE hsec hsecb hρ hρs A
  have hτsmall : τ < 1 / 10000 :=
    (hττ₀.trans (min_le_right _ _)).trans_lt (by norm_num)
  have hQex : ∀ p ∈ J, ∃ Q : M → WithLp 2 (ℝ × ℝ), Q p = 0 ∧
      (∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
        |dist (Q x) (Q y) - dist x y| ≤ τ * (Δ * ρ p)) ∧
      (∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q x).snd) ∧
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
        z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
          ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q x) z ≤ τ * (Δ * ρ p)) ∧
      p ∈ A ∧ (∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q a).snd ≤ τ * (Δ * ρ p)) ∧
      (∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) → ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
          dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p)) ∧
      ∃ (Y : Type w) (mY : MetricSpace Y), letI := mY
        ∃ (q : Y) (Fp : @KleinerLottApprox M (WithLp 2 (ℝ × Y))
            (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), q)) b),
          letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          ∀ z, (Q z).fst = ρ p * (Fp.toFun z).fst := fun p hp =>
    exists_physical_coarse_border_chart_with_splitting (X := M) hρ hρpos hΔ1 hτ hτsmall hscale
      hend hb'domain hs'domain hb'error hs'error hsb' hss' hbs p (hJE p hp)
  choose! Q hQ using hQex
  obtain ⟨F, hF0, hFL, hcent⟩ := hΔfam σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ
    (hττ₀.trans (min_le_left _ _)) hθ hκ hκκ₀ hb hbb₀ hlam hbudget E H I M g hEnorm A J Q ρ
    hρpos hJ isClosed_closure (fun p hp => (hQ p hp).1) (fun p hp => (hQ p hp).2.1)
    (fun p hp => (hQ p hp).2.2.1) (fun p hp => (hQ p hp).2.2.2.1)
    (fun p hp => (hQ p hp).2.2.2.2.1) (fun p hp => (hQ p hp).2.2.2.2.2.1)
    (fun p hp => (hQ p hp).2.2.2.2.2.2.1) hsec hρ hρs
  refine ⟨F, hF0, hFL, fun p hp => ⟨(hcent p hp).1, (hcent p hp).2.1, ?_⟩⟩
  have hr : 0 < ρ p := hρpos p
  obtain ⟨Y, mY, q, Fp, hrel⟩ := (hQ p hp).2.2.2.2.2.2.2
  refine ⟨Y, mY, q, Fp, fun z => (ρ p)⁻¹ • Q p z, fun z => ?_,
    normalized_coarse_border_LC87 (Q p) hr (hQ p hp).1 (hQ p hp).2.1 (hQ p hp).2.2.1
      (hQ p hp).2.2.2.1 (hQ p hp).2.2.2.2.2.1 (hQ p hp).2.2.2.2.2.2.1, ?_⟩
  · change (ρ p)⁻¹ * (Q p z).fst = _
    rw [hrel z, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hsecbR := radialScaled_sectional_bound g (r := b⁻¹) hr (hsecb p hp)
  have hvalR := radialScaled_value_clause (A := A) hr (hcent p hp).1
  have hscale' : Δ * (Λ : ℝ) ≤ 1 / 1000000 := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 1000000 * Δ)).mp hscale
    nlinarith
  have hρ' := lipschitzWith_normalized_scale hρ hr
  have hpA : p ∈ A := (hQ p hp).2.2.2.2.1
  intro hmetric gR hnR f hfs hfL hfval htest
  refine ⟨?_, fun x hx hfx hη hη' => ?_⟩
  · let _ := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
    exact ball_subset_edgeDiskDomain_and_cutoff_one Fp hΔ1 hb100 hμ1 hsource
      (fun x => ρ x / ρ p) (fun x => F x / ρ p) hρ' (fun x => div_pos (hρpos x) hr)
      (div_self hr.ne') hscale' A hpA (fun x _ => hvalR x) (fun x => f x.val)
      (fun x => hfval x.val x.property)
  · have hQα : letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
        ∀ z ∈ ball p (200 * Δ), (Q p z).fst = ρ p * (Fp.toFun z).fst := fun z _ => hrel z
    exact (hcent p hp).2.2 Y q Fp hsecbR hQα f hfs hfL hfval htest x hx hfx hη hη'


/-- **LC84 items 1–3 with the coarse-border composite and LFR27's clauses (QF).**
`exists_edgeCharts_of_strong_edge_family_Q` (LC87, same binders and proof) whose per-centre conclusion
also carries LC87's clauses L1–L5 of the shared smoothing at normalized scale. -/
theorem exists_edgeCharts_of_strong_edge_family_QF {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ → 1 ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ s b' s' : ℝ), 0 < σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 →
        s < b' / 100000 → s < s' / 100000 →
      ∃ b₁ : ℝ, 0 < b₁ ∧ ∀ (Λ : ℝ≥0), 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
        (Λ : ℝ) < 1 / (1000000 * Δ) → (Λ : ℝ) < s' / (100000000 * Δ ^ 2) → ∀ b : ℝ, 0 < b → b < b₀ → b < b₁ → b < 1 / 100 → 100 * Δ < b⁻¹ →
        b < s / 100000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [hM : CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (ρ : M → ℝ) (hρpos : ∀ x, 0 < ρ x) (J : Finset M),
      J.Nonempty →
      (∀ p ∈ J, @isEdgePoint.{uM, 0} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p Δ b s) →
      (∀ p ∈ J, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2)) →
      (∀ p ∈ J, ∀ z ∈ ball p (b⁻¹ * ρ p), SectionalBoundedBelowAt g z (-(b / ρ p) ^ 2)) →
      LipschitzWith Λ ρ → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      let A : Set M := closure
        {x | @isEdgePoint.{uM, 0} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
      ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        ∀ p ∈ J, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
          (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
          letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
            radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : IsRiemannianManifold I M :=
            radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : CompleteSpace M :=
            (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
          let gR : SmoothRiemannianMetric I M :=
            scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
          have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
          ∃ c : EdgeChart gR hnR Δ σ μ b γ β A (fun x => ρ x / ρ p) (fun x => F x / ρ p),
            c.center = p ∧
            (c.Qn p = 0 ∧
            (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
              (|dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ)) ∧
            (∀ x ∈ ball p (200 * Δ), 0 ≤ (c.Qn x).snd) ∧
            (∀ z : WithLp 2 (ℝ × ℝ), (|z.fst| ≤ 100 * Δ) → z.snd ∈ Icc 0 (100 * Δ) →
              ∃ x ∈ ball p (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) ∧
            (∀ a ∈ A ∩ ball p (190 * Δ), (c.Qn a).snd ≤ τ * Δ) ∧
            (∀ t : ℝ, (|t| ≤ 100 * Δ) → ∃ a ∈ A ∩ ball p (190 * Δ),
              dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)) ∧
            (∀ x, |F x / ρ p - infDist x A| < μ * Δ) ∧
            (∃ OF : Set M, IsOpen OF ∧
              closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} ⊆ OF ∧
              ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => F x / ρ p) OF) ∧
            (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
              ∀ u ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo gR A y,
                Real.sqrt (gR.inner y (gradFun gR (fun x => F x / ρ p) y + u)
                  (gradFun gR (fun x => F x / ρ p) y + u)) < ε) ∧
            (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
              Real.sqrt (gR.inner y
                (gradFun gR (fun z => F z / ρ p / (ρ z / ρ p)) y - gradFun gR (fun x => F x / ρ p) y)
                (gradFun gR (fun z => F z / ρ p / (ρ z / ρ p)) y - gradFun gR (fun x => F x / ρ p) y))
                ≤ 100 * Δ * Λ) ∧
            ∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
              ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ (fun x => F x / ρ p) (fun x => ρ x / ρ p)) x) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h44⟩ := exists_strong_edge_full_collar_cover_QF
    hβ hβγ hγ hγ1
  refine ⟨min σ₀ (1 / 2), lt_min hσ₀ (by norm_num), Δ₀, hΔ₀, fun Δ hΔ hΔ1 => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, h44Δ⟩ := h44 Δ hΔ hΔ1
  refine ⟨min τ₀ (1 / 20000), lt_min hτ₀ (by norm_num), κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ s b' s' hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀
    hb'domain hs'domain hb'error hs'error hsb' hss'
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨b₁, hb₁, h19⟩ := exists_rankOne_coordinate_value_tolerance
    (L := 100 * Δ) (T := 1000 * Δ) (e := μ * Δ) (σ := σ) (by positivity) (by linarith)
    (by positivity) hσ ((hσσ₀.trans (min_le_right _ _)).trans_lt (by norm_num))
  refine ⟨b₁, hb₁, fun Λ hlam hbudget hscale hend => ?_⟩
  intro b hb hbb₀ hbb₁ hb100 hsource hbs E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm ρ hρpos J
    hJ hJE hsec hsecb hρ hρs A
  have hτsmall : τ < 1 / 10000 := (hττ₀.trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨F, hF0, hFL, hcent⟩ := h44Δ σ ε μ τ κ b s b' s' Λ hσ.le
    (hσσ₀.trans (min_le_left _ _)) hε hε1 hμ hμ1 hτ (hττ₀.trans (min_le_left _ _)) hθ hκ hκκ₀ hb
    hbb₀ hb100 hsource hlam hbudget hscale hend hb'domain hs'domain hb'error hs'error hsb' hss' hbs
    E H I M g hEnorm ρ hρpos J hJ hJE hsec hsecb hρ hρs
  refine ⟨F, hF0, hFL, fun p hp => ⟨(hcent p hp).1, ?_⟩⟩
  have hr : 0 < ρ p := hρpos p
  have hpA : p ∈ A := (exists_physical_coarse_border_chart hρ hρpos hΔ1 hτ hτsmall hscale hend
    hb'domain hs'domain hb'error hs'error hsb' hss' hbs p (hJE p hp)).choose_spec.2.2.2.2.1
  have hL := (hcent p hp).2.1
  obtain ⟨Y, mY, q, Fp, Qn, hQn, hQprops, hcl⟩ := (hcent p hp).2.2
  have hsecbR := radialScaled_sectional_bound g (r := b⁻¹) hr (hsecb p hp)
  have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
  let _ := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : CompleteSpace M := (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr hr)).mpr hM
  let gR : SmoothRiemannianMetric I M :=
    scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
  have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
  obtain ⟨η, O, hO, hLO, hη, hηp, hηl, hval, -, -, htest⟩ :=
    h19 b hb hbb₁ E H I M gR hnR Y p q Fp hsecbR
  have hcl' := hcl η (hη.mono (ball_subset_closedBall.trans hLO)) hηl
    (fun x hx => (hval x hx).le) htest
  exact ⟨{ center := p
           rho_center := div_self hr.ne'
           center_mem := hpA
           Y := Y
           instY := mY
           q := q
           split := Fp
           Qn := Qn
           Qn_fst := hQn
           coord := η
           domain := O
           isOpen_domain := hO
           closedBall_subset_domain := hLO
           contMDiffOn_coord := hη
           coord_center := hηp
           lipschitz := hηl
           value := hval
           test := htest
           disk_subset := hcl'.1.1
           cutoff_eq_one := hcl'.1.2
           collar := hcl'.2 }, rfl, hQprops, hL⟩

end DifferentialGeometry.Geometry.Collapse
