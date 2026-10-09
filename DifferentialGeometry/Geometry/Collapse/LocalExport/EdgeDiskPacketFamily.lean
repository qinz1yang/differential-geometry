import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeChartsQF
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacket

/-!
# LFR33 / LFR44: the edge disk packets of the strong-edge family (QF re-chain, packet form)

Blueprint 207A, LFR44 (`thm:collapse-strong-edge-density-cover`, A:28614), last sentence ("If the
common analytic/curvature hypotheses and parameter bounds of LFR33 and LFR38 are supplied at these
centers, the SAME family has ONE distance smoothing, actual proper smooth disk bundles and full
adapted collars ... No choice of a new strong tolerance is made after the family is selected.") and
LFR33 (A:27771, "Each has the actual proper trivial smooth `D²`-bundle ... LFR28 now applies at
every `p_i`, with this SAME `η` and `H` and its own tangential adapted function").

`exists_edgeDiskPackets_of_strong_edge_family`: `exists_edgeCharts_of_strong_edge_family_QF` (same
parameter order) with LFR28's universal bounds added, and, after `Λ` and the common analytic data
`(K, r, v, A_curv)` (LPA04's row-10 slot), its own threshold `bd₀`; for every `b` below all thresholds,
every oriented `M : Type` with the normalized noncollapse and curvature-derivative bounds at every
centre, the ONE shared smoothing `F` and, at every strong edge centre `p` of the family, the chart
`c` together with an `EdgeDiskPacket P` (LC84) with `P.toEdgeChart = c`
(`exists_edgeDiskPacket_threshold` applied at every centre in its normalization).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Integral.Measure
open GC.MetricGeometry DifferentialGeometry.Analysis
open DifferentialGeometry.CheegerGromovCompactness

universe w

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance nezero_finrank_euclidean_three_family_LFR28ROW2 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- **LFR33 / LFR44, the disk packets of the strong-edge family.** See the module docstring. -/
theorem exists_edgeDiskPackets_of_strong_edge_family {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ → 1 ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ s b' s' : ℝ), 0 < σ → σ ≤ σ₀ → σ ≤ 1 / 10 ^ 10 → 0 < ε → ε < 1 / 100 →
        ε ≤ 1 / 10 ^ 8 → 0 < μ → μ ≤ 1 / 1000000 → μ ≤ 1 / 10 ^ 8 → 0 < τ → τ ≤ τ₀ →
        τ ≤ 1 / 10 ^ 30 → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 →
        s < b' / 100000 → s < s' / 100000 →
      ∃ b₁ : ℝ, 0 < b₁ ∧ ∀ (Λ : ℝ≥0), 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
        (Λ : ℝ) < 1 / (1000000 * Δ) → (Λ : ℝ) < s' / (100000000 * Δ ^ 2) →
        100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∀ (K : ℕ), 5 ≤ K → ∀ (r v : ℝ), 0 < r → 0 < v → ∀ (Acurv : ℝ → ℝ),
      ∃ bd₀ : ℝ, 0 < bd₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ → b < b₁ → b < bd₀ → b < 1 / 100 →
        100 * Δ < b⁻¹ → b < s / 100000 →
      ∀ (M : Type) [m : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [hM : CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) g),
        ManifoldOrientation (𝓡 3) M 3 →
      ∀ (ρ : M → ℝ) (hρpos : ∀ x, 0 < ρ x) (J : Finset M),
      J.Nonempty →
      (∀ p ∈ J, @isEdgePoint.{0, 0} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p Δ b s) →
      (∀ p ∈ J, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2)) →
      (∀ p ∈ J, ∀ z ∈ ball p (b⁻¹ * ρ p), SectionalBoundedBelowAt g z (-(b / ρ p) ^ 2)) →
      LipschitzWith Λ ρ → ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ →
      (∀ p ∈ J,
        have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
        letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsRiemannianManifold 𝓘(ℝ, E3) M :=
          radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) M :=
          scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M gR (ball p r) ∧
          ∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k gR y ≤ Acurv R) →
      let A : Set M := closure
        {x | @isEdgePoint.{0, 0} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
      ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        ∀ p ∈ J, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
          (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
          letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : IsRiemannianManifold 𝓘(ℝ, E3) M :=
            radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : CompleteSpace M :=
            (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
          let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) M :=
            scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
          have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := M) gR := isMetricNorm_of_riemannianBundle gR
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
            ∃ P : EdgeDiskPacket gR hnR Δ σ μ b γ β A (fun x => ρ x / ρ p) (fun x => F x / ρ p),
              P.toEdgeChart = c) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hQF⟩ := exists_edgeCharts_of_strong_edge_family_QF
    hβ hβγ hγ hγ1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ hΔ1 => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hQFΔ⟩ := hQF Δ hΔ hΔ1
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ s b' s' hσ hσσ₀ hσ10 hε hε1 hε8 hμ hμ1 hμ8 hτ hττ₀ hτ30 hθ hκ hκκ₀ hb'domain
    hs'domain hb'error hs'error hsb' hss'
  obtain ⟨b₁, hb₁, hQFb⟩ := hQFΔ σ ε μ τ κ s b' s' hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀
    hb'domain hs'domain hb'error hs'error hsb' hss'
  refine ⟨b₁, hb₁, fun Λ hlam hbudget hscale hend hΛ8 K hK r v hr hv Acurv => ?_⟩
  obtain ⟨bd₀, hbd₀, hpk⟩ := exists_edgeDiskPacket_threshold hΔ1 hσ hσ10 hε.le hε8 hμ hμ8 hτ hτ30
    hΛ8 K hK hr hv Acurv
  refine ⟨bd₀, hbd₀, ?_⟩
  intro b hb hbb₀ hbb₁ hbbd hb100 hsource hbs M m _ _ _ hT2 hM hconn _ _ _ g hEnorm o ρ hρpos J hJ
    hJE hsec hsecb hρ hρs hanal A
  obtain ⟨F, hF0, hFL, hcent⟩ := hQFb Λ hlam hbudget hscale hend b hb hbb₀ hbb₁ hb100 hsource hbs
    E3 E3 𝓘(ℝ, E3) M g hEnorm ρ hρpos J hJ hJE hsec hsecb hρ hρs
  refine ⟨F, hF0, hFL, fun p hp => ⟨(hcent p hp).1, ?_⟩⟩
  have hr : 0 < ρ p := hρpos p
  have hsecbR := radialScaled_sectional_bound g (r := b⁻¹) hr (hsecb p hp)
  have hρR := lipschitzWith_normalized_scale hρ hr
  have hsig : SigmaCompactSpace M := inferInstance
  obtain ⟨hvol, hcurv⟩ := hanal p hp
  have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
  let _ := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) M :=
    radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : CompleteSpace M := (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr hr)).mpr hM
  have _ : SigmaCompactSpace M := hsig
  have _ : T2Space (TangentBundle 𝓘(ℝ, E3) M) := hT2
  have _ : ConnectedSpace M := hconn
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) M :=
    scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := M) gR := isMetricNorm_of_riemannianBundle gR
  obtain ⟨c, hcp, hQ, hL1, hL2, hL3, hL4, hL5⟩ := (hcent p hp).2
  obtain ⟨OF, hOF, hCO, hFs⟩ := hL2
  obtain ⟨hQp, hQdist, hheight, hQcover, hborder, hbordercover⟩ := hQ
  refine ⟨c, hcp, ⟨hQp, hQdist, hheight, hQcover, hborder, hbordercover⟩, ?_⟩
  exact hpk b hb hbbd M gR hnR o p hvol hcurv hsecbR γ β A (fun x => ρ x / ρ p)
    (fun x => F x / ρ p) c OF hcp hQp hQdist hheight hQcover
    isClosed_closure hborder hbordercover hL1 hOF hCO hFs hL3 hL4 hL5 hρR
    ((hρs.div_const (ρ p)).contMDiffOn)

end DifferentialGeometry.Geometry.Collapse
