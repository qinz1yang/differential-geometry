import DifferentialGeometry.Geometry.Collapse.StrongEdgeFullCollarCover

/-!
# Consumer: LFR44's packets — disk-domain cover and rank-two collar from ONE smoothing

`exists_strong_edge_full_collar_cover` at `γ = 1/1000`, `β₂ = 10⁻⁷`: for a finite family of strong
edge points, one smoothing `F` such that at every centre, for every LFR19-type coordinate `f` of
the strong edge's splitting, the centre lies in the actual edge disk domain and the original pair
`(f, F/ρ)` is onto `ℝ²` throughout the own-scale ball of every band point.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Analysis

universe w uE uH uM

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- One smoothing; every strong-edge centre is in its disk domain and the pair has rank two. -/
theorem strong_edge_family_centre_in_disk_and_rankTwo :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ → 1 ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b s b' s' : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ → b < 1 / 100 → 100 * Δ < b⁻¹ →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < 1 / 1000000 →
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
      ∃ F : M → ℝ, ∀ p ∈ J,
        ∃ (Y : Type w) (mY : MetricSpace Y), letI := mY
          ∃ (q : Y) (Fp : @KleinerLottApprox M (WithLp 2 (ℝ × Y))
              (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), q)) b),
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
          p ∈ edgeDiskDomain p Δ (fun x => f x.val) (fun x => F x / ρ p) (fun x => ρ x / ρ p) ∧
          ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
            Δ / 10 ≤ F x / ρ p / (ρ x / ρ p) → F x / ρ p / (ρ x / ρ p) ≤ 10 * Δ →
            ∀ y ∈ ball x (100 * (ρ x / ρ p)), Function.Surjective (mvfderiv (I := I)
              (edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)]) y)) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hcov⟩ := exists_strong_edge_full_collar_cover.{w, uE, uH, uM}
    (β := 1 / 10000000) (γ := 1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ hΔ1 => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔcov⟩ := hcov Δ hΔ hΔ1
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b s b' s' Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb hbb₀ hb100 hsource
    hlam hbudget hscale hend hb'domain hs'domain hb'error hs'error hsb' hss' hbs
    E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm ρ hρpos J hJ hJE hsec hsecb hρ hρs
  obtain ⟨F, -, -, hcent⟩ := hΔcov σ ε μ τ κ b s b' s' Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ
    hκκ₀ hb hbb₀ hb100 hsource hlam (by linarith) hscale hend hb'domain hs'domain hb'error
    hs'error hsb' hss' hbs E H I M g hEnorm ρ hρpos J hJ hJE hsec hsecb hρ hρs
  refine ⟨F, fun p hp => ?_⟩
  obtain ⟨-, Y, mY, q, Fp, Qn, -, hblock⟩ := hcent p hp
  refine ⟨Y, mY, q, Fp, ?_⟩
  intro hmetric gR hnR f hfs hfL hfval htest
  have hall := hblock f hfs hfL hfval htest
  obtain ⟨⟨hdisk, -⟩, hcol⟩ := hall
  have hΔpos : 0 < Δ := by linarith
  refine ⟨hdisk (@mem_ball_self M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).toPseudoMetricSpace
    p (3 * Δ) (by positivity)), fun x hx hfx hη hη' y hy => ?_⟩
  obtain ⟨_hq, _hΦ, hJ'⟩ := hcol x hx hfx hη hη'
  exact hJ'.2.1 y hy

end DifferentialGeometry.Geometry.Collapse
