import DifferentialGeometry.Geometry.Collapse.EdgeFullCollarFamily
import DifferentialGeometry.Geometry.Collapse.RankStrata
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.RankExclusion
import DifferentialGeometry.Geometry.Metric.Approximation.RealSplitting
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

/-!
# LFR38's last sentence: with LC20's exclusion the full-collar points are two-stratum points

Blueprint 207A, LFR38 (`thm:collapse-full-edge-collar-packet`, A:28243–28270): "If LC20's
three-stratum exclusion is supplied, these are two-stratum points in the sense of LC16/KL7.1", and
the proof (A:28296–28298): "To identify the stratum, use the exhibited two-splitting and the
SUPPLIED absence of three-splittings; rank two alone would not supply that absence."

The accepted LFR38 theorems (lane F7-EDGE) exhibit at every band point `x` an actual KL
`β₂`-map `Φ_x` from `(M, d/ρ(x), x)` to the plane, but do not state the stratum. Here:

* `mem_scaledSplittingStratum_two_of_plane_approx` (kernel): a plane KL `(β 2)`-map at the scale
  `ρ(x)` and no `(3, β 3)`-splitting at that scale put `x` in the LC16 two-stratum
  `scaledSplittingStratum ρ hρ β 2` (the plane map gives the `(2, β 2)`-splitting by
  `hasEuclideanSplitting_two_of_plane_approximation`);
* `eventually_mem_scaledSplittingStratum_two_of_plane_approx` (LC20 binding): on LC20's eventual
  tail of the standing closed sequence (`exists_eventual_rank_exclusion`), for EVERY scale function
  with LC02's bounds at `x` and LC16 thresholds with `β 3` below LC18's threshold, the exclusion is
  supplied, so every point with a plane `(β 2)`-map at its own scale is a two-stratum point;
* `exists_edge_full_collar_parameters_two_stratum` (single centre, `ρ(p) = 1`) and
  `exists_edge_full_collar_family_two_stratum` (finite family, physical scale `ρ`): the accepted
  conclusions of `exists_edge_full_collar_parameters` / `exists_edge_full_collar_family`, verbatim,
  extended by the sentence: for every positive scale function (single centre: `ρ` itself, once it is
  positive everywhere) and all LC16 thresholds `βs` with `βs 2 = β₂`, if the three-splitting at
  `x` (scale `ρ(x)`, tolerance `βs 3`) is excluded, then `x ∈ scaledSplittingStratum ρ _ βs 2`.
  In the family form the stratum is that of the PHYSICAL metric and scale `(d, ρ)`: the normalized
  pair `(ρ(p)⁻¹ d, ρ/ρ(p))` has the same own-scale metric at `x` (`MetricSpace.rescale_inv_ratio`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold Filter
open scoped Manifold ContDiff Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry
open ContinuousLinearMap

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM uY uS

/-- **The stratum step of LFR38** (kernel). A point with an actual plane Kleiner–Lott `(β 2)`-map at
its own scale `ρ(x)` and no `(3, β 3)`-splitting at that scale lies in the LC16 two-stratum. -/
theorem mem_scaledSplittingStratum_two_of_plane_approx {M : Type uM} [m : MetricSpace M]
    {ρ : M → ℝ} (hρ : ∀ y, 0 < ρ y) {β : ℕ → ℝ} {x : M}
    (hΦ : Nonempty (@KleinerLottApprox M (WithLp 2 (ℝ × ℝ))
      (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) _ x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (β 2)))
    (h3 : ¬ @HasEuclideanSplitting.{uM, uS} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 3
      (β 3)) :
    x ∈ scaledSplittingStratum.{uM, uS} ρ hρ β 2 := by
  obtain ⟨Φ⟩ := hΦ
  change scaledSplittingRank.{uM, uS} ρ hρ β x = 2
  refine scaledSplittingRank_eq_iff.{uM, uS}.mpr ⟨by norm_num, fun _ =>
    @hasEuclideanSplitting_two_of_plane_approximation.{uM, uS} M
      (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x (β 2) Φ, fun j hj hj3 => ?_⟩
  obtain rfl : j = 3 := by omega
  exact h3

section LC20

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The stratum step on LC20's tail.** For the standing closed sequence (LC20's hypotheses) there
is `w₀` such that for `w < w₀` one tail has: for every scale function `ρ > 0`, all LC16 thresholds
`β` with `β 3` at most LC18's threshold, every point `x` whose scale `ρ(x)` satisfies LC02's bounds
and which carries an actual plane Kleiner–Lott `(β 2)`-map at the scale `ρ(x)` is a two-stratum
point. The three-splitting exclusion is LC20's (`exists_eventual_rank_exclusion`). -/
theorem eventually_mem_scaledSplittingStratum_two_of_plane_approx
    (hdim : Module.finrank ℝ E = 3) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type uM) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
      (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
      ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
      (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
        curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∀ (ρ : X i → ℝ) (hρ : ∀ y, 0 < ρ y) (β : ℕ → ℝ),
        β 3 ≤ threeSplittingExclusionThreshold.{uM, uS} → ∀ x : X i,
        firstVolumeScale (g i) x w / 2 ≤ ρ x →
        ρ x ≤ 2 * firstVolumeScale (g i) x (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) →
        Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × ℝ))
          ((mX i).rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) _ x
          (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (β 2)) →
        x ∈ scaledSplittingStratum.{uM, uS} ρ hρ β 2 := by
  obtain ⟨w₀, hw₀, htail⟩ := exists_eventual_rank_exclusion.{uM, uS} (I := I) hdim hΛ
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw hww hwc X mX _ _ _ g hmetric α hα hstand
  filter_upwards [htail w hw hww hwc X g hmetric α hα hstand] with i hi
  intro ρ hρ β hβ x hlow hup hΦ
  exact mem_scaledSplittingStratum_two_of_plane_approx hρ hΦ
    ((hi x (ρ x) (hρ x) hlow hup).1 (β 3) hβ)

end LC20

/-- **LFR38 with its last sentence** (single centre, `ρ(p) = 1`): the conclusions of
`exists_edge_full_collar_parameters`, and in addition every band point `x` is a two-stratum point
of `(M, d, ρ)` for all LC16 thresholds `βs` with `βs 2 = β₂` as soon as `ρ > 0` everywhere and the
three-splitting at `x` (scale `ρ(x)`, tolerance `βs 3`) is excluded (LC20's exclusion, supplied). -/
theorem exists_edge_full_collar_parameters_two_stratum {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 ≤ ε → ε < 1 / 100 →
        μ ≤ 1 / 1000000 → τ ≤ τ₀ → 0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type uY) [MetricSpace Y] (p : M) (y₀ : Y)
        (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b)
        (Q : M → WithLp 2 (ℝ × ℝ)) (A : Set M) (ρ F f : M → ℝ) (O : Set M),
      (∀ z ∈ ball p (10000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2)) →
      (∀ z ∈ ball p b⁻¹, SectionalBoundedBelowAt g z (-b ^ 2)) →
      IsClosed A → Q p = 0 →
      (∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
        |dist (Q y) (Q z) - dist y z| ≤ τ * Δ) →
      (∀ y ∈ ball p (200 * Δ), 0 ≤ (Q y).snd) →
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ) →
      p ∈ A → (∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ) →
      (∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ A ∩ ball p (190 * Δ),
        dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
      (∀ z ∈ ball p (200 * Δ), (Q z).fst = (α.toFun z).fst) →
      LipschitzWith Λ ρ → ρ p = 1 → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      IsOpen O →
      closedBall p (20 * Δ) ∩ {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} ⊆ O →
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O → LipschitzWith (Real.toNNReal (1 + ε)) F →
      (∀ y, |F y - infDist y A| ≤ μ * Δ) →
      (∀ y ∈ closedBall p (20 * Δ) ∩ {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
        ∀ v ∈ minimizingDirectionsTo g hEnorm A y,
          Real.sqrt (g.inner y (gradFun g F y + v) (gradFun g F y + v)) < ε) →
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
      LipschitzWith (Real.toNNReal (1 + σ)) f →
      (∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ) →
      (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
        ∀ w : TangentSpace I x, g.inner x w w = 1 →
        intrinsicGeodesic g hEnorm x w (dist x x') = x' →
        |mvfderiv (I := I) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
      ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ → Δ / 10 ≤ F x / ρ x → F x / ρ x ≤ 10 * Δ →
      ∃ hq : 99 / 100 ≤ ρ x ∧ ρ x ≤ 101 / 100,
        (letI := mM.rescale (ρ x)⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq.1));
          ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
            ∀ y, Φ.toFun y = @planeComparisonMap M mM Q p x Δ (ρ x) y) ∧
        (∀ (hρpos : ∀ y, 0 < ρ y) (βs : ℕ → ℝ), βs 2 = β →
          ¬ @HasEuclideanSplitting.{uM, uS} M (mM.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x 3
            (βs 3) → x ∈ scaledSplittingStratum.{uM, uS} ρ hρpos βs 2) ∧
        let J := edgeReferenceCoordinates ![f, fun z => F z / ρ z]
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x (300 * ρ x)) ∧
        (∀ y ∈ ball x (100 * ρ x), Function.Surjective (mvfderiv (I := I) J y)) ∧
        (∀ y ∈ ball x (100 * ρ x), ∀ z ∈ ball x (100 * ρ x),
          ‖J y - J z‖ ≤ (1 + γ) * (dist y z / ρ x)) ∧
        (∀ y ∈ ball x (100 * ρ x), infDist (J y) (ball (J x) 100) < 100 * γ) ∧
        (∀ v ∈ ball (J x) 100, ∃ y ∈ ball x (100 * ρ x), ‖J y - v‖ < 100 * γ) ∧
        ∀ y ∈ ball x (100 * ρ x), ∀ z ∈ ball x (100 * ρ x / γ), ρ x < dist y z →
          ∀ W : TangentSpace I y, g.inner y W W = 1 →
          intrinsicGeodesic g hEnorm y W (dist y z) = z →
          ‖ρ x • mvfderiv (I := I) J y W - (dist y z / ρ x)⁻¹ •
            (planeReferenceIsometry (planeComparisonMap Q p x Δ (ρ x) z) -
              planeReferenceIsometry (planeComparisonMap Q p x Δ (ρ x) y))‖ < γ := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hX⟩ := exists_edge_full_collar_parameters.{uE, uH, uM, uY} hβ hβγ hγ hγ1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hXΔ⟩ := hX Δ hΔ
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M mM _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α Q A ρ F f O
    hsecκ hsecb hA hQp hdist hheight hcover hpA hborder hbordercover hQα hρ hρp hρs
    hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx hfx hη hη'
  obtain ⟨hq, ⟨Φ, hΦ⟩, hJ⟩ := hXΔ σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam
    hbudget E H I M g hEnorm Y p y₀ α Q A ρ F f O hsecκ hsecb hA hQp hdist hheight hcover hpA
    hborder hbordercover hQα hρ hρp hρs hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx hfx
    hη hη'
  refine ⟨hq, ⟨Φ, hΦ⟩, fun hρpos βs hβs h3 => ?_, hJ⟩
  refine mem_scaledSplittingStratum_two_of_plane_approx hρpos ?_ h3
  rw [hβs]
  exact ⟨Φ⟩

/-- **LFR38 with its last sentence** (finite family): the conclusions of
`exists_edge_full_collar_family`, and in addition at every centre every band point `x` is a
two-stratum point of the PHYSICAL `(M, d, ρ)` for all LC16 thresholds `βs` with `βs 2 = β₂` as
soon as the three-splitting at `x` (physical scale `ρ(x)`, tolerance `βs 3`) is excluded (LC20's
exclusion, supplied). -/
theorem exists_edge_full_collar_family_two_stratum {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ → 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [hM : CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (A : Set M) (P : Finset M) (Q : M → M → WithLp 2 (ℝ × ℝ)) (ρ : M → ℝ)
        (hρpos : ∀ x, 0 < ρ x),
      P.Nonempty → IsClosed A → (∀ p ∈ P, Q p p = 0) →
      (∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
        |dist (Q p x) (Q p y) - dist x y| ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q p x).snd) →
      (∀ p ∈ P, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
        z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
          ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q p x) z ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, p ∈ A) →
      (∀ p ∈ P, ∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q p a).snd ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) →
        ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
          dist (Q p a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2)) →
      LipschitzWith Λ ρ → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        ∀ p ∈ P, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
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
        ∀ (Y : Type uY) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b),
        (∀ z ∈ ball p b⁻¹, SectionalBoundedBelowAt gR z (-b ^ 2)) →
        (∀ z ∈ ball p (200 * Δ), (Q p z).fst = ρ p * (α.toFun z).fst) →
        ∀ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
        LipschitzWith (Real.toNNReal (1 + σ)) f →
        (∀ x ∈ ball p (100 * Δ), |f x - (α.toFun x).fst| ≤ μ * Δ) →
        (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
          ∀ w : TangentSpace I x, gR.inner x w w = 1 →
          intrinsicGeodesic gR hnR x w (dist x x') = x' →
          |mvfderiv (I := I) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
        ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
          Δ / 10 ≤ F x / ρ p / (ρ x / ρ p) → F x / ρ p / (ρ x / ρ p) ≤ 10 * Δ →
        ∃ hq : 99 / 100 ≤ ρ x / ρ p ∧ ρ x / ρ p ≤ 101 / 100,
          (letI := (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).rescale (ρ x / ρ p)⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq.1));
            ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
              ∀ y, Φ.toFun y = @planeComparisonMap M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p)))
                (fun z => (ρ p)⁻¹ • Q p z) p x Δ (ρ x / ρ p) y) ∧
          (∀ βs : ℕ → ℝ, βs 2 = β →
            ¬ @HasEuclideanSplitting.{uM, uS} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x 3
              (βs 3) → x ∈ @scaledSplittingStratum.{uM, uS} M m ρ hρpos βs 2) ∧
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
              (planeReferenceIsometry (planeComparisonMap (fun z => (ρ p)⁻¹ • Q p z) p x Δ
                (ρ x / ρ p) z) -
                planeReferenceIsometry (planeComparisonMap (fun z => (ρ p)⁻¹ • Q p z) p x Δ
                  (ρ x / ρ p) y))‖ < γ) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hfam⟩ := exists_edge_full_collar_family.{uE, uH, uM, uY} hβ hβγ hγ hγ1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔfam⟩ := hfam Δ hΔ
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm A P Q ρ hρpos hP hA hQp hdist hheight hcover
    hpA hborder hbordercover hsec hρ hρs
  obtain ⟨F, hF0, hFL, hcent⟩ := hΔfam σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb
    hbb₀ hlam hbudget E H I M g hEnorm A P Q ρ hρpos hP hA hQp hdist hheight hcover hpA
    hborder hbordercover hsec hρ hρs
  refine ⟨F, hF0, hFL, fun p hp => ⟨(hcent p hp).1, ?_⟩⟩
  intro hmetric gR hnR Y _ y₀ α hsecb hQα f hfs hfL hfval htest x hx hfx hη hη'
  obtain ⟨hq, ⟨Φ, hΦ⟩, hJ⟩ :=
    (hcent p hp).2 Y y₀ α hsecb hQα f hfs hfL hfval htest x hx hfx hη hη'
  refine ⟨hq, ⟨Φ, hΦ⟩, fun βs hβs h3 => ?_, hJ⟩
  refine mem_scaledSplittingStratum_two_of_plane_approx hρpos ?_ h3
  rw [hβs, ← MetricSpace.rescale_inv_ratio m (hρpos p) (hρpos x)]
  exact ⟨Φ⟩

end DifferentialGeometry.Geometry.Collapse
