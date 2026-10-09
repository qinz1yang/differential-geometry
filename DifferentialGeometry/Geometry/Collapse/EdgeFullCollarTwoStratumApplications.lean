import DifferentialGeometry.Geometry.Collapse.EdgeFullCollarTwoStratum

/-!
# Consumers: the full-collar band lies in the two-stratum and misses the other strata

* `hasEuclideanSplitting_two_and_not_mem_of_mem_two`: a two-stratum point has an actual
  `(2, β 2)`-splitting at its own scale and lies in no other LC16 stratum.
* `eventually_plane_approx_two_stratum_only` (LC20 binding): on LC20's tail, a point with a plane
  `(β 2)`-map at an admissible scale has a `(2, β 2)`-splitting and lies in no stratum other than
  the two-stratum.
* `edge_full_collar_band_two_stratum` (single centre) and `edge_family_band_two_stratum` (finite
  family, physical scale), at the real values `γ = 1/1000`, `β₂ = 10⁻⁷`: with LC20's exclusion
  supplied at a band point, the band point has a `(2, β₂)`-splitting and lies in no LC16 stratum
  other than the two-stratum (in particular not in the one-stratum).
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

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM uY uS

/-- A point of the LC16 two-stratum has a `(2, β 2)`-splitting at its own scale and lies in no
other stratum. -/
theorem hasEuclideanSplitting_two_and_not_mem_of_mem_two {M : Type uM} [m : MetricSpace M]
    {ρ : M → ℝ} {hρ : ∀ y, 0 < ρ y} {β : ℕ → ℝ} {x : M}
    (hx : x ∈ scaledSplittingStratum.{uM, uS} ρ hρ β 2) :
    @HasEuclideanSplitting.{uM, uS} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 2 (β 2) ∧
      ∀ k : Fin 4, k ≠ 2 → x ∉ scaledSplittingStratum.{uM, uS} ρ hρ β k := by
  have hrank : scaledSplittingRank.{uM, uS} ρ hρ β x = 2 := hx
  exact ⟨(scaledSplittingRank_eq_iff.{uM, uS}.mp hrank).2.1 (by norm_num),
    fun k hk hk' => disjoint_left.mp (scaledSplittingStrata_disjoint.{uM, uS} ρ hρ β hk) hk' hx⟩

section LC20

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- On LC20's tail, a point with a plane Kleiner–Lott `(β 2)`-map at an admissible scale has a
`(2, β 2)`-splitting and lies in no LC16 stratum other than the two-stratum. -/
theorem eventually_plane_approx_two_stratum_only (hdim : Module.finrank ℝ E = 3) {Λ : ℝ}
    (hΛ : 0 < Λ) :
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
        @HasEuclideanSplitting.{uM, uS} (X i) ((mX i).rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 2
          (β 2) ∧ ∀ k : Fin 4, k ≠ 2 → x ∉ scaledSplittingStratum.{uM, uS} ρ hρ β k := by
  obtain ⟨w₀, hw₀, htail⟩ :=
    eventually_mem_scaledSplittingStratum_two_of_plane_approx.{uE, uH, uM, uS} (I := I) hdim hΛ
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw hww hwc X mX _ _ _ g hmetric α hα hstand
  filter_upwards [htail w hw hww hwc X g hmetric α hα hstand] with i hi
  intro ρ hρ β hβ x hlow hup hΦ
  exact hasEuclideanSplitting_two_and_not_mem_of_mem_two (hi ρ hρ β hβ x hlow hup hΦ)

end LC20

/-- **LFR38's sentence at one centre, consumed** (`γ = 1/1000`, `β₂ = 10⁻⁷`): a band point at which
LC20's exclusion is supplied has a `(2, β₂)`-splitting and lies in no LC16 stratum but the
two-stratum. -/
theorem edge_full_collar_band_two_stratum :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 ≤ ε → ε < 1 / 100 →
        μ ≤ 1 / 1000000 → τ ≤ τ₀ → 0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < 1 / 1000000 →
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
      ∀ (hρpos : ∀ y, 0 < ρ y) (βs : ℕ → ℝ), βs 2 = 1 / 10000000 →
        ¬ @HasEuclideanSplitting.{uM, uS} M (mM.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x 3
          (βs 3) →
        @HasEuclideanSplitting.{uM, uS} M (mM.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x 2
          (βs 2) ∧ ∀ k : Fin 4, k ≠ 2 → x ∉ scaledSplittingStratum.{uM, uS} ρ hρpos βs k := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hX⟩ :=
    exists_edge_full_collar_parameters_two_stratum.{uE, uH, uM, uY, uS} (β := 1 / 10000000)
      (γ := 1 / 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hXΔ⟩ := hX Δ hΔ
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M mM _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α Q A ρ F f O
    hsecκ hsecb hA hQp hdist hheight hcover hpA hborder hbordercover hQα hρ hρp hρs
    hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx hfx hη hη' hρpos βs hβs h3
  obtain ⟨-, -, hstr, -⟩ := hXΔ σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam
    (by linarith) E H I M g hEnorm Y p y₀ α Q A ρ F f O hsecκ hsecb hA hQp hdist hheight hcover
    hpA hborder hbordercover hQα hρ hρp hρs hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx
    hfx hη hη'
  exact hasEuclideanSplitting_two_and_not_mem_of_mem_two (hstr hρpos βs hβs h3)

/-- **LFR38's sentence for a finite family, consumed** (`γ = 1/1000`, `β₂ = 10⁻⁷`): at every centre,
a band point at which LC20's exclusion is supplied (physical scale) has a `(2, β₂)`-splitting and
lies in no LC16 stratum of `(M, d, ρ)` but the two-stratum. -/
theorem edge_family_band_two_stratum :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ → 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < 1 / 1000000 →
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
        ∀ βs : ℕ → ℝ, βs 2 = 1 / 10000000 →
          ¬ @HasEuclideanSplitting.{uM, uS} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x 3
            (βs 3) →
          @HasEuclideanSplitting.{uM, uS} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x 2
            (βs 2) ∧ ∀ k : Fin 4, k ≠ 2 → x ∉ @scaledSplittingStratum.{uM, uS} M m ρ hρpos βs k) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hfam⟩ :=
    exists_edge_full_collar_family_two_stratum.{uE, uH, uM, uY, uS} (β := 1 / 10000000)
      (γ := 1 / 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔfam⟩ := hfam Δ hΔ
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm A P Q ρ hρpos hP hA hQp hdist hheight hcover
    hpA hborder hbordercover hsec hρ hρs
  obtain ⟨F, hF0, hFL, hcent⟩ := hΔfam σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb
    hbb₀ hlam (by linarith) E H I M g hEnorm A P Q ρ hρpos hP hA hQp hdist hheight hcover hpA
    hborder hbordercover hsec hρ hρs
  refine ⟨F, hF0, hFL, fun p hp => ⟨(hcent p hp).1, ?_⟩⟩
  intro hmetric gR hnR Y _ y₀ α hsecb hQα f hfs hfL hfval htest x hx hfx hη hη' βs hβs h3
  obtain ⟨-, -, hstr, -⟩ :=
    (hcent p hp).2 Y y₀ α hsecb hQα f hfs hfL hfval htest x hx hfx hη hη'
  exact @hasEuclideanSplitting_two_and_not_mem_of_mem_two M m ρ hρpos βs x (hstr βs hβs h3)

end DifferentialGeometry.Geometry.Collapse
