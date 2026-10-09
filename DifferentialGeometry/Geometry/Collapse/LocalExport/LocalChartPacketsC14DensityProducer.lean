import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Density
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Producer
import DifferentialGeometry.Geometry.Collapse.StrongEdgeTail

/-!
# Producer of the final family with LFR44 item 2 (`LocalChartPacketsC14D`)

Lane C14-FAM3. ONE producer yields, on the SAME tail as `eventually_nonempty_localChartPacketsC14`
(every parameter clause verbatim), the extended family `LocalChartPacketsC14D`: the C14 family
together with LFR44 item 2 (`weak_edge_density`).

* `exists_strong_edge_density_tail_FAM3`: LFR44 items 1–2 in the strong-point form
  (`exists_strong_edge_density_riemannian`, StrongEdgeRiemannian.lean) on a tail of a standing
  sequence, the collapsed-model hypothesis discharged by LC09 (`exists_kl618_metric_model_tail`), as
  in `exists_strong_edge_cover_tail` (StrongEdgeTail.lean) for the finite form. The collapsed-model
  tolerance is chosen from `Δ, β₂, s`, the rank-one threshold is a function `b₀ βE` of the strong
  quality, the volume threshold `w₀` depends on `Δ, β₂, s, Λ₀` only.
* `eventually_nonempty_localChartPacketsC14D`: the statement of
  `eventually_nonempty_localChartPacketsC14` concluding `LocalChartPacketsC14D`. No new parameter
  request: LC09's `w₀` is folded (min) into the producer's output `w₀` (chosen after `Λ`, with
  `Λ₀ := Λ`), the rank-one threshold `b₀ b` into the output `b₀` (chosen after `b`, with
  `βE := b`); the density lemma's model tolerance is internal.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

universe u

/-- **LFR44 items 1–2, strong-point form, on a tail of a standing sequence of closed Riemannian
three-manifolds** (blueprint 207A, A:28614–28634; the collapsed-model hypothesis of
`exists_strong_edge_density_riemannian` discharged by LC09 at the scale `ρ(p)`). On that tail, for
every strong quality `βE`, every `Λ`-Lipschitz scale (`Λ < (10⁶Δ)⁻¹`), every rank-one threshold
`β 1 < b₀ βE` and every nonslim one-stratum point `p` whose scale lies within LC02's bounds:
(1) some strong edge `a` has `d(a, p) < Δρ(a)`; (2) every weak edge `q` (qualities `< 10⁻⁸`) with
`d(q, p) < 10Δρ(p)` has a strong edge `a` with `d(q, a) < ρ(a)`. -/
theorem exists_strong_edge_density_tail_FAM3 {Δ β₂ s Λ₀ : ℝ} (hβ₂ : 0 < β₂)
    (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ) (hs : 0 < s) (hssmall : s < 1 / 100)
    (hΛ₀ : 0 < Λ₀) :
    ∃ b₀ : ℝ → ℝ, (∀ βE : ℝ, 0 < βE → βE < 1 / 100 → 0 < b₀ βE) ∧
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        ∀ᶠ i in atTop, ∀ βE : ℝ, 0 < βE → βE < 1 / 100 →
        ∀ (Λ : NNReal) (ρ : X i → ℝ) (hρpos : ∀ x, 0 < ρ x), LipschitzWith Λ ρ →
          (Λ : ℝ) < 1 / (1000000 * Δ) →
        ∀ β : ℕ → ℝ, β 2 = β₂ → β 1 < b₀ βE →
        ∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1,
        firstVolumeScale (g i) p w / 2 ≤ ρ p →
        ρ p ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ₀⁻¹) ^ 3)) →
        (letI := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p));
          ∀ (A : Type) [MetricSpace A] (a : A), Bornology.IsBounded (univ : Set A) →
            diam (univ : Set A) < 1000 * Δ →
            ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
        (∃ a : X i, (@isEdgePoint.{u, 0} (X i)
            ((mX i).rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist a p < Δ * ρ a) ∧
          ∀ (b' s' : ℝ) (q : X i), b' < 1 / 100000000 → s' < 1 / 100000000 →
            (@isEdgePoint.{u, 0} (X i) ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q)))
              q Δ b' s') →
            dist q p < 10 * Δ * ρ p →
            ∃ a : X i, (@isEdgePoint.{u, 0} (X i)
              ((mX i).rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist q a < ρ a := by
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  obtain ⟨a₀, ha₀, hpar⟩ := exists_strong_edge_density_riemannian.{u, 0, 0, 0} (I := 𝓘(ℝ, E3))
    hβ₂ hβ₂small hΔ hs hssmall
  choose! b₀ hb₀ hdata using hpar
  obtain ⟨w₀, hw₀, htail⟩ := exists_kl618_metric_model_tail (I := 𝓘(ℝ, E3)) hdim
    (σ := min a₀ (1 / 2)) (lt_min ha₀ (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num))
    hΛ₀
  refine ⟨b₀, hb₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc X mX _ _ _ g hmetric α hα hstand
  filter_upwards [htail w hw hww hwc X g hmetric α hα hstand] with i hi
  intro βE hβE hβE' Λ ρ hρpos hρ hscale β hβ2 hβ1 p hp hlow hup hnonslim
  obtain ⟨Y, mY, y, hcY, -, hdimY, hcompY, hsegY, hf⟩ := hi p (ρ p) (hρpos p) hlow hup
  exact hdata βE hβE hβE' (X i) (g i) (hmetric i) Λ ρ hρpos hρ hscale β hβ2 hβ1 p hp hnonslim
    Y y (min a₀ (1 / 2)) hsegY hdimY hcompY (min_le_left _ _) hf

/-- **Producer of the final family with LFR44 item 2.** The statement of
`eventually_nonempty_localChartPacketsC14` (every clause verbatim, the same tail) concluding
`LocalChartPacketsC14D`: the C14 family of that tail together with LFR44 item 2 at the family's own
parameters (`Δ`, strong `b, s`, weak `b', s'`, threshold `β 1`). See the module docstring. -/
theorem eventually_nonempty_localChartPacketsC14D (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartPacketsC14D (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ') := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsC14 K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  -- LFR44 item 2 on LC09's tail: `Λ₀ := Λ`, its volume threshold folded into `w₀`
  obtain ⟨bD, hbD, wD, hwD, hD⟩ :=
    exists_strong_edge_density_tail_FAM3.{0} hβ₂ hβ₂small hΔ hs hssmall hΛ
  refine ⟨min w₀ wD, lt_min hw₀ hwD, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h w hw (hww.trans_le (min_le_left _ _)) hwc
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  have hb100 : b < 1 / 100 := by
    have h1 : s / 100000 < 1 / 100 := by linarith
    linarith
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs
  -- the rank-one threshold of LFR44 at the strong quality `βE := b`, folded into `b₀`
  refine ⟨min b₀ (bD b), lt_min hb₀ (hbD b hb hb100),
    fun β hβ2 hβ1 hβ1b hβone hβ3 ζ cap hβζ hζone hcap => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ', h⟩ :=
    h β hβ2 hβ1 (hβ1b.trans_le (min_le_left _ _)) hβone hβ3 ζ cap hβζ hζone hcap
  refine ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ',
    fun T hT hTΛ e he he1 X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand hder hor
  refine ⟨V, hTV, δ, hδ0, hδδ', fun Lmax hLmax => ?_⟩
  have hΔ100 : 100 ≤ Δ := by
    have h100 : 10000 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hinv : 1 / (1000000 * Δ) ≤ 1 / 100000000 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hΛc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ.le
  filter_upwards [h Lmax hLmax,
    hD w hw (hww.trans_le (min_le_right _ _)) hwc X g hmetric α hα hstand] with i hi hDi
  obtain ⟨ρ, hρpos, hρb, ⟨P⟩⟩ := hi
  refine ⟨ρ, hρpos, hρb, ⟨{ toLocalChartPacketsC14 := P, weak_edge_density := ?_ }⟩⟩
  intro p hp hns q hq hqp
  exact (hDi b hb hb100 (Real.toNNReal Λ) ρ hρpos P.lipschitz_scale (by rw [hΛc]; exact hΛ44) β
    hβ2 (hβ1b.trans_le (min_le_right _ _)) p hp (hρb p).1.le (hρb p).2.le
    (by
      intro Z mZ z hbdd hdiam hne
      exact hns ⟨Z, mZ, z, hbdd, hdiam, hne⟩)).2 b' s' q
    (hb'd.trans_le hinv) (hs'd.trans_le hinv) hq hqp

end DifferentialGeometry.Geometry.Collapse
