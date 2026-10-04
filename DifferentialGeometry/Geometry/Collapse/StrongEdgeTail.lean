import DifferentialGeometry.Geometry.Collapse.StrongEdgeRiemannian
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.KL618Tail
import DifferentialGeometry.Geometry.Metric.Approximation.PrescribedLowDimensionalModel

/-!
# LFR39 and LFR44 on a tail of a standing sequence (model hypothesis discharged by LC09)

Blueprint 207A, LFR39 (`lem:collapse-prescribed-low-dimensional-model`, A:28354–28391) and LFR44
(`thm:collapse-strong-edge-density-cover`, A:28614–28752, "Its source application is LC08–LC09,
using LC15, and the sufficiently late uniform-in-center curvature tail"). LC09
(`exists_kl618_metric_model_tail`) supplies, on a tail of a standing sequence of closed Riemannian
three-manifolds and at every scale within LC02's bounds, a KL `σ`-map to a complete proper geodesic
nonnegative model of dimension `≤ 2`. Here `σ` is the collapsed-model tolerance of the row, chosen
before every later quality:

* `exists_kl618_prescribed_one_dimensional_model_tail` (LFR39): every actual `(1,β)`-splitting with
  `β ≤ a₀` becomes an actual `(1,e)`-splitting onto a one-dimensional model, with the SAME first
  coordinate;
* `exists_strong_edge_cover_tail` (LFR44): a finite strong-edge family covering the nonslim rank-one
  stratum and the weak points of item 2. The tail does not depend on the strong quality `βE`: the
  rank-one threshold is a function `b₀ βE` fixed before the sequence.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u w w'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LFR39 on a tail of a standing sequence.** -/
theorem exists_kl618_prescribed_one_dimensional_model_tail (hdim : Module.finrank ℝ E = 3)
    {e Λ₀ : ℝ} (he : 0 < e) (heone : e < 1) (hΛ₀ : 0 < Λ₀) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ < e / 10 ∧ ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        ∀ᶠ i in atTop, ∀ (p : X i) (ρ : ℝ) (hρ : 0 < ρ), firstVolumeScale (g i) p w / 2 ≤ ρ →
          ρ ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ₀⁻¹) ^ 3)) →
          ∀ (Z : Type w) [MetricSpace Z] (z : Z) (β : ℝ), β ≤ a₀ →
          letI := (mX i).rescale ρ⁻¹ (inv_pos.mpr hρ)
          ∀ F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β,
          ∃ (W : Type) (mW : MetricSpace W), letI := mW
            ∃ q : W, ProperSpace W ∧ CompleteSpace W ∧
              fourPointComparison 0 (univ : Set W) ∧ dimH (univ : Set W) ≤ 1 ∧
              (∀ a b : W, ∃ γ : Icc (0 : ℝ) 1 → W, Continuous γ ∧
                γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
                ∀ s t, dist (γ s) (γ t) = dist a b * dist s t) ∧
              ∃ G : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) e,
                ∀ x : X i, (G.toFun x).fst = (F.toFun x).fst := by
  obtain ⟨a₀, ha₀, ha₀e, hker⟩ := exists_prescribed_one_dimensional_model_parameter.{u, 0, w} he heone
  have ha₀one : a₀ < 1 := ha₀e.trans (by linarith)
  obtain ⟨w₀, hw₀, htail⟩ := exists_kl618_metric_model_tail (I := I) hdim ha₀ ha₀one hΛ₀
  refine ⟨a₀, ha₀, ha₀e, w₀, hw₀, ?_⟩
  intro w hw hww hwc X mX _ _ _ g hmetric α hα hstand
  filter_upwards [htail w hw hww hwc X g hmetric α hα hstand] with i hi
  intro p ρ hρ hlow hup Z _ z β hβ F
  obtain ⟨Y, mY, y, hcY, _, hdimY, hcompY, hsegY, ⟨f⟩⟩ := hi p ρ hρ hlow hup
  let := (mX i).rescale ρ⁻¹ (inv_pos.mpr hρ)
  exact hker (X i) p Y y (Metric.arbitrarily_short_curves_of_metric_segments hsegY) hdimY hcompY
    Z z a₀ β le_rfl hβ f F

/-- **LFR44 on a tail of a standing sequence of closed Riemannian three-manifolds.** The
collapsed-model tolerance `a₀` is fixed from `Δ, β₂, s`; the rank-one threshold is a function
`b₀ βE` of the strong quality; LC09's tail (for a scale `ρ` within LC02's bounds at every point) does
not depend on `βE`. On that tail, for every strong quality, every `Λ`-Lipschitz LC02 scale and every
pair of weak qualities `< 10⁻⁸`, there is a finite family of strong edges (own scale) with pairwise
disjoint `B(q_i, Δρ(q_i)/3)`, whose `Δρ(q_i)`-balls cover all strong edges and whose
`2Δρ(q_i)`-balls cover every nonslim rank-one point and every weak edge within `10Δρ(p)` of one. -/
theorem exists_strong_edge_cover_tail (hdim : Module.finrank ℝ E = 3)
    {Δ β₂ s Λ₀ : ℝ} (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ)
    (hs : 0 < s) (hssmall : s < 1 / 100) (hΛ₀ : 0 < Λ₀) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ b₀ : ℝ → ℝ, (∀ βE : ℝ, 0 < βE → βE < 1 / 100 → 0 < b₀ βE) ∧
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        ∀ᶠ i in atTop, ∀ βE : ℝ, 0 < βE → βE < 1 / 100 →
        ∀ (Λ : NNReal) (ρ : X i → ℝ) (hρpos : ∀ x, 0 < ρ x), LipschitzWith Λ ρ →
          (Λ : ℝ) < 1 / (1000000 * Δ) →
        (∀ x, firstVolumeScale (g i) x w / 2 ≤ ρ x ∧
          ρ x ≤ 2 * firstVolumeScale (g i) x (w / (2 * (1 + 2 * Λ₀⁻¹) ^ 3))) →
        ∀ β : ℕ → ℝ, β 2 = β₂ → β 1 < b₀ βE →
        ∀ b' s' : ℝ, b' < 1 / 100000000 → s' < 1 / 100000000 →
        ∃ J : Set (X i), J.Finite ∧
          (∀ j ∈ J, @isEdgePoint.{u, w} (X i) ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j)))
            j Δ βE s) ∧
          J.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3)) ∧
          (∀ a : X i, @isEdgePoint.{u, w} (X i) ((mX i).rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a)))
            a Δ βE s → ∃ j ∈ J, dist a j < Δ * ρ j) ∧
          ∀ p ∈ scaledSplittingStratum.{u, w} ρ hρpos β 1,
          (letI := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p));
            ∀ (A : Type w) [MetricSpace A] (a : A), Bornology.IsBounded (univ : Set A) →
              diam (univ : Set A) < 1000 * Δ →
              ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
          (∃ j ∈ J, dist p j < 2 * Δ * ρ j) ∧
            ∀ q : X i, (@isEdgePoint.{u, w'} (X i) ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q)))
              q Δ b' s') → dist q p < 10 * Δ * ρ p → ∃ j ∈ J, dist q j < 2 * Δ * ρ j := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨a₀, ha₀, hpar⟩ := exists_finite_strong_edge_cover_riemannian.{u, 0, w, w'} (I := I)
    hβ₂ hβ₂small hΔ hs hssmall
  choose! b₀ hb₀ hdata using hpar
  obtain ⟨w₀, hw₀, htail⟩ := exists_kl618_metric_model_tail (I := I) hdim (σ := min a₀ (1 / 2))
    (lt_min ha₀ (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num)) hΛ₀
  refine ⟨a₀, ha₀, b₀, hb₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc X mX _ _ _ g hmetric α hα hstand
  filter_upwards [htail w hw hww hwc X g hmetric α hα hstand] with i hi
  intro βE hβE hβE' Λ ρ hρpos hρ hscale hbounds β hβ2 hβ1 b' s' hb' hs'
  obtain ⟨J, hfin, hJ, hdisj, hcovE, hcov⟩ := hdata βE hβE hβE' (X i) (g i) (hmetric i) Λ ρ hρpos
    hρ hscale β hβ2 hβ1 b' s' hb' hs'
  refine ⟨J, hfin, hJ, hdisj, hcovE, fun p hp hnonslim => hcov p hp hnonslim ?_⟩
  obtain ⟨Y, mY, y, hcY, _, hdimY, hcompY, hsegY, hf⟩ :=
    hi p (ρ p) (hρpos p) (hbounds p).1 (hbounds p).2
  exact ⟨Y, mY, y, min a₀ (1 / 2), hcY, hsegY, hdimY, hcompY, min_le_left _ _, hf⟩

end DifferentialGeometry.Geometry.Collapse
