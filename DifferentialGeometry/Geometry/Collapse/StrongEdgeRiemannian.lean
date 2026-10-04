import DifferentialGeometry.Geometry.Collapse.CompleteRiemannianSegments
import DifferentialGeometry.Geometry.Metric.Approximation.PhysicalStrongEdgeDensity
import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeSelection
import DifferentialGeometry.Geometry.Metric.Approximation.NoTwoSplittingEndpoint
import DifferentialGeometry.Geometry.Metric.Approximation.BoundedFactorRestriction

/-!
# Riemannian bindings of LFR41, LFR42 and LFR44 (strong-edge density and the finite cover)

Blueprint 207A, LFR41 (`lem:collapse-empty-annulus-slim-producer`, A:28455–28494), LFR42
(`lem:collapse-nonslim-endpoint-model`, A:28496–28533) and LFR44
(`thm:collapse-strong-edge-density-cover`, A:28614–28752). The manifold `M` carries a complete metric
space structure whose distance is the length distance of a smooth metric `g` (`hmetric`; this covers
`inducedMetricSpace g` and the standing sequences of LC08–LC09). All geometric hypotheses of the
metric kernels are discharged from `g`:

* minimizing segments of every rescaled distance (`segments_of_riemannianEDistOf_eq`, Hopf–Rinow);
* the rank-one stratum of LC16 (`scaledSplittingStratum ρ hρ β 1`) supplies the actual
  `(1, β 1)`-splitting and the absence of `(2, β 2)`-splittings.

The remaining inputs are those of the rows: the nonslim condition at the ORIGINAL threshold `β 1`
(written out), and, for LFR44, the collapsed-model approximation at quality `≤ a₀` (supplied on a
tail of a standing sequence by LC09, see `StrongEdgeTail.lean`). The disk-packet clause of LFR44
(one smoothing, proper disk bundles, adapted collars) needs LFR33/LFR38 and is not claimed here.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v w w'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LFR41 on a complete Riemannian manifold.** In the distance `c · d_g`, an actual
`(1,b)`-splitting whose factor admits a KL `η`-map to a bounded space of diameter `≤ 500Δ`, with
`900Δ < η⁻¹` (implied by the row's `η < (10⁴Δ)⁻¹`), gives an actual `(1,b)`-splitting with the SAME
`b`, the same first coordinate, the same residual coordinate on the tested ball, and residual factor
`B(x₀, 600Δ)` of diameter `< 1000Δ`. The row's `b < (1000Δ)⁻¹` is not needed. -/
theorem exists_slim_splitting_of_bounded_factor_riemannian
    {M : Type u} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [CompleteSpace M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b))
    {c : ℝ} (hc : 0 < c) {X : Type v} {Y : Type w} [MetricSpace X] [MetricSpace Y]
    {p : M} {x₀ : X} {y₀ : Y} {b η Δ : ℝ}
    (hY : Bornology.IsBounded (univ : Set Y)) (hD : diam (univ : Set Y) ≤ 500 * Δ)
    (hΔ : 1 ≤ Δ) (hη : 900 * Δ < η⁻¹) (G : KleinerLottApprox x₀ y₀ η) :
    letI := m.rescale c hc
    ∀ f : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), x₀)) b,
    ∃ F : KleinerLottApprox p
      (WithLp.toLp 2 ((0 : ℝ), (⟨x₀, mem_ball_self (by linarith)⟩ : ball x₀ (600 * Δ)))) b,
      (∀ z, (F.toFun z).fst = (f.toFun z).fst) ∧
      (∀ z ∈ ball p b⁻¹, ((F.toFun z).snd : X) = (f.toFun z).snd) ∧
      Bornology.IsBounded (univ : Set (ball x₀ (600 * Δ))) ∧
      diam (univ : Set (ball x₀ (600 * Δ))) < 1000 * Δ := by
  have hseg := rescale_segments m hc (segments_of_riemannianEDistOf_eq g hmetric)
  let := m.rescale c hc
  intro f
  exact exists_factor_approximation_of_bounded_target f G
    (fun x y => by
      obtain ⟨γ, _, h0, h1, hd⟩ := hseg x y
      exact ⟨γ, h0, h1, hd⟩) hY hD hΔ hη

/-- LFR41 verbatim (`b < (1000Δ)⁻¹`, `η < (10⁴Δ)⁻¹`): the original slim predicate at quality `b`. -/
example {M : Type u} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [CompleteSpace M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b))
    {c : ℝ} (hc : 0 < c) {X : Type v} {Y : Type w} [MetricSpace X] [MetricSpace Y]
    {p : M} {x₀ : X} {y₀ : Y} {b η Δ : ℝ} (hΔ : 1 ≤ Δ) (_hb : b < 1 / (1000 * Δ))
    (hηpos : 0 < η) (hη : η < 1 / (10000 * Δ)) (G : KleinerLottApprox x₀ y₀ η)
    (hY : Bornology.IsBounded (univ : Set Y)) (hD : diam (univ : Set Y) ≤ 500 * Δ) :
    letI := m.rescale c hc
    ∀ _f : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), x₀)) b,
    ∃ (A : Type v) (_ : MetricSpace A) (a : A), Bornology.IsBounded (univ : Set A) ∧
      diam (univ : Set A) < 1000 * Δ ∧
      Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) b) := by
  have hη' : 900 * Δ < η⁻¹ := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 10000 * Δ)).mp hη
    rw [← one_div]
    exact (lt_div_iff₀ hηpos).mpr (by nlinarith)
  intro f
  obtain ⟨F, _, _, hbd, hdiam⟩ :=
    exists_slim_splitting_of_bounded_factor_riemannian g hmetric hc hY hD hΔ hη' G f
  exact ⟨_, inferInstance, _, hbd, hdiam, ⟨F⟩⟩

/-- **LFR42 at a rank-one point** of a complete Riemannian manifold (LC16 stratum, own scale): an
actual `(1,e)`-splitting onto an LFR39 model with two points `> 500Δ` apart has a nearby endpoint. -/
theorem exists_nearby_endpoint_of_mem_scaledSplittingStratum_one
    {M : Type u} [m : MetricSpace M] {ρ : M → ℝ} {hρ : ∀ x, 0 < ρ x} {β : ℕ → ℝ} {p : M}
    (hp : p ∈ scaledSplittingStratum.{u, w} ρ hρ β 1)
    {Y : Type v} [MetricSpace Y] [CompleteSpace Y] {q : Y} {e Δ : ℝ}
    (F : @KleinerLottApprox M _ (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p
      (WithLp.toLp 2 ((0 : ℝ), q)) e)
    (hβ₂ : 0 < β 2) (hβ₂small : β 2 < 1 / 100) (hΔ : 100 / β 2 < Δ) (he : e < β 2 / 100)
    (hsegments : ∀ a b : Y, ∃ γ : Icc (0 : ℝ) 1 → Y, Continuous γ ∧
      γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (γ s) (γ t) = dist a b * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set Y)) (hdim : dimH (univ : Set Y) ≤ 1)
    (hlarge : ∃ a b : Y, 500 * Δ < dist a b) :
    (∃ C : ℝ, 500 * Δ < C ∧ ∃ f : Y ≃ᵢ Icc (0 : ℝ) C, (f q).val < Δ / 2) ∨
      (∃ f : Y ≃ᵢ Ici (0 : ℝ), (f q).val < Δ / 2) := by
  have hno := (splitting_one_and_no_two_of_mem_scaledSplittingStratum_one hp).2
  let := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))
  exact exists_nearby_endpoint_of_no_two_splitting F hβ₂ hβ₂small hΔ he hno hsegments hcomp hdim
    hlarge

/-- **LFR44, items 1–2, on a complete Riemannian manifold.** The collapsed-model tolerance `a₀` is
chosen from `Δ, β₂, s` only; the rank-one threshold `b₀` also from the strong quality `βE`. At a
point `p` of the LC16 rank-one stratum (with `β 2 = β₂`, `β 1 < b₀`), nonslim at the ORIGINAL
threshold `β 1`, carrying a KL `σ`-map (`σ ≤ a₀`) to a complete geodesic nonnegative model of
dimension `≤ 2` (all in the scale `ρ(p)`): (1) some strong edge `a` (own scale) has
`d(a,p) < Δρ(a)`; (2) every weak edge `q` (own scale, qualities `< 10⁻⁸`) with `d(q,p) < 10Δρ(p)`
has a strong edge `a` with `d(q,a) < ρ(a)`. Distances are the original ones of `g`. -/
theorem exists_strong_edge_density_riemannian
    {Δ β₂ s : ℝ} (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ)
    (hs : 0 < s) (hssmall : s < 1 / 100) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ βE : ℝ, 0 < βE → βE < 1 / 100 → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b)) →
      ∀ (Λ : NNReal) (ρ : M → ℝ) (hρpos : ∀ x, 0 < ρ x), LipschitzWith Λ ρ →
        (Λ : ℝ) < 1 / (1000000 * Δ) →
      ∀ β : ℕ → ℝ, β 2 = β₂ → β 1 < b₀ →
      ∀ p ∈ scaledSplittingStratum.{u, w} ρ hρpos β 1,
      (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p));
        ∀ (A : Type w) [MetricSpace A] (a : A), Bornology.IsBounded (univ : Set A) →
          diam (univ : Set A) < 1000 * Δ →
          ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
      ∀ (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C) (σ : ℝ),
      (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) → σ ≤ a₀ →
      (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p));
        Nonempty (KleinerLottApprox p c σ)) →
      (∃ a : M, (@isEdgePoint.{u, w} M
          (m.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist a p < Δ * ρ a) ∧
        ∀ (b' s' : ℝ) (q : M), b' < 1 / 100000000 → s' < 1 / 100000000 →
          (@isEdgePoint.{u, w'} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q Δ b' s') →
          dist q p < 10 * Δ * ρ p →
          ∃ a : M, (@isEdgePoint.{u, w} M
            (m.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist q a < ρ a := by
  obtain ⟨a₀, ha₀, hpar⟩ := exists_strong_edge_density_parameters.{u, v, w, w'}
    hβ₂ hβ₂small hΔ hs hssmall
  refine ⟨a₀, ha₀, fun βE hβE hβE' => ?_⟩
  obtain ⟨b₀, hb₀, hdata⟩ := hpar βE hβE hβE'
  refine ⟨b₀, hb₀, ?_⟩
  intro M m _ _ _ _ g hmetric Λ ρ hρpos hρ hscale β hβ2 hβ1 p hp hnonslim C _ _ c σ hCseg hdim
    hcomp hσ hmodel
  obtain ⟨hone, hno⟩ := splitting_one_and_no_two_of_mem_scaledSplittingStratum_one hp
  have hseg := rescale_segments m (inv_pos.mpr (hρpos p)) (segments_of_riemannianEDistOf_eq g hmetric)
  let := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
  obtain ⟨Z, mZ, z, ⟨F⟩⟩ := hasEuclideanSplitting_one_iff.mp hone
  obtain ⟨f⟩ := hmodel
  have hnoplane : ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β₂) := by
    rintro ⟨P⟩
    exact hno (hβ2 ▸ hasEuclideanSplitting_two_of_plane_approximation.{u, w} P)
  exact hdata M m p Λ ρ hρpos hρ hscale C c
    (Metric.arbitrarily_short_curves_of_metric_segments hCseg) hdim hcomp Z z σ (β 1) hσ hβ1
    f F (fun x y => by
      obtain ⟨γ, _, h0, h1, hd⟩ := hseg x y
      exact ⟨γ, h0, h1, hd⟩) hnoplane hnonslim

/-- **LFR44, finite cover, on a closed Riemannian manifold.** Same parameter order as
`exists_strong_edge_density_riemannian`; the family is chosen AFTER all tolerances. A finite set `I`
of strong edges (own scale) with pairwise disjoint `B(q_i, Δρ(q_i)/3)` such that `B(q_i, 2Δρ(q_i))`
cover every model-carrying nonslim rank-one point and every weak edge (qualities `b', s' < 10⁻⁸`)
within `10Δρ(p)` of such a point (the blueprint's radius `3Δρ(q_i)`, with its remarked constant
`2`), and `B(q_i, Δρ(q_i))` cover all strong edges. -/
theorem exists_finite_strong_edge_cover_riemannian
    {Δ β₂ s : ℝ} (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ)
    (hs : 0 < s) (hssmall : s < 1 / 100) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ βE : ℝ, 0 < βE → βE < 1 / 100 → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompactSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b)) →
      ∀ (Λ : NNReal) (ρ : M → ℝ) (hρpos : ∀ x, 0 < ρ x), LipschitzWith Λ ρ →
        (Λ : ℝ) < 1 / (1000000 * Δ) →
      ∀ β : ℕ → ℝ, β 2 = β₂ → β 1 < b₀ →
      ∀ b' s' : ℝ, b' < 1 / 100000000 → s' < 1 / 100000000 →
      ∃ J : Set M, J.Finite ∧
        (∀ i ∈ J, @isEdgePoint.{u, w} M (m.rescale (ρ i)⁻¹ (inv_pos.mpr (hρpos i))) i Δ βE s) ∧
        J.PairwiseDisjoint (fun i => ball i (Δ * ρ i / 3)) ∧
        (∀ a : M, @isEdgePoint.{u, w} M (m.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s →
          ∃ i ∈ J, dist a i < Δ * ρ i) ∧
        ∀ p ∈ scaledSplittingStratum.{u, w} ρ hρpos β 1,
        (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p));
          ∀ (A : Type w) [MetricSpace A] (a : A), Bornology.IsBounded (univ : Set A) →
            diam (univ : Set A) < 1000 * Δ →
            ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
        (∃ (C : Type v) (mC : MetricSpace C) (c : C) (σ : ℝ), letI := mC;
          CompleteSpace C ∧
          (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
            f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
            ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
          dimH (univ : Set C) ≤ 2 ∧ fourPointComparison 0 (univ : Set C) ∧ σ ≤ a₀ ∧
          Nonempty (@KleinerLottApprox M C (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ)) →
        (∃ i ∈ J, dist p i < 2 * Δ * ρ i) ∧
          ∀ q : M, (@isEdgePoint.{u, w'} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q Δ b' s') →
            dist q p < 10 * Δ * ρ p → ∃ i ∈ J, dist q i < 2 * Δ * ρ i := by
  obtain ⟨a₀, ha₀, hpar⟩ := exists_strong_edge_density_riemannian.{u, v, w, w'} (I := I)
    hβ₂ hβ₂small hΔ hs hssmall
  refine ⟨a₀, ha₀, fun βE hβE hβE' => ?_⟩
  obtain ⟨b₀, hb₀, hdata⟩ := hpar βE hβE hβE'
  refine ⟨b₀, hb₀, ?_⟩
  intro M m _ _ _ _ g hmetric Λ ρ hρpos hρ hscale β hβ2 hβ1 b' s' hb' hs'
  have hΔone : 1 ≤ Δ := by
    have hh : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hΔpos : 0 < Δ := by linarith
  have hsmall : (Λ : ℝ) * Δ ≤ 1 / 100 := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 1000000 * Δ)).mp hscale
    nlinarith
  let E : Set M := {a | @isEdgePoint.{u, w} M (m.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s}
  let N : Set M := {p | p ∈ scaledSplittingStratum.{u, w} ρ hρpos β 1 ∧
    (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p));
      ∀ (A : Type w) [MetricSpace A] (a : A), Bornology.IsBounded (univ : Set A) →
        diam (univ : Set A) < 1000 * Δ →
        ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) ∧
    (∃ (C : Type v) (mC : MetricSpace C) (c : C) (σ : ℝ), letI := mC;
      CompleteSpace C ∧
      (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      dimH (univ : Set C) ≤ 2 ∧ fourPointComparison 0 (univ : Set C) ∧ σ ≤ a₀ ∧
      Nonempty (@KleinerLottApprox M C (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ))}
  let W : Set M := {q | @isEdgePoint.{u, w'} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q Δ b' s' ∧
    ∃ p ∈ N, dist q p < 10 * Δ * ρ p}
  obtain ⟨J, hJE, hfin, hdisj, hcov, hcovE⟩ :=
    exists_finite_strong_edge_selection (E := E) (N := N) (W := W) hρ hρpos hΔone hsmall
      (fun p hp => by
        obtain ⟨hstr, hnonslim, C, mC, c, σ, hcC, hCseg, hdim, hcomp, hσ, hmodel⟩ := hp
        obtain ⟨a, ha, hd⟩ := (hdata M g hmetric Λ ρ hρpos hρ hscale β hβ2 hβ1 p hstr hnonslim
          C c σ hCseg hdim hcomp hσ hmodel).1
        exact ⟨a, ha, by rwa [dist_comm]⟩)
      (fun q hq => by
        obtain ⟨hwq, p, ⟨hstr, hnonslim, C, mC, c, σ, hcC, hCseg, hdim, hcomp, hσ, hmodel⟩, hqp⟩ := hq
        exact (hdata M g hmetric Λ ρ hρpos hρ hscale β hβ2 hβ1 p hstr hnonslim
          C c σ hCseg hdim hcomp hσ hmodel).2 b' s' q hb' hs' hwq hqp)
  refine ⟨J, hfin, fun i hi => hJE hi, hdisj, fun a ha => hcovE a ha, ?_⟩
  intro p hstr hnonslim hmodel
  have hp : p ∈ N := ⟨hstr, hnonslim, hmodel⟩
  exact ⟨hcov p (Or.inl hp), fun q hq hqp => hcov q (Or.inr ⟨hq, p, hp, hqp⟩)⟩

end DifferentialGeometry.Geometry.Collapse
