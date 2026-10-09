import DifferentialGeometry.Geometry.Collapse.SimultaneousLocalCoverSkeleton
import DifferentialGeometry.Geometry.Collapse.StrongEdgeFullCollarCover

/-!
# The edge bracket of LPA04/LPA06 on the shared tail: one smoothing, disk domains, full collars

Blueprint `master207A.tex`, LPA04 (A:30447: "every strong edge point has LFR28's disk packet and
LFR38's full collar"; A:30535–30542: "For any later finite strong-edge family, LFR33/LFR38 use ONE
smoothing … The same smoothing gives all its disk bundles, cutoffs and full lower collars") and
LPA06 (A:30610–30612: "LFR33/LFR38 supply its one shared smoothing after that finite family is
fixed, as in LPA04").

* `exists_edge_collars_of_aligned_family`: F7-EDGE's `exists_strong_edge_full_collar_cover`
  (LFR44's last clause) for a compact manifold with an aligned metric (the standing convention,
  no Riemannian-bundle instance assumed), a finite SET of strong edges (possibly empty) and the
  two curvature hypotheses at the centres.
* `eventually_simultaneous_local_cover_with_edge_collars`: `eventually_simultaneous_local_cover`
  with, on the SAME tail and scale and for the SAME strong-edge family `Je`, ONE smoothing `F` of
  the distance to the closed weak edge set, and at every centre the actual splitting, the
  normalized strip chart, the edge disk domain containing `B(p, 3Δ)` with cutoff one, and the full
  LFR38 collar of `(f, F/ρ)` for every LFR19-type `f`. The curvature at the centres is LPA01's
  all-radius clause at the fixed radii `(10⁴Δ + κ₀⁻¹)ρ` and `b⁻¹ρ`; the collar constants
  (`βc, γc → σ₀, Δ₀ → Δ → τ₀, κ₀, bc₀ → ε, τ → b′, s′ → s → b < bc₀`) precede LFR44's `b₀`, `β`,
  `σ`, `Λ`, `w` and the tail.

The proper smooth disk BUNDLES of LFR28 are not supplied (LFR28 is blocked).
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
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LFR44's collars on an aligned closed manifold.** F7-EDGE's
`exists_strong_edge_full_collar_cover` in the standing convention: a compact manifold with an
aligned metric, a finite set `Je` of strong edges (possibly empty), the curvature hypotheses at the
centres with the theorem's `κ₀` and the strong tolerance `b`. -/
theorem exists_edge_collars_of_aligned_family {βc γc : ℝ} (hβc : 0 < βc)
    (hβγ : βc < γc / 1000) (hγc : 0 < γc) (hγc1 : γc < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ → 1 ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σc ε μ τ b s b' s' Λ : ℝ), 0 ≤ σc → σc ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 < b → b < b₀ → 100 * Δ < b⁻¹ → 0 ≤ Λ → 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < 1 / (1000000 * Δ) → Λ < s' / (100000000 * Δ ^ 2) →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 →
        s < b' / 100000 → s < s' / 100000 → b < s / 100000 →
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M)
        (hmetric : ∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b))
        (ρ : M → ℝ) (hρpos : ∀ x, 0 < ρ x) (Je : Set M), Je.Finite →
      (∀ p ∈ Je, @isEdgePoint.{u, 0} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p Δ b s) →
      (∀ p ∈ Je, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ₀ / ρ p) ^ 2)) →
      (∀ p ∈ Je, ∀ z ∈ ball p (b⁻¹ * ρ p), SectionalBoundedBelowAt g z (-(b / ρ p) ^ 2)) →
      LipschitzWith (Real.toNNReal Λ) ρ → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      let A : Set M := closure
        {x | @isEdgePoint.{u, 0} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
      ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        ∀ p ∈ Je, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
          ∃ (q : Y) (Fp : @KleinerLottApprox M (WithLp 2 (ℝ × Y))
              (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), q)) b)
            (Qn : M → WithLp 2 (ℝ × ℝ)),
          (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            ∀ z, (Qn z).fst = (Fp.toFun z).fst) ∧
          (let hMc : CompleteSpace M := complete_of_compact
          letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
            radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : IsRiemannianManifold I M :=
            radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          letI : CompleteSpace M :=
            (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hMc
          let gR : SmoothRiemannianMetric I M :=
            scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
          have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
          ∀ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
          LipschitzWith (Real.toNNReal (1 + σc)) f →
          (∀ x ∈ ball p (100 * Δ), |f x - (Fp.toFun x).fst| ≤ μ * Δ) →
          (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
            ∀ w : TangentSpace I x, gR.inner x w w = 1 →
            intrinsicGeodesic gR hnR x w (dist x x') = x' →
            |mvfderiv (I := I) f x w - ((Fp.toFun x').fst - (Fp.toFun x).fst) / dist x x'| < σc) →
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
              ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) βc,
                ∀ y, Φ.toFun y = @planeComparisonMap M
                  (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) Qn p x Δ (ρ x / ρ p) y) ∧
            let Jc := edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)]
            ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ Jc (ball x (300 * (ρ x / ρ p))) ∧
            (∀ y ∈ ball x (100 * (ρ x / ρ p)), Function.Surjective (mvfderiv (I := I) Jc y)) ∧
            (∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p)),
              ‖Jc y - Jc z‖ ≤ (1 + γc) * (dist y z / (ρ x / ρ p))) ∧
            (∀ y ∈ ball x (100 * (ρ x / ρ p)), infDist (Jc y) (ball (Jc x) 100) < 100 * γc) ∧
            (∀ v ∈ ball (Jc x) 100, ∃ y ∈ ball x (100 * (ρ x / ρ p)), ‖Jc y - v‖ < 100 * γc) ∧
            ∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p) / γc),
              ρ x / ρ p < dist y z →
              ∀ W : TangentSpace I y, gR.inner y W W = 1 →
              intrinsicGeodesic gR hnR y W (dist y z) = z →
              ‖(ρ x / ρ p) • mvfderiv (I := I) Jc y W - (dist y z / (ρ x / ρ p))⁻¹ •
                (planeReferenceIsometry (planeComparisonMap Qn p x Δ (ρ x / ρ p) z) -
                  planeReferenceIsometry (planeComparisonMap Qn p x Δ (ρ x / ρ p) y))‖ < γc) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ :=
    exists_strong_edge_full_collar_cover hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ hΔ1 => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, h⟩ := h Δ hΔ hΔ1
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σc ε μ τ b s b' s' Λ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hb hbb₀ hsource hΛ hlam
    hbudget hscale hend hb'd hs'd hb'e hs'e hsb' hss' hbs M m _ _ _ g hmetric ρ hρpos Je hfin hJE
    hsecκ hsecb hρ hρs A
  have hb100 : b < 1 / 100 := by
    have h1 : 100 < b⁻¹ := by nlinarith
    have h2 := (lt_inv_comm₀ (by norm_num) hb).mp h1
    linarith
  rcases Je.eq_empty_or_nonempty with hJe | hJne
  · refine ⟨fun _ => 0, fun _ => le_rfl, (LipschitzWith.const (0 : ℝ)).weaken bot_le,
      fun p hp => ?_⟩
    rw [hJe] at hp
    exact absurd hp (notMem_empty p)
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric g
  have : IsRiemannianManifold I M := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := I) g := isMetricNorm_of_riemannianBundle g
  have : CompleteSpace M := complete_of_compact
  have hΛ' : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  obtain ⟨F, hF0, hFL, hF⟩ := h σc ε μ τ κ₀ b s b' s' (Real.toNNReal Λ) hσc hσcσ₀ hε hε1 hμ
    hμ1 hτ hττ₀ hθ hκ₀.le le_rfl hb hbb₀ hb100 hsource (by rw [hΛ']; exact hlam)
    (by rw [hΛ']; exact hbudget) (by rw [hΛ']; exact hscale) (by rw [hΛ']; exact hend) hb'd
    hs'd hb'e hs'e hsb' hss' hbs E H I M g hEnorm ρ hρpos hfin.toFinset
    (by rw [Set.Finite.toFinset_nonempty]; exact hJne)
    (fun p hp => hJE p (hfin.mem_toFinset.mp hp)) (fun p hp => hsecκ p (hfin.mem_toFinset.mp hp))
    (fun p hp => hsecb p (hfin.mem_toFinset.mp hp)) hρ hρs
  exact ⟨F, hF0, hFL, fun p hp => hF p (hfin.mem_toFinset.mpr hp)⟩


/-- **The edge bracket on LPA04's tail.** See the module docstring. -/
theorem eventually_simultaneous_local_cover_with_edge_collars (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 ≤ σc → σc ≤ σ₀ → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εz δ' Λ' : ℝ, 0 < εz ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ T V : ℝ, ∀ hT : 0 < T, 20 * Λ' ≤ T → T ≤ V →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ ∧
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        (∀ L : ℝ, 0 < L → 2 * L < α i → ∀ (p : X i), ∀ y ∈ ball p (L * ρ p),
          SectionalBoundedBelowAt (g i) y (-((L * ρ p) ^ 2)⁻¹)) ∧
        (∀ s : ℝ, 0 < s → 800 * s < α i → ∀ (p : X i), ∀ y ∈ ball p (400 * (s * ρ p)),
          SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * ρ p)⁻¹ ^ 2))) ∧
        (∀ p : X i, ∃ (C : Type) (mC : MetricSpace C), letI := mC
          ∃ c : C, CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
            fourPointComparison 0 (univ : Set C) ∧
            (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
              f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
            Nonempty (@KleinerLottApprox (X i) C
              ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ)) ∧
        (∀ p : X i, scaledSplittingRank.{u, 0} ρ hρpos β p ≤ 2) ∧
        (∀ p : X i, p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 0 ∨
          p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1 ∨
          p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2) ∧
        (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2,
          ∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
          CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
          fourPointComparison 0 (univ : Set C) ∧
          Nonempty (@KleinerLottApprox (X i) C
            ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ) ∧
          ∃ (Y : Type) (mY : MetricSpace Y) (a : Y), letI := mY
            ∃ F : @KleinerLottApprox (X i) _ ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _
              p (WithLp.toLp 2 ((0 : ℝ²), a)) (β 2),
            let hmet := hmetric i
            let hMc : CompleteSpace (X i) := complete_of_compact
            letI := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := ((mX i).rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hMc
            letI := radialScaledBundle (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := radialScaledContinuous (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := radialScaledManifold (m := mX i) (g i) hmet (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            ∃ η : X i → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball p 200),
            ∃ hrank : ∀ x ∈ ball p 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
              η p = 0 ∧ LipschitzOnWith 2 η (ball p 200) ∧
              (∀ x ∈ ball p 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
              (∀ x ∈ ball p 200, ‖η x‖ < 100 → x ∈ ball p 102) ∧
              (∀ x ∈ ball p 200, η x = 0 → x ∈ ball p 2) ∧
              (∀ x ∈ ball p 2, ‖η x‖ ≤ 8) ∧
              (let f := diskPreimageMap (ball p 200) isOpen_ball η hη.continuousOn 100
              ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
                (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
                (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
                ∀ R (hR : 0 < R) (hRr : R < 100),
                  let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
                  letI := regularFiberChartedSpace f y₀
                    (contMDiff_diskPreimageMap isOpen_ball hη 100)
                    (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
                  let U : TopologicalSpace.Opens
                      (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100) :=
                    ⟨f ⁻¹' planeBallInner 100 R,
                      (planeBallInner 100 R).isOpen.preimage
                        (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
                  ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                      (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                      ({x // f x = y₀} × planeBallInner 100 R) U ∞),
                    (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
              (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
                let f := diskPreimageMap (ball p 200) isOpen_ball η hη.continuousOn 100
                letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
                  (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
                Nonempty (Circle ≃ₘ⟮𝓡 1,
                  𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
              ∃ ζ : X i → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
                (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball p 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
                (∀ x, ζ x ≠ 0 → x ∈ ball p 200 ∧ ‖η x‖ < 9) ∧
                tsupport ζ ⊆ {x | x ∈ ball p 200 ∧ ‖η x‖ ≤ 9} ∧
                tsupport ζ ⊆
                  (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100 : Set (X i)) ∧
                @ball (X i) (mX i).toPseudoMetricSpace p (2 * ρ p) ⊆
                  (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100 : Set (X i)) ∩
                    {x | ζ x = 1} ∧
                tsupport ζ ⊆ @ball (X i) (mX i).toPseudoMetricSpace p (200 * ρ p)) ∧
        ∃ J : Set (X i), J.Finite ∧ J ⊆ scaledSplittingStratum.{u, 0} ρ hρpos β 2 ∧
          J.PairwiseDisjoint (fun p => ball p (ρ p / 3)) ∧
          (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2, ∃ j ∈ J,
            ball p (ρ p) ⊆ ball j (2 * ρ j)) ∧
          (∀ x : X i, ((J ∩ {j | x ∈ ball j (2000000 * ρ j)}).ncard : ℝ) ≤
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) ∧
          ∃ Js Je : Set (X i),
            Js.Finite ∧
            Js ⊆ {p | p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1 ∧
              (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
                Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
                Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
                  ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                  (WithLp.toLp 2 ((0 : ℝ), a)) (β 1)))} ∧
            Js.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3)) ∧
            (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1,
              (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
                Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
                Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
                  ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                  (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
              ∃ j ∈ Js, ball p (Δ * ρ p) ⊆ ball j (2 * (Δ * ρ j))) ∧
            (∀ x : X i, ((Js ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
                modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) ∧
            Je.Finite ∧
            (∀ j ∈ Je, @isEdgePoint.{u, 0} (X i)
              ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) j Δ b s) ∧
            Je.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3)) ∧
            (∀ a : X i, @isEdgePoint.{u, 0} (X i)
              ((mX i).rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ b s →
              ∃ j ∈ Je, dist a j < Δ * ρ j) ∧
            (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1,
              ¬ (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
                  Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
                  Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
                    ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                    (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
              ∃ j ∈ Je, dist p j < 2 * Δ * ρ j) ∧
            (∀ x : X i, ((Je ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
              modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
                  (4 * (1 + 2 * 2000000 + 1 / 3)) /
                modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3)) ∧
            (let A : Set (X i) := closure
              {x | @isEdgePoint.{u, 0} (X i) ((mX i).rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x)))
                x Δ b' s'}
            ∃ F : (X i) → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
              ∀ p ∈ Je, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
              ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
                ∃ (q : Y) (Fp : @KleinerLottApprox (X i) (WithLp 2 (ℝ × Y))
                    ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                    (WithLp.toLp 2 ((0 : ℝ), q)) b)
                  (Qn : (X i) → WithLp 2 (ℝ × ℝ)),
                (letI := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
                  ∀ z, (Qn z).fst = (Fp.toFun z).fst) ∧
                (let hMc : CompleteSpace (X i) := complete_of_compact
                letI := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
                letI := radialScaledBundle (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
                letI : IsContinuousRiemannianBundle E (fun x : (X i) => TangentSpace I x) :=
                  radialScaledContinuous (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
                letI : IsRiemannianManifold I (X i) :=
                  radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
                letI : CompleteSpace (X i) :=
                  ((mX i).rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hMc
                let gR : SmoothRiemannianMetric I (X i) :=
                  scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) (g i)
                have hnR : IsMetricNorm (I := I) (M := X i) gR :=
                  isMetricNorm_of_riemannianBundle gR
                ∀ f : (X i) → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
                LipschitzWith (Real.toNNReal (1 + σc)) f →
                (∀ x ∈ ball p (100 * Δ), |f x - (Fp.toFun x).fst| ≤ μ * Δ) →
                (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
                  ∀ w : TangentSpace I x, gR.inner x w w = 1 →
                  intrinsicGeodesic gR hnR x w (dist x x') = x' →
                  |mvfderiv (I := I) f x w -
                    ((Fp.toFun x').fst - (Fp.toFun x).fst) / dist x x'| < σc) →
                (ball p (3 * Δ) ⊆ edgeDiskDomain p Δ (fun x => f x.val)
                    (fun x => F x / ρ p) (fun x => ρ x / ρ p) ∧
                  EqOn ((Subtype.val : ball p (100 * Δ) → (X i)).extend
                    (fun x => edgeCoordinateProfile (f x.val / Δ) *
                      edgeHeightProfile (F x.val / ρ p / (Δ * (ρ x.val / ρ p)))) 0) 1
                    (ball p (3 * Δ))) ∧
                ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
                  Δ / 10 ≤ F x / ρ p / (ρ x / ρ p) → F x / ρ p / (ρ x / ρ p) ≤ 10 * Δ →
                ∃ hq : 99 / 100 ≤ ρ x / ρ p ∧ ρ x / ρ p ≤ 101 / 100,
                  (letI := ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).rescale (ρ x / ρ p)⁻¹
                    (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq.1));
                    ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) βc,
                      ∀ y, Φ.toFun y = @planeComparisonMap (X i)
                        ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) Qn p x Δ (ρ x / ρ p) y) ∧
                  let Jc := edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)]
                  ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ Jc (ball x (300 * (ρ x / ρ p))) ∧
                  (∀ y ∈ ball x (100 * (ρ x / ρ p)), Function.Surjective (mvfderiv (I := I) Jc y)) ∧
                  (∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p)),
                    ‖Jc y - Jc z‖ ≤ (1 + γc) * (dist y z / (ρ x / ρ p))) ∧
                  (∀ y ∈ ball x (100 * (ρ x / ρ p)), infDist (Jc y) (ball (Jc x) 100) < 100 * γc) ∧
                  (∀ v ∈ ball (Jc x) 100, ∃ y ∈ ball x (100 * (ρ x / ρ p)), ‖Jc y - v‖ < 100 * γc) ∧
                  ∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p) / γc),
                    ρ x / ρ p < dist y z →
                    ∀ W : TangentSpace I y, gR.inner y W W = 1 →
                    intrinsicGeodesic gR hnR y W (dist y z) = z →
                    ‖(ρ x / ρ p) • mvfderiv (I := I) Jc y W - (dist y z / (ρ x / ρ p))⁻¹ •
                      (planeReferenceIsometry (planeComparisonMap Qn p x Δ (ρ x / ρ p) z) -
                        planeReferenceIsometry
                          (planeComparisonMap Qn p x Δ (ρ x / ρ p) y))‖ < γc)) ∧
            (∀ x : X i, x ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 0 ∨
              (∃ j ∈ J, x ∈ ball j (2 * ρ j)) ∨ (∃ j ∈ Js, x ∈ ball j (2 * (Δ * ρ j))) ∨
              ∃ j ∈ Je, dist x j < 2 * Δ * ρ j) ∧
            ∀ r : X i → ℝ, ∀ hlower : ∀ p, T * ρ p ≤ r p, (∀ p, r p ≤ V * ρ p) →
            ∀ (N C : X i → Type v) [mN : ∀ j, MetricSpace (N j)] [∀ j, ProperSpace (N j)]
              [mC : ∀ j, MetricSpace (C j)] [∀ j, ProperSpace (C j)]
              (n₀ : ∀ j, N j) (o : ∀ j, C j), (∀ j, RadialConeData (o j)) →
            ∀ (δ : X i → ℝ) (η : X i → X i → ℝ) (O : X i → Set (X i)) {e : ℝ}, e < 1 / 40 →
            ∃ J₀ : Set (X i), J₀.Finite ∧ J₀.PairwiseDisjoint (fun j => ball j (r j)) ∧
              ((∀ j ∈ J₀,
              fourPointComparison 0 (univ : Set (N j)) ∧
              (∀ x y : N j, ∃ f : Icc (0 : ℝ) 1 → N j,
                Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
                ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
              (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
                R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N j) (C j)
                  ((mN j).rescale R⁻¹ (inv_pos.mpr hR)) (mC j) (n₀ j) (o j) δ₁)) ∧
              δ j < δ' ∧
              Nonempty (@KleinerLottApprox (X i) (C j)
                ((mX i).rescale (r j)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos j)).trans_le (hlower j))))
                (mC j) j (o j) (δ j)) ∧
              ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η j)
                {x | 3 / 40 ≤ (r j)⁻¹ * dist x j ∧ (r j)⁻¹ * dist x j ≤ 11} ∧
              (∀ x y, |(η j x - (r j)⁻¹ * dist j x) - (η j y - (r j)⁻¹ * dist j y)| ≤
                εz * ((r j)⁻¹ * dist x y)) ∧
              Continuous (η j) ∧ IsOpen (O j) ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η j) (O j) ∧
              η j ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ O j ∧
              (∀ x, |η j x - (r j)⁻¹ * dist x j| < e) ∧
              ∀ q ∈ η j ⁻¹' Icc (1 / 5 : ℝ) (9 / 10),
                Real.sqrt ((scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)).inner q
                  (gradFun (scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                    ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)) (η j) q)
                  (gradFun (scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                    ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)) (η j) q)) ≤ 1 + εz) →
                scaledSplittingStratum.{u, 0} ρ hρpos β 0 ⊆ ⋃ j ∈ J₀, ball j (r j / 10) ∧
                ∃ L : ℝ, 0 ≤ L ∧
              (∀ j ∈ J₀,
                let ζi : X i → ℝ := fun x => annularCutoff cutoffProfile (η j x)
                let gr := scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)
                ContMDiff I 𝓘(ℝ, ℝ) ∞ ζi ∧ (∀ x, ζi x ∈ Icc (0 : ℝ) 1) ∧
                (∀ x, η j x ∈ Icc (3 / 10 : ℝ) (4 / 5) → ζi x = 1) ∧
                tsupport ζi ⊆
                  {x | (1 / 5 - e) * r j < dist x j ∧ dist x j < (9 / 10 + e) * r j} ∧
                tsupport ζi ⊆ ball j (r j) ∧ HasCompactSupport ζi ∧
                (∀ q, Real.sqrt (gr.inner q (gradFun gr ζi q) (gradFun gr ζi q)) ≤ L * (1 + εz)) ∧
                ball j (r j / 10) ⊆ {x | η j x < 1 / 5}) ∧
            J₀.PairwiseDisjoint fun j =>
              tsupport fun x => annularCutoff cutoffProfile (η j x)) := by
  obtain ⟨a₂, ha₂, hG3⟩ :=
    eventually_simultaneous_local_cover.{uE, uH, u, v} (E := E) (H := H) (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hG3⟩ := hG3 γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hC⟩ :=
    exists_edge_collars_of_aligned_family.{uE, uH, u} (E := E) (H := H) (I := I) hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, bc₀, hbc₀, hC⟩ := hC Δ hΔ₀Δ hΔ1
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs hssmall
    hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, ha₀, hG3⟩ := hG3 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ s hs hssmall
  refine ⟨a₀, ha₀, fun b hb hbs hbc hsource => ?_⟩
  have hbsmall : b < 1 / 100 := by
    have h1 : 100 < b⁻¹ := by nlinarith
    have h2 := (lt_inv_comm₀ (by norm_num) hb).mp h1
    linarith
  obtain ⟨b₀, hb₀, hG3⟩ := hG3 b hb hbsmall
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨εz, δ', Λ', hεz, hδ', hΛ', hG3⟩ := hG3 β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  refine ⟨εz, δ', Λ', hεz, hδ', hΛ', fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  obtain ⟨w₀, hw₀, hG3⟩ := hG3 σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44
  refine ⟨w₀, hw₀, fun w hw hww hwc T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [hG3 w hw hww hwc T V hT hTΛ hTV X g hmetric α hα hstand,
    hα.eventually_gt_atTop (2 * (10000 * Δ + κ₀⁻¹)), hα.eventually_gt_atTop (2 * b⁻¹)]
    with i hi hακ hαb
  obtain ⟨ρ, hρpos, hρsm, hρlip, hρb, hsecL, hzero, hmod, hrank, htri, hcirc, J, hJfin, hJS,
    hJdisj, hJcov, hJmult, Js, Je, hJsfin, hJsS, hJsdisj, hJscov, hJsmult, hJefin, hJeE, hJedisj,
    hJecovE, hns, hJemult, hcov, hzeroFam⟩ := hi
  have hsecκ : ∀ p ∈ Je, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
      SectionalBoundedBelowAt (g i) z (-(κ₀ / ρ p) ^ 2) := by
    intro p _ z hz
    have hρp := hρpos p
    have hL : 0 < 10000 * Δ + κ₀⁻¹ := by positivity
    have hz' : z ∈ ball p ((10000 * Δ + κ₀⁻¹) * ρ p) := by
      refine ball_subset_ball ?_ hz
      rw [add_mul, mul_assoc]
      linarith [mul_pos (inv_pos.mpr hκ₀) hρp]
    refine (hsecL _ hL hακ p z hz').mono ?_
    rw [neg_le_neg_iff]
    have hκρ : (κ₀ / ρ p) ^ 2 = ((ρ p / κ₀) ^ 2)⁻¹ := by rw [← inv_pow, inv_div]
    rw [hκρ]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (by linarith [inv_pos.mpr hκ₀]) hρp.le
  have hsecb : ∀ p ∈ Je, ∀ z ∈ ball p (b⁻¹ * ρ p),
      SectionalBoundedBelowAt (g i) z (-(b / ρ p) ^ 2) := by
    intro p _ z hz
    have h := hsecL b⁻¹ (inv_pos.mpr hb) hαb p z hz
    have he : -((b⁻¹ * ρ p) ^ 2)⁻¹ = -(b / ρ p) ^ 2 := by
      rw [mul_pow, mul_inv, inv_pow, inv_inv, div_pow, div_eq_mul_inv, ← inv_pow]
    rwa [he] at h
  refine ⟨ρ, hρpos, hρsm, hρlip, hρb, hsecL, hzero, hmod, hrank, htri, hcirc, J, hJfin, hJS,
    hJdisj, hJcov, hJmult, Js, Je, hJsfin, hJsS, hJsdisj, hJscov, hJsmult, hJefin, hJeE, hJedisj,
    hJecovE, hns, hJemult, ?_, hcov, hzeroFam⟩
  exact hC σc ε μ τ b s b' s' Λ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hb hbc hsource hΛ.le hlam
    hbudget hΛ44 hend hb'd hs'd hb'e hs'e hsb' hss' hbs (X i) (g i) (hmetric i) ρ hρpos Je hJefin
    hJeE hsecκ hsecb hρlip hρsm


end DifferentialGeometry.Geometry.Collapse
