import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacket

/-!
# LC87 G10: the final combined family with LC84 edge disk packets

Blueprint 207A, LC87 (local-collapse export certificate) with LC84 (`def:collapse-edge-packet`,
A:30874) at every edge centre, and LFR33 / LFR44 (the SAME strong-edge family carries ONE distance
smoothing and the proper disk bundles).

* `LocalChartPacketsD`: `LocalChartPackets` (G9) together with, at every edge centre, an
  `EdgeDiskPacket` whose underlying `EdgeChart` is the family's own chart (`P.toEdgeChart = c`).
* `normalized_volume_and_derivatives_LC87`: LPA01's normalized analytic data at a point (volume of
  the normalized unit ball, curvature-derivative bounds) in the form of LFR28's threshold
  hypotheses (`ρ(p)⁻² g`, `R < b⁻¹` from `2 b⁻¹ + 2 < a`).
* `edgeDiskFamily_on_tail_LC87`: the edge block of the G10 producer on one tail member: the
  kernel `exists_edgeDiskPackets_of_strong_edge_family` (after `b`, taken as the hypothesis `hE`)
  applied to the tail's finite strong-edge set (empty set handled separately).
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

/-- **The final family with an LC84 `EdgeDiskPacket` over EVERY edge chart of the family**
(LC87 G10): a `LocalChartPackets` whose edge chart at every edge centre `j` (normalized at `j`,
with the family's ONE shared smoothing `Fs`) is the `EdgeChart` of an LC84 `EdgeDiskPacket` for
the closed weak edge set `A` and the scale `ρ/ρ(j)`. -/
structure LocalChartPacketsD (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ)
    extends LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    where
  edgeDisk : ∀ j (hj : j ∈ edge.centres),
    let c := edge.chart j hj
    let Fs := edge.smoothing
    let A : Set X := closure
      {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    ∃ P : EdgeDiskPacket gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ j)
        (fun x => Fs x / ρ j), P.toEdgeChart = c

/-- LPA01's normalized analytic data at a point in the form of LFR28's threshold hypotheses. -/
theorem normalized_volume_and_derivatives_LC87 {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    [RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ, E3) x)] [IsRiemannianManifold 𝓘(ℝ, E3) X]
    [IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x)]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) g) {p : X} {r v a b : ℝ} (hr : 0 < r) {K : ℕ}
    (Acurv : ℝ → ℝ) (hab : 2 * b⁻¹ + 2 < a)
    (hvol0 : v ≤ (ballVolume (normalizedCenterMetric g r hr) p 1).toReal)
    (hder0 : ∀ R, 0 < R → 2 * R + 2 < a → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g r hr) k y ≤ Acurv R) :
    have hmetric' := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := mX.rescale r⁻¹ (inv_pos.mpr hr)
    letI := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric' r⁻¹ (inv_pos.mpr hr)
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X := scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
    ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) X gR (ball p 1) ∧
      ∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k gR y ≤ Acurv R := by
  intro hmetric'
  let mR : MetricSpace X := mX.rescale r⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric' r⁻¹ (inv_pos.mpr hr)
  intro gR
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hmeq : normalizedCenterMetric g r hr = gR := by
    have key : ∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d), c = d →
        scaleMetric c hc g = scaleMetric d hd g := by
      rintro c d hc hd rfl
      rfl
    exact key _ _ _ _ (inv_pow r 2).symm
  have hball : ∀ ρ', riemannianBallOf gR p ρ' = ball p ρ' := fun ρ' =>
    DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm gR hnR p ρ'
  refine ⟨?_, ?_⟩
  · rw [hmeq] at hvol0
    rw [← hball 1]
    exact (ENNReal.ofReal_le_ofReal hvol0).trans ENNReal.ofReal_toReal_le
  · intro R hR hRb k hk y hy
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p R := by
      rw [hmeq, hball]
      exact hy
    have hRb' : 2 * R + 2 < a := by
      have : R < b⁻¹ := hRb
      linarith
    have hd := hder0 R hR hRb' k hk y hy'
    rw [hmeq, curvatureDerivativeNorm_eq_curvDerivNorm] at hd
    exact hd

/-- The edge block of the G10 producer on one tail member: LFR28-ROW2's kernel, specialized to
the tail's constants, applied to the tail's edge centres. -/
theorem edgeDiskFamily_on_tail_LC87 {Δ σ μ b γ β ε τ κ b' s' s v a : ℝ} {K : ℕ} {Λ : ℝ≥0}
    (Acurv : ℝ → ℝ)
    (hE :
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
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M gR (ball p 1) ∧
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
              P.toEdgeChart = c))
    {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (o : ManifoldOrientation (𝓡 3) X 3) (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p)
    (hρsm : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ) (hρlip : LipschitzWith Λ ρ)
    {Je : Set X} (hJefin : Je.Finite)
    (hJeE : ∀ p ∈ Je, @isEdgePoint.{0, 0} X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p Δ b s)
    (hsecκ : ∀ p ∈ Je, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
      SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2))
    (hsecb : ∀ p ∈ Je, ∀ z ∈ ball p (b⁻¹ * ρ p), SectionalBoundedBelowAt g z (-(b / ρ p) ^ 2))
    (hab : 2 * b⁻¹ + 2 < a)
    (hvol0 : ∀ p ∈ Je, v ≤ (ballVolume (normalizedCenterMetric g (ρ p) (hρpos p)) p 1).toReal)
    (hder0 : ∀ p ∈ Je, ∀ R, 0 < R → 2 * R + 2 < a → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρpos p)) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρpos p)) k y ≤ Acurv R) :
    ∃ F : X → ℝ, (∀ x, 0 ≤ F x) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      ∀ p ∈ Je, (∀ x, |F x - infDist x (closure {y | @isEdgePoint.{0, 0} X
        ((mX).rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'})| < μ * (Δ * ρ p)) ∧
      (let A : Set X := closure
        {y | @isEdgePoint.{0, 0} X ((mX).rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'}
      let hMc : CompleteSpace X := complete_of_compact
      letI := (mX).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
      letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
      letI : CompleteSpace X :=
        ((mX).rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
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
    rcases Je.eq_empty_or_nonempty with hJe | hJne
    · refine ⟨fun _ => 0, fun _ => le_rfl, (LipschitzWith.const (0 : ℝ)).weaken bot_le,
        fun p hp => ?_⟩
      rw [hJe] at hp
      exact absurd hp (notMem_empty p)
    let _ : RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ, E3) x) := ⟨g.toRiemannianMetric⟩
    have : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      isContinuousRiemannianBundle_of_smoothRiemannianMetric g
    have : IsRiemannianManifold 𝓘(ℝ, E3) X := by
      constructor
      intro a b
      change edist a b = riemannianEDistOf g a b
      rw [edist_dist, hmetric]
    have hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) g := isMetricNorm_of_riemannianBundle g
    have : CompleteSpace X := complete_of_compact
    obtain ⟨p₀, hp₀⟩ := hJne
    have : ConnectedSpace X := connectedSpace_of_aligned_metric g hmetric p₀
    have hcentre := fun p (hp : p ∈ hJefin.toFinset) =>
      normalized_volume_and_derivatives_LC87 g hEnorm (p := p) (hρpos p)
        (K := K) Acurv hab (hvol0 p (hJefin.mem_toFinset.mp hp)) (hder0 p (hJefin.mem_toFinset.mp hp))
    obtain ⟨F, hF0, hFL, hFc⟩ := hE X g hEnorm o ρ hρpos hJefin.toFinset
      (by rw [Set.Finite.toFinset_nonempty]; exact ⟨p₀, hp₀⟩)
      (fun p hp => hJeE p (hJefin.mem_toFinset.mp hp))
      (fun p hp => hsecκ p (hJefin.mem_toFinset.mp hp))
      (fun p hp => hsecb p (hJefin.mem_toFinset.mp hp)) hρlip hρsm hcentre
    exact ⟨F, hF0, hFL, fun p hp => hFc p (hJefin.mem_toFinset.mpr hp)⟩

end DifferentialGeometry.Geometry.Collapse
