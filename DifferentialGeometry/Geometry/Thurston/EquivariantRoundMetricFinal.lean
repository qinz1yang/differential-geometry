import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetric
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA2
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricLimit
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricModel
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

/-!
# The isometry-invariant round metric, conditional on a5

Chapter 7, surface lemma U1 (`exists_isometryInvariant_roundMetric`,
`TH/NonnegativeClassificationProof.lean`), route (a), final wiring (lane U1E2) of the design note
D17 (`docs/geometrization/handoffs/20261004-design-u1-ricci-flow-core.md`, §2 and §3, with the
errata after review 17).

* `exists_isometryInvariant_roundMetric_of_a5`: the conclusion of U1, for every compact connected
  surface `N` modeled on `MorseModel 2` and every metric `h` of positive scalar curvature, under
  one hypothesis `ha5`: the conclusion of a5 (fixed-background bounds of all orders and a
  positive lower bound for `g(t) / (2 (Tm - t))` against `g(0)`, and the decay
  `|2 (Tm - t) R - 2| ≤ C (Tm - t)^δ`, both on a terminal interval) for every maximal Ricci flow on
  `N` in the Euclidean model `surfaceModel` with positive initial scalar curvature.

The proof moves `h` to `surfaceModel` (`toSurfaceModel`), takes the maximal flow of
`exists_maximal_surfaceFlow` (a2), its rescaled round limit `surfaceFlow_limit_round_of_a5`
(a6, a7), and moves the flow and the limit back: joint smoothness through
`metricCLMSection_jointContMDiffOn_of_chartGram_on` and
`chartGramMatrix_joint_contMDiffOn_of_pullback`, the Ricci flow equation through
`ricciTensor_cross`, the curvature identity through `metricRm04Standard_pullbackCross`. The assembly
`exists_isometryInvariant_roundMetric_of_rescaled_limit` finishes. Simple connectivity of `N` is
not used.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness
open Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

local notation "MM2" => DifferentialGeometry.Topology.Morse.MorseModel 2
local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace MM2 N] [IsManifold 𝓘(ℝ, MM2) ∞ N]
  [T2Space N] [CompactSpace N] [ConnectedSpace N]

theorem exists_isometryInvariant_roundMetric_of_a5
    (ha5 : ∀ {Tm : ℝ} (hTm : 0 < Tm)
      (S : SolutionOn (I := surfaceModel) (M := N) (RealTimeInterval.closedOpen 0 Tm hTm)),
      IsSolutionOn S → (∀ x, 0 < S.scalar 0 x) →
      IsMaximalAtEndpoint (I := surfaceModel) hTm S →
      (∃ t₀ < Tm, (∀ q : ℕ, ∃ C : ℝ, ∀ t (ht : t ∈ Ico t₀ Tm), ∀ z,
          metricCovDerivNorm q
            (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2)
              (S.family.metric t)) (S.family.metric 0) z ≤ C) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ t (ht : t ∈ Ico t₀ Tm), ∀ x (v : TangentSpace surfaceModel x),
          c * (S.family.metric 0).inner x v v ≤
            (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2)
              (S.family.metric t)).inner x v v) ∧
      ∃ t₀ < Tm, ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico t₀ Tm, ∀ x,
        |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ)
    (h : SmoothRiemannianMetric 𝓘(ℝ, MM2) N) (hscal : ∀ y, 0 < metricScalarAt h y) :
    ∃ h₁ : SmoothRiemannianMetric 𝓘(ℝ, MM2) N,
      (∀ (y : N) (X Y : TangentSpace 𝓘(ℝ, MM2) y),
        metricRm04StandardAt h₁ y X Y Y X =
          1 * (h₁.inner y X X * h₁.inner y Y Y - h₁.inner y X Y * h₁.inner y X Y)) ∧
      ∀ φ : N ≃ₘ⟮𝓘(ℝ, MM2), 𝓘(ℝ, MM2)⟯ N,
        Diffeomorph.pullbackMetric h φ = h → Diffeomorph.pullbackMetric h₁ φ = h₁ := by
  have hdim : Module.finrank ℝ E2 = 2 := finrank_euclideanSpace_fin
  have : NeZero (Module.finrank ℝ E2) := ⟨by rw [hdim]; norm_num⟩
  have : NeZero (Module.finrank ℝ MM2) := ⟨by simp⟩
  have hscal' : ∀ x, 0 < metricScalarAt
      (Diffeomorph.pullbackMetricCross h (toSurfaceModel N).symm) x := fun x =>
    lt_of_lt_of_eq (hscal x) (toSurfaceModel_scalar h x).symm
  obtain ⟨Tm, P, hmax, -⟩ := exists_maximal_surfaceFlow (I := surfaceModel) hdim _ hscal'
  have hscalP : ∀ x, 0 < P.S.scalar 0 x := by
    intro x
    change 0 < metricScalarAt (P.S.family.metric 0) x
    rw [P.start]
    exact hscal' x
  obtain ⟨hfixed, hdecay⟩ := ha5 P.time_pos P.S P.isSolution hscalP hmax
  obtain ⟨τ, hlim', hτ0, hτT, hconv', hround'⟩ :=
    surfaceFlow_limit_round_of_a5 hdim P.time_pos P.S hfixed hdecay
  let Φ := toSurfaceModel N
  let g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, MM2) N := fun t =>
    Diffeomorph.pullbackMetricCross (P.S.family.metric t) Φ
  have hinner : ∀ t x (u v : TangentSpace 𝓘(ℝ, MM2) x), (g t).inner x u v =
      (P.S.family.metric t).inner (Φ x) (mfderiv 𝓘(ℝ, MM2) surfaceModel Φ x u)
        (mfderiv 𝓘(ℝ, MM2) surfaceModel Φ x v) := fun t x u v =>
    Diffeomorph.pullbackMetricCross_inner _ _ x u v
  have hg0 : g 0 = h := by
    change Diffeomorph.pullbackMetricCross (P.S.family.metric 0) Φ = h
    rw [P.start]
    exact pullback_toSurfaceModel_metric h
  have hjoint' := metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => P.S.family.metric t) (Ico 0 Tm) P.joint
  have hjoint := metricCLMSection_jointContMDiffOn_of_chartGram_on g (Ico 0 Tm)
    (fun x₀ i j => chartGramMatrix_joint_contMDiffOn_of_pullback (fun t => P.S.family.metric t)
      (Ico 0 Tm) hjoint' g Φ Φ.contMDiff (fun t _ x u v => hinner t x u v) x₀ i j)
  have hpde : ∀ t ∈ Ico 0 Tm, ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, MM2) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w)
        (Ici 0) t := by
    intro t ht x v w
    have hp := P.pde t ht (Φ x) (mfderiv 𝓘(ℝ, MM2) surfaceModel Φ x v)
      (mfderiv 𝓘(ℝ, MM2) surfaceModel Φ x w)
    have hric : ricciTensor (g t) x v w = ricciTensor (P.S.family.metric t) (Φ x)
        (mfderiv 𝓘(ℝ, MM2) surfaceModel Φ x v) (mfderiv 𝓘(ℝ, MM2) surfaceModel Φ x w) :=
      ricciTensor_cross _ Φ x v w
    rw [hric]
    simp only [hinner]
    exact hp
  let hlim := Diffeomorph.pullbackMetricCross hlim' Φ
  have hconv : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, MM2) x),
      Tendsto (fun k => 1 / (2 * (Tm - τ k)) * (g (τ k)).inner x v w) atTop
        (𝓝 (hlim.inner x v w)) := by
    intro x v w
    simp only [hinner, hlim, Diffeomorph.pullbackMetricCross_inner]
    exact hconv' (Φ x) _ _
  have hround : ∀ (y : N) (X Y : TangentSpace 𝓘(ℝ, MM2) y),
      metricRm04StandardAt hlim y X Y Y X =
        1 * (hlim.inner y X X * hlim.inner y Y Y - hlim.inner y X Y * hlim.inner y X Y) := by
    intro y X Y
    rw [metricRm04Standard_pullbackCross, hround']
    simp only [hlim, Diffeomorph.pullbackMetricCross_inner]
  exact exists_isometryInvariant_roundMetric_of_rescaled_limit h P.time_pos g hg0 hjoint hpde
    τ hτ0 hτT _ hlim hconv hround

end GC.Geometry
