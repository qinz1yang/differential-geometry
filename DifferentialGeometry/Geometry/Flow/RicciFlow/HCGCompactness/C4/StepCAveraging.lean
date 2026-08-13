import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAverageConvergence
open DifferentialGeometry.Geometry.Curvature
set_option autoImplicit false

noncomputable section

universe u uE uH uX uY

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

namespace centerAverage

variable {g : SmoothRiemannianMetric I M} {X : Type uX} {ι : Type}
variable [Fintype ι]
variable {μ : X → ι → ℝ} {pts : X → ι → M} {join : M → M → ℝ → M}
  {p : X → M} {r : X → ℝ}
  (h : ∀ x : X, CenterInput (I := I) g (μ x) (pts x) join (p x) (r x))
theorem unifTwoIdRegOn {s : Set M} {USeq : ℕ → ℕ → ι → Set M}
    {μSeq : ℕ → ℕ → M → ι → ℝ} {ptsSeq : ℕ → ℕ → M → ι → M}
    {pSeq : ℕ → ℕ → M → M} {rSeq : ℕ → ℕ → M → ℝ}
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hr : ∀ k l : ℕ, ∀ x : M, x ∈ s → 0 < rSeq k l x)
    (hqstar :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ k l : ℕ, ∀ x : M, x ∈ s → dist (pSeq k l x) x < rSeq k l x)
    (hactive_mem :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ k l : ℕ, ∀ x : M, x ∈ s → ∀ i : ι, μSeq k l x i ≠ 0 →
        dist (pSeq k l x) (ptsSeq k l x i) < rSeq k l x)
    (hμ : ∀ k l : ℕ, ∀ x : M, x ∈ s →
      (∀ i : ι, 0 ≤ μSeq k l x i) ∧
        (∃ i : ι, 0 < μSeq k l x i) ∧
          ∑ i : ι, μSeq k l x i = 1)
    (hstrict : ∀ k l : ℕ, ∀ x : M, x ∈ s →
      StrictDistInput (I := I) g
        (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x) join
        (pSeq k l x) (rSeq k l x))
    (hregion : ∀ k l : ℕ, ∀ x : M, x ∈ s → ∀ i : ι,
      μSeq k l x i ≠ 0 → x ∈ USeq k l i)
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x : M, x ∈ s →
        x ∈ USeq k l i → dist x (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist x
        (centerAverageOn (I := I) g s (μSeq k l)
          (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x)) join
          (pSeq k l) (rSeq k l) (fun x : M => x)
          (fun x hx => inputOfFill (I := I) (g := g) (μ := μSeq k l)
            (pts := ptsSeq k l) (join := join) (p := pSeq k l)
            (r := rSeq k l) (qstar := fun x : M => x) x hcomplete (hr k l x hx)
            (hqstar k l x hx) (hactive_mem k l x hx) ((hμ k l x hx).1)
            ((hμ k l x hx).2.1) (hstrict k l x hx)) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine unifTwoIdOfFillOn (I := I) (g := g) (join := join) hcomplete hr hqstar
    hactive_mem (fun k l x hx => (hμ k l x hx).1)
    (fun k l x hx => (hμ k l x hx).2.1) hstrict ?_
  intro i ε hε
  obtain ⟨N, hN⟩ := hpts i ε hε
  refine ⟨N, fun k hk l hl x hx hμx => ?_⟩
  exact hN k hk l hl x hx (hregion k l x hx i hμx)

theorem unifTwoIdDataOn {s : Set M} {USeq : ℕ → ℕ → ι → Set M}
    {μSeq : ℕ → ℕ → M → ι → ℝ} {ptsSeq : ℕ → ℕ → M → ι → M}
    {pSeq : ℕ → ℕ → M → M} {rSeq : ℕ → ℕ → M → ℝ}
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hr : ∀ k l : ℕ, ∀ x : M, x ∈ s → 0 < rSeq k l x)
    (hqstar :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ k l : ℕ, ∀ x : M, x ∈ s → dist (pSeq k l x) x < rSeq k l x)
    (hactive_mem :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ k l : ℕ, ∀ x : M, x ∈ s → ∀ i : ι, μSeq k l x i ≠ 0 →
        dist (pSeq k l x) (ptsSeq k l x i) < rSeq k l x)
    (hdata : ∀ k l : ℕ, ∀ x : M, x ∈ s →
      ((∀ i : ι, 0 ≤ μSeq k l x i) ∧
        (∃ i : ι, 0 < μSeq k l x i) ∧
          ∑ i : ι, μSeq k l x i = 1) ∧
        ∀ i : ι, μSeq k l x i ≠ 0 → x ∈ USeq k l i)
    (hstrict : ∀ k l : ℕ, ∀ x : M, x ∈ s →
      StrictDistInput (I := I) g
        (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x) join
        (pSeq k l x) (rSeq k l x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x : M, x ∈ s →
        x ∈ USeq k l i → dist x (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist x
        (centerAverageOn (I := I) g s (μSeq k l)
          (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x)) join
          (pSeq k l) (rSeq k l) (fun x : M => x)
          (fun x hx => inputOfFill (I := I) (g := g) (μ := μSeq k l)
            (pts := ptsSeq k l) (join := join) (p := pSeq k l)
            (r := rSeq k l) (qstar := fun x : M => x) x hcomplete (hr k l x hx)
            (hqstar k l x hx) (hactive_mem k l x hx) ((hdata k l x hx).1.1)
            ((hdata k l x hx).1.2.1) (hstrict k l x hx)) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact unifTwoIdRegOn (I := I) (g := g) (join := join) (USeq := USeq)
    hcomplete hr hqstar hactive_mem (fun k l x hx => (hdata k l x hx).1)
    hstrict (fun k l x hx i hμx => (hdata k l x hx).2 i hμx) hpts

theorem unifTwoIdDataSelf {s : Set M} {USeq : ℕ → ℕ → ι → Set M}
    {μSeq : ℕ → ℕ → M → ι → ℝ} {ptsSeq : ℕ → ℕ → M → ι → M}
    {rSeq : ℕ → ℕ → M → ℝ}
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hr : ∀ k l : ℕ, ∀ x : M, x ∈ s → 0 < rSeq k l x)
    (hactive_mem :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ k l : ℕ, ∀ x : M, x ∈ s → ∀ i : ι, μSeq k l x i ≠ 0 →
        dist x (ptsSeq k l x i) < rSeq k l x)
    (hdata : ∀ k l : ℕ, ∀ x : M, x ∈ s →
      ((∀ i : ι, 0 ≤ μSeq k l x i) ∧
        (∃ i : ι, 0 < μSeq k l x i) ∧
          ∑ i : ι, μSeq k l x i = 1) ∧
        ∀ i : ι, μSeq k l x i ≠ 0 → x ∈ USeq k l i)
    (hstrict : ∀ k l : ℕ, ∀ x : M, x ∈ s →
      StrictDistInput (I := I) g
        (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x) join x
        (rSeq k l x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x : M, x ∈ s →
        x ∈ USeq k l i → dist x (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist x
        (centerAverageOn (I := I) g s (μSeq k l)
          (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x)) join
          (fun x : M => x) (rSeq k l) (fun x : M => x)
          (fun x hx => inputOfFillSelf (I := I) (g := g) (μ := μSeq k l)
            (pts := ptsSeq k l) (join := join) (r := rSeq k l)
            (qstar := fun x : M => x) x hcomplete (hr k l x hx)
            (hactive_mem k l x hx) ((hdata k l x hx).1.1)
            ((hdata k l x hx).1.2.1) (hstrict k l x hx)) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact unif_two_id_fill_on (I := I) (g := g) (join := join)
    (fun k l x hx => inputOfFillSelf (I := I) (g := g) (μ := μSeq k l)
      (pts := ptsSeq k l) (join := join) (r := rSeq k l)
      (qstar := fun x : M => x) x hcomplete (hr k l x hx)
      (hactive_mem k l x hx) ((hdata k l x hx).1.1)
      ((hdata k l x hx).1.2.1) (hstrict k l x hx))
    (by
      intro i ε hε
      obtain ⟨N, hN⟩ := hpts i ε hε
      refine ⟨N, fun k hk l hl x hx hμx => ?_⟩
      exact hN k hk l hl x hx ((hdata k l x hx).2 i hμx))


theorem eqn_local (x : X)
    (hdiffSummands :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (pts x i))
        (centerAverage (I := I) g μ pts join p r h x))
    (hsrc :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, pts x i ∈
        (NormalCoordinates.normalChartAt (I := I) g
          (centerAverage (I := I) g μ pts join p r h x)).source) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ ρ : ℝ, 0 < ρ ∧
      ((∀ i : ι, pts x i ≠ centerAverage (I := I) g μ pts join p r h x →
        Real.sqrt
          (g.inner (centerAverage (I := I) g μ pts join p r h x)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerAverage (I := I) g μ pts join p r h x) (pts x i) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerAverage (I := I) g μ pts join p r h x) (pts x i) : E)) < ρ) →
        ∑ i : ι, μ x i •
          (show TangentSpace I (centerAverage (I := I) g μ pts join p r h x) from
            NormalCoordinates.normalChartAt (I := I) g
              (centerAverage (I := I) g μ pts join p r h x) (pts x i)) = 0) := by
  simpa [centerAverage] using
    centerOfMass.expInv_eqn_local (I := I) (g := g) (μ := μ x) (pts := pts x)
      (join := join) (p := p x) (r := r x) (h x) hdiffSummands hsrc


theorem eqn_local_on {s : Set X} {qstar : X → M}
    (hOn : ∀ x : X, x ∈ s → CenterInput (I := I) g (μ x) (pts x) join (p x) (r x))
    {x : X} (hx : x ∈ s)
    (hdiffSummands :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (pts x i))
        (centerAverageOn (I := I) g s μ pts join p r qstar hOn x))
    (hsrc :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, pts x i ∈
        (NormalCoordinates.normalChartAt (I := I) g
          (centerAverageOn (I := I) g s μ pts join p r qstar hOn x)).source) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ ρ : ℝ, 0 < ρ ∧
      ((∀ i : ι,
        pts x i ≠ centerAverageOn (I := I) g s μ pts join p r qstar hOn x →
        Real.sqrt
          (g.inner (centerAverageOn (I := I) g s μ pts join p r qstar hOn x)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerAverageOn (I := I) g s μ pts join p r qstar hOn x)
              (pts x i) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerAverageOn (I := I) g s μ pts join p r qstar hOn x)
              (pts x i) : E)) < ρ) →
        ∑ i : ι, μ x i •
          (show TangentSpace I
              (centerAverageOn (I := I) g s μ pts join p r qstar hOn x) from
            NormalCoordinates.normalChartAt (I := I) g
              (centerAverageOn (I := I) g s μ pts join p r qstar hOn x)
              (pts x i)) = 0) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hcm :
      centerAverageOn (I := I) g s μ pts join p r qstar hOn x =
        centerOfMass (I := I) g (μ x) (pts x) join (p x) (r x) (hOn x hx) :=
    on_eq (I := I) (g := g) (μ := μ) (pts := pts) (join := join) (p := p)
      (r := r) hOn hx
  have hdiff :
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (pts x i))
        (centerOfMass (I := I) g (μ x) (pts x) join (p x) (r x) (hOn x hx)) := by
    intro i
    simpa [hcm] using hdiffSummands i
  have hsrc' :
      ∀ i : ι, pts x i ∈
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g (μ x) (pts x) join (p x) (r x)
            (hOn x hx))).source := by
    intro i
    simpa [hcm] using hsrc i
  rw [hcm]
  exact centerOfMass.expInv_eqn_local (I := I) (g := g) (μ := μ x) (pts := pts x)
    (join := join) (p := p x) (r := r x) (hOn x hx) hdiff hsrc'

end centerAverage

theorem finite_cover_two_tail {J Y : Type*} [Finite J]
    {G : Set Y} {S : J → Set Y}
    (_hcover : G ⊆ ⋃ j, S j)
    (Q : J → Nat → Nat → Y → Prop)
    (hlocal : ∀ j, ∃ Nj : Nat, ∀ a ≥ Nj, ∀ b ≥ Nj,
      ∀ y ∈ S j, Q j a b y) :
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
      ∀ j, ∀ y ∈ S j, Q j a b y := by
  classical
  letI := Fintype.ofFinite J
  choose Nj hNj using hlocal
  refine ⟨Finset.univ.sup Nj, ?_⟩
  intro a ha b hb j y hy
  have hj : Nj j ≤ Finset.univ.sup Nj :=
    Finset.le_sup (f := Nj) (Finset.mem_univ j)
  exact hNj j a (hj.trans ha) b (hj.trans hb) y hy

end HCGCompactness
end DifferentialGeometry
