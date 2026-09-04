import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs


open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section DataMono

def MapMetricApproximationBoundsOn.mono
    {K K' : Set M} {c0 c0' cov cov' : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p Phi g h)
    (hK : K' ⊆ K) (hc0 : c0 <= c0') (hcov : cov <= cov') :
    MapMetricApproximationBoundsOn (I := I) K' c0' cov' p Phi g h where
  c0_nonneg := le_trans D.c0_nonneg hc0
  cov_nonneg := le_trans D.cov_nonneg hcov
  smoothOn := D.smoothOn.mono hK
  pullback := D.pullback
  pullback_apply := fun x hx v => D.pullback_apply x (hK hx) v
  c0_small := fun x hx => le_trans (D.c0_small x (hK hx)) hc0
  cov_small := fun a h1 h2 x hx =>
    le_trans (D.cov_small a h1 h2 x (hK hx)) hcov

def PartialDiffeomorphMetricApproximationBounds.mono [T2Space N]
    [hSigma : SigmaCompactSpace N]
    {K K' : Set M} {c0 c0' cov cov' : Real} {p : Nat}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PartialDiffeomorphMetricApproximationBounds (I := I) K c0 cov p Phi g h)
    (hK : K' ⊆ K) (hc0 : c0 <= c0') (hcov : cov <= cov') :
    PartialDiffeomorphMetricApproximationBounds (I := I) K' c0' cov' p Phi g h where
  source_sub := fun _ hx => D.source_sub (hK hx)
  forward := D.forward.mono hK hc0 hcov
  reverse := let _ := hSigma; D.reverse.mono (Set.image_mono hK) hc0 hcov

def MapMetricApproximationOn.mono
    {K K' : Set M} {ε ε' : ℝ} {p : ℕ}
    {Phi : M → N} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationOn (I := I) K ε p Phi g h)
    (hK : K' ⊆ K) (hε : ε ≤ ε') (hε1 : ε' < 1) :
    MapMetricApproximationOn (I := I) K' ε' p Phi g h where
  eps_pos := lt_of_lt_of_le D.eps_pos hε
  eps_lt_one := hε1
  smoothOn := D.smoothOn.mono hK
  pullback := D.pullback
  pullback_apply := fun x hx v => D.pullback_apply x (hK hx) v
  c0_small := fun x hx => le_trans (D.c0_small x (hK hx)) hε
  cov_deriv_small := fun a h1 h2 x hx =>
    le_trans (D.cov_deriv_small a h1 h2 x (hK hx)) hε

def PartialDiffeomorphMetricApproximation.mono [T2Space N]
    [hSigma : SigmaCompactSpace N]
    {K K' : Set M} {ε ε' : ℝ} {p : ℕ}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PartialDiffeomorphMetricApproximation (I := I) K ε p Phi g h)
    (hK : K' ⊆ K) (hε : ε ≤ ε') (hε1 : ε' < 1) :
    PartialDiffeomorphMetricApproximation (I := I) K' ε' p Phi g h where
  source_sub := fun _ hx => D.source_sub (hK hx)
  forward := D.forward.mono hK hε hε1
  reverse := let _ := hSigma; (D.reverse.mono (Set.image_mono hK) hε hε1 :)

def MapMetricApproximationOn.monoOrder
    {K : Set M} {ε : ℝ} {p p' : ℕ}
    {Phi : M → N} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationOn (I := I) K ε p Phi g h) (hp : p' ≤ p) :
    MapMetricApproximationOn (I := I) K ε p' Phi g h where
  eps_pos := D.eps_pos
  eps_lt_one := D.eps_lt_one
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := D.c0_small
  cov_deriv_small := fun a h1 h2 x hx =>
    D.cov_deriv_small a h1 (le_trans h2 hp) x hx

def PartialDiffeomorphMetricApproximation.monoOrder [T2Space N]
    [hSigma : SigmaCompactSpace N]
    {K : Set M} {ε : ℝ} {p p' : ℕ}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PartialDiffeomorphMetricApproximation (I := I) K ε p Phi g h) (hp : p' ≤ p) :
    PartialDiffeomorphMetricApproximation (I := I) K ε p' Phi g h where
  source_sub := D.source_sub
  forward := D.forward.monoOrder hp
  reverse := let _ := hSigma; D.reverse.monoOrder hp

end DataMono

end CheegerGromovCompactness
end DifferentialGeometry
