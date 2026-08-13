import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsoSeparationComposition
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section DataMono

def PreApproxIsoDataOn.mono [T2Space N] [SigmaCompactSpace N]
    {K K' : Set M} {ε ε' : ℝ} {p : ℕ}
    {Phi : M → N} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoDataOn (I := I) K ε p Phi g h)
    (hK : K' ⊆ K) (hε : ε ≤ ε') (hε1 : ε' < 1) :
    PreApproxIsoDataOn (I := I) K' ε' p Phi g h where
  eps_pos := lt_of_lt_of_le D.eps_pos hε
  eps_lt_one := hε1
  smoothOn := D.smoothOn.mono hK
  pullback := D.pullback
  pullback_apply := fun x hx v => D.pullback_apply x (hK hx) v
  c0_small := fun x hx => le_trans (D.c0_small x (hK hx)) hε
  cov_deriv_small := fun a h1 h2 x hx =>
    le_trans (D.cov_deriv_small a h1 h2 x (hK hx)) hε


def BookApproxIsoPartialData.mono [T2Space N] [SigmaCompactSpace N]
    {K K' : Set M} {ε ε' : ℝ} {p : ℕ}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoPartialData (I := I) K ε p Phi g h)
    (hK : K' ⊆ K) (hε : ε ≤ ε') (hε1 : ε' < 1) :
    BookApproxIsoPartialData (I := I) K' ε' p Phi g h where
  source_sub := fun _ hx => D.source_sub (hK hx)
  forward := D.forward.mono hK hε hε1
  reverse := (D.reverse.mono (Set.image_mono hK) hε hε1 :)

def PreApproxIsoDataOn.monoP [T2Space N] [SigmaCompactSpace N]
    {K : Set M} {ε : ℝ} {p p' : ℕ}
    {Phi : M → N} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoDataOn (I := I) K ε p Phi g h) (hp : p' ≤ p) :
    PreApproxIsoDataOn (I := I) K ε p' Phi g h where
  eps_pos := D.eps_pos
  eps_lt_one := D.eps_lt_one
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := D.c0_small
  cov_deriv_small := fun a h1 h2 x hx =>
    D.cov_deriv_small a h1 (le_trans h2 hp) x hx


def BookApproxIsoPartialData.monoP [T2Space N] [SigmaCompactSpace N]
    {K : Set M} {ε : ℝ} {p p' : ℕ}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoPartialData (I := I) K ε p Phi g h) (hp : p' ≤ p) :
    BookApproxIsoPartialData (I := I) K ε p' Phi g h where
  source_sub := D.source_sub
  forward := D.forward.monoP hp
  reverse := D.reverse.monoP hp

end DataMono

end HCGCompactness
end DifferentialGeometry
