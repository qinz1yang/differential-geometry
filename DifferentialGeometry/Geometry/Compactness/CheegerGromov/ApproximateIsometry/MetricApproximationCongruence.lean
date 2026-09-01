import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximationMonotonicity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximateIsometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PartialDiffeomorphOpens

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators ENNReal
open Bundle Manifold
open DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section DataTransport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [MetricSpace M] [Nonempty M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
  [SigmaCompactSpace N]

noncomputable def MapMetricApproximationOn.congrEq {K : Set M} {ε : ℝ} {p : ℕ} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationOn (I := I) K ε p F g h) (hEq : F' = F) :
    MapMetricApproximationOn (I := I) K ε p F' g h :=
  D.congr (fun _ _ => Filter.EventuallyEq.of_eq hEq)

noncomputable def MapMetricApproximationBoundsOn.congr {K : Set M} {c0 cov : ℝ} {p : ℕ} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p F g h)
    (hev : ∀ x ∈ K, F' =ᶠ[nhds x] F) :
    MapMetricApproximationBoundsOn (I := I) K c0 cov p F' g h where
  c0_nonneg := D.c0_nonneg
  cov_nonneg := D.cov_nonneg
  smoothOn := D.smoothOn.congr (fun x hx => (hev x hx).self_of_nhds)
  pullback := D.pullback
  pullback_apply := by
    intro x hx v
    rw [(hev x hx).self_of_nhds, (hev x hx).mfderiv_eq]
    exact D.pullback_apply x hx v
  c0_small := D.c0_small
  cov_small := D.cov_small

noncomputable def MapMetricApproximationBoundsOn.congrEq {K : Set M} {c0 cov : ℝ} {p : ℕ} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p F g h) (hEq : F' = F) :
    MapMetricApproximationBoundsOn (I := I) K c0 cov p F' g h :=
  D.congr (fun _ _ => Filter.EventuallyEq.of_eq hEq)

noncomputable def MapMetricApproximationBoundsOn.congrSet {K K' : Set M} {c0 cov : ℝ} {p : ℕ}
    {F : M → N} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p F g h) (hK : K' = K) :
    MapMetricApproximationBoundsOn (I := I) K' c0 cov p F g h := by
  subst hK
  exact D

noncomputable def PartialDiffeomorphMetricApproximation.ofParts {K : Set M} {ε : ℝ} {p : ℕ}
    {Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hsrc : K ⊆ Φ.source)
    (forward : MapMetricApproximationOn (I := I) K ε p (Φ : M → N) g h)
    (reverse : MapMetricApproximationOn (I := I) ((Φ : M → N) '' K) ε p (Φ.symm : N → M) h g) :
    PartialDiffeomorphMetricApproximation (I := I) K ε p Φ g h where
  source_sub := hsrc
  forward := forward
  reverse := reverse

noncomputable def PartialDiffeomorphMetricApproximationBounds.ofParts {K : Set M} {c0 cov : ℝ} {p : ℕ}
    {Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hsrc : K ⊆ Φ.source)
    (forward : MapMetricApproximationBoundsOn (I := I) K c0 cov p (Φ : M → N) g h)
    (reverse : MapMetricApproximationBoundsOn (I := I) ((Φ : M → N) '' K) c0 cov p (Φ.symm : N → M) h g) :
    PartialDiffeomorphMetricApproximationBounds (I := I) K c0 cov p Φ g h where
  source_sub := hsrc
  forward := forward
  reverse := reverse

noncomputable def PartialDiffeomorphMetricApproximationBounds.congrSet {K K' : Set M} {c0 cov : ℝ} {p : ℕ}
    {Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PartialDiffeomorphMetricApproximationBounds (I := I) K c0 cov p Φ g h) (hK : K' = K) :
    PartialDiffeomorphMetricApproximationBounds (I := I) K' c0 cov p Φ g h := by
  subst hK
  exact D

theorem image_eq_of_fun_eq {α β : Type*} {s : Set α} {f g : α → β} (h : f = g) :
    f '' s = g '' s := by
  subst h
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [MetricSpace M] [Nonempty M] [T2Space N]
    [SigmaCompactSpace N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [IsManifold I ∞ N] in
theorem symm_eventuallyEq_on_image
    {Φ Ψ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {U : TopologicalSpace.Opens M}
    (hUΦ : (U : Set M) ⊆ Φ.source) (hUΨ : (U : Set M) ⊆ Ψ.source)
    (hEq : (Ψ : M → N) = (Φ : M → N)) :
    ∀ y ∈ (Φ : M → N) '' (U : Set M),
      (Ψ.symm : N → M) =ᶠ[nhds y] (Φ.symm : N → M) := by
  intro y hy
  refine Filter.eventuallyEq_of_mem ((image_opens_isOpen (I := I) Φ hUΦ).mem_nhds hy) ?_
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hΨx : (Ψ : M → N) x = (Φ : M → N) x := by rw [hEq]
  calc
    (Ψ.symm : N → M) ((Φ : M → N) x)
        = (Ψ.symm : N → M) ((Ψ : M → N) x) := by rw [hΨx]
    _ = x := Ψ.left_inv' (hUΨ hx)
    _ = (Φ.symm : N → M) ((Φ : M → N) x) := (Φ.left_inv' (hUΦ hx)).symm

end DataTransport

end HCGCompactness
end DifferentialGeometry
