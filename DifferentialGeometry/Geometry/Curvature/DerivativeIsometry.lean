import DifferentialGeometry.Geometry.Curvature.LocalIsometry
import DifferentialGeometry.Tensor.Metric.IsometryNorm
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Tensor DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Riemannian
variable {E H M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem normSq_iterCov_metricRm04_of_pullback_on_opens
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    [SigmaCompactSpace U] [SigmaCompactSpace V] (Φ : U ≃ₘ⟮I, I⟯ V)
    (hmetric : ∀ (y : U) (v w : TangentSpace I y),
      g.inner (y : M) v w = h.inner (Φ y : N)
        (mfderiv I I Φ y v) (mfderiv I I Φ y w)) (k : ℕ) (x : U) :
    normSq0S g (x : M) (4 + k) (iterCov g 4 (metricRm04 g) k (x : M)) =
      normSq0S h (Φ x : N) (4 + k) (iterCov h 4 (metricRm04 h) k (Φ x : N)) := by
  have hcurv (y : U) (v : Fin 4 → TangentSpace I y) :
      metricRm04 g (y : M) v = metricRm04 h (Φ y : N)
        (fun i => mfderiv I I Φ y (v i)) := by
    have hh := metricRm04StdAt_of_pullback_on_opens g h U V Φ hmetric y
      (v 0) (v 1) (v 2) (v 3)
    have hv : vec4 (I := I) (x := (y : M)) (v 0) (v 1) (v 2) (v 3) = v := by
      funext i
      fin_cases i <;> rfl
    have hdv : vec4 (I := I) (x := (Φ y : N))
        (mfderiv I I Φ y (v 0)) (mfderiv I I Φ y (v 1))
        (mfderiv I I Φ y (v 2)) (mfderiv I I Φ y (v 3)) =
        (fun i => mfderiv I I Φ y (v i)) := by
      funext i
      fin_cases i <;> rfl
    change metricRm04At g (y : M) (vec4 (v 0) (v 1) (v 2) (v 3)) =
      metricRm04At h (Φ y : N) (vec4 (mfderiv I I Φ y (v 0))
        (mfderiv I I Φ y (v 1)) (mfderiv I I Φ y (v 2)) (mfderiv I I Φ y (v 3))) at hh
    simpa only [metricRm04_apply, hv, hdv] using hh
  exact normSq0S_iterCov_of_metric_isometry_on_opens g h U V Φ hmetric
    (metricRm04 g) (metricRm04 h) hcurv k x

variable [I.Boundaryless] [SigmaCompactSpace M] [SigmaCompactSpace N]

theorem normSq_iterCov_metricRm04_of_metric_isometry_on_open
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (U : TopologicalSpace.Opens M) (f : M → N) (hf : ContMDiffOn I I ∞ f U)
    (hmetric : ∀ (y : M), y ∈ U → ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner (f y) (mfderiv I I f y v) (mfderiv I I f y w))
    (k : ℕ) (x : U) :
    normSq0S g (x : M) (4 + k) (iterCov g 4 (metricRm04 g) k (x : M)) =
      normSq0S h (f x) (4 + k) (iterCov h 4 (metricRm04 h) k (f x)) := by
  have himm : Function.Injective (mfderiv I I f x.val) := by
    intro v w he
    by_contra hvw
    have hp := g.pos (x : M) (v - w) (sub_ne_zero.mpr hvw)
    have hz : mfderiv I I f x.val (v - w) = 0 := by rw [map_sub, he, sub_self]
    rw [hmetric x x.property, hz, map_zero] at hp
    exact (lt_irrefl 0) hp
  let L : E →L[ℝ] E := mfderiv I I f x.val
  let A : E ≃L[ℝ] E := (L.toLinearMap.linearEquivOfInjective himm rfl).toContinuousLinearEquiv
  have hloc := isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv f hf U.isOpen
    x.val x.property A ((hf.contMDiffAt (U.isOpen.mem_nhds x.property)).mdifferentiableAt
      (by simp)).hasMFDerivAt
  obtain ⟨Φ, hxΦ, hΦ⟩ := hloc
  let W : TopologicalSpace.Opens M := ⟨U ∩ Φ.source, U.isOpen.inter Φ.open_source⟩
  have hW : (W : Set M) ⊆ Φ.source := fun _ hy => hy.2
  let V : TopologicalSpace.Opens N := ⟨Φ '' (W : Set M), image_opens_isOpen Φ hW⟩
  let D : W ≃ₘ⟮I, I⟯ V := Φ.toOpensDiffeo hW
  have hpoint (y : W) : (D y : N) = f y := (hΦ y.property.2).symm
  have hd (y : W) (v : TangentSpace I y) : mfderiv I I D y v = mfderiv I I f y.val v := by
    have he : (Φ : M → N) =ᶠ[𝓝 y.val] f :=
      Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds y.property.2) (fun z hz => (hΦ hz).symm)
    exact (PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hW y v).trans
      (congrArg (fun B => B v) (he.mfderiv_eq (I := I) (I' := I)))
  have hmD (y : W) (v w : TangentSpace I y) :
      g.inner (y : M) v w = h.inner (D y : N) (mfderiv I I D y v) (mfderiv I I D y w) := by
    rw [hpoint, hd, hd]
    exact hmetric y y.property.1 v w
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  have hh := normSq_iterCov_metricRm04_of_pullback_on_opens g h W V D hmD k
    ⟨x.val, x.property, hxΦ⟩
  erw [hpoint] at hh
  exact hh
end DifferentialGeometry.Geometry.Riemannian
