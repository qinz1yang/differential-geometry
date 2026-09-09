import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Bundle.LocalFramePullback

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem MetricFamilySmoothOn.pullback
    [T2Space M]
    {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric J N) (hg : MetricFamilySmoothOn (I := J) D g)
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    MetricFamilySmoothOn (I := I) D (fun t => Diffeomorph.pullbackMetricCross (g t) Φ) where
  coeff x X Y := by
    simp only [Diffeomorph.pullbackMetricCross_inner]
    exact hg.coeff (Φ x)
      (mfderiv I J (Φ : M → N) x X) (mfderiv I J (Φ : M → N) x Y)
  coeff_cont x X Y := by
    simp only [Diffeomorph.pullbackMetricCross_inner]
    exact hg.coeff_cont (Φ x)
      (mfderiv I J (Φ : M → N) x X) (mfderiv I J (Φ : M → N) x Y)
  metricTensor_cont := by
    apply tensor0SFamilyContinuousOnSet.congr
      (tensor0SFamilyContinuousOnSet.pullback (I := I) (J := J)
        (fun t x => Tensor0SBundle.metricTensorField (I := J) (g t) x)
        hg.metricTensor_cont Φ)
    intro t _ht x
    ext slots
    rw [Tensor0SBundle.metricTensorField_apply, Diffeomorph.pullbackMetricCross_inner]
    rfl
  frameCompSmooth := by
    intro Idx _ frame u hframe i j
    have heq : (fun p : ℝ × M =>
          ((fun t => Diffeomorph.pullbackMetricCross (g t) Φ) p.1).inner p.2
            (frame i p.2) (frame j p.2))
        = fun p : ℝ × M => (g p.1).inner (Φ p.2)
            (mfderiv I J (Φ : M → N) p.2 (frame i p.2))
            (mfderiv I J (Φ : M → N) p.2 (frame j p.2)) := by
      funext p
      exact Diffeomorph.pullbackMetricCross_inner (I := I) (g p.1) Φ p.2
        (frame i p.2) (frame j p.2)
    rw [heq]
    have hpf := hg.frameCompSmooth
      (fun k (y : N) => mfderiv I J (Φ : M → N) (Φ.symm y) (frame k (Φ.symm y)))
      (hframe.pushforward Φ) i j
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (∞ : WithTop ℕ∞)
        (fun p : ℝ × M => (p.1, (Φ : M → N) p.2)) :=
      contMDiff_fst.prodMk (Φ.contMDiff.comp contMDiff_snd)
    have hmaps : Set.MapsTo (fun p : ℝ × M => (p.1, (Φ : M → N) p.2))
        (D.regular ×ˢ u) (D.regular ×ˢ (Φ '' u)) :=
      fun p hp => ⟨hp.1, Set.mem_image_of_mem _ hp.2⟩
    have hcomp := hpf.comp hmap.contMDiffOn hmaps
    have hN : ∀ (k : Idx) (x : M),
        (mfderiv I J (Φ : M → N) (Φ.symm (Φ x)) (frame k (Φ.symm (Φ x))) : F)
          = (mfderiv I J (Φ : M → N) x (frame k x) : F) :=
      fun k x => congrArg
        (fun a : M => (mfderiv I J (Φ : M → N) a (frame k a) : F)) (Φ.symm_apply_apply x)
    refine hcomp.congr ?_
    intro p _hp
    simp only [Function.comp_apply, hN]

end DifferentialGeometry.Geometry.Curvature

end
