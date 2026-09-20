import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section

open Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

section LeftInverse

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem pullbackMetricCoefficients_mfderiv_of_leftInverse
    (g : SmoothRiemannianMetric I M) {e : M → F} {r : F → M} {p : M}
    (he : MDifferentiableAt I 𝓘(ℝ, F) e p)
    (hr : MDifferentiableAt 𝓘(ℝ, F) I r (e p))
    (hleft : Function.LeftInverse r e) (v w : TangentSpace I p) :
    pullbackMetricCoefficients g r (e p)
      (mfderiv I 𝓘(ℝ, F) e p v) (mfderiv I 𝓘(ℝ, F) e p w) = g.inner p v w := by
  have hcomp : (mfderiv 𝓘(ℝ, F) I r (e p) : F →L[ℝ] E).comp
      (mfderiv I 𝓘(ℝ, F) e p) = ContinuousLinearMap.id ℝ E := by
    have hd : (mfderiv I I (r ∘ e) p : E →L[ℝ] E) =
        (mfderiv 𝓘(ℝ, F) I r (e p) : F →L[ℝ] E).comp
          (mfderiv I 𝓘(ℝ, F) e p) := mfderiv_comp p hr he
    rw [show r ∘ e = id from funext hleft, mfderiv_id] at hd
    exact hd.symm
  change (g.inner (r (e p)) : E →L[ℝ] E →L[ℝ] ℝ)
    (((mfderiv 𝓘(ℝ, F) I r (e p) : F →L[ℝ] E).comp
      (mfderiv I 𝓘(ℝ, F) e p)) v)
    (((mfderiv 𝓘(ℝ, F) I r (e p) : F →L[ℝ] E).comp
      (mfderiv I 𝓘(ℝ, F) e p)) w) = _
  rw [hcomp]
  change (g.inner (r (e p)) : E →L[ℝ] E →L[ℝ] ℝ) v w = _
  rw [hleft p]

theorem pullbackMetricCoefficients_comp_fderiv_of_leftInverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SmoothRiemannianMetric I M) {e : M → F} {r : F → M}
    {u : V → M} {x : V}
    (he : MDifferentiableAt I 𝓘(ℝ, F) e (u x))
    (hr : MDifferentiableAt 𝓘(ℝ, F) I r (e (u x)))
    (hleft : Function.LeftInverse r e)
    (hu : MDifferentiableAt 𝓘(ℝ, V) I u x) (v w : V) :
    pullbackMetricCoefficients g r (e (u x))
      (fderiv ℝ (e ∘ u) x v) (fderiv ℝ (e ∘ u) x w) =
        g.inner (u x) (mfderiv 𝓘(ℝ, V) I u x v) (mfderiv 𝓘(ℝ, V) I u x w) := by
  have hd : fderiv ℝ (e ∘ u) x =
      (mfderiv I 𝓘(ℝ, F) e (u x)).comp (mfderiv 𝓘(ℝ, V) I u x) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp x he hu
  rw [hd]
  exact pullbackMetricCoefficients_mfderiv_of_leftInverse g he hr hleft _ _

end LeftInverse

section CompactEmbedding

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [Nonempty M]

theorem exists_bounded_pullback_metric_coefficients_of_embedding
    (g : SmoothRiemannianMetric I M) {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Function.Injective (mfderiv I 𝓘(ℝ, F) e p)) :
    ∃ (r : F → M) (U : Set F),
      IsOpen U ∧ range e ⊆ U ∧ ContMDiffOn 𝓘(ℝ, F) I ∞ r U ∧
      Function.LeftInverse r e ∧
      ContDiffOn ℝ ∞ (pullbackMetricCoefficients g r) U ∧
      Continuous (fun p => pullbackMetricCoefficients g r (e p)) ∧
      (∀ y, LinearMap.IsPosSemidef (pullbackMetricCoefficients g r y).toBilinForm) ∧
      (∀ (p : M) (v w : TangentSpace I p),
        pullbackMetricCoefficients g r (e p)
          (mfderiv I 𝓘(ℝ, F) e p v) (mfderiv I 𝓘(ℝ, F) e p w) = g.inner p v w) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, ‖pullbackMetricCoefficients g r (e p)‖ ≤ C := by
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    exists_smooth_neighborhood_retraction he hemb hi
  have hB := contDiffOn_pullback_metric_coefficients g hU hr
  have hBc : Continuous (fun p => pullbackMetricCoefficients g r (e p)) :=
    hB.continuousOn.comp_continuous he.continuous (fun p => heU (mem_range_self p))
  have hn : Continuous (fun A : F →L[ℝ] F →L[ℝ] ℝ => ‖A‖) :=
    @continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance
  have hnorm : Continuous (fun p => ‖pullbackMetricCoefficients g r (e p)‖) := hn.comp hBc
  obtain ⟨A, hA⟩ := (isCompact_range hnorm).bddAbove
  refine ⟨r, U, hU, heU, hr, hleft, hB, hBc,
    (fun y => pullbackMetricCoefficients_isPosSemidef g r y), ?_,
    max A 0, le_max_right _ _, ?_⟩
  · intro p v w
    exact pullbackMetricCoefficients_mfderiv_of_leftInverse g
      (he.mdifferentiableAt (by simp))
      ((hr.contMDiffAt (hU.mem_nhds (heU (mem_range_self p)))).mdifferentiableAt
        (by simp)) hleft v w
  · intro p
    exact (hA (mem_range_self p)).trans (le_max_left _ _)

end CompactEmbedding

end DifferentialGeometry.Geometry
