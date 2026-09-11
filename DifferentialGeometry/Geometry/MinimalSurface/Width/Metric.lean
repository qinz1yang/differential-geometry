import DifferentialGeometry.Geometry.MinimalSurface.Width.Composition
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaMetric



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M] {n : ℕ}



theorem classWidth_metric_upper
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ c * g.inner x v v)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    classWidth h e (he.of_le (by exact_mod_cast le_top)) hemb ξ ≤
      c * classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ := by
  have hw := classWidth_postcompose_le g h e he hemb hi e he hemb hi id
    (metric_upper_lipschitz g h hc hgh) ξ
  change classWidth h e _ hemb (LoopFamily.postcompose (.id M) ξ) ≤
    (Real.sqrt c) ^ 2 * classWidth g e _ hemb ξ at hw
  simpa only [LoopFamily.postcompose_id, Real.sq_sqrt hc.le] using hw



theorem classWidth_metric_bounds
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), a ^ 2 * g.inner x v v ≤ h.inner x v v)
    (hhi : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ b ^ 2 * g.inner x v v)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    a ^ 2 * classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ ≤
      classWidth h e (he.of_le (by exact_mod_cast le_top)) hemb ξ ∧
    classWidth h e (he.of_le (by exact_mod_cast le_top)) hemb ξ ≤
      b ^ 2 * classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ := by
  refine ⟨?_, classWidth_metric_upper g h (sq_pos_of_pos hb) hhi e he hemb hi ξ⟩
  have hl := classWidth_metric_upper h g (inv_pos.mpr (sq_pos_of_pos ha))
    (metric_lower_inverse_upper g h (sq_pos_of_pos ha) hlo) e he hemb hi ξ
  rw [← div_eq_inv_mul] at hl
  simpa only [mul_comm] using (le_div_iff₀ (sq_pos_of_pos ha)).mp hl



theorem classWidth_scale (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (c : ℝ) (hc : 0 < c)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    classWidth (scaleMetric c hc g) e (he.of_le (by exact_mod_cast le_top)) hemb ξ =
      c * classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ := by
  obtain ⟨hl, hu⟩ := classWidth_metric_bounds g (scaleMetric c hc g)
    (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hc)
    (fun x v => by simp only [Real.sq_sqrt hc.le, scaleMetric_inner, le_refl])
    (fun x v => by simp only [Real.sq_sqrt hc.le, scaleMetric_inner, le_refl]) e he hemb hi ξ
  rw [Real.sq_sqrt hc.le] at hl hu
  exact le_antisymm hu hl

end DifferentialGeometry.Geometry
