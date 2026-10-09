import DifferentialGeometry.Analysis.Calculus.DistanceSmoothing.SeminormMollification
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Topology.FiberBundle.Separation

/-!
# Local-to-global Lipschitz bounds (LC28, tier T2, globalisation step)

* `continuous_of_locally_lipschitz`, `lipschitzWith_of_locally_of_segments`: in a pseudometric space
  in which any two points are joined by a curve `c` with `dist (c s) (c t) ≤ dist x y · (t - s)`,
  a function that is `L`-Lipschitz on a neighbourhood of every point is globally `L`-Lipschitz.
* `exists_riemannian_segment`: on a complete Riemannian manifold (instance block of the soul
  toolkit) every two points are joined by such a curve (a minimizing intrinsic geodesic).
* `lipschitzWith_of_locally_riemannian`: the combination on a Riemannian manifold.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

section Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A function that is `L`-Lipschitz on a neighbourhood of every point is continuous. -/
theorem continuous_of_locally_lipschitz {h : X → ℝ} {L : ℝ≥0}
    (hloc : ∀ x, ∃ V ∈ 𝓝 x, ∀ y ∈ V, ∀ y' ∈ V, |h y - h y'| ≤ L * dist y y') :
    Continuous h := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨V, hV, hlip⟩ := hloc x
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hball : ∀ᶠ y in 𝓝 x, dist y x < ε / (L + 1) :=
    Metric.ball_mem_nhds x (by positivity)
  filter_upwards [hV, hball] with y hy hyx
  rw [Real.dist_eq]
  calc |h y - h x| ≤ L * dist y x := hlip y hy x (mem_of_mem_nhds hV)
    _ ≤ (L + 1) * dist y x := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        linarith
    _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hyx (by positivity)
    _ = ε := by field_simp

/-- Local-to-global Lipschitz bound along segments. -/
theorem lipschitzWith_of_locally_of_segments
    (hseg : ∀ x y : X, ∃ c : ℝ → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      ∀ s t, s ≤ t → dist (c s) (c t) ≤ dist x y * (t - s))
    {h : X → ℝ} {L : ℝ≥0}
    (hloc : ∀ x, ∃ V ∈ 𝓝 x, ∀ y ∈ V, ∀ y' ∈ V, |h y - h y'| ≤ L * dist y y') :
    LipschitzWith L h := by
  have hcont := continuous_of_locally_lipschitz hloc
  have hone : ∀ x y : X, h y - h x ≤ L * dist x y := by
    intro x y
    obtain ⟨c, hc, hc0, hc1, hcd⟩ := hseg x y
    have key := sub_le_mul_sub_of_eventually_increment_le (φ := fun t => h (c t))
      (a := 0) (b := 1) (B := L * dist x y) zero_le_one (hcont.comp hc).continuousOn (by
        intro t _ c' hc'
        obtain ⟨V, hV, hlip⟩ := hloc (c t)
        have hev : ∀ᶠ s in 𝓝 t, c s ∈ V := hc.continuousAt.preimage_mem_nhds hV
        filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hts
        have hts' : t < s := hts
        have h1 := hlip (c s) hs (c t) (mem_of_mem_nhds hV)
        have h2 : dist (c s) (c t) ≤ dist x y * (s - t) := by
          rw [dist_comm]; exact hcd t s hts'.le
        have h3 : (L : ℝ) * dist (c s) (c t) ≤ L * (dist x y * (s - t)) :=
          mul_le_mul_of_nonneg_left h2 L.coe_nonneg
        have h4 : (L : ℝ) * dist x y * (s - t) ≤ c' * (s - t) :=
          mul_le_mul_of_nonneg_right hc'.le (sub_nonneg.mpr hts'.le)
        have h5 := (abs_le.mp h1).2
        nlinarith)
    simp only [hc0, hc1] at key
    linarith
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, abs_le]
  constructor
  · have := hone x y
    linarith
  · have := hone y x
    rw [dist_comm] at this
    linarith

end Metric

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
theorem riemannianEDist_toReal_eq_dist_of_isRiemannian (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

/-- On a complete Riemannian manifold every two points are joined by a minimizing intrinsic
geodesic `c` with `c 0 = x`, `c 1 = y` and `dist (c s) (c t) ≤ dist x y · (t - s)`. -/
theorem exists_riemannian_segment (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (x y : M) :
    ∃ c : ℝ → M, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      ∀ s t, s ≤ t → dist (c s) (c t) ≤ dist x y * (t - s) := by
  have hfin : riemannianEDist I x y ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top x y
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top g hEnorm x y hfin
  rw [riemannianEDist_toReal_eq_dist_of_isRiemannian] at hlen
  refine ⟨intrinsicGeodesic g hEnorm x v, (intrinsicGeodesic_contMDiff g hEnorm x v).continuous,
    intrinsicGeodesic_zero g hEnorm x v, by simpa only [expMapIntrinsic_def] using hv, ?_⟩
  intro s t hst
  have h := intrinsicGeodesic_riemannianEDist_le g hEnorm x v hst
  rw [← IsRiemannianManifold.out (I := I), edist_dist, hlen] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg dist_nonneg (sub_nonneg.mpr hst))).mp h

/-- Local-to-global Lipschitz bound on a complete Riemannian manifold. -/
theorem lipschitzWith_of_locally_riemannian (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {h : M → ℝ} {L : ℝ≥0}
    (hloc : ∀ x, ∃ V ∈ 𝓝 x, ∀ y ∈ V, ∀ y' ∈ V, |h y - h y'| ≤ L * dist y y') :
    LipschitzWith L h :=
  lipschitzWith_of_locally_of_segments (exists_riemannian_segment g hEnorm) hloc

/-- A complete Riemannian manifold with a nonempty carrier is connected (finite distances). -/
theorem connectedSpace_of_riemannian (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    [Nonempty M] : ConnectedSpace M := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  refine { isPreconnected_univ := ?_, toNonempty := ‹Nonempty M› }
  refine isPreconnected_of_forall x₀ fun y _ => ?_
  obtain ⟨c, hc, hc0, hc1, -⟩ := exists_riemannian_segment g hEnorm x₀ y
  refine ⟨c '' Icc 0 1, subset_univ _, ⟨0, ⟨le_rfl, zero_le_one⟩, hc0⟩,
    ⟨1, ⟨zero_le_one, le_rfl⟩, hc1⟩, ?_⟩
  exact (isPreconnected_Icc).image c hc.continuousOn

end Riemannian

end DifferentialGeometry.Geometry.Collapse
