import DifferentialGeometry.Geometry.Metric.Convergence.AtlasDistance
import DifferentialGeometry.Geometry.Metric.OpenAtlasGluing











set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter
open scoped ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {α ι E F H X : Type*} {l : Filter ι} [l.NeBot]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : ι → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [MetricSpace X]

private abbrev realizationBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private abbrev realizationBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
attribute [local instance] realizationBilinearGroup realizationBilinearSpace

theorem exists_unique_contMDiffMetric_of_pointed_atlas_limits
    (hX : ∀ x y : X, Metric.intrinsicEDist x y = edist x y) (k : ℕ)
    (e : α → OpenPartialHomeomorph X E)
    (hcover : ∀ x : X, ∃ a, x ∈ (e a).source)
    (htrans : ∀ a d, ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) ((e a).symm.trans (e d))
      ((e a).symm.trans (e d)).source)
    (R : α → ℝ) (hR : ∀ a, 0 < R a)
    (htarget : ∀ a, (e a).target ⊆ Metric.ball 0 (R a / 8))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hg : ∀ i, letI : RiemannianBundle (TangentSpace I : M i → Type _) :=
      ⟨(g i).toRiemannianMetric⟩; IsRiemannianManifold I (M i))
    (Φ : α → ∀ i, OpenPartialHomeomorph E (M i))
    (hΦ : ∀ a, ∀ᶠ i in l, ContMDiffOn 𝓘(ℝ, E) I 1 (Φ a i) (Φ a i).source)
    (hΦinv : ∀ a, ∀ᶠ i in l, ContMDiffOn I 𝓘(ℝ, E) 1 (Φ a i).symm (Φ a i).target)
    (hsource : ∀ a, ∀ᶠ i in l, Metric.ball (0 : E) (R a) ⊆ (Φ a i).source)
    (himage : ∀ a, ∀ᶠ i in l, (Φ a i : E → M i) '' Metric.ball 0 (R a) =
      Metric.ball (Φ a i 0) (R a))
    (hrad : ∀ a, ∀ᶠ i in l, ∀ x ∈ Metric.ball 0 (R a), dist (Φ a i x) (Φ a i 0) = ‖x‖)
    (b : α → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ a, ContDiffOn ℝ k (b a) (Metric.ball 0 (R a)))
    (hconv : ∀ a, TendstoUniformlyOn
      (fun i => pullbackMetricCoefficients (g i) (Φ a i)) (b a) l (Metric.ball 0 (R a)))
    (c : α → ℝ) (hc : ∀ a, 0 < c a)
    (hlower : ∀ a, ∀ᶠ i in l, ∀ x ∈ Metric.ball 0 (R a), ∀ v : E,
      c a * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients (g i) (Φ a i) x v v)
    (hcompat : ∀ a d u, u ∈ ((e a).symm.trans (e d)).source →
      b a u = (b d (((e a).symm.trans (e d)) u)).bilinearComp
        (fderiv ℝ ((e a).symm.trans (e d)) u)
        (fderiv ℝ ((e a).symm.trans (e d)) u))
    (o : ∀ i, M i) (p : X) {r ε : ι → ℝ}
    (A : ∀ i, GC.MetricGeometry.PointedBallApprox (o i) p (r i) (ε i))
    (hε : Tendsto ε l (𝓝 0)) (L : α → E → X)
    (hdom : ∀ a, ∀ᶠ i in l, ∀ w ∈ Metric.closedBall (0 : E) (R a / 4),
      Φ a i w ∈ Metric.closedBall (o i) (r i))
    (hmap : ∀ a, TendstoUniformlyOn (fun i w => (A i).extendToWholeSpace (Φ a i w)) (L a) l
      (Metric.closedBall 0 (R a / 4)))
    (hchart : ∀ a, EqOn (e a).symm (L a) (e a).target) :
    letI := DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover e hcover
    letI := DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover
      e hcover htrans
    letI : IsManifold 𝓘(ℝ, E) 1 X := IsManifold.of_le (n := ((k + 1 : ℕ) : ℕ∞ω))
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
    ∃! G : ContMDiffRiemannianMetric 𝓘(ℝ, E) (k : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : X → Type _),
      (∀ a x, x ∈ (e a).source → ∀ v w : E,
        G.inner x v w = b a (e a x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e a) x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e a) x w)) ∧
      (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) :=
        ⟨G.toRiemannianMetric⟩
       IsRiemannianManifold 𝓘(ℝ, E) X) := by
  let := DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover e hcover
  let := DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover
    e hcover htrans
  let : IsManifold 𝓘(ℝ, E) 1 X := IsManifold.of_le (n := ((k + 1 : ℕ) : ℕ∞ω))
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  have hsub (a : α) : (e a).target ⊆ Metric.ball (0 : E) (R a) :=
    (htarget a).trans (Metric.ball_subset_ball (by linarith [hR a]))
  have hsymm : ∀ a x, x ∈ (e a).target → ∀ v w : E, b a x v w = b a x w v := by
    intro a x hx v w
    have he (v w : E) : Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w) := by
      fun_prop
    apply tendsto_nhds_unique ((he v w).tendsto _ |>.comp
      ((hconv a).tendsto_at (hsub a hx)))
    have hs := (he w v).tendsto _ |>.comp ((hconv a).tendsto_at (hsub a hx))
    exact hs.congr (fun i => (g i).symm (Φ a i x) _ _)
  have hpos : ∀ a x, x ∈ (e a).target → ∀ v : E, v ≠ 0 → 0 < b a x v v := by
    intro a x hx v hv
    have he : Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v v) := by fun_prop
    have hl := ge_of_tendsto ((he.tendsto _).comp ((hconv a).tendsto_at (hsub a hx)))
      ((hlower a).mono (fun i hi => hi x (hsub a hx) v))
    exact (mul_pos (hc a) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le hl
  obtain ⟨G, hG, huniq⟩ := exists_unique_contMDiffMetric_of_open_atlas e hcover k htrans b
    (fun a => (hb a).mono (hsub a)) hsymm hpos hcompat
  have he (a : α) : e a ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 X :=
    IsManifold.maximalAtlas_subset_of_le (n := ((k + 1 : ℕ) : ℕ∞ω))
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
      (IsManifold.subset_maximalAtlas (Set.mem_range_self a))
  refine ⟨G, ⟨hG, ?_⟩, fun G' hG' => huniq G' hG'.1⟩
  exact isRiemannianManifold_of_atlas_metric_limits hX k G e hcover he R hR htarget
    g hg Φ hΦ hΦinv hsource himage hrad b hb hconv c hc hlower hG o p A hε L hdom hmap hchart

end DifferentialGeometry.Geometry.Metric
