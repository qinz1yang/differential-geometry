import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem riemannianEDistOf_exp_bounds_of_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b C s t : ℝ} (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (hRm : ∀ r ∈ Icc a b, ∀ x : M,
      normSq0S (I := I) (S.base.metric r) x 4 (S.base.rm04 r x) ≤ C)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x y : M) :
    ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|))) *
        riemannianEDistOf (S.base.metric t) x y ≤ riemannianEDistOf (S.base.metric s) x y ∧
      riemannianEDistOf (S.base.metric s) x y ≤
        ENNReal.ofReal (Real.exp
          ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|)) *
          riemannianEDistOf (S.base.metric t) x y := by
  have hpair := fun z v => metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular z
    (fun r hr => hRm r hr z) hs ht v
  have hlo := le_edistOf_of_quad (S.base.metric t) (S.base.metric s)
    (Real.exp_pos _) (fun z v => (hpair z v).1) x y
  have hhi := edistOf_le_of_quad (S.base.metric t) (S.base.metric s)
    (Real.exp_pos _) (fun z v => (hpair z v).2) x y
  rw [← Real.exp_half] at hlo hhi
  have hplus : 2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t| / 2 =
      (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t| := by ring
  have hminus : -(2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|) / 2 =
      -((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|) := by ring
  exact ⟨hminus ▸ hlo, hplus ▸ hhi⟩

theorem riemannianEDistOf_exp_bounds_on_terminal_ball
    (g : SmoothRiemannianMetric I M) (W : TopologicalSpace.Opens M)
    (S : SolutionOn (I := I) (M := W) D) (hS : IsSolutionOn S)
    {a b C t : ℝ} (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (hRm : ∀ r ∈ Icc a b, ∀ x : W,
      normSq0S (I := I) (S.base.metric r) x 4 (S.base.rm04 r x) ≤ C)
    (ht : t ∈ Icc a b) (hterminal : S.base.metric b = g.restrictOpen W)
    (p : W) {R : ℝ≥0} (hR : 0 < R)
    (hball : {x : M | riemannianEDistOf g p.val x < R} ⊆ W)
    (x : W) (hx : riemannianEDistOf g p.val x.val < (R / 3 : ℝ≥0)) :
    ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|))) *
        riemannianEDistOf g p.val x.val ≤ riemannianEDistOf (S.base.metric t) p x ∧
      riemannianEDistOf (S.base.metric t) p x ≤
        ENNReal.ofReal (Real.exp
          ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|)) *
          riemannianEDistOf g p.val x.val := by
  have hp : riemannianEDistOf g p.val p.val < (R / 3 : ℝ≥0) := by
    rw [riemannianEDistOf_self]
    exact_mod_cast (div_pos hR (by norm_num : (0 : ℝ≥0) < 3))
  have heq := Geometry.Metric.riemannianEDistOf_restrictOpen_eq_of_ball_subset
    g W p.val R hball p x hp hx
  have hd := riemannianEDistOf_exp_bounds_of_curvature_bound S hS hcarrier hregular hRm
    ht ⟨ht.1.trans ht.2, le_rfl⟩ p x
  rwa [hterminal, heq] at hd

theorem isCompact_intrinsic_closedBall_of_terminal_ball
    (g : SmoothRiemannianMetric I M) (W : TopologicalSpace.Opens M)
    (S : SolutionOn (I := I) (M := W) D) (hS : IsSolutionOn S)
    {a b C t : ℝ} (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (hRm : ∀ u ∈ Icc a b, ∀ x : W,
      normSq0S (I := I) (S.base.metric u) x 4 (S.base.rm04 u x) ≤ C)
    (ht : t ∈ Icc a b) (hterminal : S.base.metric b = g.restrictOpen W)
    (p : W) {r R : ℝ≥0}
    (hcompact : IsCompact {x : M | riemannianEDistOf g p.val x ≤ R})
    (hball : {x : M | riemannianEDistOf g p.val x ≤ R} ⊆ W)
    (hfit : ENNReal.ofReal (Real.exp
      ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|)) * (r : ℝ≥0∞) ≤ R) :
    IsCompact {x : W | riemannianEDistOf (S.base.metric t) p x ≤ r} := by
  let K : Set W := {x | riemannianEDistOf g p.val x.val ≤ R}
  have himage : Subtype.val '' K = {x : M | riemannianEDistOf g p.val x ≤ R} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hball hx⟩, hx, rfl⟩
  have hK : IsCompact K := by
    rw [_root_.Topology.IsEmbedding.isCompact_iff
      (_root_.Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ W))]
    exact himage ▸ hcompact
  have hclosed : IsClosed {x : W | riemannianEDistOf (S.base.metric t) p x ≤ r} := by
    apply isClosed_le ?_ continuous_const
    unfold riemannianEDistOf
    exact Geometry.Riemannian.continuous_riemannianEDist (S.base.metric t) p
  apply hK.of_isClosed_subset hclosed
  intro x hx
  have hbound := (riemannianEDistOf_exp_bounds_of_curvature_bound S hS hcarrier hregular hRm
    (show b ∈ Icc a b from ⟨ht.1.trans ht.2, le_rfl⟩) ht p x).2
  rw [hterminal, abs_sub_comm b t] at hbound
  have hmul : ENNReal.ofReal (Real.exp
      ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|)) *
      riemannianEDistOf (S.base.metric t) p x ≤
      ENNReal.ofReal (Real.exp
        ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|)) * (r : ℝ≥0∞) :=
    mul_le_mul_right hx _
  exact (DifferentialGeometry.riemannianEDistOf_le_restrictOpen g W p x).trans
    (hbound.trans (hmul.trans hfit))

end DifferentialGeometry.PDE.RicciFlow
