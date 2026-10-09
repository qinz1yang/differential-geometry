import DifferentialGeometry.Geometry.Collapse.SublevelCore.CommonOutwardDirection
import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformCollar
import DifferentialGeometry.Bundle.Section

/-!
# A bounded smooth field outward for both distances (LC53)

Frozen blueprint master207A, lemma `lem:collapse-common-outward-field` (LC53, lines 22784–22832).
On a complete connected manifold with `sec ≥ 0`, for a point `p` and a compact set `S` there are
`0 < A₀ < A₁` and a global smooth vector field `X` with `|X| < 2`, `X = 0` on the closed ball
`B̄(p, A₀) ⊇ S`, and `g(X, v) ≤ -1/4` at every `q` with `d(p, q) ≥ A₁` for EVERY inward unit
direction `v` minimizing the distance to `p` and EVERY one realizing the distance to `S`, including
points in either cut locus.

The proof is the PC convex-section patching of `exists_smooth_outward_field_at_infinity`
(`Soul/SoulAngles.lean`) with two families of half-space constraints: the local fields come from
LC52 (`exists_common_outward_direction`) and the fixed-metric openness lemma
`eventually_infDist_minimizing_inner_lt` (`Soul/DistanceField.lean`), applied to `{p}` and to `S`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The point family `𝒰_p(q)` is the closed-set family `minimizingDirectionsTo {p}`. -/
theorem mem_inwardMinimizingDirections_iff_mem_minimizingDirectionsTo
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p q : M} {v : TangentSpace I q} :
    v ∈ inwardMinimizingDirections (I := I) g hEnorm p q ↔
      v ∈ minimizingDirectionsTo (I := I) g hEnorm {p} q := by
  rw [mem_inwardMinimizingDirections]
  change _ ↔ g.inner q v v = 1 ∧ intrinsicGeodesic (I := I) g hEnorm q v (infDist q {p}) ∈ {p}
  rw [infDist_singleton, mem_singleton_iff, dist_comm]

variable [ConnectedSpace M]

/-- **LC53.** A global smooth field, bounded by `2`, vanishing on `B̄(p, A₀) ⊇ S`, with margin
`-1/4` against every inward unit minimizing direction to `p` and every inward unit direction
realizing the distance to `S`, at every point with `d(p, q) ≥ A₁`. -/
theorem exists_smooth_outward_field_two_targets
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) {S : Set M} (hS : IsCompact S) :
    ∃ A₀ A₁ : ℝ, 0 < A₀ ∧ A₀ < A₁ ∧ S ⊆ ball p A₀ ∧
      ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
        (∀ q, g.inner q (X q) (X q) < 4) ∧ (∀ q, dist p q ≤ A₀ → X q = 0) ∧
        ∀ q, A₁ ≤ dist p q → ∀ v ∈ inwardMinimizingDirections (I := I) g hEnorm p q ∪
            minimizingDirectionsTo (I := I) g hEnorm S q,
          g.inner q (X q) v ≤ -(1 / 4) := by
  classical
  obtain ⟨A, hA, hout⟩ := exists_common_outward_direction (I := I) g hEnorm hsec p hS
  obtain ⟨D, hD⟩ := hS.isBounded.subset_closedBall p
  set A₀ : ℝ := max A (D + 1) with hA₀def
  set A₁ : ℝ := A₀ + 1 with hA₁def
  have hA₀ : 0 < A₀ := lt_max_of_lt_left hA
  have hAA₀ : A ≤ A₀ := le_max_left _ _
  have hA₀₁ : A₀ < A₁ := by simp only [hA₁def]; linarith
  have hSball : S ⊆ ball p A₀ := by
    intro s hs
    have := hD hs
    rw [mem_closedBall] at this
    rw [mem_ball]
    linarith [le_max_right A (D + 1)]
  have hSclosed : IsClosed S := hS.isClosed
  let U : (q : M) → Set (TangentSpace I q) := fun q =>
    inwardMinimizingDirections (I := I) g hEnorm p q ∪ minimizingDirectionsTo (I := I) g hEnorm S q
  let t : (q : M) → Set (TangentSpace I q) := fun q =>
    {w | g.inner q w w < 4 ∧ (dist p q ≤ A₀ → w = 0) ∧
      (A₁ ≤ dist p q → ∀ v ∈ U q, g.inner q w v ≤ -(1 / 4 : ℝ))}
  have ht (q : M) : Convex ℝ (t q) := by
    intro x hx y hy a b ha hb hab
    have hid : g.inner q (a • x + b • y) (a • x + b • y) =
        (a + b) * (a * g.inner q x x + b * g.inner q y y) -
          a * b * g.inner q (x - y) (x - y) := by
      simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul,
        map_sub, sub_apply, g.symm q y x]
      ring
    have hpos := mul_nonneg (mul_nonneg ha hb) (gInner_self_nonneg (I := I) g q (x - y))
    have hbound : a * g.inner q x x + b * g.inner q y y < 4 := by
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hy.1
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hax := mul_lt_mul_of_pos_left hx.1 hap
        have hby := mul_le_mul_of_nonneg_left hy.1.le hb
        nlinarith only [hax, hby, hab]
    refine ⟨?_, ?_, ?_⟩
    · rw [hid, hab, one_mul]
      linarith
    · intro hq
      rw [hx.2.1 hq, hy.2.1 hq, smul_zero, smul_zero, add_zero]
    · intro hq v hv
      have hax := mul_le_mul_of_nonneg_left (hx.2.2 hq v hv) ha
      have hby := mul_le_mul_of_nonneg_left (hy.2.2 hq v hv) hb
      simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul]
      nlinarith only [hax, hby, hab]
  have hloc (q : M) : ∃ V ∈ 𝓝 q, ∃ W : (y : M) → TangentSpace I y,
      ContMDiffOn I I.tangent ∞ (fun y => (⟨y, W y⟩ : TangentBundle I M)) V ∧
      ∀ y ∈ V, W y ∈ t y := by
    by_cases hq : dist p q < A₁
    · have hmem : q ∈ ball p A₁ := by simpa only [mem_ball, dist_comm] using hq
      refine ⟨ball p A₁, isOpen_ball.mem_nhds hmem, fun _ => 0,
        (0 : Cₛ^∞⟮I; E, TangentSpace I⟯).contMDiff.contMDiffOn, ?_⟩
      intro y hy
      have hyd : dist p y < A₁ := by simpa only [mem_ball, dist_comm] using hy
      refine ⟨by simp, fun _ => rfl, ?_⟩
      intro hfar
      exact ((not_le_of_gt hyd) hfar).elim
    · have hfar : A₀ < dist p q := hA₀₁.trans_le (le_of_not_gt hq)
      obtain ⟨w₀, hw₀, hw₀v⟩ := hout q (hAA₀.trans hfar.le)
      obtain ⟨W, hWq⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (n := ⊤) q w₀
      have hpoint := eventually_infDist_minimizing_inner_lt (I := I) g hEnorm
        (isClosed_singleton : IsClosed ({p} : Set M)) q W W.contMDiff.continuous (-(1 / 4 : ℝ))
        (by
          intro u hu hup
          rw [hWq]
          exact (hw₀v u (Or.inl
            (mem_inwardMinimizingDirections_iff_mem_minimizingDirectionsTo.mpr ⟨hu, hup⟩))).trans
            (by norm_num))
      have hset := eventually_infDist_minimizing_inner_lt (I := I) g hEnorm hSclosed q W
        W.contMDiff.continuous (-(1 / 4 : ℝ))
        (by
          intro u hu hup
          rw [hWq]
          exact (hw₀v u (Or.inr ⟨hu, hup⟩)).trans (by norm_num))
      have hnorm : ∀ᶠ y in 𝓝 q, g.inner y (W y) (W y) < 4 :=
        ((continuousOn_metric_inner (I := I) (b := id) g W.contMDiff.continuous.continuousOn
          W.contMDiff.continuous.continuousOn).continuousAt univ_mem).eventually
          (gt_mem_nhds (by simp only [id_eq]; rw [hWq, hw₀]; norm_num))
      have houter : ∀ᶠ y in 𝓝 q, A₀ < dist p y :=
        (continuous_const.dist continuous_id).continuousAt (lt_mem_nhds hfar)
      refine ⟨_, hpoint.and (hset.and (hnorm.and houter)), W, W.contMDiff.contMDiffOn, ?_⟩
      intro y hy
      refine ⟨hy.2.2.1, fun hle => ((not_lt_of_ge hle) hy.2.2.2).elim, ?_⟩
      intro _ v hv
      rcases hv with hvp | hvS
      · have hv' := mem_inwardMinimizingDirections_iff_mem_minimizingDirectionsTo.mp hvp
        exact (hy.1 v hv'.1 hv'.2).le
      · exact (hy.2.1 v hvS.1 hvS.2).le
  obtain ⟨X, hX⟩ := exists_contMDiffSection_forall_mem_convex_of_local I
    (TangentSpace I) t ht hloc
  exact ⟨A₀, A₁, hA₀, hA₀₁, hSball, X, fun q => (hX q).1, fun q => (hX q).2.1,
    fun q => (hX q).2.2⟩

end DifferentialGeometry.Geometry.Collapse
