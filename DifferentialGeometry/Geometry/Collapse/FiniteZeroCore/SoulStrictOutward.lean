import DifferentialGeometry.Geometry.Comparison.Soul.SoulDiffeomorph
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# A soul with strict outward directions and its calibrated normal tube (LFR45, smooth carrier)

Frozen blueprint master207A, lemma `lem:collapse-finite-soul-separators` (LFR45, lines
28793–28882). For a complete connected noncompact manifold with `sec ≥ 0` there is one compact
connected boundaryless totally convex soul `S` of dimension `< dim M` such that

* (LFR45.1) for every `q ∉ S` there is a unit vector `v ∈ T_q M` with `g(v, u) < 0` for ALL unit
  minimizing directions `u` from `q` to `S` (all `u` with `|u| = 1` whose geodesic lies in `S` at
  time `d_S(q)`);
* there is a normal-tube radius `ε > 0` on which the normal exponential map
  `Φ : {|w| < ε} → {d_S < ε}` is a diffeomorphism fixing `S` with `d_S(Φ(s, w)) = |w|`.

This file proves the row for a SMOOTH metric, from the PC soul suite
(`exists_soul_set_with_radial_outward_field`, `exists_normal_tube`). The row itself is stated for
a metric of class `C^m`, `m ≥ 8`; that form needs geodesics and exponential maps of a finite-order
metric (the geodesic-flow clause of LFR01), which this tree does not have. A smooth metric is
`C^m` for every `m`, so the theorem below is the smooth-carrier special case, with the dimension
bound `dim S < dim M` in place of "at most two" (for `dim M = 3` this is `dim S ≤ 2`).
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] [SigmaCompactSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [CompleteSpace M]
  [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
/-- A vector that pairs negatively with one vector is a positive multiple of a unit vector with
the same sign pattern: normalization in `g`. -/
theorem exists_unit_of_inner_neg (g : SmoothRiemannianMetric I M) (q : M)
    (W u₀ : TangentSpace I q) (hW : g.inner q W u₀ < 0) :
    ∃ c : ℝ, 0 < c ∧ g.inner q (c • W) (c • W) = 1 := by
  have hCS := gInner_sq_le_mul g q W u₀
  have hWW : 0 < g.inner q W W := by
    by_contra hle
    push Not at hle
    have hnn : 0 ≤ g.inner q u₀ u₀ := gInner_self_nonneg g q u₀
    have h0 : g.inner q W W * g.inner q u₀ u₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hnn
    nlinarith [sq_pos_of_neg hW]
  refine ⟨(Real.sqrt (g.inner q W W))⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hWW), ?_⟩
  rw [gInner_smul_self, inv_pow, Real.sq_sqrt hWW.le, inv_mul_cancel₀ hWW.ne']

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
/-- **Kernel of (LFR45.1).** If for every small radius `r` some field is strictly outward on
`{d_S ≥ r/8}` against all unit minimizing directions to `S`, then at every `q ∉ S` one unit vector
is strictly outward against all of them. -/
theorem exists_unit_strict_outward_of_fields (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {S : Set M} (hSne : S.Nonempty)
    (hScomp : IsCompact S) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hfields : ∀ r : ℝ, 0 < r → r ≤ r₀ → ∃ W : (x : M) → TangentSpace I x,
      ∀ q : M, r / 8 ≤ infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
        intrinsicGeodesic g hEnorm q u (infDist q S) ∈ S → g.inner q (W q) u < 0)
    (q : M) (hq : q ∉ S) :
    ∃ v : TangentSpace I q, g.inner q v v = 1 ∧
      ∀ u : TangentSpace I q, g.inner q u u = 1 →
        intrinsicGeodesic g hEnorm q u (infDist q S) ∈ S → g.inner q v u < 0 := by
  have hpos : 0 < infDist q S := (hScomp.isClosed.notMem_iff_infDist_pos hSne).mp hq
  -- A field that is outward at `q`: take the radius `r = min r₀ (8 d_S(q))`.
  set r : ℝ := min r₀ (8 * infDist q S) with hr
  have hr0 : 0 < r := lt_min hr₀ (by positivity)
  have hq8 : r / 8 ≤ infDist q S := by
    have := min_le_right r₀ (8 * infDist q S)
    linarith
  obtain ⟨W, hWout⟩ := hfields r hr0 (min_le_left _ _)
  -- One unit minimizing direction from `q` to a nearest point of `S`.
  obtain ⟨n, hnS, hn⟩ := hScomp.exists_infDist_eq_dist hSne q
  have hqn : 0 < dist q n := by rw [← hn]; exact hpos
  obtain ⟨u₀, hu₀, hu₀n⟩ := soul_unit_minimizing_initial (I := I) g hEnorm q n hqn
  have hneg : g.inner q (W q) u₀ < 0 :=
    hWout q hq8 u₀ hu₀ (by rw [hn, hu₀n]; exact hnS)
  obtain ⟨c, hc, hcunit⟩ := exists_unit_of_inner_neg g q (W q) u₀ hneg
  refine ⟨c • W q, hcunit, fun u hu hend => ?_⟩
  have hWu := hWout q hq8 u hu hend
  have hlin : g.inner q (c • W q) u = c * g.inner q (W q) u := by
    rw [(g.inner q).map_smul]
    rfl
  rw [hlin]
  exact mul_neg_of_pos_of_neg hc hWu

/-- **LFR45 (smooth carrier).** One PC soul `S`, compact, path connected, totally convex, without
relative boundary and of dimension `< dim M`, with strict outward directions at every point off
`S` against ALL unit minimizing directions to `S`, and its calibrated normal tube. -/
theorem exists_soul_strict_outward_tube [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ (S : Set M) (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅),
      S.Nonempty ∧ IsCompact S ∧ PathConnectedSpace S ∧
      maxSliceDim I S < Module.finrank ℝ E ∧
      (∀ q : M, q ∉ S → ∃ v : TangentSpace I q, g.inner q v v = 1 ∧
        ∀ u : TangentSpace I q, g.inner q u u = 1 →
          intrinsicGeodesic g hEnorm q u (infDist q S) ∈ S → g.inner q v u < 0) ∧
      let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
      let _ := embeddedSliceChartedSpace hS
      let a := normalBundlePrebundle g hEnorm hconv hB
      let _ := a.totalSpaceTopology
      let _ := a.toFiberBundle
      let _ := a.toVectorBundle
      ∃ ε > 0, ∃ Φ : PartialDiffeomorph
          ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)) I
          (TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
            (normalBundleFiber g S)) M ∞,
        Φ.source = {z | Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) < ε} ∧
        Φ.target = {q | infDist q S < ε} ∧
        (Φ : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
            (normalBundleFiber g S) → M) = normalExp (I := I) g hEnorm S ∧
        (∀ s : S, (⟨s, 0⟩ : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
            (normalBundleFiber g S)) ∈ Φ.source ∧ Φ ⟨s, 0⟩ = s.1) ∧
        ∀ z ∈ Φ.source, Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) = infDist (Φ z) S := by
  classical
  obtain ⟨S, hSne, hScomp, hconv, hB, hdim, r₀, hr₀, -, -, hfields⟩ :=
    exists_soul_set_with_radial_outward_field g hEnorm hsec p
  refine ⟨S, hconv, hB, hSne, hScomp, IsTotallyConvex.pathConnectedSpace g hEnorm hconv hSne,
    hdim, ?_, exists_normal_tube g hEnorm hsec hSne hScomp hconv hB⟩
  exact exists_unit_strict_outward_of_fields g hEnorm hSne hScomp hr₀
    (fun r hr hrr₀ => by
      obtain ⟨V, -, -, hV⟩ := hfields r hr hrr₀
      exact ⟨fun x => V x, hV⟩)

end DifferentialGeometry.Geometry.Collapse
