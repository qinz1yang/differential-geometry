import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Analysis.TimeInterval
import DifferentialGeometry.Geometry.Metric.Family.Basic
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.TimeSlab
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local instance terminalCarrierC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] in
theorem metricFamily_uniform_comparison_on_compact_carrier
    {D : RealTimeInterval} (G : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) D G)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ D.carrier)
    (gRef : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ t ∈ J, ∀ x ∈ K, ∀ v : TangentSpace I x,
      gRef.inner x v v ≤ L ^ 2 * (G t).inner x v v ∧
      (G t).inner x v v ≤ L ^ 2 * gRef.inner x v v := by
  classical
  let P := {t : ℝ // t ∈ J} × MetricUnitTangent (I := I) gRef
  let Q : Set P := Set.univ ×ˢ {v : MetricUnitTangent (I := I) gRef |
    MetricUnitTangent.base v ∈ K}
  let f : P → ℝ := metricUnitTimeSlabRefQuad G J gRef
  have hf : Continuous f := metricUnitTimeSlabRefQuad_cont_of_bundle G J gRef
    (metricTimeBundleQuad_cont_of_metricFamilySmoothOn G hG hJD)
  have hpos (q : P) : 0 < f q := metricUnitTimeSlabRefQuad_pos G J gRef q
  have hc : IsCompact Q := by
    have : CompactSpace {t : ℝ // t ∈ J} := isCompact_iff_compactSpace.mp hJ
    exact isCompact_univ.prod (metricUnitOn_compact gRef hK)
  obtain ⟨B₁, hB₁⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨B₂, hB₂⟩ := hc.exists_bound_of_continuousOn
    (hf.inv₀ (fun q => (hpos q).ne')).continuousOn
  let L := |B₁| + |B₂| + 1
  have hL : 1 ≤ L := by dsimp [L]; linarith [abs_nonneg B₁, abs_nonneg B₂]
  have hB₁L : B₁ ≤ L ^ 2 := by
    have hB : B₁ ≤ L := by dsimp [L]; linarith [le_abs_self B₁, abs_nonneg B₂]
    nlinarith [sq_nonneg (L - 1)]
  have hB₂L : B₂ ≤ L ^ 2 := by
    have hB : B₂ ≤ L := by dsimp [L]; linarith [le_abs_self B₂, abs_nonneg B₁]
    nlinarith [sq_nonneg (L - 1)]
  refine ⟨L, hL, ?_⟩
  intro t ht x hx v
  by_cases hv : v = 0
  · subst v
    simp
  have hvpos : 0 < gRef.inner x v v := gRef.pos x v hv
  let r := Real.sqrt (gRef.inner x v v)
  have hr : 0 < r := Real.sqrt_pos.mpr hvpos
  have hrsq : r ^ 2 = gRef.inner x v v := Real.sq_sqrt hvpos.le
  let u : TangentSpace I x := r⁻¹ • v
  have hunit : gRef.inner x u u = 1 := by
    dsimp [u]
    rw [metric_smul2]
    rw [← hrsq]
    field_simp [hr.ne']
  let q : P := (⟨t, ht⟩, ⟨(⟨x, u⟩ : TangentBundle I M), hunit⟩)
  have hq : q ∈ Q := ⟨Set.mem_univ _, hx⟩
  have hfB₁ : |f q| ≤ B₁ := by simpa only [Real.norm_eq_abs] using hB₁ q hq
  have hfB₂ : |(f q)⁻¹| ≤ B₂ := by
    simpa only [Real.norm_eq_abs, Pi.inv_apply] using hB₂ q hq
  have hfupper : f q ≤ L ^ 2 := (le_abs_self _).trans (hfB₁.trans hB₁L)
  have hinv : (f q)⁻¹ ≤ L ^ 2 := (le_abs_self _).trans (hfB₂.trans hB₂L)
  have hflower : 1 ≤ L ^ 2 * f q := by
    have hh := mul_le_mul_of_nonneg_right hinv (hpos q).le
    simpa only [inv_mul_cancel₀ (hpos q).ne'] using hh
  have hscale : r ^ 2 * f q = (G t).inner x v v := by
    change r ^ 2 * (G t).inner x u u = _
    dsimp [u]
    rw [metric_smul2]
    field_simp [hr.ne']
  constructor
  · calc
      gRef.inner x v v = r ^ 2 := hrsq.symm
      _ ≤ r ^ 2 * (L ^ 2 * f q) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hflower (sq_nonneg r)
      _ = L ^ 2 * (G t).inner x v v := by rw [mul_left_comm, hscale]
  · calc
      (G t).inner x v v = r ^ 2 * f q := hscale.symm
      _ ≤ r ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left hfupper (sq_nonneg r)
      _ = L ^ 2 * gRef.inner x v v := by rw [mul_comm, hrsq]

theorem solution_compact_carrier_metric_curvature_bounds
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hslab : Set.Icc a b ⊆ D.carrier)
    (gRef : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) :
    ∃ L C : ℝ, 1 ≤ L ∧ 0 < C ∧
      (∀ t ∈ Set.Icc a b, ∀ x ∈ K, ∀ v : TangentSpace I x,
        gRef.inner x v v ≤ L ^ 2 * (S.base.metric t).inner x v v ∧
        (S.base.metric t).inner x v v ≤ L ^ 2 * gRef.inner x v v) ∧
      ∀ t ∈ Set.Icc a b, ∀ x ∈ K,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C ^ 2 := by
  obtain ⟨L, hL, heq⟩ := metricFamily_uniform_comparison_on_compact_carrier
    S.base.metric hS.smoothMetric isCompact_Icc hslab gRef hK
  let P := {t : ℝ // t ∈ Set.Icc a b} × M
  have hRm : tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
      (Set.Icc a b) (fun t x => S.base.rm04 t x) :=
    tensor0SFamilyContinuousOnSet.mono (I := I) (M := M) hS.rm04Cont hslab
  have hcont := (normSq0S_total_cont (I := I) gRef (s := 4)).comp hRm
  have hcpt : IsCompact (Set.univ ×ˢ K : Set P) := isCompact_univ.prod hK
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuousOn hcont.continuousOn
  let C := (L ^ 2) ^ 4 * max B 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨L, C, hL, hC, heq, ?_⟩
  intro t ht x hx
  have hfixedB : |normSq0S (I := I) gRef x 4 (S.base.rm04 t x)| ≤ B := by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using
      hB (⟨t, ht⟩, x) ⟨Set.mem_univ _, hx⟩
  have hfixed : normSq0S (I := I) gRef x 4 (S.base.rm04 t x) ≤ max B 0 :=
    (le_abs_self _).trans (hfixedB.trans (le_max_left _ _))
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hLpos : 0 < L ^ 2 := lt_of_lt_of_le zero_lt_one hLsq
  have hcompare := normSq0S_upper_le_of_equiv (I := I)
    gRef (S.base.metric t) x 4 hLsq (fun v => ⟨by
      rw [inv_mul_le_iff₀ hLpos]
      exact (heq t ht x hx v).1, (heq t ht x hx v).2⟩) (S.base.rm04 t x)
  have hbound := hcompare.trans (mul_le_mul_of_nonneg_left hfixed (by positivity))
  have hnonneg : 0 ≤ (L ^ 2) ^ 4 * max B 0 := by positivity
  dsimp [C]
  nlinarith [sq_nonneg ((L ^ 2) ^ 4 * max B 0)]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
