import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

section Metric

variable {X : Type*} [MetricSpace X]

theorem exists_nearest_superlevel
    (F : X → ℝ) (hF : Continuous F) (hC : IsCompact {z : X | 0 ≤ F z})
    {s : ℝ} (hs : 0 ≤ s) (q : X) (hq : s ≤ F q) (x : X) :
    ∃ y : X, s ≤ F y ∧ IsMinOn (dist x) {z : X | s ≤ F z} y := by
  have hK : IsCompact {z : X | s ≤ F z} :=
    hC.of_isClosed_subset (isClosed_le continuous_const hF) (fun _ hz => hs.trans hz)
  exact hK.exists_isMinOn ⟨q, hq⟩ (continuous_const.dist continuous_id).continuousOn

end Metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem exists_intrinsic_segment_dist_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p q : M) :
    ∃ v : TangentSpace I p, intrinsicGeodesic g hEnorm p v 1 = q ∧
      ∀ t : ℝ, 0 ≤ t →
        dist p (intrinsicGeodesic g hEnorm p v t) ≤ dist p q * t := by
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm p q (by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q)
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] at hlen
  refine ⟨v, hv, ?_⟩
  intro t ht
  have h := intrinsicGeodesic_riemannianEDist_le g hEnorm p v ht
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    intrinsicGeodesic_zero, sub_zero, hlen] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg dist_nonneg ht)).mp h

theorem nearest_superlevel_eq_level
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {F : M → ℝ} (hF : Continuous F) {r s : ℝ} {x y : M}
    (hx : F x = r) (hrs : r < s) (hy : s ≤ F y)
    (hnearest : IsMinOn (dist x) {z : M | s ≤ F z} y) :
    F y = s := by
  apply le_antisymm ?_ hy
  by_contra hnot
  have hys : s < F y := lt_of_not_ge hnot
  have hxy : x ≠ y := by
    intro heq
    have hFy : F y = r := heq ▸ hx
    linarith
  have hdpos : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨v, hone, hdist⟩ := exists_intrinsic_segment_dist_le g hEnorm x y
  have hcont : Continuous (fun t : ℝ => F (intrinsicGeodesic g hEnorm x v t)) :=
    hF.comp (intrinsicGeodesic_continuous g hEnorm x v)
  have hs : s ∈ Ioo (F (intrinsicGeodesic g hEnorm x v 0))
      (F (intrinsicGeodesic g hEnorm x v 1)) := by
    rw [intrinsicGeodesic_zero, hone, hx]
    exact ⟨hrs, hys⟩
  obtain ⟨t, ht, hFt⟩ :=
    intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn hs
  have hnear : dist x y ≤ dist x (intrinsicGeodesic g hEnorm x v t) :=
    (isMinOn_iff.mp hnearest) _ hFt.ge
  have hstrict : dist x (intrinsicGeodesic g hEnorm x v t) < dist x y :=
    (hdist t ht.1.le).trans_lt (by
      nlinarith [mul_pos hdpos (sub_pos.mpr ht.2)])
  exact (not_lt_of_ge hnear) hstrict

theorem nearest_superlevel_dist_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (F : M → ℝ)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ F z})
    {r s T m : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hsT : s ≤ T) (hTm : T < m)
    (q : M) (hq : F q = m) {x y : M} (hx : F x = r)
    (hnearest : IsMinOn (dist x) {z : M | s ≤ F z} y) :
    dist x y ≤ Metric.diam {z : M | 0 ≤ F z} / (m - T) * (s - r) := by
  have hrm : r < m := (hrs.trans_le hsT).trans hTm
  have hmr : 0 < m - r := sub_pos.mpr hrm
  have hmt : 0 < m - T := sub_pos.mpr hTm
  have hsr : 0 ≤ s - r := sub_nonneg.mpr hrs.le
  let theta : ℝ := (s - r) / (m - r)
  have htheta : 0 ≤ theta := div_nonneg hsr hmr.le
  have hthetaone : theta ≤ 1 := (div_le_one₀ hmr).mpr (by linarith)
  obtain ⟨v, hone, hdist⟩ := exists_intrinsic_segment_dist_le g hEnorm x q
  have hconctheta := (hconc x v).2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr hthetaone) htheta (by ring : (1 - theta) + theta = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, intrinsicGeodesic_zero,
    hone, hx, hq] at hconctheta
  have hcomb : (1 - theta) * r + theta * m = s := by
    dsimp only [theta]
    field_simp [hmr.ne']
    ring
  have hlevel : s ≤ F (intrinsicGeodesic g hEnorm x v theta) := by
    rwa [hcomb] at hconctheta
  have hxC : x ∈ {z : M | 0 ≤ F z} := by simpa only [mem_ofPred_eq, hx] using hr
  have hqC : q ∈ {z : M | 0 ≤ F z} := by
    change 0 ≤ F q
    rw [hq]
    linarith
  have hdiam : dist x q ≤ Metric.diam {z : M | 0 ≤ F z} :=
    Metric.dist_le_diam_of_mem hC.isBounded hxC hqC
  have hthetabound : theta ≤ (s - r) / (m - T) :=
    div_le_div_of_nonneg_left hsr hmt (by linarith)
  calc
    dist x y ≤ dist x (intrinsicGeodesic g hEnorm x v theta) :=
      (isMinOn_iff.mp hnearest) _ hlevel
    _ ≤ dist x q * theta := hdist theta htheta
    _ ≤ Metric.diam {z : M | 0 ≤ F z} * theta := mul_le_mul_of_nonneg_right hdiam htheta
    _ ≤ Metric.diam {z : M | 0 ≤ F z} * ((s - r) / (m - T)) :=
      mul_le_mul_of_nonneg_left hthetabound Metric.diam_nonneg
    _ = Metric.diam {z : M | 0 ≤ F z} / (m - T) * (s - r) := by ring

theorem exists_nearest_superlevel_exact_level
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (F : M → ℝ) (hF : Continuous F) (hC : IsCompact {z : M | 0 ≤ F z})
    {r s m : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hsm : s ≤ m)
    (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)
    (x : M) (hx : F x = r) :
    ∃ y : M, F y = s ∧ IsMinOn (dist x) {z : M | s ≤ F z} y := by
  obtain ⟨q, hq, _hmax⟩ := hmax
  obtain ⟨y, hy, hnearest⟩ := exists_nearest_superlevel F hF hC
    (hr.trans hrs.le) q (by simpa only [hq] using hsm) x
  exact ⟨y, nearest_superlevel_eq_level g hEnorm hF hx hrs hy hnearest, hnearest⟩

theorem exists_nearest_superlevel_step
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (F : M → ℝ) (hF : Continuous F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ F z})
    {r s T m : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hsT : s ≤ T) (hTm : T < m)
    (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)
    (x : M) (hx : F x = r) :
    ∃ y : M, F y = s ∧ IsMinOn (dist x) {z : M | s ≤ F z} y ∧
      dist x y ≤ Metric.diam {z : M | 0 ≤ F z} / (m - T) * (s - r) := by
  obtain ⟨y, hy, hnearest⟩ := exists_nearest_superlevel_exact_level g hEnorm F hF hC
    hr hrs (hsT.trans hTm.le) hmax x hx
  obtain ⟨q, hq, _hmax⟩ := hmax
  exact ⟨y, hy, hnearest,
    nearest_superlevel_dist_le g hEnorm F hconc hC hr hrs hsT hTm q hq hx hnearest⟩

end DifferentialGeometry.Geometry.Topology

end
