import DifferentialGeometry.Geometry.Comparison.Soul.SoulExists
import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteHinge

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem metricDistance (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

private theorem acute_hinge_distance_lt {d l b c : ℝ} (hd : 0 ≤ d) (hl : 0 < l)
    (hb : 0 < b) (hsmall : b < 2 * l * c)
    (hhinge : d ^ 2 ≤ l ^ 2 + b ^ 2 - 2 * l * b * c) : d < l := by
  have hprod := mul_pos hb (sub_pos.2 hsmall)
  nlinarith only [hhinge, hprod, hd, hl]

omit [T2Space (TangentBundle I M)] in
private theorem nearest_inner_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {S : Set M} {p q : M} {u v : TangentSpace I p} {l : ℝ}
    (hl : 0 < l) (hu : g.inner p u u = 1) (hv : g.inner p v v = 1)
    (hend : intrinsicGeodesic g hEnorm p u l = q) (hmin : dist p q = l)
    (hnearest : Metric.infDist q S = l)
    (hvS : ∀ᶠ t in 𝓝[>] (0 : ℝ), intrinsicGeodesic g hEnorm p v t ∈ S) :
    g.inner p u v ≤ 0 := by
  by_contra h
  have hpos : 0 < g.inner p u v := lt_of_not_ge h
  have hthr : 0 < 2 * l * g.inner p u v := by positivity
  obtain ⟨b, hbS, hb⟩ := (hvS.and (Ioo_mem_nhdsGT hthr)).exists
  have hmin' : (riemannianEDist I p (intrinsicGeodesic g hEnorm p u l)).toReal = l := by
    rw [metricDistance, hend, hmin]
  have hh := complete_hinge_sq g hEnorm hsec p u v l b hl hb.1 hu hv hmin'
  rw [metricDistance, hend] at hh
  have hlt := acute_hinge_distance_lt dist_nonneg hl hb.1 hb.2 hh
  have hle : l ≤ dist q (intrinsicGeodesic g hEnorm p v b) := by
    rw [← hnearest]
    exact Metric.infDist_le_dist_of_mem hbS
  exact (not_lt_of_ge hle) hlt

theorem nearest_geodesic_inner_eq_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {S : Set M} (hSconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅)
    {p q : M} (hp : p ∈ S) {u : TangentSpace I p} {l : ℝ} (hl : 0 < l)
    (hu : g.inner p u u = 1) (hend : intrinsicGeodesic g hEnorm p u l = q)
    (hmin : dist p q = l) (hnearest : Metric.infDist q S = l)
    {w : TangentSpace I p} (hw : w ∈ sliceTangent I S p) : g.inner p u w = 0 := by
  by_cases hw0 : w = 0
  · rw [hw0, map_zero]
  let r := Real.sqrt (g.inner p w w)
  have hr : 0 < r := Real.sqrt_pos.2 (g.pos p w hw0)
  let v := r⁻¹ • w
  have hv : g.inner p v v = 1 := by
    rw [gInner_smul_self (I := I) g p r⁻¹ w,
      ← Real.sq_sqrt (gInner_self_nonneg (I := I) g p w), inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
  have hvT : v ∈ sliceTangent I S p := (sliceTangent I S p).smul_mem r⁻¹ hw
  have hinner (z : TangentSpace I p) (hz : z ∈ sliceTangent I S p) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), intrinsicGeodesic g hEnorm p z t ∈ S := by
    have hzI := (isInnerDirection_iff_mem_sliceTangent_of_relBoundary_eq_empty
      hEnorm hSconv hB hp).2 hz
    have hzN := isInnerDirection_iff.mp hzI
    exact hzN.mono (fun _ ht => maxSliceLocus_subset ht)
  have hle := nearest_inner_nonpos g hEnorm hsec hl hu hv hend hmin hnearest (hinner v hvT)
  have hvneg : g.inner p (-v) (-v) = 1 := by
    simpa only [map_neg, neg_apply, neg_neg] using hv
  have hneg := nearest_inner_nonpos g hEnorm hsec hl hu hvneg hend hmin hnearest
    (hinner (-v) ((sliceTangent I S p).neg_mem hvT))
  rw [(g.inner p u).map_neg] at hneg
  have heq : g.inner p u v = 0 := le_antisymm hle (neg_nonpos.1 hneg)
  change g.inner p u (r⁻¹ • w) = 0 at heq
  rw [(g.inner p u).map_smul, smul_eq_mul] at heq
  exact (mul_eq_zero.mp heq).resolve_left (inv_ne_zero hr.ne')

theorem exists_minimizing_normal_exp
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {S : Set M} (hSne : S.Nonempty) (hScomp : IsCompact S)
    (hSconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅) (q : M) :
    ∃ p ∈ S, ∃ v : TangentSpace I p, expMapIntrinsic g hEnorm p v = q ∧
      g.inner p v v = (Metric.infDist q S) ^ 2 ∧
      ∀ w ∈ sliceTangent I S p, g.inner p v w = 0 := by
  by_cases hq : q ∈ S
  · refine ⟨q, hq, 0, ?_, ?_, ?_⟩
    · exact expMapIntrinsic_zero g hEnorm q
    · simp only [map_zero, Metric.infDist_zero_of_mem hq, zero_pow (by decide : 2 ≠ 0)]
    · intro w _
      rw [map_zero, zero_apply]
  have hd : 0 < Metric.infDist q S := (hScomp.isClosed.notMem_iff_infDist_pos hSne).1 hq
  obtain ⟨p, hp, hdist⟩ := hScomp.exists_infDist_eq_dist hSne q
  have hpq : dist p q = Metric.infDist q S := by rw [dist_comm, hdist]
  obtain ⟨u, hu, hend⟩ := soul_unit_minimizing_initial g hEnorm p q (hpq.symm ▸ hd)
  have hend' : intrinsicGeodesic g hEnorm p u (Metric.infDist q S) = q := by
    rwa [hpq] at hend
  refine ⟨p, hp, Metric.infDist q S • u, ?_, ?_, ?_⟩
  · simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hend'
  · rw [gInner_smul_self (I := I), hu, mul_one]
  · intro w hw
    have hnormal := nearest_geodesic_inner_eq_zero g hEnorm hsec hSconv hB hp hd hu hend' hpq rfl hw
    rw [map_smul, _root_.smul_apply, smul_eq_mul, hnormal, mul_zero]

end DifferentialGeometry.Geometry.Topology
