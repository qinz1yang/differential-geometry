import DifferentialGeometry.Geometry.Comparison.Soul.TubeDistance
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem gradient_infDist_eq_unit_curve_velocity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hq : 0 < Metric.infDist (γ t) S)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => Metric.infDist x S) (γ t))
    (hunit : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1)
    (hderiv : HasDerivAt (fun s => Metric.infDist (γ s) S) 1 t) :
    gradientFun g (fun x => Metric.infDist x S) (γ t) =
      mfderiv 𝓘(ℝ, ℝ) I γ t 1 := by
  let G := gradientFun g (fun x => Metric.infDist x S) (γ t)
  let w := mfderiv 𝓘(ℝ, ℝ) I γ t 1
  have hGG : g.inner (γ t) G G = 1 :=
    gradient_infDist_normSq_eq_one g hEnorm hS hSne hq hd
  have hcomp := hasDerivAt_comp_mfderiv_along I (fun x => Metric.infDist x S) γ t hd hγ
  have heq := hcomp.unique hderiv
  change mvfderiv (I := I) (fun x => Metric.infDist x S) (γ t)
    (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 1 at heq
  have hGw : g.inner (γ t) G w = 1 := by
    dsimp only [G, w]
    rw [inner_gradientFun]
    convert! heq using 1
  have hwG : g.inner (γ t) w G = 1 := (g.symm (γ t) w G).trans hGw
  have hww : g.inner (γ t) w w = 1 := hunit
  have hz : g.inner (γ t) (G - w) (G - w) = 0 := by
    simp only [map_sub, sub_apply, hGG, hGw, hwG, hww]
    norm_num
  have hequal : G - w = 0 := by
    by_contra h
    exact (g.pos (γ t) (G - w) h).ne' hz
  exact sub_eq_zero.mp hequal

theorem isMIntegralCurveOn_intrinsicGeodesic_of_infDist
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (p : M) (v : TangentSpace I p) (hv : g.inner p v v = 1)
    {a b : ℝ} (ha : 0 ≤ a)
    (hd : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => Metric.infDist q S)
      {q | a < Metric.infDist q S ∧ Metric.infDist q S < b})
    (hcal : ∀ t ∈ Ioo a b, Metric.infDist (intrinsicGeodesic g hEnorm p v t) S = t)
    (V : (q : M) → TangentSpace I q)
    (hV : ∀ q, a < Metric.infDist q S → Metric.infDist q S < b →
      V q = gradientFun g (fun x => Metric.infDist x S) q) :
    IsMIntegralCurveOn (intrinsicGeodesic g hEnorm p v) V (Ioo a b) := by
  let γ := intrinsicGeodesic g hEnorm p v
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff g hEnorm p v
  have hU : IsOpen {q : M | a < Metric.infDist q S ∧ Metric.infDist q S < b} :=
    (isOpen_lt continuous_const (Metric.continuous_infDist_pt S)).inter
      (isOpen_lt (Metric.continuous_infDist_pt S) continuous_const)
  intro t ht
  have hqt : a < Metric.infDist (γ t) S ∧ Metric.infDist (γ t) S < b := by
    rw [hcal t ht]
    exact ht
  have hdt := ((hd (γ t) hqt).contMDiffAt (hU.mem_nhds hqt)).mdifferentiableAt (by simp)
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    hγ.contMDiffAt.mdifferentiableAt (by simp)
  have hderiv : HasDerivAt (fun s => Metric.infDist (γ s) S) 1 t := by
    have heq : (fun s => Metric.infDist (γ s) S) =ᶠ[𝓝 t] (fun s => s) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hcal s hs
    exact (hasDerivAt_id t).congr_of_eventuallyEq heq
  have hgrad := gradient_infDist_eq_unit_curve_velocity g hEnorm hS hSne hγt
    (ha.trans_lt hqt.1) hdt ((intrinsicGeodesic_speedSq_eq g hEnorm p v t).trans hv) hderiv
  have heq : mfderiv 𝓘(ℝ, ℝ) I γ t = (1 : ℝ →L[ℝ] ℝ).smulRight (V (γ t)) := by
    apply ContinuousLinearMap.ext
    intro u
    change ℝ at u
    calc
      mfderiv 𝓘(ℝ, ℝ) I γ t u = mfderiv 𝓘(ℝ, ℝ) I γ t (u • (1 : ℝ)) := by
        rw [smul_eq_mul, mul_one]
      _ = u • mfderiv 𝓘(ℝ, ℝ) I γ t 1 := map_smul _ _ _
      _ = _ := by rw [← hgrad, ← hV (γ t) hqt.1 hqt.2]; rfl
  rw [← heq]
  exact hγt.hasMFDerivAt.hasMFDerivWithinAt

theorem flow_eq_intrinsicGeodesic_on_annulus
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (p : M) (v : TangentSpace I p) (hv : g.inner p v v = 1)
    {a b : ℝ} (ha : 0 ≤ a)
    (hd : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => Metric.infDist q S)
      {q | a < Metric.infDist q S ∧ Metric.infDist q S < b})
    (hcal : ∀ t ∈ Ioo a b, Metric.infDist (intrinsicGeodesic g hEnorm p v t) S = t)
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hV : ∀ q, a < Metric.infDist q S → Metric.infDist q S < b →
      V q = gradientFun g (fun x => Metric.infDist x S) q)
    (ϕ : Flow ℝ M) (hϕ : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    ϕ (t - s) (intrinsicGeodesic g hEnorm p v s) = intrinsicGeodesic g hEnorm p v t := by
  let γ := intrinsicGeodesic g hEnorm p v
  have hγ := isMIntegralCurveOn_intrinsicGeodesic_of_infDist g hEnorm hS hSne p v hv ha hd hcal V hV
  have hflow : IsMIntegralCurve (fun u => ϕ (u - s) (γ s)) V := by
    simpa only [Function.comp_def, sub_eq_add_neg] using (hϕ (γ s)).comp_add (-s)
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hs
    (V.contMDiff.of_le (by simp)) (hflow.isMIntegralCurveOn _) hγ
    (by simp only [sub_self, ϕ.map_zero_apply]; rfl)
  exact heq ht

theorem exists_smooth_infDist_normal_radial_data
    [ConnectedSpace M] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {S : Set M} (hSne : S.Nonempty) (hScomp : IsCompact S)
    (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅) :
    ∃ ε > 0,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => Metric.infDist q S)
        {q | 0 < Metric.infDist q S ∧ Metric.infDist q S < ε} ∧
      ∀ (p : S) (v : normalSpace g S p.1), g.inner p.1 v.1 v.1 = 1 →
        ∀ t : ℝ, 0 < t → t < ε → Metric.infDist (intrinsicGeodesic g hEnorm p.1 v.1 t) S = t := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let FN := Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ
  let NB := TotalSpace FN (normalBundleFiber g S)
  obtain ⟨r, hr, Φ, hsource, _, hΦ, _, hradius⟩ :=
    exists_normal_tube g hEnorm hsec hSne hScomp hconv hB
  obtain ⟨δ, hδ, _, hd⟩ := exists_smooth_infDist_tube g hEnorm hsec hSne hScomp hconv hB
  refine ⟨min r δ, lt_min hr hδ, hd.mono (fun q hq => ⟨hq.1, hq.2.trans_le (min_le_right _ _)⟩), ?_⟩
  intro p v hv t ht htε
  let z : NB := ⟨p, t • v⟩
  have hlen : Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) = t := by
    change Real.sqrt (g.inner p.1 (t • v.1) (t • v.1)) = t
    rw [sqrt_gInner_smul_self g p.1 ht.le v.1, hv, Real.sqrt_one, mul_one]
  have hz : z ∈ Φ.source := by
    rw [hsource]
    change Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) < r
    rw [hlen]
    exact htε.trans_le (min_le_left _ _)
  have h := hradius z hz
  rw [hlen, hΦ] at h
  change t = Metric.infDist (expMapIntrinsic g hEnorm p.1 (t • v.1)) S at h
  rw [expMapIntrinsic_smul_eq_intrinsicGeodesic] at h
  exact h.symm

end DifferentialGeometry.Geometry.Topology
