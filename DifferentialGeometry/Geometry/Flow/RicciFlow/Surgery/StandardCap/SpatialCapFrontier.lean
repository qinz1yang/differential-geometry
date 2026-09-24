import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndNeckDatum
import Mathlib.Analysis.Normed.Module.RCLike.Real
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCap
import DifferentialGeometry.Geometry.Neck.SpatialLevelEmbedding
import DifferentialGeometry.Topology.SphereSeparation.StandardSphere
import DifferentialGeometry.Topology.SphereSeparation.Transport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology.SphereSeparation
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private theorem exists_compactDomain_closedBall {r : ℝ} (hr : 0 < r) :
    ∃ K : CompactDomain ThreeSpace, K.carrier = Metric.closedBall (0 : ThreeSpace) r ∧
      Nonempty (CapCore K.carrier) := by
  let F := (LinearEquiv.smulOfNeZero ℝ ThreeSpace r hr.ne').toContinuousLinearEquiv.toDiffeomorph
  let e : Sphere 2 → ThreeSpace := F ∘ Subtype.val
  have he : IsSmoothEmbedding I2 I3 ∞ e :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp I2 I3
      Subtype.val (isSmoothEmbedding_coe_sphere (E := ThreeSpace) (n := 2)) F
  have hfront : range e = F '' Metric.sphere (0 : ThreeSpace) 1 := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y.val,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  let K := CompactDomain.ofSphereSides he (standardUnitSphereSides.image F.toHomeomorph) hfront
  have hK : K.carrier = F '' Metric.closedBall (0 : ThreeSpace) 1 := by
    change closure (F.toHomeomorph '' Metric.ball (0 : ThreeSpace) 1) =
      F.toHomeomorph '' Metric.closedBall (0 : ThreeSpace) 1
    rw [← F.toHomeomorph.image_closure, closure_ball _ one_ne_zero]
  have hscale : F '' Metric.closedBall (0 : ThreeSpace) 1 = Metric.closedBall (0 : ThreeSpace) r
    := by
    change (fun x : ThreeSpace => r • x) '' Metric.closedBall 0 1 = _
    rw [Set.image_smul, smul_closedBall' hr.ne']
    simp only [smul_zero,Real.norm_eq_abs,abs_of_pos hr,mul_one]
  refine ⟨K,hK.trans hscale,?_⟩
  rw [hK]
  exact ⟨CapCore.ball F.toPartialDiffeomorph (fun _ _ => mem_univ _) rfl⟩

theorem exists_spatial_neck_closed_ball_frontier
    {eps r : ℝ} (heps : 0 < eps) (hepssmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) {s : ℝ}
    (hs : s ∈ Ioo (-eps⁻¹) eps⁻¹) :
    ∃ nk : SpatialNeck metric eps (r • (spherePoint : ThreeSpace)),
      (∀ z : neckBuffer eps, nk.map z.val = (r + z.val.2) • (z.val.1 : ThreeSpace)) ∧
      ∃ K : CompactDomain ThreeSpace,
        K.carrier = Metric.closedBall (0 : ThreeSpace) (r+s) ∧ Nonempty (CapCore K.carrier) ∧
        (0 : ThreeSpace) ∈ interior K.carrier ∧
        frontier K.carrier = range (fun q : Sphere 2 => nk.map (q,s)) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q,s)) ∧
        (∀ z ∈ frontier K.carrier, metricScalarAt metric z = 1) ∧
        (∀ q : Sphere 2, ∀ t : ℝ, s+t ∈ Ioo (-eps⁻¹) eps⁻¹ →
          (nk.map (q,s+t) ∈ K.carrier ↔ t ≤ 0)) ∧
        (∀ z ∈ K.carrier, riemannianEDistOf metric 0 z ≤ ENNReal.ofReal (r+s)) := by
  let d := endNeckDatum r eps heps (hepssmall.trans (by norm_num)) hr ⌈eps⁻¹⌉₊ true
  obtain ⟨nk,hmark,hmap⟩ := d.toNormalizedNeck.exists_spatialNeck le_rfl hepssmall le_rfl
  change SpatialNeck metric eps (r • (spherePoint : ThreeSpace)) at nk
  have hmap' (z : neckBuffer eps) : nk.map z.val = (r+z.val.2) • (z.val.1 : ThreeSpace) := by
    exact (hmap z).trans (endNeckMap_apply r eps z)
  have hlevel (q : Sphere 2) (v : ℝ) (hv : v ∈ Ioo (-eps⁻¹) eps⁻¹) :
      nk.map (q,v) = (r+v) • (q : ThreeSpace) :=
    hmap' ⟨(q,v),by constructor <;> linarith [hv.1,hv.2]⟩
  have hrs : 0 < r+s := by linarith [transitionEnd_pos,hs.1]
  obtain ⟨K,hK,hmodel⟩ := exists_compactDomain_closedBall hrs
  refine ⟨nk,hmap',K,hK,hmodel,?_,?_,?_,?_,?_,?_⟩
  · rw [hK,interior_closedBall _ hrs.ne']
    exact Metric.mem_ball_self hrs
  · rw [hK,frontier_closedBall _ hrs.ne']
    ext x
    constructor
    · intro hx
      have hn : ‖x‖ = r+s := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
      let q : Sphere 2 := ⟨(r+s)⁻¹ • x,by
        rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hrs),hn]
        exact inv_mul_cancel₀ hrs.ne'⟩
      refine ⟨q, ?_⟩
      change nk.map (q,s) = x
      rw [hlevel q s hs]
      exact smul_inv_smul₀ hrs.ne' x
    · rintro ⟨q,rfl⟩
      change nk.map (q,s) ∈ Metric.sphere (0 : ThreeSpace) (r+s)
      rw [hlevel q s hs]
      rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hrs]
      have hq : ‖(q : ThreeSpace)‖ = 1 := by
        simpa only [Metric.mem_sphere,dist_zero_right] using q.property
      rw [hq,mul_one]
  · exact nk.isSmoothEmbedding_level (abs_lt.mpr hs)
  · intro z hz
    rw [hK,frontier_closedBall _ hrs.ne'] at hz
    apply metricScalarAt_cylindrical
    have hn : ‖z‖ = r+s := by simpa only [Metric.mem_sphere,dist_zero_right] using hz
    rw [hn]
    linarith [hs.1]
  · intro q t ht
    rw [hK,hlevel q (s+t) ht,
      Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs]
    have hp : 0 < r+(s+t) := by linarith [transitionEnd_pos,ht.1]
    have hq : ‖(q : ThreeSpace)‖ = 1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using q.property
    rw [abs_of_pos hp,hq,mul_one]
    constructor <;> intro hh <;> linarith
  · intro z hz
    rw [hK] at hz
    have hn : ‖z‖ ≤ r+s := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    rw [show riemannianEDistOf metric 0 z = ENNReal.ofReal ‖z‖ from edist_zero z]
    exact ENNReal.ofReal_le_ofReal hn

end DifferentialGeometry.PDE.RicciFlow.StandardCap
