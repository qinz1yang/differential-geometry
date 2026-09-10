import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderMetric
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Intrinsic
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance antipodalSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem sphere2_antipodal_riemannianEDist_lower (p : SpatialNeckSphere) :
    ENNReal.ofReal Real.pi ≤ riemannianEDistOf (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p (-p) := by
  let g := roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
  let _ : IsManifold (𝓡 2) 1 SpatialNeckSphere := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace SpatialNeckSphere :=
    Manifold.metrizableSpace (𝓡 2) SpatialNeckSphere
  let _ : T3Space SpatialNeckSphere := inferInstance
  let _ : RiemannianBundle (fun q : SpatialNeckSphere => TangentSpace (𝓡 2) q) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun q : SpatialNeckSphere => TangentSpace (𝓡 2) q) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro q v w; rfl⟩⟩
  let _ : EMetricSpace SpatialNeckSphere := EMetricSpace.ofRiemannianMetric (𝓡 2) SpatialNeckSphere
  let _ : PseudoEMetricSpace SpatialNeckSphere :=
    (EMetricSpace.ofRiemannianMetric (𝓡 2) SpatialNeckSphere).toPseudoEMetricSpace
  let _ : @CompleteSpace SpatialNeckSphere
      (@PseudoEMetricSpace.toUniformSpace _ ‹PseudoEMetricSpace SpatialNeckSphere›) :=
    (RiemannianMetricComplete.of_compact g).complete
  let _ : ConnectedSpace SpatialNeckSphere := by
    apply Subtype.connectedSpace
    apply isConnected_sphere
    · exact Module.one_lt_rank_of_one_lt_finrank (by simp)
    · norm_num
  have hEnorm : IsMetricNorm (I := 𝓡 2) g :=
    fun q v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g q v
  have hpp : ⟪(p : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have hpne : p ≠ -p := by
    intro heq
    have hh := congrArg
      (fun q : SpatialNeckSphere => ⟪(p : EuclideanSpace ℝ (Fin 3)),
        (q : EuclideanSpace ℝ (Fin 3))⟫) heq
    change ⟪(p : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫ =
      ⟪(p : EuclideanSpace ℝ (Fin 3)), -(p : EuclideanSpace ℝ (Fin 3))⟫ at hh
    rw [inner_neg_right, hpp] at hh
    norm_num at hh
  have hfin : riemannianEDist (𝓡 2) p (-p) ≠ ⊤ := riemannianEDist_ne_top p (-p)
  have hdne : riemannianEDist (𝓡 2) p (-p) ≠ 0 :=
    fun hzero => hpne (riemannianEDist_eq_zero_imp_eq p (-p) hzero)
  let r : ℝ := (riemannianEDist (𝓡 2) p (-p)).toReal
  have hrpos : 0 < r := ENNReal.toReal_pos hdne hfin
  obtain ⟨v, hvexp, hvnorm⟩ := minExp_of_ne_top g hEnorm p (-p) hfin
  have hinner_v : g.inner p v v = r ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg g p v), hvnorm]
  let w : TangentSpace (𝓡 2) p := r⁻¹ • v
  have hinner_w : g.inner p w w = 1 := by
    dsimp only [w]
    rw [gInner_smul_self, hinner_v, ← mul_pow, inv_mul_cancel₀ hrpos.ne', one_pow]
  have hw : ‖dIncl (n := 2) p w‖ = 1 := by
    have hsq : ‖dIncl (n := 2) p w‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, ← roundMetric_inner]
      exact hinner_w
    nlinarith [norm_nonneg (dIncl (n := 2) p w)]
  have hsmul : r • w = v := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  have hval := round_exp_val hEnorm p w hw r
  rw [hsmul, hvexp] at hval
  have hdot := congrArg
    (fun q : EuclideanSpace ℝ (Fin 3) => ⟪(p : EuclideanSpace ℝ (Fin 3)), q⟫) hval
  change ⟪(p : EuclideanSpace ℝ (Fin 3)), -(p : EuclideanSpace ℝ (Fin 3))⟫ =
    ⟪(p : EuclideanSpace ℝ (Fin 3)),
      Real.cos r • (p : EuclideanSpace ℝ (Fin 3)) + Real.sin r • dIncl (n := 2) p w⟫ at hdot
  simp only [inner_neg_right, inner_add_right, real_inner_smul_right, hpp,
    dIncl_orth, mul_one, mul_zero, add_zero] at hdot
  have hcos : Real.cos r = -1 := hdot.symm
  have hpi : Real.pi ≤ r := by
    by_contra hnot
    have hlt : r < Real.pi := lt_of_not_ge hnot
    have hc := Real.strictAntiOn_cos ⟨hrpos.le, hlt.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hlt
    rw [Real.cos_pi, hcos] at hc
    exact (lt_irrefl (-1 : ℝ)) hc
  calc
    ENNReal.ofReal Real.pi ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hpi
    _ = riemannianEDist (𝓡 2) p (-p) := ENNReal.ofReal_toReal hfin
    _ = riemannianEDistOf (I := 𝓡 2) g p (-p) :=
      (riemannianEDistOf_eq_riemannianEDist g hEnorm p (-p)).symm

theorem sphere2_antipodal_length_lower {γ : ℝ → SpatialNeckSphere} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 γ (Icc a b))
    (hanti : γ b = -γ a) :
    ENNReal.ofReal Real.pi ≤ metricPathELength (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) γ a b := by
  let g := roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
  let _ : RiemannianBundle (fun q : SpatialNeckSphere => TangentSpace (𝓡 2) q) :=
    ⟨g.toRiemannianMetric⟩
  have hdist : riemannianEDistOf (I := 𝓡 2) g (γ a) (γ b) ≤
      metricPathELength (I := 𝓡 2) g γ a b :=
    Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab
  have hend := congrArg (fun q => riemannianEDistOf (I := 𝓡 2) g (γ a) q) hanti
  exact ((sphere2_antipodal_riemannianEDist_lower (γ a)).trans_eq hend.symm).trans hdist

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
