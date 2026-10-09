import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapPlane
import DifferentialGeometry.Geometry.Operator.Pullback
import DifferentialGeometry.Geometry.Operator.Product
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Geometry.Connection.Cylinder
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
set_option autoImplicit false
noncomputable section
open Bundle Set Function Manifold Metric Filter
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Geometry.Collapse.EdgeCapCylindrical
open DifferentialGeometry.Geometry.Collapse.EdgeCapRadial
open DifferentialGeometry.Geometry.Collapse.EdgeCapHeight
open DifferentialGeometry.Geometry.Collapse.EdgeCapPlane
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology InnerProductSpace
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] capPlaneDimensionFact
namespace DifferentialGeometry.Geometry.Collapse.EdgeCapHessian
abbrev IC := (𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))
abbrev capKappa := scaledCapMetric capExampleEpsilon capExampleEpsilon_pos
abbrev polar := capPolarPartial capExampleEpsilon capExampleEpsilon_pos

def endDomain : TopologicalSpace.Opens (AddCircle (1 : ℝ) × ℝ) :=
  ⟨{q | capExampleEpsilon * (transitionEnd + 9) < q.2},
    isOpen_lt continuous_const continuous_snd⟩

theorem endDomain_source (q : endDomain) : (q : AddCircle (1 : ℝ) × ℝ) ∈ polar.source := by
  rw [capPolarPartial_source]
  have hp := mul_pos capExampleEpsilon_pos (by linarith [transitionEnd_pos] :
    0 < transitionEnd + 9)
  exact hp.trans q.property

def endProjection (q : endDomain) : E2 := polar q.val

theorem endProjection_local : IsLocalDiffeomorph IC (𝓡 2) ∞ endProjection := by
  intro q
  have hp : IsLocalDiffeomorphAt IC (𝓡 2) ∞
      (polar : (AddCircle (1 : ℝ) × ℝ) → E2) q.val :=
    ⟨polar, endDomain_source q, Set.eqOn_refl _ _⟩
  exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := IC) endDomain q).comp
    (𝓡 2) E2 hp

theorem endProjection_derivative (q : endDomain) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 2) endProjection q v = mfderiv IC (𝓡 2) polar q.val v := by
  have hp := polar.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    (endDomain_source q)
  rw [show endProjection = (polar : (AddCircle (1 : ℝ) × ℝ) → E2) ∘ Subtype.val from rfl,
    mfderiv_comp_apply q hp (hasMFDerivAt_subtype_val endDomain q).mdifferentiableAt v,
    mfderiv_subtype_val_apply]

local instance endDomainSigmaCompact : SigmaCompactSpace endDomain :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (isSigmaCompact_of_isOpen IC endDomain.isOpen)

def endPullMetric : SmoothRiemannianMetric IC endDomain :=
  localPullMetric capKappa endProjection endProjection_local

def endFlatMetric : SmoothRiemannianMetric IC endDomain :=
  (smallFlatCircleMetric.prod (euclideanMetric (E := ℝ))).restrictOpen endDomain

theorem endMetric_inner (q : endDomain) (v w : TangentSpace IC q) :
    endPullMetric.inner q v w = endFlatMetric.inner q v w := by
  rw [endPullMetric, localPullMetric_inner, endProjection_derivative,
    endProjection_derivative]
  have hend : transitionEnd ≤ capExampleEpsilon⁻¹ * q.val.2 := by
    apply (le_inv_mul_iff₀ capExampleEpsilon_pos).mpr
    have hp := mul_pos capExampleEpsilon_pos (by norm_num : (0 : ℝ) < 9)
    have hq : capExampleEpsilon * (transitionEnd + 9) < q.val.2 := q.property
    nlinarith
  have h := capPolarPartial_selected_metric q.val hend v w
  exact h

theorem endMetric_eq : endPullMetric = endFlatMetric := by
  ext q v w
  exact endMetric_inner q v w

theorem endFlatMetric_cylinder : endFlatMetric =
    (cylinderMetric smallFlatCircleMetric).restrictOpen endDomain := rfl

theorem endFlat_hessian (q : endDomain) (v w : TangentSpace IC q) :
    hessFun endFlatMetric (fun y : endDomain => y.val.2) q v w = 0 := by
  rw [endFlatMetric_cylinder]
  apply (hessFun_restrictOpen_of_contMDiff (cylinderMetric smallFlatCircleMetric)
    endDomain Prod.snd contMDiff_snd q v w).trans
  exact hessFun_height_cylinderMetric smallFlatCircleMetric q.val _ _

def capHeightSmooth : C^∞⟮𝓡 2, E2; ℝ⟯ :=
  ⟨capCollarHeight capExampleEpsilon, (capCollarHeight_smooth capExampleEpsilon).contMDiff⟩

theorem endHeight_literal (q : endDomain) : capHeightSmooth (endProjection q) = q.val.2 := by
  have hq : capExampleEpsilon * (transitionEnd + 9) < q.val.2 := q.property
  have hp := mul_pos capExampleEpsilon_pos transitionEnd_pos
  have hn : 9 * capExampleEpsilon ≤ q.val.2 := by nlinarith
  have hr : 0 ≤ q.val.2 := (capPolarPartial_source _ _).mp (endDomain_source q) |>.le
  have h := capF_ray q.val.1 (0, q.val.2) hr hn
  have he : capRayPoint q.val.1 q.val.2 = endProjection q :=
    congrFun (capRayPoint_polar q.val.2) q.val.1
  change capCollarHeight capExampleEpsilon (endProjection q) = q.val.2
  rw [← he]
  simpa only [capExampleF, planeRay, Diffeomorph.symm_apply_apply] using h

theorem endPull_height_hessian (q : endDomain) (v w : TangentSpace IC q) :
    hessFun capKappa capHeightSmooth (endProjection q)
      (mfderiv IC (𝓡 2) endProjection q v)
      (mfderiv IC (𝓡 2) endProjection q w) = 0 := by
  have hh := hessFun_localPull capKappa endProjection endProjection_local capHeightSmooth q v w
  have hf : (capHeightSmooth : E2 → ℝ) ∘ endProjection =
      fun y : endDomain => y.val.2 := funext endHeight_literal
  rw [hf] at hh
  change hessFun endPullMetric (fun y : endDomain => y.val.2) q v w = _ at hh
  rw [endMetric_eq, endFlat_hessian] at hh
  exact hh.symm


theorem endHeight_hessian (q : endDomain) (u v : TangentSpace (𝓡 2) (endProjection q)) :
    hessFun capKappa capHeightSmooth (endProjection q) u v = 0 := by
  let e := endProjection_local.mfderivToContinuousLinearEquiv (by simp) q
  have hh := endPull_height_hessian q (e.symm u) (e.symm v)
  rw [← endProjection_local.mfderivToContinuousLinearEquiv_coe (by simp) (x := q)] at hh
  simpa only [e, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using hh

theorem actual_surface_height_hessian (z : E2)
    (hz : capExampleEpsilon * (transitionEnd + 9) < physicalRadius z)
    (u v : TangentSpace (𝓡 2) z) : hessFun capKappa capHeightSmooth z u v = 0 := by
  have hne : z ≠ 0 := by
    intro he
    have hpos := mul_pos capExampleEpsilon_pos (by linarith [transitionEnd_pos] :
      0 < transitionEnd + 9)
    simp only [physicalRadius, he, norm_zero, mul_zero] at hz
    linarith
  obtain ⟨θ, r, hr, he, hp⟩ := capRayPoint_positive_cover z hne
  let q : endDomain := ⟨(θ, r), by
    change capExampleEpsilon * (transitionEnd + 9) < r
    rw [he]
    exact hz⟩
  have hq : endProjection q = z :=
    (congrFun (capRayPoint_polar r) θ).symm.trans hp
  have ht : hessFun capKappa capHeightSmooth (endProjection q) = 0 := by
    ext a b
    exact endHeight_hessian q a b
  rw [hq] at ht
  have hh := congrArg (fun B => B u v) ht
  exact hh


def productHeightSmooth : C^∞⟮(𝓘(ℝ, ℝ)).prod (𝓡 2), ℝ × E2; ℝ⟯ :=
  ⟨fun q => capHeightSmooth q.2, capHeightSmooth.contMDiff.comp contMDiff_snd⟩

theorem actual_product_height_hessian (a : ℝ × E2)
    (ha : capExampleEpsilon * (transitionEnd + 9) < physicalRadius a.2)
    (u v : TangentSpace ((𝓘(ℝ, ℝ)).prod (𝓡 2)) a) :
    hessFun (capProductMetric capExampleEpsilon capExampleEpsilon_pos)
      productHeightSmooth a u v = 0 := by
  let f : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯ := ⟨fun _ => 0, contMDiff_const⟩
  have hzero : hessFun (euclideanMetric (E := ℝ)) (fun _ : ℝ => (0 : ℝ)) a.1 = 0 := by
    change hessFun (euclideanMetric (E := ℝ)) (0 : ℝ → ℝ) a.1 = 0
    have ht := congrFun (hessFun_smul (euclideanMetric (E := ℝ)) 0
      (fun _ : ℝ => (1 : ℝ))) a.1
    simpa using ht
  have hh := hessFun_prod (euclideanMetric (E := ℝ)) capKappa f capHeightSmooth a u v
  change hessFun (capProductMetric capExampleEpsilon capExampleEpsilon_pos)
    (fun q : ℝ × E2 => 0 + capHeightSmooth q.2) a u v =
    hessFun (euclideanMetric (E := ℝ)) (fun _ : ℝ => (0 : ℝ)) a.1 u.1 v.1 +
      hessFun capKappa capHeightSmooth a.2 u.2 v.2 at hh
  simp only [zero_add] at hh
  rw [hzero, actual_surface_height_hessian a.2 ha u.2 v.2] at hh
  erw [LinearMap.zero_apply, zero_add] at hh
  exact hh

theorem actual_E3_height_hessian (x : E3)
    (hx : capExampleEpsilon * (transitionEnd + 9) < axisRadius x)
    (u v : TangentSpace (𝓡 3) x) : hessFun capExampleMetric capExampleF x u v = 0 := by
  have hh := hessFun_pullbackCross
    (capProductMetric capExampleEpsilon capExampleEpsilon_pos)
    capProductCoordinates.symm productHeightSmooth x u v
  change hessFun capExampleMetric capExampleF x u v =
    hessFun (capProductMetric capExampleEpsilon capExampleEpsilon_pos) productHeightSmooth
      (capProductCoordinates.symm x)
      (mfderiv (𝓡 3) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) capProductCoordinates.symm x u)
      (mfderiv (𝓡 3) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) capProductCoordinates.symm x v) at hh
  rw [actual_product_height_hessian (capProductCoordinates.symm x) hx] at hh
  exact hh


theorem realCollarPoint_height_hessian (u v : TangentSpace (𝓡 3) realCollarPoint) :
    hessFun capExampleMetric capExampleF realCollarPoint u v = 0 := by
  apply actual_E3_height_hessian
  have h := capF_le_axisRadius realCollarPoint
  rw [realCollarPoint_height] at h
  unfold capExampleDelta at h
  have he := capExampleEpsilon_pos
  have ht := transitionEnd_pos
  have hp := mul_pos he ht
  nlinarith

end DifferentialGeometry.Geometry.Collapse.EdgeCapHessian
