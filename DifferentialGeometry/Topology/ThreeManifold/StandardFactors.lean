import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Manifold.ProductOrientation
import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.FundamentalGroup.SphericalQuotient
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import Mathlib.Topology.Covering.Basic

noncomputable section

open Manifold Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

structure SphericalSpaceFormGroup where
  group : Subgroup (EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
  [finite : Finite group]
  positive : ∀ γ : group, (Geometry.sphereDiffeo (n := 3) γ.val).preservesOrientation
    (sphereOrientation 3 (by decide)) (sphereOrientation 3 (by decide))
  free : ∀ γ : group, ∀ x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
    Geometry.sphereDiffeo (n := 3) γ.val x = x → γ = 1

attribute [instance] SphericalSpaceFormGroup.finite

namespace SphericalSpaceFormGroup

variable (G : SphericalSpaceFormGroup)

instance instMulActionSphere : MulAction G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  smul γ x := Geometry.sphereDiffeo (n := 3) γ.val x
  one_smul x := by
    apply Subtype.ext
    change (((1 : G.group) : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
      (x : EuclideanSpace ℝ (Fin 4))) = (x : EuclideanSpace ℝ (Fin 4))
    simp
  mul_smul a b x := by
    apply Subtype.ext
    change (((a * b : G.group) : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
        (x : EuclideanSpace ℝ (Fin 4))) =
      ((a : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
        (((b : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)))
          (x : EuclideanSpace ℝ (Fin 4))))
    simp

instance instContMDiffConstSMulSphere :
    ContMDiffConstSMul (𝓡 3) ∞ G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  contMDiff_const_smul γ :=
    (Geometry.sphereDiffeo (n := 3) γ.val).contMDiff

instance instContinuousConstSMulSphere :
    ContinuousConstSMul G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  continuous_const_smul γ :=
    ((Geometry.sphereDiffeo (n := 3) γ.val).contMDiff).continuous

instance instIsCancelSMulSphere : IsCancelSMul G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  right_cancel' a b c h := by
    have h1 : (b⁻¹ * a) • c = c := by
      calc (b⁻¹ * a) • c = b⁻¹ • (a • c) := mul_smul b⁻¹ a c
        _ = b⁻¹ • (b • c) := by rw [h]
        _ = c := inv_smul_smul b c
    have h2 : b⁻¹ * a = 1 := G.free (b⁻¹ * a) c h1
    calc a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
      _ = b * 1 := by rw [h2]
      _ = b := mul_one b

def orbitSetoid : Setoid (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  MulAction.orbitRel G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

abbrev Orbit := Quotient G.orbitSetoid

def projection : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → G.Orbit :=
  Quotient.mk G.orbitSetoid

theorem projection_eq_iff (x y : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    G.projection x = G.projection y ↔
      ∃ γ : G.group, Geometry.sphereDiffeo (n := 3) γ.val x = y := by
  rw [show G.projection x = G.projection y ↔
      (MulAction.orbitRel G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) x y from
    Quotient.eq,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨γ, hγ⟩ := h
    refine ⟨γ⁻¹, ?_⟩
    change (γ⁻¹ : G.group) • x = y
    rw [← hγ, inv_smul_smul]
  · obtain ⟨γ, hγ⟩ := h
    have hγ' : γ • x = y := hγ
    refine ⟨γ⁻¹, ?_⟩
    rw [← hγ', inv_smul_smul]

theorem projection_surjective : Function.Surjective G.projection :=
  Quotient.mk_surjective

theorem projection_isQuotientMap : _root_.Topology.IsQuotientMap G.projection :=
  isQuotientMap_quotient_mk'

theorem projection_continuous : Continuous G.projection :=
  G.projection_isQuotientMap.continuous

theorem projection_invariant (γ : G.group)
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    G.projection (Geometry.sphereDiffeo (n := 3) γ.val x) = G.projection x := by
  symm
  exact (G.projection_eq_iff _ _).2 ⟨γ, rfl⟩

structure SmoothQuotient where
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.Orbit]
  [smooth : IsManifold (𝓡 3) ∞ G.Orbit]
  [hausdorff : T2Space G.Orbit]
  [compact : CompactSpace G.Orbit]
  [connected : ConnectedSpace G.Orbit]
  local_diffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ G.projection
  covering : IsCoveringMap G.projection
  orientation : ManifoldOrientation (𝓡 3) G.Orbit 3
  positive : ∀ x, Orientation.map (Fin 3)
    (local_diffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    ((sphereOrientation 3 (by decide)).orientation x) = orientation.orientation (G.projection x)


private abbrev SphereThree : Type := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

private noncomputable instance quotientChartedSpaceAux :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.Orbit :=
  MulAction.instChartedSpaceQuotient

private noncomputable instance quotientIsManifoldAux : IsManifold (𝓡 3) ∞ G.Orbit :=
  MulAction.isManifold_quotient_of_contMDiffConstSMul (M := SphereThree) (G := G.group)
    (n := ∞) (𝓡 3)

private theorem projection_localDiffeomorph_aux :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ G.projection :=
  MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul (M := SphereThree)
    (G := G.group) (n := ∞) (𝓡 3)

private theorem projection_covering_aux : IsCoveringMap G.projection :=
  (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G.group)
    (E := SphereThree)).isCoveringMap

private theorem projection_localHomeo_aux : IsLocalHomeomorph G.projection :=
  (projection_covering_aux G).isLocalHomeomorph

private noncomputable def quotientRep (q : G.Orbit) : SphereThree :=
  (Quotient.mk_surjective (s := G.orbitSetoid)).hasRightInverse.choose q

private theorem quotientRep_projection (q : G.Orbit) :
    G.projection (quotientRep G q) = q :=
  (Quotient.mk_surjective (s := G.orbitSetoid)).hasRightInverse.choose_spec q

private noncomputable def quotientSection (q : G.Orbit) :
    OpenPartialHomeomorph G.Orbit SphereThree :=
  (projection_localHomeo_aux G).localInverseAt (quotientRep G q)

private theorem chartAt_quotient_eq (q : G.Orbit) :
    chartAt (EuclideanSpace ℝ (Fin 3)) q =
      (quotientSection G q).trans (chartAt (EuclideanSpace ℝ (Fin 3)) (quotientRep G q)) :=
  rfl

private theorem quotientSection_self (q : G.Orbit) :
    quotientSection G q q = quotientRep G q := by
  have h := IsLocalHomeomorph.localInverseAt_apply_self (projection_localHomeo_aux G)
    (x := quotientRep G q)
  simpa [quotientSection, quotientRep_projection G q] using h

private theorem quotientSection_projection {q : G.Orbit} {y : G.Orbit}
    (hy : y ∈ (quotientSection G q).source) :
    G.projection (quotientSection G q y) = y :=
  IsLocalHomeomorph.apply_localInverseAt_of_mem (projection_localHomeo_aux G) hy


private theorem quotientSection_chart_eq {q y : G.Orbit} :
    (chartAt (EuclideanSpace ℝ (Fin 3)) q) y =
      (chartAt (EuclideanSpace ℝ (Fin 3)) (quotientRep G q)) (quotientSection G q y) := by
  rw [chartAt_quotient_eq G q, OpenPartialHomeomorph.trans_apply]

private theorem quotientSection_mem_chart_source {q y : G.Orbit}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).source) :
    quotientSection G q y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) (quotientRep G q)).source := by
  have h := hy
  rw [chartAt_quotient_eq G q, OpenPartialHomeomorph.trans_source] at h
  exact h.2

private theorem quotientSection_contMDiffAt {q y : G.Orbit}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).source) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (quotientSection G q) y := by
  have h1 : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (chartAt (EuclideanSpace ℝ (Fin 3)) q) y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hy
  have h2 : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      ((chartAt (EuclideanSpace ℝ (Fin 3)) (quotientRep G q)).symm)
      ((chartAt (EuclideanSpace ℝ (Fin 3)) q) y) := by
    rw [quotientSection_chart_eq (G := G) (q := q) (y := y)]
    exact contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (quotientRep G q))
      ((chartAt (EuclideanSpace ℝ (Fin 3)) (quotientRep G q)).map_source
        (quotientSection_mem_chart_source G hy))
  refine (h2.comp y h1).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (EuclideanSpace ℝ (Fin 3)) q).open_source.mem_nhds hy] with z hz
  simp only [Function.comp_apply]
  rw [quotientSection_chart_eq (G := G) (q := q) (y := z)]
  exact ((chartAt (EuclideanSpace ℝ (Fin 3)) (quotientRep G q)).left_inv
    (quotientSection_mem_chart_source G hz)).symm

private theorem quotientSection_mdifferentiableAt {q y : G.Orbit}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).source) :
    MDifferentiableAt (𝓡 3) (𝓡 3) (quotientSection G q) y :=
  (quotientSection_contMDiffAt G hy).mdifferentiableAt (by simp)


private theorem quotient_tangent_trivialization {q y : G.Orbit}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).source)
    (hb : quotientSection G q y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) (quotientRep G q)).source)
    (v : TangentSpace (𝓡 3) y) :
    (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) q).continuousLinearEquivAt ℝ y hy v =
      (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3))
        (quotientRep G q)).continuousLinearEquivAt ℝ (quotientSection G q y) hb
        (mfderiv (𝓡 3) (𝓡 3) (quotientSection G q) y v) := by
  rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hy,
    Bundle.Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hb,
    TangentBundle.continuousLinearMapAt_trivializationAt hy,
    TangentBundle.continuousLinearMapAt_trivializationAt hb]
  have heq : (extChartAt (𝓡 3) q : G.Orbit → EuclideanSpace ℝ (Fin 3)) =
      (extChartAt (𝓡 3) (quotientRep G q) : SphereThree → EuclideanSpace ℝ (Fin 3)) ∘
        (quotientSection G q : G.Orbit → SphereThree) := by
    funext z
    rw [Function.comp_apply]
    exact quotientSection_chart_eq (G := G) (q := q) (y := z)
  rw [heq]
  exact mfderiv_comp_apply y (mdifferentiableAt_extChartAt hb)
    (quotientSection_mdifferentiableAt G hy) v


private theorem orientation_map_trans' {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (e : A ≃ₗ[ℝ] B) (f : B ≃ₗ[ℝ] C) (o : Orientation ℝ A (Fin 3)) :
    Orientation.map (Fin 3) (e.trans f) o =
      Orientation.map (Fin 3) f (Orientation.map (Fin 3) e o) := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

private noncomputable def sphereOrientationField (x : SphereThree) :
    Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3) :=
  (sphereOrientation 3 (by decide)).orientation x

private noncomputable def projectionDerivEquiv (x : SphereThree) :
    TangentSpace (𝓡 3) x ≃ₗ[ℝ] TangentSpace (𝓡 3) (G.projection x) :=
  ((projection_localDiffeomorph_aux G).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv

private noncomputable def actionTangentEquiv (γ : G.group) (x : SphereThree) :
    TangentSpace (𝓡 3) x ≃ₗ[ℝ]
      TangentSpace (𝓡 3) (Geometry.sphereDiffeo (n := 3) γ.val x) :=
  ((Geometry.sphereDiffeo (n := 3) γ.val).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv

private noncomputable def pushforwardOrientation (x : SphereThree) :
    Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3) :=
  Orientation.map (Fin 3) (projectionDerivEquiv G x) (sphereOrientationField x)

private theorem projectionDerivEquiv_action (γ : G.group) (x : SphereThree) :
    (actionTangentEquiv G γ x).trans
        (projectionDerivEquiv G (Geometry.sphereDiffeo (n := 3) γ.val x)) =
      projectionDerivEquiv G x := by
  apply LinearEquiv.ext
  intro v
  change mfderiv (𝓡 3) (𝓡 3) G.projection (Geometry.sphereDiffeo (n := 3) γ.val x)
      (mfderiv (𝓡 3) (𝓡 3) (Geometry.sphereDiffeo (n := 3) γ.val) x v) =
    mfderiv (𝓡 3) (𝓡 3) G.projection x v
  rw [← mfderiv_comp_apply x
    (((projection_localDiffeomorph_aux G) (Geometry.sphereDiffeo (n := 3) γ.val x)).mdifferentiableAt
      (by simp))
    ((Geometry.sphereDiffeo (n := 3) γ.val).mdifferentiable (by simp) x)]
  rw [show G.projection ∘ ⇑(Geometry.sphereDiffeo (n := 3) γ.val) = G.projection from
    funext (fun z => G.projection_invariant γ z)]

private theorem pushforwardOrientation_action (γ : G.group) (x : SphereThree) :
    pushforwardOrientation G (Geometry.sphereDiffeo (n := 3) γ.val x) =
      pushforwardOrientation G x := by
  have h_pi : sphereOrientationField (Geometry.sphereDiffeo (n := 3) γ.val x) =
      Orientation.map (Fin 3) (actionTangentEquiv G γ x) (sphereOrientationField x) :=
    (G.positive γ x).symm
  rw [pushforwardOrientation, h_pi]
  rw [← orientation_map_trans' (actionTangentEquiv G γ x)
    (projectionDerivEquiv G (Geometry.sphereDiffeo (n := 3) γ.val x)) (sphereOrientationField x)]
  rw [projectionDerivEquiv_action G γ x, pushforwardOrientation]
  rfl


private noncomputable instance sphereThreeConnectedSpace : ConnectedSpace SphereThree :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 4)) (by
      rw [← Module.finrank_eq_rank]
      norm_num) 0 zero_le_one)

private theorem pushforwardOrientation_eq_of_orbitRel {x y : SphereThree}
    (h : MulAction.orbitRel G.group SphereThree x y) :
    pushforwardOrientation G x = pushforwardOrientation G y := by
  obtain ⟨γ, hγ⟩ := h
  rw [← hγ]
  exact pushforwardOrientation_action G γ y

private noncomputable def quotientOrientationField (q : G.Orbit) :
    Orientation ℝ (TangentSpace (𝓡 3) q) (Fin 3) :=
  Quotient.lift (fun x => pushforwardOrientation G x)
    (fun _ _ hxy => pushforwardOrientation_eq_of_orbitRel G hxy) q

private theorem quotientOrientationField_projection (x : SphereThree) :
    quotientOrientationField G (G.projection x) = pushforwardOrientation G x := rfl

private theorem mem_sphere_triv_baseSet (c z : SphereThree)
    (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) c).source) :
    z ∈ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) c).baseSet := by
  rwa [TangentBundle.trivializationAt_baseSet]

private theorem mem_quotient_triv_baseSet (c q : G.Orbit)
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) c).source) :
    q ∈ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) c).baseSet := by
  rwa [TangentBundle.trivializationAt_baseSet]

private theorem sphere_triv_toLinearEquiv (c z : SphereThree)
    (hz : z ∈ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) c).baseSet) :
    ((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) c).continuousLinearEquivAt ℝ z hz).toLinearEquiv =
      tangentChartEquiv (𝓡 3) SphereThree c z hz := by
  ext v
  rw [ContinuousLinearEquiv.coe_toLinearEquiv, Bundle.Trivialization.continuousLinearEquivAt_apply,
    tangentChartEquiv, Bundle.Trivialization.linearEquivAt_apply]

private theorem quotientSection_mem_source {q : G.Orbit} {y : G.Orbit}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).source) :
    y ∈ (quotientSection G q).source := by
  have h := hy
  rw [chartAt_quotient_eq G q, OpenPartialHomeomorph.trans_source] at h
  exact h.1

private theorem extChartAt_quotient_eq (q : G.Orbit) :
    (extChartAt (𝓡 3) q : G.Orbit → EuclideanSpace ℝ (Fin 3)) =
      (extChartAt (𝓡 3) (quotientRep G q) : SphereThree → EuclideanSpace ℝ (Fin 3)) ∘
        (quotientSection G q : G.Orbit → SphereThree) := by
  funext z
  rw [Function.comp_apply]
  exact quotientSection_chart_eq (G := G) (q := q) (y := z)

private theorem extChartAt_quotient_comp (q : G.Orbit) :
    (extChartAt (𝓡 3) q : G.Orbit → EuclideanSpace ℝ (Fin 3)) ∘ G.projection =
      (extChartAt (𝓡 3) (quotientRep G q) : SphereThree → EuclideanSpace ℝ (Fin 3)) ∘
        (fun z => quotientSection G q (G.projection z)) := by
  rw [extChartAt_quotient_eq G q]
  funext z
  simp only [Function.comp_apply]

private theorem quotientSection_comp_eventuallyEq' (q : G.Orbit) {z : SphereThree}
    (hz : z ∈ (quotientSection G q).target) :
    (fun w => quotientSection G q (G.projection w)) =ᶠ[nhds z] id := by
  filter_upwards [(quotientSection G q).open_target.mem_nhds hz] with w hw
  have h := (quotientSection G q).right_inv hw
  rwa [show ⇑(quotientSection G q).symm = G.projection from
    IsLocalHomeomorph.localInverseAt_symm (projection_localHomeo_aux G) (quotientRep G q)] at h

private theorem mfderiv_quotientSection_comp' (q : G.Orbit) {z : SphereThree}
    (hz : z ∈ (quotientSection G q).target) :
    mfderiv (𝓡 3) (𝓡 3) (fun w => quotientSection G q (G.projection w)) z =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) z) := by
  rw [(quotientSection_comp_eventuallyEq' (G := G) (q := q) hz).mfderiv_eq, mfderiv_id]

private theorem quotientSection_comp_apply_self (q : G.Orbit) {z : SphereThree}
    (hz : z ∈ (quotientSection G q).target) :
    quotientSection G q (G.projection z) = z := by
  have h := (quotientSection G q).right_inv hz
  rwa [show ⇑(quotientSection G q).symm = G.projection from
    IsLocalHomeomorph.localInverseAt_symm (projection_localHomeo_aux G) (quotientRep G q)] at h

private theorem quotient_triv_comp_projection_apply (q : G.Orbit) {y : G.Orbit}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).source)
    (v : TangentSpace (𝓡 3) (quotientSection G q y)) :
    ((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) q).continuousLinearEquivAt ℝ y
        (mem_quotient_triv_baseSet G q y hy))
        ((projectionDerivEquiv G (quotientSection G q y)) v) =
      ((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) (quotientRep G q)).continuousLinearEquivAt ℝ
        (quotientSection G q y)
        (mem_sphere_triv_baseSet (quotientRep G q) (quotientSection G q y)
          (quotientSection_mem_chart_source G hy))) v := by
  have hyS : quotientSection G q y ∈ (quotientSection G q).target :=
    (quotientSection G q).map_source (quotientSection_mem_source G hy)
  have hyproj : G.projection (quotientSection G q y) = y :=
    quotientSection_projection G (quotientSection_mem_source G hy)
  rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ (mem_quotient_triv_baseSet G q y hy),
    Bundle.Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _
      (mem_sphere_triv_baseSet (quotientRep G q) (quotientSection G q y)
        (quotientSection_mem_chart_source G hy)),
    TangentBundle.continuousLinearMapAt_trivializationAt hy,
    TangentBundle.continuousLinearMapAt_trivializationAt (quotientSection_mem_chart_source G hy)]
  change mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q) y
      (mfderiv (𝓡 3) (𝓡 3) G.projection (quotientSection G q y) v) =
    mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (quotientRep G q)) (quotientSection G q y) v
  have hchain := mfderiv_comp_apply (x := quotientSection G q y) (f := G.projection)
    (g := ⇑(extChartAt (𝓡 3) q))
    (by rw [hyproj]; exact mdifferentiableAt_extChartAt hy)
    (((projection_localDiffeomorph_aux G) (quotientSection G q y)).mdifferentiableAt (by simp)) v
  rw [hyproj] at hchain
  refine hchain.symm.trans ?_
  rw [extChartAt_quotient_comp G q]
  have hchain2 := mfderiv_comp_apply (x := quotientSection G q y)
    (f := fun z => quotientSection G q (G.projection z))
    (g := ⇑(extChartAt (𝓡 3) (quotientRep G q)))
    (by
      rw [quotientSection_comp_apply_self G q hyS]
      exact mdifferentiableAt_extChartAt (quotientSection_mem_chart_source G hy))
    ((quotientSection_comp_eventuallyEq' G q hyS).mdifferentiableAt_iff.mpr mdifferentiableAt_id) v
  refine hchain2.trans ?_
  rw [quotientSection_comp_apply_self G q hyS]
  rw [mfderiv_quotientSection_comp' (G := G) (q := q) hyS]
  rfl

private theorem quotient_triv_comp_projection (q : G.Orbit) {y : G.Orbit}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).source) :
    (projectionDerivEquiv G (quotientSection G q y)).trans
        (((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) q).continuousLinearEquivAt ℝ y
          (mem_quotient_triv_baseSet G q y hy)).toLinearEquiv) =
      ((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) (quotientRep G q)).continuousLinearEquivAt ℝ
        (quotientSection G q y)
        (mem_sphere_triv_baseSet (quotientRep G q) (quotientSection G q y)
          (quotientSection_mem_chart_source G hy))).toLinearEquiv := by
  apply LinearEquiv.ext
  intro v
  exact quotient_triv_comp_projection_apply G q hy v

private theorem quotientChartOrientation_eq (q : G.Orbit) {y : G.Orbit}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).source) :
    Orientation.map (Fin 3)
      (((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) q).continuousLinearEquivAt ℝ y
        (mem_quotient_triv_baseSet G q y hy)).toLinearEquiv)
      (pushforwardOrientation G (quotientSection G q y)) =
    Orientation.map (Fin 3)
      (((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) (quotientRep G q)).continuousLinearEquivAt ℝ
        (quotientSection G q y)
        (mem_sphere_triv_baseSet (quotientRep G q) (quotientSection G q y)
          (quotientSection_mem_chart_source G hy))).toLinearEquiv)
      (sphereOrientationField (quotientSection G q y)) := by
  rw [pushforwardOrientation]
  exact (orientation_map_trans' (projectionDerivEquiv G (quotientSection G q y))
    (((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) q).continuousLinearEquivAt ℝ y
      (mem_quotient_triv_baseSet G q y hy)).toLinearEquiv)
    (sphereOrientationField (quotientSection G q y))).symm.trans
    (congrArg (fun e => Orientation.map (Fin 3) e
      (sphereOrientationField (quotientSection G q y)))
      (quotient_triv_comp_projection G q hy))

private theorem quotientOrientationField_compatible :
    VectorBundle.IsCompatibleOrientation (F := EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3))
      (quotientOrientationField G) := by
  intro q
  obtain ⟨U₀, hU₀open, hcU₀, hU₀sub, hU₀const⟩ :=
    (sphereOrientation 3 (by decide)).locally_constant (quotientRep G q) (quotientRep G q)
      (mem_sphere_triv_baseSet (quotientRep G q) (quotientRep G q) (mem_chart_source _ _))
  have hqU₀ : quotientSection G q q ∈ U₀ := by
    rw [quotientSection_self G q]
    exact hcU₀
  have hqsrc : q ∈ (quotientSection G q).source := by
    have h := mem_chart_source (EuclideanSpace ℝ (Fin 3)) q
    rw [chartAt_quotient_eq G q, OpenPartialHomeomorph.trans_source] at h
    exact h.1
  refine ⟨trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) q, ?_,
    (chartAt (EuclideanSpace ℝ (Fin 3)) q).source ∩ (fun y => quotientSection G q y) ⁻¹' U₀,
    ?_, ?_,
    Orientation.map (Fin 3)
      (((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) (quotientRep G q)).continuousLinearEquivAt ℝ
        (quotientRep G q)
        (mem_sphere_triv_baseSet (quotientRep G q) (quotientRep G q) (mem_chart_source _ _))).toLinearEquiv)
      (sphereOrientationField (quotientRep G q)), ?_⟩
  · change MemTrivializationAtlas
      (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) q)
    infer_instance
  · have hcont : ContinuousAt (quotientSection G q) q :=
      (quotientSection G q).continuousOn_toFun.continuousAt
        ((quotientSection G q).open_source.mem_nhds hqsrc)
    exact Filter.inter_mem
      ((chartAt (EuclideanSpace ℝ (Fin 3)) q).open_source.mem_nhds (mem_chart_source _ q))
      (hcont.preimage_mem_nhds (hU₀open.mem_nhds hqU₀))
  · intro y hy
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy.1
  · intro y hy
    have hy1 : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).source := hy.1
    have hy2 : quotientSection G q y ∈ U₀ := hy.2
    have hlift : quotientOrientationField G y =
        pushforwardOrientation G (quotientSection G q y) := by
      have h1 : quotientOrientationField G (G.projection (quotientSection G q y)) =
          pushforwardOrientation G (quotientSection G q y) :=
        quotientOrientationField_projection G (quotientSection G q y)
      rwa [quotientSection_projection G (quotientSection_mem_source G hy1)] at h1
    rw [hlift, quotientChartOrientation_eq G q hy1]
    rw [sphere_triv_toLinearEquiv (quotientRep G q) (quotientSection G q y)
        (mem_sphere_triv_baseSet (quotientRep G q) (quotientSection G q y)
          (quotientSection_mem_chart_source G hy1)),
      sphere_triv_toLinearEquiv (quotientRep G q) (quotientRep G q)
        (mem_sphere_triv_baseSet (quotientRep G q) (quotientRep G q) (mem_chart_source _ _))]
    exact hU₀const (quotientSection G q y) hy2

namespace Manifold

private theorem exists_manifoldOrientation_eq_of_compatibleOrientation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}
    (hdim : Module.finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n))
    (ho : DifferentialGeometry.VectorBundle.IsCompatibleOrientation
      (F := E) (TangentSpace 𝓘(ℝ, E)) o) :
    ∃ O : ManifoldOrientation (𝓘(ℝ, E)) M n, O.orientation = o := by
  classical
  refine ⟨{ dimension_eq := hdim, orientation := o, locally_constant := ?_ }, rfl⟩
  intro p x hx
  obtain ⟨t, ht, U, hUx, hU, q, hq⟩ := ho x
  have ht_mem : MemTrivializationAtlas t := ht
  let S : Bundle.Trivialization E (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace 𝓘(ℝ, E)) → M) :=
    trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  have hSinst : MemTrivializationAtlas S := by
    change MemTrivializationAtlas (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p)
    infer_instance
  let C : M → E ≃L[ℝ] E := fun y => Bundle.Trivialization.coordChangeL ℝ t S y
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E := by simpa using hdim.symm
  have hxS : x ∈ S.baseSet := hx
  have hxT : x ∈ t.baseSet := hU (mem_of_mem_nhds hUx)
  have hcont : ContinuousOn (fun y : M =>
      (Bundle.Trivialization.coordChangeL ℝ t S y : E →L[ℝ] E)) (t.baseSet ∩ S.baseSet) :=
    continuousOn_coordChange (R := ℝ) (B := M) (F := E)
      (E := TangentSpace 𝓘(ℝ, E)) t S
  have hC : ContinuousAt (fun y => (C y : E →L[ℝ] E)) x :=
    hcont.continuousAt ((t.open_baseSet.inter S.open_baseSet).mem_nhds ⟨hxT, hxS⟩)
  have hqL : ∀ y (hy : y ∈ U),
      Orientation.map (Fin n) (t.linearEquivAt ℝ y (hU hy)) (o y) = q := by
    intro y hy
    have h := hq y hy
    rwa [show (t.continuousLinearEquivAt ℝ y (hU hy)).toLinearEquiv =
      t.linearEquivAt ℝ y (hU hy) from LinearEquiv.ext fun v => rfl] at h
  have hdet : ContinuousAt
      (fun y => LinearMap.det (((C y).toLinearEquiv) : E →ₗ[ℝ] E)) x :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hC
  have hxC : LinearMap.det (((C x).toLinearEquiv) : E →ₗ[ℝ] E) ≠ 0 :=
    (C x).toLinearEquiv.isUnit_det'.ne_zero
  have htrans (y : M) (hyT : y ∈ t.baseSet) (hyS : y ∈ S.baseSet) :
      (S.linearEquivAt ℝ y hyS) =
        (t.linearEquivAt ℝ y hyT).trans ((C y).toLinearEquiv) := by
    have hC' : (C y).toLinearEquiv =
        (t.linearEquivAt ℝ y hyT).symm.trans (S.linearEquivAt ℝ y hyS) :=
      LinearEquiv.coe_injective (Bundle.Trivialization.coe_coordChangeL (R := ℝ) t S ⟨hyT, hyS⟩)
    calc (S.linearEquivAt ℝ y hyS)
        = (t.linearEquivAt ℝ y hyT).trans
            ((t.linearEquivAt ℝ y hyT).symm.trans (S.linearEquivAt ℝ y hyS)) := by
          rw [← LinearEquiv.trans_assoc, LinearEquiv.self_trans_symm, LinearEquiv.refl_trans]
      _ = (t.linearEquivAt ℝ y hyT).trans ((C y).toLinearEquiv) := by rw [← hC']
  rcases lt_or_gt_of_ne hxC with hneg | hpos
  · have hmem : {y : M | y ∈ U ∧ y ∈ S.baseSet ∧
        LinearMap.det (((C y).toLinearEquiv) : E →ₗ[ℝ] E) < 0} ∈ nhds x :=
      Filter.inter_mem hUx
        (Filter.inter_mem (S.open_baseSet.mem_nhds hxS)
          (hdet.eventually (isOpen_Iio.mem_nhds hneg)))
    obtain ⟨U', hU'sub, hU'open, hxU'⟩ := _root_.mem_nhds_iff.mp hmem
    refine ⟨U', hU'open, hxU', fun y hy => (hU'sub hy).2.1, fun y hy => ?_⟩
    obtain ⟨hyU, hyS, hyneg⟩ := hU'sub hy
    have hyT : y ∈ t.baseSet := hU hyU
    have hmapy : Orientation.map (Fin n) (S.linearEquivAt ℝ y hyS) (o y) = -q := by
      rw [htrans y hyT hyS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL y hyU, (Orientation.map_eq_neg_iff_det_neg q (C y).toLinearEquiv hcard).2 hyneg]
    have hmapx : Orientation.map (Fin n) (S.linearEquivAt ℝ x hxS) (o x) = -q := by
      rw [htrans x hxT hxS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL x (mem_of_mem_nhds hUx),
        (Orientation.map_eq_neg_iff_det_neg q (C x).toLinearEquiv hcard).2 hneg]
    simp only [tangentChartEquiv]
    rw [hmapy, hmapx]
  · have hmem : {y : M | y ∈ U ∧ y ∈ S.baseSet ∧
        0 < LinearMap.det (((C y).toLinearEquiv) : E →ₗ[ℝ] E)} ∈ nhds x :=
      Filter.inter_mem hUx
        (Filter.inter_mem (S.open_baseSet.mem_nhds hxS)
          (hdet.eventually (isOpen_Ioi.mem_nhds hpos)))
    obtain ⟨U', hU'sub, hU'open, hxU'⟩ := _root_.mem_nhds_iff.mp hmem
    refine ⟨U', hU'open, hxU', fun y hy => (hU'sub hy).2.1, fun y hy => ?_⟩
    obtain ⟨hyU, hyS, hypos⟩ := hU'sub hy
    have hyT : y ∈ t.baseSet := hU hyU
    have hmapy : Orientation.map (Fin n) (S.linearEquivAt ℝ y hyS) (o y) = q := by
      rw [htrans y hyT hyS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL y hyU, (Orientation.map_eq_iff_det_pos q (C y).toLinearEquiv hcard).2 hypos]
    have hmapx : Orientation.map (Fin n) (S.linearEquivAt ℝ x hxS) (o x) = q := by
      rw [htrans x hxT hxS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL x (mem_of_mem_nhds hUx),
        (Orientation.map_eq_iff_det_pos q (C x).toLinearEquiv hcard).2 hpos]
    simp only [tangentChartEquiv]
    rw [hmapy, hmapx]

end Manifold

theorem exists_smooth_quotient : Nonempty G.SmoothQuotient := by
  classical
  have hT2 : T2Space (Quotient (MulAction.orbitRel G.group SphereThree)) := inferInstance
  obtain ⟨O, hO⟩ := Manifold.exists_manifoldOrientation_eq_of_compatibleOrientation
    (E := EuclideanSpace ℝ (Fin 3)) (hdim := by simp)
    (o := quotientOrientationField G) (ho := quotientOrientationField_compatible G)
  refine ⟨{
    charts := quotientChartedSpaceAux G
    smooth := quotientIsManifoldAux G
    hausdorff := hT2
    compact := inferInstance
    connected := inferInstance
    local_diffeomorph := projection_localDiffeomorph_aux G
    covering := projection_covering_aux G
    orientation := O
    positive := fun x => by
      rw [hO]
      exact (quotientOrientationField_projection G x).symm }⟩


def smoothQuotient : G.SmoothQuotient := Classical.choice G.exists_smooth_quotient

instance orbitChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.Orbit :=
  G.smoothQuotient.charts

instance orbitIsManifold : IsManifold (𝓡 3) ∞ G.Orbit := G.smoothQuotient.smooth

instance orbitT2Space : T2Space G.Orbit := G.smoothQuotient.hausdorff

instance orbitCompactSpace : CompactSpace G.Orbit := G.smoothQuotient.compact

instance orbitConnectedSpace : ConnectedSpace G.Orbit := G.smoothQuotient.connected

def manifold : ConnectedClosedOrientedManifold 3 where
  Carrier := G.Orbit
  orientation := G.smoothQuotient.orientation

@[simp] theorem manifold_carrier : G.manifold.Carrier = G.Orbit := rfl

theorem projection_isLocalDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ G.projection :=
  G.smoothQuotient.local_diffeomorph

theorem projection_isCoveringMap : IsCoveringMap G.projection := G.smoothQuotient.covering

noncomputable def fundamentalGroupEquivOfFiber
    {p : G.manifold.Carrier} (e : G.projection ⁻¹' {p}) :
    FundamentalGroup G.manifold.Carrier p ≃* G.group :=
  ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G.group)
      (E := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)).fundamentalGroupEquiv e).trans
    (MulEquiv.inv' G.group).symm

noncomputable def fundamentalGroupManifoldEquiv (p : G.manifold.Carrier) :
    FundamentalGroup G.manifold.Carrier p ≃* G.group :=
  G.fundamentalGroupEquivOfFiber
    ⟨Classical.choose (G.projection_surjective p),
      Classical.choose_spec (G.projection_surjective p)⟩

theorem nonempty_fundamentalGroupManifoldEquiv (p : G.manifold.Carrier) :
    Nonempty (FundamentalGroup G.manifold.Carrier p ≃* G.group) :=
  ⟨G.fundamentalGroupManifoldEquiv p⟩

theorem fundamentalGroupEquivOfFiber_north_eq :
    G.fundamentalGroupEquivOfFiber ⟨sphereThreeNorth, rfl⟩ =
      fundamentalGroupFiniteFreeSphereThreeQuotientEquiv (G := G.group) := rfl

theorem projection_positive (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Orientation.map (Fin 3)
      (G.projection_isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      ((sphereOrientation 3 (by decide)).orientation x) =
        G.manifold.orientation.orientation (G.projection x) :=
  G.smoothQuotient.positive x

end SphericalSpaceFormGroup

abbrev SphereTwoTimesCircle :=
  sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

theorem exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle
    (p : SphereTwoTimesCircle) :
    Nonempty (FundamentalGroup SphereTwoTimesCircle p ≃* Multiplicative ℤ) :=
  ⟨fundamentalGroupProdSphereOneEquivInt p.1 p.2⟩

def sphereTwoTimesCircleOrientation :
    ManifoldOrientation ((𝓡 2).prod (𝓡 1)) SphereTwoTimesCircle 3 :=
  productOrientation (𝓡 2) (𝓡 1) (by decide) (by decide)
    (sphereOrientation 2 (by decide)) (sphereOrientation 1 (by decide))

def isStandardFactor (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  (∃ G : SphericalSpaceFormGroup,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      M.toClosedOrientedManifold G.manifold.toClosedOrientedManifold)) ∨
  ∃ f : M.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle,
    f.preservesOrientation M.orientation sphereTwoTimesCircleOrientation

theorem isStandardFactor_spherical (G : SphericalSpaceFormGroup) :
    isStandardFactor G.manifold :=
  Or.inl ⟨G, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

end DifferentialGeometry.Topology
