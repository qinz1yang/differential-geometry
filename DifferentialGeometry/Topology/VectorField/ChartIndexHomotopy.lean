import DifferentialGeometry.Topology.VectorField.ChartIndexSum
import DifferentialGeometry.Topology.VectorField.Transport
import DifferentialGeometry.Topology.LocalDegree.FiniteAdditivity
import DifferentialGeometry.Topology.LocalDegree.BallBoundaryHomotopy
import DifferentialGeometry.Topology.Homotopy.NonzeroPerturbation

set_option autoImplicit false
noncomputable section
open Set Metric Filter Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I 1 M]
  (e : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
    (EuclideanSpace ℝ (Fin (d + 1))) M 1)
  {a : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
  (hsource : closedBall a r ⊆ e.source)
  (V : ∀ x : M, TangentSpace I x)
  (hV : ContinuousOn (fun x => (⟨x, V x⟩ : TangentBundle I M)) e.target)

include hsource hV in
private theorem continuousOn_components :
    ContinuousOn (_root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V) (closedBall a r) :=
  (contDiffOn_zero.mp (contMDiffOn_vectorSpace_iff_contDiffOn.mp
    (contMDiffOn_mpullback_partialDiffeomorph e (m := 0) (by norm_num)
      (contMDiffOn_zero_iff.mpr hV)))).mono hsource

private def componentBallMap : C(closedBall a r, EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨fun y => _root_.VectorField.mpullback
    𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V y.val,
    (continuousOn_components I e hsource V hV).domRestrict⟩

private theorem componentBall_nonzero
    (hb : ∀ y ∈ sphere a r, V (e y) ≠ 0)
    (y : closedBall a r) (hy : y.val ∈ sphere a r) :
    componentBallMap I e hsource V hV y ≠ 0 := by
  intro hz
  exact hb y.val hy ((mpullback_partialDiffeomorph_eq_zero_iff e one_ne_zero V
    (hsource y.property)).mp hz)

private theorem region_sum_eq_ballDegree (hr : 0 < r)
    (hfinite : {x | V x = 0}.Finite)
    (hisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hinterior : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (hb : ∀ y ∈ sphere a r, V (e y) ≠ 0) :
    interiorIndexSumOn I V hfinite hisolated hinterior (e '' closedBall a r) =
      Poincare.LocalDegree.euclideanBallDegree hr (componentBallMap I e hsource V hV)
        (componentBall_nonzero I e hsource V hV hb) := by
  let F := _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V
  have hF : ContinuousOn F (closedBall a r) := continuousOn_components I e hsource V hV
  have hf : {y ∈ closedBall a r | F y = 0}.Finite := by
    have hh := finite_zeroSet_in_parametrization I e V (closedBall a r) hsource hfinite
    exact hh.subset (fun _ h => ⟨h.2,h.1⟩)
  have hFb : ∀ y ∈ sphere a r, F y ≠ 0 := fun y hy hz =>
    hb y hy ((mpullback_partialDiffeomorph_eq_zero_iff e one_ne_zero V
      (hsource (sphere_subset_closedBall hy))).mp hz)
  rw [interiorIndexSumOn_eq_finsum_in_parametrization I e V hfinite hisolated hinterior
    (closedBall a r) hsource]
  change _ = Poincare.LocalDegree.euclideanBallDegree hr
    (⟨fun y => F y.val,hF.domRestrict⟩ : C(closedBall a r,EuclideanSpace ℝ (Fin (d + 1)))) _
  rw [Poincare.LocalDegree.euclideanBallDegree_eq_finsum_localDegrees hr hF hf hFb]
  have hs : {y | F y = 0 ∧ y ∈ closedBall a r} = {y ∈ closedBall a r | F y = 0} :=
    Set.ext (fun _ => and_comm)
  exact finsum_comp_equiv (Equiv.setCongr hs)
    (f := fun p : {y ∈ closedBall a r | F y = 0} => Poincare.LocalDegree.euclideanLocalDegree F p.val
      (Poincare.LocalDegree.isolatedZero_of_finite_closedBall_zeroSet hF hf hFb
        p.property.1 p.property.2))

variable (hr : 0 < r)
  (hfiniteV : {x | V x = 0}.Finite)
  (hisolatedV : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
  (hinteriorV : ∀ x, V x = 0 → I.IsInteriorPoint x)
  (W : ∀ x : M, TangentSpace I x)
  (hW : ContinuousOn (fun x => (⟨x, W x⟩ : TangentBundle I M)) e.target)
  (hfiniteW : {x | W x = 0}.Finite)
  (hisolatedW : ∀ x, W x = 0 → HasContinuousIsolatedZero I W x)
  (hinteriorW : ∀ x, W x = 0 → I.IsInteriorPoint x)
include hsource hV hr hW

theorem interiorIndexSumOn_eq_of_parametrization_boundaryHomotopy
    (K : C(unitInterval × sphere a r, EuclideanSpace ℝ (Fin (d + 1))))
    (hK : ∀ q, K q ≠ 0)
    (h₀ : ∀ y : sphere a r, K (0,y) = _root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V y.val)
    (h₁ : ∀ y : sphere a r, K (1,y) = _root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e W y.val) :
    interiorIndexSumOn I V hfiniteV hisolatedV hinteriorV (e '' closedBall a r) =
      interiorIndexSumOn I W hfiniteW hisolatedW hinteriorW (e '' closedBall a r) := by
  have hbV : ∀ y ∈ sphere a r, V (e y) ≠ 0 := by
    intro y hy hz
    exact hK (0,⟨y,hy⟩) ((h₀ ⟨y,hy⟩).trans
      ((mpullback_partialDiffeomorph_eq_zero_iff e one_ne_zero V
        (hsource (sphere_subset_closedBall hy))).mpr hz))
  have hbW : ∀ y ∈ sphere a r, W (e y) ≠ 0 := by
    intro y hy hz
    exact hK (1,⟨y,hy⟩) ((h₁ ⟨y,hy⟩).trans
      ((mpullback_partialDiffeomorph_eq_zero_iff e one_ne_zero W
        (hsource (sphere_subset_closedBall hy))).mpr hz))
  rw [region_sum_eq_ballDegree I e hsource V hV hr hfiniteV hisolatedV hinteriorV hbV,
    region_sum_eq_ballDegree I e hsource W hW hr hfiniteW hisolatedW hinteriorW hbW]
  exact Poincare.LocalDegree.euclideanBallDegree_eq_of_boundaryHomotopy hr
    (componentBall_nonzero I e hsource V hV hbV)
    (componentBall_nonzero I e hsource W hW hbW) K hK h₀ h₁

theorem interiorIndexSum_eq_of_parametrization_boundaryHomotopy
    (K : C(unitInterval × sphere a r, EuclideanSpace ℝ (Fin (d + 1))))
    (hK : ∀ q, K q ≠ 0)
    (h₀ : ∀ y : sphere a r, K (0,y) = _root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V y.val)
    (h₁ : ∀ y : sphere a r, K (1,y) = _root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e W y.val)
    (houtside : ∀ x ∉ e '' closedBall a r, V =ᶠ[𝓝 x] W) :
    interiorIndexSum I V hfiniteV hisolatedV hinteriorV =
      interiorIndexSum I W hfiniteW hisolatedW hinteriorW := by
  rw [← interiorIndexSumOn_add_compl I V hfiniteV hisolatedV hinteriorV (e '' closedBall a r),
    ← interiorIndexSumOn_add_compl I W hfiniteW hisolatedW hinteriorW (e '' closedBall a r)]
  rw [interiorIndexSumOn_eq_of_parametrization_boundaryHomotopy I e hsource V hV hr
    hfiniteV hisolatedV hinteriorV W hW hfiniteW hisolatedW hinteriorW K hK h₀ h₁,
    interiorIndexSumOn_eq_of_germ I V hfiniteV hisolatedV hinteriorV W hfiniteW
      hisolatedW hinteriorW (e '' closedBall a r)ᶜ houtside]

theorem interiorIndexSumOn_eq_of_parametrization_boundary_eq
    (hbV : ∀ y ∈ sphere a r, V (e y) ≠ 0)
    (hboundary : ∀ y ∈ sphere a r, V (e y) = W (e y)) :
    interiorIndexSumOn I V hfiniteV hisolatedV hinteriorV (e '' closedBall a r) =
      interiorIndexSumOn I W hfiniteW hisolatedW hinteriorW (e '' closedBall a r) := by
  let K : C(unitInterval × sphere a r, EuclideanSpace ℝ (Fin (d + 1))) :=
    ⟨fun q => _root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V q.2.val,
      (continuousOn_components I e hsource V hV).comp_continuous
        (continuous_subtype_val.comp continuous_snd) (fun q => sphere_subset_closedBall q.2.property)⟩
  apply interiorIndexSumOn_eq_of_parametrization_boundaryHomotopy I e hsource V hV hr
    hfiniteV hisolatedV hinteriorV W hW hfiniteW hisolatedW hinteriorW K
  · intro q hz
    exact hbV q.2.val q.2.property ((mpullback_partialDiffeomorph_eq_zero_iff e
      one_ne_zero V (hsource (sphere_subset_closedBall q.2.property))).mp hz)
  · exact fun _ => rfl
  · intro y
    change (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e y.val).inverse (V (e y.val)) =
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e y.val).inverse (W (e y.val))
    rw [hboundary y.val y.property]

theorem interiorIndexSum_eq_of_parametrization_boundary_eq
    (hbV : ∀ y ∈ sphere a r, V (e y) ≠ 0)
    (hboundary : ∀ y ∈ sphere a r, V (e y) = W (e y))
    (houtside : ∀ x ∉ e '' closedBall a r, V =ᶠ[𝓝 x] W) :
    interiorIndexSum I V hfiniteV hisolatedV hinteriorV =
      interiorIndexSum I W hfiniteW hisolatedW hinteriorW := by
  rw [← interiorIndexSumOn_add_compl I V hfiniteV hisolatedV hinteriorV (e '' closedBall a r),
    ← interiorIndexSumOn_add_compl I W hfiniteW hisolatedW hinteriorW (e '' closedBall a r)]
  rw [interiorIndexSumOn_eq_of_parametrization_boundary_eq I e hsource V hV hr
    hfiniteV hisolatedV hinteriorV W hW hfiniteW hisolatedW hinteriorW hbV hboundary,
    interiorIndexSumOn_eq_of_germ I V hfiniteV hisolatedV hinteriorV W hfiniteW
      hisolatedW hinteriorW (e '' closedBall a r)ᶜ houtside]

theorem interiorIndexSumOn_eq_of_parametrization_norm_sub_lt
    (hclose : ∀ y ∈ sphere a r,
      ‖(show EuclideanSpace ℝ (Fin (d + 1)) from
        _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e W y -
        _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V y)‖ <
      ‖(show EuclideanSpace ℝ (Fin (d + 1)) from
        _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V y)‖) :
    interiorIndexSumOn I V hfiniteV hisolatedV hinteriorV (e '' closedBall a r) =
      interiorIndexSumOn I W hfiniteW hisolatedW hinteriorW (e '' closedBall a r) := by
  let F : C(sphere a r, EuclideanSpace ℝ (Fin (d + 1))) :=
    ⟨fun y => _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V y.val,
      (continuousOn_components I e hsource V hV).comp_continuous continuous_subtype_val
        (fun y => sphere_subset_closedBall y.property)⟩
  let G : C(sphere a r, EuclideanSpace ℝ (Fin (d + 1))) :=
    ⟨fun y => _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e W y.val,
      (continuousOn_components I e hsource W hW).comp_continuous continuous_subtype_val
        (fun y => sphere_subset_closedBall y.property)⟩
  let K := ContinuousMap.Homotopy.affine F G
  exact interiorIndexSumOn_eq_of_parametrization_boundaryHomotopy I e hsource V hV hr
    hfiniteV hisolatedV hinteriorV W hW hfiniteW hisolatedW hinteriorW K.toContinuousMap
    (Poincare.Topology.affineHomotopy_ne_zero_of_norm_sub_lt F G (fun y => hclose y.val y.property))
    K.map_zero_left K.map_one_left

end Poincare.VectorField
