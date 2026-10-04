import DifferentialGeometry.Geometry.Thurston.SphericalProductIsometry
import DifferentialGeometry.Geometry.Thurston.SphericalProductDevelopingMap
import DifferentialGeometry.Geometry.Thurston.SphericalProductOrientation
import DifferentialGeometry.Geometry.Metric.LocalIsometryCovering
import DifferentialGeometry.Topology.Covering.CylindricalModel
import DifferentialGeometry.Topology.Covering.SmoothLift

/-!
# Closed `S² × ℝ` manifolds are quotients of the model

Chapter 7, packet P8b, tier 3. Let `f : S² × ℝ → P` be a local isometry from the model
`sphericalProductModelMetric` to a closed connected oriented `3`-manifold (a developing map).

* `isCoveringMap_of_developing`: `f` is a surjective covering map, since the model is complete
  (`isCoveringMap_of_isLocalIsometry`).
* `exists_deck_of_eq`: two points with the same image are related by a product isometry `γ`
  with `f ∘ cylinderAct γ = f`. The model is simply connected, so `f` lifts through itself
  (`exists_smooth_lift_of_simplyConnected`); the lift is an isometry of the model, hence a
  product isometry (`exists_cylinderIsometry_of_isometry`).
* `developingDeckGroup f`, the product isometries commuting with `f`, acts freely (lifts of `f`
  agreeing at a point agree) and preserves orientation (`det_eq_lineSign_of_comp_eq`), and `f`
  is a `CylinderQuotientPresentation` of `P` by it
  (`exists_cylinderQuotientPresentation_of_developing`).
* `sphericalProductUniversalCover`: the named statement `SphericalProductUniversalCover`, with
  the developing map of `exists_developing_of_modelAtlas`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace GC.Geometry.SphericalProduct

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CI" => SpatialNeckCylinderModel

universe u

private local instance universalCoverNeZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩

def developingDeckGroup {M : Type*} (f : SpatialNeckCylinder → M) :
    Subgroup CylinderIsometry where
  carrier := {γ | ∀ p, f (cylinderAct γ p) = f p}
  one_mem' := fun p => by rw [cylinderAct_one]
  mul_mem' := by
    intro γ δ hγ hδ p
    change f (cylinderAct (γ * δ) p) = f p
    rw [cylinderAct_mul, hγ, hδ]
  inv_mem' := by
    intro γ hγ p
    change f (cylinderAct γ⁻¹ p) = f p
    rw [← hγ (cylinderAct γ⁻¹ p), ← cylinderAct_mul, mul_inv_cancel, cylinderAct_one]

theorem mem_developingDeckGroup_iff {M : Type*} (f : SpatialNeckCylinder → M)
    (γ : CylinderIsometry) :
    γ ∈ developingDeckGroup f ↔ ∀ p, f (cylinderAct γ p) = f p := Iff.rfl

theorem eq_one_of_cylinderAct_eq_self {γ : CylinderIsometry}
    (h : ∀ p : SpatialNeckCylinder, cylinderAct γ p = p) : γ = 1 := by
  let x₀ : SpatialNeckSphere := ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
    simp only [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩
  have hsph : ∀ x : SpatialNeckSphere, γ.1 (x : E3) = x := fun x =>
    congrArg (fun q : SpatialNeckCylinder => (q.1 : E3)) (h (x, 0))
  have hlin : ∀ v : E3, γ.1 v = v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, map_zero]
    · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      let x : SpatialNeckSphere := ⟨‖v‖⁻¹ • v, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]⟩
      have hx := hsph x
      have hvx : v = ‖v‖ • (x : E3) := by
        change v = ‖v‖ • (‖v‖⁻¹ • v)
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      rw [hvx, map_smul, hx]
  have hline : ∀ s : ℝ, γ.2 s = s := fun s => congrArg Prod.snd (h (x₀, s))
  refine Prod.ext ?_ ?_
  · exact LinearIsometryEquiv.ext fun v => hlin v
  · exact AffineIsometryEquiv.ext fun s => hline s

section Developing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] (g : SmoothRiemannianMetric (𝓡 3) M) {f : SpatialNeckCylinder → M}
  (hf : IsLocalDiffeomorph CI (𝓡 3) ∞ f)
  (hiso : ∀ (x : SpatialNeckCylinder) (v w : TangentSpace CI x),
    g.inner (f x) (mfderiv CI (𝓡 3) f x v) (mfderiv CI (𝓡 3) f x w) =
      sphericalProductModelMetric.inner x v w)

include hf hiso in
theorem isCoveringMap_of_developing [ConnectedSpace M] : IsCoveringMap f ∧ Function.Surjective f :=
  isCoveringMap_of_isLocalIsometry sphericalProductModelMetric g sphericalProductModel_complete hf
    hiso

omit [T2Space M] in
include hf hiso in
theorem exists_deck_of_eq (hcov : IsCoveringMap f) {a b : SpatialNeckCylinder} (hab : f a = f b) :
    ∃ γ : CylinderIsometry, (∀ p, f (cylinderAct γ p) = f p) ∧ cylinderAct γ a = b := by
  let : SimplyConnectedSpace SpatialNeckCylinder := simplyConnectedSpace_sphereTwo_prod_real
  have hfs : ContMDiff CI (𝓡 3) ∞ f := hf.contMDiff
  obtain ⟨τ, hτa, hτf, hτs⟩ := exists_smooth_lift_of_simplyConnected hcov hf f hfs a b hab.symm
  obtain ⟨τ', hτ'b, hτ'f, hτ's⟩ := exists_smooth_lift_of_simplyConnected hcov hf f hfs b a hab
  have hleft : (τ' : SpatialNeckCylinder → SpatialNeckCylinder) ∘ τ = id :=
    hcov.eq_of_comp_eq (τ'.continuous.comp τ.continuous) continuous_id
      (funext fun x => by simp only [Function.comp_apply, id_eq, hτ'f, hτf]) a
      (by simp only [Function.comp_apply, hτa, hτ'b, id_eq])
  have hright : (τ : SpatialNeckCylinder → SpatialNeckCylinder) ∘ τ' = id :=
    hcov.eq_of_comp_eq (τ.continuous.comp τ'.continuous) continuous_id
      (funext fun x => by simp only [Function.comp_apply, id_eq, hτ'f, hτf]) b
      (by simp only [Function.comp_apply, hτa, hτ'b, id_eq])
  let Φ : SpatialNeckCylinder ≃ₘ⟮CI, CI⟯ SpatialNeckCylinder :=
    { toFun := τ
      invFun := τ'
      left_inv := fun x => congrFun hleft x
      right_inv := fun x => congrFun hright x
      contMDiff_toFun := hτs
      contMDiff_invFun := hτ's }
  have hΦ : ∀ (p : SpatialNeckCylinder) (V W : TangentSpace CI p),
      sphericalProductModelMetric.inner (Φ p) (mfderiv CI CI Φ p V) (mfderiv CI CI Φ p W) =
        sphericalProductModelMetric.inner p V W := by
    intro p V W
    have hcomp : f ∘ (Φ : SpatialNeckCylinder → SpatialNeckCylinder) = f :=
      funext fun x => hτf x
    have hchain : ∀ Z : TangentSpace CI p,
        mfderiv CI (𝓡 3) f (Φ p) (mfderiv CI CI Φ p Z) = mfderiv CI (𝓡 3) f p Z := by
      intro Z
      rw [← mfderiv_comp_apply p (hf.mdifferentiable (by simp) (Φ p))
        (Φ.mdifferentiable (by simp) p) Z, hcomp]
    rw [← hiso (Φ p), hchain, hchain, ← hiso p]
    rw [show f (Φ p) = f p from hτf p]
  obtain ⟨γ, hγ⟩ := exists_cylinderIsometry_of_isometry Φ hΦ
  refine ⟨γ, fun p => ?_, ?_⟩
  · rw [← hγ p]
    exact hτf p
  · rw [← hγ a]
    exact hτa

omit [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem developingDeckGroup_free (hcov : IsCoveringMap f) :
    ∀ γ ∈ developingDeckGroup f, γ ≠ 1 → ∀ p : SpatialNeckCylinder, cylinderAct γ p ≠ p := by
  intro γ hγ hne p hp
  apply hne
  have heq : cylinderAct γ = id :=
    hcov.eq_of_comp_eq (cylinderActDiffeo γ).continuous continuous_id (funext fun q => hγ q) p hp
  exact eq_one_of_cylinderAct_eq_self fun q => congrFun heq q

include hf hiso in
theorem exists_cylinderQuotientPresentation_of_developing [ConnectedSpace M]
    (o : ManifoldOrientation (𝓡 3) M 3) :
    ∃ G : Subgroup CylinderIsometry,
      (∀ γ ∈ G, γ ≠ 1 → ∀ p : SpatialNeckCylinder, cylinderAct γ p ≠ p) ∧
      (∀ γ ∈ G, LinearMap.det (γ.1.toLinearEquiv : E3 →ₗ[ℝ] E3) = lineSign γ.2) ∧
      Nonempty (CylinderQuotientPresentation G M) := by
  obtain ⟨hcov, hsurj⟩ := isCoveringMap_of_developing g hf hiso
  refine ⟨developingDeckGroup f, developingDeckGroup_free hcov,
    fun γ hγ => det_eq_lineSign_of_comp_eq hf o γ hγ, ⟨?_⟩⟩
  refine
    { proj := f
      isLocalDiffeomorph := hf
      surjective := hsurj
      fibres := fun a b => ⟨fun hab => ?_, ?_⟩ }
  · obtain ⟨γ, hγ, hγa⟩ := exists_deck_of_eq g hf hiso hcov hab
    exact ⟨γ, hγ, hγa⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact (hγ a).symm

end Developing

theorem sphericalProductUniversalCover : SphericalProductUniversalCover.{u} := by
  intro P g hg
  have hA : GC.Geometry.HasThurstonAtlas g.metric .sphericalProduct := hg ▸ g.atlas
  obtain ⟨f, hf, hiso⟩ := exists_developing_of_modelAtlas g.metric g.complete hA
  exact exists_cylinderQuotientPresentation_of_developing g.metric hf hiso P.orientation

end GC.Geometry.SphericalProduct
