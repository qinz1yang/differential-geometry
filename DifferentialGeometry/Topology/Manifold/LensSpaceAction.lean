import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

set_option autoImplicit false

noncomputable section

open Bundle Metric Module
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private abbrev LensAmbient := EuclideanSpace ℝ (Fin 4)
private abbrev LensSphereSpace := sphere (0 : LensAmbient) 1
private abbrev LensBlock := WithLp 2 (ℂ × ℂ)

private noncomputable def lensBlockEquiv : LensAmbient ≃ₗᵢ[ℝ] LensBlock :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSumFinEquiv (m := 2) (n := 2)).symm).trans
    (Complex.orthonormalBasisOneI.prod Complex.orthonormalBasisOneI).repr.symm

private theorem lensBlockRotation_one :
    LinearIsometryEquiv.withLpProdCongr (p := 2) (𝕜 := ℝ)
      (1 : ℂ ≃ₗᵢ[ℝ] ℂ) (1 : ℂ ≃ₗᵢ[ℝ] ℂ) = 1 := by
  ext x
  rw [WithLp.ext_iff]
  rw [LinearIsometryEquiv.withLpProdCongr_apply, WithLp.ofLp_toLp]
  rfl

private theorem lensBlockRotation_mul (f f' g g' : ℂ ≃ₗᵢ[ℝ] ℂ) :
    LinearIsometryEquiv.withLpProdCongr (p := 2) (𝕜 := ℝ) (f * f') (g * g') =
      LinearIsometryEquiv.withLpProdCongr (p := 2) (𝕜 := ℝ) f g *
        LinearIsometryEquiv.withLpProdCongr (p := 2) (𝕜 := ℝ) f' g' := by
  ext x
  rw [WithLp.ext_iff]
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply,
    LinearIsometryEquiv.withLpProdCongr_apply, WithLp.ofLp_toLp, WithLp.toLp_fst,
    WithLp.toLp_snd]

private noncomputable def lensBlockRotation : Circle →* (LensBlock ≃ₗᵢ[ℝ] LensBlock) where
  toFun u := LinearIsometryEquiv.withLpProdCongr (p := 2) (𝕜 := ℝ) (rotation u) (rotation u)
  map_one' := by
    rw [map_one]
    exact lensBlockRotation_one
  map_mul' u v := by
    rw [map_mul]
    exact lensBlockRotation_mul (rotation u) (rotation v) (rotation u) (rotation v)

private noncomputable def lensScalarActionFun (u : Circle) :
    LensAmbient ≃ₗᵢ[ℝ] LensAmbient :=
  lensBlockEquiv.trans ((lensBlockRotation u).trans lensBlockEquiv.symm)

private noncomputable def lensScalarAction : Circle →* (LensAmbient ≃ₗᵢ[ℝ] LensAmbient) where
  toFun u := lensScalarActionFun u
  map_one' := by
    change lensScalarActionFun 1 = 1
    simp only [lensScalarActionFun, map_one, LinearIsometryEquiv.refl_trans,
      LinearIsometryEquiv.self_trans_symm, LinearIsometryEquiv.one_def]
  map_mul' u v := by
    ext x
    simp only [lensScalarActionFun, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.coe_mul, Function.comp_apply, map_mul,
      LinearIsometryEquiv.apply_symm_apply]

private theorem lensScalarAction_apply (u : Circle) (x : LensAmbient) :
    lensBlockEquiv (lensScalarAction u x) = lensBlockRotation u (lensBlockEquiv x) := by
  simp [lensScalarAction, lensScalarActionFun]

private theorem lensBlockRotation_apply (u : Circle) (z : LensBlock) :
    lensBlockRotation u z = WithLp.toLp 2 ((rotation u) z.fst, (rotation u) z.snd) :=
  LinearIsometryEquiv.withLpProdCongr_apply 2 (rotation u) (rotation u) z

private theorem lensBlockRotation_fst (u : Circle) (z : LensBlock) :
    (lensBlockRotation u z).fst = (rotation u) z.fst := by
  rw [lensBlockRotation_apply, WithLp.toLp_fst]

private theorem lensBlockRotation_snd (u : Circle) (z : LensBlock) :
    (lensBlockRotation u z).snd = (rotation u) z.snd := by
  rw [lensBlockRotation_apply, WithLp.toLp_snd]

private theorem lensBlockEquiv_ne_zero {x : LensAmbient} (hx : x ≠ 0) :
    lensBlockEquiv x ≠ 0 := fun h => hx (lensBlockEquiv.injective (by rw [h, map_zero]))

private theorem circle_eq_one_of_rotation_eq_self {u : Circle} {z : ℂ} (hz : z ≠ 0)
    (h : (rotation u) z = z) : u = 1 := by
  have h0 : ((u : ℂ) - 1) * z = 0 := by
    rw [rotation_apply] at h
    rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Subtype.ext (by simpa using sub_eq_zero.mp h1)
  · exact absurd h1 hz

private theorem lensScalarAction_eq_one_of_apply_eq_self {u : Circle} {x : LensAmbient}
    (hx : x ≠ 0) (h : lensScalarAction u x = x) : u = 1 := by
  set z := lensBlockEquiv x with hz
  have hz0 : z ≠ 0 := lensBlockEquiv_ne_zero hx
  have hfix : lensBlockRotation u z = z := by
    have := congrArg lensBlockEquiv h
    simpa only [hz, lensScalarAction_apply] using this
  have hfst : (rotation u) z.fst = z.fst := by
    rw [← lensBlockRotation_fst, hfix]
  have hsnd : (rotation u) z.snd = z.snd := by
    rw [← lensBlockRotation_snd, hfix]
  rcases eq_or_ne z.fst 0 with h1 | h1
  · have h2 : z.snd ≠ 0 := fun h2 => hz0 (by
      rw [WithLp.ext_iff, WithLp.ofLp_zero, Prod.ext_iff]
      exact ⟨by simpa using h1, by simpa using h2⟩)
    exact circle_eq_one_of_rotation_eq_self h2 hsnd
  · exact circle_eq_one_of_rotation_eq_self h1 hfst

private noncomputable def lensProbe : LensBlock := WithLp.toLp 2 ((1 : ℂ), (0 : ℂ))

private theorem lensBlockRotation_probe (u : Circle) :
    lensBlockRotation u lensProbe = WithLp.toLp 2 ((u : ℂ), 0) := by
  rw [lensBlockRotation_apply, lensProbe, rotation_apply]
  simp

private theorem lensScalarAction_injective : Function.Injective lensScalarAction := by
  intro u u' h
  have h2 : lensBlockRotation u lensProbe = lensBlockRotation u' lensProbe := by
    have h3 := congrArg (fun e : LensAmbient ≃ₗᵢ[ℝ] LensAmbient =>
      lensBlockEquiv (e (lensBlockEquiv.symm lensProbe))) h
    simpa only [lensScalarAction_apply, LinearIsometryEquiv.apply_symm_apply] using h3
  rw [lensBlockRotation_probe, lensBlockRotation_probe] at h2
  exact Subtype.ext (by simpa [WithLp.toLp_fst] using congrArg WithLp.fst h2)

noncomputable def lensSpaceAction (N : ℕ) [NeZero N] :
    Multiplicative (ZMod N) →*
      (EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :=
  lensScalarAction.comp ZMod.toCircle.toMonoidHom

private theorem lensSpaceAction_apply (N : ℕ) [NeZero N] (w : Multiplicative (ZMod N)) :
    lensSpaceAction N w =
      lensScalarAction (ZMod.toCircle (Multiplicative.toAdd w)) := rfl

theorem lensSpaceAction_injective_apply (N : ℕ) [NeZero N] :
    Function.Injective (lensSpaceAction N) := by
  intro w w' h
  rw [lensSpaceAction_apply, lensSpaceAction_apply] at h
  have h1 : ZMod.toCircle (Multiplicative.toAdd w) =
      ZMod.toCircle (Multiplicative.toAdd w') := lensScalarAction_injective h
  exact Multiplicative.toAdd.injective (ZMod.injective_toCircle h1)

private theorem lensSpaceAction_range_free (N : ℕ) [NeZero N]
    (γ : (lensSpaceAction N).range) (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hx : Geometry.sphereDiffeo (n := 3) γ.val x = x) : γ = 1 := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp γ.2
  have hxval : γ.val (x : EuclideanSpace ℝ (Fin 4)) = (x : EuclideanSpace ℝ (Fin 4)) := by
    have h := congrArg Subtype.val hx
    simpa only [Geometry.sphereDiffeo_coe] using h
  have hself : lensScalarAction (ZMod.toCircle (Multiplicative.toAdd w))
      (x : EuclideanSpace ℝ (Fin 4)) = (x : EuclideanSpace ℝ (Fin 4)) := by
    rw [← hw, lensSpaceAction_apply] at hxval
    exact hxval
  have hx0 : (x : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
    intro h
    have h1 := mem_sphere_zero_iff_norm.mp x.2
    rw [h, norm_zero] at h1
    norm_num at h1
  have hval : γ.val = 1 := by
    rw [← hw, lensSpaceAction_apply,
      lensScalarAction_eq_one_of_apply_eq_self hx0 hself, map_one]
  exact Subtype.ext (by simpa using hval)

noncomputable def lensSpaceGroup (N : ℕ) [NeZero N] : SphericalSpaceFormGroup where
  group := (lensSpaceAction N).range
  finite := Finite.of_surjective
    (fun w : Multiplicative (ZMod N) =>
      (⟨lensSpaceAction N w, MonoidHom.mem_range.mpr ⟨w, rfl⟩⟩ :
        (lensSpaceAction N).range))
    (fun γ => by
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp γ.2
      exact ⟨w, Subtype.ext hw⟩)
  positive := by
    intro γ
    by_cases h : γ = 1
    · have hv : γ.val = 1 := congrArg Subtype.val h
      rw [hv]
      exact Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one _ (by
        change LinearMap.det (1 : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin 4)) = 1
        exact LinearMap.det_id)
    · exact Geometry.sphereDiffeo_preservesOrientation_of_fixed_point_free _
        (fun x hx => h (lensSpaceAction_range_free N γ x hx))
  free := fun γ x hx => lensSpaceAction_range_free N γ x hx

theorem lensSpaceGroup_card (N : ℕ) [NeZero N] :
    Nat.card ↥(lensSpaceGroup N).group = N := by
  have hinj := lensSpaceAction_injective_apply N
  change Nat.card ↥(lensSpaceAction N).range = N
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem lensSpaceGroup_projection_fiber_ncard (N : ℕ) [NeZero N]
    (x : (lensSpaceGroup N).Orbit) :
    ((lensSpaceGroup N).projection ⁻¹' {x}).ncard = N := by
  have hf : IsQuotientCoveringMap ((lensSpaceGroup N).projection) (lensSpaceGroup N).group :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  obtain ⟨y, hy⟩ := (lensSpaceGroup N).projection_surjective x
  have h := Nat.card_congr (hf.fiberEquivGroup (x := x) ⟨y, hy⟩)
  rw [← Nat.card_coe_set_eq, h, lensSpaceGroup_card N]

theorem lensSpaceGroup_fundamentalGroup_card (N : ℕ) [NeZero N]
    (p : (lensSpaceGroup N).manifold.Carrier) :
    Nat.card (FundamentalGroup (lensSpaceGroup N).manifold.Carrier p) = N := by
  rw [Nat.card_congr ((lensSpaceGroup N).fundamentalGroupManifoldEquiv p).toEquiv,
    lensSpaceGroup_card N]

theorem lensSpaceGroup_two_not_subsingleton :
    ¬ Subsingleton ↥(lensSpaceGroup 2).group := by
  intro h
  have h1 : Nat.card ↥(lensSpaceGroup 2).group = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨h, ⟨1⟩⟩
  rw [lensSpaceGroup_card 2] at h1
  norm_num at h1

end DifferentialGeometry.Topology
