import DifferentialGeometry.Geometry.Exponential.Flat.AffineTranslations
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Constructed axes of Euclidean affine isometries

Orthogonal decomposition along the fixed linear subspace constructs an actual point where the
isometry translates by a fixed vector. That vector realizes the minimum displacement. These
objects supply the axis geometry for the translation restriction in the Bieberbach argument;
no axis, minimum point, or translation subgroup is supplied as an input.
-/

set_option autoImplicit false

noncomputable section

open Set Submodule

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

theorem exists_affineAxis_point (g : V ≃ᵃⁱ[ℝ] V) :
    ∃ p q : V, g p = p + q ∧ g.linearIsometryEquiv q = q := by
  let L := g.linearIsometryEquiv
  let T : V →ₗ[ℝ] V := (L : V →ₗ[ℝ] V) - LinearMap.id
  let K := T.ker
  have hfixed : ∀ u ∈ K, L u = u := by
    intro u hu
    exact sub_eq_zero.mp hu
  have hinv : ∀ w ∈ Kᗮ, L w ∈ Kᗮ := by
    intro w hw u hu
    rw [← hfixed u hu, L.inner_map_map]
    exact hw u hu
  let A : Kᗮ →ₗ[ℝ] Kᗮ :=
    { toFun := fun w => ⟨L w - w, Kᗮ.sub_mem (hinv w w.property) w.property⟩
      map_add' := by intro w z; apply Subtype.ext; simp; abel
      map_smul' := by intro a w; apply Subtype.ext; simp [smul_sub] }
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hwK : (w : V) ∈ K := congrArg Subtype.val hw
    have hz : inner ℝ (w : V) (w : V) = 0 := w.property w hwK
    apply Subtype.ext
    exact inner_self_eq_zero.mp hz
  obtain ⟨q, hq, hw⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := K) (g 0)
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective.mp hAinj) (-⟨g 0 - q, hw⟩)
  have hpval : L (p : V) - p = -(g 0 - q) := congrArg Subtype.val hp
  refine ⟨p, q, ?_, hfixed q hq⟩
  rw [affineIsometry_apply]
  change L (p : V) + g 0 = (p : V) + q
  linear_combination (norm := abel) hpval

omit instFD in
theorem affine_axis_norm_min (g : V ≃ᵃⁱ[ℝ] V) {p q : V}
    (hp : g p = p + q) (hq : g.linearIsometryEquiv q = q) (x : V) :
    ‖q‖ ≤ ‖g x - x‖ := by
  let L := g.linearIsometryEquiv
  have hinner : inner ℝ q (L (x - p) - (x - p)) = 0 := by
    rw [inner_sub_right, ← hq, L.inner_map_map, hq, sub_self]
  have hdiff : g x - x = q + (L (x - p) - (x - p)) := by
    have hgx := affineIsometry_apply g x
    have hgp := affineIsometry_apply g p
    rw [hp] at hgp
    change g x - x = q + (g.linearIsometryEquiv (x - p) - (x - p))
    rw [map_sub]
    linear_combination (norm := abel) hgx - hgp
  have hsquare := norm_add_sq_real q (L (x - p) - (x - p))
  rw [hinner, mul_zero, add_zero] at hsquare
  rw [hdiff]
  nlinarith [norm_nonneg q, norm_nonneg (q + (L (x - p) - (x - p))),
    sq_nonneg ‖L (x - p) - (x - p)‖]

omit instFD in
theorem affine_axis_vector_unique (g : V ≃ᵃⁱ[ℝ] V) {p q p' q' : V}
    (hp : g p = p + q) (hq : g.linearIsometryEquiv q = q)
    (hp' : g p' = p' + q') (hq' : g.linearIsometryEquiv q' = q') : q = q' := by
  have hdiff : q - q' = g.linearIsometryEquiv (p - p') - (p - p') := by
    have h := g.map_vsub p p'
    simp only [hp, hp', vsub_eq_sub, map_sub] at h
    rw [map_sub]
    linear_combination (norm := abel) -h
  have hfixed : g.linearIsometryEquiv (q - q') = q - q' := by rw [map_sub, hq, hq']
  have hzero : inner ℝ (q - q') (q - q') = 0 := by
    calc
      inner ℝ (q - q') (q - q') =
          inner ℝ (q - q') (g.linearIsometryEquiv (p - p') - (p - p')) :=
        congrArg (fun z => inner ℝ (q - q') z) hdiff
      _ = 0 := by
        rw [inner_sub_right, ← hfixed, g.linearIsometryEquiv.inner_map_map, hfixed, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

omit instFD in
theorem affine_axis_conjugate (g k : V ≃ᵃⁱ[ℝ] V) {p q : V}
    (hp : g p = p + q) (hq : g.linearIsometryEquiv q = q) :
    (k * g * k⁻¹) (k p) = k p + k.linearIsometryEquiv q ∧
      (k * g * k⁻¹).linearIsometryEquiv (k.linearIsometryEquiv q) =
        k.linearIsometryEquiv q := by
  constructor
  · change k (g (k.symm (k p))) = k p + k.linearIsometryEquiv q
    rw [k.symm_apply_apply, hp]
    simpa [add_comm] using k.map_vadd p q
  · have hki := congrArg (fun A : V ≃ₗᵢ[ℝ] V => A q)
      (affineLinearHom.map_mul k⁻¹ k)
    simp only [inv_mul_cancel, map_one] at hki
    change q = (k⁻¹).linearIsometryEquiv (k.linearIsometryEquiv q) at hki
    change k.linearIsometryEquiv
      (g.linearIsometryEquiv ((k⁻¹).linearIsometryEquiv (k.linearIsometryEquiv q))) =
        k.linearIsometryEquiv q
    rw [← hki, hq]

end DifferentialGeometry.Geometry.FlatSurface
