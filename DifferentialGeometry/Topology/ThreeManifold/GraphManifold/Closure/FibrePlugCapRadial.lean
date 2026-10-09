import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCapNormal
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalDiffeomorphStraightening
import DifferentialGeometry.Topology.Manifold.ClosedBall.Diffeomorph

/-!
A real radial cap diffeomorphism with the canonical rational boundary germ.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric GC.Endpoint
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

theorem exists_boundedPlugCapRadius :
    ∃ D : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ, StrictMono D ∧
      (D : ℝ → ℝ) =ᶠ[𝓝 0] id ∧
      (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun r => (3 - 2 * r)⁻¹) ∧
      D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
  have hf : ContDiffOn ℝ ∞ (fun r : ℝ => (3 - 2 * r)⁻¹) (Iio (3 / 2)) :=
    (contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id)).inv
      (fun r hr => by
        change r < 3 / 2 at hr
        change 3 - 2 * r ≠ 0
        linarith)
  have hd : deriv (fun r : ℝ => (3 - 2 * r)⁻¹) 1 = 2 := by
    have hh := ((hasDerivAt_const (1 : ℝ) (3 : ℝ)).sub
      ((hasDerivAt_const (1 : ℝ) (2 : ℝ)).mul (hasDerivAt_id 1))).inv (by norm_num)
    change HasDerivAt (fun r : ℝ => (3 - 2 * r)⁻¹)
      (-(0 - (0 * 1 + 2 * 1)) / (3 - 2 * 1) ^ 2) 1 at hh
    norm_num at hh
    exact hh.deriv
  exact DifferentialGeometry.Analysis.exists_diffeomorph_eq_endpoint_germs (a := 0) (b := 1)
    (by norm_num) isOpen_univ (mem_univ _) contDiffOn_id isOpen_Iio (by norm_num) hf
    rfl (by norm_num) (by rw [deriv_id]; norm_num) (by rw [hd]; norm_num)

private def boundedPlugRadialMap (D : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  if x = 0 then 0 else (D ‖x‖ / ‖x‖) • x

private theorem boundedPlugRadialMap_zero (D : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) :
    boundedPlugRadialMap D 0 = 0 := by simp [boundedPlugRadialMap]

private theorem boundedPlugRadialMap_norm (D : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ)
    (hm : StrictMono D) (h0 : D 0 = 0) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖boundedPlugRadialMap D x‖ = D ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, boundedPlugRadialMap, h0]
  · have hn := norm_pos_iff.mpr hx
    have hd : 0 < D ‖x‖ := by simpa only [h0] using hm hn
    rw [boundedPlugRadialMap, ite_eq_right hx, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hd hn), div_mul_cancel₀ _ hn.ne']

private theorem boundedPlugRadialMap_inv (D : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ)
    (hm : StrictMono D) (h0 : D 0 = 0) (x : EuclideanSpace ℝ (Fin 3)) :
    boundedPlugRadialMap D.symm (boundedPlugRadialMap D x) = x := by
  by_cases hx : x = 0
  · simp [hx, boundedPlugRadialMap]
  · have hn := norm_pos_iff.mpr hx
    have hd : 0 < D ‖x‖ := by simpa only [h0] using hm hn
    have hf : boundedPlugRadialMap D x ≠ 0 := by
      rw [← norm_ne_zero_iff, boundedPlugRadialMap_norm D hm h0]
      exact hd.ne'
    rw [boundedPlugRadialMap, ite_eq_right hf, boundedPlugRadialMap_norm D hm h0,
      D.symm_apply_apply, boundedPlugRadialMap, ite_eq_right hx, smul_smul]
    have he : ‖x‖ / D ‖x‖ * (D ‖x‖ / ‖x‖) = 1 := by field_simp
    rw [he, one_smul]

private theorem boundedPlugRadialMap_smooth (D : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ)
    (hg : (D : ℝ → ℝ) =ᶠ[𝓝 0] id) :
    ContDiff ℝ ∞ (boundedPlugRadialMap D) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hn : Tendsto (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖) (𝓝 0) (𝓝 0) := by
      simpa using continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin 3))
    have he : boundedPlugRadialMap D =ᶠ[𝓝 0] id := by
      filter_upwards [hg.comp_tendsto hn] with y hy
      change D ‖y‖ = ‖y‖ at hy
      by_cases hy0 : y = 0
      · simp [boundedPlugRadialMap, hy0]
      · rw [boundedPlugRadialMap, ite_eq_right hy0, hy, id_eq,
          div_self (norm_ne_zero_iff.mpr hy0), one_smul]
    exact contDiffAt_id.congr_of_eventuallyEq he
  · have hn : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖) x :=
      contDiffAt_norm ℝ hx
    have hd := (D.contMDiff.contDiff.contDiffAt.comp x hn).div hn
      (norm_ne_zero_iff.mpr hx)
    have hf := hd.smul contDiffAt_id
    apply hf.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact ite_eq_right hy

private theorem boundedPlugRadialMap_symm_germ (D : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ)
    (hg : (D : ℝ → ℝ) =ᶠ[𝓝 0] id) :
    (D.symm : ℝ → ℝ) =ᶠ[𝓝 0] id := by
  have h0 : D 0 = 0 := hg.self_of_nhds
  have hi0 : D.symm 0 = 0 := by
    apply D.injective
    change D (D.symm 0) = D 0
    rw [D.apply_symm_apply, h0]
  have ht : Tendsto D.symm (𝓝 0) (𝓝 0) := by
    simpa only [hi0] using D.symm.continuous.tendsto 0
  filter_upwards [hg.comp_tendsto ht] with y hy
  change D (D.symm y) = D.symm y at hy
  simpa only [D.apply_symm_apply, id_eq] using hy.symm

private def boundedPlugRadialDiffeomorph (D : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ)
    (hm : StrictMono D) (hg : (D : ℝ → ℝ) =ᶠ[𝓝 0] id) :
    EuclideanSpace ℝ (Fin 3) ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3) := by
  have h0 : D 0 = 0 := hg.self_of_nhds
  have hig := boundedPlugRadialMap_symm_germ D hg
  have him : StrictMono D.symm := by
    intro a b hab
    apply hm.lt_iff_lt.mp
    simpa only [D.apply_symm_apply] using hab
  exact
    { toFun := boundedPlugRadialMap D
      invFun := boundedPlugRadialMap D.symm
      left_inv := boundedPlugRadialMap_inv D hm h0
      right_inv := boundedPlugRadialMap_inv D.symm him hig.self_of_nhds
      contMDiff_toFun := (boundedPlugRadialMap_smooth D hg).contMDiff
      contMDiff_invFun := (boundedPlugRadialMap_smooth D.symm hig).contMDiff }

private theorem boundedPlugRadialDiffeomorph_image (D : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ)
    (hm : StrictMono D) (hg : (D : ℝ → ℝ) =ᶠ[𝓝 0] id) (h1 : D 1 = 1) :
    boundedPlugRadialDiffeomorph D hm hg ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  let R := boundedPlugRadialDiffeomorph D hm hg
  have hn (x : EuclideanSpace ℝ (Fin 3)) : ‖R x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
    rw [show ‖R x‖ = D ‖x‖ from boundedPlugRadialMap_norm D hm hg.self_of_nhds x]
    simpa only [h1] using (hm.le_iff_le (a := ‖x‖) (b := 1))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_closedBall_zero_iff.mpr ((hn x).mpr
      (mem_closedBall_zero_iff.mp hx))
  · intro hy
    refine ⟨R.symm y, ?_, R.apply_symm_apply y⟩
    apply mem_closedBall_zero_iff.mpr
    apply (hn _).mp
    rw [R.apply_symm_apply]
    exact mem_closedBall_zero_iff.mp hy

def boundedPlugCapRadiusDiffeomorph : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ :=
  exists_boundedPlugCapRadius.choose

theorem boundedPlugCapRadius_strictMono : StrictMono boundedPlugCapRadiusDiffeomorph :=
  exists_boundedPlugCapRadius.choose_spec.1

theorem boundedPlugCapRadius_center :
    (boundedPlugCapRadiusDiffeomorph : ℝ → ℝ) =ᶠ[𝓝 0] id :=
  exists_boundedPlugCapRadius.choose_spec.2.1

theorem boundedPlugCapRadius_boundary :
    (boundedPlugCapRadiusDiffeomorph : ℝ → ℝ) =ᶠ[𝓝 1]
      (fun r => (3 - 2 * r)⁻¹) :=
  exists_boundedPlugCapRadius.choose_spec.2.2.1

theorem boundedPlugCapRadius_zero : boundedPlugCapRadiusDiffeomorph 0 = 0 :=
  boundedPlugCapRadius_center.self_of_nhds

theorem boundedPlugCapRadius_one : boundedPlugCapRadiusDiffeomorph 1 = 1 := by
  have h := boundedPlugCapRadius_boundary.self_of_nhds
  norm_num at h
  exact h

def boundedPlugCapRadialDiffeomorph :
    EuclideanSpace ℝ (Fin 3) ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3) :=
  boundedPlugRadialDiffeomorph boundedPlugCapRadiusDiffeomorph
    boundedPlugCapRadius_strictMono boundedPlugCapRadius_center

theorem boundedPlugCapRadialDiffeomorph_norm (x : EuclideanSpace ℝ (Fin 3)) :
    ‖boundedPlugCapRadialDiffeomorph x‖ = boundedPlugCapRadiusDiffeomorph ‖x‖ :=
  boundedPlugRadialMap_norm _ boundedPlugCapRadius_strictMono boundedPlugCapRadius_zero x

theorem boundedPlugCapRadialDiffeomorph_ray
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {r : ℝ} (hr : 0 ≤ r) :
    boundedPlugCapRadialDiffeomorph (r • z.val) =
      boundedPlugCapRadiusDiffeomorph r • z.val := by
  by_cases hr0 : r = 0
  · subst r
    rw [zero_smul, boundedPlugCapRadius_zero, zero_smul]
    exact boundedPlugRadialMap_zero _
  · have hz : z.val ≠ 0 := ne_zero_of_mem_unit_sphere z
    have hx : r • z.val ≠ 0 := smul_ne_zero hr0 hz
    have hn : ‖r • z.val‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, norm_eq_of_mem_sphere, mul_one]
    change boundedPlugRadialMap _ (r • z.val) = _
    rw [boundedPlugRadialMap, ite_eq_right hx, hn, smul_smul, div_mul_cancel₀ _ hr0]

theorem boundedPlugCapRadialDiffeomorph_center :
    (boundedPlugCapRadialDiffeomorph : EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3)) =ᶠ[𝓝 0] id := by
  have hn : Tendsto (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖) (𝓝 0) (𝓝 0) := by
    simpa using continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin 3))
  filter_upwards [boundedPlugCapRadius_center.comp_tendsto hn] with y hy
  change boundedPlugCapRadiusDiffeomorph ‖y‖ = ‖y‖ at hy
  by_cases hy0 : y = 0
  · subst y
    change boundedPlugRadialMap _ 0 = 0
    exact boundedPlugRadialMap_zero _
  · change boundedPlugRadialMap _ y = y
    rw [boundedPlugRadialMap, ite_eq_right hy0, hy,
      div_self (norm_ne_zero_iff.mpr hy0), one_smul]

theorem boundedPlugCapRadialDiffeomorph_image :
    boundedPlugCapRadialDiffeomorph ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  boundedPlugRadialDiffeomorph_image _ boundedPlugCapRadius_strictMono
    boundedPlugCapRadius_center boundedPlugCapRadius_one

local instance boundedPlugRadialCapBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

local instance boundedPlugRadialCapBallSmooth :
    IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

def boundedPlugCapBallDiffeomorph : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
  closedCellDiffeomorph boundedPlugCapRadialDiffeomorph boundedPlugCapRadialDiffeomorph_image

theorem boundedPlugCapBallDiffeomorph_apply (x : ClosedCell 3) :
    (boundedPlugCapBallDiffeomorph x).val = boundedPlugCapRadialDiffeomorph x.val := rfl

theorem boundedPlugCapBallDiffeomorph_boundary
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    boundedPlugCapBallDiffeomorph ⟨z.val, (norm_eq_of_mem_sphere z).le⟩ =
      ⟨z.val, (norm_eq_of_mem_sphere z).le⟩ := by
  apply Subtype.ext
  rw [boundedPlugCapBallDiffeomorph_apply]
  simpa only [boundedPlugCapRadius_one, one_smul] using
    boundedPlugCapRadialDiffeomorph_ray z zero_le_one

def boundedPlugCapRadialPoint (z : ClosureSphere.{u}) (r : ℝ) (hr : 0 ≤ r)
    (hr1 : r ≤ 1) : ClosedCell 3 :=
  ⟨r • z.down.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, norm_eq_of_mem_sphere, mul_one]
    exact hr1⟩

theorem boundedPlugCapBallDiffeomorph_ray (z : ClosureSphere.{u})
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (boundedPlugCapBallDiffeomorph (boundedPlugCapRadialPoint z r hr hr1)).val =
      boundedPlugCapRadiusDiffeomorph r • z.down.val := by
  rw [boundedPlugCapBallDiffeomorph_apply]
  exact boundedPlugCapRadialDiffeomorph_ray z.down hr

theorem exists_boundedPlugCapBallCollar_germ :
    ∃ ε > (0 : ℝ), ε < 1 / 4 ∧
      ∀ (z : ClosureSphere.{u}) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1),
        |r - 1| < ε →
        boundedPlugCapBallDiffeomorph (boundedPlugCapRadialPoint z r hr hr1) =
          sphereCapBallCollar (z, GC.Endpoint.halfPoint (2 - 2 * r) (by linarith)) := by
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp boundedPlugCapRadius_boundary
  refine ⟨min ε (1 / 8), lt_min hε (by norm_num), ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · intro z r hr hr1 hsmall
    have hd : boundedPlugCapRadiusDiffeomorph r = (3 - 2 * r)⁻¹ :=
      he (by simpa only [Real.dist_eq] using hsmall.trans_le (min_le_left _ _))
    apply Subtype.ext
    rw [boundedPlugCapBallDiffeomorph_ray z r hr hr1, sphereCapBallCollar_apply, hd]
    congr 2
    change 3 - 2 * r = 1 + (2 - 2 * r)
    ring

namespace MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

def boundedPlugWholeCap (i : Fin B.sphereCount) (x : ClosedCell 3) :
    B.sphereCapCarrier.Carrier :=
  B.sphereCapRelativeCapping.cap i
    ((B.sphereCapOrientationData.reparameterization i).symm (boundedPlugCapBallDiffeomorph x))

theorem boundedPlugWholeCap_eq (i : Fin B.sphereCount) (x : ClosedCell 3) :
    B.boundedPlugWholeCap i x = B.sphereCapBall i (boundedPlugCapBallDiffeomorph x) := by
  change B.sphereCapBall i
    (B.sphereCapOrientationData.reparameterization i
      ((B.sphereCapOrientationData.reparameterization i).symm _)) = _
  rw [Diffeomorph.apply_symm_apply]

theorem boundedPlugWholeCap_range (i : Fin B.sphereCount) :
    range (B.boundedPlugWholeCap i) = range (B.sphereCapBall i) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨boundedPlugCapBallDiffeomorph x, (B.boundedPlugWholeCap_eq i x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨boundedPlugCapBallDiffeomorph.symm x, ?_⟩
    rw [B.boundedPlugWholeCap_eq, Diffeomorph.apply_symm_apply]

theorem boundedPlugWholeCap_boundary (i : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.boundedPlugWholeCap i (closureSphereToBall z) =
      B.sphereCapCore (B.sphere i (z, GC.Endpoint.halfZero)) := by
  rw [B.boundedPlugWholeCap_eq]
  have hfix : boundedPlugCapBallDiffeomorph (closureSphereToBall z) = closureSphereToBall z :=
    boundedPlugCapBallDiffeomorph_boundary z.down
  rw [hfix]
  exact (B.sphereCap_attachment i z).symm

theorem exists_boundedPlugWholeCap_normal_germ :
    ∃ ε > (0 : ℝ), ε < 1 / 4 ∧
      ∀ (i : Fin B.sphereCount) (z : ClosureSphere.{u}) (r : ℝ)
        (hr : 0 ≤ r) (hr1 : r ≤ 1), |r - 1| < ε →
        B.boundedPlugWholeCap i (boundedPlugCapRadialPoint z r hr hr1) =
          B.boundedPlugCapNormal i (z, r) := by
  obtain ⟨ε, hε, hε1, hcollar⟩ := exists_boundedPlugCapBallCollar_germ.{u}
  refine ⟨ε, hε, hε1, ?_⟩
  intro i z r hr hr1 hsmall
  rw [B.boundedPlugWholeCap_eq, hcollar z r hr hr1 hsmall]
  exact (B.boundedPlugCapNormal_negative i z (by
    have hh := (abs_lt.mp hsmall).1
    linarith) hr1).symm

end MixedBoundaryCertificate

end GC.GraphManifold
