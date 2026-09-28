/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homeomorph.PlanarSphereExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderSideExtension
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Set Metric Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def planarCircleParam : loopCircle ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans
    (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
      change z ∈ sphere (0 : ℂ) 1 ↔ Complex.orthonormalBasisOneI.repr z ∈ sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
        Complex.orthonormalBasisOneI.repr.norm_map])

theorem planarCircleParam_apply (θ : loopCircle) :
    (planarCircleParam θ : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (AddCircle.toCircle θ : ℂ) := by
  change Complex.orthonormalBasisOneI.repr
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) θ : ℂ) = _
  rw [AddCircle.homeomorphCircle_apply]

theorem planarCircleParam_neg (θ : loopCircle) :
    (planarCircleParam (-θ) : EuclideanSpace ℝ (Fin 2)) =
      planarReflection (planarCircleParam θ) := by
  rw [planarCircleParam_apply, planarCircleParam_apply, planarReflection_apply_repr,
    AddCircle.toCircle_neg, Circle.coe_inv]
  congr 1
  exact Complex.inv_eq_conj (Circle.norm_coe (AddCircle.toCircle θ))

theorem planarReflection_planarReflection (x : EuclideanSpace ℝ (Fin 2)) :
    planarReflection (planarReflection x) = x := by
  obtain ⟨z, rfl⟩ := Complex.orthonormalBasisOneI.repr.surjective x
  rw [planarReflection_apply_repr, planarReflection_apply_repr, star_star]

noncomputable def sphereReflection :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  planarReflection.toHomeomorph.subtype fun x => by
    change x ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔ planarReflection x ∈ sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, planarReflection.norm_map]

theorem sphereReflection_apply (u : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (sphereReflection u : EuclideanSpace ℝ (Fin 2)) = planarReflection u := rfl

theorem hasIncreasingCircleLift_reflect_iff
    (τ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    HasIncreasingCircleLift
        (fun θ => planarCircleParam.symm (sphereReflection (τ (planarCircleParam θ)))) ↔
      ¬ HasIncreasingCircleLift (fun θ => planarCircleParam.symm (τ (planarCircleParam θ))) := by
  let P := planarCircleParam
  let φ : loopCircle ≃ₜ loopCircle := (P.trans τ).trans P.symm
  have hneg : ∀ v : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      P.symm (sphereReflection v) = -(P.symm v) := by
    intro v
    obtain ⟨x, rfl⟩ := P.surjective v
    rw [P.symm_apply_apply]
    apply P.injective
    rw [P.apply_symm_apply]
    apply Subtype.ext
    rw [sphereReflection_apply, planarCircleParam_neg]
  have hφ' : ∀ θ, P.symm (sphereReflection (τ (P θ))) = -(φ θ) := fun θ => hneg _
  constructor
  · intro h hφ
    have hs : HasIncreasingCircleLift φ.symm := hφ.inv φ.surjective φ.symm_apply_apply
    have hc : HasIncreasingCircleLift (fun θ : loopCircle => -θ) := by
      refine (h.comp hs).congr fun θ => ?_
      change -θ = P.symm (sphereReflection (τ (P (φ.symm θ))))
      rw [hφ', φ.apply_symm_apply]
    exact not_hasIncreasingCircleLift_neg hc
  · intro hφ
    exact (hasIncreasingCircleLift_neg_of_not_hasIncreasingCircleLift φ hφ).congr hφ'

theorem norm_lt_one_of_isOpen_subset_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {O : Set E} (hO : IsOpen O) (hsub : O ⊆ closedBall 0 1) {y : E}
    (hy : y ∈ O) : ‖y‖ < 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO y hy
  by_contra hn
  have hy1 : ‖y‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp (hsub hy)) (not_lt.mp hn)
  have hδ : 0 < ε / 2 := by positivity
  have hz : (1 + ε / 2) • y ∈ O := by
    apply hball
    rw [mem_ball, dist_eq_norm, show (1 + ε / 2) • y - y = (ε / 2) • y by
      rw [add_smul, one_smul]; abel, norm_smul, Real.norm_of_nonneg hδ.le, hy1]
    linarith
  have h1 := mem_closedBall_zero_iff.mp (hsub hz)
  rw [norm_smul, Real.norm_of_nonneg (by linarith), hy1] at h1
  linarith

theorem norm_lt_one_of_closedBall_homeomorph
    (γ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (x : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (hx : ‖x.val‖ < 1) : ‖(γ x).val‖ < 1 := by
  classical
  let G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun y =>
    if h : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 then (γ ⟨y, h⟩).val else y
  let U := ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hmem : ∀ y ∈ U, y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun y hy => ball_subset_closedBall hy
  have hGU : ∀ y (hy : y ∈ U), G y = (γ ⟨y, hmem y hy⟩).val := fun y hy => dite_eq_left _
  have hcont : ContinuousOn G U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun y : U => (γ ⟨y.val, hmem y.val y.2⟩).val) :=
      continuous_subtype_val.comp (γ.continuous.comp (continuous_subtype_val.subtype_mk _))
    exact hc.congr fun y => (hGU y.val y.2).symm
  have hinj : InjOn G U := by
    intro y hy y' hy' h
    rw [hGU y hy, hGU y' hy'] at h
    exact congrArg Subtype.val (γ.injective (Subtype.ext h))
  have hopen := isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 2))
    isOpen_ball hcont hinj
  have hsub : G '' U ⊆ closedBall 0 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hGU y hy]
    exact (γ _).2
  have hxU : x.val ∈ U := mem_ball_zero_iff.mpr hx
  have h := norm_lt_one_of_isOpen_subset_closedBall hopen hsub ⟨x.val, hxU, rfl⟩
  rw [hGU _ hxU] at h
  exact h

theorem norm_eq_one_iff_of_closedBall_homeomorph
    (γ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (x : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) : ‖(γ x).val‖ = 1 ↔ ‖x.val‖ = 1 := by
  have hle : ∀ y : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ‖y.val‖ ≤ 1 :=
    fun y => mem_closedBall_zero_iff.mp y.2
  constructor
  · intro h
    by_contra hne
    have h1 := norm_lt_one_of_closedBall_homeomorph γ x (lt_of_le_of_ne (hle x) hne)
    rw [h] at h1
    exact lt_irrefl _ h1
  · intro h
    by_contra hne
    have h1 := norm_lt_one_of_closedBall_homeomorph γ.symm (γ x) (lt_of_le_of_ne (hle _) hne)
    rw [γ.symm_apply_apply, h] at h1
    exact lt_irrefl _ h1

noncomputable def rimHomeomorph
    (γ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 where
  toFun u := ⟨(γ ⟨u.val, sphere_subset_closedBall u.2⟩).val, mem_sphere_zero_iff_norm.mpr
    ((norm_eq_one_iff_of_closedBall_homeomorph γ _).mpr (mem_sphere_zero_iff_norm.mp u.2))⟩
  invFun v := ⟨(γ.symm ⟨v.val, sphere_subset_closedBall v.2⟩).val, mem_sphere_zero_iff_norm.mpr
    ((norm_eq_one_iff_of_closedBall_homeomorph γ.symm _).mpr (mem_sphere_zero_iff_norm.mp v.2))⟩
  left_inv u := by
    apply Subtype.ext
    exact congrArg (fun w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 => w.val)
      (γ.symm_apply_apply ⟨u.val, sphere_subset_closedBall u.2⟩)
  right_inv v := by
    apply Subtype.ext
    exact congrArg (fun w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 => w.val)
      (γ.apply_symm_apply ⟨v.val, sphere_subset_closedBall v.2⟩)
  continuous_toFun := (continuous_subtype_val.comp
    (γ.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp
    (γ.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _

theorem rimHomeomorph_apply
    (γ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (u : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (rimHomeomorph γ u : EuclideanSpace ℝ (Fin 2)) =
      (γ ⟨u.val, sphere_subset_closedBall u.2⟩).val := rfl

theorem exists_cylinderSide_homeomorph_of_rims
    (τa τb : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hor : HasIncreasingCircleLift (fun θ => planarCircleParam.symm (τa (planarCircleParam θ))) ↔
      HasIncreasingCircleLift (fun θ => planarCircleParam.symm (τb (planarCircleParam θ)))) :
    ∃ S : cylinderSide ≃ₜ cylinderSide, (∀ q, (S q).val.2 = q.val.2) ∧
      (∀ (u : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (hq : ((u : EuclideanSpace ℝ (Fin 2)), (-1 : ℝ)) ∈ cylinderSide),
        (S ⟨_, hq⟩).val = (((τa u) : EuclideanSpace ℝ (Fin 2)), -1)) ∧
      ∀ (u : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (hq : ((u : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) ∈ cylinderSide),
        (S ⟨_, hq⟩).val = (((τb u) : EuclideanSpace ℝ (Fin 2)), 1) := by
  let P := planarCircleParam
  let φa : loopCircle ≃ₜ loopCircle := (P.trans τa).trans P.symm
  let φb : loopCircle ≃ₜ loopCircle := (P.trans τb).trans P.symm
  obtain ⟨E, hE1, hE0, hEl⟩ := exists_homeomorph_cylinder_of_same_orientation φa φb hor
  have hKmem : ∀ q : cylinderSide, (q.val.2 + 1) / 2 ∈ unitInterval := by
    intro q
    obtain ⟨h1, h2⟩ := abs_le.mp q.2.2
    exact ⟨by linarith, by linarith⟩
  have hKinv : ∀ p : unitInterval × loopCircle,
      (((P p.2 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)),
        2 * (p.1 : ℝ) - 1) ∈ cylinderSide := by
    intro p
    obtain ⟨h1, h2⟩ := p.1.2
    exact ⟨norm_eq_of_mem_sphere _, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  let K : cylinderSide ≃ₜ unitInterval × loopCircle :=
    { toFun := fun q => (⟨_, hKmem q⟩, P.symm ⟨q.val.1, mem_sphere_zero_iff_norm.mpr q.2.1⟩)
      invFun := fun p => ⟨_, hKinv p⟩
      left_inv := fun q => by
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · change ((P (P.symm ⟨q.val.1, _⟩) : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
            EuclideanSpace ℝ (Fin 2)) = q.val.1
          rw [P.apply_symm_apply]
        · change 2 * ((q.val.2 + 1) / 2) - 1 = q.val.2
          ring
      right_inv := fun p => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · change (2 * (p.1 : ℝ) - 1 + 1) / 2 = p.1
          ring
        · change P.symm ⟨_, _⟩ = p.2
          rw [Subtype.coe_eta, P.symm_apply_apply]
      continuous_toFun :=
        ((((continuous_snd.comp continuous_subtype_val).add continuous_const).div_const
          2).subtype_mk _).prodMk (P.symm.continuous.comp
            ((continuous_fst.comp continuous_subtype_val).subtype_mk _))
      continuous_invFun :=
        ((continuous_subtype_val.comp (P.continuous.comp continuous_snd)).prodMk
          ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
            continuous_const)).subtype_mk _ }
  let S : cylinderSide ≃ₜ cylinderSide := K.trans (E.trans K.symm)
  refine ⟨S, fun q => ?_, fun u hq => ?_, fun u hq => ?_⟩
  · change 2 * ((E (K q)).1 : ℝ) - 1 = q.val.2
    rw [hE1]
    change 2 * ((q.val.2 + 1) / 2) - 1 = q.val.2
    ring
  · have hK : K ⟨_, hq⟩ = (0, P.symm u) := by
      refine Prod.ext (Subtype.ext ?_) rfl
      change ((-1 : ℝ) + 1) / 2 = 0
      norm_num
    change (K.symm (E (K ⟨_, hq⟩))).val = _
    rw [hK, hE0]
    refine Prod.ext ?_ ?_
    · change ((P (φa (P.symm u)) : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
        EuclideanSpace ℝ (Fin 2)) = τa u
      change ((P (P.symm (τa (P (P.symm u)))) : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
        EuclideanSpace ℝ (Fin 2)) = τa u
      rw [P.apply_symm_apply, P.apply_symm_apply]
    · change 2 * ((0 : unitInterval) : ℝ) - 1 = -1
      norm_num
  · have hK : K ⟨_, hq⟩ = (1, P.symm u) := by
      refine Prod.ext (Subtype.ext ?_) rfl
      change ((1 : ℝ) + 1) / 2 = 1
      norm_num
    change (K.symm (E (K ⟨_, hq⟩))).val = _
    rw [hK, hEl]
    refine Prod.ext ?_ ?_
    · change ((P (P.symm (τb (P (P.symm u)))) : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
        EuclideanSpace ℝ (Fin 2)) = τb u
      rw [P.apply_symm_apply, P.apply_symm_apply]
    · change 2 * ((1 : unitInterval) : ℝ) - 1 = 1
      norm_num

theorem exists_homeomorph_extension_of_ends
    (γa γb : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hor : HasIncreasingCircleLift
        (fun θ => planarCircleParam.symm (rimHomeomorph γa (planarCircleParam θ))) ↔
      HasIncreasingCircleLift
        (fun θ => planarCircleParam.symm (rimHomeomorph γb (planarCircleParam θ)))) :
    ∃ Φ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₜ (EuclideanSpace ℝ (Fin 2) × ℝ),
      (∀ q, ‖Φ q‖ = ‖q‖) ∧
      (∀ w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, Φ (w.val, -1) = ((γa w).val, -1)) ∧
      (∀ w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, Φ (w.val, 1) = ((γb w).val, 1)) ∧
      ∀ q ∈ cylinderSide, Φ q ∈ cylinderSide ∧ (Φ q).2 = q.2 := by
  classical
  obtain ⟨S, hS2, hSa, hSb⟩ :=
    exists_cylinderSide_homeomorph_of_rims (rimHomeomorph γa) (rimHomeomorph γb) hor
  let ga : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun w =>
    if h : w ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 then (γa ⟨w, h⟩).val else w
  let gb : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun w =>
    if h : w ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 then (γb ⟨w, h⟩).val else w
  have hga : ∀ w (h : w ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1),
      ga w = (γa ⟨w, h⟩).val := fun w h => dite_eq_left h
  have hgb : ∀ w (h : w ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1),
      gb w = (γb ⟨w, h⟩).val := fun w h => dite_eq_left h
  let B0 : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ := fun q =>
    if h : q ∈ cylinderSide then (S ⟨q, h⟩).val
    else if 0 < q.2 then (gb q.1, 1) else (ga q.1, -1)
  let Sph := sphere (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1
  have hside : ∀ q (h : q ∈ cylinderSide), B0 q = (S ⟨q, h⟩).val := fun q h => dite_eq_left h
  have hcapP : ∀ q, q ∉ cylinderSide → 0 < q.2 → B0 q = (gb q.1, 1) := by
    intro q h hp
    simp only [B0, dite_eq_right h, ite_eq_left hp]
  have hcapN : ∀ q, q ∉ cylinderSide → ¬ 0 < q.2 → B0 q = (ga q.1, -1) := by
    intro q h hp
    simp only [B0, dite_eq_right h, ite_eq_right hp]
  have hrimb : ∀ q (h : q ∈ cylinderSide), q.2 = 1 → (S ⟨q, h⟩).val = (gb q.1, 1) := by
    intro q h h2
    have hu : q.1 ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := mem_sphere_zero_iff_norm.mpr h.1
    have hq : (((⟨q.1, hu⟩ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
        EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) ∈ cylinderSide := ⟨h.1, by norm_num⟩
    have he : (⟨q, h⟩ : cylinderSide) = ⟨_, hq⟩ := Subtype.ext (Prod.ext rfl h2)
    rw [he, hSb ⟨q.1, hu⟩ hq, rimHomeomorph_apply, hgb _ (sphere_subset_closedBall hu)]
  have hrima : ∀ q (h : q ∈ cylinderSide), q.2 = -1 → (S ⟨q, h⟩).val = (ga q.1, -1) := by
    intro q h h2
    have hu : q.1 ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := mem_sphere_zero_iff_norm.mpr h.1
    have hq : (((⟨q.1, hu⟩ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
        EuclideanSpace ℝ (Fin 2)), (-1 : ℝ)) ∈ cylinderSide := ⟨h.1, by norm_num⟩
    have he : (⟨q, h⟩ : cylinderSide) = ⟨_, hq⟩ := Subtype.ext (Prod.ext rfl h2)
    rw [he, hSa ⟨q.1, hu⟩ hq, rimHomeomorph_apply, hga _ (sphere_subset_closedBall hu)]
  have hcapnorm : ∀ q, q ∈ Sph → q ∉ cylinderSide → ‖(B0 q).1‖ < 1 ∧ |(B0 q).2| = 1 := by
    intro q hq hs
    obtain ⟨hq1, -⟩ := norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp hq) hs
    have hball : q.1 ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
      mem_closedBall_zero_iff.mpr hq1.le
    by_cases hp : 0 < q.2
    · rw [hcapP q hs hp, hgb _ hball]
      exact ⟨norm_lt_one_of_closedBall_homeomorph γb ⟨q.1, hball⟩ hq1, by norm_num⟩
    · rw [hcapN q hs hp, hga _ hball]
      exact ⟨norm_lt_one_of_closedBall_homeomorph γa ⟨q.1, hball⟩ hq1, by norm_num⟩
  have hB0n : ∀ q ∈ Sph, B0 q ∈ Sph := by
    intro q hq
    rw [mem_sphere_zero_iff_norm]
    by_cases hs : q ∈ cylinderSide
    · rw [hside q hs]
      exact norm_eq_one_of_mem_cylinderSide (S _).2
    · obtain ⟨h1, h2⟩ := hcapnorm q hq hs
      rw [Prod.norm_def, Real.norm_eq_abs, h2]
      exact max_eq_right h1.le
  have hsideC : IsClosed cylinderSide :=
    (isClosed_eq (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)
  let CP : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | ‖q.1‖ ≤ 1 ∧ q.2 = 1}
  let CN : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | ‖q.1‖ ≤ 1 ∧ q.2 = -1}
  have hCPC : IsClosed CP :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_eq continuous_snd continuous_const)
  have hCNC : IsClosed CN :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_eq continuous_snd continuous_const)
  have hgac : ContinuousOn ga (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_subtype_val.comp γa.continuous).congr fun w => ?_
    exact (hga w.val w.2).symm
  have hgbc : ContinuousOn gb (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_subtype_val.comp γb.continuous).congr fun w => ?_
    exact (hgb w.val w.2).symm
  have h1c : ContinuousOn B0 cylinderSide := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_subtype_val.comp S.continuous).congr fun q => ?_
    exact (hside q.val q.2).symm
  have h2c : ContinuousOn B0 CP := by
    have hc : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => (gb q.1, (1 : ℝ))) CP :=
      (hgbc.comp continuous_fst.continuousOn fun q hq =>
        mem_closedBall_zero_iff.mpr hq.1).prodMk continuousOn_const
    refine hc.congr fun q hq => ?_
    by_cases hs : q ∈ cylinderSide
    · rw [hside q hs]
      exact hrimb q hs hq.2
    · exact hcapP q hs (by rw [hq.2]; norm_num)
  have h3c : ContinuousOn B0 CN := by
    have hc : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => (ga q.1, (-1 : ℝ))) CN :=
      (hgac.comp continuous_fst.continuousOn fun q hq =>
        mem_closedBall_zero_iff.mpr hq.1).prodMk continuousOn_const
    refine hc.congr fun q hq => ?_
    by_cases hs : q ∈ cylinderSide
    · rw [hside q hs]
      exact hrima q hs hq.2
    · exact hcapN q hs (by rw [hq.2]; norm_num)
  have hcov : Sph ⊆ cylinderSide ∪ CP ∪ CN := by
    intro q hq
    by_cases hs : q ∈ cylinderSide
    · exact Or.inl (Or.inl hs)
    · obtain ⟨hq1, hq2⟩ :=
        norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp hq) hs
      rcases (abs_eq zero_le_one).mp hq2 with h | h
      · exact Or.inl (Or.inr ⟨hq1.le, h⟩)
      · exact Or.inr ⟨hq1.le, h⟩
  have hcont : ContinuousOn B0 Sph :=
    ((h1c.union_of_isClosed h2c hsideC hCPC).union_of_isClosed h3c (hsideC.union hCPC)
      hCNC).mono hcov
  let βf : Sph → Sph := fun q => ⟨B0 q.val, hB0n q.val q.2⟩
  have hβc : Continuous βf :=
    (hcont.comp_continuous continuous_subtype_val fun q => q.2).subtype_mk _
  have hsnd : ∀ q, q ∈ Sph → q ∉ cylinderSide →
      (0 < q.2 → q.2 = 1) ∧ (¬ 0 < q.2 → q.2 = -1) := by
    intro q hq hs
    obtain ⟨-, hq2⟩ := norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp hq) hs
    constructor
    · intro hp
      rcases (abs_eq zero_le_one).mp hq2 with h | h
      · exact h
      · linarith
    · intro hp
      rcases (abs_eq zero_le_one).mp hq2 with h | h
      · rw [h] at hp
        norm_num at hp
      · exact h
  have hβinj : Function.Injective βf := by
    intro q1 q2 h
    have h' : B0 q1.val = B0 q2.val := congrArg Subtype.val h
    apply Subtype.ext
    by_cases hs1 : q1.val ∈ cylinderSide <;> by_cases hs2 : q2.val ∈ cylinderSide
    · rw [hside _ hs1, hside _ hs2] at h'
      exact congrArg (fun p : cylinderSide => p.val) (S.injective (Subtype.ext h'))
    · exfalso
      have ha : ‖(B0 q1.val).1‖ = 1 := by
        rw [hside _ hs1]
        exact (S _).2.1
      rw [h'] at ha
      linarith [(hcapnorm _ q2.2 hs2).1]
    · exfalso
      have ha : ‖(B0 q2.val).1‖ = 1 := by
        rw [hside _ hs2]
        exact (S _).2.1
      rw [← h'] at ha
      linarith [(hcapnorm _ q1.2 hs1).1]
    · obtain ⟨hq1, -⟩ :=
        norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp q1.2) hs1
      obtain ⟨hq2, -⟩ :=
        norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp q2.2) hs2
      have hb1 : q1.val.1 ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        mem_closedBall_zero_iff.mpr hq1.le
      have hb2 : q2.val.1 ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        mem_closedBall_zero_iff.mpr hq2.le
      obtain ⟨hP1, hN1⟩ := hsnd _ q1.2 hs1
      obtain ⟨hP2, hN2⟩ := hsnd _ q2.2 hs2
      by_cases hp1 : 0 < q1.val.2 <;> by_cases hp2 : 0 < q2.val.2
      · rw [hcapP _ hs1 hp1, hcapP _ hs2 hp2, hgb _ hb1, hgb _ hb2] at h'
        have hw := congrArg (fun w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 => w.val)
          (γb.injective (Subtype.ext (congrArg Prod.fst h')))
        exact Prod.ext hw ((hP1 hp1).trans (hP2 hp2).symm)
      · rw [hcapP _ hs1 hp1, hcapN _ hs2 hp2] at h'
        have h2 := congrArg Prod.snd h'
        norm_num at h2
      · rw [hcapN _ hs1 hp1, hcapP _ hs2 hp2] at h'
        have h2 := congrArg Prod.snd h'
        norm_num at h2
      · rw [hcapN _ hs1 hp1, hcapN _ hs2 hp2, hga _ hb1, hga _ hb2] at h'
        have hw := congrArg (fun w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 => w.val)
          (γa.injective (Subtype.ext (congrArg Prod.fst h')))
        exact Prod.ext hw ((hN1 hp1).trans (hN2 hp2).symm)
  have hβsurj : Function.Surjective βf := by
    intro y
    by_cases hs : y.val ∈ cylinderSide
    · obtain ⟨q, hq⟩ := S.surjective ⟨y.val, hs⟩
      refine ⟨⟨q.val, mem_sphere_zero_iff_norm.mpr (norm_eq_one_of_mem_cylinderSide q.2)⟩,
        Subtype.ext ?_⟩
      change B0 q.val = y.val
      rw [hside _ q.2, hq]
    · obtain ⟨hy1, hy2⟩ :=
        norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp y.2) hs
      have hyb : y.val.1 ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        mem_closedBall_zero_iff.mpr hy1.le
      rcases (abs_eq zero_le_one).mp hy2 with ht | ht
      · let x := γb.symm ⟨y.val.1, hyb⟩
        have hx : ‖x.val‖ < 1 := norm_lt_one_of_closedBall_homeomorph γb.symm _ hy1
        let q : EuclideanSpace ℝ (Fin 2) × ℝ := (x.val, 1)
        have hqs : q ∉ cylinderSide := fun h => by
          have := h.1
          change ‖x.val‖ = 1 at this
          linarith
        have hqS : q ∈ Sph := by
          rw [mem_sphere_zero_iff_norm, Prod.norm_def, Real.norm_eq_abs, abs_one]
          exact max_eq_right hx.le
        refine ⟨⟨q, hqS⟩, Subtype.ext ?_⟩
        change B0 q = y.val
        rw [hcapP q hqs (by norm_num), hgb _ x.2]
        refine Prod.ext ?_ ht.symm
        change (γb (γb.symm ⟨y.val.1, hyb⟩)).val = y.val.1
        rw [γb.apply_symm_apply]
      · let x := γa.symm ⟨y.val.1, hyb⟩
        have hx : ‖x.val‖ < 1 := norm_lt_one_of_closedBall_homeomorph γa.symm _ hy1
        let q : EuclideanSpace ℝ (Fin 2) × ℝ := (x.val, -1)
        have hqs : q ∉ cylinderSide := fun h => by
          have := h.1
          change ‖x.val‖ = 1 at this
          linarith
        have hqS : q ∈ Sph := by
          rw [mem_sphere_zero_iff_norm, Prod.norm_def, Real.norm_eq_abs, abs_neg, abs_one]
          exact max_eq_right hx.le
        refine ⟨⟨q, hqS⟩, Subtype.ext ?_⟩
        change B0 q = y.val
        rw [hcapN q hqs (by norm_num), hga _ x.2]
        refine Prod.ext ?_ ht.symm
        change (γa (γa.symm ⟨y.val.1, hyb⟩)).val = y.val.1
        rw [γa.apply_symm_apply]
  have hSc : CompactSpace Sph := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let β : Sph ≃ₜ Sph := hβc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective βf ⟨hβinj, hβsurj⟩)
  have hΦS : ∀ q (hq : q ∈ Sph), sphereRadialHomeomorph β q = B0 q := by
    intro q hq
    have h := sphereRadialHomeomorph_apply_sphere β ⟨q, hq⟩
    exact h
  have hendS : ∀ (w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (e : ℝ), |e| = 1 →
      ((w.val, e) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ Sph := by
    intro w e he
    rw [mem_sphere_zero_iff_norm, Prod.norm_def, Real.norm_eq_abs, he]
    exact max_eq_right (mem_closedBall_zero_iff.mp w.2)
  refine ⟨sphereRadialHomeomorph β, fun q => norm_sphereRadialHomeomorph β q, fun w => ?_,
    fun w => ?_, fun q hq => ?_⟩
  · rw [hΦS _ (hendS w (-1) (by norm_num))]
    by_cases hs : ((w.val, -1) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ cylinderSide
    · rw [hside _ hs, hrima _ hs rfl, hga _ w.2]
    · rw [hcapN _ hs (by norm_num), hga _ w.2]
  · rw [hΦS _ (hendS w 1 (by norm_num))]
    by_cases hs : ((w.val, 1) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ cylinderSide
    · rw [hside _ hs, hrimb _ hs rfl, hgb _ w.2]
    · rw [hcapP _ hs (by norm_num), hgb _ w.2]
  · have hqS : q ∈ Sph := mem_sphere_zero_iff_norm.mpr (norm_eq_one_of_mem_cylinderSide hq)
    rw [hΦS _ hqS, hside _ hq]
    exact ⟨(S _).2, hS2 _⟩

end DifferentialGeometry.Topology.PiecewiseLinear
