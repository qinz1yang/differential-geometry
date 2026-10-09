/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Ext
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

open Set
open scoped Topology commutatorElement

namespace DifferentialGeometry.CrystallographicActions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {G : Type*} [Group G]

def CoboundedOrbit (ρ : G →* (E ≃ᵃⁱ[ℝ] E)) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ ∀ x : E, ∃ g : G, dist x (ρ g 0) ≤ R

def linearPart : (E ≃ᵃⁱ[ℝ] E) →* (E ≃ₗᵢ[ℝ] E) where
  toFun u := u.linearIsometryEquiv
  map_one' := by ext x; rfl
  map_mul' u v := by ext x; rfl

theorem affine_eq_linear_add (u : E ≃ᵃⁱ[ℝ] E) (x : E) :
    u x = u.linearIsometryEquiv x + u 0 := by
  simpa only [vadd_eq_add, add_zero] using u.map_vadd (0 : E) x

theorem linear_eq_zero_of_uniform_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) (B : ℝ) (hB : ∀ x : E, ‖L x‖ ≤ B) : L = 0 := by
  ext x
  by_contra hx
  have hp : 0 < ‖L x‖ := norm_pos_iff.mpr hx
  obtain ⟨k, hk⟩ := exists_nat_gt (B / ‖L x‖)
  have h := hB ((k : ℝ) • x)
  rw [map_smul, norm_smul, Real.norm_natCast] at h
  exact (not_lt_of_ge h) ((div_lt_iff₀ hp).mp hk)

theorem translation_of_bounded_displacement (u : E ≃ᵃⁱ[ℝ] E)
    (B : ℝ) (hB : ∀ x : E, dist (u x) x ≤ B) :
    ∀ x : E, u x = x + u 0 := by
  let L : E →ₗ[ℝ] E := u.linearIsometryEquiv.toLinearEquiv.toLinearMap - LinearMap.id
  have hL : L = 0 := linear_eq_zero_of_uniform_bound L (B + ‖u 0‖) (fun x => by
    have he : L x = (u x - x) - u 0 := by
      change u.linearIsometryEquiv x - x = _
      rw [affine_eq_linear_add]
      abel
    rw [he]
    exact (norm_sub_le _ _).trans
      (add_le_add (by simpa only [dist_eq_norm] using hB x) le_rfl))
  intro x
  have he : u.linearIsometryEquiv x = x := sub_eq_zero.mp (LinearMap.congr_fun hL x)
  rw [affine_eq_linear_add, he]

theorem centralizer_displacement_bound (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    {R : ℝ} (hR : ∀ x : E, ∃ g : G, dist x (ρ g 0) ≤ R)
    (u : E ≃ᵃⁱ[ℝ] E) (hu : ∀ g : G, u * ρ g = ρ g * u) (x : E) :
    dist (u x) x ≤ 2 * R + dist (u 0) 0 := by
  obtain ⟨g, hg⟩ := hR x
  have he : u (ρ g 0) = ρ g (u 0) :=
    congrArg (fun v : E ≃ᵃⁱ[ℝ] E => v 0) (hu g)
  have hm : dist (u (ρ g 0)) (ρ g 0) = dist (u 0) 0 := by
    rw [he, (ρ g).dist_map]
  have h1 := dist_triangle (u x) (u (ρ g 0)) x
  have h2 := dist_triangle (u (ρ g 0)) (ρ g 0) x
  rw [u.dist_map] at h1
  rw [hm, dist_comm (ρ g 0) x] at h2
  linarith

theorem centralizer_is_translation (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hρ : CoboundedOrbit ρ) (u : E ≃ᵃⁱ[ℝ] E)
    (hu : ∀ g : G, u * ρ g = ρ g * u) :
    ∀ x : E, u x = x + u 0 := by
  obtain ⟨R, _, hR⟩ := hρ
  exact translation_of_bounded_displacement u (2 * R + dist (u 0) 0)
    (centralizer_displacement_bound ρ hR u hu)

theorem central_is_translation (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hρ : CoboundedOrbit ρ) {g : G} (hg : g ∈ Subgroup.center G) :
    ∀ x : E, ρ g x = x + ρ g 0 := by
  apply centralizer_is_translation ρ hρ (ρ g)
  intro h
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hg h).symm]

theorem linear_fix_of_central_translation (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    {k : G} (hk : k ∈ Subgroup.center G)
    (ht : ∀ x : E, ρ k x = x + ρ k 0) (g : G) :
    (ρ g).linearIsometryEquiv (ρ k 0) = ρ k 0 := by
  have he : ρ g (ρ k 0) = ρ k (ρ g 0) := by
    have h := congrArg (fun a : G => ρ a 0) (Subgroup.mem_center_iff.mp hk g)
    simpa only [map_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply] using h
  rw [affine_eq_linear_add (ρ g) (ρ k 0), ht (ρ g 0)] at he
  exact add_right_cancel (he.trans (add_comm _ _))

theorem commutator_eq_one_of_central (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hinj : Function.Injective ρ) (hρ : CoboundedOrbit ρ) (g h : G)
    (hc : ⁅g, h⁆ ∈ Subgroup.center G) : ⁅g, h⁆ = 1 := by
  let k := ⁅g, h⁆
  let v := ρ k 0
  have ht : ∀ x : E, ρ k x = x + v := central_is_translation ρ hρ hc
  have hfix (a : G) : (ρ a).linearIsometryEquiv v = v :=
    linear_fix_of_central_translation ρ hc ht a
  have hinner (a : G) (x : E) :
      inner ℝ ((ρ a).linearIsometryEquiv x) v = inner ℝ x v := by
    calc
      _ = inner ℝ ((ρ a).linearIsometryEquiv x) ((ρ a).linearIsometryEquiv v) := by
        rw [hfix]
      _ = _ := (ρ a).linearIsometryEquiv.inner_map_map x v
  have hgh : g * h = k * (h * g) := by
    dsimp [k]
    simp only [commutatorElement_def]
    group
  have he : ρ g (ρ h 0) = ρ k (ρ h (ρ g 0)) := by
    have he' := congrArg (fun a : G => ρ a 0) hgh
    simpa only [map_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply] using he'
  rw [ht, affine_eq_linear_add (ρ g) (ρ h 0),
    affine_eq_linear_add (ρ h) (ρ g 0)] at he
  have hi := congrArg (fun x : E => inner ℝ x v) he
  simp only [inner_add_left, hinner] at hi
  have hv : v = 0 := inner_self_eq_zero.mp (show inner ℝ v v = 0 by linarith)
  apply hinj
  ext x
  rw [ht, hv, add_zero, map_one]
  rfl

theorem nilpotent_is_translation (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hinj : Function.Injective ρ) (hρ : CoboundedOrbit ρ) [Group.IsNilpotent G] :
    ∀ (g : G) (x : E), ρ g x = x + ρ g 0 := by
  have hseries : ∀ i : ℕ, Subgroup.upperCentralSeries G i ≤ Subgroup.center G := by
    intro i
    induction i with
    | zero => exact bot_le
    | succ i ih =>
      intro g hg
      apply Subgroup.mem_center_iff.mpr
      intro h
      exact (commutatorElement_eq_one_iff_mul_comm.mp
        (commutator_eq_one_of_central ρ hinj hρ g h
          (ih (Subgroup.mem_upperCentralSeries_succ_iff.mp hg h)))).symm
  obtain ⟨i, hi⟩ := Group.IsNilpotent.nilpotent (G := G)
  have htop : (⊤ : Subgroup G) ≤ Subgroup.center G := hi ▸ hseries i
  exact fun g => central_is_translation ρ hρ (htop (Subgroup.mem_top g))

theorem coboundedOrbit_finiteIndex (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hρ : CoboundedOrbit ρ) (H : Subgroup G) [H.FiniteIndex] :
    CoboundedOrbit (ρ.comp H.subtype) := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨R, hR, hcover⟩ := hρ
  let B := ∑ q : G ⧸ H, dist (0 : E) (ρ q.out 0)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => dist_nonneg)
  refine ⟨R + B, add_nonneg hR hB, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hcover x
  let q : G ⧸ H := QuotientGroup.mk g⁻¹
  have hq : g * q.out ∈ H := by
    have he : (QuotientGroup.mk g⁻¹ : G ⧸ H) = QuotientGroup.mk q.out := q.out_eq'.symm
    simpa only [inv_inv] using QuotientGroup.eq.mp he
  refine ⟨⟨g * q.out, hq⟩, ?_⟩
  change dist x (ρ (g * q.out) 0) ≤ R + B
  calc
    _ ≤ dist x (ρ g 0) + dist (ρ g 0) (ρ (g * q.out) 0) := dist_triangle _ _ _
    _ = dist x (ρ g 0) + dist (0 : E) (ρ q.out 0) := by
      rw [map_mul]
      exact congrArg (dist x (ρ g 0) + ·) ((ρ g).dist_map 0 (ρ q.out 0))
    _ ≤ R + B := by
      apply add_le_add hg
      change dist (0 : E) (ρ q.out 0) ≤ ∑ r : G ⧸ H, dist (0 : E) (ρ r.out 0)
      exact Finset.single_le_sum (f := fun r : G ⧸ H => dist (0 : E) (ρ r.out 0))
        (fun _ _ => dist_nonneg) (Finset.mem_univ q)

theorem linearPart_eq_one_of_translation (u : E ≃ᵃⁱ[ℝ] E)
    (hu : ∀ x : E, u x = x + u 0) : linearPart u = 1 := by
  ext x
  exact add_right_cancel ((affine_eq_linear_add u x).symm.trans (hu x))

theorem translation_of_linearPart_eq_one (u : E ≃ᵃⁱ[ℝ] E)
    (hu : linearPart u = 1) (x : E) : u x = x + u 0 := by
  have hx : u.linearIsometryEquiv x = x :=
    congrArg (fun A : E ≃ₗᵢ[ℝ] E => A x) hu
  rw [affine_eq_linear_add, hx]

theorem finiteIndex_linear_kernel (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hinj : Function.Injective ρ) (hρ : CoboundedOrbit ρ)
    (hvirt : Group.IsVirtuallyNilpotent G) :
    (linearPart.comp ρ).ker.FiniteIndex := by
  obtain ⟨H, hHnil, hHindex⟩ := hvirt
  let := hHnil
  let := hHindex
  have ht := nilpotent_is_translation (ρ.comp H.subtype)
    (hinj.comp H.subtype_injective) (coboundedOrbit_finiteIndex ρ hρ H)
  have hle : H ≤ (linearPart.comp ρ).ker := by
    intro g hg
    exact linearPart_eq_one_of_translation (ρ g) (ht ⟨g, hg⟩)
  exact Subgroup.finiteIndex_of_le hle

theorem finite_linear_range (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hinj : Function.Injective ρ) (hρ : CoboundedOrbit ρ)
    (hvirt : Group.IsVirtuallyNilpotent G) :
    Finite (linearPart.comp ρ).range := by
  let := finiteIndex_linear_kernel ρ hinj hρ hvirt
  exact Finite.of_equiv (G ⧸ (linearPart.comp ρ).ker)
    (QuotientGroup.quotientKerEquivRange (linearPart.comp ρ))

def translationVectorHom (ρ : G →* (E ≃ᵃⁱ[ℝ] E)) :
    Additive (linearPart.comp ρ).ker →+ E where
  toFun g := ρ (g.toMul : G) 0
  map_zero' := by
    change ρ 1 0 = 0
    rw [map_one]
    rfl
  map_add' g h := by
    change ρ ((g.toMul : G) * (h.toMul : G)) 0 =
      ρ (g.toMul : G) 0 + ρ (h.toMul : G) 0
    rw [map_mul]
    change ρ (g.toMul : G) (ρ (h.toMul : G) 0) = _
    rw [translation_of_linearPart_eq_one _ g.toMul.property, add_comm]

def translationModule (ρ : G →* (E ≃ᵃⁱ[ℝ] E)) : Submodule ℤ E :=
  (translationVectorHom ρ).range.toIntSubmodule

theorem translationVectorHom_injective (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hinj : Function.Injective ρ) : Function.Injective (translationVectorHom ρ) := by
  intro g h hgh
  apply Additive.toMul.injective
  apply Subtype.ext
  apply hinj
  ext x
  rw [translation_of_linearPart_eq_one _ g.toMul.property,
    translation_of_linearPart_eq_one _ h.toMul.property]
  exact congrArg (x + ·) hgh

def translationEquiv (ρ : G →* (E ≃ᵃⁱ[ℝ] E)) (hinj : Function.Injective ρ) :
    Multiplicative (translationModule ρ) ≃* (linearPart.comp ρ).ker :=
  (AddEquiv.toMultiplicativeRight
    (AddMonoidHom.ofInjective (translationVectorHom_injective ρ hinj))).symm

theorem translationEquiv_apply (ρ : G →* (E ≃ᵃⁱ[ℝ] E)) (hinj : Function.Injective ρ)
    (u : Multiplicative (translationModule ρ)) (x : E) :
    ρ (translationEquiv ρ hinj u : G) x = x + (u.toAdd : E) := by
  rw [translation_of_linearPart_eq_one _ (translationEquiv ρ hinj u).property]
  exact congrArg (x + ·)
    (AddMonoidHom.apply_ofInjective_symm (translationVectorHom_injective ρ hinj) u.toAdd)

theorem discrete_translationModule (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hproper : ∀ B : ℝ, {g : G | ‖ρ g 0‖ ≤ B}.Finite) :
    DiscreteTopology (translationModule ρ) := by
  let D := translationModule ρ
  let S : Set D := {v | ‖(v : E)‖ ≤ 1}
  have hS : S.Finite := by
    apply Set.Finite.of_finite_image (f := ((↑) : D → E)) ?_ Subtype.coe_injective.injOn
    apply ((hproper 1).image (fun g : G => ρ g 0)).subset
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨a, ha⟩ := v.property
    change ρ (a.toMul : G) 0 = (v : E) at ha
    refine ⟨a.toMul, ?_, ha⟩
    change ‖ρ (a.toMul : G) 0‖ ≤ 1
    rw [ha]
    exact hv
  have hc : Continuous (fun v : D => ‖(v : E)‖) := continuous_norm.comp continuous_subtype_val
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  apply isOpen_singleton_of_finite_mem_nhds (0 : D) _ hS
  exact hc.continuousAt.preimage_mem_nhds (Iic_mem_nhds (by norm_num))

theorem span_eq_top_of_cobounded [FiniteDimensional ℝ E] (D : Submodule ℤ E)
    (R : ℝ) (hR : ∀ x : E, ∃ v : D, dist x (v : E) ≤ R) :
    Submodule.span ℝ (D : Set E) = ⊤ := by
  let S := Submodule.span ℝ (D : Set E)
  let : IsClosed (S : Set E) := S.closed_of_finiteDimensional
  have hzero : S.mkQ = 0 := linear_eq_zero_of_uniform_bound S.mkQ R (fun x => by
    obtain ⟨v, hv⟩ := hR x
    have hmem : (v : E) ∈ S := Submodule.subset_span v.property
    have hvzero : S.mkQ (v : E) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hmem
    have he : S.mkQ (x - v) = S.mkQ x := by rw [map_sub, hvzero, sub_zero]
    have hnorm := Submodule.Quotient.norm_mk_le S (x - v)
    change ‖S.mkQ (x - v)‖ ≤ ‖x - v‖ at hnorm
    rw [he] at hnorm
    exact hnorm.trans (by simpa only [dist_eq_norm] using hv))
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero S).mp (LinearMap.congr_fun hzero x)

theorem isZLattice_translationModule [FiniteDimensional ℝ E]
    (ρ : G →* (E ≃ᵃⁱ[ℝ] E)) (hinj : Function.Injective ρ)
    (hρ : CoboundedOrbit ρ) (hvirt : Group.IsVirtuallyNilpotent G)
    [DiscreteTopology (translationModule ρ)] :
    IsZLattice ℝ (translationModule ρ) := by
  let := finiteIndex_linear_kernel ρ hinj hρ hvirt
  obtain ⟨R, _, hR⟩ := coboundedOrbit_finiteIndex ρ hρ (linearPart.comp ρ).ker
  refine ⟨span_eq_top_of_cobounded (translationModule ρ) R (fun x => ?_)⟩
  obtain ⟨g, hg⟩ := hR x
  exact ⟨⟨ρ (g : G) 0, ⟨Additive.ofMul g, rfl⟩⟩, hg⟩

theorem fg_of_coboundedOrbit (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hρ : CoboundedOrbit ρ)
    (hproper : ∀ B : ℝ, {g : G | ‖ρ g 0‖ ≤ B}.Finite) : Group.FG G := by
  classical
  obtain ⟨R, hR, hcover⟩ := hρ
  let S : Set G := {g | ‖ρ g 0‖ ≤ 2 * R + 1}
  let H := Subgroup.closure S
  have hshort (g h : G) (hgh : dist (ρ g 0) (ρ h 0) ≤ 2 * R + 1) :
      g⁻¹ * h ∈ H := by
    apply Subgroup.subset_closure
    have he : ρ g (ρ (g⁻¹ * h) 0) = ρ h 0 := by
      change (ρ g * ρ (g⁻¹ * h)) 0 = ρ h 0
      rw [← map_mul, mul_inv_cancel_left]
    change ‖ρ (g⁻¹ * h) 0‖ ≤ 2 * R + 1
    calc
      ‖ρ (g⁻¹ * h) 0‖ = dist (0 : E) (ρ (g⁻¹ * h) 0) := (dist_zero_left _).symm
      _ = dist (ρ g 0) (ρ g (ρ (g⁻¹ * h) 0)) := ((ρ g).dist_map _ _).symm
      _ ≤ 2 * R + 1 := by rw [he]; exact hgh
  choose a ha using hcover
  let q : E → G ⧸ H := fun x => QuotientGroup.mk (a x)
  have hnear (x y : E) (hxy : dist x y < 1) : q x = q y := by
    apply QuotientGroup.eq.mpr
    apply hshort
    have h1 := dist_triangle (ρ (a x) 0) x (ρ (a y) 0)
    have h2 := dist_triangle x y (ρ (a y) 0)
    have hx := ha x
    have hy := ha y
    rw [dist_comm (ρ (a x) 0) x] at h1
    linarith
  have hq : IsLocallyConstant q := by
    apply (IsLocallyConstant.iff_exists_open q).mpr
    intro x
    refine ⟨Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one, ?_⟩
    intro y hy
    exact hnear y x (Metric.mem_ball.mp hy)
  have ha0 : a 0 ∈ H := by
    have hd : dist (ρ 1 0) (ρ (a 0) 0) ≤ 2 * R + 1 := by
      rw [map_one]
      change dist (0 : E) (ρ (a 0) 0) ≤ 2 * R + 1
      linarith [ha 0]
    simpa only [inv_one, one_mul] using hshort 1 (a 0) hd
  have hq0 : q 0 = (QuotientGroup.mk (1 : G) : G ⧸ H) := by
    apply QuotientGroup.eq.mpr
    simpa only [mul_one] using H.inv_mem ha0
  have htop : H = ⊤ := by
    apply top_unique
    intro g _
    have hgq : (QuotientGroup.mk g : G ⧸ H) = q (ρ g 0) := by
      apply QuotientGroup.eq.mpr
      apply hshort
      linarith [ha (ρ g 0)]
    have he := (hgq.trans ((hq.apply_eq_of_preconnectedSpace (ρ g 0) 0).trans hq0)).symm
    simpa only [inv_one, one_mul] using QuotientGroup.eq.mp he
  exact Group.fg_iff.mpr ⟨S, htop, hproper (2 * R + 1)⟩

end DifferentialGeometry.CrystallographicActions
