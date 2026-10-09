import DifferentialGeometry.Geometry.Exponential.Flat.AffineTranslations
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Small rotational parts in a cocompact Euclidean group

A finite set of actual group elements approximates every rotational part. Cocompactness then
forces the displacement vectors of elements with arbitrarily small rotational part to span the
ambient space. No translation lattice, finite-index subgroup, or supplied spanning family is
assumed in this consequence of the actual affine action.
-/

set_option autoImplicit false

noncomputable section

open Set Module Submodule

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instSpace : NormedSpace ℝ V] [instFD : FiniteDimensional ℝ V]

def affineLinearOperator (g : V ≃ᵃⁱ[ℝ] V) : V →L[ℝ] V := g.linearIsometryEquiv

def affineRotationNorm (g : V ≃ᵃⁱ[ℝ] V) : ℝ :=
  ‖affineLinearOperator g - ContinuousLinearMap.id ℝ V‖

omit instFD in
theorem affineRotationNorm_mul_inv (g r : V ≃ᵃⁱ[ℝ] V) :
    affineRotationNorm (g * r⁻¹) = ‖affineLinearOperator g - affineLinearOperator r‖ := by
  have hop : affineLinearOperator (g * r⁻¹) - ContinuousLinearMap.id ℝ V =
      (affineLinearOperator g - affineLinearOperator r).comp
        ((r⁻¹).linearIsometryEquiv : V →L[ℝ] V) := by
    ext x
    change g.linearIsometryEquiv ((r⁻¹).linearIsometryEquiv x) - x =
      g.linearIsometryEquiv ((r⁻¹).linearIsometryEquiv x) -
        r.linearIsometryEquiv ((r⁻¹).linearIsometryEquiv x)
    have hid := congrArg (fun L : V ≃ₗᵢ[ℝ] V => L x)
      (affineLinearHom.map_mul r r⁻¹)
    simp only [mul_inv_cancel, map_one] at hid
    change x = r.linearIsometryEquiv ((r⁻¹).linearIsometryEquiv x) at hid
    rw [← hid]
  unfold affineRotationNorm
  rw [hop, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem finite_rotation_approx (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Set G, T.Finite ∧ ∀ g : G, ∃ r ∈ T,
      affineRotationNorm ((g * r⁻¹ : G) : V ≃ᵃⁱ[ℝ] V) < ε := by
  classical
  let L : G → V →L[ℝ] V := fun g => affineLinearOperator g
  have hbounded : Set.range L ⊆ Metric.closedBall 0 1 := by
    rintro A ⟨g, rfl⟩
    apply mem_closedBall_zero_iff.mpr
    apply ContinuousLinearMap.opNorm_le_bound (L g) zero_le_one
    intro x
    simp [L, affineLinearOperator]
  have htb : TotallyBounded (Set.range L) :=
    (isCompact_closedBall (0 : V →L[ℝ] V) 1).totallyBounded.subset hbounded
  obtain ⟨t, ht, hfin, hcover⟩ := Metric.finite_approx_of_totallyBounded htb ε hε
  let rep : (V →L[ℝ] V) → G := Function.invFun L
  have hrep : ∀ A ∈ t, L (rep A) = A := by
    intro A hA
    exact Function.invFun_eq (ht hA)
  refine ⟨rep '' t, hfin.image rep, ?_⟩
  intro g
  have hmem := hcover (Set.mem_range_self g)
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨A, hA, hgA⟩ := hmem
  refine ⟨rep A, ⟨A, hA, rfl⟩, ?_⟩
  change affineRotationNorm ((g : V ≃ᵃⁱ[ℝ] V) * (rep A : V ≃ᵃⁱ[ℝ] V)⁻¹) < ε
  rw [affineRotationNorm_mul_inv]
  change ‖L g - L (rep A)‖ < ε
  rw [hrep A hA]
  simpa only [Metric.mem_ball, dist_eq_norm] using hgA

theorem smallRotation_displacements_span (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R ε : ℝ}
    (hcov : ∀ x : V, ∃ g : G, ‖x - (g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R) (hε : 0 < ε) :
    Submodule.span ℝ {v : V | ∃ g : G,
      affineRotationNorm (g : V ≃ᵃⁱ[ℝ] V) < ε ∧ (g : V ≃ᵃⁱ[ℝ] V) 0 = v} = ⊤ := by
  classical
  let S : Set V := {v | ∃ g : G,
    affineRotationNorm (g : V ≃ᵃⁱ[ℝ] V) < ε ∧ (g : V ≃ᵃⁱ[ℝ] V) 0 = v}
  change Submodule.span ℝ S = ⊤
  by_contra hne
  obtain ⟨f, hfne, hfker⟩ := Submodule.exists_le_ker_of_lt_top (Submodule.span ℝ S)
    (lt_top_iff_ne_top.mpr hne)
  obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
    by_contra h
    push Not at h
    exact hfne (LinearMap.ext h)
  let F : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap f
  obtain ⟨T, hT, happ⟩ := finite_rotation_approx G hε
  obtain ⟨B, hB⟩ := (hT.image (fun r : G => ‖(r : V ≃ᵃⁱ[ℝ] V) 0‖)).exists_le
  have horbit : ∀ g : G, ‖F ((g : V ≃ᵃⁱ[ℝ] V) 0)‖ ≤ ‖F‖ * max B 0 := by
    intro g
    obtain ⟨r, hr, hrot⟩ := happ g
    let δ : G := g * r⁻¹
    have hzero : f ((δ : V ≃ᵃⁱ[ℝ] V) 0) = 0 :=
      hfker (Submodule.subset_span ⟨δ, hrot, rfl⟩)
    have hrel : (δ : V ≃ᵃⁱ[ℝ] V) ((r : V ≃ᵃⁱ[ℝ] V) 0) =
        (g : V ≃ᵃⁱ[ℝ] V) 0 := by
      change (g : V ≃ᵃⁱ[ℝ] V) ((r : V ≃ᵃⁱ[ℝ] V).symm
        ((r : V ≃ᵃⁱ[ℝ] V) 0)) = (g : V ≃ᵃⁱ[ℝ] V) 0
      rw [AffineIsometryEquiv.symm_apply_apply]
    have hval : F ((g : V ≃ᵃⁱ[ℝ] V) 0) =
        F ((δ : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv ((r : V ≃ᵃⁱ[ℝ] V) 0)) := by
      rw [← hrel, affineIsometry_apply, map_add]
      change f ((δ : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv ((r : V ≃ᵃⁱ[ℝ] V) 0)) +
        f ((δ : V ≃ᵃⁱ[ℝ] V) 0) =
        f ((δ : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv ((r : V ≃ᵃⁱ[ℝ] V) 0))
      rw [hzero, add_zero]
    rw [hval]
    refine (F.le_opNorm ?_).trans ?_
    rw [(δ : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_left
      ((hB _ ⟨r, hr, rfl⟩).trans (le_max_left B 0)) (norm_nonneg F)
  have hR : 0 ≤ R := by
    obtain ⟨g, hg⟩ := hcov 0
    exact (norm_nonneg (0 - (g : V ≃ᵃⁱ[ℝ] V) 0)).trans hg
  have hbound : ∀ x : V, ‖F x‖ ≤ ‖F‖ * R + ‖F‖ * max B 0 := by
    intro x
    obtain ⟨g, hg⟩ := hcov x
    calc
      ‖F x‖ = ‖F (x - (g : V ≃ᵃⁱ[ℝ] V) 0) + F ((g : V ≃ᵃⁱ[ℝ] V) 0)‖ := by
        rw [← map_add, sub_add_cancel]
      _ ≤ ‖F (x - (g : V ≃ᵃⁱ[ℝ] V) 0)‖ + ‖F ((g : V ≃ᵃⁱ[ℝ] V) 0)‖ := norm_add_le _ _
      _ ≤ ‖F‖ * R + ‖F‖ * max B 0 := add_le_add
        ((F.le_opNorm (x - (g : V ≃ᵃⁱ[ℝ] V) 0)).trans
          (mul_le_mul_of_nonneg_left hg (norm_nonneg F))) (horbit g)
  let t : ℝ := (‖F‖ * R + ‖F‖ * max B 0 + 1) / f u
  have hvalue : F (t • u) = ‖F‖ * R + ‖F‖ * max B 0 + 1 := by
    change f (t • u) = ‖F‖ * R + ‖F‖ * max B 0 + 1
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ _ hu
  have hcontra := hbound (t • u)
  rw [hvalue, Real.norm_eq_abs, abs_of_pos (by positivity)] at hcontra
  linarith

omit instFD in
theorem affineRotationNorm_commutator (g k : V ≃ᵃⁱ[ℝ] V) :
    affineRotationNorm (g * k * g⁻¹ * k⁻¹) ≤
      2 * affineRotationNorm g * affineRotationNorm k := by
  by_cases hV : Subsingleton V
  · let instSubsingleton : Subsingleton V := hV
    simp [affineRotationNorm, Subsingleton.elim
      (affineLinearOperator (g * k * g⁻¹ * k⁻¹)) (ContinuousLinearMap.id ℝ V)]
  · let instNontrivial : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    let a := g.linearIsometryEquiv.toContinuousLinearEquiv.toUnit
    let b := k.linearIsometryEquiv.toContinuousLinearEquiv.toUnit
    have hap : ‖(a⁻¹ : (V →L[ℝ] V)ˣ).val‖ = 1 := by
      exact g.linearIsometryEquiv.symm.norm_toContinuousLinearMap
    have hbp : ‖(b⁻¹ : (V →L[ℝ] V)ˣ).val‖ = 1 := by
      exact k.linearIsometryEquiv.symm.norm_toContinuousLinearMap
    have hprod : (a * b * a⁻¹ * b⁻¹).val =
        affineLinearOperator (g * k * g⁻¹ * k⁻¹) := by ext x; rfl
    have h := norm_commutator_units_sub_one_le a b
    rw [hprod, hap, hbp, mul_one, mul_one] at h
    exact h

theorem exists_smallRotation_basis (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R ε : ℝ}
    (hcov : ∀ x : V, ∃ g : G, ‖x - (g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R) (hε : 0 < ε) :
    ∃ b : Basis (Fin (finrank ℝ V)) ℝ V, ∃ a : Fin (finrank ℝ V) → G,
      ∀ i, affineRotationNorm (a i : V ≃ᵃⁱ[ℝ] V) < ε ∧ (a i : V ≃ᵃⁱ[ℝ] V) 0 = b i := by
  classical
  let S : Set V := {v | ∃ g : G,
    affineRotationNorm (g : V ≃ᵃⁱ[ℝ] V) < ε ∧ (g : V ≃ᵃⁱ[ℝ] V) 0 = v}
  have hS : ⊤ ≤ Submodule.span ℝ S := by
    rw [smallRotation_displacements_span G hcov hε]
  let J := (linearIndepOn_empty ℝ (id : V → V)).extend (empty_subset S)
  let b₀ : Basis J ℝ V := Basis.ofSpan hS
  let instIndexFinite : Finite J := Module.Finite.finite_basis b₀
  let instIndexFintype : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hmem : ∀ i, b i ∈ S := by
    intro i
    simpa only [b, Basis.reindex_apply] using
      Basis.ofSpan_subset hS (Set.mem_range_self (e.symm i))
  choose a ha using hmem
  exact ⟨b, a, ha⟩

end DifferentialGeometry.Geometry.FlatSurface
