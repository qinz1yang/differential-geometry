/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.ClosedBall.AnnulusImage
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Homotopy.ConvexProduct
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurface

/-!
# Spherical shells and their connected polyhedral separators
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [TopologicalSpace E] {X B₀ B₁ : Set E}

private theorem image_shell_slice
    (φ : (SphereTwo × unitInterval) ≃ₜ X) (t : unitInterval) :
    Subtype.val '' (φ '' {p | (p.2 : ℝ) = t}) =
      range (fun s : SphereTwo => (φ (s, t) : E)) := by
  ext x
  constructor
  · rintro ⟨y, ⟨⟨s, u⟩, hu, rfl⟩, rfl⟩
    have hut : u = t := Subtype.ext hu
    subst u
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨φ (s, t), ⟨(s, t), rfl, rfl⟩, rfl⟩

theorem IsSphericalShell.isCompact (h : IsSphericalShell X B₀ B₁) : IsCompact X := by
  obtain ⟨φ, -, -⟩ := h
  let _ : CompactSpace X := φ.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

theorem IsSphericalShell.isConnected (h : IsSphericalShell X B₀ B₁) : IsConnected X := by
  obtain ⟨φ, -, -⟩ := h
  have hrange : range (fun p : SphereTwo × unitInterval => (φ p : E)) = X := by
    rw [← Function.comp_def, range_comp, φ.surjective.range_eq, image_univ, Subtype.range_val]
  rw [← hrange]
  exact isConnected_range (continuous_subtype_val.comp φ.continuous)

theorem IsSphericalShell.isCompact_left (h : IsSphericalShell X B₀ B₁) : IsCompact B₀ := by
  obtain ⟨φ, rfl, -⟩ := h
  rw [show {p : SphereTwo × unitInterval | (p.2 : ℝ) = 0} =
    {p | (p.2 : ℝ) = (0 : unitInterval)} from rfl, image_shell_slice]
  exact isCompact_range (continuous_subtype_val.comp
    (φ.continuous.comp (continuous_id.prodMk continuous_const)))

theorem IsSphericalShell.isCompact_right (h : IsSphericalShell X B₀ B₁) : IsCompact B₁ := by
  obtain ⟨φ, -, rfl⟩ := h
  rw [show {p : SphereTwo × unitInterval | (p.2 : ℝ) = 1} =
    {p | (p.2 : ℝ) = (1 : unitInterval)} from rfl, image_shell_slice]
  exact isCompact_range (continuous_subtype_val.comp
    (φ.continuous.comp (continuous_id.prodMk continuous_const)))

theorem IsSphericalShell.isConnected_left (h : IsSphericalShell X B₀ B₁) :
    IsConnected B₀ := by
  obtain ⟨φ, rfl, -⟩ := h
  rw [show {p : SphereTwo × unitInterval | (p.2 : ℝ) = 0} =
    {p | (p.2 : ℝ) = (0 : unitInterval)} from rfl, image_shell_slice]
  exact isConnected_range (continuous_subtype_val.comp
    (φ.continuous.comp (continuous_id.prodMk continuous_const)))

theorem IsSphericalShell.isConnected_right (h : IsSphericalShell X B₀ B₁) :
    IsConnected B₁ := by
  obtain ⟨φ, -, rfl⟩ := h
  rw [show {p : SphereTwo × unitInterval | (p.2 : ℝ) = 1} =
    {p | (p.2 : ℝ) = (1 : unitInterval)} from rfl, image_shell_slice]
  exact isConnected_range (continuous_subtype_val.comp
    (φ.continuous.comp (continuous_id.prodMk continuous_const)))

theorem IsSphericalShell.left_subset (h : IsSphericalShell X B₀ B₁) : B₀ ⊆ X := by
  obtain ⟨φ, rfl, -⟩ := h
  rintro x ⟨y, -, rfl⟩
  exact y.property

theorem IsSphericalShell.right_subset (h : IsSphericalShell X B₀ B₁) : B₁ ⊆ X := by
  obtain ⟨φ, -, rfl⟩ := h
  rintro x ⟨y, -, rfl⟩
  exact y.property

theorem IsSphericalShell.disjoint (h : IsSphericalShell X B₀ B₁) : Disjoint B₀ B₁ := by
  obtain ⟨φ, rfl, rfl⟩ := h
  apply disjoint_left.mpr
  rintro x ⟨y, ⟨p, hp, rfl⟩, hpx⟩ ⟨z, ⟨q, hq, rfl⟩, hqx⟩
  have hpq : p = q := φ.injective (Subtype.ext (hpx.trans hqx.symm))
  subst q
  have : (0 : ℝ) = 1 := hp.symm.trans hq
  exact zero_ne_one this

theorem IsSphericalShell.frontier_eq
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (h : IsSphericalShell X B₀ B₁) :
    frontier X = B₀ ∪ B₁ := by
  obtain ⟨φ, rfl, rfl⟩ := h
  let g : SphereTwo × unitInterval → EuclideanSpace ℝ (Fin 3) :=
    fun p => (φ p : EuclideanSpace ℝ (Fin 3))
  have hrange : range g = X := by
    change range (Subtype.val ∘ φ) = X
    rw [range_comp, φ.surjective.range_eq, image_univ, Subtype.range_val]
  have hi : Function.Injective g := Subtype.val_injective.comp φ.injective
  have hc : Continuous g := continuous_subtype_val.comp φ.continuous
  have hf := frontier_range_sphere_prod_unitInterval g hc hi
  rw [hrange] at hf
  simpa only [← image_comp, g, Function.comp_def] using hf

theorem IsSphericalShell.simplyConnectedSpace_interior
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (h : IsSphericalShell X B₀ B₁) :
    SimplyConnectedSpace (interior X) := by
  obtain ⟨φ, -, -⟩ := h
  let g : SphereTwo × unitInterval → EuclideanSpace ℝ (Fin 3) :=
    fun p => (φ p : EuclideanSpace ℝ (Fin 3))
  have hrange : range g = X := by
    change range (Subtype.val ∘ φ) = X
    rw [range_comp, φ.surjective.range_eq, image_univ, Subtype.range_val]
  have hi : Function.Injective g := Subtype.val_injective.comp φ.injective
  have hc : Continuous g := continuous_subtype_val.comp φ.continuous
  let e := (sphereProdIooHomeomorphInteriorRange g hc hi).trans
    (Homeomorph.setCongr (congrArg interior hrange))
  let c : Ioo (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
  exact ContinuousMap.HomotopyEquiv.simplyConnectedSpace (e.symm.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex SphereTwo (convex_Ioo 0 1) c))

theorem isSphericalShell_norm_band {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsSphericalShell {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ∈ Icc a b}
      (Metric.sphere 0 a) (Metric.sphere 0 b) := by
  let φ : (SphereTwo × unitInterval) ≃ₜ
      {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ∈ Icc a b} :=
    ((Homeomorph.refl _).prodCongr (iccHomeoI a b hab).symm).trans
      (sphereProdIccHomeomorphAnnulus a b ha)
  refine ⟨φ, ?_, ?_⟩
  · apply Set.ext
    intro x
    constructor
    · intro hx
      have hn : ‖x‖ = a := mem_sphere_zero_iff_norm.mp hx
      let y : {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ∈ Icc a b} :=
        ⟨x, by change a ≤ ‖x‖ ∧ ‖x‖ ≤ b; rw [hn]; exact ⟨le_rfl, hab.le⟩⟩
      refine ⟨y, ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩, rfl⟩
      change ((iccHomeoI a b hab) ((sphereProdIccHomeomorphAnnulus a b ha).symm y).2 : ℝ) = 0
      rw [iccHomeoI_apply_coe, sphereProdIccHomeomorphAnnulus_symm_apply_snd_coe]
      change (‖x‖ - a) / (b - a) = 0
      rw [hn, sub_self, zero_div]
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      change ‖((b - a) * (p.2 : ℝ) + a) • (p.1 : EuclideanSpace ℝ (Fin 3))‖ = a
      rw [hp, mul_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
        mem_sphere_zero_iff_norm.mp p.1.property, mul_one]
  · apply Set.ext
    intro x
    constructor
    · intro hx
      have hn : ‖x‖ = b := mem_sphere_zero_iff_norm.mp hx
      let y : {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ∈ Icc a b} :=
        ⟨x, by change a ≤ ‖x‖ ∧ ‖x‖ ≤ b; rw [hn]; exact ⟨hab.le, le_rfl⟩⟩
      refine ⟨y, ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩, rfl⟩
      change ((iccHomeoI a b hab) ((sphereProdIccHomeomorphAnnulus a b ha).symm y).2 : ℝ) = 1
      rw [iccHomeoI_apply_coe, sphereProdIccHomeomorphAnnulus_symm_apply_snd_coe]
      change (‖x‖ - a) / (b - a) = 1
      rw [hn, div_self (sub_pos.mpr hab).ne']
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      change ‖((b - a) * (p.2 : ℝ) + a) • (p.1 : EuclideanSpace ℝ (Fin 3))‖ = b
      rw [hp, mul_one, sub_add_cancel, norm_smul, Real.norm_eq_abs,
        abs_of_pos (ha.trans hab), mem_sphere_zero_iff_norm.mp p.1.property, mul_one]

open Classical in
theorem IsSphericalShell.exists_connected_separating_surface
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (h : IsSphericalShell X B₀ B₁) :
    ∃ (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hLfin : L.faces.Finite),
      letI := hLfin.to_subtype
      IsCombinatorialManifold 2 L ∧ IsConnected L.space ∧ IsOrientable 2 L ∧
      IsTwoSided L.space ∧ L.space ⊆ interior X ∧ Separates L.space B₀ B₁ := by
  obtain ⟨L, hfin, hL, hc, ho, ht, -, hsep⟩ :=
    PiecewiseLinear.exists_connected_separating_surface (by simp :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
      h.isCompact_left h.isConnected_left h.isCompact_right.isClosed h.isConnected_right
      h.disjoint isOpen_univ (subset_univ _)
  let _ := hfin.to_subtype
  refine ⟨L, hfin, hL, hc, ho, ht, ?_, hsep⟩
  apply hsep.subset_interior_of_disjoint_frontier hc.isPreconnected h.isConnected.isPreconnected
  · obtain ⟨x, hx⟩ := h.isConnected_left.nonempty
    exact ⟨x, hx, h.left_subset hx⟩
  · obtain ⟨x, hx⟩ := h.isConnected_right.nonempty
    exact ⟨x, hx, h.right_subset hx⟩
  · rw [h.frontier_eq]
    exact disjoint_left.mpr fun x hx hxB => hxB.elim
      (fun hx₀ => hsep.left_subset_compl hx₀ hx)
      (fun hx₁ => hsep.right_subset_compl hx₁ hx)

end DifferentialGeometry.Topology.PiecewiseLinear
