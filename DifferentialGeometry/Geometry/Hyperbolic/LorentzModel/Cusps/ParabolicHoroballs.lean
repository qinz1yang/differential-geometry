/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.ParabolicRegions
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.TranslationLattices
import Mathlib.RingTheory.SimpleRing.Principal

noncomputable section

open Set
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.ParabolicHoroballs

open Hyperbolic HyperbolicAction HyperbolicBoundary
open Busemann BusemannCocycle BoundaryFixedPoints BoundaryStabilizer
open Horospherical MobiusBoundary TranslationLattices ParabolicRegions

variable {m : ℕ}

theorem horo_injective : Function.Injective (horo (m := m)) := by
  intro x y hxy
  have hheight := congrArg (fun ξ : BoundaryH (m + 1) => vHeight ξ.val) hxy
  have hi : (tc (horoVec x))⁻¹ = (tc (horoVec y))⁻¹ := by
    simpa only [horo, boundaryRep, vHeight_smul, vHeight_horoVec, mul_one] using hheight
  have ht : tc (horoVec x) = tc (horoVec y) := inv_injective hi
  funext i
  have h := congrArg (fun ξ : BoundaryH (m + 1) => ξ.val (Sum.inl i.castSucc)) hxy
  simp only [horo, boundaryRep, Pi.smul_apply, smul_eq_mul, horoVec_castSucc] at h
  rw [← ht] at h
  exact mul_left_cancel₀ (inv_ne_zero (tc_horoVec_pos x).ne') h

theorem translation_isParabolicAt (u : Horizontal m) (hu : u ≠ 0) :
    IsParabolicAt (by omega) (translation u) ptInfty := by
  refine ⟨?_, ?_, ?_⟩
  · intro hfin
    obtain ⟨k, hk, hpow⟩ := hfin.exists_pow_eq_one
    have hmap : translation (k • u) = translation u ^ k :=
      map_pow translationHom (Multiplicative.ofAdd u) k
    have hz : (k : ℝ) • u = 0 := by
      rw [Nat.cast_smul_eq_nsmul]
      exact translation_injective (hmap.trans (hpow.trans translation_zero.symm))
    exact hu ((smul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr hk.ne'))
  · apply (po_boundary_smul_mk (by omega) (transLor (fun i => u i)) ptInfty).trans
    apply boundary_fixed_of_eigen _ _ one_ne_zero
    rw [one_smul]
    exact transLor_fix_ptInfty _
  · intro η hη
    by_contra hne
    obtain ⟨x, rfl⟩ := exists_horo_eq_of_ne_ptInfty η hne
    have he : horo (x + (fun i => u i)) = horo x :=
      (trans_po_smul_horo (fun i => u i) x).symm.trans hη
    have hx := horo_injective he
    have hz : (fun i => u i) = 0 := add_left_cancel (hx.trans (add_zero x).symm)
    apply hu
    ext i
    exact congrFun hz i

local instance : MulAction (PO (m + 1) 1) (HUpper (m + 1)) := poMulAction (by omega)

theorem cosh_displacement_translation (u : Horizontal m) (X : HUpper (m + 1)) :
    Real.cosh (dist (translation u • X) X) =
      1 + ‖u‖ ^ 2 / (2 * height X * height X) := by
  obtain ⟨⟨x, h, hh⟩, rfl⟩ := coordsEquiv.symm.surjective X
  change Real.cosh (dist (translation u • ofCoords x h hh) (ofCoords x h hh)) =
    1 + ‖u‖ ^ 2 / (2 * height (ofCoords x h hh) * height (ofCoords x h hh))
  rw [translation_smul_ofCoords, cosh_dist_ofCoords, height_ofCoords]
  simp only [add_sub_cancel_left]
  field_simp
  ring

theorem exists_height_short_translation (u : Horizontal m) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℝ, 0 < H ∧ ∀ X : HUpper (m + 1), H ≤ height X →
      dist (translation u • X) X < ε := by
  have hcε : 1 < Real.cosh ε := by
    have h : Real.cosh 0 < Real.cosh ε :=
      Real.cosh_lt_cosh.mpr (by simpa only [abs_zero, abs_of_pos hε] using hε)
    simpa only [Real.cosh_zero] using h
  have hd : 0 < Real.cosh ε - 1 := sub_pos.mpr hcε
  obtain ⟨H, hH⟩ := exists_gt (max 1 (‖u‖ ^ 2 / (Real.cosh ε - 1)))
  have hH1 : 1 < H := (le_max_left _ _).trans_lt hH
  have hHu : ‖u‖ ^ 2 < H * (Real.cosh ε - 1) :=
    (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hH)
  refine ⟨H, by linarith, fun X hX => ?_⟩
  have hh := height_pos X
  have hh1 : 1 ≤ height X := hH1.le.trans hX
  have hsq : H ≤ 2 * height X * height X := by
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
  have hbound : ‖u‖ ^ 2 / (2 * height X * height X) < Real.cosh ε - 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * height X * height X)).mpr
    exact hHu.trans_le (by
      simpa only [mul_comm (Real.cosh ε - 1)] using mul_le_mul_of_nonneg_right hsq hd.le)
  have hcosh : Real.cosh (dist (translation u • X) X) < Real.cosh ε := by
    rw [cosh_displacement_translation]
    linarith
  simpa only [abs_of_nonneg dist_nonneg, abs_of_pos hε] using Real.cosh_lt_cosh.mp hcosh

theorem exists_horoball_subset_region (Γ : Subgroup (PO (m + 1) 1))
    (u : Horizontal m) (hu : u ≠ 0) (huΓ : translation u ∈ Γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, horoball ptInfty c ⊆ region (by omega) Γ ε ptInfty := by
  obtain ⟨H, hH, hshort⟩ := exists_height_short_translation u hε
  refine ⟨-Real.log H, fun X hX => ?_⟩
  have hheight : H ≤ height X := by
    simpa only [mem_horoball_iff_height, neg_neg, Real.exp_log hH] using hX
  exact ⟨⟨translation u, huΓ⟩, translation_isParabolicAt u hu, hshort X hheight⟩

theorem image_horoball_of_fix {n : ℕ} (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {ξ : BoundaryH n}
    (g : Γ) (hg : IsParabolicAt hn (g : PO n 1) ξ) (c : ℝ)
    (δ : Γ) (hδ : (poBoundaryMulAction hn).smul (δ : PO n 1) ξ = ξ) :
    (fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) '' horoball ξ c =
      horoball ξ c := by
  let := poMulAction hn
  have hscale := poConfFactor_eq_one_on_parabolic_stabilizer hn Γ hΓ g ξ hg.fix hg.unique δ hδ
  have hmem (x : HUpper n) :
      (poMulAction hn).smul (δ : PO n 1) x ∈ horoball ξ c ↔ x ∈ horoball ξ c := by
    simpa only [hδ, hscale, Real.log_one, sub_zero] using
      po_smul_mem_horoball_iff hn δ ξ c x
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro x hx
    let y : HUpper n := (δ : PO n 1)⁻¹ • x
    have he : (poMulAction hn).smul (δ : PO n 1) y = x := smul_inv_smul _ _
    exact ⟨y, (hmem y).mp (he.symm ▸ hx), he⟩

theorem precisely_invariant_horoball_of_subset_region {n : ℕ} (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    (hgeom : ∀ x : HUpper n,
      ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (g : Γ) (hg : IsParabolicAt hn (g : PO n 1) ξ)
    (c : ℝ) (hsub : horoball ξ c ⊆ region hn Γ ε ξ) (δ : Γ) :
    ((poBoundaryMulAction hn).smul (δ : PO n 1) ξ = ξ →
      (fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) '' horoball ξ c =
        horoball ξ c) ∧
    ((poBoundaryMulAction hn).smul (δ : PO n 1) ξ ≠ ξ →
      Disjoint
        ((fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) '' horoball ξ c)
        (horoball ξ c)) := by
  refine ⟨image_horoball_of_fix hn Γ hΓ g hg c δ, fun hδ => ?_⟩
  exact ((precisely_invariant_region hn Γ hΓ ε hgeom ξ δ).2 hδ).mono
    (Set.image_mono hsub) hsub

theorem exists_precisely_invariant_horoball (Γ : Subgroup (PO (m + 1) 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (u : Horizontal m)
    (hu : u ≠ 0) (huΓ : translation u ∈ Γ) :
    ∃ c : ℝ, ∀ δ : Γ,
      ((poBoundaryMulAction (by omega)).smul (δ : PO (m + 1) 1) ptInfty = ptInfty →
        (fun X : HUpper (m + 1) => (δ : PO (m + 1) 1) • X) '' horoball ptInfty c =
          horoball ptInfty c) ∧
      ((poBoundaryMulAction (by omega)).smul (δ : PO (m + 1) 1) ptInfty ≠ ptInfty →
        Disjoint
          ((fun X : HUpper (m + 1) => (δ : PO (m + 1) 1) • X) '' horoball ptInfty c)
          (horoball ptInfty c)) := by
  obtain ⟨ε, hε, hgeom⟩ := exists_margulis_geometry_constant (by omega : 1 ≤ m + 1)
  obtain ⟨c, hc⟩ := exists_horoball_subset_region Γ u hu huΓ hε
  exact ⟨c, fun δ => precisely_invariant_horoball_of_subset_region (by omega) Γ hΓ ε
    (hgeom Γ hΓ) ⟨translation u, huΓ⟩ (translation_isParabolicAt u hu) c hc δ⟩

end DifferentialGeometry.ParabolicHoroballs
