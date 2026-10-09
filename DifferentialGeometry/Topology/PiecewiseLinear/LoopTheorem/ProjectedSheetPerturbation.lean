/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HalfSpaceGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.HeightChange
import DifferentialGeometry.Topology.PiecewiseLinear.TransverseHeight
import DifferentialGeometry.Topology.PiecewiseLinear.SingularLocal
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_homeomorph_adjust_displacement_preserving_halfSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) (ℓ m : E →L[ℝ] ℝ) {d : E}
    (hd : d ∈ P) (hℓd : ℓ d = 1) (hmd : m d = 0)
    {a : E → E} (ha : IsPiecewiseAffineOn a univ) {k : NNReal}
    (halip : LipschitzWith k a) (hk : (‖ℓ‖₊ * k) * ‖d‖₊ < 1)
    (h : E ≃ₜ E) (hh : IsPLHomeomorphOn h univ univ)
    (hformula : ∀ x, h x = x + a x)
    (hm : ∀ x, (m (h x) = 0 ↔ m x = 0) ∧ (0 ≤ m (h x) ↔ 0 ≤ m x)) :
    ∃ H : E ≃ₜ E, IsPLHomeomorphOn H univ univ ∧ H '' (P : Set E) = h '' P ∧
      (∀ x, ℓ (H x) = ℓ x) ∧
      (∀ x, (m (H x) = 0 ↔ m x = 0) ∧ (0 ≤ m (H x) ↔ 0 ≤ m x)) ∧
      ∀ x, a x = 0 → H x = x := by
  let b : E → E := fun x => ℓ (a x) • d
  have hb : IsPiecewiseAffineOn b univ :=
    (ha.affine_comp ℓ.toLinearMap.toAffineMap).affine_comp
      (LinearMap.toSpanSingleton ℝ E d).toAffineMap
  have hblip : LipschitzWith ((‖ℓ‖₊ * k) * ‖d‖₊) b := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (ℓ (a x) • d) (ℓ (a y) • d) ≤ _
    rw [dist_eq_norm, ← sub_smul, norm_smul]
    have hbound := (ℓ.lipschitzWith.comp halip).dist_le_mul x y
    rw [dist_eq_norm] at hbound
    calc ‖ℓ (a x) - ℓ (a y)‖ * ‖d‖ ≤
          ((‖ℓ‖₊ * k : NNReal) * dist x y) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
      _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring
  have hF := isPLHomeomorphOn_id_add_of_lipschitz hb hblip hk
  let F : E ≃ₜ E :=
    (Homeomorph.Set.univ E).symm.trans (hF.homeomorph.trans (Homeomorph.Set.univ E))
  have hFP (x : E) : F x ∈ P ↔ x ∈ P :=
    P.add_mem_iff_left (P.smul_mem (ℓ (a x)) hd)
  have hFm (x : E) : m (F x) = m x := by
    change m (x + ℓ (a x) • d) = m x
    rw [map_add, map_smul, hmd, smul_zero, add_zero]
  have hFℓ (x : E) : ℓ (F x) = ℓ (h x) := by
    change ℓ (x + ℓ (a x) • d) = ℓ (h x)
    rw [hformula, map_add, map_smul, hℓd, smul_eq_mul, mul_one, map_add]
  let H : E ≃ₜ E := F.symm.trans h
  have hH : IsPLHomeomorphOn H univ univ := hF.homeomorph_symm.trans hh
  have hFinvP : F.symm '' (P : Set E) = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hFP _).mp (by rwa [F.apply_symm_apply])
    · intro hx
      exact ⟨F x, (hFP x).mpr hx, F.symm_apply_apply x⟩
  refine ⟨H, hH, ?_, ?_, ?_, ?_⟩
  · change (h ∘ F.symm) '' (P : Set E) = h '' P
    rw [image_comp, hFinvP]
  · intro x
    change ℓ (h (F.symm x)) = ℓ x
    rw [← hFℓ, F.apply_symm_apply]
  · intro x
    have hmx : m (F.symm x) = m x := by
      rw [← hFm (F.symm x), F.apply_symm_apply]
    change (m (h (F.symm x)) = 0 ↔ m x = 0) ∧ (0 ≤ m (h (F.symm x)) ↔ 0 ≤ m x)
    simpa only [hmx] using hm (F.symm x)
  · intro x hax
    have hFx : F x = x := by
      change x + ℓ (a x) • d = x
      rw [hax, map_zero, zero_smul, add_zero]
    change h (F.symm x) = x
    have hFinv : F.symm x = x := by rw [← hFx, F.symm_apply_apply, hFx]
    rw [hFinv, hformula, hax, add_zero]

private theorem crossing_of_small_displacement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) (ℓ : E →L[ℝ] ℝ)
    (hP : Module.finrank ℝ P = 2) (hdim : Module.finrank ℝ E = 3) {d : E}
    (hd : d ∈ P) (hℓd : ℓ d = 1)
    {a : E → E} (ha : IsPiecewiseAffineOn a univ) {k : NNReal}
    (halip : LipschitzWith k a) (hk : (‖ℓ‖₊ * k) * ‖d‖₊ < 1)
    (h : E ≃ₜ E) (hh : IsPLHomeomorphOn h univ univ)
    (hformula : ∀ x, h x = x + a x) :
    ∀ y ∈ h '' (P : Set E) ∩ (LinearMap.ker ℓ.toLinearMap : Set E),
      HasPLCrossingAt (h '' (P : Set E)) (LinearMap.ker ℓ.toLinearMap) y := by
  obtain ⟨H, hH, hHP, hHℓ, -, -⟩ :=
    exists_homeomorph_adjust_displacement_preserving_halfSpace P ℓ 0 hd hℓd rfl
      ha halip hk h hh hformula (fun _ => ⟨Iff.rfl, Iff.rfl⟩)
  have hHQ : H '' (LinearMap.ker ℓ.toLinearMap : Set E) = LinearMap.ker ℓ.toLinearMap := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change ℓ (H z) = 0
      rw [hHℓ]
      exact hz
    · intro hx
      refine ⟨H.symm x, ?_, H.apply_symm_apply x⟩
      change ℓ (H.symm x) = 0
      rw [← hHℓ, H.apply_symm_apply]
      exact hx
  intro y hy
  have hxP : H.symm y ∈ P := by
    obtain ⟨z, hz, heq⟩ := hHP.symm ▸ hy.1
    rwa [← heq, H.symm_apply_apply]
  have hxQ : ℓ (H.symm y) = 0 := by
    rw [← hHℓ, H.apply_symm_apply]
    exact hy.2
  have hc : HasPLCrossingAt (P : Set E) (LinearMap.ker ℓ.toLinearMap) (H.symm y) := by
    apply (hasPLCrossingAt_affineSubspace_fiber P hP hdim ℓ.toLinearMap hd
      (by change ℓ d ≠ 0; rw [hℓd]; exact one_ne_zero) (H.symm y)).congr
    · exact Filter.Eventually.of_forall fun z => P.sub_mem_iff_left hxP
    · exact Filter.Eventually.of_forall fun z => by
        change ℓ z = ℓ (H.symm y) ↔ ℓ z = 0
        rw [hxQ]
  have hc' := hc.image_homeomorph H hH
  rwa [hHP, hHQ, H.apply_symm_apply] at hc'

private theorem exists_homeomorph_generalPosition_fixing_flat_core
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) {U V Z : Set E}
    (hU : IsOpen U) (hKU : K.space ⊆ U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hZ : IsCompact Z) (hZV : Z ⊆ V) (P : Submodule ℝ E) (ℓ : E →L[ℝ] ℝ)
    (hP : Module.finrank ℝ P = 2) {d : E} (hd : d ∈ P) (hℓd : ℓ d = 1)
    (hflatK : ∀ z ∈ V, z ∈ K.space ↔ z ∈ P)
    (hflatL : ∀ z ∈ V, z ∈ L.space ↔ ℓ z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : Set E) (h : E ≃ₜ E), IsPolyhedron Q ∧ Z ⊆ interior Q ∧ Q ⊆ V ∧
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧
      EqOn h id Uᶜ ∧ EqOn h id Q ∧
      ∀ x ∈ h '' K.space ∩ L.space, HasPLCrossingAt (h '' K.space) L.space x := by
  obtain ⟨Q, hQ, hZQ, hQV⟩ := exists_isPolyhedron_neighborhood hZ hV hZV
  let c : ℝ := ‖ℓ‖ * ‖d‖ + 1
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨j, k, hklip, hkc, -, hj, hclose, hzero, hfix, hcross⟩ :=
    exists_small_homeomorph_generalPosition_off_polyhedron_with_lipschitz_displacement K L
      hK hL hdim hQ hU hKU (hQV.trans hVU) hε
      (show 0 < 1 / (2 * c) by positivity)
  let h : E ≃ₜ E :=
    (Homeomorph.Set.univ _).symm.trans (hj.homeomorph.trans (Homeomorph.Set.univ _))
  have hh : IsPLHomeomorphOn h univ univ := hj
  let a : E → E := fun x => h x - x
  have ha : IsPiecewiseAffineOn a univ := by
    have hn := isPiecewiseAffineOn_of_affine (-(AffineMap.id ℝ E)) isOpen_univ
    simpa only [a, sub_eq_add_neg, AffineMap.coe_neg, Pi.neg_apply, AffineMap.id_apply] using
      hh.isPiecewiseAffineOn.add hn
  have hk : (‖ℓ‖₊ * k) * ‖d‖₊ < 1 := by
    have hbound := (lt_div_iff₀ (show 0 < 2 * c by positivity)).mp hkc
    have hnormle : ‖ℓ‖ * ‖d‖ ≤ c := le_add_of_nonneg_right zero_le_one
    change ‖ℓ‖ * (k : ℝ) * ‖d‖ < 1
    calc ‖ℓ‖ * (k : ℝ) * ‖d‖ = (k : ℝ) * (‖ℓ‖ * ‖d‖) := by ring
      _ ≤ (k : ℝ) * c := mul_le_mul_of_nonneg_left hnormle k.property
      _ < 1 := by nlinarith
  have hmodel := crossing_of_small_displacement P ℓ hP hdim hd hℓd ha hklip hk h hh
    (fun x => by dsimp only [a]; abel)
  have hmem (T : Set E) (z : E) : z ∈ h '' T ↔ h.symm z ∈ T := by
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [h.symm_apply_apply] using hw
    · exact fun hz => ⟨h.symm z, hz, h.apply_symm_apply z⟩
  refine ⟨Q, h, hQ, hZQ, hQV, hh, hclose, hzero, hfix, fun x hx => ?_⟩
  by_cases hxQ : x ∈ Q
  · have hxV : x ∈ V := hQV hxQ
    have hinvx : h.symm x = x := by
      apply h.injective
      exact (h.apply_symm_apply x).trans (hfix hxQ).symm
    have hpreV : ∀ᶠ z in 𝓝 x, h.symm z ∈ V :=
      h.symm.continuous.continuousAt.preimage_mem_nhds
        (hV.mem_nhds (hinvx.symm ▸ hxV))
    have hxP : x ∈ h '' (P : Set E) := by
      rw [hmem]
      exact (hflatK _ (hinvx.symm ▸ hxV)).mp ((hmem K.space x).mp hx.1)
    apply (hmodel x ⟨hxP, (hflatL x hxV).mp hx.2⟩).congr
    · filter_upwards [hpreV] with z hz
      rw [hmem, hmem]
      exact (hflatK _ hz).symm
    · filter_upwards [hV.mem_nhds hxV] with z hz
      exact (hflatL z hz).symm
  · exact hcross x hx hxQ

private theorem boundary_crossing_of_submodules
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P Q : Submodule ℝ E) (m : E →ₗ[ℝ] ℝ)
    (hP : Module.finrank ℝ P = 2) (hQ : Module.finrank ℝ Q = 2)
    (hI : Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1) (hPQ : P ⊔ Q = ⊤)
    (hu : ∃ u ∈ P ⊓ Q, m u = 1) {x : E} (hxP : x ∈ P) (hxQ : x ∈ Q)
    (hmx : m x = 0) :
    HasPLBoundaryCrossingAt {y | 0 ≤ m y}
      ((P : Set E) ∩ {y | 0 ≤ m y}) ((Q : Set E) ∩ {y | 0 ≤ m y}) x := by
  have ht : IsPLHomeomorphOn (fun y : E => y - x) univ univ := by
    simpa only [sub_eq_add_neg] using isPLHomeomorphOn_add_const (-x)
  refine ⟨univ, univ, fun y => y - x, P, Q, m, isOpen_univ, isOpen_univ, mem_univ x,
    ht, sub_self x, hP, hQ, hI, hPQ, hu, Filter.Eventually.of_forall fun y => ?_⟩
  have hPy : y - x ∈ P ↔ y ∈ P := P.sub_mem_iff_left hxP
  have hQy : y - x ∈ Q ↔ y ∈ Q := Q.sub_mem_iff_left hxQ
  simp only [mem_ofPred_eq, mem_inter_iff, SetLike.mem_coe, map_sub, hmx, sub_zero, hPy, hQy,
    and_self]

private theorem crossing_of_submodules_in_open_halfSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P Q : Submodule ℝ E) (m : E →L[ℝ] ℝ)
    (hP : Module.finrank ℝ P = 2) (hQ : Module.finrank ℝ Q = 2)
    (hI : Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1) (hPQ : P ⊔ Q = ⊤)
    {x : E} (hxP : x ∈ P) (hxQ : x ∈ Q) (hmx : 0 < m x) :
    HasPLCrossingAt ((P : Set E) ∩ {y | 0 ≤ m y})
      ((Q : Set E) ∩ {y | 0 ≤ m y}) x := by
  have ht : IsPLHomeomorphOn (fun y : E => y - x) univ univ := by
    simpa only [sub_eq_add_neg] using isPLHomeomorphOn_add_const (-x)
  refine ⟨univ, univ, fun y => y - x, P, Q, 0, 0,
    isOpen_univ, isOpen_univ, mem_univ x, ht, sub_self x,
    hP, hQ, hI, hPQ, Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_⟩
  filter_upwards [(isOpen_lt continuous_const m.continuous).mem_nhds hmx] with y hy
  have hPy : y - x ∈ P ↔ y ∈ P := P.sub_mem_iff_left hxP
  have hQy : y - x ∈ Q ↔ y ∈ Q := Q.sub_mem_iff_left hxQ
  simp only [mem_inter_iff, SetLike.mem_coe, mem_ofPred_eq, hPy, hQy, LinearMap.zero_apply,
    le_refl, and_true, hy.le]

private theorem crossing_of_lipschitz_displacement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) (ℓ m : E →L[ℝ] ℝ)
    (hP : Module.finrank ℝ P = 2) (hQ : Module.finrank ℝ (LinearMap.ker ℓ.toLinearMap) = 2)
    (hI : Module.finrank ℝ (P ⊓ LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) = 1)
    (hPQ : P ⊔ LinearMap.ker ℓ.toLinearMap = ⊤)
    (hu : ∃ u ∈ P ⊓ LinearMap.ker ℓ.toLinearMap, m u = 1) {d : E}
    (hd : d ∈ P) (hℓd : ℓ d = 1) (hmd : m d = 0)
    {a : E → E} (ha : IsPiecewiseAffineOn a univ) {k : NNReal}
    (halip : LipschitzWith k a) (hk : (‖ℓ‖₊ * k) * ‖d‖₊ < 1)
    (h : E ≃ₜ E) (hh : IsPLHomeomorphOn h univ univ)
    (hformula : ∀ x, h x = x + a x)
    (hm : ∀ x, (m (h x) = 0 ↔ m x = 0) ∧ (0 ≤ m (h x) ↔ 0 ≤ m x)) :
    ∀ y ∈ h '' ((P : Set E) ∩ {x | 0 ≤ m x}) ∩
        (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x}),
      (m y = 0 ∧ HasPLBoundaryCrossingAt {x | 0 ≤ m x}
        (h '' ((P : Set E) ∩ {x | 0 ≤ m x}))
        (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x}) y) ∨
      (0 < m y ∧ HasPLCrossingAt (h '' ((P : Set E) ∩ {x | 0 ≤ m x}))
        (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x}) y) := by
  obtain ⟨H, hH, hHP, hHℓ, hHm, -⟩ :=
    exists_homeomorph_adjust_displacement_preserving_halfSpace P ℓ m hd hℓd hmd
      ha halip hk h hh hformula hm
  have hHC : H '' {x | 0 ≤ m x} = {x | 0 ≤ m x} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hHm z).2.mpr hz
    · intro hx
      exact ⟨H.symm x, (hHm _).2.mp (by rwa [H.apply_symm_apply]), H.apply_symm_apply x⟩
  have hhC : h '' {x | 0 ≤ m x} = {x | 0 ≤ m x} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hm z).2.mpr hz
    · intro hx
      exact ⟨h.symm x, (hm _).2.mp (by rwa [h.apply_symm_apply]), h.apply_symm_apply x⟩
  have hHQ : H '' ((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) =
      LinearMap.ker ℓ.toLinearMap := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change ℓ (H z) = 0
      rw [hHℓ]
      exact hz
    · intro hx
      refine ⟨H.symm x, ?_, H.apply_symm_apply x⟩
      change ℓ (H.symm x) = 0
      rw [← hHℓ, H.apply_symm_apply]
      exact hx
  have hHA : H '' ((P : Set E) ∩ {x | 0 ≤ m x}) =
      h '' ((P : Set E) ∩ {x | 0 ≤ m x}) := by
    rw [image_inter H.injective, hHP, hHC, image_inter h.injective, hhC]
  have hHB : H '' (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x}) =
      (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x}) := by
    rw [image_inter H.injective, hHQ, hHC]
  intro y hy
  have hxA : H.symm y ∈ (P : Set E) ∩ {x | 0 ≤ m x} := by
    have hyA : y ∈ H '' ((P : Set E) ∩ {x | 0 ≤ m x}) := hHA.symm ▸ hy.1
    obtain ⟨z, hz, rfl⟩ := hyA
    simpa only [H.symm_apply_apply] using hz
  have hxB : H.symm y ∈
      ((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x} := by
    have hyB : y ∈ H ''
        (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x}) :=
      hHB.symm ▸ hy.2
    obtain ⟨z, hz, rfl⟩ := hyB
    simpa only [H.symm_apply_apply] using hz
  by_cases hmy : m y = 0
  · have hmx : m (H.symm y) = 0 := (hHm _).1.mp (by rwa [H.apply_symm_apply])
    have hc := (boundary_crossing_of_submodules P (LinearMap.ker ℓ.toLinearMap) m.toLinearMap
      hP hQ hI hPQ hu hxA.1 hxB.1 hmx).image_openPartialHomeomorph
      H.toOpenPartialHomeomorph hH.isPiecewiseAffineOn (mem_univ _)
    change HasPLBoundaryCrossingAt (H '' (univ ∩ {x | 0 ≤ m x}))
      (H '' (univ ∩ ((P : Set E) ∩ {x | 0 ≤ m x})))
      (H '' (univ ∩ (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x})))
      (H (H.symm y)) at hc
    simp only [univ_inter, H.apply_symm_apply, hHC, hHA, hHB] at hc
    exact Or.inl ⟨hmy, hc⟩
  · have hmx : 0 < m (H.symm y) := lt_of_le_of_ne hxA.2
      (fun heq => hmy (by simpa only [H.apply_symm_apply] using (hHm _).1.mpr heq.symm))
    have hc := (crossing_of_submodules_in_open_halfSpace P (LinearMap.ker ℓ.toLinearMap) m
      hP hQ hI hPQ hxA.1 hxB.1 hmx).image_homeomorph H hH
    rw [hHA, hHB, H.apply_symm_apply] at hc
    exact Or.inr ⟨lt_of_le_of_ne hy.2.2 (Ne.symm hmy), hc⟩

private theorem exists_small_displacement_preserving_crossing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) (ℓ m : E →L[ℝ] ℝ)
    (hP : Module.finrank ℝ P = 2) (hQ : Module.finrank ℝ (LinearMap.ker ℓ.toLinearMap) = 2)
    (hI : Module.finrank ℝ (P ⊓ LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) = 1)
    (hPQ : P ⊔ LinearMap.ker ℓ.toLinearMap = ⊤)
    (hu : ∃ u ∈ P ⊓ LinearMap.ker ℓ.toLinearMap, m u = 1) {d : E}
    (hd : d ∈ P) (hℓd : ℓ d = 1) (hmd : m d = 0)
    {a : E → E} (ha : IsPiecewiseAffineOn a univ) {k : NNReal}
    (halip : LipschitzWith k a) (hma : ∀ x, m (a x) = 0)
    {M : ℝ} (hM : ∀ x, ‖a x‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : ℝ) (h : E ≃ₜ E), 0 < t ∧ t * (k : ℝ) < 1 ∧
      ‖ℓ‖ * (t * (k : ℝ)) * ‖d‖ < 1 ∧ IsPLHomeomorphOn h univ univ ∧
      (∀ x, h x = x + t • a x) ∧ (∀ x, dist (h x) x < ε) ∧
      (∀ x, m (h x) = m x) ∧
      ∀ y ∈ h '' ((P : Set E) ∩ {x | 0 ≤ m x}) ∩
          (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x}),
        (m y = 0 ∧ HasPLBoundaryCrossingAt {x | 0 ≤ m x}
          (h '' ((P : Set E) ∩ {x | 0 ≤ m x}))
          (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x}) y) ∨
        (0 < m y ∧ HasPLCrossingAt (h '' ((P : Set E) ∩ {x | 0 ≤ m x}))
          (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ E) : Set E) ∩ {x | 0 ≤ m x}) y) := by
  have hM0 : 0 ≤ M := (norm_nonneg (a 0)).trans (hM 0)
  let C : ℝ := (k : ℝ) * (1 + ‖ℓ‖ * ‖d‖)
  have hC0 : 0 ≤ C := mul_nonneg k.property (by positivity)
  obtain ⟨δ, hδ, hδC⟩ := exists_pos_mul_lt (a := (1 : ℝ)) zero_lt_one C
  let t : ℝ := min (ε / (M + 1)) (δ / 2)
  have ht : 0 < t := lt_min (div_pos hε (by positivity)) (half_pos hδ)
  have htδ : t < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have htC : t * C < 1 := by
    calc t * C = C * t := mul_comm _ _
      _ ≤ C * δ := mul_le_mul_of_nonneg_left htδ.le hC0
      _ < 1 := hδC
  have htM : t * M < ε := by
    have h := (le_div_iff₀ (show 0 < M + 1 by positivity)).mp
      (min_le_left (ε / (M + 1)) (δ / 2))
    change t * (M + 1) ≤ ε at h
    nlinarith
  let b : E → E := fun x => t • a x
  let kt : NNReal := ⟨t, ht.le⟩ * k
  have hb : IsPiecewiseAffineOn b univ :=
    ha.affine_comp (t • (LinearMap.id : E →ₗ[ℝ] E)).toAffineMap
  have hblip : LipschitzWith kt b := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (t • a x) (t • a y) ≤ (t * (k : ℝ)) * dist x y
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left (halip.dist_le_mul x y) ht.le).trans_eq
      (mul_assoc _ _ _).symm
  have hkt : kt < 1 := by
    change t * (k : ℝ) < 1
    apply lt_of_le_of_lt _ htC
    calc t * (k : ℝ) = (t * (k : ℝ)) * 1 := (mul_one _).symm
      _ ≤ (t * (k : ℝ)) * (1 + ‖ℓ‖ * ‖d‖) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
          (mul_nonneg (norm_nonneg ℓ) (norm_nonneg d))) (mul_nonneg ht.le k.property)
      _ = t * C := by dsimp only [C]; ring
  have hktℓ : (‖ℓ‖₊ * kt) * ‖d‖₊ < 1 := by
    change ‖ℓ‖ * (t * (k : ℝ)) * ‖d‖ < 1
    apply lt_of_le_of_lt _ htC
    calc ‖ℓ‖ * (t * (k : ℝ)) * ‖d‖ = (t * (k : ℝ)) * (‖ℓ‖ * ‖d‖) := by ring
      _ ≤ (t * (k : ℝ)) * (1 + ‖ℓ‖ * ‖d‖) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one)
          (mul_nonneg ht.le k.property)
      _ = t * C := by dsimp only [C]; ring
  have hh := isPLHomeomorphOn_id_add_of_lipschitz hb hblip hkt
  let h : E ≃ₜ E :=
    (Homeomorph.Set.univ E).symm.trans (hh.homeomorph.trans (Homeomorph.Set.univ E))
  have hheight (x : E) : m (h x) = m x := by
    change m (x + t • a x) = m x
    rw [map_add, map_smul, hma, smul_zero, add_zero]
  refine ⟨t, h, ht, hkt, hktℓ, hh, fun _ => rfl, ?_, hheight, ?_⟩
  · intro x
    change dist (x + t • a x) x < ε
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left (hM x) ht.le).trans_lt htM
  · exact crossing_of_lipschitz_displacement P ℓ m hP hQ hI hPQ hu hd hℓd hmd
      hb hblip hktℓ h hh (fun _ => rfl) (fun x => by rw [hheight]; exact ⟨Iff.rfl, Iff.rfl⟩)
private theorem exists_singularTwoCell_preserving_boundary_crossings_of_flat_sheets
    (D : SingularTwoCell (EuclideanSpace ℝ (Fin 3)))
    {P Q A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hPQ : P ∪ Q = D.domain) (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hA : IsPolyhedron A) (hB : IsPolyhedron B) (hAP : A ⊆ P) (hBQ : B ⊆ Q)
    (hAB : Disjoint A B) (hinjP : InjOn D P)
    (hfA : IsPLHomeomorphOn D A (D '' A)) (hfB : IsPLHomeomorphOn D B (D '' B))
    (hloc : IsLocallyInjective (D.domain.domRestrict D))
    (hcard : ∀ z, (D.domain ∩ D ⁻¹' {z}).encard ≤ 2)
    {U C V W : Set (EuclideanSpace ℝ (Fin 3))}
    (hVU : V ⊆ U) (hW : IsOpen W) (hWV : W ⊆ V)
    (hseam : ∀ x ∈ P ∩ Q, D x ∉ closure U)
    (hinjQ : InjOn D (Q ∩ D ⁻¹' U))
    (hcover : ∀ z ∈ U, D.domain ∩ D ⁻¹' {z} ⊆ A ∪ B)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (ℓ m : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hS : Module.finrank ℝ S = 2)
    (hu : ∃ u ∈ S ⊓ LinearMap.ker ℓ.toLinearMap, m u = 1)
    {d : EuclideanSpace ℝ (Fin 3)} (hd : d ∈ S) (hℓd : ℓ d = 1) (hmd : m d = 0)
    (hflatA : ∀ z ∈ V, z ∈ D '' A ↔ z ∈ S ∧ 0 ≤ m z)
    (hflatB : ∀ z ∈ V, z ∈ D '' B ↔ ℓ z = 0 ∧ 0 ≤ m z)
    (hC : ∀ z ∈ U, z ∈ C ↔ 0 ≤ m z)
    (hBd : ∀ z ∈ U, z ∈ frontier C ↔ m z = 0)
    (hmap : MapsTo D D.domain C)
    (hproper : D.domain ∩ D ⁻¹' frontier C = frontier D.domain)
    {a : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (ha : IsPiecewiseAffineOn a univ) {k : NNReal} (halip : LipschitzWith k a)
    (hk : k < 1) (hkℓ : (‖ℓ‖₊ * k) * ‖d‖₊ < 1)
    (hzero : EqOn a (fun _ => 0) Uᶜ) (hplane : ∀ z, m z = 0 → m (a z) = 0)
    (h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (hh : IsPLHomeomorphOn h univ univ) (hformula : ∀ z, h z = z + a z)
    (hheight : ∀ z, (m (h z) = 0 ↔ m z = 0) ∧ (0 ≤ m (h z) ↔ 0 ≤ m z))
    (hpreV : ∀ z ∈ W, h.symm z ∈ V) {ε : ℝ} (hε : 0 < ε)
    (hclose : ∀ z, dist (h z) z < ε) :
    ∃ F : SingularTwoCell (EuclideanSpace ℝ (Fin 3)), F.domain = D.domain ∧
      EqOn F (h ∘ D) P ∧ EqOn F D Q ∧ EqOn F D Pᶜ ∧
      (∀ x, dist (F x) (D x) < ε) ∧ MapsTo F F.domain C ∧
      F.domain ∩ F ⁻¹' frontier C = frontier F.domain ∧
      F '' F.domain ∩ frontier C = range F.boundary ∧
      IsLocallyInjective (F.domain.domRestrict F) ∧
      (∀ z, (F.domain ∩ F ⁻¹' {z}).encard ≤ 2) ∧
      (∀ z ∉ U, F ⁻¹' {z} = D ⁻¹' {z}) ∧
      (∀ z ∈ W ∩ doublePointSet F F.domain,
        (z ∈ frontier C ∧ HasPLBoundaryDoubleCrossingAt F F.domain C z) ∨
        (z ∉ frontier C ∧ HasPLDoubleCrossingAt F F.domain z)) ∧
      ∃ H : ContinuousMap (unitInterval × frontier D.domain) (EuclideanSpace ℝ (Fin 3)),
        (∀ x, H (0, x) = D x) ∧ (∀ x, H (1, x) = F x) ∧
        ∀ s x, dist (H (s, x)) (D x) < ε ∧ H (s, x) ∈ frontier C ∧
          (D x ∉ U → H (s, x) = D x) := by
  classical
  have hWU : W ⊆ U := hWV.trans hVU
  have hℓ : ℓ.toLinearMap ≠ 0 := by
    intro heq
    have hd0 : ℓ d = 0 := congrArg (fun f : _ →ₗ[ℝ] ℝ => f d) heq
    exact zero_ne_one (hd0.symm.trans hℓd)
  have hT : Module.finrank ℝ (LinearMap.ker ℓ.toLinearMap) = 2 := by
    have hr := LinearMap.finrank_range_add_finrank_ker ℓ.toLinearMap
    rw [LinearMap.range_eq_top.mpr (LinearMap.surjective_of_ne_zero hℓ),
      finrank_top, Module.finrank_self] at hr
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    omega
  have hST : S ⊔ LinearMap.ker ℓ.toLinearMap = ⊤ := by
    apply top_unique
    intro z _
    have hker : z - ℓ z • d ∈ LinearMap.ker ℓ.toLinearMap := by
      change ℓ (z - ℓ z • d) = 0
      rw [map_sub, map_smul, hℓd, smul_eq_mul, mul_one, sub_self]
    have hz := Submodule.add_mem (S ⊔ LinearMap.ker ℓ.toLinearMap)
      (Submodule.mem_sup_left (S.smul_mem (ℓ z) hd)) (Submodule.mem_sup_right hker)
    have heq : ℓ z • d + (z - ℓ z • d) = z := by abel
    exact heq ▸ hz
  have hI : Module.finrank ℝ (S ⊓ LinearMap.ker ℓ.toLinearMap :
      Submodule ℝ (EuclideanSpace ℝ (Fin 3))) = 1 := by
    have hr := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker ℓ.toLinearMap)
    rw [hST, finrank_top, hS, hT] at hr
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    omega
  have hcross := crossing_of_lipschitz_displacement S ℓ m hS hT hI hST hu hd hℓd hmd
    ha halip hkℓ h hh hformula hheight
  have hfix : EqOn h id Uᶜ := by
    intro z hz
    rw [hformula, hzero hz, add_zero]
    rfl
  have hpre (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ U) : h.symm z ∈ U := by
    by_contra hnot
    have heq : z = h.symm z := (h.apply_symm_apply z).symm.trans (hfix hnot)
    exact hnot (heq ▸ hz)
  have hmaps : MapsTo h U U := by
    intro z hz
    by_contra hnot
    have heq : h z = z := h.injective (hfix hnot)
    exact hnot (heq.symm ▸ hz)
  have hpres (z : EuclideanSpace ℝ (Fin 3)) :
      (h z ∈ C ↔ z ∈ C) ∧ (h z ∈ frontier C ↔ z ∈ frontier C) := by
    by_cases hz : z ∈ U
    · rw [hC _ (hmaps hz), hC _ hz, hBd _ (hmaps hz), hBd _ hz]
      exact ⟨(hheight z).2, (hheight z).1⟩
    · rw [hfix hz]
      exact ⟨Iff.rfl, Iff.rfl⟩
  have hhPL : IsPL 3 3 h := fun z =>
    ⟨h.continuous.continuousAt.continuousWithinAt, hh.isPiecewiseAffineOn z (mem_univ z)⟩
  have hf : IsPLOn 2 3 D (P ∪ Q) := hPQ.symm ▸ D.isPLOn
  have hlocPQ : IsLocallyInjective ((P ∪ Q).domRestrict D) := hPQ.symm ▸ hloc
  have hcardPQ : ∀ z, ((P ∪ Q) ∩ D ⁻¹' {z}).encard ≤ 2 := hPQ.symm ▸ hcard
  obtain ⟨g, hg, hgloc, hgcard, hgP, hgQ, hgOff, hgfiber⟩ :=
    exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective hf hP hQ hlocPQ hcardPQ
      hinjP hhPL h.injective hfix hseam hinjQ
  rw [hPQ] at hg hgloc hgcard
  have hPK : P ⊆ D.domain := hPQ ▸ subset_union_left
  have hQK : Q ⊆ D.domain := hPQ ▸ subset_union_right
  have hAK : A ⊆ D.domain := hAP.trans hPK
  have hBK : B ⊆ D.domain := hBQ.trans hQK
  have hgAeq : EqOn g (h ∘ D) A := hgP.mono hAP
  have hgBeq : EqOn g D B := hgQ.mono hBQ
  have hgAimage : g '' A = h '' (D '' A) := by
    rw [← image_comp]
    exact hgAeq.image_eq
  have hgBimage : g '' B = D '' B := hgBeq.image_eq
  have hgA : IsPLHomeomorphOn g A (g '' A) := by
    rw [hgAimage]
    have hDA := hA.image_of_isPiecewiseAffineOn hfA.isPiecewiseAffineOn hfA.bijOn.injOn
    exact (hfA.trans (hh.restrict hDA (subset_univ _))).congr hgAeq
  have hgB : IsPLHomeomorphOn g B (g '' B) := by
    rw [hgBimage]
    exact hfB.congr hgBeq
  have hgcover : ∀ z ∈ U, D.domain ∩ g ⁻¹' {z} ⊆ A ∪ B := by
    intro z hz x hx
    by_cases hxP : x ∈ P
    · have hDx : D x = h.symm z := by
        apply h.injective
        rw [h.apply_symm_apply]
        exact (hgP hxP).symm.trans hx.2
      rcases hcover (h.symm z) (hpre z hz) ⟨hx.1, hDx⟩ with hxA | hxB
      · exact Or.inl hxA
      · exact False.elim (hseam x ⟨hxP, hBQ hxB⟩
          (subset_closure (hDx.symm ▸ hpre z hz)))
    · have hDx : D x = z := (hgOff hxP).symm.trans hx.2
      exact Or.inr ((hcover z hz ⟨hx.1, hDx⟩).resolve_left (fun hxA => hxP (hAP hxA)))
  have hmem (T : Set (EuclideanSpace ℝ (Fin 3))) (z : EuclideanSpace ℝ (Fin 3)) :
      z ∈ h '' T ↔ h.symm z ∈ T := by
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [h.symm_apply_apply] using hw
    · intro hz
      exact ⟨h.symm z, hz, h.apply_symm_apply z⟩
  have hmodelA : ∀ z ∈ W, z ∈ g '' A ↔ z ∈ h '' ((S : Set _) ∩ {w | 0 ≤ m w}) := by
    intro z hz
    rw [hgAimage, hmem, hmem]
    exact hflatA _ (hpreV z hz)
  have hmodelB : ∀ z ∈ W, z ∈ g '' B ↔ ℓ z = 0 ∧ 0 ≤ m z := by
    intro z hz
    rw [hgBimage]
    exact hflatB z (hWV hz)
  have hgpres (x : EuclideanSpace ℝ (Fin 2)) :
      (g x ∈ C ↔ D x ∈ C) ∧ (g x ∈ frontier C ↔ D x ∈ frontier C) := by
    by_cases hxP : x ∈ P
    · rw [hgP hxP]
      exact hpres (D x)
    · rw [hgOff hxP]
      exact ⟨Iff.rfl, Iff.rfl⟩
  have hgproper : D.domain ∩ g ⁻¹' frontier C = frontier D.domain := by
    rw [← hproper]
    ext x
    exact and_congr_right fun _ => (hgpres x).2
  let F : SingularTwoCell (EuclideanSpace ℝ (Fin 3)) :=
    { domain := D.domain
      isPLBall_domain := D.isPLBall_domain
      toFun := g
      isPLOn := hg }
  have hgclose (x : EuclideanSpace ℝ (Fin 2)) : dist (g x) (D x) < ε := by
    by_cases hxP : x ∈ P
    · rw [hgP hxP]
      exact hclose (D x)
    · rw [hgOff hxP, dist_self]
      exact hε
  have hinter : F '' F.domain ∩ frontier C = range F.boundary := by
    rw [← image_inter_preimage]
    change g '' (D.domain ∩ g ⁻¹' frontier C) = range F.boundary
    rw [hgproper]
    ext z
    exact ⟨fun ⟨x, hx, hxz⟩ => ⟨⟨x, hx⟩, hxz⟩,
      fun ⟨x, hxz⟩ => ⟨x, x.2, hxz⟩⟩
  refine ⟨F, rfl, hgP, hgQ, hgOff, hgclose,
    fun x hx => (hgpres x).1.mpr (hmap hx), hgproper, hinter, hgloc, hgcard,
    hgfiber, ?_, ?_⟩
  · intro z hz
    have hzAB := (mem_doublePointSet_iff_mem_image_inter_of_injOn g hAK hBK hAB
      hgA.bijOn.injOn hgB.bijOn.injOn (hgcover z (hWU hz.1))).mp hz.2
    have hnear : ∀ᶠ w in 𝓝 z, D.domain ∩ g ⁻¹' {w} ⊆ A ∪ B :=
      Filter.Eventually.mono (hW.mem_nhds hz.1) fun w hw => hgcover w (hWU hw)
    have hAnear : ∀ᶠ w in 𝓝 z, w ∈ h '' ((S : Set _) ∩ {v | 0 ≤ m v}) ↔ w ∈ g '' A :=
      Filter.Eventually.mono (hW.mem_nhds hz.1) fun w hw => (hmodelA w hw).symm
    have hBnear : ∀ᶠ w in 𝓝 z,
        w ∈ (((LinearMap.ker ℓ.toLinearMap : Submodule ℝ _) : Set _) ∩ {v | 0 ≤ m v}) ↔
          w ∈ g '' B :=
      Filter.Eventually.mono (hW.mem_nhds hz.1) fun w hw => (hmodelB w hw).symm
    rcases hcross z ⟨(hmodelA z hz.1).mp hzAB.1, (hmodelB z hz.1).mp hzAB.2⟩ with
      ⟨hzeroz, hcz⟩ | ⟨hposz, hcz⟩
    · refine Or.inl ⟨(hBd z (hWU hz.1)).mpr hzeroz, ?_⟩
      have hCnear : ∀ᶠ w in 𝓝 z, w ∈ {v | 0 ≤ m v} ↔ w ∈ C :=
        Filter.Eventually.mono (hW.mem_nhds hz.1) fun w hw => (hC w (hWU hw)).symm
      exact hasPLBoundaryDoubleCrossingAt_of_crossing_and_eventually_fiber_subset
        F.continuousOn hAK hBK hA.isClosed hB.isClosed hAB hgA hgB hz.2
        (hcz.congr hCnear hAnear hBnear) hnear
    · refine Or.inr ⟨fun hzBd => hposz.ne' ((hBd z (hWU hz.1)).mp hzBd), ?_⟩
      exact hasPLDoubleCrossingAt_of_crossing_and_eventually_fiber_subset F.continuousOn
        hAK hBK hA.isClosed hB.isClosed hAB hgA hgB hz.2 (hcz.congr hAnear hBnear) hnear
  · have hcontD : Continuous (fun x : frontier D.domain => D x) := D.boundary.continuous
    have hcontg : Continuous (fun x : frontier D.domain => g x) :=
      (F.continuousOn.mono D.frontier_subset_domain).domRestrict
    let H : ContinuousMap (unitInterval × frontier D.domain) (EuclideanSpace ℝ (Fin 3)) :=
      ⟨fun z => D z.2 + (z.1 : ℝ) • (g z.2 - D z.2),
        (hcontD.comp continuous_snd).add
          ((continuous_subtype_val.comp continuous_fst).smul
            ((hcontg.comp continuous_snd).sub (hcontD.comp continuous_snd)))⟩
    refine ⟨H, fun x => by simp [H], fun x => by simp [H, F], ?_⟩
    intro s x
    have hdist : dist (H (s, x)) (D x) < ε := by
      calc dist (H (s, x)) (D x) = (s : ℝ) * dist (g x) (D x) := by
            simp only [H, ContinuousMap.coe_mk, dist_eq_norm, add_sub_cancel_left,
              norm_smul, Real.norm_eq_abs, abs_of_nonneg s.property.1]
        _ ≤ dist (g x) (D x) := mul_le_of_le_one_left dist_nonneg s.property.2
        _ < ε := hgclose x
    have hDbd : D x ∈ frontier C := (hproper.superset x.property).2
    have hHfix (hxU : D x ∉ U) : H (s, x) = D x := by
      have hgeq : g x = D x := by
        by_cases hxP : (x : EuclideanSpace ℝ (Fin 2)) ∈ P
        · exact (hgP hxP).trans (hfix hxU)
        · exact hgOff hxP
      change D x + (s : ℝ) • (g x - D x) = D x
      rw [hgeq, sub_self, smul_zero, add_zero]
    refine ⟨hdist, ?_, hHfix⟩
    by_cases hxP : (x : EuclideanSpace ℝ (Fin 2)) ∈ P
    · by_cases hxU : D x ∈ U
      · let r : ℝ := s
        have hr : 0 ≤ r := s.property.1
        have hrk : r * (k : ℝ) < 1 :=
          (mul_le_of_le_one_left k.property s.property.2).trans_lt hk
        have hpa : IsPiecewiseAffineOn (fun z => r • a z) univ :=
          ha.affine_comp (r • (LinearMap.id : _ →ₗ[ℝ] _)).toAffineMap
        have hlipa : LipschitzWith (⟨r, hr⟩ * k) (fun z => r • a z) := by
          apply LipschitzWith.of_dist_le_mul
          intro z w
          change dist (r • a z) (r • a w) ≤ (r * (k : ℝ)) * dist z w
          rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hr]
          exact (mul_le_mul_of_nonneg_left (halip.dist_le_mul z w) hr).trans_eq
            (mul_assoc _ _ _).symm
        have hj := isPLHomeomorphOn_id_add_of_lipschitz hpa hlipa hrk
        have heq : H (s, x) = D x + r • a (D x) := by
          change D x + (s : ℝ) • (g x - D x) = _
          rw [hgP hxP, Function.comp_apply, hformula, add_sub_cancel_left]
        have hHU : H (s, x) ∈ U := by
          rw [heq]
          by_contra hnot
          have hself : (D x + r • a (D x)) + r • a (D x + r • a (D x)) =
              D x + r • a (D x) := by rw [hzero hnot, smul_zero, add_zero]
          have hident := hj.bijOn.injOn (mem_univ _) (mem_univ _) hself
          exact hnot (hident.symm ▸ hxU)
        apply (hBd _ hHU).mpr
        rw [heq, map_add, map_smul, hplane _ ((hBd _ hxU).mp hDbd), smul_zero, add_zero]
        exact (hBd _ hxU).mp hDbd
      · exact (hHfix hxU).symm ▸ hDbd
    · have hgeq : g x = D x := hgOff hxP
      have heq : H (s, x) = D x := by
        change D x + (s : ℝ) • (g x - D x) = D x
        rw [hgeq, sub_self, smul_zero, add_zero]
      exact heq.symm ▸ hDbd
open Classical in
theorem SingularTwoCell.exists_small_perturbation_preserving_boundary_crossings_of_flat_sheets
    (D : SingularTwoCell (EuclideanSpace ℝ (Fin 3)))
    {P Q A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hPQ : P ∪ Q = D.domain) (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hA : IsPolyhedron A) (hB : IsPolyhedron B) (hAP : A ⊆ P) (hBQ : B ⊆ Q)
    (hAB : Disjoint A B) (hinjP : InjOn D P)
    (hfA : IsPLHomeomorphOn D A (D '' A)) (hfB : IsPLHomeomorphOn D B (D '' B))
    (hloc : IsLocallyInjective (D.domain.domRestrict D))
    (hcard : ∀ z, (D.domain ∩ D ⁻¹' {z}).encard ≤ 2)
    {U C V Z : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hZ : IsCompact Z) (hZV : Z ⊆ V)
    (hseam : ∀ x ∈ P ∩ Q, D x ∉ closure U)
    (hinjQ : InjOn D (Q ∩ D ⁻¹' U))
    (hcover : ∀ z ∈ U, D.domain ∩ D ⁻¹' {z} ⊆ A ∪ B)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (ℓ m : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hS : Module.finrank ℝ S = 2)
    (hu : ∃ u ∈ S ⊓ LinearMap.ker ℓ.toLinearMap, m u = 1)
    {d : EuclideanSpace ℝ (Fin 3)} (hd : d ∈ S) (hℓd : ℓ d = 1) (hmd : m d = 0)
    (hflatA : ∀ z ∈ V, z ∈ D '' A ↔ z ∈ S ∧ 0 ≤ m z)
    (hflatB : ∀ z ∈ V, z ∈ D '' B ↔ ℓ z = 0 ∧ 0 ≤ m z)
    (hC : ∀ z ∈ U, z ∈ C ↔ 0 ≤ m z)
    (hBd : ∀ z ∈ U, z ∈ frontier C ↔ m z = 0)
    (hmap : MapsTo D D.domain C)
    (hproper : D.domain ∩ D ⁻¹' frontier C = frontier D.domain)
    {J : Set (EuclideanSpace ℝ (Fin 3))} (hJ : IsPolyhedron J) (hJU : J ⊆ U)
    {v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hv : IsPiecewiseAffineOn v J) (hmv : ∀ z ∈ J, m (v z) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin 3))) (t : ℝ)
      (F : SingularTwoCell (EuclideanSpace ℝ (Fin 3))),
      IsOpen W ∧ Z ⊆ W ∧ W ⊆ V ∧ 0 < t ∧ F.domain = D.domain ∧
      EqOn F (fun x => D x + t • v (D x)) (P ∩ D ⁻¹' J) ∧
      EqOn F D Q ∧ EqOn F D Pᶜ ∧
      (∀ x, dist (F x) (D x) < ε) ∧ MapsTo F F.domain C ∧
      F.domain ∩ F ⁻¹' frontier C = frontier F.domain ∧
      F '' F.domain ∩ frontier C = range F.boundary ∧
      IsLocallyInjective (F.domain.domRestrict F) ∧
      (∀ z, (F.domain ∩ F ⁻¹' {z}).encard ≤ 2) ∧
      (∀ z ∉ U, F ⁻¹' {z} = D ⁻¹' {z}) ∧
      (∀ z ∈ W ∩ doublePointSet F F.domain,
        (z ∈ frontier C ∧ HasPLBoundaryDoubleCrossingAt F F.domain C z) ∨
        (z ∉ frontier C ∧ HasPLDoubleCrossingAt F F.domain z)) ∧
      ∃ H : ContinuousMap (unitInterval × frontier D.domain) (EuclideanSpace ℝ (Fin 3)),
        (∀ x, H (0, x) = D x) ∧ (∀ x, H (1, x) = F x) ∧
        ∀ s x, dist (H (s, x)) (D x) < ε ∧ H (s, x) ∈ frontier C ∧
          (D x ∉ U → H (s, x) = D x) := by
  obtain ⟨r, hr, hrV⟩ := hZ.exists_cthickening_subset_open hV hZV
  let W := thickening (r / 2) Z
  have hW : IsOpen W := isOpen_thickening
  have hZW : Z ⊆ W := self_subset_thickening (half_pos hr) Z
  have hWV : W ⊆ V := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
    exact hrV (thickening_subset_cthickening r Z
      (mem_thickening_iff.mpr ⟨w, hw, hzw.trans (half_lt_self hr)⟩))
  have hWU : W ⊆ U := hWV.trans hVU
  have hℓ : ℓ.toLinearMap ≠ 0 := by
    intro heq
    have hd0 : ℓ d = 0 := congrArg (fun f : _ →ₗ[ℝ] ℝ => f d) heq
    exact zero_ne_one (hd0.symm.trans hℓd)
  have hT : Module.finrank ℝ (LinearMap.ker ℓ.toLinearMap) = 2 := by
    have hr := LinearMap.finrank_range_add_finrank_ker ℓ.toLinearMap
    rw [LinearMap.range_eq_top.mpr (LinearMap.surjective_of_ne_zero hℓ),
      finrank_top, Module.finrank_self] at hr
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    omega
  have hST : S ⊔ LinearMap.ker ℓ.toLinearMap = ⊤ := by
    apply top_unique
    intro z _
    have hker : z - ℓ z • d ∈ LinearMap.ker ℓ.toLinearMap := by
      change ℓ (z - ℓ z • d) = 0
      rw [map_sub, map_smul, hℓd, smul_eq_mul, mul_one, sub_self]
    have hz := Submodule.add_mem (S ⊔ LinearMap.ker ℓ.toLinearMap)
      (Submodule.mem_sup_left (S.smul_mem (ℓ z) hd)) (Submodule.mem_sup_right hker)
    have heq : ℓ z • d + (z - ℓ z • d) = z := by abel
    exact heq ▸ hz
  have hI : Module.finrank ℝ (S ⊓ LinearMap.ker ℓ.toLinearMap :
      Submodule ℝ (EuclideanSpace ℝ (Fin 3))) = 1 := by
    have hr := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker ℓ.toLinearMap)
    rw [hST, finrank_top, hS, hT] at hr
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    omega
  obtain ⟨a, k, ha, halip, hagree, hzero, harange⟩ := hv.exists_lipschitz_extension hJ hU hJU
  have hma : ∀ z, m (a z) = 0 := by
    intro z
    apply convexHull_min (t := ((LinearMap.ker m.toLinearMap : Submodule ℝ _) : Set _)) ?_
      (LinearMap.ker m.toLinearMap).convex (harange z)
    rintro w (rfl | ⟨x, hx, rfl⟩)
    · exact map_zero m
    · exact hmv x hx
  have hbounded : Bornology.IsBounded (convexHull ℝ (insert 0 (v '' J))) :=
    isBounded_convexHull.mpr
      ((hJ.isCompact.image_of_continuousOn hv.continuousOn).insert 0).isBounded
  obtain ⟨M, -, hMbound⟩ := hbounded.exists_pos_norm_lt
  have hM : ∀ z, ‖a z‖ ≤ M := fun z => (hMbound _ (harange z)).le
  obtain ⟨t, h, ht, htk, htkℓ, hh, hformula, hcloseSmall, hheight, -⟩ :=
    exists_small_displacement_preserving_crossing S ℓ m hS hT hI hST hu hd hℓd hmd
      ha halip hma hM (lt_min hε (half_pos hr))
  have hclose (z : EuclideanSpace ℝ (Fin 3)) : dist (h z) z < ε :=
    (hcloseSmall z).trans_le (min_le_left _ _)
  have hpreV (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ W) : h.symm z ∈ V := by
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
    have hdist : dist (h.symm z) z < r / 2 := by
      simpa only [h.apply_symm_apply, dist_comm] using
        (hcloseSmall (h.symm z)).trans_le (min_le_right _ _)
    have hdistw := (dist_triangle (h.symm z) z w).trans_lt (add_lt_add hdist hzw)
    rw [add_halves] at hdistw
    exact hrV (thickening_subset_cthickening r Z
      (mem_thickening_iff.mpr ⟨w, hw, hdistw⟩))
  have hb : IsPiecewiseAffineOn (fun z => t • a z) univ :=
    ha.affine_comp (t • (LinearMap.id : _ →ₗ[ℝ] _)).toAffineMap
  have hblip : LipschitzWith (⟨t, ht.le⟩ * k) (fun z => t • a z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (t • a z) (t • a w) ≤ (t * (k : ℝ)) * dist z w
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left (halip.dist_le_mul z w) ht.le).trans_eq
      (mul_assoc _ _ _).symm
  have hbzero : EqOn (fun z => t • a z) (fun _ => 0) Uᶜ := by
    intro z hz
    change t • a z = 0
    rw [hzero hz, smul_zero]
  have hbplane (z : EuclideanSpace ℝ (Fin 3)) (_hz : m z = 0) : m (t • a z) = 0 := by
    rw [map_smul, hma, smul_zero]
  obtain ⟨F, hFdom, hFP, hFQ, hFoff, hFclose, hFmap, hFproper, hFimage, hFloc, hFcard,
    hFfiber, hFcross, hFhom⟩ :=
    exists_singularTwoCell_preserving_boundary_crossings_of_flat_sheets D hPQ hP hQ hA hB
      hAP hBQ hAB hinjP hfA hfB hloc hcard hVU hW hWV hseam hinjQ hcover S ℓ m hS hu hd
      hℓd hmd hflatA hflatB hC hBd hmap hproper hb hblip htk htkℓ hbzero hbplane h hh
      hformula (fun z => by rw [hheight]; exact ⟨Iff.rfl, Iff.rfl⟩) hpreV hε hclose
  refine ⟨W, t, F, hW, hZW, hWV, ht, hFdom, ?_, hFQ, hFoff, hFclose, hFmap, hFproper,
    hFimage, hFloc, hFcard, hFfiber, hFcross, hFhom⟩
  intro x hx
  exact (hFP hx.1).trans ((hformula (D x)).trans (by rw [hagree hx.2]))

open Classical in
theorem SingularTwoCell.exists_simplicial_perturbation_preserving_boundary_crossings_of_flat_sheets
    (D : SingularTwoCell (EuclideanSpace ℝ (Fin 3)))
    {P Q A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hPQ : P ∪ Q = D.domain) (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hA : IsPolyhedron A) (hB : IsPolyhedron B) (hAP : A ⊆ P) (hBQ : B ⊆ Q)
    (hAB : Disjoint A B) (hinjP : InjOn D P)
    (hfA : IsPLHomeomorphOn D A (D '' A)) (hfB : IsPLHomeomorphOn D B (D '' B))
    (hloc : IsLocallyInjective (D.domain.domRestrict D))
    (hcard : ∀ z, (D.domain ∩ D ⁻¹' {z}).encard ≤ 2)
    {U C V Z : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hZ : IsCompact Z) (hZV : Z ⊆ V)
    (hseam : ∀ x ∈ P ∩ Q, D x ∉ closure U)
    (hinjQ : InjOn D (Q ∩ D ⁻¹' U))
    (hcover : ∀ z ∈ U, D.domain ∩ D ⁻¹' {z} ⊆ A ∪ B)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (ℓ m : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hS : Module.finrank ℝ S = 2)
    (hu : ∃ u ∈ S ⊓ LinearMap.ker ℓ.toLinearMap, m u = 1)
    {d : EuclideanSpace ℝ (Fin 3)} (hd : d ∈ S) (hℓd : ℓ d = 1) (hmd : m d = 0)
    (hflatA : ∀ z ∈ V, z ∈ D '' A ↔ z ∈ S ∧ 0 ≤ m z)
    (hflatB : ∀ z ∈ V, z ∈ D '' B ↔ ℓ z = 0 ∧ 0 ≤ m z)
    (hC : ∀ z ∈ U, z ∈ C ↔ 0 ≤ m z)
    (hBd : ∀ z ∈ U, z ∈ frontier C ↔ m z = 0)
    (hmap : MapsTo D D.domain C)
    (hproper : D.domain ∩ D ⁻¹' frontier C = frontier D.domain)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hKU : K.space ⊆ U) (hKm : ∀ v ∈ K.vertices, 0 ≤ m v) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ v ∈ K.vertices, dist (φ v) v < δ) →
      (∀ v ∈ K.vertices, m v = 0 → m (φ v) = 0) →
      ∃ (W : Set (EuclideanSpace ℝ (Fin 3)))
        (F : SingularTwoCell (EuclideanSpace ℝ (Fin 3))),
        IsOpen W ∧ Z ⊆ W ∧ W ⊆ V ∧ F.domain = D.domain ∧
        EqOn F (simplicialMap K φ ∘ D) (P ∩ D ⁻¹' K.space) ∧
        EqOn F D Q ∧ EqOn F D Pᶜ ∧
        (∀ x, dist (F x) (D x) < ε) ∧ MapsTo F F.domain C ∧
        F.domain ∩ F ⁻¹' frontier C = frontier F.domain ∧
        F '' F.domain ∩ frontier C = range F.boundary ∧
        IsLocallyInjective (F.domain.domRestrict F) ∧
        (∀ z, (F.domain ∩ F ⁻¹' {z}).encard ≤ 2) ∧
        (∀ z ∉ U, F ⁻¹' {z} = D ⁻¹' {z}) ∧
        (∀ z ∈ W ∩ doublePointSet F F.domain,
          (z ∈ frontier C ∧ HasPLBoundaryDoubleCrossingAt F F.domain C z) ∨
          (z ∉ frontier C ∧ HasPLDoubleCrossingAt F F.domain z)) ∧
        ∃ H : ContinuousMap (unitInterval × frontier D.domain) (EuclideanSpace ℝ (Fin 3)),
          (∀ x, H (0, x) = D x) ∧ (∀ x, H (1, x) = F x) ∧
          ∀ s x, dist (H (s, x)) (D x) < ε ∧ H (s, x) ∈ frontier C ∧
            (D x ∉ U → H (s, x) = D x) := by
  obtain ⟨r, hr, hrV⟩ := hZ.exists_cthickening_subset_open hV hZV
  let W := thickening (r / 2) Z
  have hW : IsOpen W := isOpen_thickening
  have hZW : Z ⊆ W := self_subset_thickening (half_pos hr) Z
  have hWV : W ⊆ V := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
    exact hrV (thickening_subset_cthickening r Z
      (mem_thickening_iff.mpr ⟨w, hw, hzw.trans (half_lt_self hr)⟩))
  have hm : m.toLinearMap ≠ 0 := by
    intro heq
    obtain ⟨u, -, hmu⟩ := hu
    have hz : m u = 0 := congrArg (fun f : _ →ₗ[ℝ] ℝ => f u) heq
    exact zero_ne_one (hz.symm.trans hmu)
  let R : ℝ := ‖ℓ‖ * ‖d‖ + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨δ, hδ, hext⟩ :=
    exists_lipschitz_displacement_extending_vertex_perturbation_preserving_halfSpace
      K m.toLinearMap hm hKm hU hKU (lt_min hε (half_pos hr))
      (show 0 < 1 / (2 * R) by positivity)
  refine ⟨δ, hδ, fun φ hφ hφplane => ?_⟩
  obtain ⟨a, k, ha, halip, hkR, hk1, hnorm, hzero, hplane, hagree, hh, hheight⟩ :=
    hext φ hφ hφplane
  let h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    (Homeomorph.Set.univ _).symm.trans (hh.homeomorph.trans (Homeomorph.Set.univ _))
  have hformula (z : EuclideanSpace ℝ (Fin 3)) : h z = z + a z := rfl
  have hcloseSmall (z : EuclideanSpace ℝ (Fin 3)) : dist (h z) z < min ε (r / 2) := by
    rw [hformula, dist_eq_norm, add_sub_cancel_left]
    exact hnorm z
  have hkℓ : (‖ℓ‖₊ * k) * ‖d‖₊ < 1 := by
    have hbound := (lt_div_iff₀ (show 0 < 2 * R by positivity)).mp hkR
    have hnormle : ‖ℓ‖ * ‖d‖ ≤ R := le_add_of_nonneg_right zero_le_one
    change ‖ℓ‖ * (k : ℝ) * ‖d‖ < 1
    calc ‖ℓ‖ * (k : ℝ) * ‖d‖ = (k : ℝ) * (‖ℓ‖ * ‖d‖) := by ring
      _ ≤ (k : ℝ) * R := mul_le_mul_of_nonneg_left hnormle k.property
      _ < 1 := by nlinarith
  have hpreV (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ W) : h.symm z ∈ V := by
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
    have hdist : dist (h.symm z) z < r / 2 := by
      simpa only [h.apply_symm_apply, dist_comm] using
        (hcloseSmall (h.symm z)).trans_le (min_le_right _ _)
    have hdistw := (dist_triangle (h.symm z) z w).trans_lt (add_lt_add hdist hzw)
    rw [add_halves] at hdistw
    exact hrV (thickening_subset_cthickening r Z
      (mem_thickening_iff.mpr ⟨w, hw, hdistw⟩))
  obtain ⟨F, hFdom, hFP, hFQ, hFoff, hFclose, hFmap, hFproper, hFimage, hFloc, hFcard,
    hFfiber, hFcross, hFhom⟩ :=
    exists_singularTwoCell_preserving_boundary_crossings_of_flat_sheets D hPQ hP hQ hA hB
      hAP hBQ hAB hinjP hfA hfB hloc hcard hVU hW hWV hseam hinjQ hcover S ℓ m hS hu hd
      hℓd hmd hflatA hflatB hC hBd hmap hproper ha halip hk1 hkℓ hzero hplane h hh
      hformula hheight hpreV hε (fun z => (hcloseSmall z).trans_le (min_le_left _ _))
  refine ⟨W, F, hW, hZW, hWV, hFdom, ?_, hFQ, hFoff, hFclose, hFmap, hFproper,
    hFimage, hFloc, hFcard, hFfiber, hFcross, hFhom⟩
  intro x hx
  exact (hFP hx.1).trans (hagree hx.2)

open Classical in
theorem SingularTwoCell.exists_generalPosition_preserving_flat_boundary_crossings
    (D : SingularTwoCell (EuclideanSpace ℝ (Fin 3)))
    {P Q A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hPQ : P ∪ Q = D.domain) (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hA : IsPolyhedron A) (hB : IsPolyhedron B) (hAP : A ⊆ P) (hBQ : B ⊆ Q)
    (hAB : Disjoint A B) (hinjP : InjOn D P)
    (hfA : IsPLHomeomorphOn D A (D '' A)) (hfB : IsPLHomeomorphOn D B (D '' B))
    (hloc : IsLocallyInjective (D.domain.domRestrict D))
    (hcard : ∀ z, (D.domain ∩ D ⁻¹' {z}).encard ≤ 2)
    {U C V Z : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hZ : IsCompact Z) (hZV : Z ⊆ V)
    (hseam : ∀ x ∈ P ∩ Q, D x ∉ closure U)
    (hinjQ : InjOn D (Q ∩ D ⁻¹' U))
    (hcover : ∀ z ∈ U, D.domain ∩ D ⁻¹' {z} ⊆ A ∪ B)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (ℓ m : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hS : Module.finrank ℝ S = 2)
    (hu : ∃ u ∈ S ⊓ LinearMap.ker ℓ.toLinearMap, m u = 1)
    {d : EuclideanSpace ℝ (Fin 3)} (hd : d ∈ S) (hℓd : ℓ d = 1) (hmd : m d = 0)
    (hflatA : ∀ z ∈ V, z ∈ D '' A ↔ z ∈ S ∧ 0 ≤ m z)
    (hflatB : ∀ z ∈ V, z ∈ D '' B ↔ ℓ z = 0 ∧ 0 ≤ m z)
    (hC : ∀ z ∈ U, z ∈ C ↔ 0 ≤ m z)
    (hBd : ∀ z ∈ U, z ∈ frontier C ↔ m z = 0)
    (hmap : MapsTo D D.domain C)
    (hproper : D.domain ∩ D ⁻¹' frontier C = frontier D.domain)
    {R T : Set (EuclideanSpace ℝ (Fin 2))} (hR : IsPolyhedron R) (hT : IsPolyhedron T)
    (hRA : R ⊆ A) (hTB : T ⊆ B)
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hKspace : K.space = D '' R) (hLspace : L.space = D '' T)
    (hKU : K.space ⊆ U) (hLU : L.space ⊆ U)
    (hKboundary : ∀ z ∈ K.space, m z = 0 → z ∈ (boundaryComplex 2 K).space)
    (hLboundary : ∀ z ∈ L.space, m z = 0 → z ∈ (boundaryComplex 2 L).space)
    {O Y : Set (EuclideanSpace ℝ (Fin 3))} (hO : IsOpen O) (hOU : O ⊆ U)
    (hY : IsCompact Y) (hYO : Y ⊆ O)
    (hinner : ∀ z ∈ O, D.domain ∩ D ⁻¹' {z} ⊆ R ∪ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (W N : Set (EuclideanSpace ℝ (Fin 3)))
      (F : SingularTwoCell (EuclideanSpace ℝ (Fin 3)))
      (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsOpen W ∧ Z ⊆ W ∧ W ⊆ V ∧ IsOpen N ∧ Y ⊆ N ∧ N ⊆ O ∧
      F.domain = D.domain ∧ EqOn F D Q ∧ EqOn F D Pᶜ ∧
      (∀ x, dist (F x) (D x) < ε) ∧ MapsTo F F.domain C ∧
      F.domain ∩ F ⁻¹' frontier C = frontier F.domain ∧
      F '' F.domain ∩ frontier C = range F.boundary ∧
      IsLocallyInjective (F.domain.domRestrict F) ∧
      (∀ z, (F.domain ∩ F ⁻¹' {z}).encard ≤ 2) ∧
      (∀ z ∉ U, F ⁻¹' {z} = D ⁻¹' {z}) ∧ G.faces.Finite ∧
      G.space = F '' R ∩ F '' T ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
      G.space ∩ N = doublePointSet F F.domain ∩ N ∧
      (∀ z ∈ (W ∪ N) ∩ doublePointSet F F.domain,
        (z ∈ frontier C ∧ HasPLBoundaryDoubleCrossingAt F F.domain C z) ∨
        (z ∉ frontier C ∧ HasPLDoubleCrossingAt F F.domain z)) ∧
      ∃ H : ContinuousMap (unitInterval × frontier D.domain) (EuclideanSpace ℝ (Fin 3)),
        (∀ x, H (0, x) = D x) ∧ (∀ x, H (1, x) = F x) ∧
        ∀ t x, dist (H (t, x)) (D x) < ε ∧ H (t, x) ∈ frontier C ∧
          (D x ∉ U → H (t, x) = D x) := by
  have hPK : P ⊆ D.domain := hPQ ▸ subset_union_left
  have hQK : Q ⊆ D.domain := hPQ ▸ subset_union_right
  have hRP : R ⊆ P := hRA.trans hAP
  have hTQ : T ⊆ Q := hTB.trans hBQ
  have hRD : R ⊆ D.domain := hRP.trans hPK
  have hTD : T ⊆ D.domain := hTQ.trans hQK
  have hKm : ∀ z ∈ K.vertices, 0 ≤ m z := by
    intro z hz
    have hzK := K.subset_space hz (Finset.mem_singleton_self z)
    obtain ⟨x, hx, rfl⟩ := hKspace ▸ hzK
    exact (hC _ (hKU hzK)).mp (hmap (hRD hx))
  have hLm : ∀ z ∈ L.vertices, 0 ≤ m z := by
    intro z hz
    have hzL := L.subset_space hz (Finset.mem_singleton_self z)
    obtain ⟨x, hx, rfl⟩ := hLspace ▸ hzL
    exact (hC _ (hLU hzL)).mp (hmap (hTD hx))
  have hm : m.toLinearMap ≠ 0 := by
    intro heq
    obtain ⟨u, -, hmu⟩ := hu
    have hz : m u = 0 := congrArg (fun f : _ →ₗ[ℝ] ℝ => f u) heq
    exact zero_ne_one (hz.symm.trans hmu)
  obtain ⟨r, hr, hrV⟩ := hZ.exists_cthickening_subset_open hV hZV
  obtain ⟨q, hq, hqO⟩ := hY.exists_cthickening_subset_open hO hYO
  let W := thickening (r / 2) Z
  let N := thickening (q / 2) Y
  have hW : IsOpen W := isOpen_thickening
  have hN : IsOpen N := isOpen_thickening
  have hZW : Z ⊆ W := self_subset_thickening (half_pos hr) Z
  have hYN : Y ⊆ N := self_subset_thickening (half_pos hq) Y
  have hthick {s : ℝ} (hs : 0 < s) {X B : Set (EuclideanSpace ℝ (Fin 3))}
      (hXB : cthickening s X ⊆ B) : thickening (s / 2) X ⊆ B := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
    exact hXB (thickening_subset_cthickening s X
      (mem_thickening_iff.mpr ⟨w, hw, hzw.trans (half_lt_self hs)⟩))
  have hWV : W ⊆ V := hthick hr hrV
  have hNO : N ⊆ O := hthick hq hqO
  let c : ℝ := ‖ℓ‖ * ‖d‖ + 1
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨j, G, k, hklip, hkc, hk1, hj, hjclose, hjfix, hjheight, hGfin, hGspace,
    hGman, hGcross⟩ :=
    exists_small_homeomorph_generalPosition_in_halfSpace_with_lipschitz_displacement
      K L hK hL (by simp) m.toLinearMap hm hKm hLm
      (by convert hKboundary using 1; congr!)
      (by convert hLboundary using 1; congr!) hU hKU hLU
      (lt_min hε (lt_min (half_pos hr) (half_pos hq)))
      (show 0 < 1 / (2 * c) by positivity)
  let h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    (Homeomorph.Set.univ _).symm.trans (hj.homeomorph.trans (Homeomorph.Set.univ _))
  have hh : IsPLHomeomorphOn h univ univ := hj
  let a : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z => h z - z
  have ha : IsPiecewiseAffineOn a univ := by
    have hn := isPiecewiseAffineOn_of_affine (-(AffineMap.id ℝ (EuclideanSpace ℝ (Fin 3))))
      isOpen_univ
    simpa only [a, sub_eq_add_neg, AffineMap.coe_neg, Pi.neg_apply, AffineMap.id_apply] using
      hh.isPiecewiseAffineOn.add hn
  have halip : LipschitzWith k a := hklip
  have hzero : EqOn a (fun _ => 0) Uᶜ := by
    intro z hz
    change j z - z = 0
    rw [hjfix hz]
    exact sub_self z
  have hplane (z : EuclideanSpace ℝ (Fin 3)) (hz : m z = 0) : m (a z) = 0 := by
    change m (j z - z) = 0
    have hjz : m (j z) = 0 := (hjheight z).1.mpr hz
    rw [map_sub, hjz, hz, sub_self]
  have hformula (z : EuclideanSpace ℝ (Fin 3)) : h z = z + a z := by dsimp only [a]; abel
  have hkℓ : (‖ℓ‖₊ * k) * ‖d‖₊ < 1 := by
    have hbound := (lt_div_iff₀ (show 0 < 2 * c by positivity)).mp hkc
    have hnormle : ‖ℓ‖ * ‖d‖ ≤ c := le_add_of_nonneg_right zero_le_one
    change ‖ℓ‖ * (k : ℝ) * ‖d‖ < 1
    calc ‖ℓ‖ * (k : ℝ) * ‖d‖ = (k : ℝ) * (‖ℓ‖ * ‖d‖) := by ring
      _ ≤ (k : ℝ) * c := mul_le_mul_of_nonneg_left hnormle k.property
      _ < 1 := by nlinarith
  have hpre {s : ℝ} {X B : Set (EuclideanSpace ℝ (Fin 3))}
      (hXB : cthickening s X ⊆ B) (hsmall : ∀ z, dist (h z) z < s / 2)
      {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ thickening (s / 2) X) : h.symm z ∈ B := by
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
    have hdist : dist (h.symm z) z < s / 2 := by
      simpa only [h.apply_symm_apply, dist_comm] using hsmall (h.symm z)
    have hdistw := (dist_triangle (h.symm z) z w).trans_lt (add_lt_add hdist hzw)
    rw [add_halves] at hdistw
    exact hXB (thickening_subset_cthickening s X
      (mem_thickening_iff.mpr ⟨w, hw, hdistw⟩))
  have hpreV : ∀ z ∈ W, h.symm z ∈ V := fun _ hz => hpre hrV
    (fun z => (hjclose z).trans_le ((min_le_right _ _).trans (min_le_left _ _))) hz
  have hpreO : ∀ z ∈ N, h.symm z ∈ O := fun _ hz => hpre hqO
    (fun z => (hjclose z).trans_le ((min_le_right _ _).trans (min_le_right _ _))) hz
  obtain ⟨F, hFdom, hFP, hFQ, hFoff, hFclose, hFmap, hFproper, hFimage, hFloc, hFcard,
    hFfiber, hFcross, hFhom⟩ :=
    exists_singularTwoCell_preserving_boundary_crossings_of_flat_sheets D hPQ hP hQ hA hB
      hAP hBQ hAB hinjP hfA hfB hloc hcard hVU hW hWV hseam hinjQ hcover S ℓ m hS hu hd
      hℓd hmd hflatA hflatB hC hBd hmap hproper ha halip hk1 hkℓ hzero hplane h hh
      hformula hjheight hpreV hε (fun z => (hjclose z).trans_le (min_le_left _ _))
  have hRDF : R ⊆ F.domain := hFdom.symm ▸ hRD
  have hTDF : T ⊆ F.domain := hFdom.symm ▸ hTD
  have hRT : Disjoint R T := hAB.mono hRA hTB
  have hFReq : EqOn F (h ∘ D) R := hFP.mono hRP
  have hFTeq : EqOn F D T := hFQ.mono hTQ
  have hFRimage : F '' R = h '' K.space := by
    rw [hKspace, ← image_comp]
    exact hFReq.image_eq
  have hFTimage : F '' T = L.space := hFTeq.image_eq.trans hLspace.symm
  have hDR : IsPLHomeomorphOn D R K.space := hKspace.symm ▸ hfA.restrict hR hRA
  have hFR : IsPLHomeomorphOn F R (F '' R) := by
    rw [hFRimage]
    exact (hDR.trans (hh.restrict (isPolyhedron_space K) (subset_univ _))).congr hFReq
  have hFT : IsPLHomeomorphOn F T (F '' T) := by
    rw [hFTeq.image_eq]
    exact (hfB.restrict hT hTB).congr hFTeq
  have hGactual : G.space = F '' R ∩ F '' T := by
    rw [hFRimage, hFTimage]
    exact hGspace
  have hFinner : ∀ z ∈ N, F.domain ∩ F ⁻¹' {z} ⊆ R ∪ T := by
    intro z hz x hx
    have hxD : x ∈ D.domain := hFdom ▸ hx.1
    by_cases hxP : x ∈ P
    · have hDx : D x = h.symm z := by
        apply h.injective
        rw [h.apply_symm_apply]
        exact (hFP hxP).symm.trans hx.2
      rcases hinner (h.symm z) (hpreO z hz) ⟨hxD, hDx⟩ with hxR | hxT
      · exact Or.inl hxR
      · exact False.elim (hseam x ⟨hxP, hTQ hxT⟩
          (subset_closure (hDx.symm ▸ hOU (hpreO z hz))))
    · have hDx : D x = z := (hFoff hxP).symm.trans hx.2
      exact Or.inr ((hinner z (hNO hz) ⟨hxD, hDx⟩).resolve_left (fun hxR => hxP (hRP hxR)))
  have hdouble (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ N) :
      z ∈ G.space ↔ z ∈ doublePointSet F F.domain := by
    rw [hGactual]
    exact (mem_doublePointSet_iff_mem_image_inter_of_injOn F hRDF hTDF hRT
      hFR.bijOn.injOn hFT.bijOn.injOn (hFinner z hz)).symm
  have hNcross : ∀ z ∈ N ∩ doublePointSet F F.domain,
      (z ∈ frontier C ∧ HasPLBoundaryDoubleCrossingAt F F.domain C z) ∨
      (z ∉ frontier C ∧ HasPLDoubleCrossingAt F F.domain z) := by
    intro z hz
    have hnear : ∀ᶠ w in 𝓝 z, F.domain ∩ F ⁻¹' {w} ⊆ R ∪ T :=
      Filter.Eventually.mono (hN.mem_nhds hz.1) fun w hw => hFinner w hw
    have hGcross' : ∀ y ∈ G.space,
        (m y = 0 ∧ HasPLBoundaryCrossingAt {x | 0 ≤ m x} (h '' K.space) L.space y) ∨
        (0 < m y ∧ HasPLCrossingAt (h '' K.space) L.space y) := hGcross
    rcases hGcross' z ((hdouble z hz.1).mpr hz.2) with ⟨hz0, hc⟩ | ⟨hzpos, hc⟩
    · refine Or.inl ⟨(hBd _ (hOU (hNO hz.1))).mpr hz0, ?_⟩
      rw [← hFRimage, ← hFTimage] at hc
      have hCnear : ∀ᶠ w in 𝓝 z, w ∈ {x | 0 ≤ m x} ↔ w ∈ C :=
        Filter.Eventually.mono (hN.mem_nhds hz.1) fun w hw => (hC w (hOU (hNO hw))).symm
      exact hasPLBoundaryDoubleCrossingAt_of_crossing_and_eventually_fiber_subset
        F.continuousOn hRDF hTDF hR.isClosed hT.isClosed hRT hFR hFT hz.2
        (hc.congr hCnear (Filter.Eventually.of_forall fun _ => Iff.rfl)
          (Filter.Eventually.of_forall fun _ => Iff.rfl)) hnear
    · refine Or.inr ⟨fun hzBd => hzpos.ne' ((hBd _ (hOU (hNO hz.1))).mp hzBd), ?_⟩
      rw [← hFRimage, ← hFTimage] at hc
      exact hasPLDoubleCrossingAt_of_crossing_and_eventually_fiber_subset F.continuousOn
        hRDF hTDF hR.isClosed hT.isClosed hRT hFR hFT hz.2 hc hnear
  refine ⟨W, N, F, G, hW, hZW, hWV, hN, hYN, hNO, hFdom, hFQ, hFoff, hFclose, hFmap,
    hFproper, hFimage, hFloc, hFcard, hFfiber, hGfin, hGactual, hGman, ?_, ?_, hFhom⟩
  · ext z
    exact and_congr_left (fun hz => hdouble z hz)
  · intro z hz
    rcases hz.1 with hzW | hzN
    · exact hFcross z ⟨hzW, hz.2⟩
    · exact hNcross z ⟨hzN, hz.2⟩

open Classical in
theorem SingularTwoCell.exists_generalPosition_fixing_flat_core
    (D : SingularTwoCell (EuclideanSpace ℝ (Fin 3)))
    {P Q R T : Set (EuclideanSpace ℝ (Fin 2))}
    (hPQ : P ∪ Q = D.domain) (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hR : IsPolyhedron R) (hT : IsPolyhedron T) (hRP : R ⊆ P) (hTQ : T ⊆ Q)
    (hRT : Disjoint R T) (hinjP : InjOn D P)
    (hfR : IsPLHomeomorphOn D R (D '' R)) (hfT : IsPLHomeomorphOn D T (D '' T))
    (hloc : IsLocallyInjective (D.domain.domRestrict D))
    (hcard : ∀ z, (D.domain ∩ D ⁻¹' {z}).encard ≤ 2)
    {U C O V Y Z : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUC : U ⊆ interior C) (hO : IsOpen O) (hOU : O ⊆ U)
    (hV : IsOpen V) (hVO : V ⊆ O) (hY : IsCompact Y) (hYO : Y ⊆ O)
    (hZ : IsCompact Z) (hZV : Z ⊆ V)
    (hseam : ∀ x ∈ P ∩ Q, D x ∉ closure U)
    (hinjQ : InjOn D (Q ∩ D ⁻¹' U))
    (hinner : ∀ z ∈ O, D.domain ∩ D ⁻¹' {z} ⊆ R ∪ T)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hS : Module.finrank ℝ S = 2)
    {d : EuclideanSpace ℝ (Fin 3)} (hd : d ∈ S) (hℓd : ℓ d = 1)
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hKspace : K.space = D '' R) (hLspace : L.space = D '' T) (hKU : K.space ⊆ U)
    (hflatK : ∀ z ∈ V, z ∈ K.space ↔ z ∈ S)
    (hflatL : ∀ z ∈ V, z ∈ L.space ↔ ℓ z = 0)
    (hmap : MapsTo D D.domain C)
    (hproper : D.domain ∩ D ⁻¹' frontier C = frontier D.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ (J N : Set (EuclideanSpace ℝ (Fin 3)))
      (F : SingularTwoCell (EuclideanSpace ℝ (Fin 3))),
      IsPolyhedron J ∧ Z ⊆ interior J ∧ J ⊆ V ∧ IsOpen N ∧ Y ⊆ N ∧ J ⊆ N ∧ N ⊆ O ∧
      F.domain = D.domain ∧ EqOn F D Q ∧ EqOn F D Pᶜ ∧ EqOn F D (D ⁻¹' J) ∧
      EqOn F D (frontier D.domain) ∧ (∀ x, dist (F x) (D x) < ε) ∧
      MapsTo F F.domain C ∧ F.domain ∩ F ⁻¹' frontier C = frontier F.domain ∧
      F '' F.domain ∩ frontier C = range F.boundary ∧
      IsLocallyInjective (F.domain.domRestrict F) ∧
      (∀ z, (F.domain ∩ F ⁻¹' {z}).encard ≤ 2) ∧
      (∀ z ∉ U, F ⁻¹' {z} = D ⁻¹' {z}) ∧
      (F '' R ∩ F '' T) ∩ N = doublePointSet F F.domain ∩ N ∧
      (∀ z ∈ N ∩ doublePointSet F F.domain, HasPLDoubleCrossingAt F F.domain z) ∧
      ∃ H : ContinuousMap (unitInterval × frontier D.domain) (EuclideanSpace ℝ (Fin 3)),
        (∀ x, H (0, x) = D x) ∧ (∀ x, H (1, x) = F x) ∧
        ∀ t x, H (t, x) = D x ∧ H (t, x) ∈ frontier C := by
  obtain ⟨r, hr, hrO⟩ := hY.exists_cthickening_subset_open hO hYO
  obtain ⟨J, h, hJ, hZJ, hJV, hh, hclose, hfix, hfixJ, hcross⟩ :=
    exists_homeomorph_generalPosition_fixing_flat_core K L hK hL (by simp) hU hKU hV
      (hVO.trans hOU) hZ hZV S ℓ hS hd hℓd hflatK hflatL (lt_min hε hr)
  have hpreY : ∀ z ∈ Y, h.symm z ∈ O := by
    intro z hz
    have hdist : dist (h.symm z) z < r := by
      simpa only [h.apply_symm_apply, dist_comm] using
        (hclose (h.symm z)).trans_le (min_le_right _ _)
    exact hrO (thickening_subset_cthickening r Y (mem_thickening_iff.mpr ⟨z, hz, hdist⟩))
  let N := O ∩ h.symm ⁻¹' O
  have hN : IsOpen N := hO.inter (hO.preimage h.symm.continuous)
  have hJN : J ⊆ N := by
    intro z hz
    have hinv : h.symm z = z := by
      apply h.injective
      exact (h.apply_symm_apply z).trans (hfixJ hz).symm
    refine ⟨hVO (hJV hz), ?_⟩
    change h.symm z ∈ O
    rw [hinv]
    exact hVO (hJV hz)
  have hmaps : MapsTo h U U := by
    intro z hz
    by_contra hnot
    have heq : h z = z := h.injective (hfix hnot)
    exact hnot (heq.symm ▸ hz)
  have hpres (z : EuclideanSpace ℝ (Fin 3)) :
      (h z ∈ C ↔ z ∈ C) ∧ (h z ∈ frontier C ↔ z ∈ frontier C) := by
    by_cases hz : z ∈ U
    · exact ⟨iff_of_true (interior_subset (hUC (hmaps hz))) (interior_subset (hUC hz)),
        iff_of_false (fun hb => hb.2 (hUC (hmaps hz))) (fun hb => hb.2 (hUC hz))⟩
    · rw [hfix hz]
      exact ⟨Iff.rfl, Iff.rfl⟩
  have hhPL : IsPL 3 3 h := fun z =>
    ⟨h.continuous.continuousAt.continuousWithinAt, hh.isPiecewiseAffineOn z (mem_univ z)⟩
  have hf : IsPLOn 2 3 D (P ∪ Q) := hPQ.symm ▸ D.isPLOn
  have hlocPQ : IsLocallyInjective ((P ∪ Q).domRestrict D) := hPQ.symm ▸ hloc
  have hcardPQ : ∀ z, ((P ∪ Q) ∩ D ⁻¹' {z}).encard ≤ 2 := hPQ.symm ▸ hcard
  obtain ⟨g, hg, hgloc, hgcard, hgP, hgQ, hgOff, hgfiber⟩ :=
    exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective hf hP hQ hlocPQ hcardPQ
      hinjP hhPL h.injective hfix hseam hinjQ
  rw [hPQ] at hg hgloc hgcard
  let F : SingularTwoCell (EuclideanSpace ℝ (Fin 3)) :=
    { domain := D.domain
      isPLBall_domain := D.isPLBall_domain
      toFun := g
      isPLOn := hg }
  have hgpres (x : EuclideanSpace ℝ (Fin 2)) :
      (g x ∈ C ↔ D x ∈ C) ∧ (g x ∈ frontier C ↔ D x ∈ frontier C) := by
    by_cases hxP : x ∈ P
    · rw [hgP hxP]
      exact hpres (D x)
    · rw [hgOff hxP]
      exact ⟨Iff.rfl, Iff.rfl⟩
  have hgproper : D.domain ∩ g ⁻¹' frontier C = frontier D.domain := by
    rw [← hproper]
    ext x
    exact and_congr_right fun _ => (hgpres x).2
  have hgboundary : EqOn g D (frontier D.domain) := by
    intro x hx
    have hDx : D x ∈ frontier C := (hproper.superset hx).2
    have hout : D x ∉ U := fun hxin => hDx.2 (hUC hxin)
    by_cases hxP : x ∈ P
    · exact (hgP hxP).trans (hfix hout)
    · exact hgOff hxP
  have hRD : R ⊆ F.domain := hRP.trans (hPQ ▸ subset_union_left)
  have hTD : T ⊆ F.domain := hTQ.trans (hPQ ▸ subset_union_right)
  have hgReq : EqOn F (h ∘ D) R := hgP.mono hRP
  have hgTeq : EqOn F D T := hgQ.mono hTQ
  have hFRimage : F '' R = h '' K.space := by
    rw [hKspace, ← image_comp]
    exact hgReq.image_eq
  have hFTimage : F '' T = L.space := hgTeq.image_eq.trans hLspace.symm
  have hFR : IsPLHomeomorphOn F R (F '' R) := by
    have hDR : IsPLHomeomorphOn D R K.space := hKspace.symm ▸ hfR
    rw [hFRimage]
    exact (hDR.trans (hh.restrict (isPolyhedron_space K) (subset_univ _))).congr hgReq
  have hFT : IsPLHomeomorphOn F T (F '' T) := by
    rw [hgTeq.image_eq]
    exact hfT.congr hgTeq
  have hFinner : ∀ z ∈ N, F.domain ∩ F ⁻¹' {z} ⊆ R ∪ T := by
    intro z hz x hx
    by_cases hxP : x ∈ P
    · have hDx : D x = h.symm z := by
        apply h.injective
        rw [h.apply_symm_apply]
        exact (hgP hxP).symm.trans hx.2
      rcases hinner (h.symm z) hz.2 ⟨hx.1, hDx⟩ with hxR | hxT
      · exact Or.inl hxR
      · exact False.elim (hseam x ⟨hxP, hTQ hxT⟩
          (subset_closure (hDx.symm ▸ hOU hz.2)))
    · have hDx : D x = z := (hgOff hxP).symm.trans hx.2
      exact Or.inr ((hinner z hz.1 ⟨hx.1, hDx⟩).resolve_left (fun hxR => hxP (hRP hxR)))
  have hdouble (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ N) :
      z ∈ F '' R ∩ F '' T ↔ z ∈ doublePointSet F F.domain :=
    (mem_doublePointSet_iff_mem_image_inter_of_injOn F hRD hTD hRT
      hFR.bijOn.injOn hFT.bijOn.injOn (hFinner z hz)).symm
  have hinter : F '' F.domain ∩ frontier C = range F.boundary := by
    rw [← image_inter_preimage]
    change g '' (D.domain ∩ g ⁻¹' frontier C) = range F.boundary
    rw [hgproper]
    ext z
    exact ⟨fun ⟨x, hx, hxz⟩ => ⟨⟨x, hx⟩, hxz⟩,
      fun ⟨x, hxz⟩ => ⟨x, x.2, hxz⟩⟩
  refine ⟨J, N, F, hJ, hZJ, hJV, hN, fun z hz => ⟨hYO hz, hpreY z hz⟩,
    hJN, inter_subset_left, rfl, hgQ, hgOff, ?_, hgboundary, ?_,
    fun x hx => (hgpres x).1.mpr (hmap hx), hgproper, hinter, hgloc, hgcard, hgfiber, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxP : x ∈ P
    · exact (hgP hxP).trans (hfixJ hx)
    · exact hgOff hxP
  · intro x
    by_cases hxP : x ∈ P
    · rw [show F x = h (D x) from hgP hxP]
      exact (hclose (D x)).trans_le (min_le_left _ _)
    · rw [show F x = D x from hgOff hxP, dist_self]
      exact hε
  · ext z
    exact and_congr_left fun hz => hdouble z hz
  · intro z hz
    have hc : HasPLCrossingAt (F '' R) (F '' T) z := by
      have hzRT := (hdouble z hz.1).mpr hz.2
      rw [hFRimage, hFTimage] at hzRT ⊢
      exact hcross z hzRT
    have hnear : ∀ᶠ w in 𝓝 z, F.domain ∩ F ⁻¹' {w} ⊆ R ∪ T :=
      Filter.Eventually.mono (hN.mem_nhds hz.1) fun w hw => hFinner w hw
    exact hasPLDoubleCrossingAt_of_crossing_and_eventually_fiber_subset F.continuousOn
      hRD hTD hR.isClosed hT.isClosed hRT hFR hFT hz.2 hc hnear
  · let H : ContinuousMap (unitInterval × frontier D.domain) (EuclideanSpace ℝ (Fin 3)) :=
      ⟨fun z => D z.2, D.boundary.continuous.comp continuous_snd⟩
    exact ⟨H, fun _ => rfl, fun x => (hgboundary x.property).symm,
      fun _ x => ⟨rfl, (hproper.superset x.property).2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
