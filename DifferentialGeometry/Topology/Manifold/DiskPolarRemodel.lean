import DifferentialGeometry.Topology.Manifold.DiskBoundaryGerm
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Polar re-modelling of a disk along a regular boundary-defining function

Review 44 item (3) (R1, lane LFR28-ROW3). Let `S` be a manifold with boundary with a
diffeomorphism `D₀ : ClosedCell (m + 1) ≃ₘ S`, and let `T : S → ℝ` be smooth on an open
neighbourhood `V` of `∂S` with `T = c` on `∂S`, `T ≤ c` on `V` and `dT ≠ 0` on `∂S` (an ARBITRARY
regular boundary-defining function, as the review's disposition 3(b) requires). Then
`exists_diskDiffeomorph_polar_of_boundaryDefining` gives `δ ∈ (0, η)` and a diffeomorphism
`D : ClosedCell (m + 1) ≃ₘ S` with

* `T (D z) = c + κ (‖z‖ - 1)` for `1 - δ < ‖z‖` (so `T ∘ D (r θ̂)` is radial near the boundary and
  the angle is the cell's standard one),
* `D = D₀` on the boundary sphere and on `‖z‖ ≤ 1 - η`.

`exists_diskDiffeomorph_polar_radial` is the two-dimensional form with the review's hypothesis
`∂S = {T = c}` (on `V`) and the conclusion written in polar coordinates `r θ̂`.

Construction. The core is `exists_closedCellDiffeomorph_polar` on the cell itself (`u = T ∘ D₀`):
1. a cut-off of `u` near the sphere has a smooth half-space extension `G : ℝᵐ⁺¹ → ℝ`;
2. `G = c` on the sphere, so its derivative vanishes on tangent directions
   (`fderiv_apply_eq_zero_of_eqOn_unitSphere`); regularity of `u` gives `dG x ≠ 0`, hence the radial
   derivative `dG x x ≠ 0` (`fderiv_apply_self_ne_zero_of_eqOn_unitSphere`);
3. the radial normalization `h z = (1 + κ⁻¹ (G z - c)) • (‖z‖⁻¹ • z)` (`boundaryPolarMap`) is the
   identity on the sphere and has bijective derivative there (`bijective_fderiv_boundaryPolarMap`),
   so it is a partial diffeomorphism near the sphere; `‖h z‖ = 1 + κ⁻¹ (G z - c)`;
4. the inverse germ `F = h⁻¹` on a thin annulus maps the outside of the ball to the outside
   (by `u ≤ c` inside and injectivity of `h`); the tree's sphere-germ isotopy
   (`PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball`,
   the same ambient step as in `exists_diskDiffeomorph_eq_boundaryGerm`) realizes `F` near the
   sphere by a diffeomorphism of the plane preserving the ball and supported in `{‖x‖ > 1 - η}`;
   restricted to the cell (`closedCellDiffeomorph`) it is `ψ`, and `u (ψ z) = G (F z)` with
   `‖z‖ = ‖h (F z)‖ = 1 + κ⁻¹ (G (F z) - c)`.

Strengthening against the brief: no gradient-like collar of `∂S` is assumed (the radial lines of
`D₀` serve as the transverse field), and `∂S = {T = c}` is used only in the direction
`∂S ⊆ {T = c}`. Deviation: the germ is produced on the ambient plane, so the ambient step of
`exists_diskDiffeomorph_eq_boundaryGerm` is used directly instead of that lemma (whose input is a
partial diffeomorphism of the closed cell).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.Topology.Manifold

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A function constant on the unit sphere has vanishing derivative along the tangent
directions of the sphere. -/
theorem fderiv_apply_eq_zero_of_eqOn_unitSphere {G : E → ℝ} {c : ℝ}
    (hGc : ∀ y : E, ‖y‖ = 1 → G y = c) {x : E} (hx : ‖x‖ = 1) (hG : DifferentiableAt ℝ G x)
    {v : E} (hv : ⟪x, v⟫ = 0) : fderiv ℝ G x v = 0 := by
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set w : E := ‖v‖⁻¹ • v with hwdef
  have hw1 : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
  have hxw : ⟪x, w⟫ = 0 := by rw [hwdef, inner_smul_right, hv, mul_zero]
  let γ : ℝ → E := fun t => Real.cos t • x + Real.sin t • w
  have hγ1 : ∀ t, ‖γ t‖ = 1 := by
    intro t
    have hsq : ‖γ t‖ ^ 2 = 1 := by
      change ‖Real.cos t • x + Real.sin t • w‖ ^ 2 = 1
      rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hxw, hx, hw1,
        Real.norm_eq_abs, Real.norm_eq_abs]
      simp only [conj_trivial, mul_zero, mul_one, add_zero]
      rw [sq_abs, sq_abs, Real.cos_sq_add_sin_sq]
    have h0 : 0 ≤ ‖γ t‖ := norm_nonneg _
    nlinarith
  have hγ0 : γ 0 = x := by simp [γ]
  have hγd : HasDerivAt γ w 0 := by
    have h := ((Real.hasDerivAt_cos 0).smul_const x).add ((Real.hasDerivAt_sin 0).smul_const w)
    simp only [Real.sin_zero, neg_zero, zero_smul, Real.cos_zero, one_smul, zero_add] at h
    exact h
  have hcomp : HasDerivAt (G ∘ γ) (fderiv ℝ G x w) 0 := by
    have hG' : HasFDerivAt G (fderiv ℝ G x) (γ 0) := by rw [hγ0]; exact hG.hasFDerivAt
    exact hG'.comp_hasDerivAt 0 hγd
  have hconst : G ∘ γ = fun _ => c := by
    funext t
    exact hGc _ (hγ1 t)
  rw [hconst] at hcomp
  have hw0 : fderiv ℝ G x w = 0 := (hasDerivAt_const (0 : ℝ) c).unique hcomp |>.symm
  have hvw : v = ‖v‖ • w := by rw [hwdef, smul_smul, mul_inv_cancel₀ hnv.ne', one_smul]
  rw [hvw, map_smul, hw0, smul_zero]

/-- A function constant on the unit sphere with nonzero derivative at a point of the sphere has
nonzero radial derivative there. -/
theorem fderiv_apply_self_ne_zero_of_eqOn_unitSphere {G : E → ℝ} {c : ℝ}
    (hGc : ∀ y : E, ‖y‖ = 1 → G y = c) {x : E} (hx : ‖x‖ = 1) (hG : DifferentiableAt ℝ G x)
    (hne : fderiv ℝ G x ≠ 0) : fderiv ℝ G x x ≠ 0 := by
  intro h0
  apply hne
  ext y
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have horth : ⟪x, y - ⟪x, y⟫ • x⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right, hxx, mul_one, sub_self]
  have hdec : y = ⟪x, y⟫ • x + (y - ⟪x, y⟫ • x) := by abel
  rw [hdec, map_add, map_smul, h0, smul_zero, zero_add,
    fderiv_apply_eq_zero_of_eqOn_unitSphere hGc hx hG horth, zero_apply]

/-- The derivative of `z ↦ ‖z‖⁻¹` at a point of the unit sphere sends that point to `-1`. -/
theorem fderiv_norm_inv_apply_self {x : E} (hx : ‖x‖ = 1) :
    fderiv ℝ (fun z : E => ‖z‖⁻¹) x x = -1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hN : DifferentiableAt ℝ (fun z : E => ‖z‖⁻¹) x :=
    ((contDiffAt_norm ℝ hx0 (n := 1)).inv (norm_ne_zero_iff.mpr hx0)).differentiableAt
      (by norm_num)
  have hcurve : HasDerivAt (fun t : ℝ => (1 + t) • x) x 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const x
    simp only [one_smul] at h
    exact h
  have hcomp : HasDerivAt ((fun z : E => ‖z‖⁻¹) ∘ fun t : ℝ => (1 + t) • x)
      (fderiv ℝ (fun z : E => ‖z‖⁻¹) x x) 0 := by
    have hN' : HasFDerivAt (fun z : E => ‖z‖⁻¹) (fderiv ℝ (fun z : E => ‖z‖⁻¹) x)
        ((fun t : ℝ => (1 + t) • x) 0) := by
      simp only [add_zero, one_smul]
      exact hN.hasFDerivAt
    exact hN'.comp_hasDerivAt 0 hcurve
  have hinv : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-1) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)
    simp only [id, add_zero, one_pow, div_one] at h
    exact h
  have hev : ((fun z : E => ‖z‖⁻¹) ∘ fun t : ℝ => (1 + t) • x) =ᶠ[𝓝 0]
      fun t : ℝ => (1 + t)⁻¹ := by
    have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 + t := by
      have : (0 : ℝ) < 1 + 0 := by norm_num
      exact (continuous_const.add continuous_id).continuousAt.eventually (lt_mem_nhds this)
    filter_upwards [hpos] with t ht
    simp only [comp_apply, norm_smul, hx, mul_one, Real.norm_eq_abs, abs_of_pos ht]
  exact (hinv.congr_of_eventuallyEq hev).unique hcomp |>.symm

/-- The radial normalization of a function near the unit sphere:
`z ↦ (1 + κ⁻¹ (G z - c)) • (‖z‖⁻¹ • z)`. Its norm is `1 + κ⁻¹ (G z - c)`. -/
def boundaryPolarMap (G : E → ℝ) (c κ : ℝ) (z : E) : E :=
  (1 + κ⁻¹ * (G z - c)) • (‖z‖⁻¹ • z)

theorem boundaryPolarMap_of_norm_eq_one {G : E → ℝ} {c κ : ℝ} {z : E} (hz : ‖z‖ = 1)
    (hGz : G z = c) : boundaryPolarMap G c κ z = z := by
  simp [boundaryPolarMap, hz, hGz]

theorem norm_boundaryPolarMap {G : E → ℝ} {c κ : ℝ} {z : E} (hz : z ≠ 0)
    (h0 : 0 ≤ 1 + κ⁻¹ * (G z - c)) : ‖boundaryPolarMap G c κ z‖ = 1 + κ⁻¹ * (G z - c) := by
  rw [boundaryPolarMap, norm_smul, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz), mul_one, Real.norm_eq_abs, abs_of_nonneg h0]

theorem contDiffOn_boundaryPolarMap {G : E → ℝ} (hG : ContDiff ℝ ∞ G) (c κ : ℝ) :
    ContDiffOn ℝ ∞ (boundaryPolarMap G c κ) {z | z ≠ 0} := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  exact (contDiffAt_const.add (contDiffAt_const.mul (hG.contDiffAt.sub contDiffAt_const))).smul
    (((contDiffAt_norm ℝ hz).inv (norm_ne_zero_iff.mpr hz)).smul contDiffAt_id)

/-- The derivative of the radial normalization is bijective at the unit sphere when `G` is
constant on the sphere with nonzero derivative there. -/
theorem bijective_fderiv_boundaryPolarMap [FiniteDimensional ℝ E] {G : E → ℝ} {c κ : ℝ}
    (hGc : ∀ y : E, ‖y‖ = 1 → G y = c) {x : E} (hx : ‖x‖ = 1) (hG : DifferentiableAt ℝ G x)
    (hne : fderiv ℝ G x ≠ 0) (hκ : κ ≠ 0) :
    Bijective (fderiv ℝ (boundaryPolarMap G c κ) x) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  set N' := fderiv ℝ (fun z : E => ‖z‖⁻¹) x with hN'def
  have hN : HasFDerivAt (fun z : E => ‖z‖⁻¹) N' x :=
    (((contDiffAt_norm ℝ hx0 (n := 1)).inv (norm_ne_zero_iff.mpr hx0)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hn : HasFDerivAt (fun z : E => ‖z‖⁻¹ • z)
      (‖x‖⁻¹ • ContinuousLinearMap.id ℝ E + N'.smulRight x) x :=
    hN.fun_smul (hasFDerivAt_id x)
  have hk : HasFDerivAt (fun z => 1 + κ⁻¹ * (G z - c)) (κ⁻¹ • fderiv ℝ G x) x :=
    ((hG.hasFDerivAt.sub_const c).const_mul κ⁻¹).const_add 1
  have hh := hk.fun_smul hn
  have hL : ∀ y : E, fderiv ℝ (boundaryPolarMap G c κ) x y =
      y + (N' y + κ⁻¹ * fderiv ℝ G x y) • x := by
    intro y
    rw [show boundaryPolarMap G c κ = fun z => (1 + κ⁻¹ * (G z - c)) • (‖z‖⁻¹ • z) from rfl,
      hh.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, hGc x hx, sub_self,
      mul_zero, add_zero, one_smul, hx, inv_one, smul_eq_mul]
    rw [add_smul, add_assoc]
  have hLx : fderiv ℝ (boundaryPolarMap G c κ) x x = (κ⁻¹ * fderiv ℝ G x x) • x := by
    rw [hL, hN'def, fderiv_norm_inv_apply_self hx]
    rw [show x + (-1 + κ⁻¹ * fderiv ℝ G x x) • x = (κ⁻¹ * fderiv ℝ G x x) • x + (x - x) by
      rw [add_smul, neg_one_smul]; abel, sub_self, add_zero]
  have hax : κ⁻¹ * fderiv ℝ G x x ≠ 0 :=
    mul_ne_zero (inv_ne_zero hκ) (fderiv_apply_self_ne_zero_of_eqOn_unitSphere hGc hx hG hne)
  have hinj : Injective (fderiv ℝ (boundaryPolarMap G c κ) x) := by
    refine (injective_iff_map_eq_zero (fderiv ℝ (boundaryPolarMap G c κ) x)).mpr ?_
    intro y hy
    set t : ℝ := -(N' y + κ⁻¹ * fderiv ℝ G x y) with htdef
    have hyt : y = t • x := by
      rw [hL] at hy
      rw [htdef, neg_smul, eq_neg_iff_add_eq_zero]
      exact hy
    rw [hyt, map_smul, hLx, smul_smul] at hy
    have ht0 : t * (κ⁻¹ * fderiv ℝ G x x) = 0 := by
      by_contra hne'
      exact hx0 ((smul_eq_zero.mp hy).resolve_left hne')
    have ht : t = 0 := (mul_eq_zero.mp ht0).resolve_right hax
    rw [hyt, ht, zero_smul]
  exact ⟨hinj, (LinearMap.injective_iff_surjective
    (f := (fderiv ℝ (boundaryPolarMap G c κ) x).toLinearMap)).mp hinj⟩

end Sphere

section Cell

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- **Polar re-modelling on the closed cell.** A function `u` on `ClosedCell (m + 1)`, smooth on
an open neighbourhood `W` of the boundary sphere, equal to `c` on the sphere, `≤ c` on `W` and
regular on the sphere, is made radial near the sphere by a diffeomorphism of the cell that fixes
the sphere pointwise and is the identity on `‖z‖ ≤ 1 - η`:
`u (ψ z) = c + κ (‖z‖ - 1)` for `‖z‖ > 1 - δ`. -/
theorem exists_closedCellDiffeomorph_polar {m : ℕ} {u : ClosedCell (m + 1) → ℝ}
    {W : Set (ClosedCell (m + 1))} (hW : IsOpen W)
    (hSW : ∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 → z ∈ W)
    (hu : ContMDiffOn (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ u W) {c : ℝ}
    (huc : ∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 → u z = c)
    (hule : ∀ z ∈ W, u z ≤ c)
    (hreg : ∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 →
      mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) u z ≠ 0)
    {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
      ∃ ψ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1),
        (∀ z : ClosedCell (m + 1), 1 - δ < ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ →
          ψ z ∈ W ∧ u (ψ z) = c + κ * (‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ - 1)) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 → ψ z = z) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 - η → ψ z = z) := by
  -- 1. a collar inside `W`
  obtain ⟨U, hUo, hUs⟩ := isOpen_induced_iff.mp hW
  have hSU : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆ U := by
    intro x hx
    have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hmem : (⟨x, hx1.le⟩ : ClosedCell (m + 1)) ∈ W := hSW _ hx1
    rw [← hUs] at hmem
    exact hmem
  obtain ⟨δ₀', hδ₀', hthick⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).exists_thickening_subset_open hUo hSU
  set δ₀ := min δ₀' (1 / 2) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min hδ₀' (by norm_num)
  have hδ₀1 : δ₀ ≤ 1 / 2 := min_le_right _ _
  have hcollar : ∀ z : ClosedCell (m + 1), 1 - δ₀ < ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ →
      z ∈ W := by
    intro z hz
    have hz1 : ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := z.2
    have hz0 : (z : EuclideanSpace ℝ (Fin (m + 1))) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      linarith
    have habs : |‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ - 1| < δ₀' := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith [min_le_left δ₀' (1 / 2)]
    have hzU : (z : EuclideanSpace ℝ (Fin (m + 1))) ∈ U :=
      hthick (mem_thickening_sphere_of_abs_norm_sub_one_lt hz0 habs)
    rw [← hUs]
    exact hzU
  -- 2. the cut-off and the half-space extension `G`
  set a : ℝ := 1 - δ₀ / 2 with hadef
  set b : ℝ := 1 - δ₀ / 4 with hbdef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  let χ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ :=
    fun x => Real.smoothTransition ((‖x‖ ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2))
  have hχs : ContDiff ℝ ∞ χ := by
    refine Real.smoothTransition.contDiff.comp ?_
    exact ((contDiff_norm_sq ℝ).sub contDiff_const).div_const _
  have hba2 : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hχ1 : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), b ≤ ‖x‖ → χ x = 1 := by
    intro x hx
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hba2]
    nlinarith [norm_nonneg x]
  have hχ0 : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), ‖x‖ ≤ a → χ x = 0 := by
    intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hba2.le
    nlinarith [norm_nonneg x]
  let ũ : ClosedCell (m + 1) → ℝ := fun z => χ (z : EuclideanSpace ℝ (Fin (m + 1))) • u z
  have hval : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) :=
    Handle.closedCellInclusion_contMDiff m
  have hũ : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ ũ := by
    intro z
    by_cases hz : z ∈ W
    · exact ((hχs.contMDiff.comp hval) z).smul ((hu z hz).contMDiffAt (hW.mem_nhds hz))
    · have hza : ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ < a := by
        by_contra h
        exact hz (hcollar z (by push Not at h; linarith))
      have hev : ũ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        have hop : IsOpen {w : ClosedCell (m + 1) | ‖(w : EuclideanSpace ℝ (Fin (m + 1)))‖ < a} :=
          isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
        filter_upwards [hop.mem_nhds hza] with w hw
        change χ (w : EuclideanSpace ℝ (Fin (m + 1))) • _ = 0
        rw [hχ0 _ (le_of_lt hw), zero_smul]
      exact contMDiffAt_const.congr_of_eventuallyEq hev
  have hKc : IsCompact (univ : Set (ClosedCell (m + 1))) := by
    rw [Subtype.isCompact_iff, image_univ, Subtype.range_coe_subtype]
    convert isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 using 1
    ext x
    simp only [mem_ofPred_eq, mem_closedBall_zero_iff]
  obtain ⟨G, hG, -, -, hGu⟩ :=
    (Handle.closedCellInclusion_isSmoothEmbedding m).exists_contDiff_compact_extension_halfspace
      hũ hKc isOpen_univ (subset_univ _)
  have hGeq : ∀ z : ClosedCell (m + 1), b ≤ ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ →
      G z = u z := by
    intro z hz
    have h := hGu (mem_univ z)
    change G (z : EuclideanSpace ℝ (Fin (m + 1))) = χ (z : EuclideanSpace ℝ (Fin (m + 1))) • _ at h
    rw [h, hχ1 _ hz, one_smul]
  have hGc : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → G y = c := by
    intro y hy
    have h1 := hGeq ⟨y, hy.le⟩ (by change b ≤ ‖y‖; rw [hy, hbdef]; linarith)
    rw [huc ⟨y, hy.le⟩ hy] at h1
    exact h1
  -- 3. regularity of `G` on the sphere
  have hGne : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), ‖x‖ = 1 → fderiv ℝ G x ≠ 0 := by
    intro x hx h0
    let xc : ClosedCell (m + 1) := ⟨x, hx.le⟩
    apply hreg xc hx
    have hev : u =ᶠ[𝓝 xc] (G ∘ (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1)))) := by
      have hop : IsOpen {w : ClosedCell (m + 1) | b < ‖(w : EuclideanSpace ℝ (Fin (m + 1)))‖} :=
        isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
      have hxb : xc ∈ {w : ClosedCell (m + 1) | b < ‖(w : EuclideanSpace ℝ (Fin (m + 1)))‖} := by
        change b < ‖x‖
        rw [hx, hbdef]
        linarith
      filter_upwards [hop.mem_nhds hxb] with w hw
      exact (hGeq w hw.le).symm
    have h0' : fderiv ℝ G (xc : EuclideanSpace ℝ (Fin (m + 1))) = 0 := h0
    rw [hev.mfderiv_eq, mfderiv_comp xc ((hG.contMDiff (x := x)).mdifferentiableAt (by simp))
      ((hval xc).mdifferentiableAt (by simp)), mfderiv_eq_fderiv, h0']
    ext v
    simp
  -- 4. the radial normalization is a local diffeomorphism at the sphere
  let h := boundaryPolarMap G c κ
  have hhs : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ h {z | z ≠ 0} :=
    (contDiffOn_boundaryPolarMap hG c κ).contMDiffOn
  have hloc : IsLocalDiffeomorphOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ h
      (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
    intro x
    have hx : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have hx0 : (x : EuclideanSpace ℝ (Fin (m + 1))) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hx
      exact zero_ne_one hx
    have hbij := bijective_fderiv_boundaryPolarMap hGc hx (hG.differentiable (by simp) x)
      (hGne x hx) hκ.ne'
    let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ h x)
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
    have hd : DifferentiableAt ℝ h x :=
      ((contDiffOn_boundaryPolarMap hG c κ).contDiffAt (isOpen_ne.mem_nhds hx0)).differentiableAt
        (by simp)
    exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv h hhs isOpen_ne x hx0 A
      hd.hasFDerivAt.hasMFDerivAt
  have hhS : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), ‖x‖ = 1 → h x = x :=
    fun x hx => boundaryPolarMap_of_norm_eq_one hx (hGc x hx)
  have hinjS : InjOn h (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
    intro x hx y hy hxy
    rwa [hhS x (mem_sphere_zero_iff_norm.mp hx), hhS y (mem_sphere_zero_iff_norm.mp hy)] at hxy
  obtain ⟨φ, hφs, hφh⟩ := DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
    hloc (isCompact_sphere _ _) (NormedSpace.sphere_nonempty.mpr zero_le_one) hinjS
  -- 5. the annulus where `|G - c| < κ / 2`
  have hO₁ : IsOpen {z : EuclideanSpace ℝ (Fin (m + 1)) | |G z - c| < κ / 2} :=
    isOpen_lt ((hG.continuous.sub continuous_const).abs) continuous_const
  have hSO₁ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆
      {z : EuclideanSpace ℝ (Fin (m + 1)) | |G z - c| < κ / 2} := by
    intro x hx
    change |G x - c| < κ / 2
    rw [hGc x (mem_sphere_zero_iff_norm.mp hx), sub_self, abs_zero]
    linarith
  obtain ⟨δ₁', hδ₁', hthick₁⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).exists_thickening_subset_open hO₁ hSO₁
  set δ₁ := min δ₁' (δ₀ / 4) with hδ₁def
  have hδ₁ : 0 < δ₁ := lt_min hδ₁' (by positivity)
  have hδ₁4 : δ₁ ≤ δ₀ / 4 := min_le_right _ _
  let Ann : Set (EuclideanSpace ℝ (Fin (m + 1))) := {z | 1 - δ₁ < ‖z‖ ∧ ‖z‖ < 1 + δ₁}
  have hAnn : IsOpen Ann :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAnnp : ∀ z ∈ Ann, z ≠ 0 ∧ |G z - c| < κ / 2 ∧ b ≤ ‖z‖ := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h0
      have := hz.1
      rw [h0, norm_zero] at this
      linarith
    refine ⟨hz0, ?_, by rw [hbdef]; linarith [hz.1]⟩
    have habs : |‖z‖ - 1| < δ₁' := by
      rw [abs_lt]
      constructor <;> linarith [hz.1, hz.2, min_le_left δ₁' (δ₀ / 4)]
    exact hthick₁ (mem_thickening_sphere_of_abs_norm_sub_one_lt hz0 habs)
  have hSAnn : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆ Ann := by
    intro x hx
    have hx1 := mem_sphere_zero_iff_norm.mp hx
    exact ⟨by rw [hx1]; linarith, by rw [hx1]; linarith⟩
  have hpos : ∀ z ∈ Ann, 0 ≤ 1 + κ⁻¹ * (G z - c) := by
    intro z hz
    have h1 := (abs_lt.mp (hAnnp z hz).2.1).1
    have h2 : -(κ / 2) * κ⁻¹ ≤ (G z - c) * κ⁻¹ :=
      mul_le_mul_of_nonneg_right h1.le (inv_pos.mpr hκ).le
    have h3 : -(κ / 2) * κ⁻¹ = -(1 / 2) := by field_simp
    rw [h3] at h2
    linarith [mul_comm (G z - c) κ⁻¹]
  -- 6. the inverse germ `F`
  let φA := DifferentialGeometry.Topology.PartialDiffeomorph.restrict φ Ann hAnn
  have hφAapp : ∀ z, φA z = h z := fun z => congrFun hφh z
  let F := φA.symm
  have hSsrc : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, x ∈ φA.source :=
    fun x hx => ⟨hφs hx, hSAnn hx⟩
  have hSF : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆ F.source := by
    intro x hx
    have h1 := φA.toPartialEquiv.map_source (hSsrc x hx)
    change φA x ∈ φA.target at h1
    rw [hφAapp, hhS x (mem_sphere_zero_iff_norm.mp hx)] at h1
    exact h1
  have hFfix : EqOn F id (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
    intro x hx
    have h1 := φA.toPartialEquiv.left_inv (hSsrc x hx)
    change φA.symm (φA x) = x at h1
    rw [hφAapp, hhS x (mem_sphere_zero_iff_norm.mp hx)] at h1
    exact h1
  have hFspec : ∀ w ∈ F.source, F w ∈ φ.source ∧ F w ∈ Ann ∧ h (F w) = w := by
    intro w hw
    have h1 := φA.toPartialEquiv.map_target hw
    have h2 := φA.toPartialEquiv.right_inv hw
    change φA (F w) = w at h2
    rw [hφAapp] at h2
    exact ⟨h1.1, h1.2, h2⟩
  have hFmap : MapsTo F ((ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)ᶜ ∩ F.source)
      (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)ᶜ := by
    rintro w ⟨hw1, hws⟩
    obtain ⟨hzφ, hzA, hhz⟩ := hFspec w hws
    intro hzb
    have hz1 : ‖F w‖ < 1 := mem_ball_zero_iff.mp hzb
    have hw1' : 1 ≤ ‖w‖ := by
      by_contra hcon
      exact hw1 (mem_ball_zero_iff.mpr (lt_of_not_ge hcon))
    obtain ⟨hz0, -, hzb'⟩ := hAnnp _ hzA
    have hzW : (⟨F w, hz1.le⟩ : ClosedCell (m + 1)) ∈ W :=
      hcollar _ (by change 1 - δ₀ < ‖F w‖; rw [hbdef] at hzb'; linarith)
    have hGz : G (F w) ≤ c := by
      rw [show G (F w) = u ⟨F w, hz1.le⟩ from hGeq ⟨F w, hz1.le⟩ hzb']
      exact hule _ hzW
    have hnw : ‖w‖ = 1 + κ⁻¹ * (G (F w) - c) := by
      have h1 := norm_boundaryPolarMap (κ := κ) hz0 (hpos _ hzA)
      change ‖h (F w)‖ = _ at h1
      rw [hhz] at h1
      exact h1
    have hGz' : G (F w) = c := by
      have hk : 0 < κ⁻¹ := inv_pos.mpr hκ
      have h1 : 0 ≤ κ⁻¹ * (G (F w) - c) := by linarith
      have h2 : 0 ≤ G (F w) - c := nonneg_of_mul_nonneg_right (by linarith [mul_comm κ⁻¹ (G (F w) - c)]) hk
      linarith
    set n := ‖F w‖⁻¹ • F w with hndef
    have hn1 : ‖n‖ = 1 := by
      rw [hndef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
    have hhz' : h (F w) = n := by
      change boundaryPolarMap G c κ (F w) = n
      rw [boundaryPolarMap, hGz', sub_self, mul_zero, add_zero, one_smul]
    have hnφ : n ∈ φ.source := hφs (mem_sphere_zero_iff_norm.mpr hn1)
    have heq : F w = n := by
      apply φ.toPartialEquiv.injOn hzφ hnφ
      rw [hφh, hhz', hhS n hn1]
    have : ‖F w‖ = 1 := by rw [heq, hn1]
    linarith
  -- 7. the ambient isotopy and the cell diffeomorphism
  have hOo : IsOpen {x : EuclideanSpace ℝ (Fin (m + 1)) | 1 - η < ‖x‖} :=
    isOpen_lt continuous_const continuous_norm
  have hSO : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆
      {x : EuclideanSpace ℝ (Fin (m + 1)) | 1 - η < ‖x‖} := fun x hx => by
    change 1 - η < ‖x‖
    rw [mem_sphere_zero_iff_norm.mp hx]
    linarith
  obtain ⟨V, hVo, hSV, hVF, Φ, -, -, -, hΦ1, hfixΦ, hball, L, -, hLO, hLid⟩ :=
    F.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball one_pos hSF
      hFfix hFmap hOo hSO
  obtain ⟨δ₂, hδ₂, hthickV⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).exists_thickening_subset_open hVo hSV
  let ψ := closedCellDiffeomorph (m := m) (Φ 1) (hball 1 ⟨zero_le_one, le_rfl⟩)
  set δ : ℝ := min δ₂ (η / 2) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₂ (by positivity)
  have hδη : δ < η := (min_le_right _ _).trans_lt (by linarith)
  have hδ2 : δ ≤ δ₂ := min_le_left _ _
  refine ⟨δ, hδ0, hδη, ψ, ?_, ?_, ?_⟩
  · intro z hz
    have hz1 : ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := z.2
    have hz0 : (z : EuclideanSpace ℝ (Fin (m + 1))) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz
      linarith [min_le_right δ₂ (η / 2)]
    have hzV : (z : EuclideanSpace ℝ (Fin (m + 1))) ∈ V :=
      hthickV (mem_thickening_sphere_of_abs_norm_sub_one_lt hz0 (by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith))
    have hψz : ((ψ z : ClosedCell (m + 1)) : EuclideanSpace ℝ (Fin (m + 1))) = F z := hΦ1 hzV
    obtain ⟨-, hFA, hhF⟩ := hFspec _ (hVF hzV)
    obtain ⟨hF0, -, hFb⟩ := hAnnp _ hFA
    have hψb : b ≤ ‖((ψ z : ClosedCell (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
      rw [hψz]
      exact hFb
    refine ⟨hcollar _ (by rw [hbdef] at hψb; linarith), ?_⟩
    rw [← hGeq _ hψb, hψz]
    have hnz : ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 + κ⁻¹ * (G (F z) - c) := by
      have h1 := norm_boundaryPolarMap (κ := κ) hF0 (hpos _ hFA)
      change ‖h (F z)‖ = _ at h1
      rw [hhF] at h1
      exact h1
    rw [hnz]
    field_simp
    ring
  · intro z hz
    apply Subtype.ext
    exact (hfixΦ 1).1 (mem_sphere_zero_iff_norm.mpr hz)
  · intro z hz
    apply Subtype.ext
    have hzL : (z : EuclideanSpace ℝ (Fin (m + 1))) ∈ Lᶜ := fun hL => by
      have := hLO hL
      change 1 - η < ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ at this
      linarith
    exact (hLid 1).1 hzL

/-- **R1 item (3) (review 44): polar re-modelling of a disk along an arbitrary regular
boundary-defining function.** Let `S` be a manifold with boundary with a diffeomorphism
`D₀ : ClosedCell (m + 1) ≃ₘ S`, and `T : S → ℝ` smooth on an open neighbourhood `V` of `∂S`, with
`T = c` on `∂S`, `T ≤ c` on `V` and `dT ≠ 0` on `∂S`. For every `κ > 0` and `0 < η < 1` there are
`δ ∈ (0, η)` and a diffeomorphism `D : ClosedCell (m + 1) ≃ₘ S` with
`T (D z) = c + κ (‖z‖ - 1)` for `‖z‖ > 1 - δ` (`T ∘ D (r θ̂)` is radial near the boundary, with
the standard angle), `D = D₀` on the boundary sphere, and `D = D₀` on `‖z‖ ≤ 1 - η`. -/
theorem exists_diskDiffeomorph_polar_of_boundaryDefining {m : ℕ} {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) S]
    (D₀ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ S) {T : S → ℝ} {V : Set S}
    (hV : IsOpen V) (hbV : ∀ y : S, (𝓡∂ (m + 1)).IsBoundaryPoint y → y ∈ V)
    (hT : ContMDiffOn (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ T V) {c : ℝ}
    (hTc : ∀ y : S, (𝓡∂ (m + 1)).IsBoundaryPoint y → T y = c) (hTle : ∀ y ∈ V, T y ≤ c)
    (hreg : ∀ y : S, (𝓡∂ (m + 1)).IsBoundaryPoint y → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) T y ≠ 0)
    {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ ∃ D : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ S,
      (∀ z : ClosedCell (m + 1), 1 - δ < ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ →
        D z ∈ V ∧ T (D z) = c + κ * (‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ - 1)) ∧
      (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 → D z = D₀ z) ∧
      (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 - η →
        D z = D₀ z) := by
  have hbd : ∀ z : ClosedCell (m + 1),
      (𝓡∂ (m + 1)).IsBoundaryPoint z ↔ ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
    fun z => Set.ext_iff.mp (closedCell_boundary_eq_sphere m) z
  have hbdD : ∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 →
      (𝓡∂ (m + 1)).IsBoundaryPoint (D₀ z) := fun z hz =>
    ((D₀.isLocalDiffeomorph z).isBoundaryPoint_iff (by simp)).mp ((hbd z).mpr hz)
  have hW : IsOpen (D₀ ⁻¹' V) := hV.preimage D₀.continuous
  have hu : ContMDiffOn (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ (T ∘ D₀) (D₀ ⁻¹' V) :=
    hT.comp D₀.contMDiff.contMDiffOn (fun _ hz => hz)
  have hureg : ∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 →
      mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) (T ∘ D₀) z ≠ 0 := by
    intro z hz h0
    have hy := hbdD z hz
    have hTd : MDifferentiableAt (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) T (D₀ z) :=
      ((hT _ (hbV _ hy)).contMDiffAt (hV.mem_nhds (hbV _ hy))).mdifferentiableAt (by simp)
    have hDd : MDifferentiableAt (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) D₀ z :=
      D₀.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    rw [mfderiv_comp z hTd hDd] at h0
    obtain ⟨e, he⟩ := (D₀.isLocalDiffeomorph z).isInvertible_mfderiv (by simp)
    apply hreg _ hy
    ext v
    have h1 := congrArg (fun L => L (e.symm v)) h0
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at h1
    rw [← he, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h1
    rw [h1, zero_apply]
  obtain ⟨δ, hδ0, hδη, ψ, hψ, hψS, hψη⟩ := exists_closedCellDiffeomorph_polar hW
    (fun z hz => hbV _ (hbdD z hz)) hu (fun z hz => hTc _ (hbdD z hz)) (fun z hz => hTle _ hz)
    hureg hκ hη0 hη1
  refine ⟨δ, hδ0, hδη, ψ.trans D₀, hψ, ?_, ?_⟩
  · intro z hz
    change D₀ (ψ z) = D₀ z
    rw [hψS z hz]
  · intro z hz
    change D₀ (ψ z) = D₀ z
    rw [hψη z hz]

/-- **Item (3), two-dimensional verbatim form, in polar coordinates.** For a fibre `S` with a disk
model `D₀` and a smooth `T` near `∂S` with `∂S = {T = c}` (on `V`), `T ≤ c` and `dT ≠ 0` on `∂S`:
a disk model `D`, equal to `D₀` on the rim and on `‖z‖ ≤ 1 - η`, with
`T (D (r θ̂)) = c + κ (r - 1)` for every unit vector `θ̂` and `1 - δ < r ≤ 1`. -/
theorem exists_diskDiffeomorph_polar_radial {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] (D₀ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ S) {T : S → ℝ}
    {V : Set S} (hV : IsOpen V) (hbV : ∀ y : S, (𝓡∂ 2).IsBoundaryPoint y → y ∈ V)
    (hT : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞ T V) {c : ℝ}
    (hlevel : ∀ y ∈ V, ((𝓡∂ 2).IsBoundaryPoint y ↔ T y = c)) (hTle : ∀ y ∈ V, T y ≤ c)
    (hreg : ∀ y : S, (𝓡∂ 2).IsBoundaryPoint y → mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) T y ≠ 0)
    {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ ∃ D : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ S,
      (∀ (θ : EuclideanSpace ℝ (Fin 2)), ‖θ‖ = 1 → ∀ r : ℝ, 1 - δ < r → ∀ z : ClosedCell 2,
        (z : EuclideanSpace ℝ (Fin 2)) = r • θ → D z ∈ V ∧ T (D z) = c + κ * (r - 1)) ∧
      (∀ z : ClosedCell 2, ‖(z : EuclideanSpace ℝ (Fin 2))‖ = 1 → D z = D₀ z) ∧
      (∀ z : ClosedCell 2, ‖(z : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 - η → D z = D₀ z) := by
  obtain ⟨δ, hδ0, hδη, D, hD, hDS, hDη⟩ := exists_diskDiffeomorph_polar_of_boundaryDefining
    (m := 1) D₀ hV hbV hT (fun y hy => (hlevel y (hbV y hy)).mp hy) hTle hreg hκ hη0 hη1
  refine ⟨δ, hδ0, hδη, D, ?_, hDS, hDη⟩
  intro θ hθ r hr z hz
  have hr0 : 0 ≤ r := by linarith
  have hnz : ‖(z : EuclideanSpace ℝ (Fin 2))‖ = r := by
    rw [hz, norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]
  have h := hD z (by rw [hnz]; exact hr)
  rw [hnz] at h
  exact h

end Cell

end DifferentialGeometry.Topology.Manifold
