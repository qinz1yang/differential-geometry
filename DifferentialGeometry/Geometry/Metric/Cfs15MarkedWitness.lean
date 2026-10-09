import DifferentialGeometry.Geometry.Metric.Cfs15StageOutput
import DifferentialGeometry.Geometry.Fibration.GenericMarkedPatchChart

/-!
# CGP04–CGP05 on a native stage output: marker exclusion and (MW) witnesses (kernel form)

Blueprint `master207B.tex`, CGP04 (`lem:fibration-smoothed-locus-marker-exclusion`,
B:4057–4082) and CGP05 (`lem:fibration-marked-smoothed-witness`, B:4084–4128); external draft 59
§4 "第二步" (D59-5). Everything is stated on ONE `Cfs15StageOutput` `O` (its selection `I`, its
zero set `Z`, its planes `P`, its radius `r = Σ ρ ∘ sel`) and abstract source data (`F' : M → H`,
block formula `u(F' q) = Rζ(q) η(q)`, `v(F' q) = Rζ(q)`, scale on the support). The statements cover
the WHOLE zero set: no point is assumed to come from a local section.

* `marker_eq_zero_of_contributors_BAS`: if every selected centre `i` whose weight can be nonzero at
  `w ∈ Z` (`w ∈ B(i, 80ε⁻¹r_i)`) has `v(i) = 0` and `P_i ⊆ ker v`, then `v(w) = 0` (CFS24's
  pointwise spectral calculation, `affine_marker_weighted_normal_spectral_section`).
* `cgp04_kernel_BAS` (CGP04, marker form): if `v(i) = 0`, `P_i ⊆ ker v` at every cloud point with
  `r_i > τ`, then `v = 0` on `Z ∩ B(y, 20ε⁻¹r_y)` for every selected `y` with `r_y > (5/3)τ`
  (the contributing centres are CFS07-comparable, `|i - y| < 128ε⁻¹ max(r_i, r_y)`). These balls
  cover `Z` (`exists_selected_mem_ball_BAS`).
* `marker_vector_of_close_block_norm_BAS`: the vector form of `marker_vector_of_close_block`.
* `cgp05_kernel_BAS` (CGP05): for EVERY `w ∈ V⁰ = {w ∈ Z | v(w) > .9R, ‖u(w)‖ < 5.5ℓR}` there is
  `q ∈ Ã` with `ζ(q) > .899`, `‖η(q)‖ < 6.2ℓ` and `‖w - F'(q)‖ < (25/12)εΣR` (MW). Inputs: CFS14's
  witness (`near_cloud`), CFS07's ratio (`hmcb`), the preimage ratio on `S̃`, CGP04.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open DifferentialGeometry.Geometry.Collapse

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The selected balls `B(y, 20ε⁻¹r_y)`, `y ∈ I`, cover the zero set (it lies in the tube). -/
theorem exists_selected_mem_ball_BAS {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ}
    {P : H → Submodule ℝ H} (O : Cfs15StageOutput k K ε cw S T r P) {w : H} (hw : w ∈ O.Z) :
    ∃ y ∈ O.I, w ∈ ball y (20 * ε⁻¹ * r y) := by
  obtain ⟨y, hy, hwy⟩ := mem_iUnion₂.mp hw.1
  exact ⟨y, hy, hwy⟩

/-- **CFS24's pointwise calculation at a zero.** If every selected centre `i` with
`w ∈ B(i, 80ε⁻¹r_i)` has `v(i) = 0` and `P_i ⊆ ker v`, then `v(w) = 0` for `w ∈ Z`. -/
theorem marker_eq_zero_of_contributors_BAS {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ}
    {P : H → Submodule ℝ H} (O : Cfs15StageOutput k K ε cw S T r P) (v : H →L[ℝ] ℝ) {w : H}
    (hw : w ∈ O.Z)
    (h : ∀ i ∈ O.I, w ∈ ball i (80 * ε⁻¹ * r i) →
      v i = 0 ∧ P i ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) :
    v w = 0 := by
  set Kv : Submodule ℝ H := (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ with hKv
  have hKperp : Kvᗮ = LinearMap.ker (v : H →ₗ[ℝ] ℝ) := by
    rw [hKv, Submodule.orthogonal_orthogonal]
  have hcontrib : ∀ i ∈ O.hI.toFinset, (∃ z ∈ ({w} : Set H), cfs15Weight_C15 ε r O.hI i z ≠ 0) →
      v i = 0 ∧ P i ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ) := by
    rintro i hi ⟨z, hz, hne⟩
    rw [mem_singleton_iff] at hz
    subst hz
    have hiI := O.hI.mem_toFinset.mp hi
    exact h i hiI (cfs15Weight_mem_ball_C15 O.eps_pos O.hI (O.radius_pos_I i hiI) hne)
  have hloc := Submodule.affine_marker_weighted_normal_spectral_section O.hI.toFinset {w}
    (cfs15Weight_C15 ε r O.hI)
    (fun y hy => by
      rw [mem_singleton_iff] at hy
      rw [hy]
      exact cfs15Weight_sum_C15 O.eps_pos O.hI O.radius_pos_I hw.1) P (fun i => i) Kv 0
    (fun i hi hex => by
      rw [Submodule.starProjection_apply_eq_zero_iff, hKperp]
      exact (hcontrib i hi hex).1)
    (fun i hi hex => by
      rw [hKperp]
      exact (hcontrib i hi hex).2) w (mem_singleton w)
  have h0 : Kv.starProjection (cfs15Section_C15 ε r P O.hI w) = Kv.starProjection w - 0 := hloc
  rw [hw.2, map_zero, sub_zero] at h0
  have hmem : w ∈ Kvᗮ := (Submodule.starProjection_apply_eq_zero_iff Kv).mp h0.symm
  rw [hKperp] at hmem
  exact hmem

/-- **CGP04 (marker form, kernel).** If every cloud point `i` with `r_i > τ` has `v(i) = 0` and
`P_i ⊆ ker v` (no tiny marker at comparable centres), then for every selected `y` with
`r_y > (5/3)τ`, `v = 0` on `Z ∩ B(y, 20ε⁻¹r_y)`. -/
theorem cgp04_kernel_BAS {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ}
    {P : H → Submodule ℝ H} (O : Cfs15StageOutput k K ε cw S T r P) (v : H →L[ℝ] ℝ)
    (hST : S ⊆ T)
    (hmcb : ∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * ε⁻¹ * max (r y) (r x) → r y ≤ 5 / 3 * r x)
    {τ : ℝ} (hvanish : ∀ i ∈ S, τ < r i → v i = 0 ∧ P i ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ))
    {y : H} (hy : y ∈ O.I) (hry : 5 / 3 * τ < r y) {w : H} (hw : w ∈ O.Z)
    (hwy : w ∈ ball y (20 * ε⁻¹ * r y)) : v w = 0 := by
  refine marker_eq_zero_of_contributors_BAS O v hw fun i hi hwi => hvanish i (O.I_subset hi) ?_
  have hε := O.eps_pos
  have hri := O.radius_pos_I i hi
  have hryp := O.radius_pos_I y hy
  have hdist : dist y i ≤ 128 * ε⁻¹ * max (r y) (r i) := by
    have h1 : dist y i ≤ dist w y + dist w i := by
      have := dist_triangle y w i
      rw [dist_comm y w] at this
      exact this
    have h2 : dist w y < 20 * ε⁻¹ * r y := hwy
    have h3 : dist w i < 80 * ε⁻¹ * r i := hwi
    have hεi : 0 < ε⁻¹ := inv_pos.mpr hε
    have h4 : 20 * ε⁻¹ * r y ≤ 20 * ε⁻¹ * max (r y) (r i) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have h5 : 80 * ε⁻¹ * r i ≤ 80 * ε⁻¹ * max (r y) (r i) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    have h6 : 0 ≤ ε⁻¹ * max (r y) (r i) := mul_nonneg hεi.le (hri.le.trans (le_max_right _ _))
    nlinarith
  have hcmp := hmcb i (hST (O.I_subset hi)) y (hST (O.I_subset hy)) hdist
  linarith

/-- The vector form of FC01's marker reading of a close block: if `|Rζ − v_w| ≤ d`,
`‖(Rζ)η − u_w‖ ≤ d`, `d < R/1000`, `v_w > .9R`, `‖u_w‖ < 5.5ℓR` (`ℓ ≥ 1`), then `ζ > .899` and
`‖η‖ < 6.2ℓ`. -/
theorem marker_vector_of_close_block_norm_BAS {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {R ℓ ζ d vw : ℝ} {η uw : E} (hR : 0 < R) (hℓ : 1 ≤ ℓ)
    (hu : ‖(R * ζ) • η - uw‖ ≤ d) (hv : |R * ζ - vw| ≤ d) (hd : d < R / 1000)
    (hvw : 9 / 10 * R < vw) (huw : ‖uw‖ < 11 / 2 * ℓ * R) :
    899 / 1000 < ζ ∧ ‖η‖ < 31 / 5 * ℓ := by
  have hRζ : 899 / 1000 * R < R * ζ := by
    have := (abs_le.mp hv).1
    linarith
  have hζ : 899 / 1000 < ζ := by nlinarith
  refine ⟨hζ, ?_⟩
  have hRζ0 : 0 < R * ζ := by nlinarith
  have hprod : ‖η‖ * (R * ζ) < 11 / 2 * ℓ * R + R / 1000 := by
    have h1 : ‖(R * ζ) • η‖ ≤ ‖uw‖ + d := by
      have := norm_sub_norm_le ((R * ζ) • η) uw
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRζ0] at h1
    linarith
  by_contra hcon
  have hge : 31 / 5 * ℓ ≤ ‖η‖ := le_of_not_gt hcon
  have h2 : 31 / 5 * ℓ * (899 / 1000 * R) ≤ ‖η‖ * (R * ζ) :=
    mul_le_mul hge hRζ.le (by positivity) (norm_nonneg η)
  nlinarith

/-- **CGP05 (kernel).** For the output `O` with radius `r = Σ ρ ∘ sel`, abstract source data
(`F'`, block formula, scale `≤ 5R/4` on the support of `ζ`), CFS07's ratio on `S̃`, the preimage
ratio on `S̃`, and no tiny marker at comparable cloud points: EVERY `w ∈ V⁰` has an original
witness `q ∈ Ã` with `ζ(q) > .899`, `‖η(q)‖ < 6.2ℓ` and (MW) `‖w − F'(q)‖ < (25/12)εΣR`. -/
theorem cgp05_kernel_BAS {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k K : ℕ}
    {ε cw Sg : ℝ} {S T : Set H} {sel : H → M} {ρM : M → ℝ} {P : H → Submodule ℝ H}
    (O : Cfs15StageOutput k K ε cw S T (fun x => Sg * ρM (sel x)) P)
    (F' : M → H) (At : Set M) (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1) (v : H →L[ℝ] ℝ) (hv : ‖v‖ ≤ 1)
    (η : M → E) (ζ : M → ℝ) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ) (hSg : 0 < Sg)
    (hSgε : Sg ≤ ε / 640) (hρpos : ∀ q, 0 < ρM q)
    (hblock : ∀ q, u (F' q) = (R * ζ q) • η q ∧ v (F' q) = R * ζ q)
    (hscale : ∀ q, ζ q ≠ 0 → ρM q ≤ 5 / 4 * R)
    (hT : ∀ z ∈ T, ∃ q ∈ At, F' q = z)
    (hratioT : ∀ z ∈ T, ∀ q ∈ At, F' q = z → ρM (sel z) ≤ 5 / 3 * ρM q)
    (hmcb : ∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * ε⁻¹ * max (Sg * ρM (sel y)) (Sg * ρM (sel x)) →
      Sg * ρM (sel y) ≤ 5 / 3 * (Sg * ρM (sel x)))
    (hST : S ⊆ T)
    (hvanish : ∀ i ∈ S, 25 / 3 * R < ρM (sel i) →
      v i = 0 ∧ P i ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) :
    ∀ w ∈ markedPatch_BPRE O.Z u v R ℓ, ∃ q ∈ At, 899 / 1000 < ζ q ∧ ‖η q‖ < 31 / 5 * ℓ ∧
      ‖w - F' q‖ < 25 / 12 * ε * Sg * R := by
  intro w hw
  obtain ⟨hwZ, hvw, huw⟩ := hw
  have hε := O.eps_pos
  have hε1 := O.eps_le
  have hεi : 0 < ε⁻¹ := inv_pos.mpr hε
  -- CGP04: the selected ball containing `w` has `ρ(sel y) ≤ (125/9)R`
  obtain ⟨y, hyI, hwy⟩ := exists_selected_mem_ball_BAS O hwZ
  have hy : ρM (sel y) ≤ 125 / 9 * R := by
    by_contra hcon
    have hlt : 5 / 3 * (Sg * (25 / 3 * R)) < Sg * ρM (sel y) := by
      have : 125 / 9 * R < ρM (sel y) := lt_of_not_ge hcon
      nlinarith
    have h0 := cgp04_kernel_BAS O v hST hmcb (τ := Sg * (25 / 3 * R))
      (fun i hi hri => hvanish i hi (by
        have : Sg * (25 / 3 * R) < Sg * ρM (sel i) := hri
        exact lt_of_mul_lt_mul_left this hSg.le)) hyI hlt hwZ hwy
    linarith
  -- CFS14's witness `z ∈ S̃` and CFS07's ratio
  have hnear := O.near_cloud hwZ
  obtain ⟨z, hzT, hwz⟩ := mem_iUnion₂.mp hnear
  have hwz' : dist w z < ε * (Sg * ρM (sel z)) := hwz
  have hyT : y ∈ T := hST (O.I_subset hyI)
  have hrz := hρpos (sel z)
  have hry := hρpos (sel y)
  have hdist : dist z y ≤ 128 * ε⁻¹ * max (Sg * ρM (sel z)) (Sg * ρM (sel y)) := by
    have h1 : dist z y ≤ dist w z + dist w y := by
      have := dist_triangle z w y
      rw [dist_comm z w] at this
      exact this
    have h2 : dist w y < 20 * ε⁻¹ * (Sg * ρM (sel y)) := hwy
    have hm1 : Sg * ρM (sel z) ≤ max (Sg * ρM (sel z)) (Sg * ρM (sel y)) := le_max_left _ _
    have hm2 : Sg * ρM (sel y) ≤ max (Sg * ρM (sel z)) (Sg * ρM (sel y)) := le_max_right _ _
    have hmpos : 0 < max (Sg * ρM (sel z)) (Sg * ρM (sel y)) :=
      lt_of_lt_of_le (mul_pos hSg hrz) hm1
    have hεε : ε ≤ 108 * ε⁻¹ := by
      rw [le_mul_inv_iff₀ hε]
      nlinarith
    have h3 : ε * (Sg * ρM (sel z)) ≤ 108 * ε⁻¹ * max (Sg * ρM (sel z)) (Sg * ρM (sel y)) :=
      mul_le_mul hεε hm1 (mul_pos hSg hrz).le (by positivity)
    have h4 : 20 * ε⁻¹ * (Sg * ρM (sel y)) ≤
        20 * ε⁻¹ * max (Sg * ρM (sel z)) (Sg * ρM (sel y)) :=
      mul_le_mul_of_nonneg_left hm2 (by positivity)
    linarith
  have hcmp := hmcb y hyT z hzT hdist
  have hz1 : ρM (sel z) ≤ 625 / 27 * R := by
    have : Sg * ρM (sel z) ≤ Sg * (5 / 3 * ρM (sel y)) := by linarith
    have h' := le_of_mul_le_mul_left this hSg
    linarith
  -- the first proximity `‖w − z‖ < R/1000`
  have hd1 : ‖w - z‖ < R / 1000 := by
    rw [← dist_eq_norm]
    have h1 : ε * (Sg * ρM (sel z)) ≤ ε * ((ε / 640) * (625 / 27 * R)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hSgε hz1 hrz.le (by positivity)) hε.le
    have h2 : ε * ε ≤ 1 / 10 * (1 / 10) := mul_le_mul hε1 hε1 hε.le (by norm_num)
    have h3 : ε * ((ε / 640) * (625 / 27 * R)) = ε * ε * (625 / 17280 * R) := by ring
    have h4 : ε * ε * (625 / 17280 * R) ≤ 1 / 10 * (1 / 10) * (625 / 17280 * R) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    nlinarith
  -- the original witness `q`
  obtain ⟨q, hqA, hqz⟩ := hT z hzT
  have hblk := hblock q
  rw [hqz] at hblk
  have hvclose : |R * ζ q - v w| ≤ ‖w - z‖ := by
    have h1 : |v z - v w| = ‖v (z - w)‖ := by rw [map_sub, Real.norm_eq_abs]
    rw [← hblk.2, h1]
    calc ‖v (z - w)‖ ≤ ‖v‖ * ‖z - w‖ := v.le_opNorm _
      _ ≤ 1 * ‖z - w‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
      _ = ‖w - z‖ := by rw [one_mul, norm_sub_rev]
  have huclose : ‖(R * ζ q) • η q - u w‖ ≤ ‖w - z‖ := by
    rw [← hblk.1, ← map_sub]
    calc ‖u (z - w)‖ ≤ ‖u‖ * ‖z - w‖ := u.le_opNorm _
      _ ≤ 1 * ‖z - w‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      _ = ‖w - z‖ := by rw [one_mul, norm_sub_rev]
  obtain ⟨hζ, hη⟩ := marker_vector_of_close_block_norm_BAS hR hℓ huclose hvclose hd1 hvw huw
  refine ⟨q, hqA, hζ, hη, ?_⟩
  -- the improved proximity (MW)
  have hq := hscale q (by linarith)
  have hsz := hratioT z hzT q hqA hqz
  have hz2 : ρM (sel z) ≤ 25 / 12 * R := by linarith
  rw [hqz, ← dist_eq_norm]
  have h1 : ε * (Sg * ρM (sel z)) ≤ ε * (Sg * (25 / 12 * R)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz2 hSg.le) hε.le
  nlinarith

end GC.MetricGeometry
