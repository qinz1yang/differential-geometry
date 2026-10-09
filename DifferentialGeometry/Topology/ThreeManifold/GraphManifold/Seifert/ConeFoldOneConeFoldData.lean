import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeWalls

/-!
# The fold data of the one-cone shapes `(p, ⊤, ⊤)`

Lane A4b2, milestones 6–7 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`,
§0, §8). For a shape with a cusp at `0` (`θ₂ = 0`) and a cone of order `p` at `v₁`
(`θ₁ p = π`, so `p ≥ 2` and the shape is admissible, `admissible_of_mul_eq_pi`) the fold is the
mirror `f = -conj ∘ F` of the core-replaced map `F` of `exists_foldCore`. It satisfies the frozen
interface `ConeShape.FoldData` of `SF/ConeFoldSpec.lean` (`oneConeFoldData`):
* `U` is the set of points near which `F` is smooth with nonzero Jacobian (off `v₁`), cut down to
  positive Jacobian of `f` off `v₁`; the triangle lies in `U` because the Jacobian of `f` is
  continuous and nonzero on the preconnected set `T \ {v₁}` (`isPreconnected_triangle_diff`) and
  positive near `v₁`, where `f` is the branched model `coneApexOne p` (`det_pos_on_triangle`);
* the wall neighbourhoods are `U ∩ refl⁻¹ U ∩ wallSet ∩ refl⁻¹ wallSet` outside the core disc,
  on which the wall identities of `foldE` hold;
* `bijOn_f` comes from A4Q's `bijOn_of_local'` with the wall values of `foldE`;
* `‖f‖ = outerProfile K Y₁ Y₂ (Im z)` above height `2` and `‖f + 3/2‖ = G(η₀)` below
  `η₀ = foldH/2` (the core lies below height `2` and above `η₀ = foldH/2`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

open ConeLayout

namespace ConeShape

variable (σ : ConeShape)

/-! ### Admissibility of the one-cone shapes -/

theorem two_le_of_mul_eq_pi {p : ℕ} (hpθ : σ.θ₁ * p = Real.pi) : 2 ≤ p := by
  by_contra h
  push Not at h
  have hp1 : (p : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 h
  have := σ.θ₁_le
  have h0 := σ.θ₁_pos
  have : σ.θ₁ * p ≤ σ.θ₁ := by nlinarith [Nat.cast_nonneg (α := ℝ) p]
  linarith [Real.pi_pos]

theorem admissible_of_mul_eq_pi {p : ℕ} (hpθ : σ.θ₁ * p = Real.pi) :
    Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁ := by
  have hp := σ.two_le_of_mul_eq_pi hpθ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hθ : σ.θ₁ = Real.pi / p := by field_simp; linarith
  rcases (show p = 2 ∨ 3 ≤ p by omega) with h | h
  · left
    rw [hθ, h]
    push_cast
    exact Real.cos_pi_div_two
  · right
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast h
    have hle : σ.θ₁ ≤ Real.pi / 3 := by
      rw [hθ]; exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h3
    have := Real.cos_le_cos_of_nonneg_of_le_pi σ.θ₁_pos.le (by linarith [Real.pi_pos]) hle
    rw [Real.cos_pi_div_three] at this
    exact this

/-! ### The triangle minus `v₁` is preconnected -/

theorem isPreconnected_triangle_diff : IsPreconnected (σ.triangle \ {σ.vertexOne}) := by
  have hW := σ.width_pos
  have hv := σ.vertexOne_im_pos
  have hv1 : σ.vertexOne.im ≤ 1 / 4 := by
    rw [vertexOne_im]; linarith [Real.sin_le_one σ.θ₁]
  set pt : ℝ → ℝ → ℂ := fun x t => (x : ℂ) + (t : ℂ) * I with hpt
  have hpt_re : ∀ x t, (pt x t).re = x := fun x t => by simp [hpt]
  have hpt_im : ∀ x t, (pt x t).im = t := fun x t => by simp [hpt]
  have hcx : ∀ x, Continuous (pt x) := fun x => by simp only [hpt]; fun_prop
  have hct : ∀ t, Continuous fun x => pt x t := fun t => by simp only [hpt]; fun_prop
  set vS : ℝ → ℝ → ℝ → Set ℂ := fun x a b => pt x '' Icc a b with hvS
  set hS : ℝ → ℝ → ℝ → Set ℂ := fun y a b => (fun s => pt s y) '' uIcc a b with hhS
  have hvSc : ∀ x a b, IsPreconnected (vS x a b) := fun x a b =>
    isPreconnected_Icc.image _ (hcx x).continuousOn
  have hhSc : ∀ y a b, IsPreconnected (hS y a b) := fun y a b =>
    isPreconnected_uIcc.image _ (hct y).continuousOn
  have hw2 : ∀ w : ℂ, 3 ≤ w.im → 0 < σ.wallSide 2 w := by
    intro w hw
    change 0 < (w.re - σ.centre) ^ 2 + w.im ^ 2 - 1 / 16
    nlinarith [sq_nonneg (w.re - σ.centre)]
  have htop : ∀ w : ℂ, 3 ≤ w.im → 0 ≤ w.re → w.re ≤ σ.width →
      w ∈ σ.triangle \ {σ.vertexOne} := by
    intro w hw h0 h1
    refine ⟨⟨by linarith, fun i => ?_⟩, fun h => ?_⟩
    · fin_cases i
      · exact h0
      · change 0 ≤ σ.width - w.re; linarith
      · exact (hw2 w hw).le
    · rw [mem_singleton_iff] at h
      rw [h] at hw
      linarith
  refine isPreconnected_of_forall (pt (σ.width / 2) 3) fun z hz => ?_
  obtain ⟨hzT, hzv⟩ := hz
  rw [mem_singleton_iff] at hzv
  set Y := max z.im 3 with hY
  have hzY : z.im ≤ Y := le_max_left _ _
  have h3Y : 3 ≤ Y := le_max_right _ _
  have hx0 := σ.re_nonneg_of_triangle hzT
  have hxW := σ.re_le_width_of_mem_triangle hzT
  set P := (vS z.re z.im Y ∪ hS Y z.re (σ.width / 2)) ∪ vS (σ.width / 2) 3 Y with hP
  refine ⟨P, ?_, Or.inr ⟨3, ⟨le_rfl, h3Y⟩, rfl⟩, Or.inl (Or.inl ⟨z.im, ⟨le_rfl, hzY⟩, ?_⟩), ?_⟩
  · rintro w ((⟨t, ⟨ht1, ht2⟩, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨t, ⟨ht1, ht2⟩, rfl⟩)
    · refine ⟨⟨by rw [hpt_im]; linarith [hzT.1], fun i => ?_⟩, fun h => ?_⟩
      · fin_cases i
        · change 0 ≤ (pt z.re t).re; rw [hpt_re]; exact hx0
        · change 0 ≤ σ.width - (pt z.re t).re; rw [hpt_re]; linarith
        · have := hzT.2 2
          change 0 ≤ (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 at this
          change 0 ≤ ((pt z.re t).re - σ.centre) ^ 2 + (pt z.re t).im ^ 2 - 1 / 16
          rw [hpt_re, hpt_im]
          nlinarith [hzT.1]
      · rw [mem_singleton_iff] at h
        have hre : z.re = σ.width := by rw [← vertexOne_re, ← h, hpt_re]
        have hle := σ.vertexOne_im_le_of_wallOne hzT hre
        have him : t = σ.vertexOne.im := by rw [← h, hpt_im]
        apply hzv
        exact Complex.ext (by rw [hre, vertexOne_re]) (by linarith)
    · have hs' : min z.re (σ.width / 2) ≤ s ∧ s ≤ max z.re (σ.width / 2) := hs
      exact htop _ (by rw [hpt_im]; exact h3Y)
        (by rw [hpt_re]; linarith [le_min hx0 (by linarith : (0 : ℝ) ≤ σ.width / 2)])
        (by rw [hpt_re]; linarith [max_le hxW (by linarith : σ.width / 2 ≤ σ.width)])
    · exact htop _ (by rw [hpt_im]; exact ht1) (by rw [hpt_re]; linarith)
        (by rw [hpt_re]; linarith)
  · exact Complex.ext (hpt_re _ _) (hpt_im _ _)
  · refine IsPreconnected.union (pt (σ.width / 2) Y) (Or.inr ⟨σ.width / 2, right_mem_uIcc, rfl⟩)
      ⟨Y, ⟨h3Y, le_rfl⟩, rfl⟩ ?_ (hvSc _ _ _)
    exact IsPreconnected.union (pt z.re Y) ⟨Y, ⟨hzY, le_rfl⟩, rfl⟩
      ⟨z.re, left_mem_uIcc, rfl⟩ (hvSc _ _ _) (hhSc _ _ _)

/-! ### Facts about the core disc -/

theorem foldH_half_lt_of_coreMap_le (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im)
    (h : ‖σ.coreMap z‖ ≤ 89 / 1000) : σ.foldH / 2 < cuspZeroHeight z := by
  have hc := σ.outer_core_of_coreMap_le hz h
  obtain ⟨-, hN, -⟩ := core_facts hc
  rw [normSq_sub_coreCentre, coreOuter] at hc
  have hY : (σ.fermiChart z).im ≤ 1173 / 1000 := by
    nlinarith [sq_nonneg (-(σ.fermiChart z).re - 201 / 1000)]
  have hY0 := σ.fermiChart_im_pos hz
  have hid := σ.sqrt_constK_mul_normSq_fermiChart hθ hz
  have hs := σ.sqrt_constK_pos
  unfold foldH
  by_contra hle
  push Not at hle
  have h1 : (σ.fermiChart z).im * cuspZeroHeight z ≤ 1173 / 1000 * (20 / 21 * √σ.constK / 2) :=
    mul_le_mul hY hle (cuspZeroHeight_pos hz).le (by norm_num)
  nlinarith

theorem not_core_of_wall {z : ℂ} (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) (hz : 0 < z.im) {i : Fin 3}
    (hw : σ.wallSide i z = 0) : 89 / 1000 < ‖σ.coreMap z‖ := by
  by_contra hle
  push Not at hle
  obtain ⟨-, h0, h1, h2⟩ := σ.mem_triangle_of_coreMap_le h₁ h₂ hz hle
  fin_cases i
  · exact absurd hw h0.ne'
  · exact absurd hw h1.ne'
  · exact absurd hw h2.ne'

/-! ### The fold data -/

theorem neg_conj_im (u : ℂ) : (-conj u).im = u.im := by simp

theorem neg_conj_re (u : ℂ) : (-conj u).re = -u.re := by simp

theorem norm_neg_conj_add (u : ℂ) : ‖-conj u + 3 / 2‖ = ‖u - 3 / 2‖ := by
  rw [show -conj u + 3 / 2 = conj (-(u - 3 / 2)) by simp [map_ofNat]; ring, Complex.norm_conj,
    norm_neg]

theorem contDiffAt_neg_conj {F : ℂ → ℂ} {z : ℂ} (h : ContDiffAt ℝ ∞ F z) :
    ContDiffAt ℝ ∞ (fun w => -conj (F w)) z :=
  (-(conjCLE : ℂ →L[ℝ] ℂ)).contDiff.contDiffAt.comp z h

section Data

variable (hθ : σ.θ₂ = 0) {p : ℕ} (hpθ : σ.θ₁ * p = Real.pi)

include hθ hpθ in
theorem nonempty_foldData : Nonempty σ.FoldData := by
  have h₁ := σ.admissible_of_mul_eq_pi hpθ
  have h₂ := σ.adm_two_of_cusp hθ
  have hp2 := σ.two_le_of_mul_eq_pi hpθ
  have hp : 1 ≤ p := by omega
  have hp0 : p ≠ 0 := by omega
  have hv := σ.vertexOne_im_pos
  obtain ⟨F, hF1, hF2, hF3, hF4⟩ := σ.exists_foldCore hθ h₁ hp hpθ
  set f : ℂ → ℂ := fun z => -conj (F z) with hfdef
  set good : Set ℂ := {z | 0 < z.im ∧ ContDiffAt ℝ ∞ F z ∧
    (z ≠ σ.vertexOne → (fderiv ℝ F z).det ≠ 0)} with hgood
  set U₀ := interior good with hU₀
  have hU₀o : IsOpen U₀ := isOpen_interior
  have hU₀g : ∀ z ∈ U₀, z ∈ good := fun z hz => interior_subset hz
  have hTU₀ : σ.triangle ⊆ U₀ := fun z hz => mem_interior_iff_mem_nhds.2 (hF2 z hz)
  have hfc : ∀ z ∈ U₀, ContDiffAt ℝ ∞ f z := fun z hz => contDiffAt_neg_conj (hU₀g z hz).2.1
  have hfU₀ : ContDiffOn ℝ ∞ f U₀ := fun z hz => (hfc z hz).contDiffWithinAt
  have hdetf : ∀ z ∈ U₀, (fderiv ℝ f z).det = -(fderiv ℝ F z).det := fun z hz =>
    det_fderiv_neg_conj ((hU₀g z hz).2.1.differentiableAt (by simp))
  have hdetc : ContinuousOn (fun z => (fderiv ℝ f z).det) U₀ :=
    continuous_det_clm.comp_continuousOn (hfU₀.continuousOn_fderiv_of_isOpen hU₀o (by simp))
  have hFE : ∀ z : ℂ, 0 < z.im → 87 / 1000 < ‖σ.coreMap z‖ → F =ᶠ[𝓝 z] σ.foldE p := by
    intro z hz h
    filter_upwards [continuousAt_const.eventually_lt (σ.contDiffAt_coreMap hz).continuousAt.norm h]
      with w hw
    exact hF1 w fun h' => by linarith [h'.2]
  have hvT : σ.vertexOne ∈ σ.triangle := by
    refine ⟨hv, fun i => ?_⟩
    fin_cases i
    · change 0 ≤ σ.vertexOne.re; rw [vertexOne_re]; exact σ.width_pos.le
    · change 0 ≤ σ.width - σ.vertexOne.re; rw [vertexOne_re]; simp
    · change 0 ≤ (σ.vertexOne.re - σ.centre) ^ 2 + σ.vertexOne.im ^ 2 - 1 / 16
      have hW : σ.width - σ.centre = Real.cos σ.θ₁ / 4 := by unfold width centre; ring
      rw [vertexOne_re, vertexOne_im, hW]
      have hs := Real.sin_sq_add_cos_sq σ.θ₁
      nlinarith
  have hvcore : 87 / 1000 < ‖σ.coreMap σ.vertexOne‖ := by
    have := σ.not_core_of_wall h₁ h₂ hv (i := 1) (by simp [wallSide, vertexOne_re])
    linarith
  have hfapex : f =ᶠ[𝓝 σ.vertexOne] σ.coneApexOne p := by
    filter_upwards [hFE _ hv hvcore, σ.foldE_eventually_apex hθ h₁ (p := p)] with w h1 h2
    rw [hfdef]
    simp only
    rw [h1, h2, σ.apexBefore_eq, map_neg, Complex.conj_conj, neg_neg]
  have hsign : ∀ z ∈ σ.triangle \ {σ.vertexOne}, 0 < (fderiv ℝ f z).det := by
    have hne : ∀ z ∈ σ.triangle \ {σ.vertexOne}, (fderiv ℝ f z).det ≠ 0 := by
      intro z ⟨hzT, hzv⟩
      rw [hdetf z (hTU₀ hzT)]
      exact neg_ne_zero.2 ((hU₀g z (hTU₀ hzT)).2.2 hzv)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hfapex.eventuallyEq_nhds
    set zs : ℂ := ⟨σ.width, σ.vertexOne.im + ε / 2⟩ with hzs
    have hzsd : dist zs σ.vertexOne < ε := by
      rw [dist_eq_norm, show zs - σ.vertexOne = ((ε / 2 : ℝ) : ℂ) * I by
        apply Complex.ext <;> simp [hzs, vertexOne_re]]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have hzsT : zs ∈ σ.triangle \ {σ.vertexOne} := by
      refine ⟨⟨by change 0 < σ.vertexOne.im + ε / 2; linarith, fun i => ?_⟩, fun h => ?_⟩
      · fin_cases i
        · change 0 ≤ σ.width; exact σ.width_pos.le
        · change 0 ≤ σ.width - σ.width; simp
        · change 0 ≤ (zs.re - σ.centre) ^ 2 + zs.im ^ 2 - 1 / 16
          simp only [hzs]
          have hW : σ.width - σ.centre = Real.cos σ.θ₁ / 4 := by unfold width centre; ring
          rw [hW, vertexOne_im]
          have hs := Real.sin_sq_add_cos_sq σ.θ₁
          nlinarith [σ.sin_θ₁_pos]
      · rw [mem_singleton_iff] at h
        have := congrArg Complex.im h
        simp [hzs] at this
        linarith
    have hpos : 0 < (fderiv ℝ f zs).det := by
      rw [(hball hzsd).fderiv_eq]
      exact σ.det_fderiv_coneApexOne_pos hp0 hzsT.1.1 hzsT.2
    intro z hz
    by_contra hle
    push Not at hle
    have hlt : (fderiv ℝ f z).det < 0 := lt_of_le_of_ne hle (hne z hz)
    have hcont : ContinuousOn (fun z => (fderiv ℝ f z).det) (σ.triangle \ {σ.vertexOne}) :=
      hdetc.mono fun w hw => hTU₀ hw.1
    have hIcc := σ.isPreconnected_triangle_diff.intermediate_value hz hzsT hcont
    obtain ⟨w, hw, hw0⟩ := hIcc ⟨hlt.le, hpos.le⟩
    exact hne w hw hw0
  set U : Set ℂ := U₀ ∩ {z | z = σ.vertexOne ∨ 0 < (fderiv ℝ f z).det} with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU₀, hz | hz⟩
    · subst hz
      filter_upwards [hU₀o.mem_nhds hzU₀, hfapex.eventuallyEq_nhds,
        isOpen_upper.mem_nhds hv] with w hw hwe hwi
      refine ⟨hw, ?_⟩
      by_cases hwv : w = σ.vertexOne
      · exact Or.inl hwv
      · right
        rw [hwe.fderiv_eq]
        exact σ.det_fderiv_coneApexOne_pos hp0 hwi hwv
    · filter_upwards [hU₀o.mem_nhds hzU₀,
        continuousAt_const.eventually_lt (hdetc.continuousAt (hU₀o.mem_nhds hzU₀)) hz] with w hw hwd
      exact ⟨hw, Or.inr hwd⟩
  have hTU : σ.triangle ⊆ U := by
    intro z hz
    refine ⟨hTU₀ hz, ?_⟩
    by_cases hzv : z = σ.vertexOne
    · exact Or.inl hzv
    · exact Or.inr (hsign z ⟨hz, hzv⟩)
  have hUim : ∀ z ∈ U, 0 < z.im := fun z hz => (hU₀g z hz.1).1
  set V : Fin 3 → Set ℂ := fun i => {z | z ∈ U ∧ σ.refl i z ∈ U ∧ z ∈ σ.wallSet i ∧
    σ.refl i z ∈ σ.wallSet i ∧ 87 / 1000 < ‖σ.coreMap z‖ ∧
      87 / 1000 < ‖σ.coreMap (σ.refl i z)‖} with hV
  have hVo : ∀ i, IsOpen (V i) := by
    intro i
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU, hrU, hzW, hrW, hzc, hrc⟩
    have hz := hUim z hzU
    have hr := hUim _ hrU
    have hcr := σ.continuousAt_refl i hz
    have hWo := σ.isOpen_wallSet hθ i
    filter_upwards [hUo.mem_nhds hzU, hcr.preimage_mem_nhds (hUo.mem_nhds hrU),
      hWo.mem_nhds hzW, hcr.preimage_mem_nhds (hWo.mem_nhds hrW),
      continuousAt_const.eventually_lt (σ.contDiffAt_coreMap hz).continuousAt.norm hzc,
      continuousAt_const.eventually_lt
        (((σ.contDiffAt_coreMap hr).continuousAt.comp hcr).norm) hrc]
      with w h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hVmaps : ∀ i, MapsTo (σ.refl i) (V i) (V i) := by
    rintro i z ⟨hzU, hrU, hzW, hrW, hzc, hrc⟩
    have hz := hUim z hzU
    have e := σ.refl_refl hz i
    exact ⟨hrU, by rw [e]; exact hzU, hrW, by rw [e]; exact hzW, hrc, by rw [e]; exact hzc⟩
  have hWallV : ∀ i, σ.foldWall i ⊆ V i := by
    intro i z hz
    have hrz := σ.refl_eq_self_of_mem_foldWall hz
    have hc := σ.not_core_of_wall h₁ h₂ hz.1.1 hz.2
    have hW := σ.foldWall_subset_wallSet hθ h₁ i hz
    refine ⟨hTU hz.1, ?_, hW, ?_, by linarith, ?_⟩ <;> rw [hrz]
    · exact hTU hz.1
    · exact hW
    · linarith
  have hfrefl : ∀ i, ∀ z ∈ V i, f (σ.refl i z) = conj (f z) := by
    rintro i z ⟨hzU, hrU, hzW, hrW, hzc, hrc⟩
    have hz := hUim z hzU
    have e1 : F z = σ.foldE p z := hF1 z fun h' => by linarith [h'.2]
    have e2 : F (σ.refl i z) = σ.foldE p (σ.refl i z) := hF1 _ fun h' => by linarith [h'.2]
    have key : σ.foldE p (σ.refl i z) = conj (σ.foldE p z) := by
      fin_cases i
      · exact σ.foldE_refl_zero hθ h₁ hzW hrW
      · exact σ.foldE_refl_one hθ h₁ hzW hrW
      · exact σ.foldE_refl_two hθ h₁ hpθ hzW
    simp only [hfdef]
    rw [e1, e2, key, map_neg, Complex.conj_conj]
  have hcuspInf : ∀ z ∈ U, 2 < z.im → ‖f z‖ = outerProfile σ.constK σ.foldY₁ σ.foldY₂ z.im := by
    intro z hzU hy
    have hz := hUim z hzU
    have hnc : ¬ (0 < z.im ∧ ‖σ.coreMap z‖ < 87 / 1000) := fun h' =>
      absurd (σ.im_lt_two_of_coreMap_le hz (by linarith [h'.2])) (by linarith)
    have hH := σ.foldH_pos
    have hHh := σ.foldH_lt_half
    have hd : z ∈ σ.domOne :=
      σ.mem_domOne_of_im_gt (by rw [vertexOne_im]; linarith [Real.sin_le_one σ.θ₁])
    have h0 : σ.foldH ≤ cuspZeroHeight z := by linarith [im_le_cuspZeroHeight hz]
    have h1 : σ.foldH ≤ σ.etaOne z := by linarith [σ.im_le_etaOne hd]
    have hL : 1 / 10 ≤ |σ.sinhN z| := by
      have hs : 1 / 10 ≤ σ.sinhN z := by
        unfold sinhN
        rw [le_div_iff₀ hz]
        simp only [wallSide]
        nlinarith [sq_nonneg (z.re - σ.centre)]
      exact le_trans hs (le_abs_self _)
    have hR : 0 < outerProfile σ.constK σ.foldY₁ σ.foldY₂ z.im :=
      lt_trans (by norm_num) (two_lt_outerProfile σ.constK_pos σ.sqrt_constK_le_half
        (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz)
    simp only [hfdef]
    rw [norm_neg, Complex.norm_conj, hF1 z hnc, σ.foldE_of_inf hθ h₁ h0 h1 hL, cornerInfW,
      norm_ofReal_mul_exp _ _ hR.le]
  have hcuspZero : ∀ z ∈ U, cuspZeroHeight z < σ.foldH / 2 →
      ‖f z + 3 / 2‖ = coneProfile σ.constK (cuspZeroHeight z) := by
    intro z hzU h0
    have hz := hUim z hzU
    have hnc : ¬ (0 < z.im ∧ ‖σ.coreMap z‖ < 87 / 1000) := fun h' =>
      absurd (σ.foldH_half_lt_of_coreMap_le hθ hz (by linarith [h'.2])) (by linarith)
    have hH := σ.foldH_pos
    have h0' : cuspZeroHeight z < σ.foldH := by linarith
    simp only [hfdef]
    rw [norm_neg_conj_add, hF1 z hnc, σ.foldE_of_zero h0', cornerZero, add_sub_cancel_left,
      norm_ofReal_mul_exp _ _ (σ.holeModulus_pos z).le]
  have hbij : BijOn f σ.triangle σ.basePlus := by
    refine σ.bijOn_of_local' hUo hTU (fun z hz => (hfc z hz.1).contDiffWithinAt)
      (fun z hz hzv _ => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun h => absurd hθ h.ne')
      σ.foldY₁_lt_foldY₂ (H := 2) (fun z hz hy => hcuspInf z (hTU hz) hy)
      (B := σ.foldH / 2) (by linarith [σ.foldH_pos]) (fun _ z hz h => hcuspZero z (hTU hz) h)
    · rcases hz.2 with h | h
      · exact absurd h hzv
      · exact h.ne'
    · exact σ.im_eq_zero_of_wall_identities fun i => ⟨V i, hWallV i, hfrefl i⟩
    · intro z hz z' hz' h
      simp only [hfdef, neg_inj] at h
      exact hF3 hz hz' ((starRingEnd ℂ).injective h)
    · intro z hz
      obtain ⟨h3, him, hh⟩ := hF4 z hz
      refine ⟨by simp only [hfdef]; rw [norm_neg, Complex.norm_conj]; exact h3, by
        simp only [hfdef]; rw [neg_conj_im]; exact him, fun _ => ?_⟩
      simp only [hfdef]
      rw [norm_neg_conj_add]
      exact hh
    · intro z hz hw
      have hc := σ.not_core_of_wall h₁ h₂ hz.1 hw
      simp only [hfdef]
      rw [neg_conj_re, hF1 z fun h' => by linarith [h'.2]]
      linarith [σ.foldE_wall_zero_re hθ h₁ (p := p) hz hw]
    · intro z hz hw
      have hc := σ.not_core_of_wall h₁ h₂ hz.1 hw
      have hx : z.re = σ.width := by
        change σ.width - z.re = 0 at hw; linarith
      simp only [hfdef]
      rw [neg_conj_re, hF1 z fun h' => by linarith [h'.2]]
      linarith [σ.foldE_wall_one_re hθ h₁ hp hz hx]
    · intro z hz hw
      have hc := σ.not_core_of_wall h₁ h₂ hz.1 hw
      simp only [hfdef]
      rw [neg_conj_re, hF1 z fun h' => by linarith [h'.2]]
      have := σ.foldE_wall_two_re hθ h₁ hp hpθ hz hw
      constructor <;> linarith [this.1, this.2]
    · have := hfapex.self_of_nhds
      rw [this, σ.coneApexOne_vertexOne hp0]
  exact ⟨{
    U := U
    f := f
    isOpen_U := hUo
    im_pos_of_mem_U := hUim
    triangle_subset_U := hTU
    contDiffOn_f := fun z hz => (hfc z hz.1).contDiffWithinAt
    det_fderiv_pos := fun z hz hzv _ => by
      rcases hz.2 with h | h
      · exact absurd h hzv
      · exact h
    V := V
    isOpen_V := hVo
    V_subset_U := fun i z hz => hz.1
    foldWall_subset_V := hWallV
    refl_mapsTo_V := hVmaps
    f_refl := hfrefl
    bijOn_f := hbij
    f_apexOne := fun q hq => by
      have hqp : q = p := by
        have : (q : ℝ) = p := by
          have h := hq.trans hpθ.symm
          exact mul_left_cancel₀ σ.θ₁_pos.ne' h
        exact_mod_cast this
      subst hqp
      exact hfapex
    f_apexTwo := fun q hq => by
      rw [hθ, zero_mul] at hq
      exact absurd hq Real.pi_pos.ne
    outerY₁ := σ.foldY₁
    outerY₂ := σ.foldY₂
    outerY₁_pos := σ.foldY₁_pos
    outerY₁_lt := σ.foldY₁_lt_foldY₂
    outerY₂_lt := σ.foldY₂_lt_sqrt
    cuspInfHeight := 2
    norm_f_cuspInf := hcuspInf
    cuspZeroBound := σ.foldH / 2
    cuspZeroBound_pos := by linarith [σ.foldH_pos]
    norm_f_cuspZero := fun _ z hz h => hcuspZero z hz h }⟩

end Data

noncomputable def oneConeFoldData (hθ : σ.θ₂ = 0) {p : ℕ} (hpθ : σ.θ₁ * p = Real.pi) :
    σ.FoldData :=
  Classical.choice (σ.nonempty_foldData hθ hpθ)

end ConeShape

end GC.Seifert
