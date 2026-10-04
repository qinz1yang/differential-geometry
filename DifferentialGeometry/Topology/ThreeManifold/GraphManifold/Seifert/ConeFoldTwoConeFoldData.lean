import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeWalls

/-!
# The fold data of the two-cone shapes `(p₁, p₂, ⊤)`

Lane A4b3, milestone 5 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`,
§0, §8, two-cone shapes). For a shape with cones of orders `p` at `v₁` (`θ₁ p = π`) and `q` at
`v₂` (`θ₂ q = π`) the fold is the mirror `f = -conj ∘ F` of the core-replaced map `F` of
`exists_foldCore₂`. It satisfies the frozen interface `ConeShape.FoldData` of
`SF/ConeFoldSpec.lean` (`twoConeFoldData`):
* `U` is the set of points near which `F` is smooth with nonzero Jacobian off both vertices, cut
  down to positive Jacobian of `f` off the vertices; the Jacobian has one sign on the preconnected
  set `T \ {v₁, v₂}` (`isPreconnected_triangle_diff₂`) and is positive near `v₁`, where `f` is the
  branched model `coneApexOne p`; near `v₂` the map is `coneApexTwo q`;
* the wall neighbourhoods are `U ∩ refl⁻¹ U ∩ wallSetC ∩ refl⁻¹ wallSetC` outside the core disc;
* `bijOn_f` comes from A4Q's `bijOn_of_local'` (no hole: `basePlus = {‖u‖ < 3, Im u ≥ 0}`);
* `‖f‖ = outerProfile K Y₁ Y₂ (Im z)` above height `2`; the cusp-`0` clause is vacuous.
The condition `(p₁, p₂) ≠ (2, 2)` is part of `ConeShape` (`θ₁ + θ₂ < π`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

open ConeLayout

namespace ConeShape

variable (σ : ConeShape)

theorem discTwo_self_aux : coneDisc σ.vertexTwo σ.vertexTwo = 0 := coneDisc_self _

theorem hasDerivAt_coneApexTwo (hθ : 0 < σ.θ₂) (q : ℕ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (σ.coneApexTwo q)
      (-(q * coneDisc σ.vertexTwo z ^ (q - 1) *
        ((σ.vertexTwo - conj σ.vertexTwo) / (z - conj σ.vertexTwo) ^ 2) / 2)) z := by
  have h := ((hasDerivAt_coneDisc (σ.vertexTwo_im_pos hθ) hz).pow q).div_const 2
  exact (h.const_sub (-(3 / 2))).congr_deriv (by ring)

theorem det_fderiv_coneApexTwo_pos (hθ : 0 < σ.θ₂) {q : ℕ} (hq : q ≠ 0) {z : ℂ} (hz : 0 < z.im)
    (hzv : z ≠ σ.vertexTwo) : 0 < (fderiv ℝ (σ.coneApexTwo q) z).det := by
  have hv := σ.vertexTwo_im_pos hθ
  rw [det_fderiv_of_hasDerivAt (σ.hasDerivAt_coneApexTwo hθ q hz)]
  apply normSq_pos.2
  have h1 : coneDisc σ.vertexTwo z ≠ 0 := coneDisc_ne_zero hv hz hzv
  have h2 : σ.vertexTwo - conj σ.vertexTwo ≠ 0 := sub_conj_self_ne hv
  have h3 := sub_conj_ne_zero hv hz
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  exact neg_ne_zero.2 (div_ne_zero (mul_ne_zero (mul_ne_zero hq' (pow_ne_zero _ h1))
    (div_ne_zero h2 (pow_ne_zero _ h3))) two_ne_zero)

theorem isPreconnected_triangle_diff₂ :
    IsPreconnected (σ.triangle \ {σ.vertexOne, σ.vertexTwo}) := by
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
  have hv2 : σ.vertexTwo.im ≤ 1 / 4 := by
    rw [vertexTwo_im]; linarith [Real.sin_le_one σ.θ₂]
  have htop : ∀ w : ℂ, 3 ≤ w.im → 0 ≤ w.re → w.re ≤ σ.width →
      w ∈ σ.triangle \ {σ.vertexOne, σ.vertexTwo} := by
    intro w hw h0 h1
    refine ⟨⟨by linarith, fun i => ?_⟩, fun h => ?_⟩
    · fin_cases i
      · exact h0
      · change 0 ≤ σ.width - w.re; linarith
      · exact (hw2 w hw).le
    · rcases h with h | h
      · rw [h] at hw
        linarith
      · rw [mem_singleton_iff] at h
        rw [h] at hw
        linarith
  refine isPreconnected_of_forall (pt (σ.width / 2) 3) fun z hz => ?_
  obtain ⟨hzT, hzvv⟩ := hz
  have hzv : z ≠ σ.vertexOne := fun h => hzvv (Or.inl h)
  have hzv2 : z ≠ σ.vertexTwo := fun h => hzvv (Or.inr h)
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
      · rcases h with h | h
        · have hre : z.re = σ.width := by rw [← vertexOne_re, ← h, hpt_re]
          have hle := σ.vertexOne_im_le_of_wallOne hzT hre
          have him : t = σ.vertexOne.im := by rw [← h, hpt_im]
          apply hzv
          exact Complex.ext (by rw [hre, vertexOne_re]) (by linarith)
        · rw [mem_singleton_iff] at h
          have hre : z.re = 0 := by rw [← vertexTwo_re, ← h, hpt_re]
          have him : t = σ.vertexTwo.im := by rw [← h, hpt_im]
          have hle : σ.vertexTwo.im ≤ z.im := by
            have hw2 := hzT.2 2
            simp only [wallSide] at hw2
            rw [hre] at hw2
            have hc : σ.centre = Real.cos σ.θ₂ / 4 := rfl
            rw [hc] at hw2
            have hs := Real.sin_sq_add_cos_sq σ.θ₂
            have hsq : σ.vertexTwo.im ^ 2 ≤ z.im ^ 2 := by rw [vertexTwo_im]; nlinarith
            have h0 : 0 ≤ σ.vertexTwo.im := by rw [vertexTwo_im]; linarith [σ.sin_θ₂_nonneg]
            exact (pow_le_pow_iff_left₀ h0 hzT.1.le two_ne_zero).1 hsq
          apply hzv2
          exact Complex.ext (by rw [hre, vertexTwo_re]) (by linarith)
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

section Data

variable (hθ : 0 < σ.θ₂) {p q : ℕ} (hpθ : σ.θ₁ * p = Real.pi) (hqθ : σ.θ₂ * q = Real.pi)

include hθ hpθ hqθ in
theorem nonempty_foldData₂ : Nonempty σ.FoldData := by
  have h₁ := σ.admissible_of_mul_eq_pi hpθ
  have h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂ :=
    (σ.swap hθ).admissible_of_mul_eq_pi hqθ
  have hp2 := σ.two_le_of_mul_eq_pi hpθ
  have hq2 := (σ.swap hθ).two_le_of_mul_eq_pi hqθ
  have hp : 1 ≤ p := by omega
  have hp0 : p ≠ 0 := by omega
  have hq : 1 ≤ q := by omega
  have hq0 : q ≠ 0 := by omega
  have hv := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  obtain ⟨F, hF1, hF2, hF3, hF4⟩ := σ.exists_foldCore₂ hθ h₁ h₂ hp hq hpθ hqθ
  set f : ℂ → ℂ := fun z => -conj (F z) with hfdef
  set good : Set ℂ := {z | 0 < z.im ∧ ContDiffAt ℝ ∞ F z ∧
    (z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ F z).det ≠ 0)} with hgood
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
  have hFE : ∀ z : ℂ, 0 < z.im → 87 / 1000 < ‖σ.coreMap z‖ → F =ᶠ[𝓝 z] σ.foldE₂ hθ p q := by
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
    filter_upwards [hFE _ hv hvcore, σ.foldE₂_eventually_apexOne hθ h₁ h₂ (p := p) (q := q)]
      with w h1 h2
    rw [hfdef]
    simp only
    rw [h1, h2, σ.apexBefore_eq, map_neg, Complex.conj_conj, neg_neg]
  have hvT2 : σ.vertexTwo ∈ σ.triangle := by
    refine ⟨hv2, fun i => ?_⟩
    fin_cases i
    · change 0 ≤ σ.vertexTwo.re; rw [vertexTwo_re]
    · change 0 ≤ σ.width - σ.vertexTwo.re; rw [vertexTwo_re]; linarith [σ.width_pos]
    · change 0 ≤ (σ.vertexTwo.re - σ.centre) ^ 2 + σ.vertexTwo.im ^ 2 - 1 / 16
      rw [vertexTwo_re, vertexTwo_im]
      have hc : σ.centre = Real.cos σ.θ₂ / 4 := rfl
      rw [hc]
      have hs := Real.sin_sq_add_cos_sq σ.θ₂
      nlinarith
  have hvcore2 : 87 / 1000 < ‖σ.coreMap σ.vertexTwo‖ := by
    have := σ.not_core_of_wall h₁ h₂ hv2 (i := 0) (by simp [wallSide, vertexTwo_re])
    linarith
  have hfapex2 : f =ᶠ[𝓝 σ.vertexTwo] σ.coneApexTwo q := by
    filter_upwards [hFE _ hv2 hvcore2, σ.foldE₂_eventually_apexTwo hθ h₁ h₂ (p := p) (q := q)]
      with w h1 h2
    rw [hfdef]
    simp only
    rw [h1, h2, σ.neg_conj_apexTwoBefore]
  have hsign : ∀ z ∈ σ.triangle \ {σ.vertexOne, σ.vertexTwo}, 0 < (fderiv ℝ f z).det := by
    have hne : ∀ z ∈ σ.triangle \ {σ.vertexOne, σ.vertexTwo}, (fderiv ℝ f z).det ≠ 0 := by
      intro z ⟨hzT, hzv⟩
      rw [hdetf z (hTU₀ hzT)]
      exact neg_ne_zero.2 ((hU₀g z (hTU₀ hzT)).2.2 (fun h => hzv (Or.inl h))
        (fun h => hzv (Or.inr h)))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hfapex.eventuallyEq_nhds
    set zs : ℂ := ⟨σ.width, σ.vertexOne.im + ε / 2⟩ with hzs
    have hzsd : dist zs σ.vertexOne < ε := by
      rw [dist_eq_norm, show zs - σ.vertexOne = ((ε / 2 : ℝ) : ℂ) * I by
        apply Complex.ext <;> simp [hzs, vertexOne_re]]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have hzsT : zs ∈ σ.triangle \ {σ.vertexOne, σ.vertexTwo} := by
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
      · rcases h with h | h
        · have := congrArg Complex.im h
          simp [hzs] at this
          linarith
        · rw [mem_singleton_iff] at h
          have := congrArg Complex.re h
          simp [hzs, vertexTwo_re] at this
          linarith [σ.width_pos]
    have hpos : 0 < (fderiv ℝ f zs).det := by
      rw [(hball hzsd).fderiv_eq]
      exact σ.det_fderiv_coneApexOne_pos hp0 hzsT.1.1 (fun h => hzsT.2 (Or.inl h))
    intro z hz
    by_contra hle
    push Not at hle
    have hlt : (fderiv ℝ f z).det < 0 := lt_of_le_of_ne hle (hne z hz)
    have hcont : ContinuousOn (fun z => (fderiv ℝ f z).det)
        (σ.triangle \ {σ.vertexOne, σ.vertexTwo}) :=
      hdetc.mono fun w hw => hTU₀ hw.1
    have hIcc := σ.isPreconnected_triangle_diff₂.intermediate_value hz hzsT hcont
    obtain ⟨w, hw, hw0⟩ := hIcc ⟨hlt.le, hpos.le⟩
    exact hne w hw hw0
  set U : Set ℂ := U₀ ∩ {z | z = σ.vertexOne ∨ z = σ.vertexTwo ∨ 0 < (fderiv ℝ f z).det}
    with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU₀, hz | hz | hz⟩
    · subst hz
      filter_upwards [hU₀o.mem_nhds hzU₀, hfapex.eventuallyEq_nhds,
        isOpen_upper.mem_nhds hv] with w hw hwe hwi
      refine ⟨hw, ?_⟩
      by_cases hwv : w = σ.vertexOne
      · exact Or.inl hwv
      · right; right
        rw [hwe.fderiv_eq]
        exact σ.det_fderiv_coneApexOne_pos hp0 hwi hwv
    · subst hz
      filter_upwards [hU₀o.mem_nhds hzU₀, hfapex2.eventuallyEq_nhds,
        isOpen_upper.mem_nhds hv2] with w hw hwe hwi
      refine ⟨hw, ?_⟩
      by_cases hwv : w = σ.vertexTwo
      · exact Or.inr (Or.inl hwv)
      · right; right
        rw [hwe.fderiv_eq]
        exact σ.det_fderiv_coneApexTwo_pos hθ hq0 hwi hwv
    · filter_upwards [hU₀o.mem_nhds hzU₀,
        continuousAt_const.eventually_lt (hdetc.continuousAt (hU₀o.mem_nhds hzU₀)) hz] with w hw hwd
      exact ⟨hw, Or.inr (Or.inr hwd)⟩
  have hTU : σ.triangle ⊆ U := by
    intro z hz
    refine ⟨hTU₀ hz, ?_⟩
    by_cases hzv : z = σ.vertexOne
    · exact Or.inl hzv
    by_cases hzv2 : z = σ.vertexTwo
    · exact Or.inr (Or.inl hzv2)
    · exact Or.inr (Or.inr (hsign z ⟨hz, fun h => h.elim hzv hzv2⟩))
  have hUim : ∀ z ∈ U, 0 < z.im := fun z hz => (hU₀g z hz.1).1
  set V : Fin 3 → Set ℂ := fun i => {z | z ∈ U ∧ σ.refl i z ∈ U ∧ z ∈ σ.wallSetC hθ i ∧
    σ.refl i z ∈ σ.wallSetC hθ i ∧ 87 / 1000 < ‖σ.coreMap z‖ ∧
      87 / 1000 < ‖σ.coreMap (σ.refl i z)‖} with hV
  have hVo : ∀ i, IsOpen (V i) := by
    intro i
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU, hrU, hzW, hrW, hzc, hrc⟩
    have hz := hUim z hzU
    have hr := hUim _ hrU
    have hcr := σ.continuousAt_refl i hz
    have hWo := σ.isOpen_wallSetC hθ i
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
    have hW := σ.foldWall_subset_wallSetC hθ h₁ h₂ i hz
    refine ⟨hTU hz.1, ?_, hW, ?_, by linarith, ?_⟩ <;> rw [hrz]
    · exact hTU hz.1
    · exact hW
    · linarith
  have hfrefl : ∀ i, ∀ z ∈ V i, f (σ.refl i z) = conj (f z) := by
    rintro i z ⟨hzU, hrU, hzW, hrW, hzc, hrc⟩
    have hz := hUim z hzU
    have e1 : F z = σ.foldE₂ hθ p q z := hF1 z fun h' => by linarith [h'.2]
    have e2 : F (σ.refl i z) = σ.foldE₂ hθ p q (σ.refl i z) := hF1 _ fun h' => by linarith [h'.2]
    have key : σ.foldE₂ hθ p q (σ.refl i z) = conj (σ.foldE₂ hθ p q z) := by
      fin_cases i
      · exact σ.foldE₂_refl_zero hθ h₁ h₂ hzW hrW
      · exact σ.foldE₂_refl_one hθ h₁ h₂ hzW hrW
      · exact σ.foldE₂_refl_two hθ h₁ h₂ hpθ hqθ hzW
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
    have hd0 : z ∈ σ.domZeroC :=
      σ.mem_domZeroC_of_im_gt hθ (by rw [vertexTwo_im]; linarith [Real.sin_le_one σ.θ₂])
    have h0 : σ.foldH ≤ σ.etaTwoC z := by linarith [σ.im_le_etaTwoC hθ hd0]
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
    rw [norm_neg, Complex.norm_conj, hF1 z hnc, σ.foldE₂_of_inf hθ h0 h1 hL, cornerInfC,
      norm_ofReal_mul_exp _ _ hR.le]
  have hbij : BijOn f σ.triangle σ.basePlus := by
    refine σ.bijOn_of_local' hUo hTU (fun z hz => (hfc z hz.1).contDiffWithinAt)
      (fun z hz hzv hzv2 => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ => ?_)
      σ.foldY₁_lt_foldY₂ (H := 2) (fun z hz hy => hcuspInf z (hTU hz) hy)
      (B := 1) one_pos (fun h => absurd h hθ.ne')
    · rcases hz.2 with h | h | h
      · exact absurd h hzv
      · exact absurd h hzv2
      · exact h.ne'
    · exact σ.im_eq_zero_of_wall_identities fun i => ⟨V i, hWallV i, hfrefl i⟩
    · intro z hz z' hz' h
      simp only [hfdef, neg_inj] at h
      exact hF3 hz hz' ((starRingEnd ℂ).injective h)
    · intro z hz
      obtain ⟨h3, him⟩ := hF4 z hz
      refine ⟨by simp only [hfdef]; rw [norm_neg, Complex.norm_conj]; exact h3, by
        simp only [hfdef]; rw [neg_conj_im]; exact him, fun h => absurd h hθ.ne'⟩
    · intro z hz hw
      have hc := σ.not_core_of_wall h₁ h₂ hz.1 hw
      simp only [hfdef]
      rw [neg_conj_re, hF1 z fun h' => by linarith [h'.2]]
      linarith [σ.foldE₂_wall_zero_re hθ h₁ h₂ (p := p) hq hz hw]
    · intro z hz hw
      have hc := σ.not_core_of_wall h₁ h₂ hz.1 hw
      have hx : z.re = σ.width := by
        change σ.width - z.re = 0 at hw; linarith
      simp only [hfdef]
      rw [neg_conj_re, hF1 z fun h' => by linarith [h'.2]]
      linarith [σ.foldE₂_wall_one_re hθ h₁ h₂ (q := q) hp hz hx]
    · intro z hz hw
      have hc := σ.not_core_of_wall h₁ h₂ hz.1 hw
      simp only [hfdef]
      rw [neg_conj_re, hF1 z fun h' => by linarith [h'.2]]
      have := σ.foldE₂_wall_two_re hθ h₁ h₂ hp hq hpθ hqθ hz hw
      constructor <;> linarith [this.1, this.2]
    · have := hfapex.self_of_nhds
      rw [this, σ.coneApexOne_vertexOne hp0]
    · have := hfapex2.self_of_nhds
      rw [this, coneApexTwo, discTwo_self_aux, zero_pow hq0]
      norm_num
  exact ⟨{
    U := U
    f := f
    isOpen_U := hUo
    im_pos_of_mem_U := hUim
    triangle_subset_U := hTU
    contDiffOn_f := fun z hz => (hfc z hz.1).contDiffWithinAt
    det_fderiv_pos := fun z hz hzv hzv2 => by
      rcases hz.2 with h | h | h
      · exact absurd h hzv
      · exact absurd h hzv2
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
    f_apexTwo := fun q' hq' => by
      have hqq : q' = q := by
        have : (q' : ℝ) = q := by
          have h := hq'.trans hqθ.symm
          exact mul_left_cancel₀ hθ.ne' h
        exact_mod_cast this
      subst hqq
      exact hfapex2
    outerY₁ := σ.foldY₁
    outerY₂ := σ.foldY₂
    outerY₁_pos := σ.foldY₁_pos
    outerY₁_lt := σ.foldY₁_lt_foldY₂
    outerY₂_lt := σ.foldY₂_lt_sqrt
    cuspInfHeight := 2
    norm_f_cuspInf := hcuspInf
    cuspZeroBound := 1
    cuspZeroBound_pos := one_pos
    norm_f_cuspZero := fun h => absurd h hθ.ne' }⟩

end Data

theorem θ₂_pos_of_mul_eq_pi {q : ℕ} (hqθ : σ.θ₂ * q = Real.pi) : 0 < σ.θ₂ := by
  rcases σ.θ₂_nonneg.lt_or_eq with h | h
  · exact h
  · rw [← h, zero_mul] at hqθ
    exact absurd hqθ Real.pi_pos.ne

noncomputable def twoConeFoldData {p₁ p₂ : ℕ} (hθ₁ : σ.θ₁ * p₁ = Real.pi)
    (hθ₂ : σ.θ₂ * p₂ = Real.pi) : σ.FoldData :=
  Classical.choice (σ.nonempty_foldData₂ (σ.θ₂_pos_of_mul_eq_pi hθ₂) hθ₁ hθ₂)

end ConeShape

end GC.Seifert
