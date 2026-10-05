import DifferentialGeometry.Topology.Diffeomorph.SphereGerm
import DifferentialGeometry.Topology.Manifold.ClosedBall.Diffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Topology.Handle.Embedding
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A germ of diffeomorphism of the closed disk along its boundary is realized globally

Review 44 item (2) (R1, lane LFR28-ROW2), frozen interface:
`exists_diskDiffeomorph_eq_boundaryGerm`. A partial diffeomorphism `g` of the closed disk
`ClosedCell 2` whose source contains the boundary circle and which fixes it pointwise agrees, on a
collar `{1 - δ < ‖z‖}` (`δ < η`), with a diffeomorphism `ψ` of the whole closed disk that is the
identity on `{‖z‖ ≤ 1 - η}`.

Construction (the germ-to-ambient step is new; the ambient step is the tree's):
1. `δ₀`: the collar `{1 - δ₀ < ‖z‖}` lies in the source (`IsCompact.exists_thickening_subset_open`
   and `mem_thickening_sphere_of_abs_norm_sub_one_lt`);
2. the cut-off germ `u = χ(‖z‖) · g z` (`χ = 0` on `‖z‖ ≤ 1 - δ₀/2`, `χ = 1` on `‖z‖ ≥ 1 - δ₀/4`)
   is smooth on the closed disk; its half-space extension `G : ℝ² → ℝ²`
   (`IsSmoothEmbedding.exists_contDiff_compact_extension_halfspace`) has bijective derivative on the
   circle (as in `Handle.exists_contDiff_closedCell_extension_bijective_fderiv`, pointwise), hence is
   a partial diffeomorphism near the circle (`IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact`),
   restricted to `{‖x‖ > 1 - δ₀/4}`;
3. the compactly supported ambient isotopy of
   `PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood`, with support in
   `{‖x‖ > 1 - η}`, at time one, restricted to the closed disk (`closedCellDiffeomorph`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- A point at distance `< δ` from the unit circle in norm lies in the `δ`-thickening of the unit
sphere. -/
theorem mem_thickening_sphere_of_abs_norm_sub_one_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {z : E} {δ : ℝ} (hz0 : z ≠ 0) (hz : |‖z‖ - 1| < δ) :
    z ∈ thickening δ (sphere (0 : E) 1) := by
  rw [mem_thickening_iff]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  refine ⟨‖z‖⁻¹ • z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · rw [dist_eq_norm, show z - ‖z‖⁻¹ • z = (1 - ‖z‖⁻¹) • z by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs]
    have h : |1 - ‖z‖⁻¹| * ‖z‖ = |‖z‖ - 1| := by
      rw [← abs_of_pos hn, ← abs_mul, abs_of_pos hn, sub_mul, one_mul, inv_mul_cancel₀ hn.ne']
    rw [h]
    exact hz

/-- **R1: a boundary germ of a disk diffeomorphism is realized by a global one.** -/
theorem exists_diskDiffeomorph_eq_boundaryGerm
    (g : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) (ClosedCell 2) (ClosedCell 2) ∞)
    (hsrc : {z : ClosedCell 2 | ‖(z : E2)‖ = 1} ⊆ g.source)
    (hfix : ∀ z : ClosedCell 2, ‖(z : E2)‖ = 1 → g z = z) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ ∃ ψ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2,
      {z : ClosedCell 2 | 1 - δ < ‖(z : E2)‖} ⊆ g.source ∧
      EqOn ψ g {z : ClosedCell 2 | 1 - δ < ‖(z : E2)‖} ∧
      EqOn ψ id {z : ClosedCell 2 | ‖(z : E2)‖ ≤ 1 - η} := by
  -- 1. a collar inside the source
  obtain ⟨U, hUo, hUs⟩ := isOpen_induced_iff.mp g.open_source
  have hSU : sphere (0 : E2) 1 ⊆ U := by
    intro x hx
    have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hmem : (⟨x, hx1.le⟩ : ClosedCell 2) ∈ g.source := hsrc hx1
    rw [← hUs] at hmem
    exact hmem
  obtain ⟨δ₀', hδ₀', hthick⟩ := (isCompact_sphere (0 : E2) 1).exists_thickening_subset_open hUo hSU
  set δ₀ := min δ₀' (1 / 2) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min hδ₀' (by norm_num)
  have hδ₀1 : δ₀ ≤ 1 / 2 := min_le_right _ _
  have hcollar : ∀ z : ClosedCell 2, 1 - δ₀ < ‖(z : E2)‖ → z ∈ g.source := by
    intro z hz
    have hz1 : ‖(z : E2)‖ ≤ 1 := z.2
    have hz0 : (z : E2) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      linarith
    have habs : |‖(z : E2)‖ - 1| < δ₀' := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith [min_le_left δ₀' (1 / 2)]
    have hzU : (z : E2) ∈ U := hthick (mem_thickening_sphere_of_abs_norm_sub_one_lt hz0 habs)
    rw [← hUs]
    exact hzU
  -- 2. the cut-off germ and its extension
  set a : ℝ := 1 - δ₀ / 2 with hadef
  set b : ℝ := 1 - δ₀ / 4 with hbdef
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have ha0 : 0 < a := by rw [hadef]; linarith
  let χ : E2 → ℝ := fun x => Real.smoothTransition ((‖x‖ ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2))
  have hχs : ContDiff ℝ ∞ χ := by
    refine Real.smoothTransition.contDiff.comp ?_
    exact ((contDiff_norm_sq ℝ).sub contDiff_const).div_const _
  have hba2 : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hχ1 : ∀ x : E2, b ≤ ‖x‖ → χ x = 1 := by
    intro x hx
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hba2]
    nlinarith [norm_nonneg x]
  have hχ0 : ∀ x : E2, ‖x‖ ≤ a → χ x = 0 := by
    intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hba2.le
    nlinarith [norm_nonneg x]
  let u : ClosedCell 2 → E2 := fun z => χ (z : E2) • ((g z : ClosedCell 2) : E2)
  have hval : ContMDiff (𝓡∂ 2) (𝓡 2) ∞ (Subtype.val : ClosedCell 2 → E2) :=
    Handle.closedCellInclusion_contMDiff 1
  have hu : ContMDiff (𝓡∂ 2) 𝓘(ℝ, E2) ∞ u := by
    intro z
    by_cases hz : z ∈ g.source
    · have hg : ContMDiffAt (𝓡∂ 2) (𝓡∂ 2) ∞ g z :=
        (g.contMDiffOn_toFun z hz).contMDiffAt (g.open_source.mem_nhds hz)
      exact ((hχs.contMDiff.comp hval) z).smul ((hval (g z)).comp z hg)
    · have hza : ‖(z : E2)‖ < a := by
        by_contra h
        exact hz (hcollar z (by push Not at h; linarith))
      have hev : u =ᶠ[𝓝 z] fun _ => (0 : E2) := by
        have hop : IsOpen {w : ClosedCell 2 | ‖(w : E2)‖ < a} :=
          isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
        filter_upwards [hop.mem_nhds hza] with w hw
        change χ (w : E2) • _ = 0
        rw [hχ0 _ (le_of_lt hw), zero_smul]
      exact contMDiffAt_const.congr_of_eventuallyEq hev
  have hKc : IsCompact (univ : Set (ClosedCell 2)) := by
    rw [Subtype.isCompact_iff, image_univ, Subtype.range_coe_subtype]
    convert isCompact_closedBall (0 : E2) 1 using 1
    ext x
    simp only [mem_ofPred_eq, mem_closedBall_zero_iff]
  obtain ⟨G, hG, -, -, hGu⟩ :=
    (Handle.closedCellInclusion_isSmoothEmbedding (m := 1)).exists_contDiff_compact_extension_halfspace
      hu hKc isOpen_univ (subset_univ _)
  have hGg : ∀ z : ClosedCell 2, b ≤ ‖(z : E2)‖ → G z = g z := by
    intro z hz
    have h := hGu (mem_univ z)
    change G (z : E2) = χ (z : E2) • _ at h
    rw [h, hχ1 _ hz, one_smul]
  -- the derivative of `G` on the circle
  have hbij : ∀ x : E2, ‖x‖ = 1 → Bijective (fderiv ℝ G x) := by
    intro x hx
    let xc : ClosedCell 2 := ⟨x, hx.le⟩
    have hxs : xc ∈ g.source := hsrc hx
    have hev : (G ∘ (Subtype.val : ClosedCell 2 → E2)) =ᶠ[𝓝 xc]
        ((Subtype.val : ClosedCell 2 → E2) ∘ g) := by
      have hop : IsOpen {w : ClosedCell 2 | b < ‖(w : E2)‖} :=
        isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
      have hxb : xc ∈ {w : ClosedCell 2 | b < ‖(w : E2)‖} := by
        change b < ‖x‖
        rw [hx, hbdef]
        linarith
      filter_upwards [hop.mem_nhds hxb] with w hw
      exact hGg w hw.le
    have hgd : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 2) g xc :=
      ((g.contMDiffOn_toFun xc hxs).contMDiffAt (g.open_source.mem_nhds hxs)).mdifferentiableAt
        (by simp)
    have hinj_g : Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) g xc) := by
      obtain ⟨e, he⟩ := (g.isLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ hxs).isInvertible_mfderiv
        (by simp)
      rw [← he]
      exact e.injective
    have hinj_val : Injective (mfderiv (𝓡∂ 2) (𝓡 2) (Subtype.val : ClosedCell 2 → E2) (g xc)) :=
      injective_mfderiv_of_isImmersionAt (𝓡∂ 2) (𝓡 2) _ _
        ((Handle.closedCellInclusion_isSmoothEmbedding (m := 1)).isImmersion.isImmersionAt _)
    have hi : Injective (mfderiv (𝓡∂ 2) (𝓡 2) (G ∘ (Subtype.val : ClosedCell 2 → E2)) xc) := by
      rw [hev.mfderiv_eq, mfderiv_comp xc ((hval (g xc)).mdifferentiableAt (by simp)) hgd]
      exact hinj_val.comp hinj_g
    rw [mfderiv_comp xc ((hG.contMDiff (x := x)).mdifferentiableAt (by simp))
      ((hval xc).mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at hi
    have hs : Surjective ((fderiv ℝ G x).comp
        (mfderiv (𝓡∂ 2) (𝓡 2) (Subtype.val : ClosedCell 2 → E2) xc)) :=
      LinearMap.surjective_of_injective
        (f := ((fderiv ℝ G x).comp
          (mfderiv (𝓡∂ 2) (𝓡 2) (Subtype.val : ClosedCell 2 → E2) xc)).toLinearMap) hi
    have hGs : Surjective (fderiv ℝ G x) :=
      Surjective.of_comp (f := fderiv ℝ G x)
        (g := mfderiv (𝓡∂ 2) (𝓡 2) (Subtype.val : ClosedCell 2 → E2) xc) hs
    exact ⟨(LinearMap.injective_iff_surjective (f := (fderiv ℝ G x).toLinearMap)).mpr hGs, hGs⟩
  have hGfix : ∀ x : E2, ‖x‖ = 1 → G x = x := by
    intro x hx
    have h := hGg ⟨x, hx.le⟩ (by rw [hx, hbdef]; linarith)
    rw [hfix ⟨x, hx.le⟩ hx] at h
    exact h
  have hloc : IsLocalDiffeomorphOn (𝓡 2) (𝓡 2) ∞ G (sphere (0 : E2) 1) := by
    intro x
    have hx : ‖(x : E2)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ G x)
      (LinearMap.ker_eq_bot.mpr (hbij _ hx).1) (LinearMap.range_eq_top.mpr (hbij _ hx).2)
    exact isLocalDiffeomorphAt_of_hasMFDerivAt_equiv G hG.contMDiff x A
      ((hG.differentiable (by simp) x).hasFDerivAt.hasMFDerivAt)
  have hinjS : InjOn G (sphere (0 : E2) 1) := by
    intro x hx y hy hxy
    rwa [hGfix x (mem_sphere_zero_iff_norm.mp hx), hGfix y (mem_sphere_zero_iff_norm.mp hy)] at hxy
  obtain ⟨φ, hφs, hφG⟩ := DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
    hloc (isCompact_sphere _ _)
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hinjS
  have hUb : IsOpen {x : E2 | b < ‖x‖} := isOpen_lt continuous_const continuous_norm
  let F := DifferentialGeometry.Topology.PartialDiffeomorph.restrict φ _ hUb
  have hFapp : ∀ x, F x = G x := fun x => congrFun hφG x
  have hFsrc : F.source = φ.source ∩ {x : E2 | b < ‖x‖} := rfl
  have hSF : sphere (0 : E2) 1 ⊆ F.source := by
    intro x hx
    rw [hFsrc]
    refine ⟨hφs hx, ?_⟩
    change b < ‖x‖
    rw [mem_sphere_zero_iff_norm.mp hx, hbdef]
    linarith
  have hFfix : EqOn F id (sphere (0 : E2) 1) := fun x hx => by
    rw [hFapp]
    exact hGfix x (mem_sphere_zero_iff_norm.mp hx)
  have hFmap : MapsTo F (closedBall (0 : E2) 1 ∩ F.source) (closedBall (0 : E2) 1) := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx.1
    have hxb : b < ‖x‖ := by rw [hFsrc] at hx; exact hx.2.2
    rw [hFapp, hGg ⟨x, hx1⟩ hxb.le, mem_closedBall_zero_iff]
    exact (g ⟨x, hx1⟩).2
  -- 3. the ambient isotopy, supported in `{‖x‖ > 1 - η}`
  have hOo : IsOpen {x : E2 | 1 - η < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hSO : sphere (0 : E2) 1 ⊆ {x : E2 | 1 - η < ‖x‖} := fun x hx => by
    change 1 - η < ‖x‖
    rw [mem_sphere_zero_iff_norm.mp hx]
    linarith
  obtain ⟨V, hVo, hSV, hVF, Φ, -, -, -, hΦ1, -, hball, L, -, hLO, hLid⟩ :=
    F.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood one_pos hSF hFfix hFmap hOo hSO
  obtain ⟨δ₂, hδ₂, hthickV⟩ := (isCompact_sphere (0 : E2) 1).exists_thickening_subset_open hVo hSV
  let ψ := closedCellDiffeomorph (m := 1) (Φ 1) (hball 1 ⟨zero_le_one, le_rfl⟩)
  set δ : ℝ := min (min δ₂ (δ₀ / 4)) (η / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hδ₂ (by positivity)) (by positivity)
  have hδη : δ < η := (min_le_right _ _).trans_lt (by linarith)
  have hδ4 : δ ≤ δ₀ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ2 : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_left _ _)
  refine ⟨δ, hδ0, hδη, ψ, fun z hz => hcollar z (by change 1 - δ < _ at hz; linarith), ?_, ?_⟩
  · intro z hz
    change 1 - δ < ‖(z : E2)‖ at hz
    have hz1 : ‖(z : E2)‖ ≤ 1 := z.2
    have hz0 : (z : E2) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      linarith
    have hzV : (z : E2) ∈ V := hthickV (mem_thickening_sphere_of_abs_norm_sub_one_lt hz0 (by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith))
    apply Subtype.ext
    change Φ 1 (z : E2) = ((g z : ClosedCell 2) : E2)
    rw [hΦ1 hzV, hFapp, hGg z (by rw [hbdef]; linarith)]
  · intro z hz
    change ‖(z : E2)‖ ≤ 1 - η at hz
    apply Subtype.ext
    change Φ 1 (z : E2) = (z : E2)
    have hzL : (z : E2) ∈ Lᶜ := fun h => by
      have := hLO h
      change 1 - η < ‖(z : E2)‖ at this
      linarith
    exact ((hLid 1).1 hzL)

end DifferentialGeometry.Topology.Manifold
