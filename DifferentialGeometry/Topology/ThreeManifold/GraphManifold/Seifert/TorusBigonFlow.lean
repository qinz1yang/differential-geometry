import DifferentialGeometry.Topology.Diffeomorph.Flow
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Pushing a parabolic lens below its straight side

A compactly supported vertical flow on `ℝ × ℝ` that moves the parabola `u = 1 - v ^ 2` strictly
below the line `u = 0`, supported in a prescribed neighbourhood of the lens it bounds.
-/

set_option autoImplicit false

noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace GC.Seifert

private theorem isCompact_lens :
    IsCompact {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ 1 - z.2 ^ 2} := by
  refine ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst (continuous_const.sub (continuous_snd.pow 2)))
  · rintro ⟨u, v⟩ ⟨h0, h1⟩
    refine ⟨⟨h0, by nlinarith⟩, ?_, ?_⟩ <;> nlinarith

private theorem cthickening_lens_box {ε : ℝ} (hε : 0 ≤ ε) {z : ℝ × ℝ}
    (hz : z ∈ Metric.cthickening ε {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ 1 - z.2 ^ 2}) :
    -ε ≤ z.1 ∧ -1 - ε ≤ z.2 ∧ z.2 ≤ 1 + ε := by
  rw [isCompact_lens.cthickening_eq_biUnion_closedBall hε] at hz
  simp only [mem_iUnion, Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, max_le_iff,
    abs_le] at hz
  obtain ⟨x, ⟨hx0, hx1⟩, ⟨h1, h2⟩, h3, h4⟩ := hz
  refine ⟨by linarith, ?_, ?_⟩ <;> nlinarith

theorem exists_lens_push {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hXW : {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ 1 - z.2 ^ 2} ⊆ W) {r : ℝ} (hr : 0 < r) :
    ∃ H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (H q.1).symm q.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ ∧
      ∃ S : Set (ℝ × ℝ), IsCompact S ∧ S ⊆ W ∧
        S ∩ {z | z.1 < 0} ⊆ Ioo (-r) 0 ×ˢ Ioo (-1 - r) (1 + r) ∧
        (∀ s z, z ∉ S → H s z = z) ∧
        (∀ s z, (H s z).2 = z.2) ∧
        ∀ τ : ℝ, (H 1 (1 - τ ^ 2, τ)).1 < 0 := by
  set X : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ z.1 ≤ 1 - z.2 ^ 2}
  have hXc : IsCompact X := isCompact_lens
  obtain ⟨δ, hδ, hδW⟩ := hXc.exists_cthickening_subset_open hW hXW
  set ε := min δ (r / 2)
  have hε0 : 0 < ε := lt_min hδ (half_pos hr)
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℝ × ℝ)
    (n := (⊤ : ℕ∞)) (Metric.isOpen_thickening (δ := ε) (E := X)).isClosed_compl hXc.isClosed
    (disjoint_compl_left_iff_subset.mpr (Metric.self_subset_thickening hε0 X))
  have hfs : ContDiff ℝ ∞ (f : ℝ × ℝ → ℝ) := contMDiff_iff_contDiff.mp f.contMDiff
  let V : (z : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) z := fun z => (-(2 * f z), (0 : ℝ))
  have hVs : ContDiff ℝ ∞ V := ((contDiff_const.mul hfs).neg).prodMk contDiff_const
  have hV : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, ℝ × ℝ)) ∞
      (fun z : ℝ × ℝ => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hVs
  set S := Metric.cthickening ε X
  have hSc : IsCompact S := hXc.cthickening
  have hVS : tsupport V ⊆ S := by
    refine (closure_mono ?_).trans (Metric.closure_thickening_subset_cthickening ε X)
    intro z hz
    by_contra hzt
    apply hz
    have h0 : f z = 0 := hf0 hzt
    change ((-(2 * f z), (0 : ℝ)) : ℝ × ℝ) = 0
    simp [h0]
  have hVc : IsCompact (tsupport V) := hSc.of_isClosed_subset (isClosed_tsupport _) hVS
  set H := Diffeomorph.compactSupportFlow V hV hVc
  have hcurve (z : ℝ × ℝ) (t : ℝ) : HasDerivAt (fun s => H s z) (V (H t z)) t := by
    have h := Diffeomorph.isMIntegralCurve_compactSupportFlow V hV hVc z t
    exact hasDerivAt_iff_hasFDerivAt.mpr (hasMFDerivAt_iff_hasFDerivAt.mp h)
  have hfst (z : ℝ × ℝ) (t : ℝ) :
      HasDerivAt (fun s => (H s z).1) (-(2 * f (H t z))) t := by
    have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := H t z)).comp_hasDerivAt t (hcurve z t)
    exact h
  have hsnd (z : ℝ × ℝ) (t : ℝ) : HasDerivAt (fun s => (H s z).2) 0 t := by
    have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := H t z)).comp_hasDerivAt t (hcurve z t)
    exact h
  have hH0 : H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ :=
    Diffeomorph.compactSupportFlow_zero V hV hVc
  have hv (s : ℝ) (z : ℝ × ℝ) : (H s z).2 = z.2 := by
    have hc := is_const_of_deriv_eq_zero (fun t => (hsnd z t).differentiableAt)
      (fun t => (hsnd z t).deriv) s 0
    rw [hc, hH0]
    rfl
  have hanti (z : ℝ × ℝ) : Antitone (fun s => (H s z).1) := by
    refine antitone_of_deriv_nonpos (fun t => (hfst z t).differentiableAt) (fun t => ?_)
    rw [(hfst z t).deriv]
    have := (hf01 (H t z)).1
    linarith
  refine ⟨H, ?_, ?_, hH0, S, hSc, ?_, ?_, ?_, hv, ?_⟩
  · have h := Diffeomorph.contMDiff_compactSupportFlow V hV hVc
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact contMDiff_iff_contDiff.mp h
  · have h := Diffeomorph.contMDiff_compactSupportFlow_symm V hV hVc
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact contMDiff_iff_contDiff.mp h
  · exact (Metric.cthickening_mono (min_le_left _ _) X).trans hδW
  · rintro z ⟨hzS, hz0⟩
    obtain ⟨h1, h2, h3⟩ := cthickening_lens_box hε0.le hzS
    have hεr : ε < r := (min_le_right _ _).trans_lt (half_lt_self hr)
    exact ⟨⟨by linarith, hz0⟩, by linarith, by linarith⟩
  · intro s z hz
    exact (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport V hV hVc s).1 (fun h => hz (hVS h))
  · intro τ
    by_contra hneg
    push Not at hneg
    set z : ℝ × ℝ := (1 - τ ^ 2, τ)
    have hz0 : (H 0 z).1 = 1 - τ ^ 2 := by rw [hH0]; rfl
    have hinX (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : H t z ∈ X := by
      have hle1 := hanti z ht1
      have hle0 := hanti z ht0
      simp only at hle1 hle0
      refine ⟨by linarith, ?_⟩
      rw [hv t z]
      change (H t z).1 ≤ 1 - τ ^ 2
      linarith
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun s => (H s z).1)
      (fun s => -(2 * f (H s z))) zero_lt_one
      (fun t _ => (hfst z t).continuousAt.continuousWithinAt) (fun t _ => hfst z t)
    rw [hf1 (hinX c hc.1.le hc.2.le), hz0] at hcd
    simp only [Pi.one_apply] at hcd
    have hτ := sq_nonneg τ
    linarith

end GC.Seifert
