import DifferentialGeometry.Analysis.Elliptic.Planar.BoundaryCauchyJets

set_option autoImplicit false
noncomputable section

open Set Filter InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem secondJet_comp_zero
    {w : ℂ → ℝ} {f : ℂ → ℂ} {y : ℂ}
    (hw : ContDiffAt ℝ 2 w (f y)) (hf : ContDiffAt ℝ 2 f y)
    (hd0 : fderiv ℝ w (f y) = 0) (hdd0 : fderiv ℝ (fderiv ℝ w) (f y) = 0) :
    fderiv ℝ (fun z => w (f z)) y = 0 ∧
      fderiv ℝ (fderiv ℝ (fun z => w (f z))) y = 0 := by
  have hwd := (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfd := hf.differentiableAt (by norm_num)
  have hfdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : fderiv ℝ (fun z => w (f z)) =ᶠ[𝓝 y]
      fun z => (fderiv ℝ w (f z)).comp (fderiv ℝ f z) := by
    filter_upwards [hf.eventually (by norm_num),
      hf.continuousAt (hw.eventually (by norm_num))] with z hfz hwz
    change ContDiffAt ℝ 2 w (f z) at hwz
    exact fderiv_fun_comp z (hwz.differentiableAt (by norm_num))
      (hfz.differentiableAt (by norm_num))
  constructor
  · rw [fderiv_fun_comp y (hw.differentiableAt (by norm_num)) hfd, hd0]
    rfl
  · have hsecond := ((hwd.hasFDerivAt.comp y hfd.hasFDerivAt).clm_comp
      hfdd.hasFDerivAt).fderiv
    simp only [Function.comp_def] at hsecond
    rw [hnear.fderiv_eq, hsecond]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, hd0, hdd0, zero_apply, add_zero]

/-- Transport the actual one-sided original scalar equation and its derived
vanishing seam jets through the supplied isothermal coordinate map. The new
side is its literal image, so a curved isothermal seam is retained. No equation
is asserted on the opposite side and the coordinate map is never reselected. -/
theorem planarScalarOperator_isothermal_cauchy_data
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ)
    (e : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) e.source)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun x => beta x i) e.source)
    (hc : ContDiffOn ℝ ∞ c e.source) (hw : ContDiffOn ℝ ∞ w e.source)
    (hpos : ∀ x ∈ e.source, (A x).PosDef)
    (hpde : ∀ x ∈ e.source, 0 < x.im → planarScalarOperator A beta c w x = 0)
    (hzero : ∀ x ∈ e.source, x.im = 0 → w x = 0 ∧ fderiv ℝ w x = 0)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hlam : ContDiffOn ℝ ∞ lam e.source) (hlampos : ∀ x ∈ e.source, 0 < lam x)
    (hprincipal : ∀ x ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
        H (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
          (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) =
        lam x * (H 1 1 + H Complex.I Complex.I)) :
    let v : ℂ → ℝ := fun y => w (e.symm y)
    let B : ℂ → ℂ := fun y => (lam (e.symm y))⁻¹ •
      planarCoordinateDrift A beta e (e.symm y)
    let q : ℂ → ℝ := fun y => c (e.symm y) / lam (e.symm y)
    let s := e '' (e.source ∩ {x : ℂ | 0 < x.im})
    IsOpen s ∧ s ⊆ e.target ∧
      ContDiffOn ℝ ∞ v e.target ∧ ContDiffOn ℝ ∞ B e.target ∧
      ContDiffOn ℝ ∞ q e.target ∧
      (∀ y ∈ s, Laplacian.laplacian v y + fderiv ℝ v y (B y) + q y * v y = 0) ∧
      (∀ y ∈ e.target ∩ frontier s,
        planarGradientSection v y = 0 ∧ fderiv ℝ (planarGradientSection v) y = 0) ∧
      (∀ x ∈ e.source, v (e x) = w x) ∧
      (∀ y ∈ e.target, y ∈ s ↔ 0 < (e.symm y).im) := by
  intro v B q s
  have hsdef : s = e.target ∩ e.symm ⁻¹' {x : ℂ | 0 < x.im} :=
    e.image_source_inter_eq' _
  have hs : IsOpen s := e.isOpen_image_source_inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hst : s ⊆ e.target := by rw [hsdef]; exact inter_subset_left
  have hmem (y : ℂ) (hy : y ∈ e.target) : y ∈ s ↔ 0 < (e.symm y).im := by
    rw [hsdef]
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  have hv : ContDiffOn ℝ ∞ v e.target := hw.comp hei (fun y hy => e.map_target hy)
  have hB : ContDiffOn ℝ ∞ B e.target :=
    ((hlam.inv (fun x hx => (hlampos x hx).ne')).smul
      (contDiffOn_planarCoordinateDrift e.open_source hA hbeta he)).comp hei
        (fun y hy => e.map_target hy)
  have hq : ContDiffOn ℝ ∞ q e.target :=
    (hc.div hlam (fun x hx => (hlampos x hx).ne')).comp hei (fun y hy => e.map_target hy)
  have hPDE : ∀ y ∈ s,
      Laplacian.laplacian v y + fderiv ℝ v y (B y) + q y * v y = 0 := by
    intro y hys
    have hy := hst hys
    have hx := e.map_target hy
    have hpush := planarScalarOperator_pushforward A beta c e
      (hw.of_le (by simp)) (he.of_le (by simp)) (hei.of_le (by simp)) hy
    change planarScalarOperator A beta c w (e.symm y) = _ at hpush
    rw [hpde _ hx ((hmem y hy).mp hys), hprincipal _ hx] at hpush
    have hlap : Laplacian.laplacian v y =
        fderiv ℝ (fderiv ℝ v) y 1 1 + fderiv ℝ (fderiv ℝ v) y Complex.I Complex.I := by
      rw [laplacian_eq_iteratedFDeriv_complexPlane]
      simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hlap]
    change _ + fderiv ℝ v y ((lam (e.symm y))⁻¹ •
      planarCoordinateDrift A beta e (e.symm y)) +
        (c (e.symm y) / lam (e.symm y)) * v y = 0
    rw [map_smul, smul_eq_mul]
    have hn := (hlampos _ hx).ne'
    apply mul_left_cancel₀ hn
    rw [mul_zero]
    calc
      _ = lam (e.symm y) *
          (fderiv ℝ (fderiv ℝ v) y 1 1 + fderiv ℝ (fderiv ℝ v) y Complex.I Complex.I) +
          fderiv ℝ v y (planarCoordinateDrift A beta e (e.symm y)) + c (e.symm y) * v y := by
            field_simp [hn]
      _ = 0 := hpush.symm
  have hwjet := fderiv_fderiv_eq_zero_on_flat_seam_of_planarScalarOperator
    e.open_source hA hbeta hc hw hpos hpde hzero
  refine ⟨hs, hst, hv, hB, hq, hPDE, ?_,
    fun x hx => congrArg w (e.left_inv hx), hmem⟩
  intro y hy
  have hyfront := hy.2
  rw [frontier, hs.interior_eq] at hyfront
  have hnpos : ¬ 0 < (e.symm y).im := fun hh => hyfront.2 ((hmem y hy.1).mpr hh)
  have hnneg : ¬ (e.symm y).im < 0 := by
    intro hh
    let N := e.target ∩ e.symm ⁻¹' {x : ℂ | x.im < 0}
    have hN : IsOpen N := e.isOpen_inter_preimage_symm
      (isOpen_lt Complex.continuous_im continuous_const)
    obtain ⟨z, hzN, hzs⟩ := mem_closure_iff.mp hyfront.1 N hN ⟨hy.1, hh⟩
    exact (not_lt_of_ge ((hmem z (hst hzs)).mp hzs).le) hzN.2
  have him : (e.symm y).im = 0 := le_antisymm (le_of_not_gt hnpos) (le_of_not_gt hnneg)
  have hx := e.map_target hy.1
  obtain ⟨hw0, hd0⟩ := hzero _ hx him
  have hww : ContDiffAt ℝ 2 w (e.symm y) :=
    (hw.contDiffAt (e.open_source.mem_nhds hx)).of_le (by simp)
  have hee : ContDiffAt ℝ 2 e.symm y :=
    (hei.contDiffAt (e.open_target.mem_nhds hy.1)).of_le (by simp)
  obtain ⟨hv0, hvv0⟩ := secondJet_comp_zero hww hee hd0 (hwjet _ hx him)
  exact planarGradientSection_firstJet_zero_of_secondJet_zero
    ((hv.contDiffAt (e.open_target.mem_nhds hy.1)).of_le (by simp)) hw0 hv0 hvv0

/-- Transport a regular curved original frontier and its derived second jets
through the same isothermal map. Both the projected original side and its
isothermal image are literal supplied sets; no straight-seam hypothesis or
opposite-side equation is used. -/
theorem planarScalarOperator_isothermal_cauchy_data_on_regular_side
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ)
    (e : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ)
    (S : Set ℂ) (hS : IsOpen S) (hSU : S ⊆ e.source)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) e.source)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun x => beta x i) e.source)
    (hc : ContDiffOn ℝ ∞ c e.source) (hw : ContDiffOn ℝ ∞ w e.source)
    (hpos : ∀ x ∈ e.source, (A x).PosDef)
    (hpde : ∀ x ∈ S, planarScalarOperator A beta c w x = 0)
    (hzero : ∀ x ∈ e.source ∩ frontier S, w x = 0 ∧ fderiv ℝ w x = 0)
    (hcurve : ∀ x ∈ e.source ∩ frontier S, ∃ (γ : ℝ → ℂ) (τ : ℂ),
      γ 0 = x ∧ HasDerivAt γ τ 0 ∧ τ ≠ 0 ∧
        ∀ᶠ t in 𝓝 0, γ t ∈ e.source ∩ frontier S)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hlam : ContDiffOn ℝ ∞ lam e.source) (hlampos : ∀ x ∈ e.source, 0 < lam x)
    (hprincipal : ∀ x ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
        H (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
          (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) =
        lam x * (H 1 1 + H Complex.I Complex.I)) :
    let v : ℂ → ℝ := fun y => w (e.symm y)
    let B : ℂ → ℂ := fun y => (lam (e.symm y))⁻¹ •
      planarCoordinateDrift A beta e (e.symm y)
    let q : ℂ → ℝ := fun y => c (e.symm y) / lam (e.symm y)
    let s := e '' (e.source ∩ S)
    IsOpen s ∧ s ⊆ e.target ∧
      ContDiffOn ℝ ∞ v e.target ∧ ContDiffOn ℝ ∞ B e.target ∧
      ContDiffOn ℝ ∞ q e.target ∧
      (∀ y ∈ s, Laplacian.laplacian v y + fderiv ℝ v y (B y) + q y * v y = 0) ∧
      (∀ y ∈ e.target ∩ frontier s,
        planarGradientSection v y = 0 ∧ fderiv ℝ (planarGradientSection v) y = 0) ∧
      (∀ x ∈ e.source, v (e x) = w x) ∧
      (∀ y ∈ e.target, y ∈ s ↔ e.symm y ∈ S) := by
  intro v B q s
  have hsdef : s = e.target ∩ e.symm ⁻¹' S :=
    e.image_source_inter_eq' _
  have hs : IsOpen s := e.isOpen_image_source_inter hS
  have hst : s ⊆ e.target := by rw [hsdef]; exact inter_subset_left
  have hmem (y : ℂ) (hy : y ∈ e.target) : y ∈ s ↔ e.symm y ∈ S := by
    rw [hsdef]
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  have hv : ContDiffOn ℝ ∞ v e.target := hw.comp hei (fun y hy => e.map_target hy)
  have hB : ContDiffOn ℝ ∞ B e.target :=
    ((hlam.inv (fun x hx => (hlampos x hx).ne')).smul
      (contDiffOn_planarCoordinateDrift e.open_source hA hbeta he)).comp hei
        (fun y hy => e.map_target hy)
  have hq : ContDiffOn ℝ ∞ q e.target :=
    (hc.div hlam (fun x hx => (hlampos x hx).ne')).comp hei (fun y hy => e.map_target hy)
  have hPDE : ∀ y ∈ s,
      Laplacian.laplacian v y + fderiv ℝ v y (B y) + q y * v y = 0 := by
    intro y hys
    have hy := hst hys
    have hx := e.map_target hy
    have hpush := planarScalarOperator_pushforward A beta c e
      (hw.of_le (by simp)) (he.of_le (by simp)) (hei.of_le (by simp)) hy
    change planarScalarOperator A beta c w (e.symm y) = _ at hpush
    rw [hpde _ ((hmem y hy).mp hys), hprincipal _ hx] at hpush
    have hlap : Laplacian.laplacian v y =
        fderiv ℝ (fderiv ℝ v) y 1 1 + fderiv ℝ (fderiv ℝ v) y Complex.I Complex.I := by
      rw [laplacian_eq_iteratedFDeriv_complexPlane]
      simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hlap]
    change _ + fderiv ℝ v y ((lam (e.symm y))⁻¹ •
      planarCoordinateDrift A beta e (e.symm y)) +
        (c (e.symm y) / lam (e.symm y)) * v y = 0
    rw [map_smul, smul_eq_mul]
    have hn := (hlampos _ hx).ne'
    apply mul_left_cancel₀ hn
    rw [mul_zero]
    calc
      _ = lam (e.symm y) *
          (fderiv ℝ (fderiv ℝ v) y 1 1 + fderiv ℝ (fderiv ℝ v) y Complex.I Complex.I) +
          fderiv ℝ v y (planarCoordinateDrift A beta e (e.symm y)) + c (e.symm y) * v y := by
            field_simp [hn]
      _ = 0 := hpush.symm
  have hwjet := fderiv_fderiv_eq_zero_on_regular_frontier_of_planarScalarOperator
    e.open_source hSU hA hbeta hc hw hpos hpde hzero hcurve
  refine ⟨hs, hst, hv, hB, hq, hPDE, ?_,
    fun x hx => congrArg w (e.left_inv hx), hmem⟩
  intro y hy
  have hyfront := hy.2
  rw [frontier, hs.interior_eq] at hyfront
  have hx := e.map_target hy.1
  have hxcl : e.symm y ∈ closure S := by
    apply mem_closure_iff.mpr
    intro N hN hxN
    have hM : IsOpen (e '' (e.source ∩ N)) := e.isOpen_image_source_inter hN
    have hyM : y ∈ e '' (e.source ∩ N) :=
      ⟨e.symm y, ⟨hx, hxN⟩, e.right_inv hy.1⟩
    obtain ⟨z, hzM, hzs⟩ := mem_closure_iff.mp hyfront.1 _ hM hyM
    obtain ⟨x, hxN', hxeq⟩ := hzM
    have hzN : e.symm z ∈ N := by
      rw [← hxeq, e.left_inv hxN'.1]
      exact hxN'.2
    exact ⟨e.symm z, hzN, (hmem z (hst hzs)).mp hzs⟩
  have hxnS : e.symm y ∉ S := fun hh => hyfront.2 ((hmem y hy.1).mpr hh)
  have hxfront : e.symm y ∈ frontier S := by
    rw [frontier, hS.interior_eq]
    exact ⟨hxcl, hxnS⟩
  obtain ⟨hw0, hd0⟩ := hzero _ ⟨hx, hxfront⟩
  have hww : ContDiffAt ℝ 2 w (e.symm y) :=
    (hw.contDiffAt (e.open_source.mem_nhds hx)).of_le (by simp)
  have hee : ContDiffAt ℝ 2 e.symm y :=
    (hei.contDiffAt (e.open_target.mem_nhds hy.1)).of_le (by simp)
  obtain ⟨hv0, hvv0⟩ := secondJet_comp_zero hww hee hd0 (hwjet _ ⟨hx, hxfront⟩)
  exact planarGradientSection_firstJet_zero_of_secondJet_zero
    ((hv.contDiffAt (e.open_target.mem_nhds hy.1)).of_le (by simp)) hw0 hv0 hvv0

end DifferentialGeometry.Analysis
