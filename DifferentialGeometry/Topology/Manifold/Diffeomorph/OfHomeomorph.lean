import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A `C¹` homeomorphism with invertible differentials is a `C¹` diffeomorphism

Manifolds with boundary or corners are allowed (no `Boundaryless` hypothesis): the inverse is
differentiated within the range of the model, using `HasFDerivWithinAt.of_local_left_inverse`.

* `contDiffOn_one_of_leftInverse_of_isInvertible` (Euclidean kernel): a continuous right inverse
  `g` on `T` of a `C¹` map `f` on `S` with invertible derivatives is `C¹` on `T`
  (`S`, `T` with unique derivatives, e.g. relatively open subsets of half-spaces);
* `isInvertible_fderivWithin_extChartAt_comp`: invertibility of `mfderiv f` at a point of a chart
  domain is invertibility of the derivative (within the model range) of the coordinate expression
  of `f` in arbitrary fixed extended charts;
* `contMDiff_symm_of_isInvertible_mfderiv`, `Homeomorph.toDiffeomorphOfIsInvertibleMFDeriv`: a
  homeomorphism `f : M ≃ₜ N` that is `C¹` with invertible `mfderiv` everywhere is a
  `C¹` diffeomorphism.

The tree's other inverse tools need either boundaryless models (`InverseFunctionTheorem/Basic`) or
a diffeomorphism to start from (`contMDiffOn_diffeomorph_symm_image`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold

section Euclidean

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Euclidean kernel.** A continuous right inverse `g : T → S` of a map `f` that is `C¹` on `S`
with invertible derivatives (within `S`) is `C¹` on `T`. -/
theorem contDiffOn_one_of_leftInverse_of_isInvertible {S : Set E} {T : Set F}
    (hS : UniqueDiffOn ℝ S) (hT : UniqueDiffOn ℝ T) {f : E → F} {g : F → E}
    (hf : ContDiffOn ℝ 1 f S) (hg : ContinuousOn g T) (hgT : MapsTo g T S)
    (hfg : ∀ y ∈ T, f (g y) = y) (hinv : ∀ y ∈ T, (fderivWithin ℝ f S (g y)).IsInvertible) :
    ContDiffOn ℝ 1 g T := by
  have hd : ∀ y ∈ T, HasFDerivWithinAt g
      (ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y))) T y := by
    intro y hy
    obtain ⟨e, he⟩ := hinv y hy
    have hf' : HasFDerivWithinAt f (e : E →L[ℝ] F) S (g y) := by
      rw [he]
      exact ((hf.differentiableOn one_ne_zero) (g y) (hgT hy)).hasFDerivWithinAt
    have h := hf'.of_local_left_inverse ((hg y hy).tendsto_nhdsWithin hgT) hy
      (eventually_nhdsWithin_of_forall hfg)
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact h
  have hfd : ∀ y ∈ T, fderivWithin ℝ g T y =
      ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y)) :=
    fun y hy => (hd y hy).fderivWithin (hT y hy)
  have h1 : ContDiffOn ℝ ((0 : ℕ∞ω) + 1) g T := by
    rw [contDiffOn_succ_iff_fderivWithin hT]
    refine ⟨fun y hy => (hd y hy).differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    have hcf : ContinuousOn (fun y => fderivWithin ℝ f S (g y)) T :=
      (hf.continuousOn_fderivWithin hS le_rfl).comp hg hgT
    intro y hy
    have hic : ContinuousAt ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y)) :=
      ((hinv y hy).contDiffAt_map_inverse (n := 0)).continuousAt
    have hc : ContinuousWithinAt
        (fun y => ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y))) T y :=
      ContinuousAt.comp_continuousWithinAt (f := fun y => fderivWithin ℝ f S (g y)) hic (hcf y hy)
    exact hc.congr (fun y' hy' => hfd y' hy') (hfd y hy)
  simpa using h1

end Euclidean

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

omit [CompleteSpace E] in
/-- Invertibility of `mfderiv f` at a point of a chart domain gives invertibility of the
derivative (within the model range) of the coordinate expression of `f` in fixed extended charts. -/
theorem isInvertible_fderivWithin_extChartAt_comp {f : M → N} (hf : ContMDiff I J 1 f)
    {x₀ : M} {y₀ : N} {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hfz : f ((extChartAt I x₀).symm z) ∈ (extChartAt J y₀).source)
    (hinv : (mfderiv I J f ((extChartAt I x₀).symm z)).IsInvertible) :
    (fderivWithin ℝ (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) (range I) z).IsInvertible := by
  set x := (extChartAt I x₀).symm z with hx
  have h1 : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z :=
    mdifferentiableWithinAt_extChartAt_symm hz
  have h2 : MDifferentiableAt I J f x := hf.mdifferentiableAt one_ne_zero
  have h3 : MDifferentiableAt J 𝓘(ℝ, E') (extChartAt J y₀) (f x) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hfz)
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, E) (range I) z :=
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt).mpr
      (I.uniqueDiffOn z (extChartAt_target_subset_range x₀ hz))
  have hc : mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E') (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
      (range I) z = (mfderiv J 𝓘(ℝ, E') (extChartAt J y₀) (f x)).comp
        ((mfderiv I J f x).comp (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z)) := by
    have h23 : MDifferentiableAt I 𝓘(ℝ, E') (extChartAt J y₀ ∘ f) x := h3.comp x h2
    rw [show extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm =
      (extChartAt J y₀ ∘ f) ∘ (extChartAt I x₀).symm from rfl,
      mfderiv_comp_mfderivWithin z h23 h1 hu, mfderiv_comp x h3 h2]
    rfl
  have hmi : (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E') (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
      (range I) z).IsInvertible := by
    rw [hc]
    exact (isInvertible_mfderiv_extChartAt (by simpa only [extChartAt_source] using hfz)).comp
      (hinv.comp (isInvertible_mfderivWithin_extChartAt_symm hz))
  obtain ⟨e, he⟩ := hmi
  have hm := mfderivWithin_eq_fderivWithin (𝕜 := ℝ)
    (f := extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) (s := range I) (x := z)
  refine ⟨((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.trans e).trans
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z)), ?_⟩
  ext v
  have h := congrArg (fun L => L ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) (he.trans hm)
  simp only [ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply, h]
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) _).apply_symm_apply _

/-- **A `C¹` homeomorphism with invertible differentials has a `C¹` inverse** (boundary and
corners allowed). -/
theorem contMDiff_symm_of_isInvertible_mfderiv (f : M ≃ₜ N) (hf : ContMDiff I J 1 f)
    (hinv : ∀ x, (mfderiv I J f x).IsInvertible) : ContMDiff J I 1 f.symm := by
  intro y₀
  set x₀ := f.symm y₀ with hx₀
  set φ := extChartAt I x₀ with hφ
  set ψ := extChartAt J y₀ with hψ
  rw [contMDiffAt_iff]
  refine ⟨f.symm.continuous.continuousAt, ?_⟩
  set S : Set E := φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source) with hSdef
  set T : Set E' := ψ.target ∩ ψ.symm ⁻¹' (f.symm ⁻¹' φ.source) with hTdef
  -- unique differentiability
  obtain ⟨VS, hVS, hVSe⟩ := (continuousOn_iff'.mp (continuousOn_extChartAt_symm (I := I) x₀))
    (f ⁻¹' ψ.source) ((isOpen_extChartAt_source y₀).preimage f.continuous)
  have hSV : φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source) = φ.target ∩ VS := by
    rw [inter_comm, hVSe, inter_comm]
  obtain ⟨VT, hVT, hVTe⟩ := (continuousOn_iff'.mp (continuousOn_extChartAt_symm (I := J) y₀))
    (f.symm ⁻¹' φ.source) ((isOpen_extChartAt_source x₀).preimage f.symm.continuous)
  have hTV : ψ.target ∩ ψ.symm ⁻¹' (f.symm ⁻¹' φ.source) = ψ.target ∩ VT := by
    rw [inter_comm, hVTe, inter_comm]
  have hS : UniqueDiffOn ℝ S := by
    rw [hSdef, hSV]
    exact (uniqueDiffOn_extChartAt_target x₀).inter hVS
  have hT : UniqueDiffOn ℝ T := by
    rw [hTdef, hTV]
    exact (uniqueDiffOn_extChartAt_target y₀).inter hVT
  -- the coordinate expressions
  have hRf : ContDiffOn ℝ 1 (ψ ∘ f ∘ φ.symm) S := by
    have h1 : ContMDiffOn 𝓘(ℝ, E) J 1 (f ∘ φ.symm) S :=
      (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀)).mono inter_subset_left
    have h : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') 1 (ψ ∘ (f ∘ φ.symm)) S :=
      (contMDiffOn_extChartAt (n := 1) (x := y₀)).comp h1 (fun y hy => by
        have h' : f (φ.symm y) ∈ ψ.source := hy.2
        rw [hψ, extChartAt_source] at h'
        exact h')
    exact contMDiffOn_iff_contDiffOn.mp h
  have hRg : ContinuousOn (φ ∘ f.symm ∘ ψ.symm) T := by
    refine (continuousOn_extChartAt x₀).comp ?_ ?_
    · exact f.symm.continuous.comp_continuousOn
        ((continuousOn_extChartAt_symm y₀).mono inter_subset_left)
    · intro y hy
      exact hy.2
  have hmaps : MapsTo (φ ∘ f.symm ∘ ψ.symm) T S := by
    intro y hy
    have hsrc : f.symm (ψ.symm y) ∈ φ.source := hy.2
    refine ⟨φ.map_source hsrc, ?_⟩
    simp only [mem_preimage, comp_apply, φ.left_inv hsrc, f.apply_symm_apply]
    exact ψ.map_target hy.1
  have hfg : ∀ y ∈ T, (ψ ∘ f ∘ φ.symm) ((φ ∘ f.symm ∘ ψ.symm) y) = y := by
    intro y hy
    have hsrc : f.symm (ψ.symm y) ∈ φ.source := hy.2
    simp only [comp_apply, φ.left_inv hsrc, f.apply_symm_apply]
    exact ψ.right_inv hy.1
  have hinv' : ∀ y ∈ T,
      (fderivWithin ℝ (ψ ∘ f ∘ φ.symm) S ((φ ∘ f.symm ∘ ψ.symm) y)).IsInvertible := by
    intro y hy
    have hz := hmaps hy
    have hS' : S = range I ∩ (I.symm ⁻¹' (chartAt H x₀).target ∩ VS) := by
      rw [hSdef, hSV, hφ, extChartAt_target]
      ext w
      simp only [mem_inter_iff, mem_preimage]
      tauto
    have hO : I.symm ⁻¹' (chartAt H x₀).target ∩ VS ∈ 𝓝 ((φ ∘ f.symm ∘ ψ.symm) y) := by
      refine (((chartAt H x₀).open_target.preimage I.continuous_symm).inter hVS).mem_nhds ?_
      rw [hS'] at hz
      exact hz.2
    rw [hS', fderivWithin_inter hO]
    exact isInvertible_fderivWithin_extChartAt_comp hf hz.1 hz.2 (hinv _)
  have hg1 := contDiffOn_one_of_leftInverse_of_isInvertible hS hT hRf hRg hmaps hfg hinv'
  have hy₀T : ψ y₀ ∈ T := by
    refine ⟨mem_extChartAt_target y₀, ?_⟩
    simp only [mem_preimage, hψ, extChartAt_to_inv]
    exact mem_extChartAt_source _
  have hTnhds : T ∈ 𝓝[range J] (ψ y₀) := by
    refine inter_mem (extChartAt_target_mem_nhdsWithin y₀) ?_
    have h := extChartAt_preimage_mem_nhdsWithin (I := J) (x := y₀) (s := univ)
      (t := f.symm ⁻¹' φ.source)
      (mem_nhdsWithin_of_mem_nhds (((isOpen_extChartAt_source x₀).preimage
        f.symm.continuous).mem_nhds (mem_extChartAt_source _)))
    simpa only [preimage_univ, univ_inter] using h
  exact (hg1 _ hy₀T).mono_of_mem_nhdsWithin hTnhds

/-- A homeomorphism that is `C¹` with invertible `mfderiv` everywhere, as a `C¹` diffeomorphism. -/
def _root_.Homeomorph.toDiffeomorphOfIsInvertibleMFDeriv (f : M ≃ₜ N) (hf : ContMDiff I J 1 f)
    (hinv : ∀ x, (mfderiv I J f x).IsInvertible) : M ≃ₘ^1⟮I, J⟯ N where
  toEquiv := f.toEquiv
  contMDiff_toFun := hf
  contMDiff_invFun := contMDiff_symm_of_isInvertible_mfderiv f hf hinv

@[simp]
theorem _root_.Homeomorph.coe_toDiffeomorphOfIsInvertibleMFDeriv (f : M ≃ₜ N)
    (hf : ContMDiff I J 1 f) (hinv : ∀ x, (mfderiv I J f x).IsInvertible) :
    ⇑(f.toDiffeomorphOfIsInvertibleMFDeriv hf hinv) = f :=
  rfl

end Manifold

/-- **Concrete consumer.** Scaling `x ↦ 2 x` of `ℝ`, given only as a homeomorphism, is a
`C¹` diffeomorphism. -/
theorem nonempty_diffeomorph_two_mul :
    ∃ Φ : ℝ ≃ₘ^1⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ, ∀ x, Φ x = 2 * x := by
  let f : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ (2 : ℝ) two_ne_zero
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 f := (contDiff_const.mul contDiff_id).contMDiff
  have hinv : ∀ x, (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f x).IsInvertible := by
    intro x
    have hd : HasFDerivAt (fun y : ℝ => 2 * y) ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) x := by
      simpa using (hasFDerivAt_id x).const_mul (2 : ℝ)
    have hm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f x = (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ :=
      hd.hasMFDerivAt.mfderiv
    rw [hm]
    refine ⟨(LinearEquiv.smulOfNeZero ℝ ℝ (2 : ℝ) two_ne_zero).toContinuousLinearEquiv, ?_⟩
    ext
    rfl
  exact ⟨f.toDiffeomorphOfIsInvertibleMFDeriv hf hinv, fun x => rfl⟩

end DifferentialGeometry.Topology.Manifold
