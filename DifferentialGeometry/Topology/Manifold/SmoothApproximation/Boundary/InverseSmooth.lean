import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of the inverse of a finite-order diffeomorphism where it is smooth

`contMDiffOn_diffeomorph_symm_image`: if `h : M ≃ₘ^k⟮I, J⟯ N` is a `C^k`
diffeomorphism (`1 ≤ k`) of manifolds, possibly with boundary or corners, and `h` is smooth on an
open set `U`, then `h.symm` is smooth on `h '' U`. Consequently `h` is a smooth local
diffeomorphism at every point of `U`, and so is every map agreeing with `h` on `U`
(`isLocalDiffeomorphAt_of_eqOn_diffeomorph`).

The Euclidean kernel `contDiffOn_infty_of_inverse_pair` works on sets with unique
differentials (half-space chart images included): the derivative of the inverse is the inverse of
the derivative composed with the inverse, and `contDiffOn_succ_iff_fderivWithin` bootstraps the
order. No open-set inverse function theorem is used, so boundary points are covered.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

/-- Euclidean bootstrap on sets with unique differentials: if `f` is smooth on `S`, `g` is `C¹`
on `T`, and they are mutually inverse bijections `S ↔ T`, then `g` is smooth on `T`. -/
theorem contDiffOn_infty_of_inverse_pair
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {T : Set F} (hS : UniqueDiffOn ℝ S) (hT : UniqueDiffOn ℝ T)
    {f : E → F} {g : F → E} (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ 1 g T)
    (hfS : MapsTo f S T) (hgT : MapsTo g T S)
    (hfg : ∀ y ∈ T, f (g y) = y) (hgf : ∀ x ∈ S, g (f x) = x) :
    ContDiffOn ℝ ∞ g T := by
  have hdf : ∀ x ∈ S, DifferentiableWithinAt ℝ f S x := fun x hx =>
    (hf.differentiableOn (by simp)) x hx
  have hdg : ∀ y ∈ T, DifferentiableWithinAt ℝ g T y := fun y hy =>
    (hg.differentiableOn one_ne_zero) y hy
  have h1 : ∀ y ∈ T, (fderivWithin ℝ f S (g y)).comp (fderivWithin ℝ g T y) =
      ContinuousLinearMap.id ℝ F := by
    intro y hy
    rw [← fderivWithin_comp y (hdf _ (hgT hy)) (hdg y hy) hgT (hT y hy)]
    have e1 : fderivWithin ℝ (f ∘ g) T y = fderivWithin ℝ id T y :=
      fderivWithin_congr (fun z hz => hfg z hz) (hfg y hy)
    rw [e1]
    exact fderivWithin_id (hT y hy)
  have h2 : ∀ y ∈ T, (fderivWithin ℝ g T y).comp (fderivWithin ℝ f S (g y)) =
      ContinuousLinearMap.id ℝ E := by
    intro y hy
    have hx := hgT hy
    have hcomp := fderivWithin_comp (g y) (hdg _ (hfS hx)) (hdf _ hx) hfS (hS _ hx)
    rw [hfg y hy] at hcomp
    have e2 : fderivWithin ℝ (g ∘ f) S (g y) = fderivWithin ℝ id S (g y) :=
      fderivWithin_congr (fun z hz => hgf z hz) (hgf _ hx)
    rw [← hcomp, e2]
    exact fderivWithin_id (hS _ hx)
  let L : ∀ y ∈ T, E ≃L[ℝ] F := fun y hy =>
    ContinuousLinearEquiv.equivOfInverse (fderivWithin ℝ f S (g y)) (fderivWithin ℝ g T y)
      (fun v => by simpa using congrArg (fun T => T v) (h2 y hy))
      (fun w => by simpa using congrArg (fun T => T w) (h1 y hy))
  have hL : ∀ y (hy : y ∈ T), ((L y hy : E ≃L[ℝ] F) : E →L[ℝ] F) = fderivWithin ℝ f S (g y) :=
    fun _ _ => rfl
  have hform : ∀ y ∈ T, fderivWithin ℝ g T y =
      ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y)) := by
    intro y hy
    rw [← hL y hy, ContinuousLinearMap.inverse_equiv]
    rfl
  rw [contDiffOn_infty]
  intro m
  induction m with
  | zero => exact hg.of_le (by simp)
  | succ m ih =>
    have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_fderivWithin hT]
    refine ⟨hg.differentiableOn one_ne_zero, by simp, ?_⟩
    have hDf : ContDiffOn ℝ m (fun x => fderivWithin ℝ f S x) S :=
      hf.fderivWithin hS (by exact_mod_cast le_top)
    have hcomp : ContDiffOn ℝ m (fun y => fderivWithin ℝ f S (g y)) T := hDf.comp ih hgT
    have hinv : ContDiffOn ℝ m
        (fun y => ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y))) T := by
      intro y hy
      have hat : ContDiffAt ℝ m ContinuousLinearMap.inverse
          (fderivWithin ℝ f S (g y)) := by
        rw [← hL y hy]
        exact contDiffAt_map_inverse (L y hy)
      exact hat.comp_contDiffWithinAt y (hcomp y hy)
    exact hinv.congr fun y hy => hform y hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

omit [CompleteSpace E] [IsManifold I ∞ M] in
private theorem uniqueDiffOn_extChartAt_image {x : M} {W : Set M} (hW : IsOpen W)
    (hWs : W ⊆ (extChartAt I x).source) : UniqueDiffOn ℝ (extChartAt I x '' W) := by
  rw [(extChartAt I x).image_eq_target_inter_inv_preimage hWs]
  intro z hz
  refine (uniqueDiffOn_extChartAt_target x z hz.1).inter' (mem_nhdsWithin_of_mem_nhds ?_)
  have hzs : (extChartAt I x).symm z ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target hz.1
  have h := extChartAt_preimage_mem_nhds' (I := I) hzs (hW.mem_nhds hz.2)
  rwa [(extChartAt I x).right_inv hz.1] at h

/-- **Smooth inverse where smooth.** A `C^k` diffeomorphism (`1 ≤ k`) that is smooth on an open
set `U` has a smooth inverse on `h '' U`. Boundary and corner points are allowed. -/
theorem contMDiffOn_diffeomorph_symm_image {k : ℕ∞ω} (hk : 1 ≤ k)
    (h : M ≃ₘ^k⟮I, J⟯ N) {U : Set M} (hU : IsOpen U) (hh : ContMDiffOn I J ∞ h U) :
    ContMDiffOn J I ∞ h.symm (h '' U) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  rintro _ ⟨x, hxU, rfl⟩
  set W : Set M := U ∩ (chartAt H x).source ∩ h ⁻¹' (chartAt H' (h x)).source with hWdef
  have hWo : IsOpen W :=
    (hU.inter (chartAt H x).open_source).inter
      ((chartAt H' (h x)).open_source.preimage h.continuous)
  have hxW : x ∈ W := ⟨⟨hxU, mem_chart_source H x⟩, mem_chart_source H' (h x)⟩
  have hhW : IsOpen (h '' W) := h.toHomeomorph.isOpenMap W hWo
  have hWs : W ⊆ (chartAt H x).source := fun z hz => hz.1.2
  have hWt : MapsTo h W (chartAt H' (h x)).source := fun z hz => hz.2
  have hhWs : h '' W ⊆ (chartAt H' (h x)).source := by
    rintro _ ⟨z, hz, rfl⟩; exact hz.2
  have hhWt : MapsTo h.symm (h '' W) (chartAt H x).source := by
    rintro _ ⟨z, hz, rfl⟩; rw [h.symm_apply_apply]; exact hz.1.2
  have hFsm := (contMDiffOn_iff_of_subset_source hWs hWt).mp (hh.mono fun z hz => hz.1.1)
  have hGk : ContMDiffOn J I 1 h.symm (h '' W) :=
    (h.symm.contMDiff.of_le hk).contMDiffOn
  have hG1 := (contMDiffOn_iff_of_subset_source hhWs hhWt).mp hGk
  have hsrcW : W ⊆ (extChartAt I x).source := by rw [extChartAt_source]; exact hWs
  have hsrchW : h '' W ⊆ (extChartAt J (h x)).source := by rw [extChartAt_source]; exact hhWs
  have hS : UniqueDiffOn ℝ (extChartAt I x '' W) := uniqueDiffOn_extChartAt_image hWo hsrcW
  have hT : UniqueDiffOn ℝ (extChartAt J (h x) '' (h '' W)) :=
    uniqueDiffOn_extChartAt_image hhW hsrchW
  have hmapF : MapsTo (extChartAt J (h x) ∘ h ∘ (extChartAt I x).symm)
      (extChartAt I x '' W) (extChartAt J (h x) '' (h '' W)) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨h z, ⟨z, hz, rfl⟩, ?_⟩
    simp only [comp_apply, (extChartAt I x).left_inv (hsrcW hz)]
  have hmapG : MapsTo (extChartAt I x ∘ h.symm ∘ (extChartAt J (h x)).symm)
      (extChartAt J (h x) '' (h '' W)) (extChartAt I x '' W) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    simp only [comp_apply, (extChartAt J (h x)).left_inv (hsrchW ⟨z, hz, rfl⟩),
      h.symm_apply_apply]
  have hFG : ∀ y ∈ extChartAt J (h x) '' (h '' W),
      (extChartAt J (h x) ∘ h ∘ (extChartAt I x).symm)
        ((extChartAt I x ∘ h.symm ∘ (extChartAt J (h x)).symm) y) = y := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    simp only [comp_apply, (extChartAt J (h x)).left_inv (hsrchW ⟨z, hz, rfl⟩),
      h.symm_apply_apply, (extChartAt I x).left_inv (hsrcW hz)]
  have hGF : ∀ y ∈ extChartAt I x '' W,
      (extChartAt I x ∘ h.symm ∘ (extChartAt J (h x)).symm)
        ((extChartAt J (h x) ∘ h ∘ (extChartAt I x).symm) y) = y := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [comp_apply, (extChartAt I x).left_inv (hsrcW hz),
      (extChartAt J (h x)).left_inv (hsrchW ⟨z, hz, rfl⟩), h.symm_apply_apply]
  have hGsm := contDiffOn_infty_of_inverse_pair hS hT hFsm.2 hG1.2 hmapF hmapG hFG hGF
  have hon : ContMDiffOn J I ∞ h.symm (h '' W) :=
    (contMDiffOn_iff_of_subset_source hhWs hhWt).mpr ⟨hG1.1, hGsm⟩
  exact (hon.contMDiffAt (hhW.mem_nhds ⟨x, hxW, rfl⟩)).contMDiffWithinAt

/-- A `C^k` diffeomorphism (`1 ≤ k`) that is smooth on an open set `U` is a smooth local
diffeomorphism at every point of `U`; so is every map that agrees with it on `U`. -/
theorem isLocalDiffeomorphAt_of_eqOn_diffeomorph {k : ℕ∞ω} (hk : 1 ≤ k)
    (h : M ≃ₘ^k⟮I, J⟯ N) {U : Set M} (hU : IsOpen U) (hh : ContMDiffOn I J ∞ h U)
    {f : M → N} (hf : EqOn f h U) {x : M} (hx : x ∈ U) : IsLocalDiffeomorphAt I J ∞ f x :=
  ⟨{ toPartialEquiv := h.toEquiv.toPartialEquivOfImageEq U (h '' U) rfl
     open_source := hU
     open_target := h.toHomeomorph.isOpenMap U hU
     contMDiffOn_toFun := hh
     contMDiffOn_invFun := contMDiffOn_diffeomorph_symm_image hk h hU hh }, hx,
    fun _ hy => hf hy⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
