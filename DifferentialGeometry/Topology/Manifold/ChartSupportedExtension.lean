/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace OpenPartialHomeomorph

def extendById {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (f : Y → Y) (x : X) : X := by
  classical
  exact if x ∈ e.source then e.symm (f (e x)) else x

theorem extendById_eq_of_notMem_image {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (f : Y → Y) {K : Set Y}
    (hf : ∀ z, z ∉ K → f z = z) {x : X} (hx : x ∉ e.symm '' K) :
    e.extendById f x = x := by
  by_cases hxs : x ∈ e.source
  · rw [show e.extendById f x = e.symm (f (e x)) from ite_eq_left hxs]
    have hek : e x ∉ K := fun h ↦ hx ⟨e x, h, e.left_inv hxs⟩
    rw [hf _ hek, e.left_inv hxs]
  · exact ite_eq_right hxs

theorem extendById_mem_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (f : Y → Y)
    (hmap : MapsTo f e.target e.target) {A B : Set X} {C D : Set Y}
    (hA : e.IsImage A C) (hB : e.IsImage B D)
    (houtside : ∀ x ∉ e.source, x ∈ A ↔ x ∈ B)
    (hf : ∀ y ∈ e.target, f y ∈ D ↔ y ∈ C) (x : X) :
    e.extendById f x ∈ B ↔ x ∈ A := by
  by_cases hx : x ∈ e.source
  · rw [show e.extendById f x = e.symm (f (e x)) from ite_eq_left hx]
    exact (hB.symm (hmap (e.map_source hx))).trans ((hf _ (e.map_source hx)).trans (hA hx))
  · rw [show e.extendById f x = x from ite_eq_right hx]
    exact (houtside x hx).symm

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.Manifold

section

variable {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]

def extendChartById (e : OpenPartialHomeomorph M E) (f : E → E) (x : M) : M := by
  classical
  exact if x ∈ e.source then e.symm (f (e x)) else x

private theorem extendChartById_of_mem (e : OpenPartialHomeomorph M E) (f : E → E)
    {x : M} (hx : x ∈ e.source) : extendChartById e f x = e.symm (f (e x)) :=
  ite_eq_left hx

private theorem extendChartById_of_notMem (e : OpenPartialHomeomorph M E) (f : E → E)
    {x : M} (hx : x ∉ e.source) : extendChartById e f x = x := ite_eq_right hx

theorem extendChartById_eq_of_notMem_image
    (e : OpenPartialHomeomorph M E) (f : E → E) {K : Set E}
    (hf : ∀ z, z ∉ K → f z = z) {x : M} (hx : x ∉ e.symm '' K) :
    extendChartById e f x = x := by
  by_cases hxs : x ∈ e.source
  · rw [extendChartById_of_mem e f hxs]
    have hek : e x ∉ K := fun h ↦ hx ⟨e x, h, e.left_inv hxs⟩
    rw [hf _ hek, e.left_inv hxs]
  · exact extendChartById_of_notMem e f hxs

theorem extendChartById_mem_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (f : Y → Y)
    (hmap : MapsTo f e.target e.target) {A B : Set X} {C D : Set Y}
    (hA : e.IsImage A C) (hB : e.IsImage B D)
    (houtside : ∀ x ∉ e.source, x ∈ A ↔ x ∈ B)
    (hf : ∀ y ∈ e.target, f y ∈ D ↔ y ∈ C) (x : X) :
    extendChartById e f x ∈ B ↔ x ∈ A :=
  e.extendById_mem_iff f hmap hA hB houtside hf x

end

variable {E F P H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ F H}

theorem contMDiff_extendChartById [T2Space M]
    (e : OpenPartialHomeomorph M E) (htarget : e.target = univ)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    {f : P × E → E} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (hfix : ∀ p z, z ∉ K → f (p, z) = z) :
    ContMDiff (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M ↦ extendChartById e (fun z ↦ f (q.1, z)) q.2) := by
  have hi : ContMDiff 𝓘(ℝ, E) I ∞ e.symm := contMDiffOn_univ.mp (htarget ▸ hei)
  have hKi : IsCompact (e.symm '' K) := hK.image hi.continuous
  intro q
  by_cases hq : q.2 ∈ e.source
  · have hc : ContMDiffAt (𝓘(ℝ, P).prod I) 𝓘(ℝ, E) ∞
        (fun r : P × M ↦ e r.2) q :=
      (he.contMDiffAt (e.open_source.mem_nhds hq)).comp q contMDiffAt_snd
    have hs := (hi.contMDiffAt.comp q
      (hf.contMDiff.contMDiffAt.comp q (contMDiffAt_fst.prodMk_space hc)))
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hq)] with r hr
    exact extendChartById_of_mem e _ hr
  · have hqK : q.2 ∉ e.symm '' K := by
      rintro ⟨z, _, hz⟩
      exact hq (hz ▸ e.map_target (htarget ▸ mem_univ z))
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (hKi.isClosed.isOpen_compl.mem_nhds hqK)] with r hr
    exact extendChartById_eq_of_notMem_image e _ (hfix r.1) hr

omit [NormedSpace ℝ E] in
theorem leftInverse_extendChartById
    (e : OpenPartialHomeomorph M E) (htarget : e.target = univ)
    {f g : E → E} (hgf : Function.LeftInverse g f) :
    Function.LeftInverse (extendChartById e g) (extendChartById e f) := by
  intro x
  by_cases hx : x ∈ e.source
  · rw [extendChartById_of_mem e f hx,
      extendChartById_of_mem e g (e.map_target (htarget ▸ mem_univ (f (e x)))),
      e.right_inv (htarget ▸ mem_univ (f (e x))), hgf, e.left_inv hx]
  · rw [extendChartById_of_notMem e f hx, extendChartById_of_notMem e g hx]

theorem exists_diffeomorph_extension_of_chart_family [T2Space M]
    (e : OpenPartialHomeomorph M E) (htarget : e.target = univ)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    (D : P → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hD : ContDiff ℝ ∞ (fun q : P × E ↦ D q.1 q.2))
    (hDi : ContDiff ℝ ∞ (fun q : P × E ↦ (D q.1).symm q.2))
    {K : Set E} (hK : IsCompact K)
    (hfix : ∀ p z, z ∉ K → D p z = z ∧ (D p).symm z = z) :
    ∃ J : P → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun q : P × M ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun q : P × M ↦ (J q.1).symm q.2) ∧
      (∀ p x, J p x = extendChartById e (D p) x ∧
        (J p).symm x = extendChartById e (D p).symm x) ∧
      IsCompact (e.symm '' K) ∧ e.symm '' K ⊆ e.source ∧
      ∀ p x, x ∉ e.symm '' K → J p x = x ∧ (J p).symm x = x := by
  have hF := contMDiff_extendChartById e htarget he hei hD hK
    (fun p z hz ↦ (hfix p z hz).1)
  have hG := contMDiff_extendChartById e htarget he hei hDi hK
    (fun p z hz ↦ (hfix p z hz).2)
  let J (p : P) : Diffeomorph I I M M ∞ :=
    { toEquiv :=
        { toFun := extendChartById e (D p)
          invFun := extendChartById e (D p).symm
          left_inv := leftInverse_extendChartById e htarget (D p).symm_apply_apply
          right_inv := leftInverse_extendChartById e htarget (D p).apply_symm_apply }
      contMDiff_toFun := hF.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hG.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨J, hF, hG, fun _ _ ↦ ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact hK.image (contMDiffOn_univ.mp (htarget ▸ hei)).continuous
  · rintro x ⟨z, _, rfl⟩
    exact e.map_target (htarget ▸ mem_univ z)
  · intro p x hx
    exact ⟨extendChartById_eq_of_notMem_image e _ (fun z hz ↦ (hfix p z hz).1) hx,
      extendChartById_eq_of_notMem_image e _ (fun z hz ↦ (hfix p z hz).2) hx⟩

end DifferentialGeometry.Topology.Manifold
