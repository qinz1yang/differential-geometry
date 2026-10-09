/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

private theorem mapsTo_of_injective_of_fix_compl {X : Type*} {f : X → X}
    (hf : Function.Injective f) {K U : Set X} (hKU : K ⊆ U)
    (hfix : ∀ x, x ∉ K → f x = x) : MapsTo f U U := by
  intro x hx
  by_contra hfx
  have he : f (f x) = f x := hfix _ (fun h ↦ hfx (hKU h))
  exact hfx ((hf he).symm ▸ hx)

section Smooth

variable {E F EP H G HP M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace HP]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {IP : ModelWithCorners ℝ EP HP}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace P] [ChartedSpace HP P]

theorem contMDiff_extendById_of_contMDiff_of_mapsTo [T2Space M]
    (e : OpenPartialHomeomorph M N)
    (he : ContMDiffOn I J ∞ e e.source)
    (hei : ContMDiffOn J I ∞ e.symm e.target)
    {f : P × N → N} (hf : ContMDiff (IP.prod J) J ∞ f)
    (hmap : ∀ p, MapsTo (fun z ↦ f (p, z)) e.target e.target)
    {K : Set N} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ p z, z ∉ K → f (p, z) = z) :
    ContMDiff (IP.prod I) I ∞
      (fun q : P × M ↦ OpenPartialHomeomorph.extendById e (fun z ↦ f (q.1, z)) q.2) := by
  have hKi : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (hei.continuousOn.mono hKt)
  intro q
  by_cases hq : q.2 ∈ e.source
  · have hc : ContMDiffAt (IP.prod I) J ∞ (fun r : P × M ↦ e r.2) q :=
      (he.contMDiffAt (e.open_source.mem_nhds hq)).comp q contMDiffAt_snd
    have hi := hei.contMDiffAt (e.open_target.mem_nhds (hmap q.1 (e.map_source hq)))
    have hs := hi.comp q (hf.contMDiffAt.comp q (contMDiffAt_fst.prodMk hc))
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hq)] with r hr
    exact ite_eq_left hr
  · have hqK : q.2 ∉ e.symm '' K := by
      rintro ⟨z, hz, heq⟩
      exact hq (heq ▸ e.map_target (hKt hz))
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (hKi.isClosed.isOpen_compl.mem_nhds hqK)] with r hr
    exact OpenPartialHomeomorph.extendById_eq_of_notMem_image e _ (hfix r.1) hr

end Smooth

theorem leftInverse_extendById_of_mapsTo
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M N) {f g : N → N}
    (hgf : Function.LeftInverse g f) (hf : MapsTo f e.target e.target) :
    Function.LeftInverse (OpenPartialHomeomorph.extendById e g)
      (OpenPartialHomeomorph.extendById e f) := by
  intro x
  by_cases hx : x ∈ e.source
  · have hfx := hf (e.map_source hx)
    rw [show OpenPartialHomeomorph.extendById e f x = e.symm (f (e x)) from ite_eq_left hx,
      show OpenPartialHomeomorph.extendById e g (e.symm (f (e x))) =
        e.symm (g (e (e.symm (f (e x))))) from ite_eq_left (e.map_target hfx),
      e.right_inv hfx, hgf, e.left_inv hx]
  · rw [show OpenPartialHomeomorph.extendById e f x = x from ite_eq_right hx]
    exact ite_eq_right hx

end DifferentialGeometry.Topology.Manifold

namespace PartialDiffeomorph

open DifferentialGeometry.Topology.Manifold

variable {E F EP H G HP M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace HP]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {IP : ModelWithCorners ℝ EP HP}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace P] [ChartedSpace HP P]

theorem exists_diffeomorph_family_extension [T2Space M]
    (e : PartialDiffeomorph J I N M ∞)
    (D : P → Diffeomorph J J N N ∞)
    (hD : ContMDiff (IP.prod J) J ∞ (fun q : P × N ↦ D q.1 q.2))
    (hDi : ContMDiff (IP.prod J) J ∞ (fun q : P × N ↦ (D q.1).symm q.2))
    {K : Set N} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hfix : ∀ p z, z ∉ K → D p z = z) :
    ∃ F : P → Diffeomorph I I M M ∞,
      ContMDiff (IP.prod I) I ∞ (fun q : P × M ↦ F q.1 q.2) ∧
      ContMDiff (IP.prod I) I ∞ (fun q : P × M ↦ (F q.1).symm q.2) ∧
      (∀ p x, F p x = OpenPartialHomeomorph.extendById e.symm.toOpenPartialHomeomorph (D p) x ∧
        (F p).symm x =
          OpenPartialHomeomorph.extendById e.symm.toOpenPartialHomeomorph (D p).symm x) ∧
      IsCompact (e '' K) ∧ e '' K ⊆ e.target ∧
      ∀ p x, x ∉ e '' K → F p x = x ∧ (F p).symm x = x := by
  let c := e.symm.toOpenPartialHomeomorph
  have hfixi (p : P) (z : N) (hz : z ∉ K) : (D p).symm z = z := by
    simpa only [hfix p z hz] using (D p).symm_apply_apply z
  have hmap (p : P) : MapsTo (D p) c.target c.target :=
    mapsTo_of_injective_of_fix_compl (D p).injective hKs (fun z hz ↦ hfix p z hz)
  have hmapi (p : P) : MapsTo (D p).symm c.target c.target :=
    mapsTo_of_injective_of_fix_compl (D p).symm.injective hKs (fun z hz ↦ hfixi p z hz)
  have hF := contMDiff_extendById_of_contMDiff_of_mapsTo c e.contMDiffOn_invFun
    e.contMDiffOn_toFun hD hmap hK hKs (fun p z hz ↦ hfix p z hz)
  have hG := contMDiff_extendById_of_contMDiff_of_mapsTo c e.contMDiffOn_invFun
    e.contMDiffOn_toFun hDi hmapi hK hKs (fun p z hz ↦ hfixi p z hz)
  let F (p : P) : Diffeomorph I I M M ∞ :=
    { toEquiv :=
        { toFun := OpenPartialHomeomorph.extendById c (D p)
          invFun := OpenPartialHomeomorph.extendById c (D p).symm
          left_inv := leftInverse_extendById_of_mapsTo c (D p).symm_apply_apply (hmap p)
          right_inv := leftInverse_extendById_of_mapsTo c (D p).apply_symm_apply (hmapi p) }
      contMDiff_toFun := hF.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hG.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨F, hF, hG, fun _ _ ↦ ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact hK.image_of_continuousOn (e.contMDiffOn_toFun.continuousOn.mono hKs)
  · rintro x ⟨z, hz, rfl⟩
    exact e.map_source (hKs hz)
  · intro p x hx
    exact ⟨OpenPartialHomeomorph.extendById_eq_of_notMem_image c _ (fun z hz ↦ hfix p z hz) hx,
      OpenPartialHomeomorph.extendById_eq_of_notMem_image c _ (fun z hz ↦ hfixi p z hz) hx⟩

end PartialDiffeomorph
