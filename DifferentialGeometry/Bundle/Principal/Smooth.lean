import DifferentialGeometry.Bundle.Principal.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace Bundle.Trivialization

section LocalSection

variable {k G B : Type*} [NontriviallyNormedField k] [One G]
  [TopologicalSpace G] [TopologicalSpace B]
  {P : B → Type*} [∀ x, Nonempty (P x)]
  [TopologicalSpace (TotalSpace G P)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners k E H} [ChartedSpace H B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace k EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners k EG HG} [ChartedSpace HG G]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners k EP HP}
  [ChartedSpace HP (TotalSpace G P)] {n : ℕ∞ω}

theorem contMDiffOn_principalSection
    (e : Trivialization G (π G P))
    (he : ContMDiffOn (I.prod IG) IP n e.toOpenPartialHomeomorph.symm e.target) :
    ContMDiffOn I IP n (fun x => (⟨x, e.principalSection x⟩ : TotalSpace G P)) e.baseSet := by
  apply (he.comp (contMDiffOn_id.prodMk (contMDiffOn_const (c := (1 : G))))
    (fun _ hx => e.mem_target.mpr hx)).congr
  intro x hx
  exact e.mk_symm hx 1

end LocalSection

variable {k G B : Type*} [NontriviallyNormedField k] [Group G]
  [TopologicalSpace G] [TopologicalSpace B]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners k E H} [ChartedSpace H B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace k EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners k EG HG} [ChartedSpace HG G]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners k EP HP}
  [ChartedSpace HP (TotalSpace G P)] {n : ℕ∞ω}

theorem contMDiffOn_principalSection_sdiv
    (e e' : Trivialization G (π G P)) [MemTrivializationAtlas e]
    (he : ContMDiffOn IP (I.prod IG) n e e.source)
    (he' : ContMDiffOn (I.prod IG) IP n e'.toOpenPartialHomeomorph.symm e'.target) :
    ContMDiffOn I IG n (fun x => e'.principalSection x /ₛ e.principalSection x)
      (e.baseSet ∩ e'.baseSet) := by
  have h := he.comp
    ((e'.contMDiffOn_principalSection he').mono inter_subset_right)
    (fun _ hx => e.mem_source.mpr hx.1)
  apply ((contMDiff_snd : ContMDiff (I.prod IG) IG n (fun z : B × G => z.2)).comp_contMDiffOn h).congr
  intro x hx
  exact e.sdiv_principalSection hx.1 _

end Bundle.Trivialization

