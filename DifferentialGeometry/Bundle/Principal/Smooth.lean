import DifferentialGeometry.Bundle.Principal.Defs
import DifferentialGeometry.Bundle.TotalSpace
import Mathlib.Geometry.Manifold.Algebra.SMul
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

namespace Bundle

variable {k G B : Type*} [NontriviallyNormedField k] [Group G]
  [TopologicalSpace G] [TopologicalSpace B]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners k E H) [ChartedSpace H B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace k EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners k EG HG) [ChartedSpace HG G]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners k EP HP)
  [ChartedSpace HP (TotalSpace G P)]

theorem contMDiffSMul_of_principal_atlas {n : ℕ∞ω} [ContMDiffMul IG n G]
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) n e e.source ∧
      ContMDiffOn (I.prod IG) IP n e.toOpenPartialHomeomorph.symm e.target) :
    ContMDiffSMul IG IP n G (TotalSpace G P) := by
  constructor
  intro z
  let e := e₀ z.2.proj
  let := hA e (he₀ z.2.proj)
  have hp : z.2 ∈ e.source := e.mem_source.mpr (hx₀ z.2.proj)
  have he : ContMDiffAt IP (I.prod IG) n e z.2 :=
    ((hP e (he₀ z.2.proj)).1).contMDiffAt (e.open_source.mem_nhds hp)
  have hcoord := he.comp z (contMDiffAt_snd (I := IG) (J := IP))
  have hmodel := hcoord.fst.prodMk ((contMDiffAt_fst (I := IG) (J := IP)).mul hcoord.snd)
  have htarget : ((e z.2).1, z.1 * (e z.2).2) ∈ e.target := by
    rw [e.coe_fst' (hx₀ z.2.proj)]
    exact e.mem_target.mpr (hx₀ z.2.proj)
  have hinv := ((hP e (he₀ z.2.proj)).2).contMDiffAt (e.open_target.mem_nhds htarget)
  apply (hinv.comp z hmodel).congr_of_eventuallyEq
  have hneigh : {y : G × TotalSpace G P | y.2 ∈ e.source} ∈ nhds z :=
    continuous_snd.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hp)
  filter_upwards [hneigh] with y hy
  have hybase : y.2.proj ∈ e.baseSet := e.mem_source.mp hy
  have hys : y.1 • y.2 ∈ e.source := e.mem_source.mpr (by exact hybase)
  have heq : e (y.1 • y.2) = ((e y.2).1, y.1 * (e y.2).2) := by
    apply Prod.ext
    · exact (e.coe_fst' (e.mem_source.mp hys)).trans (e.coe_fst' hybase).symm
    · exact e.apply_smul (e.mem_source.mp hy) y.1 y.2.snd
  exact (e.toOpenPartialHomeomorph.left_inv hys).symm.trans
    (congrArg e.toOpenPartialHomeomorph.symm heq)

end Bundle
