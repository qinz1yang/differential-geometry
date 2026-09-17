import DifferentialGeometry.Topology.Manifold.ImmersionRange
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Mathlib.Geometry.Manifold.SmoothEmbedding

open scoped ContDiff Manifold

namespace Manifold

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F V : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {H G P M N Q : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace P]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace Q] [ChartedSpace P Q]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {K : ModelWithCorners 𝕜 V P} [I.Boundaryless] [J.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {g : N → Q}

theorem IsImmersion.of_comp (h : IsImmersion I K n (g ∘ f)) (hn : n ≠ 0)
    (hf : ContMDiff I J n f) (hg : ContMDiff J K n g) : IsImmersion I J n f := by
  apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv hn hf
  intro x
  have hinj := (h.isImmersionAt x).injective_mfderiv hn
  rw [mfderiv_comp x (hg.mdifferentiableAt hn) (hf.mdifferentiableAt hn)] at hinj
  exact Function.Injective.of_comp hinj

theorem IsSmoothEmbedding.of_comp (h : IsSmoothEmbedding I K n (g ∘ f)) (hn : n ≠ 0)
    (hf : ContMDiff I J n f) (hg : ContMDiff J K n g) : IsSmoothEmbedding I J n f :=
  ⟨h.isImmersion.of_comp hn hf hg,
    _root_.Topology.IsEmbedding.of_comp hf.continuous hg.continuous h.isEmbedding⟩

theorem IsSmoothEmbedding.fst_of_snd_eq_const
    {f : M → F × V} {a : V} (h : IsSmoothEmbedding I 𝓘(𝕜, F × V) n f)
    (hn : n ≠ 0) (hsnd : ∀ x, (f x).2 = a) :
    IsSmoothEmbedding I 𝓘(𝕜, F) n (fun x => (f x).1) := by
  let p : M → F := fun x => (f x).1
  let j : F → F × V := fun y => (y, a)
  have hp : ContMDiff I 𝓘(𝕜, F) n p := contDiff_fst.contMDiff.comp h.contMDiff
  have hj : ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, F × V) n j :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  have heq : j ∘ p = f := by
    funext x
    exact Prod.ext rfl (hsnd x).symm
  have hh : IsSmoothEmbedding I 𝓘(𝕜, F × V) n (j ∘ p) := heq ▸ h
  exact hh.of_comp hn hp hj


theorem IsImmersion.isOpen_preimage_range_of_range_subset
    {e : M → Q} (he : IsImmersion I K n e) (hg : IsSmoothEmbedding J K n g)
    (hn : n ≠ 0) (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 F)
    (hsub : Set.range e ⊆ Set.range g) : IsOpen (g ⁻¹' Set.range e) := by
  let q : M → N := fun x => hg.isEmbedding.toHomeomorph.symm
    ⟨e x, hsub (Set.mem_range_self x)⟩
  have heq (x : M) : g (q x) = e x :=
    congrArg Subtype.val (hg.isEmbedding.toHomeomorph.apply_symm_apply
      ⟨e x, hsub (Set.mem_range_self x)⟩)
  have hqcont : Continuous q := hg.isEmbedding.toHomeomorph.symm.continuous.comp
    (he.contMDiff.continuous.subtype_mk _)
  have hq : ContMDiff I J n q :=
    (ContMDiff.iff_comp_isImmersion hg.isImmersion).mpr
      ⟨hqcont, he.contMDiff.congr heq⟩
  have hcomp : IsImmersion I K n (g ∘ q) := by
    simpa only [Function.comp_def, heq] using he
  have hqi := hcomp.of_comp hn hq hg.contMDiff
  have hqo : IsOpen (Set.range q) :=
    _root_.Manifold.isOpen_range_of_isImmersion hdim hqi
  have hr : g ⁻¹' Set.range e = Set.range q := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, hg.isEmbedding.injective ((heq x).trans hx)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, (heq x).symm⟩
  rwa [hr]

end Manifold
