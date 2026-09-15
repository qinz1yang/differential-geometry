import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.Quotient
import Mathlib.Algebra.Ring.Periodic

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace AddCircle

theorem contMDiff_periodic_lift {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hper : Function.Periodic β 1) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ hper.lift := by
  apply AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
    QuotientAddGroup.mk_surjective
  · change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ β
    exact hβ.contMDiff

end AddCircle

namespace AddCircle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H K]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem contMDiffOn_of_comp_coe {U : Set K} {f : K × AddCircle (1 : ℝ) → N}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞
      (fun p : K × ℝ => f (p.1, (p.2 : AddCircle (1 : ℝ)))) (U ×ˢ univ)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞ f (U ×ˢ univ) := by
  rintro ⟨k, z⟩ hz
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  let hloc := isLocalDiffeomorph_coe x
  let ψ : K × AddCircle (1 : ℝ) → K × ℝ := fun p => (p.1, hloc.localInverse p.2)
  let g : K × ℝ → N := fun p => f (p.1, (p.2 : AddCircle (1 : ℝ)))
  have hleft : hloc.localInverse (x : AddCircle (1 : ℝ)) = x :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hmap : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ ψ
      (k, (x : AddCircle (1 : ℝ))) :=
    contMDiffAt_fst.prodMk (hloc.localInverse_contMDiffAt.comp
      (k, (x : AddCircle (1 : ℝ))) contMDiffAt_snd)
  have hg : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) J ∞ g (U ×ˢ univ)
      (ψ (k, (x : AddCircle (1 : ℝ)))) := hf _ ⟨hz.1, mem_univ _⟩
  have hcomp : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) J ∞ (g ∘ ψ)
      (U ×ˢ univ) (k, (x : AddCircle (1 : ℝ))) :=
    hg.comp (k, (x : AddCircle (1 : ℝ))) hmap.contMDiffWithinAt
      (show MapsTo ψ (U ×ˢ univ) (U ×ˢ univ) from fun p hp => ⟨hp.1, mem_univ _⟩)
  apply hcomp.congr_of_eventuallyEq
  · apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source)] with p hp
    change f p = f (p.1, (hloc.localInverse p.2 : AddCircle (1 : ℝ)))
    rw [hloc.localInverse_right_inv hp]
  · change f (k, (x : AddCircle (1 : ℝ))) =
      f (k, (hloc.localInverse (x : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ)))
    rw [hleft]

end AddCircle
