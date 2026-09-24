import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import DifferentialGeometry.Topology.Manifold.OpenTarget

noncomputable section
open Set Manifold TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F H G X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace G Y]

theorem exists_contMDiff_interval_lift_of_injective_localDiffeomorph
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (γ : ℝ → Y) (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ) {a b : ℝ} (hab : a < b)
    (hstay : MapsTo γ (Icc a b) (range f)) :
    ∃ β : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) I 1 β ∧ EqOn (f ∘ β) γ (Icc a b) := by
  let U := hf.image
  let e := diffeomorphOntoImage f hf hinj
  obtain ⟨ρ, lo, hi, hlo, hhi, hρ, hρid, _, hρrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset
      (U.isOpen.preimage hγ.continuous) hab hstay
  let η : ℝ → U := fun t => ⟨γ (ρ t), hρrange t⟩
  have hη : ContMDiff 𝓘(ℝ, ℝ) J 1 η := by
    apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff (n := 1) U η).mp
    exact hγ.comp (hρ.contMDiff.of_le (by norm_num))
  refine ⟨e.symm ∘ η, (e.symm.contMDiff.of_le (by norm_num)).comp hη, ?_⟩
  intro t ht
  change f (e.symm (η t)) = γ t
  rw [show f (e.symm (η t)) = (η t).val from diffeomorphOntoImage_symm_apply f hf hinj (η t)]
  change γ (ρ t) = γ t
  rw [hρid ⟨hlo.le.trans ht.1, ht.2.trans hhi.le⟩]
  rfl

end DifferentialGeometry.Topology.Manifold
