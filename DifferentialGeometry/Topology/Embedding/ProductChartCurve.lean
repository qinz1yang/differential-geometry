import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Order.ProjIcc

noncomputable section
open Set Topology

namespace DifferentialGeometry.Topology.Embedding

theorem exists_curve_of_product_chart_segment
    {N M W : Type*} [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace W]
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (e : O ≃ₜ V) (ι : W → M) (hemb : IsEmbedding ι)
    (p : N) (t σ r : ℝ) (hr : 0 < r)
    (hsegment : ∀ s ∈ Icc 0 r, (p, t + σ * s) ∈ O)
    (himage : ∀ s (hs : s ∈ Icc 0 r), (e ⟨(p, t + σ * s), hsegment s hs⟩ : M) ∈ range ι) :
    ∃ γ : ℝ → W, Continuous γ ∧
      ∀ s (hs : s ∈ Icc 0 r), ι (γ s) = (e ⟨(p, t + σ * s), hsegment s hs⟩ : M) := by
  let clamp : ℝ → Icc 0 r := projIcc 0 r hr.le
  let q : ℝ → O := fun s ↦ ⟨(p, t + σ * (clamp s : ℝ)), hsegment _ (clamp s).property⟩
  have hclamp : Continuous (fun s ↦ (clamp s : ℝ)) :=
    continuous_subtype_val.comp continuous_projIcc
  have hq : Continuous q :=
    (continuous_const.prodMk (continuous_const.add (continuous_const.mul hclamp))).subtype_mk _
  have hpre : ∀ s, ∃ w : W, ι w = (e (q s) : M) :=
    fun s ↦ himage _ (clamp s).property
  choose γ hγeq using hpre
  have hγ : Continuous γ := by
    apply hemb.isInducing.continuous_iff.mpr
    have heq : ι ∘ γ = fun s ↦ (e (q s) : M) := funext hγeq
    rw [heq]
    exact continuous_subtype_val.comp (e.continuous.comp hq)
  refine ⟨γ, hγ, ?_⟩
  intro s hs
  rw [hγeq]
  congr 2
  apply Subtype.ext
  change (p, t + σ * (projIcc 0 r hr.le s : ℝ)) = (p, t + σ * s)
  rw [projIcc_of_mem hr.le hs]

end DifferentialGeometry.Topology.Embedding
