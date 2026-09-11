import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMap









noncomputable section

open Set Filter Function Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem exists_manifold_local_leftInverse {e : M → F}
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (p : M)
    (hi : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) :
    ∃ (r : F → M) (U : Set F) (V : Set M),
      IsOpen U ∧ e p ∈ U ∧ ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U ∧
      IsOpen V ∧ p ∈ V ∧ (∀ q ∈ V, r (e q) = q) := by
  let c := chartAt E p
  let f : E → F := e ∘ c.symm
  have hc : ContDiffOn ℝ ∞ f c.target :=
    (he.comp_contMDiffOn contMDiffOn_chart_symm).contDiffOn
  have hcp : c p ∈ c.target := c.map_source (mem_chart_source E p)
  have hfe : f (c p) = e p := by
    dsimp only [f, Function.comp_apply]
    rw [c.left_inv (mem_chart_source E p)]
  have hd : fderiv ℝ f (c p) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p := by
    rw [(he.mdifferentiable (by simp) p).mfderiv]
    simp only [writtenInExtChartAt, mfld_simps, f, c, fderivWithin_univ]
  obtain ⟨r₀, U₀, V₀, hU₀, hpU₀, hV₀, hpV₀, hVs, hr₀, hleft, hbase⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_local_leftInverse c.open_target hc hcp (hd ▸ hi)
  let U : Set F := U₀ ∩ r₀ ⁻¹' c.target
  let V : Set M := c.source ∩ c ⁻¹' V₀
  let r : F → M := c.symm ∘ r₀
  have hpU : e p ∈ U := by
    rw [← hfe]
    refine ⟨hpU₀, ?_⟩
    change r₀ (f (c p)) ∈ c.target
    rw [hbase]
    exact hcp
  have hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U :=
    contMDiffOn_chart_symm.comp (hr₀.contMDiffOn.mono inter_subset_left) (fun _ hy => hy.2)
  refine ⟨r, U, V, ?_, hpU, hr, c.isOpen_inter_preimage hV₀,
    ⟨mem_chart_source E p, hpV₀⟩, ?_⟩
  · exact hr₀.continuousOn.isOpen_inter_preimage hU₀ c.open_target
  · intro q hq
    have hqf : f (c q) = e q := by
      dsimp only [f, Function.comp_apply]
      rw [c.left_inv hq.1]
    change c.symm (r₀ (e q)) = q
    rw [← hqf, hleft (c q) hq.2, c.left_inv hq.1]



theorem exists_local_retraction_of_embedding {e : M → F}
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (p : M) (hi : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) :
    ∃ (r : F → M) (U : Set F), IsOpen U ∧ e p ∈ U ∧
      ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U ∧ ∀ q, e q ∈ U → r (e q) = q := by
  obtain ⟨r, U, V, hU, hpU, hr, hV, hpV, hleft⟩ :=
    exists_manifold_local_leftInverse he p hi
  obtain ⟨W, hW, hVW⟩ := hemb.isInducing.isOpen_iff.mp hV
  refine ⟨r, U ∩ W, hU.inter hW, ⟨hpU, ?_⟩, hr.mono inter_subset_left, ?_⟩
  · rw [← hVW] at hpV
    exact hpV
  · intro q hq
    apply hleft q
    rw [← hVW]
    exact hq.2

end DifferentialGeometry.Geometry
