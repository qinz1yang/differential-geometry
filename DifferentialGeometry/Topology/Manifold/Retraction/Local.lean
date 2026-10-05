import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMap









noncomputable section

open Set Filter Function Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem exists_manifold_local_leftInverse {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (p : M)
    (hi : Injective (mfderiv I 𝓘(ℝ, F) e p)) :
    ∃ (r : F → M) (U : Set F) (V : Set M),
      IsOpen U ∧ e p ∈ U ∧ ContMDiffOn 𝓘(ℝ, F) I ∞ r U ∧
      IsOpen V ∧ p ∈ V ∧ (∀ q ∈ V, r (e q) = q) := by
  let c := extChartAt I p
  let f : E → F := e ∘ c.symm
  have hc : ContDiffOn ℝ ∞ f c.target :=
    (he.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := I) p)).contDiffOn
  have hsrc : p ∈ c.source := by rw [extChartAt_source]; exact mem_chart_source H p
  have hcp : c p ∈ c.target := c.map_source hsrc
  have hce : c p = I ((chartAt H p) p) := by
    simp only [c, extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply]
  have hfe : f (c p) = e p := by
    dsimp only [f, Function.comp_apply]
    rw [c.left_inv hsrc]
  have hd : fderiv ℝ f (c p) = mfderiv I 𝓘(ℝ, F) e p := by
    rw [(he.mdifferentiable (by simp) p).mfderiv]
    simp only [writtenInExtChartAt, mfld_simps, f, c, fderivWithin_univ,
      ModelWithCorners.range_eq_univ]
    rfl
  obtain ⟨r₀, U₀, V₀, hU₀, hpU₀, hV₀, hpV₀, hVs, hr₀, hleft, hbase⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_local_leftInverse
      (isOpen_extChartAt_target (I := I) p) hc hcp (hd ▸ hi)
  let U : Set F := U₀ ∩ r₀ ⁻¹' c.target
  let V : Set M := (chartAt H p).source ∩ (chartAt H p) ⁻¹' (I ⁻¹' V₀)
  let r : F → M := c.symm ∘ r₀
  have hpU : e p ∈ U := by
    rw [← hfe]
    refine ⟨hpU₀, ?_⟩
    change r₀ (f (c p)) ∈ c.target
    rw [hbase]
    exact hcp
  have hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U :=
    (contMDiffOn_extChartAt_symm (I := I) p).comp
      (hr₀.contMDiffOn.mono inter_subset_left) (fun _ hy => hy.2)
  refine ⟨r, U, V, ?_, hpU, hr, ?_, ⟨mem_chart_source H p, ?_⟩, ?_⟩
  · exact hr₀.continuousOn.isOpen_inter_preimage hU₀ (isOpen_extChartAt_target (I := I) p)
  · exact (chartAt H p).isOpen_inter_preimage (I.continuous_toFun.isOpen_preimage V₀ hV₀)
  · change I ((chartAt H p) p) ∈ V₀
    rw [← hce]
    exact hpV₀
  · intro q hq
    simp only [V, Set.mem_inter_iff, Set.mem_preimage] at hq
    have hqs : q ∈ c.source := by rw [extChartAt_source]; exact hq.1
    have hqc : c q = I ((chartAt H p) q) := by
      simp only [c, extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply]
    have hqf : f (c q) = e q := by
      dsimp only [f, Function.comp_apply]
      rw [c.left_inv hqs]
    have hmem : c q ∈ V₀ := by
      rw [hqc]
      exact hq.2
    change c.symm (r₀ (e q)) = q
    rw [← hqf, hleft (c q) hmem, c.left_inv hqs]



theorem exists_local_retraction_of_embedding {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (p : M) (hi : Injective (mfderiv I 𝓘(ℝ, F) e p)) :
    ∃ (r : F → M) (U : Set F), IsOpen U ∧ e p ∈ U ∧
      ContMDiffOn 𝓘(ℝ, F) I ∞ r U ∧ ∀ q, e q ∈ U → r (e q) = q := by
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
