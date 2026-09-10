import DifferentialGeometry.Topology.VectorField.DiffeomorphPatch
import DifferentialGeometry.Topology.VectorField.PullbackComposition

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField

theorem exists_patchThroughDiffeomorph_model_germ
    {E F G H H' H'' M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    [TopologicalSpace P] [ChartedSpace H'' P]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} {K : ModelWithCorners ℝ G H''}
    (U : TopologicalSpace.Opens M) (e : Diffeomorph J I N U ∞)
    (V : ∀ x : M, TangentSpace I x) (L : ∀ q : N, TangentSpace J q)
    (C : ∀ p : P, TangentSpace K p) (f : PartialDiffeomorph J K N P ∞)
    {q : N} (hq : q ∈ f.source)
    (hL : L =ᶠ[𝓝 q] _root_.VectorField.mpullback J K f C) :
    ∃ Φ : PartialDiffeomorph K I P M ∞, f q ∈ Φ.source ∧ Φ (f q) = (e q).val ∧
      patchThroughDiffeomorph U e V L =ᶠ[𝓝 (e q).val] _root_.VectorField.mpullback I K Φ.symm C := by
  let u := Poincare.Manifold.openSubtypePartialDiffeomorph I U ⟨e q⟩
  let g := u.symm.trans e.symm.toPartialDiffeomorph
  have hxu : (e q).val ∈ u.symm.source := by
    change (e q).val ∈ u.target
    rw [Poincare.Manifold.openSubtypePartialDiffeomorph_target]
    exact (e q).property
  have hu : u.symm (e q).val = e q :=
    Poincare.Manifold.openSubtypePartialDiffeomorph_symm_apply I U ⟨e q⟩ (e q).property
  have hxg : (e q).val ∈ g.source := ⟨hxu, trivial⟩
  have hg : g (e q).val = q := by
    change e.symm (u.symm (e q).val) = q
    rw [hu, e.symm_apply_apply]
  let ψ := g.trans f
  have hxψ : (e q).val ∈ ψ.source := by
    refine ⟨hxg, ?_⟩
    change g (e q).val ∈ f.source
    rw [hg]
    exact hq
  have hψ : ψ (e q).val = f q := congrArg f hg
  refine ⟨ψ.symm, hψ ▸ ψ.map_source hxψ, ?_, ?_⟩
  · rw [← hψ]
    exact ψ.left_inv hxψ
  · have hLt : (fun p => (⟨p, L p⟩ : TangentBundle J N)) =ᶠ[𝓝 (g (e q).val)]
        (fun p => (⟨p, _root_.VectorField.mpullback J K f C p⟩ : TangentBundle J N)) := by
      rw [hg]
      filter_upwards [hL] with p hp
      exact congrArg (fun v => (⟨p, v⟩ : TangentBundle J N)) hp
    have hp := mpullback_partialDiffeomorph_congr_germ g hxg hLt
    have hpatch := patchOnOpen_eventuallyEq_mpullback U V
      (_root_.VectorField.mpullback I J e.symm L) (e q).property
    filter_upwards [hp, hpatch, ψ.open_source.mem_nhds hxψ] with x hx hpch hxs
    have h1 := TotalSpace.mk_injective x hpch
    have h2 := TotalSpace.mk_injective x hx
    change patchThroughDiffeomorph U e V L x = _
    change patchThroughDiffeomorph U e V L x =
      _root_.VectorField.mpullback I I u.symm (_root_.VectorField.mpullback I J e.symm L) x at h1
    exact h1.trans ((mpullback_trans_partialDiffeomorph u.symm e.symm.toPartialDiffeomorph
      (by simp) L hxs.1.1 hxs.1.2).symm.trans
        (h2.trans (mpullback_trans_partialDiffeomorph g f (by simp) C hxs.1 hxs.2).symm))

end Poincare.VectorField
