import DifferentialGeometry.Topology.Manifold.SmoothBilinearEigenpair
import DifferentialGeometry.Bundle.RightInverse
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom

noncomputable section
open Set Bundle
open scoped ContDiff Manifold
open DifferentialGeometry

namespace Poincare.Geometry.VectorBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem frame_section_smooth
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M))
    [MemTrivializationAtlas e] {U : Set M} (hU : U ⊆ e.baseSet)
    {v : M → E} (hv : ContMDiffOn I 𝓘(ℝ, E) ∞ v U) :
    ContMDiffOn I I.tangent ∞ (fun x ↦ (⟨x, e.symmL ℝ x (v x)⟩ : TangentBundle I M)) U := by
  rw [e.contMDiffOn_iff (fun x hx ↦ e.mem_source.mpr (hU hx))]
  refine ⟨contMDiffOn_id, hv.congr ?_⟩
  intro x hx
  rw [e.symmL_apply (hU hx), e.apply_mk_symm (hU hx)]

theorem exists_smooth_metric_normalized_eigenpair
    (g : SmoothRiemannianMetric I M)
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    {U : Set M} (hU : IsOpen U)
    (hA : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) x (A x)) U)
    {x₀ : M} (hx₀ : x₀ ∈ U)
    (hself : ∀ u v : TangentSpace I x₀, g.inner x₀ (A x₀ u) v = g.inner x₀ u (A x₀ v))
    (μ₀ : ℝ) (w₀ : TangentSpace I x₀) (hw₀ : g.inner x₀ w₀ w₀ = 1)
    (heigen : A x₀ w₀ = μ₀ • w₀)
    (hsimple : Module.End.eigenspace (A x₀).toLinearMap μ₀ = Submodule.span ℝ {w₀}) :
    ∃ V : Set M, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      ∃ (μ : M → ℝ) (w : ∀ x : M, TangentSpace I x),
        ContMDiffOn I 𝓘(ℝ) ∞ μ V ∧
        ContMDiffOn I I.tangent ∞ (fun x ↦ (⟨x, w x⟩ : TangentBundle I M)) V ∧
        μ x₀ = μ₀ ∧ w x₀ = w₀ ∧
        ∀ x ∈ V, g.inner x (w x) (w x) = 1 ∧ A x (w x) = μ x • w x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  let D := U ∩ e.baseSet
  let C : M → E →L[ℝ] E := fun x ↦
    (e.continuousLinearMapAt ℝ x).comp ((A x).comp (e.symmL ℝ x))
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ (g.inner x (e.symmL ℝ x v)).comp (e.symmL ℝ x)
      map_add' := by
        intro v w
        ext u
        simp only [map_add, ContinuousLinearMap.comp_apply, add_apply]
      map_smul' := by
        intro c v
        ext u
        simp only [map_smul, ContinuousLinearMap.comp_apply, smul_apply]
        rfl }
  have hC : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞ C D := by
    apply contMDiffOn_clm_apply_iff.mpr
    intro v
    have hv := frame_section_smooth e (U := D) inter_subset_right (contMDiffOn_const (c := v))
    have ha := ContMDiffOn.clm_bundle_apply (E₁ := TangentSpace I) (E₂ := TangentSpace I)
      (b := id) (ϕ := A) (v := fun x ↦ e.symmL ℝ x v) (hA.mono inter_subset_left) hv
    have hc := (e.contMDiffOn (IB := I) (n := ∞)).comp ha
      (fun x hx ↦ e.mem_source.mpr hx.2)
    exact (contMDiff_snd.comp_contMDiffOn hc).congr (fun x hx ↦
      e.continuousLinearMapAt_apply_of_mem ℝ hx.2 _)
  have hB : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B D := by
    apply contMDiffOn_clm_apply_iff.mpr
    intro v
    apply contMDiffOn_clm_apply_iff.mpr
    intro w
    have hv := frame_section_smooth e (U := D) inter_subset_right (contMDiffOn_const (c := v))
    have hw := frame_section_smooth e (U := D) inter_subset_right (contMDiffOn_const (c := w))
    have ht := ContMDiffOn.clm_bundle_apply₂ (E₁ := TangentSpace I) (E₂ := TangentSpace I)
      (E₃ := fun _ : M ↦ ℝ) (b := id) (ψ := g.inner)
      (v := fun x ↦ e.symmL ℝ x v) (w := fun x ↦ e.symmL ℝ x w) g.contMDiff.contMDiffOn hv hw
    intro x hx
    exact (contMDiffWithinAt_totalSpace.mp (ht x hx)).2
  let p := e.continuousLinearEquivAt ℝ x₀ hx
  have hp (v : TangentSpace I x₀) : e.symmL ℝ x₀ (p v) = v := by
    simpa only [p, Trivialization.symm_continuousLinearEquivAt_eq] using p.symm_apply_apply v
  have hCp (v : TangentSpace I x₀) : C x₀ (p v) = p (A x₀ v) := by
    change e.continuousLinearMapAt ℝ x₀ (A x₀ (e.symmL ℝ x₀ (p v))) = p (A x₀ v)
    rw [hp]
    simp only [p, Trivialization.coe_continuousLinearEquivAt_eq]
  have hCs (v : E) : e.symmL ℝ x₀ (C x₀ v) = A x₀ (e.symmL ℝ x₀ v) := by
    exact e.symmL_continuousLinearMapAt (R := ℝ) hx _
  have hCe : C x₀ (p w₀) = μ₀ • p w₀ := by rw [hCp, heigen, map_smul]
  have hCsimple : Module.End.eigenspace (C x₀).toLinearMap μ₀ = Submodule.span ℝ {p w₀} := by
    apply le_antisymm
    · intro v hv
      have hve := Module.End.mem_eigenspace_iff.mp hv
      change C x₀ v = μ₀ • v at hve
      have ha : A x₀ (e.symmL ℝ x₀ v) = μ₀ • e.symmL ℝ x₀ v := by
        rw [← hCs, hve, map_smul]
      have hm : e.symmL ℝ x₀ v ∈ Submodule.span ℝ {w₀} :=
        hsimple ▸ Module.End.mem_eigenspace_iff.mpr ha
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      have hh := congrArg p hc
      rw [map_smul] at hh
      apply hh.trans
      simpa only [p, Trivialization.coe_continuousLinearEquivAt_eq] using
        e.continuousLinearMapAt_symmL (R := ℝ) hx v
    · apply Submodule.span_le.mpr
      intro v hv
      obtain rfl := Set.mem_singleton_iff.mp hv
      exact Module.End.mem_eigenspace_iff.mpr hCe
  obtain ⟨V, hVo, hxV, hVD, μ, w, hμ, hw, hμ₀, hw₀', heq⟩ :=
    Poincare.Topology.Manifold.exists_contMDiff_bilinear_normalized_eigenpair C B
      (hU.inter e.open_baseSet) hC hB (p₀ := x₀) ⟨hx₀, hx⟩
      (fun u v ↦ g.symm x₀ _ _)
      (by intro u v; change g.inner x₀ (e.symmL ℝ x₀ (C x₀ u)) (e.symmL ℝ x₀ v) =
            g.inner x₀ (e.symmL ℝ x₀ u) (e.symmL ℝ x₀ (C x₀ v))
          rw [hCs, hCs]; exact hself _ _)
      μ₀ (p w₀) (by change g.inner x₀ (e.symmL ℝ x₀ (p w₀)) (e.symmL ℝ x₀ (p w₀)) = 1
                    rwa [hp]) hCe hCsimple
  refine ⟨V, hVo, hxV, fun x hx ↦ (hVD hx).1, μ, (fun x ↦ e.symmL ℝ x (w x)),
    hμ, frame_section_smooth e (fun x hx ↦ (hVD hx).2) hw, hμ₀, ?_, ?_⟩
  · change e.symmL ℝ x₀ (w x₀) = w₀
    rw [hw₀', hp]
  · intro x hx
    refine ⟨(heq x hx).1, ?_⟩
    apply (e.continuousLinearEquivAt ℝ x (hVD hx).2).injective
    have hh := (heq x hx).2
    change e.continuousLinearMapAt ℝ x (A x (e.symmL ℝ x (w x))) = μ x • w x at hh
    simpa only [Trivialization.coe_continuousLinearEquivAt_eq, map_smul,
      e.continuousLinearMapAt_symmL (R := ℝ) (hVD hx).2] using hh

end Poincare.Geometry.VectorBundle
