import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Normed.Module.Dual

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_smooth_function_with_differential
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (x : M) (a : ℝ) (α : TangentSpace I x →L[ℝ] ℝ)
    {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ f x = a ∧
      mvfderiv I f x = α ∧ HasCompactSupport f ∧ tsupport f ⊆ U := by
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU
  let e := extChartAt I x
  let D : TangentSpace I x →L[ℝ] E := mfderiv I 𝓘(ℝ, E) e x
  have hD : D.IsInvertible := isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)
  let L : E →L[ℝ] ℝ := α.comp D.inverse
  let F : E → ℝ := fun z ↦ a + L (z - e x)
  let f : M → ℝ := fun y ↦ χ y * F (e y)
  have hF : ContDiff ℝ ∞ F := contDiff_const.add
    (L.contDiff.comp (contDiff_id.sub contDiff_const))
  have hFs : ContMDiffOn I 𝓘(ℝ) ∞ (F ∘ e) (chartAt H x).source :=
    hF.contMDiff.comp_contMDiffOn contMDiffOn_extChartAt
  have hf : ContMDiff I 𝓘(ℝ) ∞ f := χ.contMDiff_smul hFs
  have heq : f =ᶠ[𝓝 x] F ∘ e := by
    filter_upwards [χ.eventuallyEq_one] with y hy
    change χ y * F (e y) = F (e y)
    rw [hy]
    exact one_mul _
  have hFd : HasFDerivAt F L (e x) := by
    convert (L.hasFDerivAt.comp (e x)
      ((hasFDerivAt_id (e x)).sub_const (e x))).const_add a using 1
    all_goals rfl
  have he : MDifferentiableAt I 𝓘(ℝ, E) e x :=
    (contMDiffAt_extChartAt (I := I) (x := x) (n := ∞)).mdifferentiableAt (by simp)
  have hder : mvfderiv I f x = α := by
    have hfder : mvfderiv I f x = mvfderiv I (F ∘ e) x := heq.mfderiv_eq
    rw [hfder, mvfderiv_comp x hFd.differentiableAt.mdifferentiableAt he]
    have hFd' : mvfderiv 𝓘(ℝ, E) F (e x) = L := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) F (e x) = L
      rw [mfderiv_eq_fderiv]
      exact hFd.fderiv
    rw [hFd']
    change (α.comp D.inverse).comp D = α
    rw [ContinuousLinearMap.comp_assoc, hD.inverse_comp_self,
      ContinuousLinearMap.comp_id]
  have hsupport : tsupport f ⊆ tsupport χ := tsupport_mul_subset_left
  refine ⟨f, hf, ?_, hder, ?_, hsupport.trans hχ⟩
  · rw [heq.eq_of_nhds]
    simp [F]
  · exact χ.hasCompactSupport.of_isClosed_subset isClosed_closure hsupport

theorem tangent_eq_of_smooth_function_differentials
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {x : M} {v w : TangentSpace I x}
    (h : ∀ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f → HasCompactSupport f →
      mvfderiv I f x v = mvfderiv I f x w) : v = w := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ) (V := E)).mpr
  intro α
  obtain ⟨f, hf, _, hd, hc, _⟩ :=
    exists_smooth_function_with_differential (I := I) x 0 α
      (U := Set.univ) Filter.univ_mem
  exact hd ▸ h f hf hc

end DifferentialGeometry.Topology.Manifold
