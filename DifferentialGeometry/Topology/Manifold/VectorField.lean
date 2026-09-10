import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

noncomputable section
open scoped ContDiff Manifold Topology
open Bundle

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [IsManifold I ∞ M] [T2Space M]

theorem exists_compactlySupported_vectorField_eq (x₀ : M)
    (v : TangentSpace I x₀) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯,
      V x₀ = v ∧ IsCompact (tsupport V) ∧ tsupport V ⊆ U := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have he : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  obtain ⟨β, -, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp
    (Filter.inter_mem hU (e.open_baseSet.mem_nhds he))
  let w := e.continuousLinearMapAt ℝ x₀ v
  let s : (x : M) → TangentSpace I x := fun x ↦ e.symmL ℝ x w
  have hs : ContMDiffOn I I.tangent ∞
      (fun x ↦ (⟨x, s x⟩ : TangentBundle I M)) e.baseSet := by
    rw [e.contMDiffOn_iff (fun x hx ↦ e.mem_source.mpr hx)]
    refine ⟨contMDiffOn_id, (contMDiffOn_const (c := w)).congr ?_⟩
    intro x hx
    dsimp only [s]
    rw [e.symmL_apply hx, e.apply_mk_symm hx]
  have hsm := β.contMDiff.contMDiffOn.smul_section_of_tsupport
    e.open_baseSet (fun x hx ↦ (hβ hx).2) hs
  let V : Cₛ^∞⟮I; E, TangentSpace I⟯ := ⟨(fun x ↦ β x • s x), hsm⟩
  have hsupp : tsupport V ⊆ tsupport β := tsupport_smul_subset_left _ _
  refine ⟨V, ?_, β.hasCompactSupport.of_isClosed_subset (isClosed_tsupport V) hsupp,
    fun x hx ↦ (hβ (hsupp hx)).1⟩
  change β x₀ • e.symmL ℝ x₀ (e.continuousLinearMapAt ℝ x₀ v) = v
  rw [β.eq_one, one_smul]
  simpa only [Trivialization.symm_continuousLinearEquivAt_eq,
    Trivialization.coe_continuousLinearEquivAt_eq] using
    (e.continuousLinearEquivAt ℝ x₀ he).symm_apply_apply v

end Poincare.Topology.Manifold
