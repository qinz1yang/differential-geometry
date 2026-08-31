import DifferentialGeometry.Geometry.Metric.SmoothVectorFieldExt
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.BumpFunction

noncomputable section


open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]


theorem exists_contMDiff_vectorField_eq (q : M) (v : TangentSpace I q) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (V x)) ∧
      V q = v := by
  classical
  set c : E := (trivializationAt E (TangentSpace I) q ⟨q, v⟩).2 with hc
  let f : SmoothBumpFunction I q := Classical.arbitrary _
  have htsupp : tsupport (⇑f) ⊆ (trivializationAt E (TangentSpace I) q).baseSet := by
    have h1 := f.tsupport_subset_extChartAt_source
    rw [extChartAt_source] at h1
    exact h1
  refine ⟨fun x => f x • chartConstVecFiber (I := I) q c x, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport
      (f.contMDiff.contMDiffOn) (trivializationAt E (TangentSpace I) q).open_baseSet htsupp
      (chartConstVec_contMDiffOn (I := I) q c)
  · have hf1 : f q = 1 := f.eventuallyEq_one.self_of_nhds
    change f q • chartConstVecFiber (I := I) q c q = v
    rw [hf1, one_smul, chartConstVecFiber_self]

theorem exists_contMDiff_vectorFieldAlong_zero_endpoints
    (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (a c b : Real) (P : TangentSpace I (gamma c)) :
    ∃ W : Real → E,
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (gamma s) (W s) : TangentBundle I M)) ∧
      W a = 0 ∧ W b = 0 ∧ W c = ((c - a) * (b - c)) • P := by
  obtain ⟨X, hX, hXc⟩ := exists_contMDiff_vectorField_eq (I := I) (gamma c) P
  let chi : Real → Real := fun s ↦ (s - a) * (b - s)
  let W : Real → E := fun s ↦ chi s • X (gamma s)
  have hchi : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ chi := by
    exact (contMDiff_id.sub contMDiff_const).mul (contMDiff_const.sub contMDiff_id)
  have hXalong : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma s) (X (gamma s)) : TangentBundle I M)) := by
    exact hX.comp hgamma
  have hW : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma s) (W s) : TangentBundle I M)) := by
    intro s0
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨hgamma s0, ?_⟩
    have hXfib := ((Bundle.contMDiffAt_totalSpace (f := fun s : Real ↦
      (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (gamma s) (X (gamma s)) : TangentBundle I M))).1 (hXalong s0)).2
    have hsmul := (hchi s0).smul hXfib
    refine hsmul.congr_of_eventuallyEq ?_
    have hbase : ∀ᶠ s in 𝓝 s0,
        gamma s ∈ (trivializationAt E (TangentSpace I) (gamma s0)).baseSet := by
      have hmem : gamma s0 ∈
          (trivializationAt E (TangentSpace I) (gamma s0)).baseSet :=
        FiberBundle.mem_baseSet_trivializationAt' (gamma s0)
      exact (hgamma s0).continuousAt.preimage_mem_nhds
        ((trivializationAt E (TangentSpace I) (gamma s0)).open_baseSet.mem_nhds hmem)
    filter_upwards [hbase] with s hs
    simp only [W, TotalSpace.mk']
    change _ = chi s •
      (((trivializationAt E (TangentSpace I) (gamma s0))
        (TotalSpace.mk' E (gamma s) (X (gamma s)) : TangentBundle I M)).2)
    rw [(trivializationAt E (TangentSpace I) (gamma s0)).apply_eq_prod_continuousLinearEquivAt
          Real (gamma s) hs,
      (trivializationAt E (TangentSpace I) (gamma s0)).apply_eq_prod_continuousLinearEquivAt
          Real (gamma s) hs]
    exact map_smul _ _ _
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · simp only [W, chi, sub_self, zero_mul, zero_smul]
    rfl
  · simp only [W, chi, sub_self, mul_zero, zero_smul]
    rfl
  · simp only [W, chi, hXc]
    rfl

end Riemannian
end Geometry
end DifferentialGeometry

end
