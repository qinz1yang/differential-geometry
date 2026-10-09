import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.LinearAlgebra.Determinant
import DifferentialGeometry.Analysis.Calculus.Inverse.DerivativePerturbation
import DifferentialGeometry.Analysis.Calculus.Inverse.PerturbationDeterminant

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn mapDerivNorm
  mapDerivNorm_nonneg)
namespace DifferentialGeometry.Analysis

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem tendsto_fderiv_of_mapCPConvergenceOn {S : Set E} {T : ℕ → E → F} {T₀ : E → F}
    (hconv : MapCPConvergenceOn S 1 T T₀) {u : E} (hu : u ∈ S)
    (hT₀ : DifferentiableAt ℝ T₀ u) (hT : ∀ᶠ i in atTop, DifferentiableAt ℝ (T i) u) :
    Tendsto (fun i => fderiv ℝ (T i) u) atTop (𝓝 (fderiv ℝ T₀ u)) := by
  have hmd : Tendsto (fun i => mapDerivNorm 1 (T i) T₀ u) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k0, hk0⟩ := hconv (ε / 2) (by positivity)
    refine ⟨k0, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mapDerivNorm_nonneg 1 (T k) T₀ u)]
    exact (hk0 k hk 1 le_rfl u hu).trans_lt (by linarith)
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (hmd.congr' ?_)
  filter_upwards [hT] with i hi
  have hn := norm_iteratedFDeriv_one (𝕜 := ℝ) (fun y => T i y - T₀ y) (x := u)
  rw [fderiv_fun_sub hi hT₀] at hn
  exact hn

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem det_fderiv_ne_zero_of_eventuallyEq_id {f g : E → E} {u : E}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g (f u)) (hgf : g ∘ f =ᶠ[𝓝 u] id) :
    (fderiv ℝ f u).det ≠ 0 := by
  have h1 : (fderiv ℝ g (f u)).comp (fderiv ℝ f u) = ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp u hg hf, hgf.fderiv_eq, fderiv_id]
  have h2 : LinearMap.det (fderiv ℝ g (f u) : E →ₗ[ℝ] E) *
      LinearMap.det (fderiv ℝ f u : E →ₗ[ℝ] E) = 1 := by
    rw [← LinearMap.det_comp]
    exact (congrArg (fun T : E →L[ℝ] E => LinearMap.det (T : E →ₗ[ℝ] E)) h1).trans
      LinearMap.det_id
  exact right_ne_zero_of_mul_eq_one h2

omit [NormedSpace ℝ E] in
theorem trans_symm_apply_mem_source {X : Type*} [TopologicalSpace X]
    {e e' : OpenPartialHomeomorph E X} {u : E} (hu : u ∈ (e.trans e'.symm).source) :
    (e.trans e'.symm) u ∈ (e'.trans e.symm).source := by
  rw [OpenPartialHomeomorph.trans_source] at hu ⊢
  have hu2 : e u ∈ e'.target := hu.2
  refine ⟨e'.map_target hu2, ?_⟩
  change e' (e'.symm (e u)) ∈ e.symm.source
  rw [e'.right_inv hu2]
  exact e.map_source hu.1

theorem det_fderiv_trans_symm_ne_zero {X : Type*} [TopologicalSpace X]
    {e e' : OpenPartialHomeomorph E X} {u : E} (hu : u ∈ (e.trans e'.symm).source)
    (hd : DifferentiableAt ℝ (e.trans e'.symm) u)
    (hd' : DifferentiableAt ℝ (e'.trans e.symm) ((e.trans e'.symm) u)) :
    (fderiv ℝ (e.trans e'.symm) u).det ≠ 0 := by
  refine det_fderiv_ne_zero_of_eventuallyEq_id hd hd' ?_
  filter_upwards [(e.trans e'.symm).open_source.mem_nhds hu] with x hx
  have hx' : x ∈ e.source ∩ e ⁻¹' e'.symm.source := by
    rw [← OpenPartialHomeomorph.trans_source]
    exact hx
  have hx2 : e x ∈ e'.target := hx'.2
  change e.symm (e' (e'.symm (e x))) = x
  rw [e'.right_inv hx2, e.left_inv hx'.1]

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem det_fderiv_pos_of_mapCPConvergenceOn_at {S : Set E} {T : ℕ → E → E} {T₀ : E → E}
    (hconv : MapCPConvergenceOn S 1 T T₀) {u : E} (hu : u ∈ S)
    (hT₀ : DifferentiableAt ℝ T₀ u) (hne : (fderiv ℝ T₀ u).det ≠ 0)
    (hpos : ∀ᶠ i in atTop, DifferentiableAt ℝ (T i) u ∧ 0 < (fderiv ℝ (T i) u).det) :
    0 < (fderiv ℝ T₀ u).det := by
  have hd := tendsto_fderiv_of_mapCPConvergenceOn hconv hu hT₀ (hpos.mono fun _ hi => hi.1)
  have hdet : Tendsto (fun i => (fderiv ℝ (T i) u).det) atTop (𝓝 (fderiv ℝ T₀ u).det) :=
    (ContinuousLinearMap.continuous_det.tendsto _).comp hd
  have hge : 0 ≤ (fderiv ℝ T₀ u).det := ge_of_tendsto hdet (hpos.mono fun _ hi => hi.2.le)
  exact lt_of_le_of_ne hge (Ne.symm hne)

omit [FiniteDimensional ℝ E] in
theorem det_fderiv_pos_of_mapCPConvergenceOn {S : Set E} {T : ℕ → E → E} {T₀ : E → E}
    (hconv : MapCPConvergenceOn S 1 T T₀) (hT₀ : ∀ u ∈ S, DifferentiableAt ℝ T₀ u)
    (hne : ∀ u ∈ S, (fderiv ℝ T₀ u).det ≠ 0)
    (hpos : ∀ u ∈ S, ∀ᶠ i in atTop, DifferentiableAt ℝ (T i) u ∧ 0 < (fderiv ℝ (T i) u).det) :
    ∀ u ∈ S, 0 < (fderiv ℝ T₀ u).det :=
  fun u hu => det_fderiv_pos_of_mapCPConvergenceOn_at hconv hu (hT₀ u hu) (hne u hu) (hpos u hu)

end

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem MapCPConvergenceOn.eventually_det_fderiv_pos
    {K : Set E} {F : ℕ → E → E} (hF : MapCPConvergenceOn K 1 F id)
    (hdiff : ∀ᶠ n in atTop, ∀ x ∈ K, DifferentiableAt ℝ (F n) x) :
    ∀ᶠ n in atTop, ∀ x ∈ K, 0 < (fderiv ℝ (F n) x).det := by
  classical
  by_cases hfin : FiniteDimensional ℝ E
  · let _ : FiniteDimensional ℝ E := hfin
    obtain ⟨N, hN⟩ := hF (1 / 2) (by norm_num)
    filter_upwards [eventually_ge_atTop N, hdiff] with n hn hdn x hx
    have hbound : ‖fderiv ℝ (F n) x - ContinuousLinearMap.id ℝ E‖ < 1 := by
      rw [norm_sub_rev]
      exact (neumannOfDerivNorm (hdn x hx) (hN n hn 1 le_rfl x hx)).trans_lt
        (by norm_num)
    have hpos := DifferentialGeometry.Analysis.det_id_add_pos
      (fderiv ℝ (F n) x - ContinuousLinearMap.id ℝ E) hbound
    have heq : ContinuousLinearMap.id ℝ E +
        (fderiv ℝ (F n) x - ContinuousLinearMap.id ℝ E) = fderiv ℝ (F n) x := by abel
    rwa [heq] at hpos
  · exact Filter.Eventually.of_forall fun n x _ => by
      change 0 < LinearMap.det (fderiv ℝ (F n) x).toLinearMap
      rw [LinearMap.det_eq_one_of_not_module_finite hfin]
      exact zero_lt_one

end DifferentialGeometry.CheegerGromovCompactness
