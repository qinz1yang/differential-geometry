import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.JacobiField.FamilyChain.Defs

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

section Along

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] {n : WithTop ℕ∞} {α : ℝ → X} {t₀ : ℝ}

private theorem coord_eq_clm {t : ℝ}
    (ht : α t ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)).baseSet)
    (w : TangentSpace ThreeModel (α t)) :
    (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)
        (TotalSpace.mk' ThreeSpace (α t) w)).2 =
      (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)).continuousLinearMapAt ℝ
        (α t) w := by
  rw [(trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)).continuousLinearMapAt_apply
    (R := ℝ), (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)).coe_linearMapAt_of_mem
    ht]

private theorem eventually_baseSet (hα : ContinuousAt α t₀) : ∀ᶠ t in 𝓝 t₀,
    α t ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)).baseSet :=
  hα.preimage_mem_nhds
    ((trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)))

theorem contMDiffAt_totalSpace_add {V W : ∀ t, TangentSpace ThreeModel (α t)}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel.tangent n
      (fun t => (TotalSpace.mk' ThreeSpace (α t) (V t) : TangentBundle ThreeModel X)) t₀)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel.tangent n
      (fun t => (TotalSpace.mk' ThreeSpace (α t) (W t) : TangentBundle ThreeModel X)) t₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel.tangent n
      (fun t => (TotalSpace.mk' ThreeSpace (α t) (V t + W t) : TangentBundle ThreeModel X))
      t₀ := by
  rw [Bundle.contMDiffAt_totalSpace] at hV hW ⊢
  refine ⟨hV.1, (hV.2.add hW.2).congr_of_eventuallyEq ?_⟩
  filter_upwards [eventually_baseSet hV.1.continuousAt] with t ht
  change (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)
    (TotalSpace.mk' ThreeSpace (α t) (V t + W t))).2 =
    (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)
      (TotalSpace.mk' ThreeSpace (α t) (V t))).2 +
    (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)
      (TotalSpace.mk' ThreeSpace (α t) (W t))).2
  rw [coord_eq_clm ht, coord_eq_clm ht, coord_eq_clm ht, map_add]

theorem contMDiffAt_totalSpace_smul {ρ : ℝ → ℝ} {V : ∀ t, TangentSpace ThreeModel (α t)}
    (hρ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n ρ t₀)
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel.tangent n
      (fun t => (TotalSpace.mk' ThreeSpace (α t) (V t) : TangentBundle ThreeModel X)) t₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel.tangent n
      (fun t => (TotalSpace.mk' ThreeSpace (α t) (ρ t • V t) : TangentBundle ThreeModel X))
      t₀ := by
  rw [Bundle.contMDiffAt_totalSpace] at hV ⊢
  refine ⟨hV.1, (hρ.smul hV.2).congr_of_eventuallyEq ?_⟩
  filter_upwards [eventually_baseSet hV.1.continuousAt] with t ht
  change (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)
    (TotalSpace.mk' ThreeSpace (α t) (ρ t • V t))).2 =
    ρ t • (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)
      (TotalSpace.mk' ThreeSpace (α t) (V t))).2
  rw [coord_eq_clm ht, coord_eq_clm ht, map_smul]

theorem contMDiffAt_totalSpace_zero (hα : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel n α t₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel.tangent n
      (fun t => (TotalSpace.mk' ThreeSpace (α t) (0 : TangentSpace ThreeModel (α t)) :
        TangentBundle ThreeModel X)) t₀ := by
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hα, (contMDiffAt_const (c := (0 : ThreeSpace))).congr_of_eventuallyEq ?_⟩
  filter_upwards [eventually_baseSet hα.continuousAt] with t ht
  change (trivializationAt ThreeSpace (TangentSpace ThreeModel) (α t₀)
    (TotalSpace.mk' ThreeSpace (α t) (0 : TangentSpace ThreeModel (α t)))).2 = 0
  rw [coord_eq_clm ht, map_zero]

end Along

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
