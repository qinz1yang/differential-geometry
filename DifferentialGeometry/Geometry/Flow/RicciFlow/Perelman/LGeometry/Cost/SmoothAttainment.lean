import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import Mathlib.Geometry.Manifold.Metrizable
import DifferentialGeometry.Topology.Manifold.ZeroDimensional
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

theorem exists_contMDiff_lCost_minimizer
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T τ : ℝ) (hτ : 0 < τ) (hreg : Icc (T - τ) T ⊆ D.regular)
    (x y : M) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀)
    (h₀ : α₀ 0 = x) (h₁ : α₀ (Real.sqrt τ) = y) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧ α 0 = x ∧ α (Real.sqrt τ) = y ∧
      lLength S T (squareRootReparametrization α) 0 τ = lCost S T x y τ := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : DiscreteTopology M := DifferentialGeometry.discrete_topology_of_finrank_eq_zero I hdim
    have hconst (β : ℝ → M) (hβ : ContMDiff 𝓘(ℝ, ℝ) I 1 β) (hβ0 : β 0 = x) : β = fun _ => x := by
      funext t
      exact ((IsLocallyConstant.iff_continuous β).mpr hβ.continuous).apply_eq_of_preconnectedSpace t 0 |>.trans hβ0
    have hy : y = x := h₁.symm.trans (congrFun (hconst α₀ hα₀ h₀) (Real.sqrt τ))
    let α : ℝ → M := fun _ => x
    refine ⟨α,contMDiff_const,rfl,hy.symm,?_⟩
    unfold lCost
    have hset : {r : ℝ | ∃ β : ℝ → M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 β ∧ β 0 = x ∧ β (Real.sqrt τ) = y ∧
          lLength S T (squareRootReparametrization β) 0 τ = r} =
        {lLength S T (squareRootReparametrization α) 0 τ} := by
      ext r
      constructor
      · rintro ⟨β,hβ,hβ0,_,hr⟩
        rw [hconst β hβ hβ0] at hr
        exact hr.symm
      · intro hr
        exact ⟨α,contMDiff_const,rfl,hy.symm,hr.symm⟩
    rw [hset,csInf_singleton]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  have hback (s : ℝ) (hs : s ∈ Icc (0:ℝ) (Real.sqrt τ)) : T-s^2 ∈ Icc (T - τ) T := by
    have hsq : s^2 ≤ τ := (sq_le_sq₀ hs.1 (Real.sqrt_nonneg τ)).mpr hs.2 |>.trans_eq (Real.sq_sqrt hτ.le)
    exact ⟨by linarith,by linarith [sq_nonneg s]⟩
  obtain ⟨Z,hmin,hend⟩ := exists_lMinimizingVector S hS T (T - τ) T τ hτ
    (hreg.trans D.regular_subset) hback x y α₀ hα₀ h₀ h₁
    (fun s hs => hreg (hback s hs))
  obtain ⟨hdom,hcost⟩ := (mem_lMinDomain S T x Z τ).mp hmin
  obtain ⟨_,_,hroot⟩ := (mem_lExpPosDom S T x Z τ).mp hdom
  obtain ⟨ρ,hρ,hρid,_,hρrange⟩ := exists_lRegularizedDomain_smoothClamp S T x Z
    (Real.sqrt_pos.mpr hτ) hroot
  let α : ℝ → M := fun s => lRegularizedCurve S T x Z (ρ s)
  have hα : ContMDiff 𝓘(ℝ, ℝ) I ∞ α := by
    rw [← contMDiffOn_univ]
    exact (lRegularizedCurve_smoothOn S hS T x).comp
      (contMDiff_const.prodMk hρ.contMDiff).contMDiffOn (fun s _ => hρrange s)
  have hαeq : EqOn α (lRegularizedCurve S T x Z) (Icc (0:ℝ) (Real.sqrt τ)) := by
    intro s hs
    exact congrArg (lRegularizedCurve S T x Z) (hρid hs)
  have hα0 : α 0 = x := (hαeq ⟨le_rfl,Real.sqrt_nonneg τ⟩).trans (lRegularizedCurve_zero S T x Z)
  have hα1 : α (Real.sqrt τ) = y := (hαeq ⟨Real.sqrt_nonneg τ,le_rfl⟩).trans hend
  refine ⟨α,hα,hα0,hα1,?_⟩
  rw [lLength_squareRootReparametrization_eq_lRegularizedAction S T α τ hτ.le]
  have heq : lRegularizedAction S T α 0 (Real.sqrt τ) =
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt τ) := by
    apply lRegularizedAction_congr
    intro s hs
    have hs' : s ∈ Ioo (0:ℝ) (Real.sqrt τ) := by
      simpa only [uIoo_of_le (Real.sqrt_nonneg τ)] using hs
    exact hαeq ⟨hs'.1.le,hs'.2.le⟩
  rw [heq,← lLength_squareRootReparametrization_eq_lRegularizedAction S T (lRegularizedCurve S T x Z) τ hτ.le]
  exact hcost.trans (congrArg (fun z => lCost S T x z τ) hend)

end DifferentialGeometry.PDE.RicciFlow.Perelman
