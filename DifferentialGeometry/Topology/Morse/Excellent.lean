import DifferentialGeometry.Topology.Morse.ExcellentFamily
import DifferentialGeometry.Topology.Morse.RelativePerturbationPositive
import DifferentialGeometry.Topology.Order.FiniteSeparation

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]


theorem exists_positive_distinct_critical_values {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hC : {x | IsCriticalPointAt I f x}.Finite) {U S : Set M}
    (hU : IsOpen U) (hCU : {x | IsCriticalPointAt I f x} ⊆ U)
    (hUI : ∀ x ∈ U, I.IsInteriorPoint x) (hUS : U ⊆ S) (hpos : ∀ x ∈ S, 0 < f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ EqOn g f N) ∧
      (∀ x ∈ S, 0 < g x) ∧
      {x | IsCriticalPointAt I g x} = {x | IsCriticalPointAt I f x} ∧
      InjOn g {x | IsCriticalPointAt I g x} ∧
      ∀ x, IsCriticalPointAt I f x → ∃ b : ℝ, g =ᶠ[𝓝 x] (fun y => f y + b) := by
  obtain ⟨n,e,φ,ε,_,heC,hφ,hgerm,hε,hcrit⟩ :=
    exists_critical_value_perturbation_family hf hC hU hCU hUI
  obtain ⟨δ,hδ,hpositive⟩ := exists_pos_radius_finitePerturbation hf.continuous
    (fun i => (hφ i).1.continuous) (fun i => (hφ i).2.1)
    (fun i => (hφ i).2.2.trans hUS) hpos
  obtain ⟨p,hp,hinj⟩ := DifferentialGeometry.Topology.exists_small_injective_add (fun i => f (e i)) (lt_min hε hδ)
  have hpε : ‖p‖ < ε := lt_of_lt_of_le hp (min_le_left _ _)
  have hpδ : ‖p‖ < δ := lt_of_lt_of_le hp (min_le_right _ _)
  obtain ⟨N,hN,hUN,hfix⟩ := exists_open_finitePerturbation_eq (f := f) (fun i => (hφ i).2.2)
  refine ⟨finitePerturbation f φ p,contMDiff_finitePerturbation hf (fun i => (hφ i).1) p,
    ⟨N,hN,hUN,hfix p⟩,hpositive p hpδ,hcrit p hpε,?_,?_⟩
  · intro x hx y hy hxy
    have hxC := (Set.ext_iff.mp (hcrit p hpε) x).mp hx
    have hyC := (Set.ext_iff.mp (hcrit p hpε) y).mp hy
    obtain ⟨i,rfl⟩ := heC.symm ▸ hxC
    obtain ⟨j,rfl⟩ := heC.symm ▸ hyC
    apply congrArg e
    apply hinj
    exact (hgerm i p).eq_of_nhds.symm.trans (hxy.trans (hgerm j p).eq_of_nhds)
  · intro x hx
    obtain ⟨i,rfl⟩ := heC.symm ▸ (show x ∈ {x | IsCriticalPointAt I f x} from hx)
    exact ⟨p i,hgerm i p⟩


theorem exists_positive_relative_excellent_morse {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hC : {x | IsCriticalPointAt I f x}.Finite)
    (hnd : ∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x)
    {U S : Set M} (hU : IsOpen U) (hCU : {x | IsCriticalPointAt I f x} ⊆ U)
    (hUI : ∀ x ∈ U, I.IsInteriorPoint x) (hUS : U ⊆ S) (hpos : ∀ x ∈ S, 0 < f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ EqOn g f N) ∧
      (∀ x ∈ S, 0 < g x) ∧
      {x | IsCriticalPointAt I g x} = {x | IsCriticalPointAt I f x} ∧
      InjOn g {x | IsCriticalPointAt I g x} ∧
      (∀ x, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x) ∧
      ∀ x, IsCriticalPointAt I f x → ∃ b : ℝ, g =ᶠ[𝓝 x] (fun y => f y + b) := by
  obtain ⟨g,hg,hfix,hpositive,hcrit,hinj,hgerm⟩ :=
    exists_positive_distinct_critical_values hf hC hU hCU hUI hUS hpos
  refine ⟨g,hg,hfix,hpositive,hcrit,hinj,?_,hgerm⟩
  intro x hx
  have hxC := (Set.ext_iff.mp hcrit x).mp hx
  obtain ⟨b,hb⟩ := hgerm x hxC
  exact (isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const
    (hf.mdifferentiableAt (by simp)) (hUI x (hCU hxC)) hb).mpr (hnd x hxC)

end DifferentialGeometry.Morse
