import DifferentialGeometry.Topology.Morse.RelativePerturbationAvoidance
import DifferentialGeometry.Topology.Morse.CriticalFinite

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [T2Space M]


theorem exists_positive_relative_morse {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K U S : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUI : ∀ x ∈ U, I.IsInteriorPoint x)
    (hcrit : ∀ x, IsCriticalPointAt I f x → x ∈ K)
    (hUS : U ⊆ S) (hpos : ∀ x ∈ S, 0 < f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ EqOn g f N) ∧
      (∀ x ∈ S, 0 < g x) ∧
      (∀ x, IsCriticalPointAt I g x → I.IsInteriorPoint x ∧ IsNondegenerateCriticalPointAt I g x) ∧
      {x : M | IsCriticalPointAt I g x}.Finite := by
  obtain ⟨n,φ,hφ,hspan⟩ := exists_supported_differentials_span_of_isCompact (I := I) hK hU hKU
  have hKI : ∀ x ∈ K, I.IsInteriorPoint x := fun x hx => hUI x (hKU hx)
  obtain ⟨R,ε,hR,hKR,hRR,hε,havoid⟩ :=
    exists_open_radius_critical_mem_surjective_parameterDifferential hf (fun i => (hφ i).1)
      (fun i => (hφ i).2.1) (fun i x hx => hUI x ((hφ i).2.2 hx)) hKI
      (fun x hx => surjective_parameterDifferential (hspan x hx)) hcrit
  obtain ⟨δ,hδ,hpositive⟩ := exists_pos_radius_finitePerturbation hf.continuous
    (fun i => (hφ i).1.continuous) (fun i => (hφ i).2.1) (fun i => (hφ i).2.2.trans hUS) hpos
  let C : Set M := (⋃ i, tsupport (φ i)) ∪ K
  have hC : IsCompact C := (isCompact_iUnion (fun i => (hφ i).2.1)).union hK
  have hCI : ∀ x ∈ C, I.IsInteriorPoint x := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact hUI x ((hφ i).2.2 hi)
    · exact hKI x hx
  have hae := ae_nondegenerate_finitePerturbation_on_isCompact hf (fun i => (hφ i).1) hC hCI
  obtain ⟨p,hp,hgood⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
    (Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) 0 (lt_min hε hδ)).ne'
    (MeasureTheory.ae_restrict_of_ae hae)
  have hp' : ‖p‖ < min ε δ := by simpa only [Metric.mem_ball,dist_zero_right] using hp
  obtain ⟨N,hN,hUN,hfix⟩ := exists_open_finitePerturbation_eq (f := f) (φ := φ) (fun i => (hφ i).2.2)
  have hfp := contMDiff_finitePerturbation hf (fun i => (hφ i).1) p
  have hnondeg : ∀ x, IsCriticalPointAt I (finitePerturbation f φ p) x →
      I.IsInteriorPoint x ∧ IsNondegenerateCriticalPointAt I (finitePerturbation f φ p) x := by
    intro x hx
    have hxR := havoid p (lt_of_lt_of_le hp' (min_le_left _ _)) x hx
    have hxC : x ∈ C := critical_finitePerturbation_mem_support_union hcrit p hx
    exact ⟨(hRR x hxR).1,isNondegenerateCriticalPointAt_of_bijective_hessian hfp (hRR x hxR).1 hx
      (hgood x hxC (hRR x hxR).2 hx)⟩
  refine ⟨finitePerturbation f φ p,hfp,⟨N,hN,hUN,hfix p⟩,
    hpositive p (lt_of_lt_of_le hp' (min_le_right _ _)),hnondeg,?_⟩
  exact finite_criticalPoints_of_isCompact hfp hC hCI
    (fun _ hx => critical_finitePerturbation_mem_support_union hcrit p hx) (fun x hx => (hnondeg x hx).2)

end DifferentialGeometry.Morse
