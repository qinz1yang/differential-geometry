import DifferentialGeometry.Topology.Morse.RelativePerturbationAvoidance
import DifferentialGeometry.Topology.Manifold.FinitePointBumps
import DifferentialGeometry.Topology.Morse.ConstantGerm

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace Poincare.Morse
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]


theorem exists_critical_value_perturbation_family {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hC : {x | IsCriticalPointAt I f x}.Finite) {U : Set M}
    (hU : IsOpen U) (hCU : {x | IsCriticalPointAt I f x} ⊆ U)
    (hUI : ∀ x ∈ U, I.IsInteriorPoint x) :
    ∃ (n : ℕ) (e : Fin n → M) (φ : Fin n → M → ℝ) (ε : ℝ),
      Injective e ∧ range e = {x | IsCriticalPointAt I f x} ∧
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      (∀ i p, finitePerturbation f φ p =ᶠ[𝓝 (e i)] (fun y => f y + p i)) ∧
      0 < ε ∧ ∀ p : Fin n → ℝ, ‖p‖ < ε →
        {x | IsCriticalPointAt I (finitePerturbation f φ p) x} = {x | IsCriticalPointAt I f x} := by
  classical
  let C := {x | IsCriticalPointAt I f x}
  let : Fintype C := hC.fintype
  let n := Fintype.card C
  let e : Fin n → M := fun i => ((Fintype.equivFin C).symm i : M)
  have he : Injective e := Subtype.val_injective.comp (Fintype.equivFin C).symm.injective
  have heC : range e = C := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ((Fintype.equivFin C).symm i).property
    · intro hx
      exact ⟨(Fintype.equivFin C) ⟨x,hx⟩,by simp [e]⟩
  obtain ⟨φ,hφ,hgerm⟩ := Poincare.Manifold.exists_finite_point_bumps (I := I) he hU
    (fun i => hCU ((Fintype.equivFin C).symm i).property)
  have hlocal : ∀ i, ∃ R : Set M, IsOpen R ∧ e i ∈ R ∧
      ∀ y ∈ R, ∀ j, φ j y = if j = i then 1 else 0 := by
    intro i
    have hnear : ∀ᶠ y in 𝓝 (e i), ∀ j, φ j y = if j = i then 1 else 0 := by
      apply Filter.eventually_all.mpr
      intro j
      by_cases hji : j = i
      · subst j
        filter_upwards [(hgerm i).1] with y hy
        simpa only [ite_true] using hy
      · filter_upwards [(hgerm i).2 j hji] with y hy
        simpa only [hji,ite_false] using hy
    obtain ⟨R,hR,hRo,hi⟩ := mem_nhds_iff.mp hnear
    exact ⟨R,hRo,hi,hR⟩
  choose R hR hiR hval using hlocal
  have hfamily : ∀ i p, EqOn (finitePerturbation f φ p) (fun y => f y + p i) (R i) := by
    intro i p y hy
    simp [finitePerturbation,hval i y hy]
  have hfamilyGerm : ∀ i p x, x ∈ R i →
      finitePerturbation f φ p =ᶠ[𝓝 x] (fun y => f y + p i) := by
    intro i p x hx
    filter_upwards [(hR i).mem_nhds hx] with y hy
    exact hfamily i p hy
  have hcritLocal : ∀ i p x, x ∈ R i →
      (IsCriticalPointAt I (finitePerturbation f φ p) x ↔ IsCriticalPointAt I f x) := by
    intro i p x hx
    exact isCriticalPointAt_iff_of_eventuallyEq_add_const (hf.mdifferentiableAt (by simp))
      (hfamilyGerm i p x hx)
  let V : Set M := ⋃ i, R i
  have hV : IsOpen V := isOpen_iUnion hR
  have hCV : C ⊆ V := by
    intro x hx
    obtain ⟨i,rfl⟩ := heC.symm ▸ hx
    exact mem_iUnion.mpr ⟨i,hiR i⟩
  let A : Set M := ⋃ i, tsupport (φ i)
  have hA : IsCompact A := isCompact_iUnion (fun i => (hφ i).2.1)
  have hAU : A ⊆ U := iUnion_subset fun i => (hφ i).2.2
  have hL : IsCompact (A ∩ Vᶜ) := hA.inter_right hV.isClosed_compl
  obtain ⟨ε,hε,havoid⟩ := exists_radius_mfderiv_finitePerturbation_ne_zero hf (fun i => (hφ i).1)
    hL (fun x hx => hUI x (hAU hx.1)) (fun x hx hz => hx.2 (hCV hz))
  obtain ⟨N,hN,hAN,hfix⟩ := exists_open_finitePerturbation_eq (f := f) (φ := φ)
    (U := A) (fun i => subset_iUnion (fun i => tsupport (φ i)) i)
  refine ⟨n,e,φ,ε,he,heC,hφ,(fun i p => hfamilyGerm i p (e i) (hiR i)),hε,?_⟩
  intro p hp
  ext x
  change mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x = 0 ↔ mfderiv I 𝓘(ℝ, ℝ) f x = 0
  by_cases hxV : x ∈ V
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hxV
    exact hcritLocal i p x hi
  · by_cases hxA : x ∈ A
    · exact iff_of_false (havoid p hp x ⟨hxA,hxV⟩) (fun hz => hxV (hCV hz))
    · have hh : finitePerturbation f φ p =ᶠ[𝓝 x] f := by
        filter_upwards [hN.mem_nhds (hAN hxA)] with y hy
        exact hfix p hy
      exact Iff.of_eq (congrArg (fun L : E →L[ℝ] ℝ => L = 0) hh.mfderiv_eq)

end Poincare.Morse
