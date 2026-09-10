import DifferentialGeometry.Topology.Morse.FiniteBandEuler
import DifferentialGeometry.Topology.Morse.BoundaryExcellentHomeomorph

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace Poincare.Morse
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_relative_morse_eulerChar :
    ∃ f : M → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ x, f x ≤ 0) ∧ (∀ x, f x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x) ∧
      (∀ x, (𝓡∂ (n + 1)).IsInteriorPoint x → f x < 0) ∧
      (∀ x, IsCriticalPointAt (𝓡∂ (n + 1)) f x →
        (𝓡∂ (n + 1)).IsInteriorPoint x ∧ IsNondegenerateCriticalPointAt (𝓡∂ (n + 1)) f x) ∧
      InjOn f {x | IsCriticalPointAt (𝓡∂ (n + 1)) f x} ∧
      ∃ hfinite : {x | IsCriticalPointAt (𝓡∂ (n + 1)) f x}.Finite,
        ∀ (K : Type) [Field K],
          Poincare.Homology.finiteHomologyType K (TopCat.of M) ∧
          Poincare.Homology.eulerChar K (TopCat.of M) =
            ∑ p ∈ hfinite.toFinset, (-1 : ℤ) ^ sigNeg (chartHessianAt
              (fun y => f ((extChartAt (𝓡∂ (n + 1)) p).symm y))
              (extChartAt (𝓡∂ (n + 1)) p p)) := by
  obtain ⟨f,a,c,W,hf,_,hc,hbound,_,hlevel,_,_,hcrit,_,hfinite,hinj,hint,⟨hhomeo⟩,_⟩ :=
    exists_relative_excellent_morse_sublevel_homeomorph (M := M) (n := n) 0
  have hz : ∀ x, f x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x := by
    intro x
    change (x ∈ f ⁻¹' {0}) ↔ x ∈ (𝓡∂ (n + 1)).boundary M
    rw [hlevel]
  have hnegative : ∀ x, (𝓡∂ (n + 1)).IsInteriorPoint x → f x < 0 := by
    intro x hx
    apply lt_of_le_of_ne (hbound x).2
    intro he
    exact ((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mp hx ((hz x).mp he)
  refine ⟨f,hf,fun x => (hbound x).2,hz,hnegative,fun x hx =>
    ⟨(hcrit x hx).1,(hcrit x hx).2.1⟩,hinj,hfinite,?_⟩
  intro K instK
  obtain ⟨hfin, hχ⟩ := finiteHomologyType_and_eulerChar_of_finite_morse_sublevel
    (𝓡∂ (n + 1)) K (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (n + 1)))
    hf c (isClosed_Iic.preimage hf.continuous).isCompact hint hfinite
    (fun x hx => (hcrit x hx).2.1) hinj (fun x hx => (hcrit x hx).2.2)
  exact ⟨(Poincare.Homology.finiteHomologyType_iff_of_homeomorph K
      (X := TopCat.of M) (Y := TopCat.of (SublevelSpace f c)) hhomeo).mpr hfin,
    (Poincare.Homology.eulerChar_eq_of_homeomorph K hhomeo).trans hχ⟩

end Poincare.Morse
