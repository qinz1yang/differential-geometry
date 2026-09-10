import DifferentialGeometry.Topology.Manifold.Boundary.DefiningFunction
import DifferentialGeometry.Topology.Morse.RelativePerturbationGlobal

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace Poincare.Morse
variable {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [T2Space M] [CompactSpace M]


theorem exists_morse_boundary_definingFunction :
    ∃ (r : M → ℝ) (W : TopologicalSpace.Opens M), ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ r ∧
      (∀ x, 0 ≤ r x) ∧ (∀ x, r x = 0 ↔ (𝓡∂ n).IsBoundaryPoint x) ∧
      (∀ x, (𝓡∂ n).IsInteriorPoint x → 0 < r x) ∧ (𝓡∂ n).boundary M ⊆ W ∧
      (∀ x, IsCriticalPointAt (𝓡∂ n) r x →
        (𝓡∂ n).IsInteriorPoint x ∧ IsNondegenerateCriticalPointAt (𝓡∂ n) r x) ∧
      {x : M | IsCriticalPointAt (𝓡∂ n) r x}.Finite ∧
      ∃ V : (y : M) → TangentSpace (𝓡∂ n) y,
        ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞ (fun y => (⟨y,V y⟩ : TangentBundle (𝓡∂ n) M)) ∧
        IsCompact (tsupport V) ∧
        (∀ y ∈ W, (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) r y) (V y) = (1 : ℝ)) ∧
        ∀ y : BoundaryManifold (𝓡∂ n) M,
          0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (V y) := by
  have hB : IsCompact ((𝓡∂ n).boundary M) := ((𝓡∂ n).isClosed_boundary (n := ∞) (by simp)).isCompact
  obtain ⟨f,O,hf,hfn,hfzero,hfpos,hBO,V,hV,hVc,hunit,hVpos⟩ := Poincare.Manifold.Boundary.exists_global_boundary_definingFunction hB
  have hKI : (O : Set M)ᶜ ⊆ (𝓡∂ n).interior M := by
    intro x hx
    exact ((𝓡∂ n).isInteriorPoint_iff_not_isBoundaryPoint x).mpr (fun hb => hx (hBO hb))
  have hcrit : ∀ x, IsCriticalPointAt (𝓡∂ n) f x → x ∈ (O : Set M)ᶜ := by
    intro x hc hx
    have hh := hunit x hx
    have hzero : mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x = 0 := hc
    rw [hzero] at hh
    change (0 : ℝ) = 1 at hh
    exact zero_ne_one hh
  obtain ⟨r,hr,⟨N,hN,hBN,heq⟩,hrpos,hrnd,hrfinite⟩ :=
    exists_positive_relative_morse hf O.isOpen.isClosed_compl.isCompact
      ((𝓡∂ n).isOpen_interior (n := ∞) (by simp)) hKI (fun _ hx => hx) hcrit
      (Subset.refl _) hfpos
  have hBN' : (𝓡∂ n).boundary M ⊆ N := by
    simpa only [ModelWithCorners.compl_interior] using hBN
  have hrzero : ∀ x, r x = 0 ↔ (𝓡∂ n).IsBoundaryPoint x := by
    intro x
    constructor
    · intro hx
      by_contra hb
      have hp := hrpos x (((𝓡∂ n).isInteriorPoint_iff_not_isBoundaryPoint x).mpr hb)
      exact (ne_of_gt hp) hx
    · intro hb
      exact (heq (hBN' hb)).trans ((hfzero x).mpr hb)
  have hrn : ∀ x, 0 ≤ r x := by
    intro x
    rcases (𝓡∂ n).isInteriorPoint_or_isBoundaryPoint x with hi | hb
    · exact (hrpos x hi).le
    · exact le_of_eq ((hrzero x).mpr hb).symm
  let W : TopologicalSpace.Opens M := ⟨(O : Set M) ∩ N,O.isOpen.inter hN⟩
  refine ⟨r,W,hr,hrn,hrzero,hrpos,(fun x hx => ⟨hBO hx,hBN' hx⟩),hrnd,hrfinite,V,hV,hVc,?_,hVpos⟩
  intro y hy
  have hlocal : r =ᶠ[𝓝 y] f := by
    filter_upwards [hN.mem_nhds hy.2] with z hz
    exact heq hz
  have hd : mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) r y = mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y := hlocal.mfderiv_eq
  exact (congrArg (fun L : TangentSpace (𝓡∂ n) y →L[ℝ] ℝ => L (V y)) hd).trans (hunit y hy.1)

end Poincare.Morse
