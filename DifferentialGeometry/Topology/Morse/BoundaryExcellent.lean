import DifferentialGeometry.Topology.Morse.BoundaryMorse
import DifferentialGeometry.Topology.Morse.Excellent

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace DifferentialGeometry.Morse
variable {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [T2Space M] [CompactSpace M]


theorem exists_excellent_morse_boundary_definingFunction :
    ∃ (r : M → ℝ) (W : TopologicalSpace.Opens M), ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ r ∧
      (∀ x, 0 ≤ r x) ∧ (∀ x, r x = 0 ↔ (𝓡∂ n).IsBoundaryPoint x) ∧
      (∀ x, (𝓡∂ n).IsInteriorPoint x → 0 < r x) ∧ (𝓡∂ n).boundary M ⊆ W ∧
      (∀ x, IsCriticalPointAt (𝓡∂ n) r x →
        (𝓡∂ n).IsInteriorPoint x ∧ IsNondegenerateCriticalPointAt (𝓡∂ n) r x) ∧
      {x : M | IsCriticalPointAt (𝓡∂ n) r x}.Finite ∧
      InjOn r {x | IsCriticalPointAt (𝓡∂ n) r x} ∧
      ∃ V : (y : M) → TangentSpace (𝓡∂ n) y,
        ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞ (fun y => (⟨y,V y⟩ : TangentBundle (𝓡∂ n) M)) ∧
        IsCompact (tsupport V) ∧
        (∀ y ∈ W, (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) r y) (V y) = (1 : ℝ)) ∧
        ∀ y : BoundaryManifold (𝓡∂ n) M,
          0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (V y) := by
  obtain ⟨f,O,hf,_,hfzero,hfpos,hBO,hfnd,hfcrit,V,hV,hVc,hunit,hVpos⟩ :=
    exists_morse_boundary_definingFunction (M := M) (n := n)
  obtain ⟨r,hr,⟨N,hN,hBN,heq⟩,hrpos,hrcrit,hrinj,hrnd,_⟩ :=
    exists_positive_relative_excellent_morse hf hfcrit (fun x hx => (hfnd x hx).2)
      ((𝓡∂ n).isOpen_interior (n := ∞) (by simp)) (fun x hx => (hfnd x hx).1)
      (fun _ hx => hx) (Subset.refl _) hfpos
  have hrfinite : {x : M | IsCriticalPointAt (𝓡∂ n) r x}.Finite := hrcrit.symm ▸ hfcrit
  have hrnd' : ∀ x, IsCriticalPointAt (𝓡∂ n) r x →
      (𝓡∂ n).IsInteriorPoint x ∧ IsNondegenerateCriticalPointAt (𝓡∂ n) r x := by
    intro x hx
    exact ⟨(hfnd x ((Set.ext_iff.mp hrcrit x).mp hx)).1,hrnd x hx⟩
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
  refine ⟨r,W,hr,hrn,hrzero,hrpos,(fun x hx => ⟨hBO hx,hBN' hx⟩),hrnd',hrfinite,hrinj,V,hV,hVc,?_,hVpos⟩
  intro y hy
  have hlocal : r =ᶠ[𝓝 y] f := by
    filter_upwards [hN.mem_nhds hy.2] with z hz
    exact heq hz
  have hd : mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) r y = mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y := hlocal.mfderiv_eq
  exact (congrArg (fun L : TangentSpace (𝓡∂ n) y →L[ℝ] ℝ => L (V y)) hd).trans (hunit y hy.1)

end DifferentialGeometry.Morse
