import DifferentialGeometry.Topology.Morse.BoundaryMorse
import DifferentialGeometry.Topology.Morse.Affine
import DifferentialGeometry.Topology.Manifold.Boundary.RegularBand

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


theorem exists_relative_morse_sublevel_thresholds (b : ℝ) :
    ∃ (f : M → ℝ) (a c₀ : ℝ) (W : TopologicalSpace.Opens M),
      ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f ∧ a < c₀ ∧ c₀ < b ∧
      (∀ x, a < f x ∧ f x ≤ b) ∧ f ⁻¹' Iic a = ∅ ∧ f ⁻¹' {b} = (𝓡∂ n).boundary M ∧
      (𝓡∂ n).boundary M ⊆ W ∧ f ⁻¹' Icc c₀ b ⊆ W ∧
      (∀ x, IsCriticalPointAt (𝓡∂ n) f x →
        (𝓡∂ n).IsInteriorPoint x ∧ IsNondegenerateCriticalPointAt (𝓡∂ n) f x ∧ f x < c₀) ∧
      (∀ x, f x = c₀ → ¬ IsCriticalPointAt (𝓡∂ n) f x) ∧
      {x : M | IsCriticalPointAt (𝓡∂ n) f x}.Finite ∧
      ∃ V : (y : M) → TangentSpace (𝓡∂ n) y,
        ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞ (fun y => (⟨y,V y⟩ : TangentBundle (𝓡∂ n) M)) ∧
        IsCompact (tsupport V) ∧
        (∀ y ∈ W, (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y) (V y) = (-1 : ℝ)) ∧
        ∀ y : BoundaryManifold (𝓡∂ n) M,
          0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (V y) := by
  obtain ⟨r,W,hr,hrn,hrzero,hrpos,hBW,hrnd,hrfinite,V,hV,hVc,hunit,hVpos⟩ :=
    exists_morse_boundary_definingFunction (M := M) (n := n)
  let f : M → ℝ := fun x => b - r x
  have hf : ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_const.sub hr
  obtain ⟨δ,hδ,hsmall,hcritical,_⟩ := Poincare.Manifold.Boundary.exists_regular_boundary_band
    hr.continuous hrpos W.isOpen hBW hunit
  let c₀ : ℝ := b - δ
  have hc₀ : c₀ < b := by dsimp [c₀]; linarith
  obtain ⟨A,hA⟩ := (isCompact_range hf.continuous).bddBelow
  let a : ℝ := min (A - 1) (c₀ - 1)
  have ha : a < c₀ := lt_of_le_of_lt (min_le_right _ _) (sub_one_lt _)
  have hax : ∀ x, a < f x := fun x =>
    lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le (sub_one_lt _) (hA (mem_range_self x)))
  have hfb : ∀ x, f x ≤ b := fun x => sub_le_self b (hrn x)
  have hcrit : ∀ x, IsCriticalPointAt (𝓡∂ n) f x → IsCriticalPointAt (𝓡∂ n) r x :=
    fun x hx => (isCriticalPointAt_const_sub_iff (hr.mdifferentiableAt (by simp)) b).mp hx
  have hcritlt : ∀ x, IsCriticalPointAt (𝓡∂ n) f x → f x < c₀ := by
    intro x hx
    have hd := hcritical x (hcrit x hx)
    dsimp [f,c₀]
    linarith
  have hband : f ⁻¹' Icc c₀ b ⊆ W := by
    intro x hx
    apply hsmall
    change r x ≤ δ
    have hh := hx.1
    dsimp [f,c₀] at hh
    linarith
  have hlevel : f ⁻¹' {b} = (𝓡∂ n).boundary M := by
    ext x
    change (b - r x ∈ ({b} : Set ℝ)) ↔ (𝓡∂ n).IsBoundaryPoint x
    rw [mem_singleton_iff,← hrzero x]
    constructor <;> intro h <;> linarith
  have hfinite : {x : M | IsCriticalPointAt (𝓡∂ n) f x}.Finite :=
    hrfinite.subset (fun x hx => hcrit x hx)
  refine ⟨f,a,c₀,W,hf,ha,hc₀,(fun x => ⟨hax x,hfb x⟩),?_,hlevel,hBW,hband,?_,?_,hfinite,V,hV,hVc,?_,hVpos⟩
  · exact eq_empty_iff_forall_notMem.mpr (fun x hx => not_le_of_gt (hax x) hx)
  · intro x hx
    have hh := hrnd x (hcrit x hx)
    exact ⟨hh.1,(isNondegenerateCriticalPointAt_const_sub_iff hr hh.1 b).mpr hh.2,hcritlt x hx⟩
  · intro x hx hc
    exact (ne_of_lt (hcritlt x hc)) hx
  · intro y hy
    have hd := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L (V y))
      (Poincare.Manifold.mfderiv_const_sub_real (x := y) (hr.mdifferentiableAt (by simp)) b)
    change (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y) (V y) = -(mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) r y) (V y) at hd
    exact hd.trans (congrArg Neg.neg (hunit y hy))

end Poincare.Morse
