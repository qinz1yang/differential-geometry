import DifferentialGeometry.Integral.Measure.ChartDensity

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Symmetry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Two smooth Riemannian metrics `g, h` on `M` are **conformally
equivalent** iff there exists a smooth function `f : M → ℝ` such that
`h.inner x V W = exp (2 f x) · g.inner x V W` for every point `x` and
every pair of tangent vectors `V, W : T_x M`.

Conformal equivalence preserves angles between tangent vectors (the
inner product factor scales positively and uniformly). It is reflexive
(take `f ≡ 0`), symmetric (take `-f`), and transitive (add the two
scaling functions). -/
def IsConformalTo
    (g h : SmoothRiemannianMetric I M) : Prop :=
  ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
    ∀ (x : M) (V W : TangentSpace I x),
      h.inner x V W = Real.exp (2 * f x) * g.inner x V W

/-- Reflexivity of conformal equivalence: every metric is conformal to
itself via the zero scaling function. -/
theorem IsConformalTo.refl (g : SmoothRiemannianMetric I M) :
    IsConformalTo (I := I) g g := by
  refine ⟨fun _ : M => 0, ?_, ?_⟩
  · exact contMDiff_const
  · intro x V W
    simp [Real.exp_zero]

/-- Symmetry of conformal equivalence: if `g` is conformal to `h` via
`f`, then `h` is conformal to `g` via `-f`. -/
theorem IsConformalTo.symm
    {g h : SmoothRiemannianMetric I M}
    (hgh : IsConformalTo (I := I) g h) :
    IsConformalTo (I := I) h g := by
  obtain ⟨f, hf_smooth, hf_eq⟩ := hgh
  refine ⟨fun x => -f x, ?_, ?_⟩
  · exact hf_smooth.neg
  · intro x V W
    -- g.inner = exp(-2f) · h.inner; multiply h.inner = exp(2f) · g.inner by exp(-2f)
    have hh := hf_eq x V W
    -- hh : h.inner x V W = exp (2 * f x) * g.inner x V W
    -- Goal : g.inner x V W = exp (2 * -f x) * h.inner x V W
    have h2neg : (2 : ℝ) * -f x = -(2 * f x) := by ring
    rw [hh, h2neg, Real.exp_neg]
    -- Now: g.inner x V W = (exp (2 * f x))⁻¹ * (exp (2 * f x) * g.inner x V W)
    have hpos : Real.exp (2 * f x) > 0 := Real.exp_pos _
    field_simp

/-- Transitivity of conformal equivalence: if `g` is conformal to `h`
via `f₁` and `h` is conformal to `k` via `f₂`, then `g` is conformal to
`k` via `f₁ + f₂`. -/
theorem IsConformalTo.trans
    {g h k : SmoothRiemannianMetric I M}
    (hgh : IsConformalTo (I := I) g h)
    (hhk : IsConformalTo (I := I) h k) :
    IsConformalTo (I := I) g k := by
  obtain ⟨f, hf_smooth, hf_eq⟩ := hgh
  obtain ⟨e, he_smooth, he_eq⟩ := hhk
  refine ⟨fun x => f x + e x, ?_, ?_⟩
  · exact hf_smooth.add he_smooth
  · intro x V W
    have h1 := hf_eq x V W
    have h2 := he_eq x V W
    -- h1 : h.inner = exp(2f) · g.inner
    -- h2 : k.inner = exp(2e) · h.inner
    -- Goal : k.inner = exp(2(f+e)) · g.inner
    rw [h2, h1]
    have h_exp : Real.exp (2 * (f x + e x)) =
        Real.exp (2 * e x) * Real.exp (2 * f x) := by
      have : (2 : ℝ) * (f x + e x) = 2 * e x + 2 * f x := by ring
      rw [this, Real.exp_add]
    rw [h_exp]
    ring

end Symmetry
end Riemannian
end Geometry
end DifferentialGeometry

end
