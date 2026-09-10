import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Conormal
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Operator
namespace Poincare.VectorField

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

theorem gradientFun_eq_zero_iff_mfderiv_eq_zero
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradientFun g f x = 0 ↔ mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
  constructor
  · intro h
    ext v
    have hh := inner_gradientFun g f x v
    rw [h, map_zero, zero_apply] at hh
    exact hh.symm
  · exact gradientFun_eq_zero_of_mfderiv_eq_zero g f

end Poincare.VectorField

namespace Poincare.VectorField
variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

theorem proj_gradientFun_neg_of_nonpos
    (g : DifferentialGeometry.SmoothRiemannianMetric (𝓡∂ n) M)
    {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f x)
    (hx : (𝓡∂ n).IsBoundaryPoint x) (hf0 : f x = 0)
    (hneg : ∀ᶠ y in 𝓝 x, f y ≤ 0)
    (hreg : mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x ≠ 0) :
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (gradientFun g f x) < 0 := by
  have hnegreg : mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) (-f) x ≠ 0 := by
    rw [mfderiv_neg]
    exact neg_ne_zero.mpr hreg
  obtain ⟨c,hc,he⟩ := Poincare.Manifold.BoundaryCollar.mfderiv_eq_pos_smul_proj_of_nonneg
    hf.neg hx (by simp [hf0]) (hneg.mono fun _ hy => neg_nonneg.mpr hy) hnegreg
  rw [mfderiv_neg] at he
  have hV : gradientFun g f x ≠ 0 :=
    mt (gradientFun_eq_zero_iff_mfderiv_eq_zero g f x).mp hreg
  have hpos := g.pos x (gradientFun g f x) hV
  have heval := congrArg (fun L : TangentSpace (𝓡∂ n) x →L[ℝ] ℝ =>
    L (gradientFun g f x)) he
  change -(show ℝ from mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x (gradientFun g f x)) =
    c * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (gradientFun g f x) at heval
  have hinner := inner_gradientFun g f x (gradientFun g f x)
  change g.inner x (gradientFun g f x) (gradientFun g f x) =
    mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x (gradientFun g f x) at hinner
  have hmul : c * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (gradientFun g f x) < 0 := by
    rw [← heval]
    exact neg_neg_of_pos (hinner ▸ hpos)
  exact neg_of_mul_neg_right hmul hc.le

end Poincare.VectorField
