import DifferentialGeometry.Geometry.Comparison.BonnetMyers.LengthBound
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Curvature.SectionalCone

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Riemannian.BonnetMyers

open Bundle
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem ricci_nonneg_of_sec
    (g : SmoothRiemannianMetric I M) (x : M)
    (hsec : metricRm04At (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (v : TangentSpace I x) :
    0 ≤ ricciTensor (I := I) g x v v := by
  by_cases hv : v = 0
  · subst v
    simp
  let : Nontrivial E := ⟨⟨v, 0, hv⟩⟩
  let : NeZero (Module.finrank ℝ E) :=
    ⟨(Module.finrank_pos (R := ℝ) (M := E)).ne'⟩
  have hvpos : 0 < g.inner x v v := g.pos x v hv
  obtain ⟨e, hON, hperp⟩ := exists_perp_pos (I := I) g x v hvpos
  rw [← ricci_eq_sum_perp (I := I) g x v hvpos e hON hperp]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  have hcurv :=
    (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (M := M) g x).mp hsec (e i) v
  calc
    0 ≤ metricRm04StdAt (I := I) (M := M) g x (e i) v v (e i) := hcurv
    _ = g.inner x (e i)
        (riemannOp (LeviCivita (I := I) g) x (e i) v v) :=
      rm04_eq_inner_riem (I := I) (M := M) g x (e i) v v (e i)
    _ = g.inner x
        (riemannOp (LeviCivita (I := I) g) x (e i) v v) (e i) :=
      g.symm x (e i) _

omit [SigmaCompactSpace M] in
theorem ricci_pos_of_sec
    (g : SmoothRiemannianMetric I M) (x : M)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hsec : ∀ a b : TangentSpace I x,
      a ≠ 0 → b ≠ 0 → g.inner x a b = 0 →
        0 < metricRm04StdAt (I := I) (M := M) g x a b b a)
    {v : TangentSpace I x} (hv : v ≠ 0) :
    0 < ricciTensor (I := I) g x v v := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hvpos : 0 < g.inner x v v := g.pos x v hv
  obtain ⟨e, hON, hperp⟩ := exists_perp_pos (I := I) g x v hvpos
  calc
    0 < ∑ i : Fin (Module.finrank ℝ E - 1),
        g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v v) (e i) := by
      refine Finset.sum_pos (fun i _ ↦ ?_) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
      have hei : e i ≠ 0 := by
        intro hei
        have hii := hON i i
        simp [hei] at hii
      calc
        0 < metricRm04StdAt (I := I) (M := M) g x (e i) v v (e i) :=
          hsec (e i) v hei hv (hperp i)
        _ = g.inner x (e i)
            (riemannOp (LeviCivita (I := I) g) x (e i) v v) :=
          rm04_eq_inner_riem (I := I) (M := M) g x (e i) v v (e i)
        _ = g.inner x
            (riemannOp (LeviCivita (I := I) g) x (e i) v v) (e i) :=
          g.symm x (e i) _
    _ = ricciTensor (I := I) g x v v :=
      ricci_eq_sum_perp (I := I) g x v hvpos e hON hperp

omit [SigmaCompactSpace M] in
theorem ricciLower_of_sec
    (g : SmoothRiemannianMetric I M)
    (hsec : ∀ x : M, metricRm04At (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    RicciBoundedBelow (I := I) g 0 := by
  intro x v
  simpa only [zero_mul] using
    ricci_nonneg_of_sec (I := I) (M := M) g x (hsec x) v

end DifferentialGeometry.Geometry.Riemannian.BonnetMyers

end
