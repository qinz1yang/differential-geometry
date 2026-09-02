import DifferentialGeometry.Topology.Morse.Riemannian
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIdentities

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Topology.Morse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_isNondegenerateCriticalPointAt_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hcrit : IsCriticalPointAt I f x) :
    IsNondegenerateCriticalPointAt I f x := by
  apply isNondegenerateCriticalPointAt_of_hessFun_eq_smul_metric
    (c := (1 - metricScalarAt (I := I) (M := M) g x) / 2) g f x hcrit
  · intro hzero
    apply hnonconstant
    have hscalarx : metricScalarAt (I := I) (M := M) g x = 1 := by
      linarith
    have hgradx : gradFun (I := I) g f x = 0 :=
      gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g f hcrit
    have hpotentialx := normalizedGradientRicciSoliton_potential_equation (I := I) h x
    have hfx : f x = 1 := by
      rw [hgradx] at hpotentialx
      simpa [hscalarx] using hpotentialx.symm
    obtain ⟨a, ha⟩ :=
      normalizedGradientRicciSoliton_exists_scalar_eq_const_mul_exp_of_finrank_eq_two
        (I := I) h hdim
    have hax := ha x
    rw [hscalarx, hfx] at hax
    have haeq : a = Real.exp (-1) := by
      calc
        a = 1 / Real.exp 1 := (eq_div_iff (Real.exp_ne_zero 1)).2 hax.symm
        _ = Real.exp (-1) := by
          simpa [div_eq_mul_inv] using (Real.exp_neg (1 : Real)).symm
    have hfOne : ∀ y : M, f y = 1 := by
      intro y
      have hscalarY : metricScalarAt (I := I) (M := M) g y =
          Real.exp (f y - 1) := by
        rw [ha y, haeq, ← Real.exp_add]
        congr 1
        ring
      have hpotentialY := normalizedGradientRicciSoliton_potential_equation (I := I) h y
      have hinnerNonneg : 0 ≤
          g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g f y) := by
        simpa only [normGradSqFun_def] using
          normGradSqFun_nonneg (I := I) g (f : M → Real) y
      have hexp_le : Real.exp (f y - 1) ≤ f y := by
        rw [hscalarY] at hpotentialY
        linarith
      by_contra hfy
      have hsub : f y - 1 ≠ 0 := sub_ne_zero.mpr hfy
      have hstrict := Real.add_one_lt_exp hsub
      have : f y < Real.exp (f y - 1) := by
        simpa using hstrict
      exact (not_lt_of_ge hexp_le) this
    intro y z
    rw [hfOne y, hfOne z]
  · intro v w
    exact normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
      (I := I) h hdim x v w

end DifferentialGeometry.Geometry
