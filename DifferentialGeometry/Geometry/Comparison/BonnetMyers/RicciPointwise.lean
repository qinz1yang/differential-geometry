import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound

open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciLowerAt_of_rm
    (g : SmoothRiemannianMetric I M) {x : M} {Rm : ℝ}
    (hRm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
        (metricRm04At (I := I) (M := M) g x)) ≤ Rm)
    (v : TangentSpace I x) :
    -((Module.finrank ℝ E : ℝ) ^ 2 * Rm) * g.inner x v v ≤
      ricciTensor (I := I) g x v v := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H x
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E :=
    ((trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x hxbase).finrank_eq
  let A : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
    (metricRm04At (I := I) (M := M) g x))
  have hcomp : ∀ i j,
      |metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j))| ≤
        (Module.finrank ℝ E : ℝ) * A := by
    intro i j
    calc
      |metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j))| ≤
          (Module.finrank ℝ (TangentSpace I x) : ℝ) * A := by
        simpa [A] using metricRicciComp_le (I := I) g basis hON i j
      _ = (Module.finrank ℝ E : ℝ) * A := by rw [hrank]
  have hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 →
      |metricRicciAt (I := I) (M := M) g x (vec2 (I := I) u u)| ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * A := by
    intro u hu
    have h := ricci_unitSphere_le_of_componentBound
      (I := I) g (metricRicciAt (I := I) (M := M) g x) basis hON
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hcomp u hu
    calc
      |metricRicciAt (I := I) (M := M) g x (vec2 (I := I) u u)| ≤
          (Module.finrank ℝ (TangentSpace I x) : ℝ) *
            ((Module.finrank ℝ E : ℝ) * A) := by
        simpa [A, mul_assoc] using h
      _ = (Module.finrank ℝ E : ℝ) ^ 2 * A := by
        rw [hrank]
        ring
  have hquad := tensor02_quadForm_abs_le_of_unit_bound
    (I := I) g (metricRicciAt (I := I) (M := M) g x) hunit v
  rw [metricRicciAt_apply_eq_ricciTensor (I := I) g x v v] at hquad
  have hinner : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · subst v
      simp
    · exact (g.pos x v hv).le
  have hcoef :
      (Module.finrank ℝ E : ℝ) ^ 2 * A ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Rm :=
    mul_le_mul_of_nonneg_left hRm (sq_nonneg _)
  have habs : |ricciTensor (I := I) g x v v| ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * Rm) * g.inner x v v :=
    hquad.trans (mul_le_mul_of_nonneg_right hcoef hinner)
  simpa only [neg_mul] using (abs_le.mp habs).1

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
