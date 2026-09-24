import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Components

noncomputable section

open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable (J : Set ℝ)

theorem iterCovComp_joint_contMDiffOn {Idx : Type*} [Fintype Idx]
    {r : ℕ} (u : Set M) (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% (frame i)) u)
    (chr : ℝ → M → Idx → Idx → Idx → ℝ)
    (base : ℝ → M → (Fin r → Idx) → ℝ)
    (hchr : ∀ i j k, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chr p.1 p.2 i j k) (J ×ˢ u))
    (hbase : ∀ n, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => base p.1 p.2 n) (J ×ˢ u)) :
    ∀ a, ∀ n : Fin (r + a) → Idx,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => iterCovComp (I := I) frame (chr p.1) (base p.1) a p.2 n) (J ×ˢ u) := by
  classical
  intro a
  induction a with
  | zero => exact hbase
  | succ a ih =>
    intro n
    have hd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => mvfderiv (I := I)
          (fun y => iterCovComp (I := I) frame (chr p.1) (base p.1) a y (Fin.tail n))
          p.2 (frame (n 0) p.2)) (J ×ˢ u) := by
      intro p hp
      exact prodExtDeriv_joint hu hp.1 hp.2 (ih (Fin.tail n) p hp)
        ((hframe (n 0)).contMDiffAt (hu.mem_nhds hp.2))
    have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => ∑ s : Fin (r + a), ∑ j : Idx,
          chr p.1 p.2 (n 0) (Fin.tail n s) j *
            iterCovComp (I := I) frame (chr p.1) (base p.1) a p.2
              (Function.update (Fin.tail n) s j)) (J ×ˢ u) := by
      intro p hp
      exact ContMDiffWithinAt.sum fun s _ => ContMDiffWithinAt.sum fun j _ =>
        (hchr (n 0) (Fin.tail n s) j p hp).mul (ih (Function.update (Fin.tail n) s j) p hp)
    simpa only [iterCovComp_succ, covDerivStepComp, frameDirectionalDerivatives] using hd.sub hs

end DifferentialGeometry.PDE.RicciFlow
