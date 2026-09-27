import DifferentialGeometry.Analysis.Spectral.HamiltonTraceContractions
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.BlockAlgebra

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators
open DifferentialGeometry.Analysis.Spectral

theorem hamilton_trace_from_block_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ι → ι → ι → Real)
    (P : ι → ι → ι → Real)
    (M : ι → ι → Real)
    (v dR : ι → Real)
    (hBlock : ∀ r, 0 ≤ hamiltonBlockPolarized
      (fun a b c d => R a b d c) P M
      (fun a b => hamiltonTraceWedge v r a b)
      (fun a b => hamiltonTraceWedge v r a b)
      (hamiltonTraceWeight r) (hamiltonTraceWeight r))
    (hPFirst : ∀ a, (∑ c, P c a c) = -(1 / 2 : Real) * dR a)
    (hPSecond : ∀ a, (∑ c, P a c c) = (1 / 2 : Real) * dR a)
    (hRFirst : ∀ a b c d, R a b c d = -R b a c d)
    (hRLast : ∀ a b c d, R a b c d = -R a b d c)
    (hRPair : ∀ a b c d, R a b c d = R c d a b) :
    0 ≤ (∑ a, M a a) + ∑ a, dR a * v a +
      ∑ a, ∑ b, hamiltonRicciContraction R a b * v a * v b := by
  have hsum : 0 ≤ ∑ r, hamiltonBlockPolarized
      (fun a b c d => R a b d c) P M
      (fun a b => hamiltonTraceWedge v r a b)
      (fun a b => hamiltonTraceWedge v r a b)
      (hamiltonTraceWeight r) (hamiltonTraceWeight r) :=
    Finset.sum_nonneg (fun r _ => hBlock r)
  calc
    0 ≤ ∑ r, hamiltonBlockPolarized
      (fun a b c d => R a b d c) P M
      (fun a b => hamiltonTraceWedge v r a b)
      (fun a b => hamiltonTraceWedge v r a b)
      (hamiltonTraceWeight r) (hamiltonTraceWeight r) := hsum
    _ = (∑ r, ∑ a, ∑ b, ∑ c, ∑ d,
        R a b d c * hamiltonTraceWedge v r a b *
          hamiltonTraceWedge v r c d) +
        (∑ r, ∑ a, ∑ b, ∑ c,
          2 * P a b c * hamiltonTraceWedge v r a b *
            hamiltonTraceWeight r c) +
        ∑ r, ∑ a, ∑ b, M a b *
          hamiltonTraceWeight r a * hamiltonTraceWeight r b := by
      simp only [hamiltonBlockPolarized, mul_add, Finset.sum_add_distrib]
      have hdouble (f : ι → ι → ι → ι → Real) :
          (∑ r, ∑ a, ∑ b, ∑ c, f r a b c) +
              ∑ r, ∑ a, ∑ b, ∑ c, f r a b c =
            ∑ r, ∑ a, ∑ b, ∑ c, 2 * f r a b c := by
        calc
          (∑ r, ∑ a, ∑ b, ∑ c, f r a b c) +
                ∑ r, ∑ a, ∑ b, ∑ c, f r a b c =
              ∑ r, ∑ a, ∑ b, ∑ c, (f r a b c + f r a b c) := by
                simp only [Finset.sum_add_distrib]
          _ = ∑ r, ∑ a, ∑ b, ∑ c, 2 * f r a b c := by
                refine Finset.sum_congr rfl fun r _ => ?_
                refine Finset.sum_congr rfl fun a _ => ?_
                refine Finset.sum_congr rfl fun b _ => ?_
                refine Finset.sum_congr rfl fun c _ => ?_
                ring
      simpa [mul_assoc] using hdouble
        (fun r a b c => P a b c * hamiltonTraceWedge v r a b *
          hamiltonTraceWeight r c)
    _ = (∑ a, ∑ b, hamiltonRicciContraction R a b * v a * v b) +
        (∑ a, dR a * v a) + ∑ a, M a a := by
      rw [← DifferentialGeometry.Analysis.Spectral.hamilton_trace_curvature_contraction
        R v hRFirst hRLast hRPair]
      rw [← DifferentialGeometry.Analysis.Spectral.hamilton_trace_P_contraction
        P v dR hPFirst hPSecond]
      rw [← DifferentialGeometry.Analysis.Spectral.hamilton_trace_M_contraction M]
    _ = (∑ a, M a a) + ∑ a, dR a * v a +
        ∑ a, ∑ b, hamiltonRicciContraction R a b * v a * v b := by ring

end DifferentialGeometry.PDE.RicciFlow
