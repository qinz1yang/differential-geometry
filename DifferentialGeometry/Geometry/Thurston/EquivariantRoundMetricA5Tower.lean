import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Shi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace

/-!
# The curvature-derivative input of the a5 Bernstein towers

Chapter 7, surface lemma U1, route (a), step a5 (lane U1E2), interface between a5.1 and the
potential-gauge design D18 (`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`,
§3 (iii) and (viii)).

* `surfaceFlow_shi_iterCov_bound`: the hypothesis `hshi` of D18 (iii) and (viii), verbatim with
  `flowExtinctionTime S = A₀ / C₀` unfolded: on every terminal interval `[t₀, T)`,
  `|∇^q Rm|² ≤ B (T* - t)^(-(2 + q))` for the iterated Levi-Civita derivatives `iterCov` of
  `metricRm04`. It is the a5.1 bound `surfaceFlow_normalized_curvatureDerivative_bound` rewritten
  through `nablaKRm_eq_iterCov`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]

theorem surfaceFlow_shi_iterCov_bound (hdim : Module.finrank ℝ E = 2) {T : ℝ} {hT : 0 < T}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) :
    ∀ t₀ ∈ Ioo 0 T, ∀ q : ℕ, ∃ B : ℝ, ∀ t ∈ Ico t₀ T, ∀ x,
      normSq0S (S.family.metric t) x (4 + q)
          (iterCov (S.family.metric t) 4 (metricRm04 (S.family.metric t)) q x) ≤
        B * (surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0) - t) ^
          (-(2 + q : ℝ)) := by
  intro t₀ ht₀ q
  obtain ⟨C, hC⟩ := surfaceFlow_normalized_curvatureDerivative_bound hdim hT S hS hscal ht₀.1 q
  set Tst := surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0)
  have hTT : T ≤ Tst := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  refine ⟨max C 0 / 2 ^ (q + 2), fun t ht x => ?_⟩
  have hd : 0 < Tst - t := by linarith [ht.2]
  have hN : normSq0S (S.family.metric t) x (4 + q)
      (iterCov (S.family.metric t) 4 (metricRm04 (S.family.metric t)) q x) =
      nablaKRm04NormSqIntrinsic S q t x := by
    rw [nablaKRm04NormSqIntrinsic, nablaKRm_eq_iterCov]
    rfl
  rw [hN]
  have hpos : 0 < (2 * (Tst - t)) ^ (q + 2) := by positivity
  have hN' : nablaKRm04NormSqIntrinsic S q t x ≤ max C 0 / (2 * (Tst - t)) ^ (q + 2) := by
    rw [le_div_iff₀ hpos, mul_comm]
    exact (hC t ht x).trans (le_max_left _ _)
  have hexp : (Tst - t) ^ (-(2 + q : ℝ)) = ((Tst - t) ^ (q + 2))⁻¹ := by
    rw [Real.rpow_neg hd.le, show (2 + q : ℝ) = ((q + 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hexp]
  calc nablaKRm04NormSqIntrinsic S q t x ≤ max C 0 / (2 * (Tst - t)) ^ (q + 2) := hN'
    _ = max C 0 / 2 ^ (q + 2) * ((Tst - t) ^ (q + 2))⁻¹ := by
      rw [mul_pow]
      field_simp

end GC.Geometry
