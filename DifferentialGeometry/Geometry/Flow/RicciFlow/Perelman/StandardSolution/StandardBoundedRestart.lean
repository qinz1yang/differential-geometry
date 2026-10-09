import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CapReferenceRestart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardBoundedTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedRestart

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1

theorem standard_closed_restart_extension_of_curvature_bound
    (T K : ℝ) (hT : 0 < T) (hK : 0 ≤ K) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ KR : ℝ, 0 ≤ KR ∧
      ∀ S : PartialStandardSolution, S.lifetime = ENNReal.ofReal T →
        (∀ t ∈ Ico 0 T, ∀ x : E3,
          Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K) →
        ∃ G H : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
        ∃ Q : PartialStandardSolution,
          (∀ t ∈ Ico 0 T, G t = S.metric t) ∧ H 0 = G T ∧
          Q.metric = gluedFamily G H T ∧
          Q.lifetime = ENNReal.ofReal (T + τ) ∧ S.IsExtendedBy Q ∧
          S.lifetime < Q.lifetime ∧
          (∀ t ∈ Icc 0 (T + τ), RiemannianMetricComplete (Q.metric t)) ∧
          ∀ t ∈ Icc 0 (T + τ), ∀ x : E3,
            Real.sqrt (normSq0S (Q.metric t) x 4 (metricRm04 (Q.metric t) x)) ≤ KR := by
  obtain ⟨Λ, hΛ, C, L, hC, hL, hfamily⟩ :=
    standard_smooth_terminal_families_of_curvature_bound T K hT hK
  let D : ℕ → ℝ := fun k => L k * T
  have hD (k : ℕ) : 0 ≤ D k := mul_nonneg (hL k) hT.le
  have hell : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  obtain ⟨τ, hτ, B, hB, ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, hrestart⟩ :=
    exists_uniform_complete_cap_reference_core_restarts Λ⁻¹ hell D hD
  refine ⟨τ, hτ, max 0 (max K (567 * B 0)), le_max_left _ _, ?_⟩
  intro S htime hRm
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed⟩ :=
    hfamily S htime.symm.le hRm
  have hlow (x : E3) (v : TangentSpace (𝓡 3) x) :
      Λ⁻¹ * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤ (G T).inner x v v :=
    ((he T ⟨hT.le, le_rfl⟩).2 x (mem_univ x) v).1
  have hdiff (k : ℕ) (x : E3) :
      DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm k (G T)
        DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ D k := by
    have hh := hLip k T ⟨hT.le, le_rfl⟩ 0 ⟨le_rfl, hT.le⟩ x
    simpa only [D, hzero, sub_zero, abs_of_nonneg hT.le] using hh
  let north : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨Z, hZ, hZfields, bf, co, hbound, hcovTail, hinit, hcomplete,
    hjlim, hglim, hplim, hllim, hcurv⟩ := hrestart (G T) hlow hdiff north
  obtain ⟨Q, hQtime, hQmetric, hExt, hstrict, hQcomp, hQcurv⟩ :=
    S.exists_strict_extension_of_closed_restart T τ hT hτ htime G co.gInf
      hEq hzero hc hj hpde (hclosed T ⟨hT.le, le_rfl⟩)
      hinit hcomplete hjlim hplim K (567 * B 0) hRm hcurv
  exact ⟨G, co.gInf, Q, hEq, hinit, hQmetric, hQtime, hExt, hstrict, hQcomp, hQcurv⟩
end DifferentialGeometry.PDE.RicciFlow
