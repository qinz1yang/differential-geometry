import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalCoreLimits
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedRestart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureControl

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1

theorem standard_uniform_closed_restart_extension :
    ∃ α : ℝ, 0 < α ∧ ∃ τ : ℝ, 0 < τ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ S : PartialStandardSolution, ∀ T : ℝ, 0 < T → T ≤ α →
        S.lifetime = ENNReal.ofReal T →
        ∃ G H : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
        ∃ Q : PartialStandardSolution,
          (∀ t ∈ Ico 0 T, G t = S.metric t) ∧ H 0 = G T ∧
          Q.metric = gluedFamily G H T ∧
          Q.lifetime = ENNReal.ofReal (T + τ) ∧ S.IsExtendedBy Q ∧
          S.lifetime < Q.lifetime ∧
          (∀ t ∈ Icc 0 (T + τ), RiemannianMetricComplete (Q.metric t)) ∧
          ∀ t ∈ Icc 0 (T + τ), ∀ x : E3,
            Real.sqrt (normSq0S (Q.metric t) x 4 (metricRm04 (Q.metric t) x)) ≤ K := by
  obtain ⟨α, hα, Λ, hΛ, C, L, D, A, hC, hL, hD, hA, ell, hell,
    τ, hτ, B, hB, ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, hfamily⟩ :=
      standard_uniform_terminal_core_limits
  obtain ⟨β, hβ, KG, hKG, hcurv⟩ := standard_uniform_initial_curvature_control
  refine ⟨min α β, lt_min hα hβ, τ, hτ, max 0 (max KG (567 * B 0)),
    le_max_left _ _, ?_⟩
  intro S T hT hTα htime
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed,
    htrunc, hjets, hflows, hlimits⟩ :=
      hfamily S T hT (hTα.trans (min_le_left _ _)) htime.symm.le
  let north : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨Z, hZ, hZfields, bf, co, hbound, hcovTail, hinit, hcomplete,
    hjlim, hglim, hplim, hllim, hRm⟩ := hlimits north
  have hleft : ∀ t ∈ Ico 0 T, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ KG := by
    intro t ht x
    have htl : ENNReal.ofReal t < S.lifetime := by
      rw [htime]
      exact (ENNReal.ofReal_lt_ofReal_iff hT).mpr ht.2
    exact hcurv S t ht.1 (ht.2.le.trans (hTα.trans (min_le_right _ _))) htl
      t ⟨ht.1, le_rfl⟩ x
  obtain ⟨Q, hQtime, hQmetric, hExt, hstrict, hQcomp, hQcurv⟩ :=
    S.exists_strict_extension_of_closed_restart T τ hT hτ htime G co.gInf
      hEq hzero hc hj hpde (hclosed T ⟨hT.le, le_rfl⟩)
      hinit hcomplete hjlim hplim KG (567 * B 0) hleft hRm
  exact ⟨G, co.gInf, Q, hEq, hinit, hQmetric, hQtime, hExt, hstrict, hQcomp, hQcurv⟩
end DifferentialGeometry.PDE.RicciFlow
