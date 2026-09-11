import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardBoundedRestart
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Data.ENNReal.Inv

set_option autoImplicit false
noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem standard_curvature_unbounded_before_finite_lifetime
    (S : StandardSolution)
    (T : ℝ) (hT : 0 < T)
    (hLifetime : S.val.lifetime = ENNReal.ofReal T)
    (θ : ℝ) (hθ : θ ∈ Ico 0 T) (K : ℝ) :
    ∃ t ∈ Ioo θ T, ∃ x : E3,
      K < Real.sqrt
        (normSq0S (S.val.metric t) x 4
          (metricRm04 (S.val.metric t) x)) := by
  by_contra hno
  have htail :
      ∀ t ∈ Ioo θ T, ∀ x : E3,
        Real.sqrt
          (normSq0S (S.val.metric t) x 4
            (metricRm04 (S.val.metric t) x)) ≤ K := by
    intro t ht x
    exact le_of_not_gt (fun hx => hno ⟨t, ht, x, hx⟩)
  have hθlife : ENNReal.ofReal θ < S.val.lifetime := by
    rw [hLifetime]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hθ.1).mpr hθ.2
  obtain ⟨K₀, hK₀, hprefix⟩ :=
    S.val.curvature_bound θ hθ.1 hθlife
  have hK : 0 ≤ max K₀ K := hK₀.trans (le_max_left K₀ K)
  have hwhole :
      ∀ t ∈ Ico 0 T, ∀ x : E3,
        Real.sqrt
          (normSq0S (S.val.metric t) x 4
            (metricRm04 (S.val.metric t) x)) ≤ max K₀ K := by
    intro t ht x
    by_cases htθ : t ≤ θ
    · exact (hprefix t ⟨ht.1, htθ⟩ x).trans (le_max_left K₀ K)
    · exact (htail t ⟨lt_of_not_ge htθ, ht.2⟩ x).trans
        (le_max_right K₀ K)
  obtain ⟨τ, _, KR, _, hrestart⟩ :=
    standard_closed_restart_extension_of_curvature_bound T (max K₀ K) hT hK
  obtain ⟨_, _, Q, _, _, _, _, hExt, hStrict, _, _⟩ :=
    hrestart S.val hLifetime hwhole
  exact (not_le_of_gt hStrict) (S.property Q hExt).1

theorem standard_curvature_limsup_eq_top
    (S : StandardSolution) (hfinite : S.val.lifetime ≠ ⊤) :
    Filter.limsup
      (fun t : ℝ =>
        ⨆ x : E3,
          ENNReal.ofReal
            (Real.sqrt
              (normSq0S (S.val.metric t) x 4
                (metricRm04 (S.val.metric t) x))))
      (𝓝[<] S.val.lifetime.toReal) = ⊤ := by
  let T : ℝ := S.val.lifetime.toReal
  have hT : 0 < T :=
    ENNReal.toReal_pos S.val.lifetime_pos.ne' hfinite
  have hLifetime : S.val.lifetime = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal hfinite).symm
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  apply Filter.le_limsup_of_frequently_le'
  apply (nhdsLT_basis S.val.lifetime.toReal).frequently_iff.mpr
  intro θ hθ
  have hmax : max (0 : ℝ) θ ∈ Ico 0 T :=
    ⟨le_max_left _ _, max_lt hT hθ⟩
  obtain ⟨t, ht, x, hx⟩ :=
    standard_curvature_unbounded_before_finite_lifetime
      S T hT hLifetime (max 0 θ) hmax (r : ℝ)
  refine ⟨t, ⟨(le_max_right 0 θ).trans_lt ht.1, ht.2⟩, ?_⟩
  have hr :
      (r : ℝ≥0∞) ≤
        ENNReal.ofReal
          (Real.sqrt
            (normSq0S (S.val.metric t) x 4
              (metricRm04 (S.val.metric t) x))) := by
    have hh := ENNReal.ofReal_le_ofReal hx.le
    simpa only [ENNReal.ofReal_coe_nnreal] using hh
  exact hr.trans
    (le_iSup
      (fun y : E3 =>
        ENNReal.ofReal
          (Real.sqrt
            (normSq0S (S.val.metric t) y 4
              (metricRm04 (S.val.metric t) y))))
      x)

end DifferentialGeometry.PDE.RicciFlow
