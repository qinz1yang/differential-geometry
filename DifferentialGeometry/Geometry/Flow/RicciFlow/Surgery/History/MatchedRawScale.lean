import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRawScale

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology

namespace GC.GeneralFlow
universe u

/-- One threshold for all late queries of a fixed history family and its records. -/
private theorem eventually_matched_raw_scale_on_history_family
    (histories : ℕ → ObservedHistory.{u}) (q : CutoffParameters)
    (records : ∀ n, ∀ i : Fin (histories n).eventCount,
      GeometricCutoffRecord (histories n) i q)
    (hdecay : Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ)))
    (hrecent : ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ n : ℕ,
      ∀ i : Fin (histories n).eventCount,
        (histories n).time i.succ ∈ Icc (t / 2) t →
        ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t) :
    ∀ C : ℝ, 1 ≤ C → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ t : ℝ, T₀ ≤ t → ∀ n : ℕ,
      ∀ i : Fin (histories n).eventCount,
        (histories n).time i.succ ∈ Icc (t / 2) t →
      ∀ {fixed : StaticCapScaffold} {Dbig ζ : ℝ} {m : ℕ}
        {b : ((histories n).event i).RetainedBoundaryIndex}
        (raw : ((histories n).event i).PresentedStaticCap fixed Dbig m ζ b),
        raw.neck.scale = ((records n i).static b).neck.scale →
      ∀ Q : ℝ, 0 < Q → Q ≤ (q.neckRadius t ^ 2)⁻¹ →
        18 * C * Q < raw.neck.scale := by
  intro C hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hbeta : 0 < 1 / Real.sqrt (72 * C) := by positivity
  obtain ⟨Tβ, hTβ, hrecentβ⟩ := hrecent (1 / Real.sqrt (72 * C)) hbeta
  have hc : 0 < q.recenterConstant :=
    lt_of_lt_of_le (by norm_num) q.recenterConstant_ge_four
  have hτ : 0 < 1 / (2 * q.recenterConstant) := by positivity
  have hsmall : ∀ᶠ u in Filter.atTop, q.delta u < 1 / (2 * q.recenterConstant) :=
    hdecay.eventually (eventually_lt_nhds hτ)
  obtain ⟨Tδ, hTδ⟩ := Filter.eventually_atTop.mp hsmall
  let T₀ : ℝ := max Tβ (max 1 (2 * max Tδ 0))
  have hT₀ : 0 < T₀ := lt_of_lt_of_le hTβ (le_max_left _ _)
  refine ⟨T₀, hT₀, ?_⟩
  intro t ht n i hi fixed Dbig ζ m b raw hmatch Q hQ hceiling
  have hβt : Tβ ≤ t := (le_max_left _ _).trans ht
  have hδt : 2 * max Tδ 0 ≤ t :=
    (le_max_right 1 _).trans ((le_max_right Tβ _).trans ht)
  have hδbirth : Tδ ≤ (histories n).time i.succ := by
    have hmax : Tδ ≤ max Tδ 0 := le_max_left _ _
    linarith only [hδt, hmax, hi.1]
  have herror : q.recenterConstant * q.delta ((histories n).time i.succ) ≤ 1 / 2 := by
    have hδ := hTδ _ hδbirth
    have hprod := mul_le_mul_of_nonneg_left hδ.le hc.le
    have hnormalize : q.recenterConstant * (1 / (2 * q.recenterConstant)) = 1 / 2 := by
      apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
      calc
        q.recenterConstant * (1 / (2 * q.recenterConstant)) * 2 =
            (2 * q.recenterConstant) * (1 / (2 * q.recenterConstant)) := by ring
        _ = 1 := mul_one_div_cancel (by positivity)
    simpa only [hnormalize] using hprod
  exact (records n i).raw_scale_gt_of_recent_nominal_bound raw hmatch
    C Q (q.neckRadius t) hC hQ
    (q.neckRadius_pos t (hT₀.trans_le ht).le) herror
    (hrecentβ t hβt n i hi) hceiling

end GC.GeneralFlow
