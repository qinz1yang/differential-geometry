import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardInitialExistence

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.exists_strict_extension_of_closed_restart
    (S : PartialStandardSolution)
    (T τ : ℝ) (hT : 0 < T) (hτ : 0 < τ)
    (hlifetime : S.lifetime = ENNReal.ofReal T)
    (G H : ℝ → SmoothRiemannianMetric (𝓡 3) E3)
    (hagree : ∀ t ∈ Ico 0 T, G t = S.metric t)
    (hGinitial : G 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric)
    (hGcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (G t))
    (hGjets :
      ∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
        ContinuousOn
          (fun p : ℝ × E3 =>
            iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
          (Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target))
    (hGright :
      ∀ t ∈ Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
        HasDerivWithinAt (fun s => (G s).inner x v w)
          (-2 * ricciTensor (G t) x v w) (Ici 0) t)
    (hGend :
      ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
        HasDerivWithinAt (fun s => (G s).inner x v w)
          (-2 * ricciTensor (G T) x v w) (Icc 0 T) T)
    (hHzero : H 0 = G T)
    (hHcomplete : ∀ t ∈ Icc 0 τ, RiemannianMetricComplete (H t))
    (hHjets :
      ∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
        ContinuousOn
          (fun p : ℝ × E3 =>
            iteratedFDeriv ℝ r (chartGramOnE (H p.1) x₀ i j) p.2)
          (Icc 0 τ ×ˢ interior (extChartAt (𝓡 3) x₀).target))
    (hHinterior :
      ∀ t ∈ Ioo 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
        HasDerivAt (fun s => (H s).inner x v w)
          (-2 * ricciTensor (H t) x v w) t)
    (KG KH : ℝ)
    (hKG :
      ∀ t ∈ Ico 0 T, ∀ x : E3,
        Real.sqrt (normSq0S (S.metric t) x 4
          (metricRm04 (S.metric t) x)) ≤ KG)
    (hKH :
      ∀ t ∈ Icc 0 τ, ∀ x : E3,
        Real.sqrt (normSq0S (H t) x 4
          (metricRm04 (H t) x)) ≤ KH) :
    ∃ Q : PartialStandardSolution,
      Q.lifetime = ENNReal.ofReal (T + τ) ∧
      Q.metric = gluedFamily G H T ∧
      S.IsExtendedBy Q ∧
      S.lifetime < Q.lifetime ∧
      (∀ t ∈ Icc 0 (T + τ),
        RiemannianMetricComplete (Q.metric t)) ∧
      ∀ t ∈ Icc 0 (T + τ), ∀ x : E3,
        Real.sqrt (normSq0S (Q.metric t) x 4
          (metricRm04 (Q.metric t) x)) ≤ max 0 (max KG KH) := by
  let F := gluedFamily G H T
  have hsum : 0 < T + τ := add_pos hT hτ
  have hregular := gluedFamily_closed_regularity
    G H T τ hT hτ hHzero hGjets hHjets hGright hGend hHinterior
  have hCartesian := cartesian_contDiffOn_of_chartGram
    F (Icc 0 (T + τ)) hregular.2.1
  have hleftSlice (t : ℝ) (ht : t < T) : F t = G t :=
    gluedFamily_of_lt G H T ht
  have hrightSlice (t : ℝ) (ht : T ≤ t) : F t = H (t - T) :=
    gluedFamily_of_ge G H T ht
  have hFzero : F 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric :=
    (hleftSlice 0 hT).trans hGinitial
  have hFcomplete :
      ∀ t ∈ Icc 0 (T + τ), RiemannianMetricComplete (F t) := by
    intro t ht
    by_cases hlt : t < T
    · rw [hleftSlice t hlt]
      exact hGcomplete t ⟨ht.1, hlt.le⟩
    · have hge : T ≤ t := le_of_not_gt hlt
      rw [hrightSlice t hge]
      exact hHcomplete (t - T)
        ⟨sub_nonneg.mpr hge, by linarith [ht.2]⟩
  let K : ℝ := max 0 (max KG KH)
  have hK : 0 ≤ K := le_max_left _ _
  have hKGK : KG ≤ K :=
    (le_max_left KG KH).trans (le_max_right 0 (max KG KH))
  have hKHK : KH ≤ K :=
    (le_max_right KG KH).trans (le_max_right 0 (max KG KH))
  have hFcurvature :
      ∀ t ∈ Icc 0 (T + τ), ∀ x : E3,
        Real.sqrt (normSq0S (F t) x 4
          (metricRm04 (F t) x)) ≤ K := by
    intro t ht x
    by_cases hlt : t < T
    · rw [hleftSlice t hlt, hagree t ⟨ht.1, hlt⟩]
      exact (hKG t ⟨ht.1, hlt⟩ x).trans hKGK
    · have hge : T ≤ t := le_of_not_gt hlt
      rw [hrightSlice t hge]
      exact (hKH (t - T)
        ⟨sub_nonneg.mpr hge, by linarith [ht.2]⟩ x).trans hKHK
  have hdomain :
      (lifetimeInterval (ENNReal.ofReal (T + τ))
        (ENNReal.ofReal_pos.mpr hsum)).carrier = Ico 0 (T + τ) := by
    rw [lifetimeInterval_ofReal (T + τ) hsum]
    rfl
  let Q : PartialStandardSolution :=
    { lifetime := ENNReal.ofReal (T + τ)
      lifetime_pos := ENNReal.ofReal_pos.mpr hsum
      metric := F
      smooth := by
        rw [hdomain]
        exact hCartesian.mono (prod_mono Ico_subset_Icc_self subset_rfl)
      equation := by
        rw [hdomain]
        exact hregular.2.2.2
      initial := hFzero
      complete := by
        rw [hdomain]
        exact fun t ht => hFcomplete t (Ico_subset_Icc_self ht)
      curvature_bound := by
        intro θ _ hθlifetime
        have hθ : θ < T + τ :=
          (ENNReal.ofReal_lt_ofReal_iff hsum).mp hθlifetime
        exact ⟨K, hK, fun t ht x =>
          hFcurvature t ⟨ht.1, ht.2.trans hθ.le⟩ x⟩ }
  have hstrict : S.lifetime < Q.lifetime := by
    change S.lifetime < ENNReal.ofReal (T + τ)
    rw [hlifetime]
    exact (ENNReal.ofReal_lt_ofReal_iff hsum).mpr (by linarith)
  have hextends : S.IsExtendedBy Q := by
    refine ⟨hstrict.le, ?_⟩
    intro t ht
    have htdomain :=
      (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
    rw [hlifetime] at htdomain
    have htT : t < T :=
      (ENNReal.ofReal_lt_ofReal_iff hT).mp htdomain.2
    change F t = S.metric t
    exact (hleftSlice t htT).trans (hagree t ⟨htdomain.1, htT⟩)
  exact ⟨Q, rfl, rfl, hextends, hstrict, hFcomplete, hFcurvature⟩

end DifferentialGeometry.PDE.RicciFlow
