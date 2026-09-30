import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryScalarFloor

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

open DifferentialGeometry.Geometry.Curvature

variable {H : ObservedHistory.{u}}

private theorem setLIntegral_eq_zero_of_forall_mem {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {s : Set X} {f : X → ℝ≥0∞} (hf : ∀ x ∈ s, f x = 0) :
    ∫⁻ x in s, f x ∂μ = 0 := by
  rw [lintegral_def, ← le_zero_iff]
  refine iSup₂_le fun g hg => ?_
  rw [SimpleFunc.lintegral, le_zero_iff]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases eq_or_ne c 0 with rfl | hc
  · exact zero_mul _
  rw [Measure.restrict_apply (g.measurableSet_preimage _)]
  have hempty : g ⁻¹' {c} ∩ s = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => hc ?_
    have hgx : g x ≤ f x := hg x
    rw [hf x hx.2, le_zero_iff] at hgx
    exact (mem_singleton_iff.mp hx.1).symm.trans hgx
  rw [hempty, measure_empty, mul_zero]

variable (H) in
def historyLCurve {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (T v : ℝ)
    (p : (H.stage last).Carrier) (Z : H.historyLExpDomain hle T v p) :
    (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
  Classical.choose Z.property

variable (H) in
def historyLAction {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (T v : ℝ)
    (p : (H.stage last).Carrier) (Z : H.historyLExpDomain hle T v p) : ℝ :=
  ∑ j : H.StageInterval first last,
    H.stageRegularizedAction j.val T (H.historyLCurve hle T v p Z j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)

variable (H) in
def historyMinDomain {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (T B v : ℝ)
    (p : (H.stage last).Carrier) : Set (TangentSpace ThreeModel p) :=
  {Z | ∃ α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
    H.IsHistoryLGeodesicOn hle T v α ∧ H.HasHistoryLInitialVector T α p Z ∧
    (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ∧
    α ⟨last, hle, le_rfl⟩ 0 = p ∧
    H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v p (α ⟨first, le_rfl, hle⟩ v) ∧
    H.regularizedExtendedAction first last T B 0 v α ≠ ⊤}

section MinDomain

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T B v : ℝ}
  {p : (H.stage last).Carrier}

theorem isHistoryLGeodesicOn_historyLCurve (Z : H.historyLExpDomain hle T v p) :
    H.IsHistoryLGeodesicOn hle T v (H.historyLCurve hle T v p Z) :=
  (Classical.choose_spec Z.property).1

theorem hasHistoryLInitialVector_historyLCurve (Z : H.historyLExpDomain hle T v p) :
    H.HasHistoryLInitialVector T (H.historyLCurve hle T v p Z) p Z :=
  (Classical.choose_spec Z.property).2

theorem historyLExp_eq_historyLCurve (Z : H.historyLExpDomain hle T v p) :
    H.historyLExp hle T v p Z = H.historyLCurve hle T v p Z ⟨first, le_rfl, hle⟩ v :=
  rfl

theorem historyMinDomain_subset_historyLExpDomain :
    H.historyMinDomain hle T B v p ⊆ H.historyLExpDomain hle T v p :=
  fun _ ⟨α, hα, hZ, _⟩ => ⟨α, hα, hZ⟩

theorem eqOn_historyLCurve (hv : 0 < v) (Z : H.historyLExpDomain hle T v p)
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hα : H.IsHistoryLGeodesicOn hle T v α) (hZ : H.HasHistoryLInitialVector T α p Z)
    (j : H.StageInterval first last) :
    EqOn (H.historyLCurve hle T v p Z j) (α j)
      (Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :=
  IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector hv
    (isHistoryLGeodesicOn_historyLCurve Z) hα (hasHistoryLInitialVector_historyLCurve Z) hZ j

theorem regularizedExtendedAction_historyLCurve_eq (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p)
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hα : H.IsHistoryLGeodesicOn hle T v α) (hZ : H.HasHistoryLInitialVector T α p Z) :
    H.regularizedExtendedAction first last T B 0 v (H.historyLCurve hle T v p Z) =
      H.regularizedExtendedAction first last T B 0 v α := by
  unfold regularizedExtendedAction
  exact Finset.sum_congr rfl fun j _ => H.stageRegularizedExtendedAction_congr j.val T B _ _ _ _
    ((eqOn_historyLCurve hv Z hα hZ j).mono Ioo_subset_Icc_self)

theorem historyLExp_mem_regularMinimizerEndpoints (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (hZ : Z.1 ∈ H.historyMinDomain hle T B v p) :
    H.historyLExp hle T v p Z ∈ H.regularMinimizerEndpoints first last hle T B v p := by
  obtain ⟨α, hgeo, hinit, hac, hp, hmin, -⟩ := hZ
  rw [historyLExp_eq hv Z hgeo hinit]
  exact ⟨α, hac, hp, rfl, hgeo.2.1, hmin⟩

theorem regularizedCost_historyLExp_ne_top (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (hZ : Z.1 ∈ H.historyMinDomain hle T B v p) :
    H.regularizedCost first last hle T B 0 v p (H.historyLExp hle T v p Z) ≠ ⊤ := by
  obtain ⟨α, hgeo, hinit, -, -, hmin, hfin⟩ := hZ
  rw [historyLExp_eq hv Z hgeo hinit, ← hmin]
  exact hfin

private theorem bounds_of_regularizedCost_ne_top {q : (H.stage first).Carrier}
    (h : H.regularizedCost first last hle T B 0 v p q ≠ ⊤) :
    T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) ∧ T - v ^ 2 ∈ H.stageDomain first := by
  have hne : (H.regularizedActionValues first last hle T B 0 v p q).Nonempty := by
    by_contra hn
    exact h (H.regularizedCost_eq_top_of_no_competitor first last hle T B 0 v p q
      (not_nonempty_iff_eq_empty.1 hn))
  obtain ⟨A, -, -, hupper, hlower, -⟩ := hne
  exact ⟨hupper, hlower⟩

theorem image_historyMinDomain_subset (hv : 0 < v) :
    H.historyLExp hle T v p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v p) ⊆
      H.regularMinimizerEndpoints first last hle T B v p ∩
        {q | H.regularizedCost first last hle T B 0 v p q ≠ ⊤} := by
  rintro _ ⟨Z, hZ, rfl⟩
  exact ⟨historyLExp_mem_regularMinimizerEndpoints hv Z hZ,
    regularizedCost_historyLExp_ne_top hv Z hZ⟩

variable (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
  -B ≤ metricScalarAt (H.stageMetric j t) x)
include hfloor

theorem regularizedExtendedAction_historyLCurve_eq_historyLAction (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (hZ : Z.1 ∈ H.historyMinDomain hle T B v p) :
    H.regularizedExtendedAction first last T B 0 v (H.historyLCurve hle T v p Z) =
      (H.historyLAction hle T v p Z : WithTop ℝ) := by
  obtain ⟨α, hgeo, hinit, hac, -, hmin, hfin⟩ := hZ
  have heq := eqOn_historyLCurve hv Z hgeo hinit
  obtain ⟨hupper, hlower⟩ := bounds_of_regularizedCost_ne_top (hle := hle) (hmin ▸ hfin)
  have hae : ∀ j : H.StageInterval first last, ∀ᵐ t ∂volume.restrict
      (Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t) := by
    intro j
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hfloor j.val _ (H.mapsTo_regularizedStage_Ioo T 0 v j.val ht) _
  have hab (j : H.StageInterval first last) :=
    (H.regularizedStage_bounds le_rfl hv.le hupper hlower j).2.1
  have hint : ∀ j : H.StageInterval first last,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) := by
    intro j
    by_contra hni
    apply hfin
    unfold regularizedExtendedAction
    refine WithTop.sum_eq_top.2 ⟨j, Finset.mem_univ _, ?_⟩
    exact (H.stageRegularizedExtendedAction_eq_top_iff j.val T B (α j) (hab j)
      (H.aestronglyMeasurable_stageRegularizedLagrangian_of_absolutelyContinuousOnInterval
        j.val T 0 v (α j) (hac j)) (hae j)).2 hni
  rw [regularizedExtendedAction_historyLCurve_eq hv Z hgeo hinit,
    H.regularizedExtendedAction_eq_sum_action first last le_rfl hv.le hupper hlower α hint hae,
    historyLAction, WithTop.coe_inj]
  refine Finset.sum_congr rfl fun j _ => H.stageRegularizedAction_congr j.val T _ _ _ _ ?_
  rw [uIoo_of_le (hab j)]
  exact fun t ht => (heq j (Ioo_subset_Icc_self ht)).symm

theorem regularizedCost_historyLExp_eq (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (hZ : Z.1 ∈ H.historyMinDomain hle T B v p) :
    H.regularizedCost first last hle T B 0 v p (H.historyLExp hle T v p Z) =
      (H.historyLAction hle T v p Z : WithTop ℝ) := by
  have h := regularizedExtendedAction_historyLCurve_eq_historyLAction hfloor hv Z hZ
  obtain ⟨α, hgeo, hinit, -, -, hmin, -⟩ := hZ
  rw [historyLExp_eq hv Z hgeo hinit, ← hmin, ← regularizedExtendedAction_historyLCurve_eq hv Z
    hgeo hinit, h]

theorem regularizedDensity_historyLExp_eq (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (hZ : Z.1 ∈ H.historyMinDomain hle T B v p) :
    H.regularizedDensity first last hle T B v p (H.historyLExp hle T v p Z) =
      ENNReal.ofReal (Real.exp (-H.historyLAction hle T v p Z / (2 * v) -
        (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi))) :=
  regularizedDensity_eq_exp_of_regularizedCost_eq first last hle T B hv p _
    (regularizedCost_historyLExp_eq hfloor hv Z hZ)

theorem exists_historyLExp_eq_of_mem_regularMinimizerEndpoints (hv : 0 < v)
    (hT : T ∈ Ioo (H.time last) (H.stageEndTime last)) {q : (H.stage first).Carrier}
    (hq : q ∈ H.regularMinimizerEndpoints first last hle T B v p)
    (hfin : H.regularizedCost first last hle T B 0 v p q ≠ ⊤) :
    ∃ Z : H.historyLExpDomain hle T v p,
      Z.1 ∈ H.historyMinDomain hle T B v p ∧ H.historyLExp hle T v p Z = q := by
  obtain ⟨α, hac, hp, hq, hcross, hmin⟩ := hq
  subst hp hq
  have hfin' : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤ := by
    rw [hmin]
    exact hfin
  have hgeo := isHistoryLGeodesicOn_of_regularizedCost_eq hle hfloor hac hcross hmin hfin' hv
  obtain ⟨Z, hZ⟩ :=
    exists_hasHistoryLInitialVector_of_regularizedCost_eq hle hfloor hac hcross hmin hfin' hv hT
  exact ⟨⟨Z, α, hgeo, hZ⟩, ⟨α, hgeo, hZ, hac, rfl, hmin, hfin'⟩, historyLExp_eq hv _ hgeo hZ⟩

theorem image_historyMinDomain (hv : 0 < v) (hT : T ∈ Ioo (H.time last) (H.stageEndTime last)) :
    H.historyLExp hle T v p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v p) =
      H.regularMinimizerEndpoints first last hle T B v p ∩
        {q | H.regularizedCost first last hle T B 0 v p q ≠ ⊤} := by
  refine (image_historyMinDomain_subset hv).antisymm fun q ⟨hq, hfin⟩ => ?_
  obtain ⟨Z, hZ, rfl⟩ :=
    exists_historyLExp_eq_of_mem_regularMinimizerEndpoints hfloor hv hT hq hfin
  exact ⟨Z, hZ, rfl⟩

theorem regularizedDensity_eq_zero_of_mem_diff_image (hv : 0 < v)
    (hT : T ∈ Ioo (H.time last) (H.stageEndTime last)) {q : (H.stage first).Carrier}
    (hq : q ∈ H.regularMinimizerEndpoints first last hle T B v p \
      H.historyLExp hle T v p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v p)) :
    H.regularizedDensity first last hle T B v p q = 0 := by
  rw [image_historyMinDomain hfloor hv hT] at hq
  apply regularizedDensity_eq_zero_of_regularizedCost_eq_top
  by_contra hne
  exact hq.2 ⟨hq.1, hne⟩

theorem setLIntegral_regularMinimizerEndpoints_eq (hv : 0 < v)
    (hT : T ∈ Ioo (H.time last) (H.stageEndTime last))
    [MeasurableSpace (H.stage first).Carrier] (μ : Measure (H.stage first).Carrier) :
    ∫⁻ q in H.regularMinimizerEndpoints first last hle T B v p,
      H.regularizedDensity first last hle T B v p q ∂μ =
    ∫⁻ q in H.historyLExp hle T v p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v p),
      H.regularizedDensity first last hle T B v p q ∂μ := by
  set E := H.regularMinimizerEndpoints first last hle T B v p
  set I := H.historyLExp hle T v p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v p)
  have hIE : I ⊆ E := (image_historyMinDomain_subset hv).trans inter_subset_left
  refine le_antisymm ?_ (lintegral_mono_set hIE)
  have hEI : E ⊆ I ∪ E \ I := fun q hq => by
    by_cases h : q ∈ I
    exacts [Or.inl h, Or.inr ⟨hq, h⟩]
  calc ∫⁻ q in E, H.regularizedDensity first last hle T B v p q ∂μ
      ≤ ∫⁻ q in I ∪ E \ I, H.regularizedDensity first last hle T B v p q ∂μ :=
        lintegral_mono_set hEI
    _ ≤ ∫⁻ q in I, H.regularizedDensity first last hle T B v p q ∂μ +
        ∫⁻ q in E \ I, H.regularizedDensity first last hle T B v p q ∂μ :=
        lintegral_union_le _ _ _
    _ = ∫⁻ q in I, H.regularizedDensity first last hle T B v p q ∂μ := by
        rw [setLIntegral_eq_zero_of_forall_mem μ
          fun q hq => regularizedDensity_eq_zero_of_mem_diff_image hfloor hv hT hq, add_zero]

end MinDomain

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

theorem exists_reducedVolume_eq_lintegral_image_historyMinDomain :
    ∃ b : ℝ, ∀ B₀ : ℝ, b ≤ B₀ → ∀ (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier)
      (T v : ℝ)
      (hle : H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)) ≤ k),
      0 < v → T ∈ Ioo (H.toHistory.time k) (H.toHistory.stageEndTime k) →
      H.reducedVolume k p T v =
        ∫⁻ q in H.toHistory.historyLExp hle T v p ''
            (Subtype.val ⁻¹' H.toHistory.historyMinDomain hle T B₀ v p),
          H.toHistory.regularizedDensity _ k hle T B₀ v p q
          ∂riemannianVolumeMeasure ThreeModel
            (H.stage (H.toHistory.activeStage
              (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)))).Carrier
            (H.toHistory.stageMetric _ (T - v ^ 2)) := by
  obtain ⟨b, hb⟩ := H.exists_reducedVolume_eq_lintegral
  obtain ⟨b', -, hfloor⟩ := H.exists_stageMetric_scalar_lower_bound
  refine ⟨max b b', fun B₀ hB₀ k p T v hle hv hT => ?_⟩
  refine (hb B₀ (le_of_max_le_left hB₀) k p T v hle).trans ?_
  exact ObservedHistory.setLIntegral_regularMinimizerEndpoints_eq (H := H.toHistory)
    (first := H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)))
    (last := k) (hle := hle) (T := T) (B := B₀) (v := v) (p := p)
    (fun j t ht x => (neg_le_neg (le_of_max_le_right hB₀)).trans (hfloor j t ht x)) hv hT _

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
