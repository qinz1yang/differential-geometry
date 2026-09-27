import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.Window
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.EulerLagrangeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.C1Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.Extension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.Sobolev

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem isLRegularizedGeodesicOn_of_lRegularizedAction_le [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {T a b : ℝ} (hab : a < b) (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (γ : ℝ → M) (hγc : Continuous γ) (hγ : Manifold.absolutelyContinuousOnInterval I γ a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T γ) volume a b)
    (hmin : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = γ a → δ b = γ b →
      lRegularizedAction S T γ a b ≤ lRegularizedAction S T δ a b) :
    IsLRegularizedGeodesicOn S T γ (Ioo a b) := by
  obtain ⟨m, t, p, w, ht0, htmono, htlast, hsrc, hrep, -⟩ :=
    exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval S hS.smoothMetric
      ⟨hS.scalarCont⟩ T a b hab.le γ hγ hint (fun s hs => D.regular_subset (hreg s hs))
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  intro s hs
  exact ⟨hreg s (Ioo_subset_Icc_self hs), lMinCurve_regularity S hS T a b hab t htmono ht0 htlast
    p γ hγc w hsrc hrep hreg hmin s hs⟩

theorem eq_of_eqOn_lRegularizedCurve (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T b : ℝ} (hT : T ∈ D.regular) (hb : 0 < b) (x : M)
    {Z Z' : TangentSpace I x}
    (h : EqOn (lRegularizedCurve S T x Z) (lRegularizedCurve S T x Z') (Icc 0 b)) :
    Z = Z' := by
  have hdiff (W : TangentSpace I x) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I (lRegularizedCurve S T x W) 0 := by
    have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
        (fun r : ℝ => ((W, r) : E × ℝ)) 0 :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact ((lRegularizedCurve_smoothAt S hS T x W hT).comp 0 hpair).mdifferentiableAt
      (by simp)
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) b) 0 :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_Icc hb 0 ⟨le_rfl, hb.le⟩)
  have hd : mfderiv 𝓘(ℝ, ℝ) I (lRegularizedCurve S T x Z) 0 =
      mfderiv 𝓘(ℝ, ℝ) I (lRegularizedCurve S T x Z') 0 := by
    rw [← mfderivWithin_eq_mfderiv hu (hdiff Z), ← mfderivWithin_eq_mfderiv hu (hdiff Z')]
    exact mfderivWithin_congr h (h ⟨le_rfl, hb.le⟩)
  have h2 : (2 : ℝ) • Z = (2 : ℝ) • Z' := by
    rw [← lRegularizedCurve_velocity_zero S hS T x Z hT,
      ← lRegularizedCurve_velocity_zero S hS T x Z' hT]
    unfold lVelocity
    exact congrArg (fun L => L (1 : ℝ)) hd
  exact smul_right_injective _ two_ne_zero h2

theorem existsUnique_eqOn_lRegularizedCurve_of_lRegularizedAction_le
    [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T b : ℝ} (hb : 0 < b)
    (hreg : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.regular)
    (γ : ℝ → M) (hγc : Continuous γ) (hγ : Manifold.absolutelyContinuousOnInterval I γ 0 b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T γ) volume 0 b)
    (hmin : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = γ 0 → δ b = γ b →
      lRegularizedAction S T γ 0 b ≤ lRegularizedAction S T δ 0 b) :
    ∃! Z : TangentSpace I (γ 0), b ∈ lRegularizedDomain S T (γ 0) Z ∧
      EqOn (lRegularizedCurve S T (γ 0) Z) γ (Icc 0 b) := by
  have hT : T ∈ D.regular := by simpa using hreg 0 ⟨le_rfl, hb.le⟩
  obtain ⟨m, t, p, w, ht0, htmono, htlast, hsrc, hrep, -⟩ :=
    exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval S hS.smoothMetric
      ⟨hS.scalarCont⟩ T 0 b hb.le γ hγ hint (fun s hs => D.regular_subset (hreg s hs))
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have hc1 := lMinCurve_c1 S hS T 0 b hb t htmono ht0 htlast p γ hγc w hsrc hrep hreg hmin
  have hsol := lMinCurve_regularity S hS T 0 b hb t htmono ht0 htlast p γ hγc w hsrc hrep hreg
    hmin
  obtain ⟨α, hαγ, e, he, hα⟩ := exists_lRegularizedExtOn S hS T 0 b hb γ hc1 hreg hsol
  let Z : TangentSpace I (γ 0) := (2 : ℝ)⁻¹ • lVelocity (I := I) α 0
  have hvel : lVelocity (I := I) α 0 = 2 • Z := by
    have hreal : lVelocity (I := I) α 0 = (2 : ℝ) • Z :=
      (smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0) _).symm
    exact hreal.trans (Nat.cast_smul_eq_nsmul ℝ 2 Z)
  have hcurve : IsLRegularizedCurveOn S T α (Ioo (-e) (b + e)) (γ 0) Z :=
    ⟨hαγ ⟨le_rfl, hb.le⟩, hvel, by simpa only [IsLRegularizedGeodesicOn, zero_sub] using hα⟩
  have hZ : EqOn (lRegularizedCurve S T (γ 0) Z) γ (Icc 0 b) := fun s hs =>
    (lRegularizedCurve_eqIcc S hS T b e hb.le he hcurve hs).trans (hαγ hs)
  refine ⟨Z, ⟨⟨α, Ioo (-e) (b + e), isOpen_Ioo, isPreconnected_Ioo,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hcurve⟩, hZ⟩, ?_⟩
  rintro Z' ⟨-, hZ'⟩
  exact eq_of_eqOn_lRegularizedCurve S hS hT hb (γ 0) fun s hs => (hZ' hs).trans (hZ hs).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.LWindow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u
variable {H : ObservedHistory.{u}} {lo hi : Fin (H.eventCount + 1)} {T : ℝ}
  (W : H.LWindow lo hi T)

theorem intervalIntegrable_lRegularizedLagrangian_of_ne_top
    {first last : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (hhi : hi ≤ last) {B u v : ℝ}
    (hu : 0 ≤ u) (hua : u ≤ W.a) (hbv : W.b ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (γ : ℝ → W.X) (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j : H.StageInterval lo hi,
      EqOn (W.f j ∘ γ) (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
        (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) :
    IntervalIntegrable (lRegularizedLagrangian W.S T γ) volume W.a W.b := by
  have hsc (j : Fin (H.eventCount + 1)) (u' v' : ℝ) :
      ∀ t ∈ Ioo (H.regularizedStageStart T u' j) (H.regularizedStageEnd T v' j),
        ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) x :=
    fun t ht x => hfloor j _ (H.mapsTo_regularizedStage_Ioo T u' v' j ht) x
  have hav : W.a ≤ v := W.lt.le.trans hbv
  have h1 := regularizedExtendedAction_eq_add_at_parameter hi (hlo.trans W.le) hhi hu hua hav
    W.upper (hsc hi u v) α hα
  have hα' : ∀ j : H.StageInterval first hi, Manifold.absolutelyContinuousOnInterval ThreeModel
      (α ⟨j.val, j.property.1, j.property.2.trans hhi⟩)
      (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T v j.val) := by
    intro j
    have hb := (H.regularizedStage_bounds W.nonneg hav W.upper_mem_Icc hlower j).2.1
    apply Manifold.absolutelyContinuousOnInterval_mono (hα _)
    rw [uIcc_of_le hb, uIcc_of_le (H.regularizedStage_bounds hu (hua.trans hav) hupper hlower
      ⟨j.val, j.property.1, j.property.2.trans hhi⟩).2.1]
    exact Icc_subset_Icc (regularizedStageStart_le_of_le hu hua j.val) le_rfl
  have h2 := regularizedExtendedAction_eq_add_at_parameter lo hlo W.le W.nonneg W.lt.le hbv
    W.lower (hsc lo W.a v) _ hα'
  have hE2 : H.regularizedExtendedAction lo hi T B W.a W.b
      (fun j => α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩) ≠ ⊤ := by
    intro h
    apply hfin
    rw [h1, h2, h, top_add, add_top]
  exact not_not.1 fun hn => hE2 ((W.regularizedExtendedAction_eq_top_iff
    (fun j => hsc j.val W.a W.b) _ γ hγ heq).2 hn)

theorem isLRegularizedGeodesicOn_of_regularizedCost_eq {first last : Fin (H.eventCount + 1)}
    (hle : first ≤ last) (hlo : first ≤ lo) (hhi : hi ≤ last) {B u v : ℝ} (hu : 0 ≤ u)
    (hua : u ≤ W.a) (hbv : W.b ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v α =
      H.regularizedCost first last hle T B u v (α ⟨last, hle, le_rfl⟩ u)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (γ : ℝ → W.X) (hγc : Continuous γ)
    (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j : H.StageInterval lo hi,
      EqOn (W.f j ∘ γ) (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
        (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) :
    IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  exact isLRegularizedGeodesicOn_of_lRegularizedAction_le W.S W.solution W.lt W.regular γ hγc hγ
    (W.intervalIntegrable_lRegularizedLagrangian_of_ne_top hlo hhi hu hua hbv hupper hlower
      hfloor α hα hfin γ hγ heq)
    (fun δ hδ hδa hδb => W.lRegularizedAction_le_of_regularizedCost_eq hle hlo hhi hu hua hbv
      hupper hlower hfloor α hα hnode hmin hfin γ hγ heq δ hδ hδa hδb)

theorem exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (hlo : first ≤ lo)
    (hhi : hi ≤ last) {B u v : ℝ} (hu : 0 ≤ u) (hua : u ≤ W.a) (hbv : W.b ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v α =
      H.regularizedCost first last hle T B u v (α ⟨last, hle, le_rfl⟩ u)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (hrange : ∀ j : H.StageInterval lo hi,
      MapsTo (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
        (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))
        (range (W.f j))) :
    ∃ γ : ℝ → W.X, Continuous γ ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b ∧
      (∀ j : H.StageInterval lo hi,
        EqOn (W.f j ∘ γ) (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
          (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) ∧
      IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) := by
  have hav : W.a ≤ v := W.lt.le.trans hbv
  have hαW : ∀ j : H.StageInterval lo hi, Manifold.absolutelyContinuousOnInterval ThreeModel
      (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
      (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) := by
    intro j
    have hb := (H.regularizedStage_bounds W.nonneg W.lt.le W.upper_mem_Icc W.lower j).2.1
    apply Manifold.absolutelyContinuousOnInterval_mono (hα _)
    rw [uIcc_of_le hb, uIcc_of_le (H.regularizedStage_bounds hu (hua.trans hav) hupper hlower
      ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩).2.1]
    exact Icc_subset_Icc (regularizedStageStart_le_of_le hu hua j.val)
      (regularizedStageEnd_le_of_le (W.nonneg.trans W.lt.le) hbv j.val)
  obtain ⟨γ, hγc, hγ, heq⟩ := W.exists_lift
    (fun j => α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩) hαW
    (fun i hl hh => hnode i (hlo.trans hl) (hh.trans hhi)) hrange
  exact ⟨γ, hγc, hγ, heq, W.isLRegularizedGeodesicOn_of_regularizedCost_eq hle hlo hhi hu hua
    hbv hupper hlower hfloor α hα hnode hmin hfin γ hγc hγ heq⟩

theorem existsUnique_eqOn_lRegularizedCurve_of_regularizedCost_eq
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (hlo : first ≤ lo)
    (hhi : hi ≤ last) {B v : ℝ} (ha : W.a = 0) (hbv : W.b ≤ v)
    (hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤)
    (γ : ℝ → W.X) (hγc : Continuous γ)
    (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j : H.StageInterval lo hi,
      EqOn (W.f j ∘ γ) (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
        (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) :
    ∃! Z : TangentSpace ThreeModel (γ 0), W.b ∈ lRegularizedDomain W.S T (γ 0) Z ∧
      EqOn (lRegularizedCurve W.S T (γ 0) Z) γ (Icc 0 W.b) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hint := W.intervalIntegrable_lRegularizedLagrangian_of_ne_top hlo hhi le_rfl ha.ge hbv
    hupper hlower hfloor α hα hfin γ hγ heq
  have hmin' := fun δ hδ hδa hδb => W.lRegularizedAction_le_of_regularizedCost_eq hle hlo hhi
    le_rfl ha.ge hbv hupper hlower hfloor α hα hnode hmin hfin γ hγ heq δ hδ hδa hδb
  have hreg := W.regular
  have hb : 0 < W.b := ha ▸ W.lt
  rw [ha] at hint hmin' hreg hγ
  exact existsUnique_eqOn_lRegularizedCurve_of_lRegularizedAction_le W.S W.solution hb hreg γ hγc
    hγ hint hmin'

theorem exists_stage (j : Fin (H.eventCount + 1)) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hstart : H.time j < T - b ^ 2) (hend : T - a ^ 2 < H.stageEndTime j) :
    ∃ W : H.LWindow j j T, W.a = a ∧ W.b = b ∧ ∀ k, range (W.f k) = univ := by
  have hmem : ∀ s ∈ Icc a b, T - s ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j) := by
    intro s hs
    have h1 : a ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ ha hs.1 2
    have h2 : s ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (ha.trans hs.1) hs.2 2
    exact ⟨by linarith, by linarith⟩
  have hdom : ∀ s ∈ Icc a b, T - s ^ 2 ∈ H.stageDomain j := by
    intro s hs
    have h := hmem s hs
    cases j using Fin.lastCases with
    | last =>
      rw [stageEndTime_last] at h
      simp only [stageDomain, Fin.lastCases_last, mem_Icc]
      exact ⟨h.1.le, h.2.le⟩
    | cast i =>
      rw [stageEndTime_castSucc] at h
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico]
      exact ⟨h.1.le, h.2⟩
  have key : ∀ {D : RealTimeInterval}
      (S : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) D), IsSolutionOn S →
      (∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) →
      (∀ s ∈ Ioo a b, S.base.metric (T - s ^ 2) = H.stageMetric j (T - s ^ 2)) →
      ∃ W : H.LWindow j j T, W.a = a ∧ W.b = b ∧ ∀ k, range (W.f k) = univ := by
    intro D S hS hreg hmet
    refine ⟨ofStage j ha hab (hdom a ⟨le_rfl, hab.le⟩) (hdom b ⟨hab.le, le_rfl⟩) S hS hreg hmet ⊤,
      rfl, rfl, ?_⟩
    rintro ⟨k, h1, h2⟩
    obtain rfl := le_antisymm h1 h2
    exact eq_univ_of_forall fun y => ⟨⟨y, trivial⟩, rfl⟩
  cases j using Fin.lastCases with
  | last =>
    have h := hmem a ⟨le_rfl, hab.le⟩
    rw [stageEndTime_last] at h
    have hlt : H.time (Fin.last H.eventCount) < H.horizon := h.1.trans h.2
    refine key (H.finalSlab hlt).flow (H.finalSlab hlt).equation (fun s hs => ?_) (fun s _ => ?_)
    · have h' := hmem s hs
      rw [stageEndTime_last] at h'
      exact h'
    · simp only [stageMetric, Fin.lastCases_last, dif_pos hlt]
  | cast i =>
    refine key (H.event i).incoming.flow (H.event i).incoming.equation (fun s hs => ?_)
      (fun s _ => ?_)
    · have h' := hmem s hs
      rw [stageEndTime_castSucc] at h'
      exact h'
    · simp only [stageMetric, Fin.lastCases_castSucc]

theorem exists_stage_isLRegularizedGeodesicOn_of_regularizedCost_eq
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {B u v : ℝ} (hu : 0 ≤ u)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v α =
      H.regularizedCost first last hle T B u v (α ⟨last, hle, le_rfl⟩ u)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (j : H.StageInterval first last) {a b : ℝ} (hua : u ≤ a) (hab : a < b) (hbv : b ≤ v)
    (hstart : H.time j.val < T - b ^ 2) (hend : T - a ^ 2 < H.stageEndTime j.val) :
    ∃ W : H.LWindow j.val j.val T, W.a = a ∧ W.b = b ∧ (∀ k, range (W.f k) = univ) ∧
      ∃ γ : ℝ → W.X, Continuous γ ∧
        EqOn (W.f ⟨j.val, le_rfl, le_rfl⟩ ∘ γ) (α j) (Icc a b) ∧
        IsLRegularizedGeodesicOn W.S T γ (Ioo a b) := by
  obtain ⟨W, rfl, rfl, hr⟩ := exists_stage j.val (hu.trans hua) hab hstart hend
  obtain ⟨γ, hγc, -, heq, hgeo⟩ := W.exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq
    hle j.property.1 j.property.2 hu hua hbv hupper hlower hfloor α hα hnode hmin hfin
    (fun k => by rw [hr k]; exact mapsTo_univ _ _)
  have h := heq ⟨j.val, le_rfl, le_rfl⟩
  rw [H.regularizedStageStart_eq_of_mem_Icc W.nonneg W.upper_mem_Icc,
    H.regularizedStageEnd_eq_of_mem_stageDomain (W.nonneg.trans W.lt.le) W.lower] at h
  exact ⟨W, rfl, rfl, hr, γ, hγc, h, hgeo⟩

theorem exists_stage_initialVector_of_regularizedCost_eq
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {B v : ℝ}
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤)
    {b : ℝ} (hb : 0 < b) (hbv : b ≤ v) (hstart : H.time last < T - b ^ 2)
    (hend : T < H.stageEndTime last) :
    ∃ W : H.LWindow last last T, W.a = 0 ∧ W.b = b ∧ (∀ k, range (W.f k) = univ) ∧
      ∃ γ : ℝ → W.X, Continuous γ ∧
        EqOn (W.f ⟨last, le_rfl, le_rfl⟩ ∘ γ) (α ⟨last, hle, le_rfl⟩) (Icc 0 b) ∧
        IsLRegularizedGeodesicOn W.S T γ (Ioo 0 b) ∧
        ∃! Z : TangentSpace ThreeModel (γ 0), b ∈ lRegularizedDomain W.S T (γ 0) Z ∧
          EqOn (lRegularizedCurve W.S T (γ 0) Z) γ (Icc 0 b) := by
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨W, ha, rfl, hr⟩ := exists_stage last le_rfl hb hstart (by simpa using hend)
  obtain ⟨γ, hγc, hγ, heq, hgeo⟩ := W.exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq
    hle hle le_rfl le_rfl ha.ge hbv hupper hlower hfloor α hα hnode hmin hfin
    (fun k => by rw [hr k]; exact mapsTo_univ _ _)
  have h := heq ⟨last, le_rfl, le_rfl⟩
  rw [H.regularizedStageStart_eq_of_mem_Icc W.nonneg W.upper_mem_Icc,
    H.regularizedStageEnd_eq_of_mem_stageDomain (W.nonneg.trans W.lt.le) W.lower, ha] at h
  rw [ha] at hgeo
  exact ⟨W, ha, rfl, hr, γ, hγc, h, hgeo,
    W.existsUnique_eqOn_lRegularizedCurve_of_regularizedCost_eq hle hle le_rfl ha hbv hupper
      hlower hfloor α hα hnode hmin hfin γ hγc hγ heq⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.LWindow
