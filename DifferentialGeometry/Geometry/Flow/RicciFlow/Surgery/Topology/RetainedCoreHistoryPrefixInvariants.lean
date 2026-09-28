import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerBookkeeping

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u})

theorem inCutoffClass_prefixAt {g₀ : P₀.Metric} {B : ℝ} {p₀ : CutoffParameters}
    {δbound ρbound : ℝ} (hH : H.InCutoffClass g₀ B p₀ δbound ρbound)
    (k : Fin (H.eventCount + 1)) : (H.prefixAt k).InCutoffClass g₀ B p₀ δbound ρbound := by
  obtain ⟨⟨A⟩, -, hB, hrec, hΛ⟩ := hH
  have hc : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) (0 : Fin (k.val + 1)) = 0 :=
    Fin.ext (by simp)
  refine ⟨⟨InitialIdentification.of_stageZero A (congrArg H.stage hc)
    (congr_arg_heq H.initialMetric hc)⟩, rfl, ?_, ?_, hΛ⟩
  · exact ((H.time_strictMono.monotone (Fin.le_last k)).trans H.time_le_horizon).trans_lt hB
  · obtain ⟨p, records, hfam⟩ :=
      (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound
        ρbound).mp hrec
    exact ((H.prefixAt k).hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀
      δbound ρbound).mpr ⟨p, H.prefixRecords k records,
        H.isCanonicalCutoffRecordFamily_prefixAt k hfam⟩

theorem eventSlabsCanonical_prefixAt (k : Fin (H.eventCount + 1)) {ε C1 C2 q τmin : ℝ}
    (h : H.EventSlabsCanonical ε C1 C2 q τmin k) :
    (H.prefixAt k).EventSlabsCanonical ε C1 C2 q τmin (Fin.last _) :=
  fun i _ => h (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) (Fin.lt_def.mpr i.isLt)

theorem eventSlabsGradient_prefixAt (k : Fin (H.eventCount + 1)) {Cgrad : ℝ≥0} {q : ℝ}
    (h : H.EventSlabsGradient Cgrad q k) :
    (H.prefixAt k).EventSlabsGradient Cgrad q (Fin.last _) :=
  fun i _ => h (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) (Fin.lt_def.mpr i.isLt)

theorem eventSlabsSpatiallyCanonical_prefixAt (k : Fin (H.eventCount + 1)) {ε C1 C2 q : ℝ}
    (h : H.EventSlabsSpatiallyCanonical ε C1 C2 q k) :
    (H.prefixAt k).EventSlabsSpatiallyCanonical ε C1 C2 q (Fin.last _) :=
  fun i _ => h (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) (Fin.lt_def.mpr i.isLt)

theorem prefixAt_activeStage_val (k : Fin (H.eventCount + 1))
    (τ : Icc (0 : ℝ) (H.prefixAt k).toHistory.horizon) (τ' : Icc (0 : ℝ) H.toHistory.horizon)
    (hττ : (τ : ℝ) = τ') :
    ((H.prefixAt k).toHistory.activeStage τ).val = (H.toHistory.activeStage τ').val := by
  have hk := (H.prefixAt k).toHistory.activeStage_time_le τ
  have h1 : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))
      ((H.prefixAt k).toHistory.activeStage τ) ≤ H.toHistory.activeStage τ' :=
    H.toHistory.le_activeStage τ' _ (by rw [← hττ]; exact hk)
  have hk'τ := H.toHistory.activeStage_time_le τ'
  have hτk : (τ : ℝ) ≤ H.time k := τ.2.2
  have hk'k : H.toHistory.activeStage τ' ≤ k := by
    refine H.time_strictMono.le_iff_le.mp ?_
    change H.time (H.toHistory.activeStage τ') ≤ H.time k
    have : (τ' : ℝ) ≤ H.time k := hττ ▸ hτk
    linarith
  have hk'v : (H.toHistory.activeStage τ').val ≤ k.val := Fin.le_def.mp hk'k
  have h2 : (⟨(H.toHistory.activeStage τ').val, by
      change (H.toHistory.activeStage τ').val < k.val + 1
      omega⟩ :
      Fin ((H.prefixAt k).toHistory.eventCount + 1)) ≤ (H.prefixAt k).toHistory.activeStage τ :=
    (H.prefixAt k).toHistory.le_activeStage τ _ (by
      change H.time (H.toHistory.activeStage τ') ≤ (τ : ℝ)
      rw [hττ]
      exact hk'τ)
  exact le_antisymm (Fin.le_def.mp h1) (Fin.le_def.mp h2)

theorem prefixAt_stageMetric_activeStage (k : Fin (H.eventCount + 1))
    (τ : Icc (0 : ℝ) (H.prefixAt k).toHistory.horizon) :
    (H.prefixAt k).toHistory.stageMetric ((H.prefixAt k).toHistory.activeStage τ) τ =
      H.toHistory.stageMetric (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))
        ((H.prefixAt k).toHistory.activeStage τ)) τ := by
  have hle := (H.prefixAt k).toHistory.activeStage_time_le τ
  generalize (H.prefixAt k).toHistory.activeStage τ = m at hle ⊢
  cases m using Fin.lastCases with
  | last =>
    have hτk : (τ : ℝ) ≤ H.time k := τ.2.2
    have heq : (τ : ℝ) = H.time (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))
        (Fin.last (H.prefixAt k).toHistory.eventCount)) := le_antisymm hτk hle
    rw [ObservedHistory.stageMetric_last_of_le (H := (H.prefixAt k).toHistory) le_rfl, heq,
      ObservedHistory.stageMetric_initial]
    rfl
  | cast i =>
    rw [ObservedHistory.stageMetric_castSucc_apply]
    change _ = H.toHistory.stageMetric (Fin.castLE (Nat.le_of_lt_succ k.isLt) i).castSucc τ
    rw [ObservedHistory.stageMetric_castSucc_apply]
    rfl

open private rm_bound_of_stage_eq volume_lower_bound_of_stage_index from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport

theorem noncollapsedBefore_prefixAt (k : Fin (H.eventCount + 1)) {κ ρ t : ℝ}
    (h : H.NoncollapsedBefore κ ρ t) (ht : H.time k ≤ t) :
    (H.prefixAt k).NoncollapsedBefore κ ρ (H.time k) := by
  have hTH : H.time k ≤ H.horizon :=
    (H.time_strictMono.monotone (Fin.le_last k)).trans H.time_le_horizon
  have hcast : k.val + 1 ≤ H.eventCount + 1 := Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)
  intro τ p r hτ hr hball
  obtain ⟨hr0, a, hat, ha, htr⟩ := hball
  let τ' : Icc (0 : ℝ) H.toHistory.horizon := ⟨τ, τ.2.1, τ.2.2.trans hTH⟩
  let a' : Icc (0 : ℝ) H.toHistory.horizon := ⟨a, a.2.1, a.2.2.trans hTH⟩
  have hAτ := H.prefixAt_activeStage_val k τ τ' rfl
  have hAa := H.prefixAt_activeStage_val k a a' rfl
  have hka := (H.prefixAt k).toHistory.activeStage_mono hat
  rw [H.prefixAt_stageMetric_activeStage k τ]
  refine volume_lower_bound_of_stage_index H h τ' (hτ.trans ht)
    (Fin.castLE hcast ((H.prefixAt k).toHistory.activeStage τ)) (Fin.ext hAτ.symm) p hr0 hr a'
    hat ha (Fin.castLE hcast ((H.prefixAt k).toHistory.activeStage a))
    (Fin.le_def.mpr (le_of_eq hAa)) (Fin.le_def.mpr (Fin.le_def.mp hka)) ?_
  intro x hx
  have hx' : x ∈ riemannianBallOf ((H.prefixAt k).toHistory.stageMetric
      ((H.prefixAt k).toHistory.activeStage τ) τ) p r := by
    rw [H.prefixAt_stageMetric_activeStage k τ]
    exact hx
  obtain ⟨A, hA1, hA2⟩ := htr x hx'
  refine ⟨H.backwardPointTraceOfPrefix k A, ?_, ?_⟩
  · intro v hav hvt
    have hvT : (v : ℝ) ≤ H.time k := (show (v : ℝ) ≤ τ from hvt).trans τ.2.2
    let vK : Icc (0 : ℝ) (H.prefixAt k).toHistory.horizon := ⟨v, v.2.1, hvT⟩
    have hAv := H.prefixAt_activeStage_val k vK v rfl
    have hav' : a ≤ vK := show (a : ℝ) ≤ v from hav
    have hvt' : vK ≤ τ := show (v : ℝ) ≤ τ from hvt
    have hA := hA1 vK hav' hvt'
    rw [H.prefixAt_stageMetric_activeStage k vK] at hA
    refine rm_bound_of_stage_eq _ (m' := Fin.castLE hcast
        ((H.prefixAt k).toHistory.activeStage vK))
      (m := H.toHistory.activeStage v) (Fin.ext hAv) _ _
      (Fin.le_def.mpr (Fin.le_def.mp
        ((H.prefixAt k).toHistory.activeStage_mono hav')))
      (Fin.le_def.mpr (Fin.le_def.mp
        ((H.prefixAt k).toHistory.activeStage_mono hvt'))) v r ?_
    exact hA
  · intro i hi hil
    have hil' : i.val + 1 ≤ ((H.prefixAt k).toHistory.activeStage τ).val := Fin.le_def.mp hil
    have hkj : ((H.prefixAt k).toHistory.activeStage τ).val < k.val + 1 :=
      ((H.prefixAt k).toHistory.activeStage τ).isLt
    have hi' : ((H.prefixAt k).toHistory.activeStage a).val ≤ i.val := by
      rw [hAa]
      exact Fin.le_def.mp hi
    exact hA2 ⟨i.val, by
        change i.val < k.val
        omega⟩ (Fin.le_def.mpr hi') (Fin.le_def.mpr hil')

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
