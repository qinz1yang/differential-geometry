import DifferentialGeometry.Analysis.Integration.Measure.Lebesgue.RatioMonotonicity
import DifferentialGeometry.Geometry.Comparison.Volume.Model

/-!
# BSA02: relative volume comparison with exits (abstract kernel)

Blueprint `master207B.tex`, BSA02 (`lem:fibration-convex-boundary-volume-comparison`,
lines 7674–7762): on a compact Riemannian three-manifold with strictly convex boundary, with
`Ric ≥ −2κ² g` on `B_M(p, L)`, `Vol B_M(p, b) / V_κ(b) ≤ Vol B_M(p, a) / V_κ(a)` for
`0 < a ≤ b < L`, also at the endpoint by volume continuity, including centres on the boundary.

The tree has no polar calculus on manifolds with boundary (exit times, minimizers avoiding a convex
boundary, the inward hemisphere at boundary centres), so this module proves the measure-theoretic
core of the blueprint proof for ABSTRACT polar data: a measure space `Θ` of initial directions
(the sphere, or the inward hemisphere at a boundary centre), radial Jacobians `J θ`, alive sets
`A θ` (the times before the first boundary exit / loss of minimality; down-closed), a model density
`m`, and a volume function `vol` with the polar formula
`vol t = ∫_Θ ∫_{(0,t]} 1_{A θ} J θ` (`hpolar`).

* `bsa02_stopped_cross`: a nonnegative Jacobian with `J/m` nonincreasing on its alive set,
  extended by zero after the stopping time, satisfies the cross inequality (no adverse exit term).
* `bsa02_volume_cross`: the cross form `vol b · V(a) ≤ vol a · V(b)`, `V(t) = ∫_{(0,t]} m`.
* `bsa02_volume_cross_endpoint`: the endpoint `b = L` under volume continuity
  `vol L = ⨆_{b ∈ (0,L)} vol b`.
* `bsa02_volume_ratio`: the ratio form (BSA02.a) for finite volumes.
* `bsa02_modelVolume_cross`: the same with the model of the LC02 interface,
  `V_κ = modelVolume (−κ²) 3`, and the blueprint's hypothesis `J θ / s_κ²` nonincreasing.

Missing actual-manifold inputs (none is assumed as a named Prop; each is an explicit hypothesis
of the kernel): the polar formula with exit times on a compact manifold with strictly convex
boundary (`hpolar`, needs: minimizers do not touch the convex boundary at interior times, the
inward hemisphere at boundary centres, measure-zero cut and critical sets); the Riccati/Jacobi
comparison of `J θ / s_κ²` along interior rays under `Ric ≥ −2κ²` (`hratio`; the tree has it
for complete boundaryless manifolds, `intrModelRatioOfFrame_on`); volume continuity at `L`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

/-- One direction: a nonnegative Jacobian whose ratio to a positive model density is
nonincreasing on its (down-closed) alive set, extended by zero afterwards, satisfies the cross
inequality on `(0, L)`. -/
theorem bsa02_stopped_cross {J m : ℝ → ℝ} {A : Set ℝ} {L : ℝ} (hJ : ∀ t, 0 ≤ J t)
    (hm : ∀ t ∈ Ioo 0 L, 0 < m t) (hdown : ∀ a b, 0 < a → a ≤ b → b ∈ A → a ∈ A)
    (hratio : AntitoneOn (fun t => J t / m t) (A ∩ Ioo 0 L)) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < L) :
    ENNReal.ofReal (A.indicator J b) * ENNReal.ofReal (m a) ≤
      ENNReal.ofReal (A.indicator J a) * ENNReal.ofReal (m b) := by
  by_cases hbA : b ∈ A
  · have haA : a ∈ A := hdown a b ha hab hbA
    have hma : 0 < m a := hm a ⟨ha, hab.trans_lt hb⟩
    have hmb : 0 < m b := hm b ⟨ha.trans_le hab, hb⟩
    have hle : J b / m b ≤ J a / m a :=
      hratio ⟨haA, ha, hab.trans_lt hb⟩ ⟨hbA, ha.trans_le hab, hb⟩ hab
    have hcross : J b * m a ≤ J a * m b := (div_le_div_iff₀ hmb hma).mp hle
    rw [indicator_of_mem hbA, indicator_of_mem haA, ← ENNReal.ofReal_mul (hJ b),
      ← ENNReal.ofReal_mul (hJ a)]
    exact ENNReal.ofReal_le_ofReal hcross
  · rw [indicator_of_notMem hbA, ENNReal.ofReal_zero, zero_mul]
    exact bot_le

/-- BSA02 kernel, cross form: with the polar formula `vol t = ∫_Θ ∫_{(0,t]} 1_{A θ} J θ` on
`(0, L)` and `J θ / m` nonincreasing on each alive set, `vol b · V(a) ≤ vol a · V(b)` for
`0 < a ≤ b < L`, where `V(t) = ∫_{(0,t]} m`. -/
theorem bsa02_volume_cross {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (J : Θ → ℝ → ℝ)
    (A : Θ → Set ℝ) (m : ℝ → ℝ) {L : ℝ} (vol : ℝ → ℝ≥0∞) (hJ : ∀ θ t, 0 ≤ J θ t)
    (hm : ∀ t ∈ Ioo 0 L, 0 < m t) (hdown : ∀ θ a b, 0 < a → a ≤ b → b ∈ A θ → a ∈ A θ)
    (hratio : ∀ θ, AntitoneOn (fun t => J θ t / m t) (A θ ∩ Ioo 0 L))
    (hmeas : ∀ θ, Measurable ((A θ).indicator (J θ))) (hmmeas : Measurable m)
    (hmint : ∀ t ∈ Ioo 0 L, IntegrableOn m (Ioc 0 t))
    (hpolar : ∀ t ∈ Ioo 0 L,
      vol t = ∫⁻ θ, (∫⁻ s in Ioc 0 t, ENNReal.ofReal ((A θ).indicator (J θ) s)) ∂ν)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < L) :
    vol b * ∫⁻ s in Ioc 0 a, ENNReal.ofReal (m s) ≤
      vol a * ∫⁻ s in Ioc 0 b, ENNReal.ofReal (m s) := by
  have hdir : ∀ θ, (∫⁻ s in Ioc 0 b, ENNReal.ofReal ((A θ).indicator (J θ) s)) *
      (∫⁻ s in Ioc 0 a, ENNReal.ofReal (m s)) ≤
      (∫⁻ s in Ioc 0 a, ENNReal.ofReal ((A θ).indicator (J θ) s)) *
        ∫⁻ s in Ioc 0 b, ENNReal.ofReal (m s) := by
    intro θ
    refine setLIntegral_Ioc_mul_setLIntegral_Ioc_le (hmeas θ).ennreal_ofReal.aemeasurable
      hmmeas.ennreal_ofReal.aemeasurable (fun a' b' ha' hab' hb' => ?_) hab
    exact bsa02_stopped_cross (hJ θ) hm (hdown θ) (hratio θ) ha' hab' (hb'.trans_lt hb)
  have hfin : (∫⁻ s in Ioc 0 b, ENNReal.ofReal (m s)) ≠ ⊤ :=
    (hmint b ⟨ha.trans_le hab, hb⟩).lintegral_lt_top.ne
  rw [hpolar b ⟨ha.trans_le hab, hb⟩, hpolar a ⟨ha, hab.trans_lt hb⟩]
  calc (∫⁻ θ, (∫⁻ s in Ioc 0 b, ENNReal.ofReal ((A θ).indicator (J θ) s)) ∂ν) *
        ∫⁻ s in Ioc 0 a, ENNReal.ofReal (m s)
      ≤ ∫⁻ θ, ((∫⁻ s in Ioc 0 b, ENNReal.ofReal ((A θ).indicator (J θ) s)) *
          ∫⁻ s in Ioc 0 a, ENNReal.ofReal (m s)) ∂ν := lintegral_mul_const_le _ _
    _ ≤ ∫⁻ θ, ((∫⁻ s in Ioc 0 a, ENNReal.ofReal ((A θ).indicator (J θ) s)) *
          ∫⁻ s in Ioc 0 b, ENNReal.ofReal (m s)) ∂ν := lintegral_mono hdir
    _ = (∫⁻ θ, (∫⁻ s in Ioc 0 a, ENNReal.ofReal ((A θ).indicator (J θ) s)) ∂ν) *
          ∫⁻ s in Ioc 0 b, ENNReal.ofReal (m s) := lintegral_mul_const' _ _ hfin

/-- BSA02 at the endpoint `b = L`, by volume continuity `vol L = ⨆_{b ∈ (0, L)} vol b`. -/
theorem bsa02_volume_cross_endpoint {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (J : Θ → ℝ → ℝ) (A : Θ → Set ℝ) (m : ℝ → ℝ) {L : ℝ} (vol : ℝ → ℝ≥0∞)
    (hJ : ∀ θ t, 0 ≤ J θ t) (hm : ∀ t ∈ Ioo 0 L, 0 < m t)
    (hdown : ∀ θ a b, 0 < a → a ≤ b → b ∈ A θ → a ∈ A θ)
    (hratio : ∀ θ, AntitoneOn (fun t => J θ t / m t) (A θ ∩ Ioo 0 L))
    (hmeas : ∀ θ, Measurable ((A θ).indicator (J θ))) (hmmeas : Measurable m)
    (hmint : ∀ t ∈ Ioo 0 L, IntegrableOn m (Ioc 0 t))
    (hpolar : ∀ t ∈ Ioo 0 L,
      vol t = ∫⁻ θ, (∫⁻ s in Ioc 0 t, ENNReal.ofReal ((A θ).indicator (J θ) s)) ∂ν)
    (hcont : vol L = ⨆ b ∈ Ioo 0 L, vol b) {a : ℝ} (ha : 0 < a) (haL : a < L) :
    vol L * ∫⁻ s in Ioc 0 a, ENNReal.ofReal (m s) ≤
      vol a * ∫⁻ s in Ioc 0 L, ENNReal.ofReal (m s) := by
  rw [hcont, ENNReal.iSup_mul]
  refine iSup_le fun b => ?_
  rw [ENNReal.iSup_mul]
  refine iSup_le fun hb => ?_
  rcases le_total a b with hab | hba
  · exact (bsa02_volume_cross ν J A m vol hJ hm hdown hratio hmeas hmmeas hmint hpolar ha hab
      hb.2).trans (by gcongr; exact hb.2.le)
  · have hvol : vol b ≤ vol a := by
      rw [hpolar b hb, hpolar a ⟨ha, haL⟩]
      exact lintegral_mono fun θ => lintegral_mono_set (Ioc_subset_Ioc le_rfl hba)
    calc vol b * ∫⁻ s in Ioc 0 a, ENNReal.ofReal (m s) ≤
        vol a * ∫⁻ s in Ioc 0 a, ENNReal.ofReal (m s) := by gcongr
      _ ≤ vol a * ∫⁻ s in Ioc 0 L, ENNReal.ofReal (m s) := by gcongr

/-- BSA02, ratio form (BSA02.a) for finite volumes: `vol b / V(b) ≤ vol a / V(a)`. -/
theorem bsa02_volume_ratio {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (J : Θ → ℝ → ℝ)
    (A : Θ → Set ℝ) (m : ℝ → ℝ) {L : ℝ} (vol : ℝ → ℝ≥0∞) (hJ : ∀ θ t, 0 ≤ J θ t)
    (hm : ∀ t ∈ Ioo 0 L, 0 < m t) (hdown : ∀ θ a b, 0 < a → a ≤ b → b ∈ A θ → a ∈ A θ)
    (hratio : ∀ θ, AntitoneOn (fun t => J θ t / m t) (A θ ∩ Ioo 0 L))
    (hmeas : ∀ θ, Measurable ((A θ).indicator (J θ))) (hmmeas : Measurable m)
    (hmint : ∀ t ∈ Ioo 0 L, IntegrableOn m (Ioc 0 t))
    (hpolar : ∀ t ∈ Ioo 0 L,
      vol t = ∫⁻ θ, (∫⁻ s in Ioc 0 t, ENNReal.ofReal ((A θ).indicator (J θ) s)) ∂ν)
    (hvolfin : ∀ t ∈ Ioo 0 L, vol t ≠ ⊤) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < L) :
    (vol b).toReal / ∫ s in (0 : ℝ)..b, m s ≤ (vol a).toReal / ∫ s in (0 : ℝ)..a, m s := by
  have haL : a ∈ Ioo 0 L := ⟨ha, hab.trans_lt hb⟩
  have hbL : b ∈ Ioo 0 L := ⟨ha.trans_le hab, hb⟩
  have hV : ∀ t ∈ Ioo 0 L, ∫⁻ s in Ioc 0 t, ENNReal.ofReal (m s) =
      ENNReal.ofReal (∫ s in (0 : ℝ)..t, m s) := by
    intro t ht
    rw [intervalIntegral.integral_of_le ht.1.le, ofReal_integral_eq_lintegral_ofReal (hmint t ht)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (hm s ⟨hs.1, hs.2.trans_lt ht.2⟩).le
  have hVpos : ∀ t ∈ Ioo 0 L, 0 < ∫ s in (0 : ℝ)..t, m s := fun t ht =>
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).mpr (hmint t ht))
      (fun s hs => hm s ⟨hs.1, hs.2.trans ht.2⟩) ht.1
  have h := bsa02_volume_cross ν J A m vol hJ hm hdown hratio hmeas hmmeas hmint hpolar ha hab hb
  rw [hV a haL, hV b hbL] at h
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (hvolfin a haL) ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hVpos a haL).le,
    ENNReal.toReal_ofReal (hVpos b hbL).le] at h'
  rw [div_le_div_iff₀ (hVpos b hbL) (hVpos a haL)]
  exact h'

/-- The model area `modelArea (−κ²) 3 = 4π s_κ²` is positive on `(0, ∞)`. -/
theorem bsa02_modelArea_pos (κ : ℝ) {t : ℝ} (ht : 0 < t) : 0 < modelArea (-(κ ^ 2)) 3 t :=
  modelArea_pos (by norm_num) ⟨ht, fun h => absurd h (not_lt.mpr (neg_nonpos.mpr (sq_nonneg κ)))⟩

/-- `∫_{(0,t]} modelArea (−κ²) 3 = V_κ(t)` as an extended real. -/
theorem bsa02_lintegral_modelArea (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, ENNReal.ofReal (modelArea (-(κ ^ 2)) 3 s) =
      ENNReal.ofReal (modelVolume (-(κ ^ 2)) 3 t) := by
  have hdef : modelVolume (-(κ ^ 2)) 3 t = ∫ s in (0 : ℝ)..t, modelArea (-(κ ^ 2)) 3 s := rfl
  rw [hdef, intervalIntegral.integral_of_le ht,
    ofReal_integral_eq_lintegral_ofReal (modelArea_continuous _ _).integrableOn_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact (bsa02_modelArea_pos κ hs.1).le

/-- The blueprint's ratio `J/s_κ²` and the ratio `J/modelArea` differ by the factor `4π`. -/
theorem bsa02_antitoneOn_div_modelArea {J : ℝ → ℝ} {S : Set ℝ} (κ : ℝ)
    (hratio : AntitoneOn (fun t => J t / modelRadius (-(κ ^ 2)) t ^ 2) S) :
    AntitoneOn (fun t => J t / modelArea (-(κ ^ 2)) 3 t) S := by
  have hc : 0 < (3 : ℝ) * euclideanUnitBallVolume 3 := by
    have := euclideanUnitBallVolume_pos 3
    positivity
  have key : ∀ t, J t / modelArea (-(κ ^ 2)) 3 t =
      J t / modelRadius (-(κ ^ 2)) t ^ 2 / (3 * euclideanUnitBallVolume 3) := by
    intro t
    have hA : modelArea (-(κ ^ 2)) 3 t =
        (3 : ℝ) * euclideanUnitBallVolume 3 * modelRadius (-(κ ^ 2)) t ^ 2 := by
      simp [modelArea]
    rw [hA, div_div, mul_comm (modelRadius (-(κ ^ 2)) t ^ 2)]
  intro x hx y hy hxy
  simp only [key]
  exact div_le_div_of_nonneg_right (hratio hx hy hxy) hc.le

/-- BSA02 with the model of the LC02 interface: if `J θ / s_κ²` is nonincreasing on every alive
set inside `(0, L)` and the polar formula holds, then
`Vol(b) · V_κ(a) ≤ Vol(a) · V_κ(b)` for `0 < a ≤ b < L`, `V_κ = modelVolume (−κ²) 3`. -/
theorem bsa02_modelVolume_cross {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (J : Θ → ℝ → ℝ) (A : Θ → Set ℝ) (κ : ℝ) {L : ℝ} (vol : ℝ → ℝ≥0∞)
    (hJ : ∀ θ t, 0 ≤ J θ t) (hdown : ∀ θ a b, 0 < a → a ≤ b → b ∈ A θ → a ∈ A θ)
    (hratio : ∀ θ, AntitoneOn (fun t => J θ t / modelRadius (-(κ ^ 2)) t ^ 2) (A θ ∩ Ioo 0 L))
    (hmeas : ∀ θ, Measurable ((A θ).indicator (J θ)))
    (hpolar : ∀ t ∈ Ioo 0 L,
      vol t = ∫⁻ θ, (∫⁻ s in Ioc 0 t, ENNReal.ofReal ((A θ).indicator (J θ) s)) ∂ν)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < L) :
    vol b * ENNReal.ofReal (modelVolume (-(κ ^ 2)) 3 a) ≤
      vol a * ENNReal.ofReal (modelVolume (-(κ ^ 2)) 3 b) := by
  have h := bsa02_volume_cross ν J A (modelArea (-(κ ^ 2)) 3) vol hJ
    (fun t ht => bsa02_modelArea_pos κ ht.1) hdown
    (fun θ => bsa02_antitoneOn_div_modelArea κ (hratio θ)) hmeas
    (modelArea_continuous _ _).measurable
    (fun _ _ => (modelArea_continuous _ _).integrableOn_Ioc) hpolar ha hab hb
  rwa [bsa02_lintegral_modelArea κ ha.le, bsa02_lintegral_modelArea κ (ha.le.trans hab)] at h

/-- BSA02 with the LC02 model at the endpoint `b = L` (volume continuity). -/
theorem bsa02_modelVolume_cross_endpoint {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (J : Θ → ℝ → ℝ) (A : Θ → Set ℝ) (κ : ℝ) {L : ℝ} (vol : ℝ → ℝ≥0∞)
    (hJ : ∀ θ t, 0 ≤ J θ t) (hdown : ∀ θ a b, 0 < a → a ≤ b → b ∈ A θ → a ∈ A θ)
    (hratio : ∀ θ, AntitoneOn (fun t => J θ t / modelRadius (-(κ ^ 2)) t ^ 2) (A θ ∩ Ioo 0 L))
    (hmeas : ∀ θ, Measurable ((A θ).indicator (J θ)))
    (hpolar : ∀ t ∈ Ioo 0 L,
      vol t = ∫⁻ θ, (∫⁻ s in Ioc 0 t, ENNReal.ofReal ((A θ).indicator (J θ) s)) ∂ν)
    (hcont : vol L = ⨆ b ∈ Ioo 0 L, vol b) {a : ℝ} (ha : 0 < a) (haL : a < L) :
    vol L * ENNReal.ofReal (modelVolume (-(κ ^ 2)) 3 a) ≤
      vol a * ENNReal.ofReal (modelVolume (-(κ ^ 2)) 3 L) := by
  have h := bsa02_volume_cross_endpoint ν J A (modelArea (-(κ ^ 2)) 3) vol hJ
    (fun t ht => bsa02_modelArea_pos κ ht.1) hdown
    (fun θ => bsa02_antitoneOn_div_modelArea κ (hratio θ)) hmeas
    (modelArea_continuous _ _).measurable
    (fun _ _ => (modelArea_continuous _ _).integrableOn_Ioc) hpolar hcont ha haL
  rwa [bsa02_lintegral_modelArea κ ha.le, bsa02_lintegral_modelArea κ (ha.trans haL).le] at h

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
