import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaFreshHCT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HstayGuardedGateP6HS

/-!
# guarded late FOOT3 gate 的天花板透传孪生（O-CH11-HCEILT G5 P3，后缀 `_HCT`）

`hlocBCD_of_localSupplies_gate_late_guarded_P6HS` 逐字，
`hceil : ∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹`
逐 frame 透传（gate 块后插入；证明中 `hdσ` 后插 `hceil`）。
槽形收窄 = 义务变弱（§0.2/§0.3），旧 → 新由忽略 `hceil` 得。生成器 gen/genP.py。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open ObservedHistory

/-- **FOOT3 gate guarded 孪生（`_P6HS`，PROVISIONAL：binder 同 P6HP2 gate，`hderivL` / `hgradL` 换 c⋆
guard 形）**：结论逐字；kernel = `terminal_scalar_bound_local_late_guarded_P6HS`。 -/
theorem hlocBCD_of_localSupplies_gate_late_guarded_HCT {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Aseed : ℝ}
    {q : CutoffParameters}
    (hεle : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cg : ℝ} {Cder Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hmargin :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)) (δ : ℝ), 0 < δ →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            riemannianEDistOf ((Kh k).stageMetric (i k).castSucc t)
                ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal δ)
    (hrecords :
      ∀ (Rrad ζ₀ B Dcap : ℝ), 0 < ζ₀ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (T₀ : ℝ)
          (records : ∀ i' : Fin (Kh k).eventCount, T₀ ≤ (Kh k).time i'.succ →
            GeometricCutoffRecord (Kh k) i' pp),
          (∀ i' hT b, ((records i' hT).static b).hasCanonicalWindow) ∧
          Rrad ≤ pp.modelRadius ∧ 2 ≤ pp.modelOrder ∧ pp.modelAccuracy ≤ ζ₀ ∧
          T₀ ≤ (σ k : ℝ) - B / R k ∧
          ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ¬ ∃ (i' : Fin (Kh k).eventCount)
              (hT : T₀ ≤ (Kh k).time i'.succ) (hl : i'.succ ≤ (i k).castSucc)
              (Btr : BackwardPointTrace (Kh k) i'.succ (i k).castSucc hl p')
              (b : ((Kh k).event i').RetainedBoundaryIndex)
              (w : standardCapWindow pp.modelRadius),
              Btr.point i'.succ le_rfl hl = ((records i' hT).static b).window w ∧
                ‖w.val‖ < Dcap + 1 ∧
                t - (Kh k).time i'.succ ≤ 1 / 2 * (((records i' hT).static b).neck.scale)⁻¹)
    (hpinch :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ i' : Fin (Kh k).eventCount,
          Perelman.PhiAlmostNonnegative ((Kh k).event i').incoming.flow
            (Ico ((Kh k).time i'.castSucc) ((Kh k).time i'.succ) ∩ Ici (1 / 2)) phi)
    (hderivL :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            (∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
                (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
                (hij : i'.castSucc < (i k).castSucc),
              ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event i').incoming.flow.scalar v'
                  (B.point i'.castSucc hf hij.le) →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Cder : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                    (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                  Cder * ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) ^ 2) ∧
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Cder : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                    (Iic v') v'| ≤
                  Cder * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2)
    (hgradL :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Cder : ℝ) 1) →
                ∀ ξ : TangentSpace ThreeModel z,
                  |scalarDifferential ((Kh k).event (i k)).incoming.flow v' z ξ| ≤
                    Cgrad * ((Kh k).event (i k)).incoming.flow.scalar v' z *
                      Real.sqrt (((Kh k).event (i k)).incoming.flow.scalar v' z) *
                      Real.sqrt
                        ((((Kh k).event (i k)).incoming.flow.base.metric v').inner z ξ ξ))
    (hkappaL :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
            riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
              ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (pT k) 1)) →
          (∀ k, 2 < (Tn k : ℝ)) →
          (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
            q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k) ≤ 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∃ ρ : ℕ → ℝ, Tendsto (fun k => ρ k * Real.sqrt (R k)) atTop atTop ∧
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : Icc (0 : ℝ) (Kh k).horizon,
              t - T / R k ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
              (Kh k).time (i k).castSucc < τ → (τ : ℝ) < (Kh k).time (i k).succ →
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (zz : ((Kh k).stageAt τ).Carrier), HEq zz z →
              ∀ (b : ℝ), 0 < b → b ≤ ρ k →
                (Kh k).isParabolicallyRmControlledBall τ zz b →
                ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                  riemannianVolumeMeasure ThreeModel ((Kh k).stageAt τ).Carrier
                    ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
                    (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage τ) τ) zz b)) :
      ∀ A : ℝ, 0 < A → ∃ QA : ℝ, 0 < QA ∧
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
            riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
              ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (pT k) 1)) →
          (∀ k, 2 < (Tn k : ℝ)) →
          (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
            q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k) ≤ 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ∀ hcross : ((Kh k).event (i k)).RegularCrossing p' q,
          ∀ z ∈ riemannianBallOf ((Kh k).event (i k)).terminal.metric
              ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ (A / Real.sqrt (R k)),
            metricScalarAt ((Kh k).event (i k)).terminal.metric z ≤ QA * R k := by
  intro A hA
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hζ₀, hBw, hmain⟩ :=
    RetainedCoreHistory.terminal_scalar_bound_local_late_guarded_P6HS hεle κ C1 C2 hκ Cder Cgrad
      hphi A hA
      (max 4 Cg)
  refine ⟨2 * Q, by positivity, ?_⟩
  intro ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L
      hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ hceil i hi
  have hrad : (0 : ℝ) < max (2 * Rad) 1 := lt_max_of_lt_right one_pos
  have h3B : (0 : ℝ) < 3 * Bw := by positivity
  have hrec := hrecords Rrad ζ₀ (3 * Bw) Dcap hζ₀
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hpi := hpinch
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hma := hmargin
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hde := hderivL (3 * Bw) (max (2 * Rad) 1) h3B hrad
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hgr := hgradL (3 * Bw) (max (2 * Rad) 1) h3B hrad
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  obtain ⟨ρ, hρlim, hka⟩ := hkappaL (3 * Bw) (max (2 * Rad) 1) h3B hrad
    ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ hceil i hi
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  filter_upwards [hrec, hpi, hde, hgr, hka, hma, hRlim.eventually_ge_atTop (4 * Λ),
    hρlim.eventually_ge_atTop (2 * Λ), hL.eventually_ge_atTop (max (4 * Rad) 1),
    haS 1 one_pos, haS (3 * Bw) h3B] with k hrk hpk hdk hgk hkk hmk hR4 hρk hLk haSk haSk3
  intro p' q hq hcross
  obtain ⟨pp, T₀, records, hcan, hRr', hord, hacc, hT₀, hnotk⟩ := hrk
  have hRk := hRpos k
  have hsR : 0 < Real.sqrt (R k) := Real.sqrt_pos.mpr hRk
  have hLpos : 0 < L k := by linarith [le_max_right (4 * Rad) 1]
  have haσ : (aSeed k : ℝ) < σ k := by
    have := div_pos one_pos hRk
    linarith
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have hσT : (σ k : ℝ) ≤ Tn k := Subtype.coe_le_coe.mpr (hsT k)
  have h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc :=
    (Kh k).activeStage_le_castSucc_P6HE (i k) (aSeed k) (by rw [← hσs]; exact haσ)
  have h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k) :=
    (Kh k).le_activeStage (Tn k) (i k).castSucc (by rw [← hσs] at hcs; linarith)
  have hRx : metricScalarAt ((Kh k).event (i k)).terminal.metric
      ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ = R k := by
    rw [MetricCutCapEvent.RegularCrossing.scalar_eq ((Kh k).event (i k))
        (p := ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩) hcross, hRdef k,
      (Kh k).scalar_eq_of_heq_P6BT (i k) (hi k) hq]
  have hq4 : 4 * R k ≤ max 4 Cg * R k :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hRk.le
  have hCgq : Cg * R k ≤ max 4 Cg * R k :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hRk.le
  have hqpos : 0 < max 4 Cg * R k := mul_pos (lt_max_of_lt_left (by norm_num)) hRk
  have hr : 2 * Rad / Real.sqrt (R k) ≤ L k / (2 * Real.sqrt (R k)) := by
    rw [div_le_div_iff₀ hsR (by positivity)]
    have h4 : 4 * Rad ≤ L k := (le_max_left _ _).trans hLk
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) hsR.le]
  have hδ : 0 < L k / (2 * Real.sqrt (R k)) := by positivity
  have hCN := RetainedCoreHistory.eventually_witness_of_hwin_P6BT
    ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)) (i k) (haT k) (seedTrace k) (hsT k)
    (has k) (hi k) (y k) hRk hLpos haσ (hgood k) h1 h2 p' (hmk p' q hq hcross h1 h2 _ hδ) hr hq4
  have hσ1 : 1 ≤ (σ k : ℝ) := (hone k).trans (Subtype.coe_le_coe.mpr (has k))
  have hΛt : 4 * Λ ≤ R k * (Kh k).time (i k).succ := by
    rw [← hσs]
    nlinarith
  have hball : ∀ (t : ℝ) (z' : ((Kh k).stage (i k).castSucc).Carrier),
      z' ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
        (2 * Rad / Real.sqrt (R k)) →
      z' ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
        (max (2 * Rad) 1 / Real.sqrt (R k)) := fun t z' hz' =>
    lt_of_lt_of_le hz' (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le))
  have hdk' := hdk p' q hq hcross
  have hgk' := hgk p' q hq hcross
  have hkk' := hkk p' q hq hcross
  let records' := records_raise_P6HP2 (H := Kh k) (p := pp) (T₀ := T₀) (1 / 2) records
  exact hmain ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)) (i k) (max T₀ (1 / 2))
    records'
    (fun i' hT b => hcan i' ((le_max_left T₀ (1 / 2)).trans hT) b) hRr' hord hacc
    (hpinch_slot_threshold_P6HP2 (Kh := Kh k) hpk T₀)
    ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ (R k)
    (max 4 Cg * R k) (ρ k) hRx hRk hqpos le_rfl (by linarith) hΛt hρk
    (by rw [hσs] at hT₀ haSk3; exact max_le hT₀ (by linarith [hone k]))
    (hdk'.mono fun t ht first hfl z' hz' B i' hf hij v' hv' hwin hqv hg =>
      ht.1 first hfl z' (hball t z' hz') B i' hf hij v' hv' hwin (lt_of_le_of_lt hCgq hqv) hg)
    (hdk'.mono fun t ht z' hz' v' hv' hwin hqv hg =>
      ht.2 z' (hball t z' hz') v' hv' hwin (lt_of_le_of_lt hCgq hqv) hg)
    (hgk'.mono fun t ht z' hz' v' hv' hwin hqv hg ξ =>
      ht z' (hball t z' hz') v' hv' hwin (lt_of_le_of_lt hCgq hqv) hg ξ)
    (hkk'.mono fun t ht τ hτ1 hτ2 hτ3 hτ4 z' hz' zz hzz b hb0 hbρ hctrl =>
      ht τ hτ1 hτ2 hτ3 hτ4 z' (hball t z' hz') zz hzz b hb0 hbρ hctrl)
    hCN ((hnotk p' q hq hcross).mono fun t ht hex => ht (by
      obtain ⟨i', hT, hl, Btr, b, w, hw⟩ := hex
      exact ⟨i', (le_max_left T₀ (1 / 2)).trans hT, hl, Btr, b, w, hw⟩))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
