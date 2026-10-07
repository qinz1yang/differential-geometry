import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateCoreP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.S15.WireC11S15

/-!
# S15 的 `hband` ⇐ `CanonicalLateCore_P6X`；selected 反证 ⇐ 纯类反证（O-CH11-P6SEL G3，后缀 `_P6X`）

* `hband_of_canonicalLateCore_P6X`：(b) 最小合同 ⇒ `s15_of_s8_C11S15` 的 `hband`（逐字形；`hband` 的
  `r̄√t < r` 与 band 上界 `R ≤ ρ(t)⁻²` 只是多出的前提，`K₁ T` 不依赖 `r̄`）；
* `s15_of_canonicalLateCore_P6X`：(b) 最小合同 ⇒ S15 = `LargerBallCanonicalLateSupply_C11E`（G2a slice 桥，
  **不经 S8**，D-16/D-18 的依赖图 native → (b) → (c)）；consumer `example`：`a12Enhanced_of_chain_C11P2`
  的 `hext` 里 `hband` 合取项换成 `CanonicalLateCore_P6X`，经 `s15_of_s8_C11S15` 的 `hband` 位给出（型对齐）；
* **`selected_of_pureClass_P6X`**：G2 的缺口 `hP6`（任意 selected 坏序列 ⇒ False）⇐ 只对**纯类**序列的反证
  `hP6'`：(U) event 内部 ∧ `n+1 < R`（G1 主形 P6D 接口）∨ final 内部 ∨ 边界（`¬∃` spatial witness）∨
  `R` 尾有界（D-17 normalization）。证明 = 位置四分子列（`exists_strictMono_interior_or_boundary_P6S`）+
  `R` 子列二分（`exists_strictMono_succ_lt_or_bdd_P6X`）+ selected 数据沿严格单调子列重索引；
* `canonicalLateCore_of_pureClass_P6X`：S5 + S11 + `hP6'` ⇒ `CanonicalLateCore_P6X`。
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set Filter
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

universe u

/-- **(b) 最小合同 ⇒ S15 的 `hband`**（`s15_of_s8_C11S15` 的 binder 逐字形，`ρ` 任意）。 -/
theorem hband_of_canonicalLateCore_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε C1 C2 : ℝ}
    (h : CanonicalLateCore_P6X F ε C1 C2) :
    ∀ A : ℝ, 1 < A → ∀ rbar : ℝ, 0 < rbar → ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → rbar * Real.sqrt t < r → 2 * r ^ 2 < (t : ℝ) →
          hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
            K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
            metricScalarAt (H.stageMetric (H.activeStage t) t) y ≤ (ρ t ^ 2)⁻¹ →
            ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
              W.capTubeHasNeckChart ε := by
  intro A hA rbar _
  obtain ⟨K₁, T, hK₁, hT, hB⟩ := h A (zero_lt_one.trans hA)
  exact ⟨K₁, T, hK₁, hT, fun n t p r hTt _ ht hs hv y hy hK _ => hB n t p r hTt ht hs hv y hy hK⟩

/-- **(b) 最小合同 ⇒ S15**（RegularSlice 形，G2a slice 桥；不经 S8）。 -/
theorem s15_of_canonicalLateCore_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ}
    (h : CanonicalLateCore_P6X F ε C1 C2) :
    LargerBallCanonicalLateSupply_C11E F ε C1 C2 :=
  largerBallCanonicalLateSupply_of_history_C11S15 h

/-- 子列下标：`k + 1 ≤ φ k + 1`。 -/
theorem natCast_succ_le_of_strictMono_P6X {φ : ℕ → ℕ} (hφ : StrictMono φ) (k : ℕ) :
    (k : ℝ) + 1 ≤ (φ k : ℝ) + 1 := by
  have := hφ.id_le k
  have h : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast this
  linarith

/-- **selected 反证 ⇐ 纯类反证**（G2 缺口 `hP6` 的分情形归约）：见文件头。 -/
theorem selected_of_pureClass_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {A : ℝ}
    (hP6' : ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop →
      (((∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) ∧
          ∀ k : ℕ, (k : ℝ) + 1 < R k) ∨
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
        (∀ k, ¬ ∃ W : SpatialCanonicalWitness ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ε C1 C2 (y k), W.capTubeHasNeckChart ε) ∨
        (∃ M : ℝ, ∀ᶠ k in atTop, R k ≤ M)) →
      False) :
    ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop →
      False := by
  intro ind Kh Tn pT r hr hlate htime hsmall hvol aSeed haT hclock seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii
  have key : ∀ φ : ℕ → ℕ, StrictMono φ →
      ((∀ k, ∃ j : Fin (Kh (φ k)).eventCount, (Kh (φ k)).time j.castSucc < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).time j.succ) ∧ ∀ k : ℕ, (k : ℝ) + 1 < R (φ k)) ∨
        (∀ k, (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).horizon) ∨
        (∀ k, ¬ ∃ W : SpatialCanonicalWitness ((Kh (φ k)).stageMetric
            ((Kh (φ k)).activeStage (σ (φ k))) (σ (φ k))) ε C1 C2 (y (φ k)),
          W.capTubeHasNeckChart ε) ∨
        (∃ M : ℝ, ∀ᶠ k in atTop, R (φ k) ≤ M) → False := by
    intro φ hφ hcls
    have hφt := hφ.tendsto_atTop
    exact hP6' (fun k => ind (φ k)) (fun k => Tn (φ k)) (fun k => pT (φ k)) (fun k => r (φ k))
      (fun k => hr (φ k))
      (fun k => (natCast_succ_le_of_strictMono_P6X hφ k).trans (hlate (φ k)))
      (fun k => htime (φ k)) (fun k => hsmall (φ k)) (fun k => hvol (φ k))
      (fun k => aSeed (φ k)) (fun k => haT (φ k)) (fun k => hclock (φ k))
      (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
      (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
      (fun k => hRpos (φ k))
      (fun k => (natCast_succ_le_of_strictMono_P6X hφ k).trans (hRr (φ k)))
      (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
      (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
      (hroom.comp hφt) (hradii.comp hφt) hcls
  have hpos := ObservedHistory.exists_strictMono_interior_or_boundary_P6S (Kh := Kh) σ y hsel
  obtain ⟨ψ, hψ, hcls⟩ := hpos
  rcases hcls with hev | hfin | hbd
  · rcases ObservedHistory.exists_strictMono_succ_lt_or_bdd_P6X (fun k => R (ψ k)) with
      ⟨ψ', hψ', hlt⟩ | ⟨M, hM⟩
    · exact key (fun k => ψ (ψ' k)) (hψ.comp hψ') (Or.inl ⟨fun k => hev (ψ' k), hlt⟩)
    · exact key ψ hψ (Or.inr (Or.inr (Or.inr ⟨M, hM⟩)))
  · exact key ψ hψ (Or.inr (Or.inl hfin))
  · exact key ψ hψ (Or.inr (Or.inr (Or.inl hbd)))

/-- **S5 + S11 + 纯类反证 ⇒ `CanonicalLateCore_P6X`**（G2 ∘ `selected_of_pureClass_P6X`）。 -/
theorem canonicalLateCore_of_pureClass_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hP6' : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop →
      (((∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) ∧
          ∀ k : ℕ, (k : ℝ) + 1 < R k) ∨
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
        (∀ k, ¬ ∃ W : SpatialCanonicalWitness ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ε C1 C2 (y k), W.capTubeHasNeckChart ε) ∨
        (∃ M : ℝ, ∀ᶠ k in atTop, R k ≤ M)) →
      False) :
    CanonicalLateCore_P6X F ε C1 C2 :=
  canonicalLateCore_of_selected_P6X hanti hcan hder fun A hA =>
    selected_of_pureClass_P6X (hP6' A hA)

/-- consumer（S15 型对齐）：`a12Enhanced_of_chain_C11P2` 的 `hext` 里 `hband` 合取项换成
`CanonicalLateCore_P6X F ε C1 C2`，经 `hband_of_canonicalLateCore_P6X` 放进 `s15_of_s8_C11S15` 的
`hband` 位。 -/
example {pBase : CutoffParameters} {C : GC.GeneralFlow.ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (hext : ∃ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g,
      ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
        (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
        F.tower = S.tower ∧ ε = C.epsilon ∧
        (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
          q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy) ∧
        CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
        AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
        HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
        (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
          (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
        Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
        LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) ∧
        LinkedWindowsSupply_C11E records ∧ TimeDerivativeSupply_C11E F q.neckRadius C.Ctime ∧
        LateLinkedRecordsSupply_C11E F q ∧
        CanonicalLateCore_P6X F ε C1 C2 ∧
        StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 ∧
        CompatibleCapsSupply_C11E F q records ∧ FrontierCollarSupply_C11E F q) :
    A12EnhancedConclusion_C11E P g := by
  obtain ⟨S, F, q, κ, records, ε, C1, C2, hF, hε, hq, hconst, hκ, hκanti, hδanti, hρanti, hcan,
    hnc, hδlim, hrecent, hS8, hP1, hP2, hP5, hcore, hStrong, hCompat, hRFC⟩ := hext
  exact a12Enhanced_of_chain_C11P2 hP3 hprof
    ⟨S, F, q, κ, records, ε, C1, C2, hF, hε, hq, hconst, hκ, hκanti, hδanti, hρanti, hcan, hnc,
      hδlim, hrecent, hS8, hP1, hP2, hP5,
      s15_of_s8_C11S15 (largerBallAccuracySupply_diagonal_C11S q hδanti) hS8 hcan
        (hband_of_canonicalLateCore_P6X hcore),
      hStrong, hCompat, hRFC⟩

end GC.LongTime.Ch11
