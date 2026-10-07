import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalCollarReserve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothSurvivorRepresentatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothStageRepresentatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothSurvivorJoins
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.InterleavedJoins

/-!
# S-CH11-FIX8 port of astra `SmoothCollarGeometry`（`PortC11P`）

来源：donor `SmoothCollarGeometry.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（主定理 `unknown free variable`）。

本 port 只有 elaboration 层面修补（no statement / definition / proof idea altered）：
* 所有 `x ^ 2` 写成 `x ^ (2 : ℕ)`（同一个项）：`.metric (T - r ^ 2)` 这类实参里默认 `2 : ℕ`
  的 postponed 实例问题会让整条声明报 `unknown free variable`。

* `choose … using hraw` 在本树 Mathlib 里会清掉 `hraw`（后面还要用）：改 `using id hraw`；
* 4 处 `simpa only [(hjoin i).1] using …`（及 `hhi`、`hTLlit` 同类）：simp 不会展开 `jn i` / `N`
  这类 let 变量，匹配不上 → 改成 `rw [← …] at h; exact h`（`exact` 用 defeq 展开 let）；
* 第一个 `obtain ⟨… 50 个名字 …⟩ := H.exists_physical_collar_reserve_of_attained_action …` 一次拆
  ∃ 链要 ~29 s（整条定理超 200000 heartbeat）：拆成三段 `obtain`（同一模式，分段命名），
  且三个 `obtain … := H.exists_…` 都改成 `have h0 := H.exists_…; obtain … := h0`（大上下文里
  项的 elaboration 与模式拆解分开），整条定理 elaboration 46 s → ~12 s，不用 `set_option`；
* `hg0` 里 `rw [hg0eq, hgeq]` 之后 `rfl` 多余（rw 已用 `rfl` 关掉目标）。

原路径 `SmoothCollarGeometry` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u uP

/-- Produce the actual smooth collar geometry of the original attained curve.
The survivor representatives and positive reserve precede the prefix cutoff.
The resulting interleaved joins retain the physical metrics and original
velocity, and decode pointwise for the same arbitrary-parameter family. -/
theorem exists_smooth_physical_collar_geometry_of_attained_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Ioc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ (2 : ℕ) ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount)
      (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (hC1Atv : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel 1
      (gamma ⟨first, le_rfl, hle⟩) v)
    (hcross : ∀ (i : Fin H.eventCount)
      (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hle⟩;
    let jl : J := ⟨last, hle, le_rfl⟩;
    let N := last.val - first.val;
    ∃ (DT : RealTimeInterval)
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (b lowT highT : ℝ) (alphaT : ℝ → (H.stage first).Carrier),
      IsSolutionOn ST ∧
      (∀ t, ST.base.metric t = H.stageMetric first t) ∧
      0 < b ∧ b < v ∧
      (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b ∧
      lowT < b ∧ v < highT ∧
      (∀ r ∈ Ioo lowT highT, T - r ^ (2 : ℕ) ∈ DT.regular) ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ alphaT ∧
      IsLRegularizedGeodesicOn ST T alphaT (Icc b v) ∧
      EqOn alphaT (gamma jf) (Icc b v) ∧
      alphaT =ᶠ[𝓝 b] gamma jf ∧
      alphaT v = gamma jf v ∧
      lVelocity (I := ThreeModel) alphaT v =
        lVelocity (I := ThreeModel) (gamma jf) v ∧
      lRegularizedAction ST T alphaT b v =
        H.stageRegularizedAction first T (gamma jf) b v ∧
      ∃ (C D : E → ℝ) (hCs : ∀ i, C i < H.time i.val.succ)
        (hsD : ∀ i, H.time i.val.succ < D i)
        (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
        (FC : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
          (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
        (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i)
          (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le))
        (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞
          (fun z : W i => z.val.val))
        (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞
          (fun z : W i => FC i z.val))
        (c0 d0 : E → ℝ) (eta : (i : E) → ℝ → W i),
        (∀ i,
          0 < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < v ∧
          H.time i.val.castSucc < C i ∧ D i < H.stageEndTime i.val.succ ∧
          (FC i).source = W i ∧ IsSolutionOn (SS i) ∧
          (∀ z : W i, (H.event i.val).RegularCrossing z.val.val (FC i z.val)) ∧
          (∀ t ∈ Ico (C i) (H.time i.val.succ), (SS i).base.metric t =
            localPullMetric (H.stageMetric i.val.castSucc t)
              (fun z : W i => z.val.val) (hold i)) ∧
          (∀ t ∈ Icc (H.time i.val.succ) (D i), (SS i).base.metric t =
            localPullMetric (H.stageMetric i.val.succ t)
              (fun z : W i => FC i z.val) (hnew i)) ∧
          (SS i).base.metric (H.time i.val.succ) =
            (H.event i.val).terminal.metric.restrictOpen (W i) ∧
          0 < c0 i ∧ c0 i < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < d0 i ∧ d0 i < v ∧
          H.regularizedStageStart T 0 i.val.succ < c0 i ∧
          d0 i < H.regularizedStageEnd T v i.val.castSucc ∧
          (∀ r ∈ Icc (c0 i) (d0 i), T - r ^ (2 : ℕ) ∈ Ioo (C i) (D i)) ∧
          Manifold.absolutelyContinuousOnInterval ThreeModel (eta i) (c0 i) (d0 i) ∧
          ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (eta i) (Icc (c0 i) (d0 i)) ∧
          IsLRegularizedGeodesicOn (SS i) T (eta i) (Ioo (c0 i) (d0 i)) ∧
          EqOn ((fun z : W i => FC i z.val) ∘ eta i) (gamma (jn i))
            (Icc (c0 i) (Real.sqrt (T - H.time i.val.succ))) ∧
          EqOn ((fun z : W i => z.val.val) ∘ eta i) (gamma (jo i))
            (Icc (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
          IntervalIntegrable (lRegularizedLagrangian (SS i) T (eta i))
            volume (c0 i) (d0 i) ∧
          lRegularizedAction (SS i) T (eta i) (c0 i) (d0 i) =
            H.stageRegularizedAction i.val.succ T (gamma (jn i)) (c0 i)
              (Real.sqrt (T - H.time i.val.succ)) +
            H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
              (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
        ∃ (j : Fin (N + 1) ≃ J) (e : Fin N ≃ E)
          (c d : E → ℝ) (a0 : ℝ),
          j 0 = jl ∧ j (Fin.last N) = jf ∧
          (∀ k, j k.castSucc = jn (e k) ∧ j k.succ = jo (e k)) ∧
          0 < a0 ∧ a0 < b ∧
          (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
            Real.sqrt (T - H.time i.val.succ) < d i ∧ d i < b ∧
            Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i)) ∧
          H.regularizedStageStart T 0 last = 0 ∧
          H.regularizedStageEnd T v first = v ∧
          (∀ x : J, H.regularizedStageStart T 0 x.val <
            H.regularizedStageEnd T v x.val) ∧
          ∃ (lowS highS : E → ℝ) (alphaS : (i : E) → ℝ → W i),
      ((∀ i, lowS i < c i ∧ d i < highS i) ∧
      (∀ i, ∀ r ∈ Ioo (lowS i) (highS i),
        T - r ^ (2 : ℕ) ∈
          (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le).regular) ∧
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alphaS i)) ∧
      (∀ i, ∀ r ∈ Icc (c i) (d i), alphaS i =ᶠ[𝓝 r] eta i) ∧
      (∀ i, IsLRegularizedGeodesicOn (SS i) T (alphaS i) (Icc (c i) (d i))) ∧
      (∀ i, EqOn ((fun z : W i => FC i z.val) ∘ alphaS i) (gamma (jn i))
        (Icc (c i) (Real.sqrt (T - H.time i.val.succ)))) ∧
      (∀ i, EqOn ((fun z : W i => z.val.val) ∘ alphaS i) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (d i))) ∧
      (∀ i, ((fun z : W i => FC i z.val) ∘ alphaS i) =ᶠ[𝓝 (c i)] gamma (jn i)) ∧
      (∀ i, ((fun z : W i => z.val.val) ∘ alphaS i) =ᶠ[𝓝 (d i)] gamma (jo i)) ∧
      (∀ i, EqOn (lRegularizedLagrangian (SS i) T (alphaS i))
        (lRegularizedLagrangian (SS i) T (eta i)) (Icc (c i) (d i))) ∧
      (∀ i, IntervalIntegrable (lRegularizedLagrangian (SS i) T (alphaS i)) volume (c i) (d i)) ∧
      (∀ i, lRegularizedAction (SS i) T (alphaS i) (c i) (d i) =
        H.stageRegularizedAction i.val.succ T (gamma (jn i)) (c i)
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (d i)) ∧
      (∀ i (weight : ℝ → ℝ), ContinuousOn weight (Icc (c i) (d i)) →
        IntervalIntegrable (fun r => weight r * lRegularizedLagrangian (SS i) T (alphaS i) r)
          volume (c i) (d i) ∧
        IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.val.succ T
          (gamma (jn i)) r) volume (c i) (Real.sqrt (T - H.time i.val.succ)) ∧
        IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.val.castSucc T
          (gamma (jo i)) r) volume (Real.sqrt (T - H.time i.val.succ)) (d i) ∧
        (∫ r in (c i)..(d i), weight r * lRegularizedLagrangian (SS i) T (alphaS i) r) =
          (∫ r in (c i)..Real.sqrt (T - H.time i.val.succ), weight r *
            H.stageRegularizedLagrangian i.val.succ T (gamma (jn i)) r) +
          ∫ r in Real.sqrt (T - H.time i.val.succ)..(d i), weight r *
            H.stageRegularizedLagrangian i.val.castSucc T (gamma (jo i)) r)) ∧
          ∀ a ∈ Ioo 0 a0,
            ∃ (lo hi : J → ℝ) (s : Fin (2 * N + 3) → ℝ),
              StrictMono s ∧ s 0 = a ∧ s (Fin.last (2 * N + 2)) = v ∧
              s ⟨2 * N + 1, by omega⟩ = b ∧
              (∀ k, s ⟨2 * k.val, by omega⟩ = lo (j k) ∧
                s ⟨2 * k.val + 1, by omega⟩ = hi (j k)) ∧
              (∀ k, s ⟨2 * k.val + 1, by omega⟩ = c (e k) ∧
                s ⟨2 * k.val + 2, by omega⟩ = d (e k)) ∧
              lo jl = a ∧ hi jf = b ∧
              (∀ i, hi (jn i) = c i ∧ lo (jo i) = d i) ∧
              (∀ x : J, H.regularizedStageStart T 0 x.val < lo x ∧ lo x < hi x ∧
                hi x < H.regularizedStageEnd T v x.val) ∧
              T - a ^ (2 : ℕ) ∈ Icc (H.time last) (H.stageEndTime last) ∧
              (∀ x : J, H.regularizedStageStart T a x.val ≤ lo x ∧ lo x ≤ hi x ∧
                hi x ≤ H.regularizedStageEnd T v x.val) ∧
              Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 a ∧
              ∃ (DO : J → RealTimeInterval)
      (SO : (x : J) → SolutionOn (I := ThreeModel) (M := (H.stage x.val).Carrier) (DO x))
      (alphaO : (x : J) → ℝ → (H.stage x.val).Carrier) (lowO highO : J → ℝ),
      ((∀ x, IsSolutionOn (SO x)) ∧
      (∀ x t, (SO x).base.metric t = H.stageMetric x.val t) ∧
      (∀ x, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alphaO x)) ∧
      (∀ x, ∀ r ∈ Icc (lo x) (hi x), alphaO x =ᶠ[𝓝 r] gamma x) ∧
      (∀ x, EqOn (alphaO x) (gamma x) (Icc (lo x) (hi x))) ∧
      (∀ x, IsLRegularizedGeodesicOn (SO x) T (alphaO x) (Icc (lo x) (hi x))) ∧
      (∀ x, lowO x < lo x ∧ hi x < highO x) ∧
      (∀ x, ∀ r ∈ Ioo (lowO x) (highO x), T - r ^ (2 : ℕ) ∈ (DO x).regular) ∧
      (∀ x, EqOn (lRegularizedLagrangian (SO x) T (alphaO x))
        (H.stageRegularizedLagrangian x.val T (gamma x)) (Icc (lo x) (hi x))) ∧
      (∀ x, lRegularizedAction (SO x) T (alphaO x) (lo x) (hi x) =
        H.stageRegularizedAction x.val T (gamma x) (lo x) (hi x)) ∧
      (∀ x (weight : ℝ → ℝ),
        (∫ r in (lo x)..(hi x), weight r * lRegularizedLagrangian (SO x) T (alphaO x) r) =
          ∫ r in (lo x)..(hi x), weight r * H.stageRegularizedLagrangian x.val T (gamma x) r)) ∧
    let DS : E → RealTimeInterval := fun i =>
      RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le;
    let Tag := Fin (N + 1) ⊕ (Fin N ⊕ Fin 1);
    let M0 : Tag → Type u := ActualPieceCarrier H first last j e (fun k => W (e k));
    let D0 : Tag → RealTimeInterval := Sum.elim (fun k => DO (j k))
      (Sum.elim (fun k => DS (e k)) (fun _ => DT));
    let S0 : (k : Tag) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k) :=
      Sum.rec (fun k => SO (j k)) (Sum.rec (fun k => SS (e k)) (fun _ => ST));
    let alpha0 : (k : Tag) → ℝ → M0 k :=
      Sum.rec (fun k => alphaO (j k)) (Sum.rec (fun k => alphaS (e k)) (fun _ => alphaT));
    let Q := interleavedPieceEquiv N;
    let M : Fin (2 * N + 2) → Type u := fun i => M0 (Q.symm i);
    let Dpiece : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (Q.symm i);
    let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (Dpiece i) :=
      fun i => S0 (Q.symm i);
    let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (Q.symm i);
    let lowFlat : Fin (2 * N + 2) → ℝ := fun i =>
      Sum.elim (fun k => lowO (j k))
        (Sum.elim (fun k => lowS (e k)) (fun _ => lowT)) (Q.symm i);
    let highFlat : Fin (2 * N + 2) → ℝ := fun i =>
      Sum.elim (fun k => highO (j k))
        (Sum.elim (fun k => highS (e k)) (fun _ => highT)) (Q.symm i);
      (∀ i, IsSolutionOn (S i)) ∧
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alpha i)) ∧
      (∀ i, lowFlat i < s i.castSucc ∧ s i.succ < highFlat i) ∧
      (∀ i r, r ∈ Ioo (lowFlat i) (highFlat i) → T - r ^ (2 : ℕ) ∈ (Dpiece i).regular) ∧
      (∀ i, IsLRegularizedGeodesicOn (S i) T (alpha i) (Icc (s i.castSucc) (s i.succ))) ∧
    ∃ Phi : (i : Fin (2 * N + 1)) →
      PartialDiffeomorph ThreeModel ThreeModel (M i.castSucc) (M i.succ) ∞,
      (∀ i : Fin (2 * N + 1),
        let r := s i.castSucc.succ;
        alpha i.castSucc r ∈ (Phi i).source ∧
        Phi i (alpha i.castSucc r) = alpha i.succ r ∧
        (Phi i : M i.castSucc → M i.succ) ∘ alpha i.castSucc =ᶠ[𝓝 r] alpha i.succ ∧
        (∀ x ∈ (Phi i).source, ∀ V W : TangentSpace ThreeModel x,
          ((S i.castSucc).base.metric (T - r ^ (2 : ℕ))).inner x V W =
            ((S i.succ).base.metric (T - r ^ (2 : ℕ))).inner (Phi i x)
              (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x V)
              (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x W)) ∧
        (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ)
          (alpha i.castSucc r) (lVelocity (I := ThreeModel) (alpha i.castSucc) r) : ThreeSpace) =
            lVelocity (I := ThreeModel) (alpha i.succ) r ∧
        (S i.castSucc).scalar (T - r ^ (2 : ℕ)) (alpha i.castSucc r) =
          (S i.succ).scalar (T - r ^ (2 : ℕ)) (alpha i.succ r) ∧
        lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) r =
          lRegularizedLagrangian (S i.succ) T (alpha i.succ) r) ∧
      ∀ (P : Type uP) (f : (i : Fin (2 * N + 2)) → P × ℝ → M i),
    let g := (Equiv.piCongrLeft' (fun k => P × ℝ → M0 k) Q).symm f;
    let ordinary : (x : J) → P × ℝ → (H.stage x.val).Carrier :=
      (Equiv.piCongrLeft' (fun x : J => P × ℝ → (H.stage x.val).Carrier) j.symm).symm
        (fun k => g (.inl k));
    let survivor : (i : E) → P × ℝ → W i :=
      (Equiv.piCongrLeft' (fun i : E => P × ℝ → W i) e.symm).symm
        (fun k => g (.inr (.inl k)));
    let tail : P × ℝ → (H.stage first).Carrier := g (.inr (.inr 0));
      ∀ z : P,
        (∀ i : Fin (2 * N + 1),
          f i.castSucc (z, s i.castSucc.succ) ∈ (Phi i).source ∧
          Phi i (f i.castSucc (z, s i.castSucc.succ)) =
            f i.succ (z, s i.succ.castSucc)) →
        (∀ i, ordinary (jn i) (z, hi (jn i)) = FC i (survivor i (z, hi (jn i))).val) ∧
        (∀ i, ordinary (jo i) (z, lo (jo i)) = (survivor i (z, lo (jo i))).val.val) ∧
        ordinary jf (z, hi jf) = tail (z, hi jf) := by
  classical
  intro J E jo jn jf jl N
  have hres0 := H.exists_physical_collar_reserve_of_attained_action first last hle hv
    hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin hC1Atv hcross
  obtain ⟨DT, ST, b, lowT, highT, alphaT, hST, hmetricT, hb0, hbv, hmb,
      hlowT, hhighT, hregT, hsmT, hgeoT, hcenterT, hGermT, hvalueT, hvelocityT,
      hactionT, hres1⟩ := hres0
  obtain ⟨C, D, hCs, hsD, W, FC, SS, hold, hnew, c0, d0, eta, hraw, hres2⟩ := hres1
  obtain ⟨j, e, c, d, a0, hj0, hjLast, hjEvent, ha0, ha0b, hcollar, hstart, hend,
      hpositive, hpieces⟩ := hres2
  choose _hw0 _hwv _hC _hD _hSource hSS _hCross hmetricOld hmetricNew
    _hmetricEvent _hc00 _hc0w _hwd0 _hd0v _hnewClip _holdClip hrawPhysical
    hACeta _hC1eta hGeoeta hProjNew hProjOld hInteta _hActioneta using id hraw
  have hsurvivorCut (i : E) : 0 ≤ c i ∧
      c i < Real.sqrt (T - H.time i.val.succ) ∧
      Real.sqrt (T - H.time i.val.succ) < d i ∧ Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i) := by
    rcases hcollar i with ⟨hac, hcw, hwd, _, hsub⟩
    exact ⟨(ha0.trans hac).le, hcw, hwd, hsub⟩
  have hsurv0 := H.exists_smooth_prefix_survivor_representatives first last last le_rfl
    gamma T C D hCs hsD W FC SS hold hnew c0 d0 c d eta hSS hmetricOld hmetricNew
    hACeta hInteta hGeoeta hProjNew hProjOld hsurvivorCut hrawPhysical
  obtain ⟨lowS, highS, alphaS, hsurvivorData⟩ := hsurv0
  have hsurvivorData' := hsurvivorData
  rcases hsurvivorData' with ⟨hmarginS, hregS, hsmS, _hGermEta, hgeoS,
    hcenterNew, hcenterOld, hGermNew, hGermOld, _hLagEta, _hIntS, _hActionS, _hWeightedS⟩
  refine ⟨DT, ST, b, lowT, highT, alphaT, hST, hmetricT, hb0, hbv, hmb,
    hlowT, hhighT, hregT, hsmT, hgeoT, hcenterT, hGermT, hvalueT, hvelocityT,
    hactionT, C, D, hCs, hsD, W, FC, SS, hold, hnew, c0, d0, eta, hraw,
    j, e, c, d, a0, hj0, hjLast, hjEvent, ha0, ha0b, hcollar, hstart, hend,
    hpositive, lowS, highS, alphaS, hsurvivorData, ?_⟩
  intro a ha
  obtain ⟨lo, hi, s, hs, hs0, hsv, hsb, hsO, hsS, hlo, hhi, hjoin, hgap,
      hupperCut, hboundsCut, hprefixAC⟩ := hpieces a ha
  have hupperClosed : T ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨hupper.1.le, hupper.2⟩
  have hscalarClock : ∀ x : J,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 x.val) (H.regularizedStageEnd T v x.val),
      ∀ y : (H.stage x.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric x.val (T - r ^ (2 : ℕ))) y := by
    intro x r hr y
    exact hscalar x.val (T - r ^ (2 : ℕ)) (H.mapsTo_regularizedStage_Ioo T 0 v x.val hr) y
  have hord0 := H.exists_smooth_prefix_stage_representatives first last hle hv
    hupperClosed hpast hscalarClock gamma hgammaAC hgammaInt hgammaNodes hmin last le_rfl
    lo hi (fun x => ⟨(hgap x).1, (hgap x).2.1.le, (hgap x).2.2⟩)
  obtain ⟨DO, SO, alphaO, lowO, highO, hordinaryData⟩ := hord0
  have hordinaryData' := hordinaryData
  rcases hordinaryData' with ⟨hSO, hmetricO, hsmO, hGermO, _hcenterO, hgeoO,
    hmarginO, hregO, _hLagO, _hActionO, _hWeightedO⟩
  refine ⟨lo, hi, s, hs, hs0, hsv, hsb, hsO, hsS, hlo, hhi, hjoin, hgap,
    hupperCut, hboundsCut, hprefixAC, DO, SO, alphaO, lowO, highO, hordinaryData, ?_⟩
  intro DS Tag M0 D0 S0 alpha0 Q M Dpiece S alpha lowFlat highFlat
  have hbounds (x : J) : H.regularizedStageStart T 0 x.val ≤ lo x ∧ lo x ≤ hi x ∧
      hi x ≤ H.regularizedStageEnd T v x.val :=
    ⟨(hgap x).1.le, (hgap x).2.1.le, (hgap x).2.2.le⟩
  have hstrict (i : E) : hi (jn i) < Real.sqrt (T - H.time i.val.succ) ∧
      Real.sqrt (T - H.time i.val.succ) < lo (jo i) := by
    rw [(hjoin i).1, (hjoin i).2]
    exact ⟨(hcollar i).2.1, (hcollar i).2.2.1⟩
  have hphysical (i : E) (r : ℝ) (hr : r ∈ Icc (hi (jn i)) (lo (jo i))) :
      T - r ^ (2 : ℕ) ∈ Ioo (C i) (D i) := by
    rw [(hjoin i).1, (hjoin i).2] at hr
    exact hrawPhysical i r (Ioo_subset_Icc_self ((hcollar i).2.2.2.2 hr))
  have hGermNew' (i : E) : ((fun z : W i => FC i z.val) ∘ alphaS i)
      =ᶠ[𝓝 (hi (jn i))] gamma (jn i) := by
    have h := hGermNew i
    rw [← (hjoin i).1] at h
    exact h
  have hGermOld' (i : E) : ((fun z : W i => z.val.val) ∘ alphaS i)
      =ᶠ[𝓝 (lo (jo i))] gamma (jo i) := by
    have h := hGermOld i
    rw [← (hjoin i).2] at h
    exact h
  have hOL (k : Fin (N + 1)) : s (Q (.inl k)).castSucc = lo (j k) := (hsO k).1
  have hOR (k : Fin (N + 1)) : s (Q (.inl k)).succ = hi (j k) := (hsO k).2
  have hSL (k : Fin N) : s (Q (.inr (.inl k))).castSucc = hi (jn (e k)) :=
    (hsS k).1.trans (hjoin (e k)).1.symm
  have hSR (k : Fin N) : s (Q (.inr (.inl k))).succ = lo (jo (e k)) :=
    (hsS k).2.trans (hjoin (e k)).2.symm
  have hjn (k : Fin N) : j k.castSucc = jn (e k) := (hjEvent k).1
  have hjo (k : Fin N) : j k.succ = jo (e k) := (hjEvent k).2
  have hc (i : E) : 0 ≤ hi (jn i) :=
    (Real.sqrt_nonneg _).trans ((hbounds (jn i)).1.trans (hbounds (jn i)).2.1)
  choose Fn0 Fo0 hEqN0 hEqO0 hgeomN0 hgeomO0 using fun i : E =>
    H.exists_smooth_survivor_directed_joins i.val
      ((H.time_strictMono.monotone i.property.2).trans hupperClosed.1) (hc i)
      (hstrict i).1 (hstrict i).2 (W i) (FC i) (SS i) (SO (jn i)) (SO (jo i))
      (hold i) (hnew i) (hmetricO (jn i)) (hmetricO (jo i)) (hmetricOld i) (hmetricNew i)
      (hphysical i _ ⟨le_rfl, ((hstrict i).1.trans (hstrict i).2).le⟩)
      (hphysical i _ ⟨((hstrict i).1.trans (hstrict i).2).le, le_rfl⟩)
      (alphaS i) (alphaO (jn i)) (gamma (jn i)) (alphaO (jo i)) (gamma (jo i))
      ((hsmS i).mdifferentiableAt (by simp)) ((hsmS i).mdifferentiableAt (by simp))
      (hGermNew' i) (hGermOld' i)
      (hGermO (jn i) _ ⟨(hbounds (jn i)).2.1, le_rfl⟩)
      (hGermO (jo i) _ ⟨le_rfl, (hbounds (jo i)).2.1⟩)
  have hN (i : E) (x : J) (hx : x = jn i) (r : ℝ) (hr : r = hi (jn i)) :
      ∃ F : PartialDiffeomorph ThreeModel ThreeModel (W i) (H.stage x.val).Carrier ∞,
        EqOn (fun z : W i => cast (congrArg (fun x : J => (H.stage x.val).Carrier) hx.symm)
          (FC i z.val)) F F.source ∧
        (alphaO x) r ∈ F.symm.source ∧
        (F.symm : _ → _) ∘ (alphaO x) =ᶠ[𝓝 r] (alphaS i) ∧
        (∀ y ∈ F.symm.source, ∀ V W : TangentSpace ThreeModel y,
          ((SO x).base.metric (T - r ^ (2 : ℕ))).inner y V W =
            ((SS i).base.metric (T - r ^ (2 : ℕ))).inner (F.symm y)
              (mfderiv ThreeModel ThreeModel (F.symm : _ → _) y V)
              (mfderiv ThreeModel ThreeModel (F.symm : _ → _) y W)) ∧
        (mfderiv ThreeModel ThreeModel (F.symm : _ → _) ((alphaO x) r)
          (lVelocity (I := ThreeModel) (alphaO x) r) : ThreeSpace) =
            lVelocity (I := ThreeModel) (alphaS i) r ∧
        (SO x).scalar (T - r ^ (2 : ℕ)) ((alphaO x) r) =
          (SS i).scalar (T - r ^ (2 : ℕ)) ((alphaS i) r) ∧
        lRegularizedLagrangian (SO x) T (alphaO x) r =
          lRegularizedLagrangian (SS i) T (alphaS i) r := by
    subst x
    subst r
    exact ⟨Fn0 i, hEqN0 i, hgeomN0 i⟩
  have hO (i : E) (x : J) (hx : x = jo i) (r : ℝ) (hr : r = lo (jo i)) :
      ∃ F : PartialDiffeomorph ThreeModel ThreeModel (W i) (H.stage x.val).Carrier ∞,
        EqOn (fun z : W i => cast (congrArg (fun x : J => (H.stage x.val).Carrier) hx.symm)
          z.val.val) F F.source ∧
        (alphaS i) r ∈ F.source ∧
        (F : _ → _) ∘ (alphaS i) =ᶠ[𝓝 r] (alphaO x) ∧
        (∀ y ∈ F.source, ∀ V W : TangentSpace ThreeModel y,
          ((SS i).base.metric (T - r ^ (2 : ℕ))).inner y V W =
            ((SO x).base.metric (T - r ^ (2 : ℕ))).inner (F y)
              (mfderiv ThreeModel ThreeModel (F : _ → _) y V)
              (mfderiv ThreeModel ThreeModel (F : _ → _) y W)) ∧
        (mfderiv ThreeModel ThreeModel (F : _ → _) ((alphaS i) r)
          (lVelocity (I := ThreeModel) (alphaS i) r) : ThreeSpace) =
            lVelocity (I := ThreeModel) (alphaO x) r ∧
        (SS i).scalar (T - r ^ (2 : ℕ)) ((alphaS i) r) =
          (SO x).scalar (T - r ^ (2 : ℕ)) ((alphaO x) r) ∧
        lRegularizedLagrangian (SS i) T (alphaS i) r =
          lRegularizedLagrangian (SO x) T (alphaO x) r := by
    subst x
    subst r
    exact ⟨Fo0 i, hEqO0 i, hgeomO0 i⟩
  choose Fn hEqn hgeomNew using fun k : Fin N => hN (e k) (j k.castSucc) (hjn k)
    (s (interleavedPieceEquiv N (.inr (.inl k))).castSucc) (hSL k)
  choose Fo hEqo hgeomOld using fun k : Fin N => hO (e k) (j k.succ) (hjo k)
    (s (interleavedPieceEquiv N (.inr (.inl k))).succ) (hSR k)
  have htail : alphaO jf =ᶠ[𝓝 (hi jf)] alphaT :=
    (hGermO jf (hi jf) ⟨(hbounds jf).2.1, le_rfl⟩).trans (by
      have h := hGermT.symm
      rw [← hhi] at h
      exact h)
  have hTL : s (Fin.last (2 * N + 1)).castSucc = hi jf := hsb.trans hhi.symm
  have hTLlit : s ⟨2 * N + 1, by omega⟩ = hi jf := hTL
  let newProjection (k : Fin N) (z : W (e k)) : (H.stage (j k.castSucc).val).Carrier :=
    cast (congrArg (fun x : J => (H.stage x.val).Carrier) (hjn k).symm) (FC (e k) z.val)
  let oldProjection (k : Fin N) (z : W (e k)) : (H.stage (j k.succ).val).Carrier :=
    cast (congrArg (fun x : J => (H.stage x.val).Carrier) (hjo k).symm) z.val.val
  have hjfirst : (j (Fin.last N)).val = first := congrArg Subtype.val hjLast
  obtain ⟨Phi, hPhi, _, _, _, hcompat⟩ := H.exists_interleaved_actual_joins first last
    j e hjfirst (fun k => W (e k)) (fun k => DO (j k)) (fun k => DS (e k)) DT
    (fun k => SO (j k)) (fun k => SS (e k)) ST (hmetricO (j (Fin.last N))) hmetricT
    (fun k => alphaO (j k)) (fun k => alphaS (e k)) alphaT T s Fn Fo
    newProjection oldProjection hEqn hEqo
    (by
      have heq : HEq (hjfirst ▸ alphaO (j (Fin.last N))) (alphaO jf) :=
        eqRec_heq_iff.mpr (congr_arg_heq alphaO hjLast)
      rw [eq_of_heq heq]
      rw [← hTLlit] at htail
      exact htail) hgeomNew hgeomOld
  have hqTail : Q (.inr (.inr 0)) = Fin.last (2 * N + 1) :=
    (interleavedPieceEquiv_values N).2.2
  let low0 : Tag → ℝ := Sum.elim (fun k => lowO (j k))
    (Sum.elim (fun k => lowS (e k)) (fun _ => lowT))
  let high0 : Tag → ℝ := Sum.elim (fun k => highO (j k))
    (Sum.elim (fun k => highS (e k)) (fun _ => highT))
  have hSol0 (k : Tag) : IsSolutionOn (S0 k) := by
    rcases k with k | (k | k)
    · exact hSO (j k)
    · exact hSS (e k)
    · exact hST
  have hsm0 (k : Tag) : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alpha0 k) := by
    rcases k with k | (k | k)
    · exact hsmO (j k)
    · exact hsmS (e k)
    · exact hsmT
  have hlo0 (k : Tag) : low0 k < s (Q k).castSucc := by
    rcases k with k | (k | k)
    · simpa only [low0, Sum.elim, hOL] using (hmarginO (j k)).1
    · change lowS (e k) < s (Q (.inr (.inl k))).castSucc
      rw [hSL, (hjoin (e k)).1]
      exact (hmarginS (e k)).1
    · fin_cases k
      change lowT < s (Q (.inr (.inr 0))).castSucc
      rw [hqTail, hTL, hhi]
      exact hlowT
  have hhi0 (k : Tag) : s (Q k).succ < high0 k := by
    rcases k with k | (k | k)
    · simpa only [high0, Sum.elim, hOR] using (hmarginO (j k)).2
    · change s (Q (.inr (.inl k))).succ < highS (e k)
      rw [hSR, (hjoin (e k)).2]
      exact (hmarginS (e k)).2
    · fin_cases k
      change s (Q (.inr (.inr 0))).succ < highT
      rw [hqTail, Fin.succ_last, hsv]
      exact hhighT
  have hreg0 (k : Tag) : ∀ r ∈ Ioo (low0 k) (high0 k), T - r ^ (2 : ℕ) ∈ (D0 k).regular := by
    rcases k with k | (k | k)
    · exact hregO (j k)
    · exact hregS (e k)
    · exact hregT
  have hgeo0 (k : Tag) : IsLRegularizedGeodesicOn (S0 k) T (alpha0 k)
      (Icc (s (Q k).castSucc) (s (Q k).succ)) := by
    rcases k with k | (k | k)
    · intro r hr
      rw [hOL, hOR] at hr
      exact hgeoO (j k) r hr
    · intro r hr
      rw [hSL, hSR, (hjoin (e k)).1, (hjoin (e k)).2] at hr
      exact hgeoS (e k) r hr
    · fin_cases k
      change IsLRegularizedGeodesicOn ST T alphaT
        (Icc (s (Q (.inr (.inr 0))).castSucc) (s (Q (.inr (.inr 0))).succ))
      rw [hqTail, hTL, hhi, Fin.succ_last, hsv]
      exact hgeoT
  refine ⟨(fun i => hSol0 (Q.symm i)), (fun i => hsm0 (Q.symm i)), ?_,
    (fun i => hreg0 (Q.symm i)), ?_, Phi, hPhi, ?_⟩
  · intro i
    constructor
    · simpa only [Q.apply_symm_apply] using hlo0 (Q.symm i)
    · simpa only [Q.apply_symm_apply] using hhi0 (Q.symm i)
  · intro i
    simpa only [Q.apply_symm_apply] using hgeo0 (Q.symm i)
  · intro P f g ordinary survivor tail z hf
    let f0 : (i : Fin (2 * N + 2)) → ℝ → ℝ → M i := fun i _ r => f i (z, r)
    let g0 := (Equiv.piCongrLeft' (fun k => ℝ → ℝ → M0 k) Q).symm f0
    have hg0eq (i : Fin (2 * N + 2)) : g0 (Q.symm i) = f0 i :=
      Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
    have hgeq (i : Fin (2 * N + 2)) : g (Q.symm i) = f i :=
      Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
    have hg0 (k : Tag) (r : ℝ) : g0 k 0 r = g k (z, r) := by
      obtain ⟨i, rfl⟩ := Q.symm.surjective k
      rw [hg0eq, hgeq]
    obtain ⟨hN, hO, hT⟩ := hcompat f0 0 (fun i => hf i)
    have hOeq (k) : ordinary (j k) = g (.inl k) :=
      Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
    have hSeq (k) : survivor (e k) = g (.inr (.inl k)) :=
      Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
    change (∀ k : Fin N,
      newProjection k (g0 (.inr (.inl k)) 0 (s ⟨2 * k.val + 1, by omega⟩)) =
        g0 (.inl k.castSucc) 0 (s ⟨2 * k.val + 1, by omega⟩)) at hN
    change (∀ k : Fin N,
      oldProjection k (g0 (.inr (.inl k)) 0 (s ⟨2 * k.val + 2, by omega⟩)) =
        g0 (.inl k.succ) 0 (s ⟨2 * k.val + 2, by omega⟩)) at hO
    change HEq (g0 (.inl (Fin.last N)) 0 (s ⟨2 * N + 1, by omega⟩))
      (g0 (.inr (.inr 0)) 0 (s ⟨2 * N + 1, by omega⟩)) at hT
    simp only [hg0] at hN hO hT
    refine ⟨?_, ?_, ?_⟩
    · intro i
      obtain ⟨k, rfl⟩ := e.surjective i
      have hh := (heq_of_eq (hN k)).symm.trans (cast_heq _ _)
      change HEq (g (.inl k.castSucc) (z, s ⟨2 * k.val + 1, by omega⟩))
        (FC (e k) (g (.inr (.inl k)) (z, s ⟨2 * k.val + 1, by omega⟩)).val) at hh
      have hc : s ⟨2 * k.val + 1, by omega⟩ = hi (jn (e k)) := hSL k
      rw [hc, ← hOeq, ← hSeq] at hh
      exact eq_of_heq ((congr_arg_heq
        (fun x => ordinary x (z, hi (jn (e k)))) (hjn k).symm).trans hh)
    · intro i
      obtain ⟨k, rfl⟩ := e.surjective i
      have hh := (heq_of_eq (hO k)).symm.trans (cast_heq _ _)
      change HEq (g (.inl k.succ) (z, s ⟨2 * k.val + 2, by omega⟩))
        ((g (.inr (.inl k)) (z, s ⟨2 * k.val + 2, by omega⟩)).val.val) at hh
      have hc : s ⟨2 * k.val + 2, by omega⟩ = lo (jo (e k)) := hSR k
      rw [hc, ← hOeq, ← hSeq] at hh
      exact eq_of_heq ((congr_arg_heq
        (fun x => ordinary x (z, lo (jo (e k)))) (hjo k).symm).trans hh)
    · have hh := hT
      change HEq (g (.inl (Fin.last N)) (z, s ⟨2 * N + 1, by omega⟩))
        (tail (z, s ⟨2 * N + 1, by omega⟩)) at hh
      rw [hTLlit, ← hOeq] at hh
      exact eq_of_heq ((congr_arg_heq
        (fun x => ordinary x (z, hi jf)) hjLast.symm).trans hh)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
