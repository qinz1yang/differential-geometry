import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarSupportJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.WeightedCollarAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteJointRayTrace

/-!
# S-CH11-FIX8 port of astra `SmoothCollarTraceEnergy`（`PortC11P`）

来源：donor `SmoothCollarTraceEnergy.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`；思路沿 S-CH11-FIX7 的
`SmoothCollarSupportJets` 与其对本文件的诊断）：
* `/-- docstring -/ attribute [-instance] … in theorem` 的顺序对调（docstring 不能放在
  `attribute … in` 前面）；
* 陈述里所有 `x ^ 2` 写成 `x ^ (2 : ℕ)`（同一个项）：`.metric (T - r ^ 2)` 这类实参里默认 `2 : ℕ`
  的 postponed 实例问题会让整条声明报 `unknown free variable`；
* `𝓝` 写成 `nhds`（namespace 内 `open scoped Topology` 被解析成 `_root_.DifferentialGeometry.Topology`）；
* 陈述里 `hindexInt` 的 `fun r => ((r - s 0) / (v - s 0)) • Pframe i k r`（两处）与 `hfield` 的
  `fun t => (((t - s 0) / (v - s 0)) • Pframe i k t : ThreeSpace)`：`•` 在 `Pframe i k r :
  TangentSpace ThreeModel (alpha i r)` 上触发另一类 `unknown free variable`（逐 binder 二分定位）→ 写成
  `SMul.smul (…) (Pframe i k r : ThreeSpace)`（同一个项）。
* 结论里 `let clock := 2 * v ^ 2 * ST.scalar … q - …`：`binop%` 对叶子 `2`（未定类型的数字字面量）与
  `ST.scalar …` 的统一在 let 链里触发 `unknown free variable`（逐 `let` 二分定位）→ 写
  `(2 : ℝ) * v ^ (2 : ℕ) * …`（同一个项）。
* 结论里 `let Woriginal := ∑ x, ∫ r in …, (1 - (s 0) ^ 2 / r ^ 2) * …`：同类的数字字面量统一问题
  → `((1 : ℝ) - …)`（同一个项）。
* 证明体：`interleaved_actual_flow_joint_families` 补显式 `(P := P)`（typeclass
  `NormedSpace ℝ ?m` stuck，同 FIX7 的 SmoothCollarSupportJets）；两个大 `obtain ⟨…⟩ := H.…`
  （`exists_smooth_collar_cost_support_with_jets`、`interleaved_actual_flow_joint_families`）
  改成 `have h0 := H.…; obtain ⟨…⟩ := h0`（大上下文里项的 elaboration 与模式拆解分开，heartbeat）。
* 证明体里 `Q`、`S0` 等 let 变量：本树 `simp` 不做 zeta-delta，`hslo`/`hshi`/`hsnew`/`hsold`（用
  `interleavedPieceEquiv N` 写）匹配不上目标里的 `Q` → 补 `hslo'` 等 4 条 `Q` 形重述（defeq）并在
  `hsplit'` / `hgeoTag` 的 simp 里换用；`hgeoTag` 的 `fin_cases` 产物 `⟨0, _⟩` 补 `Fin.zero_eta` 与
  `Fin.succ_last`；
* `hvel`：`rw [(hcenter i r hr).mfderiv_eq]` 之后补 `rfl`（同 SmoothCollarSupportJets）；
* `hindexInt` / `hfield` 的 `(by simpa only [hsv] using h)`：statement 里为绕过 `•` 的 elaboration 用了
  `SMul.smul`，simp 后与引理的 `•` 形不同 → `(by simp only [hsv]; exact h)`（`exact` 做 defeq）；
* `htailScalar` / `htailSpeed` 是 `S0 (Q.symm …)` 形，`htrace` 里是 `S (Fin.last …)` 形，`rw` 匹配不上 →
  先用同一证明重述成 `S` 形（defeq）再 `rw`。
* `henergy`：`simpa only [… hAlphaEnd …] using htrace` 的 simp 改不了 `inner (alphaT v) …`（依赖类型位）→ 先
  `rw [hAlphaEnd] at h`（同时改写所有出现）再 `simp only [...] at h; exact h`。
* 陈述里 32 个未被引用的具名 hypothesis binder（`hs`、`hslo`、…、`hvelocityT`）加 `_` 前缀（alpha-重命名，
  同一命题；消 unused-variable 警告；证明体用 `intro` 自己命名，不受影响）。

原路径 `SmoothCollarTraceEnergy` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Bundle Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u uP

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The same actual-history cost support has the original-history weighted
trace energy. Its prefix, joint family, inverse branch and nonzero original
endpoint velocity are preserved. The weighted surgery seams are derived from
the actual pullback metrics and projected central curves. -/
theorem exists_smooth_collar_cost_support_with_trace_energy
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Ioc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ (2 : ℕ) ∈ Ioo (H.time first) (H.stageEndTime first)) (Bfloor : ℝ)
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -Bfloor ≤ metricScalarAt (H.stageMetric j t) x) :
    let Jstage := H.StageInterval first last;
    let Eevent := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : Eevent) : Jstage := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : Eevent) : Jstage := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : Jstage := ⟨first, le_rfl, hle⟩;
    let jl : Jstage := ⟨last, hle, le_rfl⟩;
    ∀ (gamma : (j : Jstage) → ℝ → (H.stage j.val).Carrier) (lo hi : Jstage → ℝ),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      hi jf < v →
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 (lo jl) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
      H.regularizedExtendedAction first last T Bfloor 0 v gamma =
        H.regularizedCost first last hle T Bfloor 0 v (gamma jl 0) (gamma jf v) →
    ∀ (W : (i : Eevent) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (FC : (i : Eevent) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (DO : Jstage → RealTimeInterval) (DS : Eevent → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : Jstage) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (SS : (i : Eevent) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => FC i z.val))
      {N : ℕ} (j : Fin (N + 1) ≃ Jstage) (e : Fin N ≃ Eevent)
      (s : Fin (2 * N + 3) → ℝ) (_hs : StrictMono s)
      (_hslo : ∀ k, s (interleavedPieceEquiv N (.inl k)).castSucc = lo (j k))
      (_hshi : ∀ k, s (interleavedPieceEquiv N (.inl k)).succ = hi (j k))
      (_hsnew : ∀ k, s (interleavedPieceEquiv N (.inr (.inl k))).castSucc = hi (jn (e k)))
      (_hsold : ∀ k, s (interleavedPieceEquiv N (.inr (.inl k))).succ = lo (jo (e k)))
      (_hstail : s (Fin.last (2 * N + 1)).castSucc = hi jf)
      (_hsv : s (Fin.last (2 * N + 2)) = v)
      (alphaO : (x : Jstage) → ℝ → (H.stage x.val).Carrier)
      (alphaS : (i : Eevent) → ℝ → W i) (alphaT : ℝ → (H.stage first).Carrier),
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
    let D : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (Q.symm i);
    let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (D i) :=
      fun i => S0 (Q.symm i);
    let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (Q.symm i);
    let a : Fin (2 * N + 2) → ℝ := fun i => s i.castSucc;
    let b : Fin (2 * N + 2) → ℝ := fun i => s i.succ;
    ∀ (f : (i : Fin (2 * N + 2)) → P × ℝ → M i)
      (_hf : ∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 (f i))
      (_hgeoO : ∀ x, IsLRegularizedGeodesicOn (SO x) T (alphaO x) (Icc (lo x) (hi x)))
      (_hgeoS : ∀ i, IsLRegularizedGeodesicOn (SS i) T (alphaS i) (Icc (hi (jn i)) (lo (jo i))))
      (_hgeoT : IsLRegularizedGeodesicOn ST T alphaT (Icc (hi jf) v))
      (_hcenter : ∀ i r, r ∈ Icc (a i) (b i) → (fun t => f i (0, t)) =ᶠ[nhds r] alpha i)
      (Phi : (i : Fin (2 * N + 1)) →
        PartialDiffeomorph ThreeModel ThreeModel (M i.castSucc) (M i.succ) ∞)
      (_hmetric : ∀ (i : Fin (2 * N + 1)) (x : M i.castSucc), x ∈ (Phi i).source →
        ∀ V W : TangentSpace ThreeModel x,
        ((S i.castSucc).base.metric (T - (b i.castSucc) ^ (2 : ℕ))).inner x V W =
          ((S i.succ).base.metric (T - (a i.succ) ^ (2 : ℕ))).inner (Phi i x)
            (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x V)
            (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x W))
      (_hjoin : ∀ z i, f i.castSucc (z, b i.castSucc) ∈ (Phi i).source ∧
        Phi i (f i.castSucc (z, b i.castSucc)) = f i.succ (z, a i.succ))
      (_hvelocity : ∀ i : Fin (2 * N + 1),
        (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ)
          (alpha i.castSucc (b i.castSucc))
          (lVelocity (I := ThreeModel) (alpha i.castSucc) (b i.castSucc)) : ThreeSpace) =
            lVelocity (I := ThreeModel) (alpha i.succ) (a i.succ))
      (_hfirst : ∀ z, f 0 (z, a 0) = alpha 0 (a 0)),
    let g := (Equiv.piCongrLeft' (fun k => P × ℝ → M0 k) Q).symm f;
    let ordinary : (x : Jstage) → P × ℝ → (H.stage x.val).Carrier :=
      (Equiv.piCongrLeft' (fun x : Jstage => P × ℝ → (H.stage x.val).Carrier) j.symm).symm
        (fun k => g (.inl k));
    let survivor : (i : Eevent) → P × ℝ → W i :=
      (Equiv.piCongrLeft' (fun i : Eevent => P × ℝ → W i) e.symm).symm
        (fun k => g (.inr (.inl k)));
    let tail : P × ℝ → (H.stage first).Carrier := g (.inr (.inr 0));
      (∀ j, IsSolutionOn (SO j)) → (∀ i, IsSolutionOn (SS i)) → IsSolutionOn ST →
      (∀ j t, (SO j).base.metric t = H.stageMetric j.val t) →
      (∀ t, ST.base.metric t = H.stageMetric first t) →
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (FC i z.val)) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (SS i).base.metric (T - r ^ (2 : ℕ)) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ (2 : ℕ)))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (SS i).base.metric (T - r ^ (2 : ℕ)) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ (2 : ℕ)))
            (fun z : W i => FC i z.val) (hnew i)) →
    ∀ (V : Set P), IsOpen V → (0 : P) ∈ V →
    ∀ (KO : Jstage → Set ℝ) (KS : Eevent → Set ℝ) (KT : Set ℝ),
      (∀ j, IsOpen (KO j) ∧ IsPreconnected (KO j) ∧ lo j ∈ KO j ∧ hi j ∈ KO j) →
      (∀ i, IsOpen (KS i) ∧ IsPreconnected (KS i) ∧ hi (jn i) ∈ KS i ∧ lo (jo i) ∈ KS i) →
      IsOpen KT ∧ IsPreconnected KT ∧ hi jf ∈ KT ∧ v ∈ KT →
      (∀ j r, r ∈ KO j → T - r ^ (2 : ℕ) ∈ (DO j).regular) →
      (∀ i r, r ∈ KS i → T - r ^ (2 : ℕ) ∈ (DS i).regular) →
      (∀ r ∈ KT, T - r ^ (2 : ℕ) ∈ DT.regular) →
      (∀ z ∈ V, ordinary jl (z, lo jl) = gamma jl (lo jl)) →
      (∀ z ∈ V, ∀ i, ordinary (jo i) (z, lo (jo i)) =
        (survivor i (z, lo (jo i))).val.val) →
      (∀ z ∈ V, ∀ i, ordinary (jn i) (z, hi (jn i)) =
        FC i (survivor i (z, hi (jn i))).val) →
      (∀ z ∈ V, ordinary jf (z, hi jf) = tail (z, hi jf)) →
      (∀ j, EqOn (fun r => ordinary j (0, r)) (gamma j) (Icc (lo j) (hi j))) →
      (∀ i, EqOn (fun r => (survivor i (0, r)).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => FC i (survivor i (0, r)).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
      EqOn (fun r => tail (0, r)) (gamma jf) (Icc (hi jf) v) →
    ∀ (Bframe : P ≃L[ℝ] ThreeSpace),
      (fun z => tail (z, v)) =ᶠ[nhds (0 : P)]
        (fun z => expMap (ST.base.metric (T - v ^ (2 : ℕ))) (gamma jf v)
          (show TangentSpace ThreeModel (gamma jf v) from Bframe z)) →
    ∀ (basis : Module.Basis (Fin (Module.finrank ℝ ThreeSpace)) ℝ P),
      (∀ i j, (ST.base.metric (T - v ^ (2 : ℕ))).inner (gamma jf v)
        (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis i))
        (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis j)) =
          if i = j then 1 else 0) →
    ∀ (_haCut : 0 < s 0)
      (_hupperCut : T - (s 0) ^ (2 : ℕ) ∈ Icc (H.time last) (H.stageEndTime last))
      (_hloCut : lo jl = s 0)
      (_hboundsCut : ∀ x, H.regularizedStageStart T (s 0) x.val ≤ lo x ∧
        lo x ≤ hi x ∧ hi x ≤ H.regularizedStageEnd T v x.val)
      (Pframe : (i : Fin (2 * N + 2)) → Fin (Module.finrank ℝ ThreeSpace) →
        ∀ r, TangentSpace ThreeModel (alpha i r))
      (_hLag : ∀ i, ContinuousOn (lRegularizedLagrangian (S i) T (alpha i))
        (Icc (a i) (b i)))
      (_hHam : ∀ i, IntervalIntegrable (lHamSq (S i) T (alpha i)) volume (a i) (b i))
      (_hregFrame : ∀ i, ∀ r ∈ Icc (a i) (b i), T - r ^ (2 : ℕ) ∈ (D i).regular)
      (_halphaFrame : ∀ i, ∀ r ∈ Icc (a i) (b i),
        MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel (alpha i) r)
      (_hP : ∀ i k r, r ∈ Icc (a i) (b i) →
        DifferentiableAt ℝ (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
          (I := ThreeModel) (alpha i) (Pframe i k) r) r)
      (_hDP : ∀ i k, IsLAdapted (S i) T (alpha i) (Pframe i k) (Icc (a i) (b i)))
      (_hONframe : ∀ i k l,
        ((S i).base.metric (T - (b i) ^ (2 : ℕ))).inner (alpha i (b i))
          (Pframe i k (b i)) (Pframe i l (b i)) = if k = l then 1 else 0)
      (_hindexInt : ∀ i k, IntervalIntegrable
        (lRegularizedIndexIntegrand (S i) T (alpha i)
          (fun r => (SMul.smul ((r - s 0) / (v - s 0)) (Pframe i k r : ThreeSpace) : ThreeSpace))
          (fun r => (SMul.smul ((r - s 0) / (v - s 0)) (Pframe i k r : ThreeSpace) : ThreeSpace)))
          volume (a i) (b i))
      (_hscalarJoin : ∀ i : Fin (2 * N + 1),
        (S i.castSucc).scalar (T - (b i.castSucc) ^ (2 : ℕ)) (alpha i.castSucc (b i.castSucc)) =
          (S i.succ).scalar (T - (a i.succ) ^ (2 : ℕ)) (alpha i.succ (a i.succ)))
      (_hlagJoin : ∀ i : Fin (2 * N + 1),
        lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) (b i.castSucc) =
          lRegularizedLagrangian (S i.succ) T (alpha i.succ) (a i.succ))
      (_hfield : ∀ i k r, r ∈ Icc (a i) (b i) →
        Filter.EventuallyEq (β := ThreeSpace) (nhds r)
          (fun t => (mfderiv 𝓘(ℝ, P) ThreeModel (fun z => f i (z, t)) 0
            (basis k) : ThreeSpace))
          (fun t => (SMul.smul ((t - s 0) / (v - s 0)) (Pframe i k t : ThreeSpace) : ThreeSpace)))
      (_hvelocityT : lVelocity (I := ThreeModel) alphaT v =
        lVelocity (I := ThreeModel) (gamma jf) v),
    let action : P × ℝ → ℝ := fun z =>
      H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
      (∑ j : Jstage, lRegularizedAction (SO j) T (fun r => ordinary j (z.1, r)) (lo j) (hi j)) +
      (∑ i : Eevent, lRegularizedAction (SS i) T (fun r => survivor i (z.1, r))
        (hi (jn i)) (lo (jo i))) +
      lRegularizedAction ST T (fun r => tail (z.1, r)) (hi jf) z.2;
    ∃ (Jclock : Set ℝ) (U : Set ((H.stage first).Carrier × ℝ))
      (psi : (H.stage first).Carrier × ℝ → P) (F : (H.stage first).Carrier × ℝ → ℝ),
      (IsOpen Jclock ∧ v ∈ Jclock ∧ Jclock ⊆ KT ∧
      (∀ w ∈ Jclock, 0 < w ∧ hi jf < w ∧ T - w ^ (2 : ℕ) ∈ H.stageDomain first) ∧
      ContDiffOn ℝ 2 action (V ×ˢ KT) ∧
      IsOpen U ∧ (gamma jf v, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      psi (gamma jf v, v) = 0 ∧
      F (gamma jf v, v) = ∑ j : Jstage, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) ∧
      H.regularizedCost first last hle T Bfloor 0 v (gamma jl 0) (gamma jf v) =
        (F (gamma jf v, v) : WithTop ℝ) ∧
      ∀ x ∈ U, psi x ∈ V ∧ x.2 ∈ Jclock ∧
        tail (psi x, x.2) = x.1 ∧ F x = action (psi x, x.2) ∧
        H.regularizedCost first last hle T Bfloor 0 x.2 (gamma jl 0) x.1 ≤
          (F x : WithTop ℝ)) ∧
      (∀ z w, action (z, w) =
        H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
          finiteJointAction S T f a b (z, w)) ∧
    let gphys := ST.base.metric (T - v ^ (2 : ℕ))
    let q := gamma jf v
    let velocity : TangentSpace ThreeModel q :=
      show ThreeSpace from lVelocity (I := ThreeModel) (fun r => tail (0, r)) v
    let clock := (2 : ℝ) * v ^ (2 : ℕ) * ST.scalar (T - v ^ (2 : ℕ)) q -
      (1 / 2 : ℝ) * gphys.inner q velocity velocity
    HasMFDerivAt (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) F (q, v)
      ((gphys.inner q velocity).comp (ContinuousLinearMap.fst ℝ ThreeSpace ℝ) +
        clock • ContinuousLinearMap.snd ℝ ThreeSpace ℝ) ∧
    gradientFun gphys (fun y => F (y, v)) q = velocity ∧
    HasDerivAt (fun w => F (q, w)) clock v ∧
    (∀ ξ : P, abstractHessian gphys (fun y => F (y, v)) q
      (show TangentSpace ThreeModel q from Bframe ξ) (show TangentSpace ThreeModel q from Bframe ξ) =
        2 * ∑ i : Fin (2 * N + 2), lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • ξ, r)) 0)
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • ξ, r)) 0) (a i) (b i)) ∧
    laplacian (LeviCivita gphys) gphys (fun y => F (y, v)) q =
      2 * ∑ i : Fin (2 * N + 2), ∑ k : Fin (Module.finrank ℝ ThreeSpace),
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0)
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0) (a i) (b i) ∧
    (∀ ξ : P, (fun u : ℝ => F (expMap gphys q (u • (show TangentSpace ThreeModel q from Bframe ξ)), v))
      =ᶠ[nhds 0] (fun u => H.stageRegularizedAction last T (gamma jl) 0 (lo jl) + finiteJointAction S T f a b (u • ξ, v))) ∧
    let gOriginal := H.stageMetric first (T - v ^ (2 : ℕ))
    let Vorig : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v
    let Woriginal := ∑ x : Jstage,
      ∫ r in H.regularizedStageStart T (s 0) x.val..H.regularizedStageEnd T v x.val,
        ((1 : ℝ) - (s 0) ^ (2 : ℕ) / r ^ (2 : ℕ)) * H.stageRegularizedLagrangian x.val T (gamma x) r
    laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q =
      3 / (v - s 0) - v * metricScalarAt gOriginal q -
        Woriginal / (2 * (v - s 0) ^ (2 : ℕ)) + gOriginal.inner q Vorig Vorig / (4 * v) := by
  classical
  intro Jstage Eevent jo jn jf jl gamma lo hi hbounds hiv hprefixAC hInt hattain
    W FC DO DS DT SO SS ST hold hnew N j e s hs hslo hshi hsnew hsold
    hstail hsv alphaO alphaS alphaT Tag M0 D0 S0 alpha0 Q M D S alpha a b
    f hf hgeoO hgeoS hgeoT hcenter Phi hmetric hjoin hvelocity hfirst g ordinary survivor tail
    hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew
    V hV h0 KO KS KT hKO hKS hKT hregO hregS hregT
    hfix hjoinOld hjoinNew hjoinTail hcenterO hcenterOld hcenterNew hcenterTail
    Bframe hexp basis hON haCut hupperCut hloCut hboundsCut Pframe hLag hHam
    hregFrame halphaFrame hP hDP hONframe hindexInt hscalarJoin hlagJoin hfield hvelocityT action
  obtain ⟨Jclock, U, psi, F, hsupport, hAction, hFD, hgradient, hclock, hhessian,
      hlap, hray⟩ :=
    H.exists_smooth_collar_cost_support_with_jets first last hle hv hupper hpast Bfloor hscalar
      gamma lo hi hbounds hiv hprefixAC hInt hattain W FC DO DS DT SO SS ST hold hnew
      j e s hs hslo hshi hsnew hsold hstail hsv alphaO alphaS alphaT
      f hf hgeoO hgeoS hgeoT hcenter Phi hmetric hjoin hvelocity hfirst
      hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew
      V hV h0 KO KS KT hKO hKS hKT hregO hregS hregT
      hfix hjoinOld hjoinNew hjoinTail hcenterO hcenterOld hcenterNew hcenterTail
      Bframe hexp basis hON
  refine ⟨Jclock, U, psi, F, hsupport, hAction, hFD, hgradient, hclock, hhessian,
    hlap, hray, ?_⟩
  have hg (i : Fin (2 * N + 2)) : g (Q.symm i) = f i :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  have hOrdinary (k : Fin (N + 1)) : ordinary (j k) = g (.inl k) :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  have hSurvivor (k : Fin N) : survivor (e k) = g (.inr (.inl k)) :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  have htailQ : Q (.inr (.inr 0)) = Fin.last (2 * N + 1) :=
    (interleavedPieceEquiv_values N).2.2
  have htailIndex : Q.symm (Fin.last (2 * N + 1)) = (.inr (.inr 0) : Tag) := by
    rw [← htailQ]
    exact Q.symm_apply_apply _
  have hav : s 0 < v := by
    rw [← hsv]
    exact hs (by change 0 < 2 * N + 2; omega)
  have hab (i : Fin (2 * N + 2)) : a i < b i := hs i.castSucc_lt_succ
  have hjoint0 :=
    H.interleaved_actual_flow_joint_families (P := P) first last j e (fun k => W (e k))
      (fun k => DO (j k)) (fun k => DS (e k)) DT (fun k => SO (j k))
      (fun k => SS (e k)) ST (fun k => hSO (j k)) (fun k => hSS (e k)) hST
      (fun k => alphaO (j k)) (fun k => alphaS (e k)) alphaT T s
  obtain ⟨hS, _hSOeq, _hSSeq, _hSTeq, hmap⟩ := hjoint0
  obtain ⟨_hmap, hSmooth, hCenters, _hSplit⟩ := hmap f
  have hSurv (i : Eevent) :
      ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 (survivor i) := by
    obtain ⟨k, rfl⟩ := e.surjective i
    rw [hSurvivor]
    exact (hSmooth hf).2.1 k
  have hSurv1 (i : Eevent) :
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (fun r => survivor i (0, r)) :=
    ((hSurv i).comp (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num)
  have hclockS (i : Eevent) (r : ℝ) (hr : r ∈ Icc (hi (jn i)) (lo (jo i))) :
      T - r ^ (2 : ℕ) ∈ (DS i).carrier :=
    (DS i).regular_subset (hregS i r
      ((hKS i).2.1.ordConnected.out (hKS i).2.2.1 (hKS i).2.2.2 hr))
  let weight : ℝ → ℝ := fun r => 1 - (s 0) ^ (2 : ℕ) / r ^ (2 : ℕ)
  have hweight : ContinuousOn weight (Icc (s 0) v) :=
    continuousOn_const.sub (continuousOn_const.div (continuousOn_id.pow 2)
      (fun r hr => pow_ne_zero 2 (ne_of_gt (haCut.trans_le hr.1))))
  have hOrdEq (x : Jstage) :
      EqOn (fun r => ordinary x (0, r)) (gamma x) (uIoo (lo x) (hi x)) := by
    rw [uIoo_of_le (hbounds x).2.1]
    exact (hcenterO x).mono Ioo_subset_Icc_self
  have hTailEq : EqOn (fun r => tail (0, r)) (gamma jf) (uIoo (hi jf) v) := by
    rw [uIoo_of_le hiv.le]
    exact hcenterTail.mono Ioo_subset_Icc_self
  have hphysical := H.sum_weighted_stage_action_eq_smooth_collar_action_of_physical_projections
    first last hle haCut.le hav.le hupperCut (H.mem_stageDomain_of_mem_Ioo hpast)
    lo hi gamma hboundsCut hloCut hInt weight hweight W FC DS SS hold hnew
    (fun i r => survivor i (0, r)) hSS hclockS hmetricOld hmetricNew hSurv1
    hcenterOld hcenterNew DO DT SO ST (fun x r => ordinary x (0, r))
    (fun r => tail (0, r)) (fun x r _ => hmetricO x (T - r ^ (2 : ℕ)))
    (fun r _ => hmetricT (T - r ^ (2 : ℕ))) hOrdEq hTailEq
  have hOrdSum :
      (∑ x : Jstage, ∫ r in lo x..hi x,
        weight r * lRegularizedLagrangian (SO x) T (fun t => ordinary x (0, t)) r) =
      ∑ k : Fin (N + 1), ∫ r in lo (j k)..hi (j k),
        weight r * lRegularizedLagrangian (SO (j k)) T (fun t => g (.inl k) (0, t)) r := by
    rw [← j.sum_comp (fun x => ∫ r in lo x..hi x,
      weight r * lRegularizedLagrangian (SO x) T (fun t => ordinary x (0, t)) r)]
    simp only [hOrdinary]
  have hSurvSum :
      (∑ i : Eevent, ∫ r in hi (jn i)..lo (jo i),
        weight r * lRegularizedLagrangian (SS i) T (fun t => survivor i (0, t)) r) =
      ∑ k : Fin N, ∫ r in hi (jn (e k))..lo (jo (e k)),
        weight r * lRegularizedLagrangian (SS (e k)) T
          (fun t => g (.inr (.inl k)) (0, t)) r := by
    rw [← e.sum_comp (fun i => ∫ r in hi (jn i)..lo (jo i),
      weight r * lRegularizedLagrangian (SS i) T (fun t => survivor i (0, t)) r)]
    simp only [hSurvivor]
  have hslo' : ∀ k, s (Q (.inl k)).castSucc = lo (j k) := hslo
  have hshi' : ∀ k, s (Q (.inl k)).succ = hi (j k) := hshi
  have hsnew' : ∀ k, s (Q (.inr (.inl k))).castSucc = hi (jn (e k)) := hsnew
  have hsold' : ∀ k, s (Q (.inr (.inl k))).succ = lo (jo (e k)) := hsold
  let Aweight : Tag → ℝ := fun k => ∫ r in (s (Q k).castSucc)..(s (Q k).succ),
    weight r * lRegularizedLagrangian (S0 k) T (fun t => g k (0, t)) r
  have hsum : (∑ i : Fin (2 * N + 2), ∫ r in (a i)..(b i),
      weight r * lRegularizedLagrangian (S i) T (fun t => f i (0, t)) r) =
        ∑ k : Tag, Aweight k := by
    rw [← Q.symm.sum_comp Aweight]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Aweight, Q.apply_symm_apply, hg]
    rfl
  have hsplit := hsum.trans (Fintype.sum_sum_type Aweight)
  have hsplit' : (∑ i : Fin (2 * N + 2), ∫ r in (a i)..(b i),
      weight r * lRegularizedLagrangian (S i) T (fun t => f i (0, t)) r) =
      (∑ k : Fin (N + 1), ∫ r in lo (j k)..hi (j k),
        weight r * lRegularizedLagrangian (SO (j k)) T (fun t => g (.inl k) (0, t)) r) +
      (∑ k : Fin N, ∫ r in hi (jn (e k))..lo (jo (e k)),
        weight r * lRegularizedLagrangian (SS (e k)) T
          (fun t => g (.inr (.inl k)) (0, t)) r) +
      ∫ r in hi jf..v, weight r * lRegularizedLagrangian ST T (fun t => tail (0, t)) r := by
    have h := hsplit
    simp only [Aweight, Fintype.sum_sum_type, Fin.sum_univ_one, S0,
      hslo', hshi', hsnew', hsold', htailQ, hstail, Fin.succ_last, hsv, tail,
      ← add_assoc] at h ⊢
    exact h
  have hfiniteCenter : (∑ i : Fin (2 * N + 2), ∫ r in (a i)..(b i),
      weight r * lRegularizedLagrangian (S i) T (fun t => f i (0, t)) r) =
      ∑ i : Fin (2 * N + 2), ∫ r in (a i)..(b i),
        weight r * lRegularizedLagrangian (S i) T (alpha i) r := by
    apply Finset.sum_congr rfl
    intro i _
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (hab i).le] at hr
    have hpoint : f i (0, r) = alpha i r := (hcenter i r hr).self_of_nhds
    have hvel : lVelocity (I := ThreeModel) (fun t => f i (0, t)) r =
        lVelocity (I := ThreeModel) (alpha i) r := by
      unfold lVelocity
      rw [(hcenter i r hr).mfderiv_eq]
      rfl
    simp only [lRegularizedLagrangian, hvel]
    rw [hpoint]
    rfl
  have hWfinite : (∑ x : Jstage,
      ∫ r in H.regularizedStageStart T (s 0) x.val..H.regularizedStageEnd T v x.val,
        weight r * H.stageRegularizedLagrangian x.val T (gamma x) r) =
      ∑ i : Fin (2 * N + 2), ∫ r in (a i)..(b i),
        weight r * lRegularizedLagrangian (S i) T (alpha i) r := by
    rw [hOrdSum, hSurvSum] at hphysical
    exact hphysical.trans (hsplit'.symm.trans hfiniteCenter)
  have hgeoTag (k : Tag) : IsLRegularizedGeodesicOn (S0 k) T (alpha0 k)
      (Icc (s (Q k).castSucc) (s (Q k).succ)) := by
    rcases k with k | (k | k)
    · have h := hgeoO (j k)
      rw [← hslo' k, ← hshi' k] at h
      exact h
    · have h := hgeoS (e k)
      rw [← hsnew' k, ← hsold' k] at h
      exact h
    · fin_cases k
      have h := hgeoT
      have e1 : s (Q (.inr (.inr 0))).castSucc = hi jf := by
        rw [htailQ]
        exact hstail
      have e2 : s (Q (.inr (.inr 0))).succ = v := by
        rw [htailQ, Fin.succ_last]
        exact hsv
      rw [← e1, ← e2] at h
      exact h
  have hgeoAlpha (i : Fin (2 * N + 2)) :
      IsLRegularizedGeodesicOn (S i) T (alpha i) (Ioo (a i) (b i)) := by
    have hc : IsLRegularizedGeodesicOn (S i) T (alpha i) (Icc (a i) (b i)) := by
      simpa only [Q.apply_symm_apply] using hgeoTag (Q.symm i)
    exact fun r hr => hc r (Ioo_subset_Icc_self hr)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have htrace := sum_lRegularizedIndex_parameter_rays_eq_energy S hS T alpha s
    hs.monotone haCut (by simpa only [hsv] using hav) Pframe hgeoAlpha hLag hHam
    hregFrame halphaFrame hP hDP hONframe (by simp only [hsv]; exact hindexInt)
    hscalarJoin hlagJoin f hf (fun k => basis k) hcenter
    (by simp only [hsv]; exact hfield)
  have htailData (k : Tag) (hk : k = .inr (.inr 0)) :
      (S0 k).scalar (T - v ^ (2 : ℕ)) (alpha0 k v) = ST.scalar (T - v ^ (2 : ℕ)) (alphaT v) ∧
      ((S0 k).base.metric (T - v ^ (2 : ℕ))).inner (alpha0 k v)
        (lVelocity (I := ThreeModel) (alpha0 k) v)
        (lVelocity (I := ThreeModel) (alpha0 k) v) =
      (ST.base.metric (T - v ^ (2 : ℕ))).inner (alphaT v)
        (lVelocity (I := ThreeModel) alphaT v) (lVelocity (I := ThreeModel) alphaT v) := by
    subst k
    exact ⟨rfl, rfl⟩
  have htailScalar := (htailData _ htailIndex).1
  have htailSpeed := (htailData _ htailIndex).2
  have hTailGerm : (fun r => tail (0, r)) =ᶠ[nhds v] alphaT :=
    (hCenters hcenter).2.2 v (by
      change v ∈ Icc (s (⟨2 * N + 1, by omega⟩ : Fin (2 * N + 3)))
        (s (Fin.last (2 * N + 2)))
      have hlo : s (⟨2 * N + 1, by omega⟩ : Fin (2 * N + 3)) = hi jf := hstail
      rw [hlo, hsv]
      exact ⟨hiv.le, le_rfl⟩)
  have hAlphaEnd : alphaT v = gamma jf v :=
    hTailGerm.self_of_nhds.symm.trans (hcenterTail ⟨hiv.le, le_rfl⟩)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hsv' : s (Fin.last (2 * N + 1 + 1)) = v := hsv
  simp only [hsv] at htrace
  rw [hsv'] at htrace
  have htailScalar' : (S (Fin.last (2 * N + 1))).scalar (T - v ^ (2 : ℕ))
      (alpha (Fin.last (2 * N + 1)) v) = ST.scalar (T - v ^ (2 : ℕ)) (alphaT v) :=
    (htailData _ htailIndex).1
  have htailSpeed' : ((S (Fin.last (2 * N + 1))).base.metric (T - v ^ (2 : ℕ))).inner
      (alpha (Fin.last (2 * N + 1)) v)
      (lVelocity (I := ThreeModel) (alpha (Fin.last (2 * N + 1))) v)
      (lVelocity (I := ThreeModel) (alpha (Fin.last (2 * N + 1))) v) =
      (ST.base.metric (T - v ^ (2 : ℕ))).inner (alphaT v)
        (lVelocity (I := ThreeModel) alphaT v) (lVelocity (I := ThreeModel) alphaT v) :=
    (htailData _ htailIndex).2
  rw [htailScalar'] at htrace
  erw [htailSpeed'] at htrace
  rw [← hWfinite] at htrace
  have henergy :
      2 * ∑ i : Fin (2 * N + 2), ∑ k : Fin (Module.finrank ℝ ThreeSpace),
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0)
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0) (a i) (b i) =
      3 / (v - s 0) - v * metricScalarAt (H.stageMetric first (T - v ^ (2 : ℕ))) (gamma jf v) -
        (∑ x : Jstage,
          ∫ r in H.regularizedStageStart T (s 0) x.val..H.regularizedStageEnd T v x.val,
            (1 - (s 0) ^ (2 : ℕ) / r ^ (2 : ℕ)) *
              H.stageRegularizedLagrangian x.val T (gamma x) r) /
          (2 * (v - s 0) ^ (2 : ℕ)) +
        (H.stageMetric first (T - v ^ (2 : ℕ))).inner (gamma jf v)
          (lVelocity (I := ThreeModel) (gamma jf) v)
          (lVelocity (I := ThreeModel) (gamma jf) v) / (4 * v) := by
    have h := htrace
    rw [hAlphaEnd] at h
    simp only [hdim, Nat.cast_ofNat, hvelocityT,
      SolutionOn.scalar, SolutionFamily.scalar, hmetricT, weight] at h
    exact h
  have hlapPhysical :
      laplacian (LeviCivita (H.stageMetric first (T - v ^ (2 : ℕ))))
        (H.stageMetric first (T - v ^ (2 : ℕ))) (fun y => F (y, v)) (gamma jf v) =
      2 * ∑ i : Fin (2 * N + 2), ∑ k : Fin (Module.finrank ℝ ThreeSpace),
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0)
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0) (a i) (b i) := by
    simpa only [hmetricT] using hlap
  exact hlapPhysical.trans henergy

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
