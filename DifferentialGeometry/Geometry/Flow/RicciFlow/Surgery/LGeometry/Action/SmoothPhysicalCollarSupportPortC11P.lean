import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarTraceEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmallPrefixTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalClockSupport

/-!
# S-CH11-FIX9 port of astra `SmoothPhysicalCollarSupport`（`PortC11P`）

来源：donor `SmoothPhysicalCollarSupport.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`；思路沿 S-CH11-FIX8 对 `SmoothCollarTraceEnergy` 的修补）：
* `/-- docstring -/ attribute [-instance] … in theorem` 的顺序对调（docstring 不能放在
  `attribute … in` 前面）；
* 陈述里所有 `x ^ 2` 写成 `x ^ (2 : ℕ)`（同一个项）：陈述里 `.metric (T - v ^ 2)` 等实参的默认 `2 : ℕ`
  postponed 实例让整条声明的 elaboration 用尽 200000 heartbeat（`synthesize pending MVars`；
  FIX7 / FIX8 对同族 `SmoothCollarSupportJets` / `SmoothCollarTraceEnergy` 的同一修法）。
* `𝓝` 写成 `nhds`（`=ᶠ[𝓝 …]` 与 `(𝓝 r)`；同 FIX8 对 TraceEnergy 的处理）；
* 陈述里 `hindexInt` 的 `fun r => ((r - s 0) / (v - s 0)) • Pframe i k r`（两处）与 `hfield` 的
  `fun t => (((t - s 0) / (v - s 0)) • Pframe i k t : ThreeSpace)`：`•` 在
  `Pframe i k r : TangentSpace ThreeModel (alpha i r)` 上触发 `unknown free variable`
  （FIX8 对 TraceEnergy 逐 binder 二分定位的同一处）→ 写成 `SMul.smul (…) (Pframe i k r : ThreeSpace)`；
* `H.interleaved_actual_flow_joint_families …` 的隐式 `P` 推不出（`typeclass instance problem is
  stuck NormedSpace ℝ ?m`）→ 显式 `(P := P)`，并先 `have hjoint0 := …` 再 `obtain`（同 FIX8）；
* `hTailVelocity`：`calc _ = … := by unfold lVelocity; rw […]` 的首项 `_` 不再由目标确定（`Trans Eq Eq ?m`）
  → 先 `have h1 : … = lVelocity alphaT v`（`rw [germ.mfderiv_eq]` 之后剩 `tangentSpaceCast` 的恒等，补 `rfl`，
  同 FIX8 对 TraceEnergy 的处理），`exact h1.trans hvelocityT`；
* `hgradientOriginal` / `hclockOriginal` 的 `simpa only [… hTailVelocity] using h…`：simp 把
  `tail`（let）展开成 `(Equiv.piCongrLeft' …).symm f …` 后 `hTailVelocity`（用 `tail` 陈述）匹配不上 → 先把
  `hgradient` / `hclock` 写成 `tail` 形的显式类型（defeq，`have this := …; this` 与 `tail` 都是 let），
  再 `rw [hTailVelocity]`，其余沿用原 simp 集；
* 末尾 `field_simp [hv.ne'] <;> ring`：`field_simp` 已关掉目标，`ring` 永不执行 → 删去 `<;> ring`；
* 陈述里 31 个只在 `intro` 里引用的 binder 名（`hs hsCut hslo hshi hsnew hsold hstail hsv hf hgeoO
  hgeoS hgeoT hcenter hmetric hjoin hvelocity hfirst hloCut hboundsCut hLag hHam hregFrame
  halphaFrame hP hDP hONframe hindexInt hscalarJoin hlagJoin hfield hvelocityT`）→ 加 `_` 前缀
  （unusedVariables；binder 名不改变陈述）。
* `Woriginal` 积分里的叶子 `1`（未定类型数字字面量）→ `(1 : ℝ)`。

原路径 `SmoothPhysicalCollarSupport` 是只 import 本文件的 re-export shim。
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
/-- Choose the trace error and positive prefix before the actual collar family,
then use one original-history support in physical time. Its metric and endpoint
velocity remain the original ones. This receives an actual minimizing family;
it does not construct that family or assume that its endpoint velocity vanishes. -/
theorem exists_smooth_physical_collar_cost_support
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
    ∀ (gamma : (j : Jstage) → ℝ → (H.stage j.val).Carrier),
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
      H.regularizedExtendedAction first last T Bfloor 0 v gamma =
        H.regularizedCost first last hle T Bfloor 0 v (gamma jl 0) (gamma jf v) →
    ∀ {rho eta : ℝ}, 0 < rho → 0 < eta →
    let epsilon := eta / (2 * v);
    ∃ aCut : ℝ, 0 < aCut ∧ aCut < rho ∧ aCut < v ∧
      T - aCut ^ (2 : ℕ) ∈ Icc (H.time last) (H.stageEndTime last) ∧
    ∀ (lo hi : Jstage → ℝ),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      hi jf < v →
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 (lo jl) →
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
      (s : Fin (2 * N + 3) → ℝ) (_hs : StrictMono s) (_hsCut : s 0 = aCut)
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
    ∀ (_hloCut : lo jl = s 0)
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
    let q := gamma jf v
    let Loriginal := ∑ x : Jstage, H.stageRegularizedAction x.val T (gamma x)
      (H.regularizedStageStart T 0 x.val) (H.regularizedStageEnd T v x.val)
    let gOriginal := H.stageMetric first (T - v ^ (2 : ℕ))
    let Vorig : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v
    let Roriginal := metricScalarAt gOriginal q
    gradientFun gOriginal (fun y => F (y, v)) q = Vorig ∧
    HasDerivAt (fun w => F (q, w))
      (2 * v ^ (2 : ℕ) * Roriginal - (1 / 2 : ℝ) * gOriginal.inner q Vorig Vorig) v ∧
    let Woriginal := ∑ x : Jstage,
      ∫ r in H.regularizedStageStart T aCut x.val..H.regularizedStageEnd T v x.val,
        ((1 : ℝ) - aCut ^ (2 : ℕ) / r ^ (2 : ℕ)) * H.stageRegularizedLagrangian x.val T (gamma x) r
    laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q =
      3 / (v - aCut) - v * Roriginal -
        Woriginal / (2 * (v - aCut) ^ (2 : ℕ)) + gOriginal.inner q Vorig Vorig / (4 * v) ∧
    laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q <
      3 / v - v * Roriginal - Loriginal / (2 * v ^ (2 : ℕ)) +
        gOriginal.inner q Vorig Vorig / (4 * v) + epsilon ∧
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < T ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (T - z.2)) ∈ U}
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (T - z.2) * F (z.1, Real.sqrt (T - z.2))
    IsOpen Omega ∧ (q, T - v ^ (2 : ℕ)) ∈ Omega ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega ∧
      Aphys (q, T - v ^ (2 : ℕ)) = 2 * v * Loriginal ∧
      (∀ z ∈ Omega, ∃ cost : ℝ,
        H.regularizedCost first last hle T Bfloor 0 (Real.sqrt (T - z.2))
          (gamma jl 0) z.1 = (cost : WithTop ℝ) ∧
        2 * Real.sqrt (T - z.2) * cost ≤ Aphys z) ∧
      H.regularizedCost first last hle T Bfloor 0
        (Real.sqrt (T - (T - v ^ (2 : ℕ)))) (gamma jl 0) q = (Loriginal : WithTop ℝ) ∧
      gradientFun gOriginal (fun y => Aphys (y, T - v ^ (2 : ℕ))) q = (2 * v) • Vorig ∧
      HasDerivAt (fun t => Aphys (q, t))
        (-Loriginal / v - 2 * v ^ (2 : ℕ) * Roriginal + gOriginal.inner q Vorig Vorig / 2)
        (T - v ^ (2 : ℕ)) ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, T - v ^ (2 : ℕ))) q =
        2 * v * laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q ∧
      -6 - eta < deriv (fun t => Aphys (q, t)) (T - v ^ (2 : ℕ)) -
        laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, T - v ^ (2 : ℕ))) q := by
  classical
  intro Jstage Eevent jo jn jf jl gamma hInt hattain rho eta hrho heta epsilon
  have hepsilon : 0 < epsilon := div_pos heta (mul_pos (by norm_num) hv)
  have hStageGap (k : Fin (H.eventCount + 1)) (hk : k ≤ last) :
      H.time k < H.stageEndTime k := by
    have hkT : H.time k < T := (H.time_strictMono.monotone hk).trans_lt hupper.1
    cases k using Fin.lastCases with
    | last =>
      have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last last) hk
      simpa only [hlast] using hkT.trans_le hupper.2
    | cast i =>
      simpa only [H.stageEndTime_castSucc] using H.time_strictMono i.castSucc_lt_succ
  have hpos (x : Jstage) :
      H.regularizedStageStart T 0 x.val < H.regularizedStageEnd T v x.val := by
    have hxT : H.time x.val < T :=
      (H.time_strictMono.monotone x.property.2).trans_lt hupper.1
    have hpastEnd : T - v ^ 2 < H.stageEndTime x.val :=
      hpast.2.trans_le (H.stageEndTime_mono x.property.1)
    have hgap : max (T - v ^ 2) (H.time x.val) < min T (H.stageEndTime x.val) :=
      max_lt (lt_min (sub_lt_self T (sq_pos_of_pos hv)) hpastEnd)
        (lt_min hxT (hStageGap x.val x.property.2))
    have hsqrt := Real.sqrt_lt_sqrt
      (sub_nonneg.mpr (min_le_left T (H.stageEndTime x.val))) (sub_lt_sub_left hgap T)
    simpa only [regularizedStageStart, regularizedStageEnd, zero_pow two_ne_zero,
      sub_zero] using hsqrt
  have hreserve : 0 < min rho (Real.sqrt (T - H.time last)) :=
    lt_min hrho (Real.sqrt_pos.mpr (sub_pos.mpr hupper.1))
  obtain ⟨aCut, haCut, haReserve, haV, henergy⟩ :=
    H.exists_small_prefix_trace_energy_lt first last last hle le_rfl T hv gamma hpos
      (fun x hx => (not_lt_of_ge x.property.2 hx).elim) hInt hreserve hepsilon
  have haRho : aCut < rho := haReserve.trans_le (min_le_left _ _)
  have haSqrt : aCut < Real.sqrt (T - H.time last) :=
    haReserve.trans_le (min_le_right _ _)
  have hupperCut : T - aCut ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    constructor
    · have hsqrtSq := Real.sq_sqrt (sub_nonneg.mpr hupper.1.le)
      have hproduct : 0 < (Real.sqrt (T - H.time last) - aCut) *
          (Real.sqrt (T - H.time last) + aCut) :=
        mul_pos (sub_pos.mpr haSqrt)
          (add_pos (Real.sqrt_pos.mpr (sub_pos.mpr hupper.1)) haCut)
      nlinarith
    · exact (sub_le_self T (sq_nonneg aCut)).trans hupper.2
  refine ⟨aCut, haCut, haRho, haV, hupperCut, ?_⟩
  intro lo hi hbounds hiv hprefixAC
    W FC DO DS DT SO SS ST hold hnew N j e s hs hsCut hslo hshi hsnew hsold
    hstail hsv alphaO alphaS alphaT Tag M0 D0 S0 alpha0 Q M D S alpha a b
    f hf hgeoO hgeoS hgeoT hcenter Phi hmetric hjoin hvelocity hfirst g ordinary survivor tail
    hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew
    V hV h0 KO KS KT hKO hKS hKT hregO hregS hregT
    hfix hjoinOld hjoinNew hjoinTail hcenterO hcenterOld hcenterNew hcenterTail
    Bframe hexp basis hON hloCut hboundsCut Pframe hLag hHam
    hregFrame halphaFrame hP hDP hONframe hindexInt hscalarJoin hlagJoin hfield hvelocityT action
  have hsPos : 0 < s 0 := by simpa only [hsCut] using haCut
  have hsUpper : T - (s 0) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [hsCut] using hupperCut
  obtain ⟨Jclock, U, psi, F, hsupport, hAction, _hFD, hgradient, hclock,
      _hhessian, _hlap, _hray, htrace⟩ :=
    H.exists_smooth_collar_cost_support_with_trace_energy first last hle hv hupper hpast
      Bfloor hscalar gamma lo hi hbounds hiv hprefixAC hInt hattain
      W FC DO DS DT SO SS ST hold hnew j e s hs hslo hshi hsnew hsold hstail hsv
      alphaO alphaS alphaT f hf hgeoO hgeoS hgeoT hcenter Phi hmetric hjoin hvelocity hfirst
      hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew
      V hV h0 KO KS KT hKO hKS hKT hregO hregS hregT
      hfix hjoinOld hjoinNew hjoinTail hcenterO hcenterOld hcenterNew hcenterTail
      Bframe hexp basis hON hsPos hsUpper hloCut hboundsCut Pframe hLag hHam
      hregFrame halphaFrame hP hDP hONframe hindexInt hscalarJoin hlagJoin hfield hvelocityT
  refine ⟨Jclock, U, psi, F, hsupport, hAction, ?_⟩
  intro q Loriginal gOriginal Vorig Roriginal
  have hjoint0 :=
    H.interleaved_actual_flow_joint_families (P := P) first last j e (fun k => W (e k))
      (fun k => DO (j k)) (fun k => DS (e k)) DT (fun k => SO (j k))
      (fun k => SS (e k)) ST (fun k => hSO (j k)) (fun k => hSS (e k)) hST
      (fun k => alphaO (j k)) (fun k => alphaS (e k)) alphaT T s
  obtain ⟨_hS, _hSOeq, _hSSeq, _hSTeq, hmap⟩ := hjoint0
  obtain ⟨_hmap, _hSmooth, hCenters, _hSplit⟩ := hmap f
  have hTailGerm : (fun r => tail (0, r)) =ᶠ[nhds v] alphaT :=
    (hCenters hcenter).2.2 v (by
      change v ∈ Icc (s (⟨2 * N + 1, by omega⟩ : Fin (2 * N + 3)))
        (s (Fin.last (2 * N + 2)))
      have hlo : s (⟨2 * N + 1, by omega⟩ : Fin (2 * N + 3)) = hi jf := hstail
      rw [hlo, hsv]
      exact ⟨hiv.le, le_rfl⟩)
  have hTailVelocity : lVelocity (I := ThreeModel) (fun r => tail (0, r)) v =
      lVelocity (I := ThreeModel) (gamma jf) v := by
    have h1 : lVelocity (I := ThreeModel) (fun r => tail (0, r)) v =
        lVelocity (I := ThreeModel) alphaT v := by
      unfold lVelocity
      rw [hTailGerm.mfderiv_eq]
      rfl
    exact h1.trans hvelocityT
  have hgradientOriginal : gradientFun gOriginal (fun y => F (y, v)) q = Vorig := by
    have h : gradientFun (ST.base.metric (T - v ^ 2)) (fun y => F (y, v)) q =
        lVelocity (I := ThreeModel) (fun r => tail (0, r)) v := hgradient
    rw [hmetricT, hTailVelocity] at h
    exact h
  have hclockOriginal : HasDerivAt (fun w => F (q, w))
      (2 * v ^ 2 * Roriginal - (1 / 2 : ℝ) * gOriginal.inner q Vorig Vorig) v := by
    have h : HasDerivAt (fun w => F (q, w))
        (2 * v ^ 2 * ST.scalar (T - v ^ 2) q - (1 / 2 : ℝ) *
          (ST.base.metric (T - v ^ 2)).inner q
            (lVelocity (I := ThreeModel) (fun r => tail (0, r)) v)
            (lVelocity (I := ThreeModel) (fun r => tail (0, r)) v)) v := hclock
    rw [hTailVelocity] at h
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, hmetricT] using h
  refine ⟨hgradientOriginal, hclockOriginal, ?_⟩
  intro Woriginal
  have htraceOriginal : laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q =
      3 / (v - aCut) - v * Roriginal - Woriginal / (2 * (v - aCut) ^ 2) +
        gOriginal.inner q Vorig Vorig / (4 * v) := by
    simpa only [hsCut] using htrace
  have htraceApprox : laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q <
      3 / v - v * Roriginal - Loriginal / (2 * v ^ 2) +
        gOriginal.inner q Vorig Vorig / (4 * v) + epsilon := by
    rw [htraceOriginal]
    exact henergy
  refine ⟨htraceOriginal, htraceApprox, ?_⟩
  intro Omega Aphys
  obtain ⟨_hJ, _hvJ, _hJKT, _hJtimes, _hactionSmooth, hU, hqU, _hpsiSmooth,
      hFSmooth, _hpsiCenter, hFvalue, hcostF, hsupportNear⟩ := hsupport
  have hcost : H.regularizedCost first last hle T Bfloor 0 v (gamma jl 0) q =
      (Loriginal : WithTop ℝ) :=
    hcostF.trans (congrArg (fun r : ℝ => (r : WithTop ℝ)) hFvalue)
  have hphysical := H.physical_clock_support_of_same_history_jets first last hle T Bfloor
    hv hpast gamma U F hU hqU hFSmooth hFvalue hcost
    (fun z hz => (hsupportNear z hz).2.2.2.2)
    hgradientOriginal hclockOriginal epsilon htraceApprox
  have hepsilonCancel : 2 * v * epsilon = eta := by
    dsimp only [epsilon]
    field_simp [hv.ne']
  simpa only [hepsilonCancel] using hphysical

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
