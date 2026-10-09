import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.InterleavedJointAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointBranchJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence

/-!
# S-CH11-FIX7 port of `Surgery.LGeometry.Action.SmoothCollarSupportJets` (`PortC11P`)

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim 它在本树里 6 error；以下全是 elaboration 层面的修补，陈述 / 定义 / 证明思路逐字不改：
* `attribute [-instance] … in` 与 docstring 的顺序对调（docstring 不能放在它前面）。
* 主定理陈述里所有 `x ^ 2` 写成 `x ^ (2 : ℕ)`（同一个项）：`.metric (T - r ^ 2)` 这类
  实参里默认 `2 : ℕ` 的 postponed 实例问题会让整条声明报 `unknown free variable`。
* `𝓝` 写成 `nhds`（namespace 内 `open scoped Topology` 被解析成
  `_root_.DifferentialGeometry.Topology`）。
* `endpoint_branch_jets_of_reindex`：`hlast` 的 `simpa only [hlast]` 改为先 `subst`
  整个族 `f = fun i => g0 (rho i)`，再 `exact`。
* `hfamily`：`Equiv.piCongrLeft'_symm_apply_apply` 显式给参数；
  `interleaved_actual_flow_joint_families` 显式 `(P := P)`；`hAction` 末尾
  `simp only [tail, add_assoc]` 改 `simp only [add_assoc]; rfl`。
* `hS0 / hgeoTag / hK0 / hexp' / hON'` 与最后的 `hjets`：`simpa only [...] using` 改为
  `rw [...] at h; exact h`（或 `key` 引理 + `exact`）：simp 后两个类型只差 let /
  `Sum.rec` 展开。
* `hvel`：`rw [mfderiv_eq]` 之后补 `rfl`（同 FIX4 的
  `smooth_collar_original_velocity_of_terminal_germ`）。
* 36 个陈述里未被引用的具名 hypothesis 改成 `_h…`（α-重命名，同一命题；unusedVariables）。
No statement, definition or proof idea is altered.  The module
`Surgery.LGeometry.Action.SmoothCollarSupportJets` is a shim re-exporting this file.
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

universe u uP uTag

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Equality elimination at the terminal tag transports the carrier, every
manifold instance, the actual flow and the same functions simultaneously. -/
private theorem endpoint_branch_jets_of_reindex
    {n : ℕ} {Tag : Type uTag} {M0 : Tag → Type u}
    [∀ k, TopologicalSpace (M0 k)] [∀ k, ChartedSpace ThreeSpace (M0 k)]
    [∀ k, IsManifold ThreeModel ∞ (M0 k)] [∀ k, T2Space (M0 k)]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (D0 : Tag → RealTimeInterval)
    (S0 : (k : Tag) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k))
    (hS0 : ∀ k, IsSolutionOn (S0 k)) (T : ℝ)
    (rho : Fin (n + 1) → Tag) (k : Tag) (hk : rho (Fin.last n) = k) :
    let M : Fin (n + 1) → Type u := fun i => M0 (rho i);
    let D : Fin (n + 1) → RealTimeInterval := fun i => D0 (rho i);
    let S : (i : Fin (n + 1)) → SolutionOn (I := ThreeModel) (M := M i) (D i) :=
      fun i => S0 (rho i);
    ∀ (f : (i : Fin (n + 1)) → P × ℝ → M i)
    (g0 : (k : Tag) → P × ℝ → M0 k)
    (_hfamily : ∀ i, f i = g0 (rho i))
    (_hf : ∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel (8 : ℕ) (f i))
    (a b : Fin (n + 1) → ℝ)
    (_hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T
      (fun r => f i (0, r)) (uIcc (a i) (b i)))
    (Phi : (i : Fin n) → PartialDiffeomorph ThreeModel ThreeModel (M i.castSucc) (M i.succ) ∞)
    (_hmetric : ∀ (i : Fin n) (x : M i.castSucc), x ∈ (Phi i).source →
      ∀ V W : TangentSpace ThreeModel x,
      ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner x V W =
        ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner (Phi i x)
          (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x V)
          (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x W))
    (_hjoin : ∀ᶠ z in 𝓝 (0 : P), ∀ i : Fin n,
      f i.castSucc (z, b i.castSucc) ∈ (Phi i).source ∧
      Phi i (f i.castSucc (z, b i.castSucc)) = f i.succ (z, a i.succ))
    (_hvelocity : ∀ i : Fin n,
      (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ)
        (f i.castSucc (0, b i.castSucc))
        (lVelocity (I := ThreeModel) (fun r => f i.castSucc (0, r)) (b i.castSucc)) : ThreeSpace) =
          lVelocity (I := ThreeModel) (fun r => f i.succ (0, r)) (a i.succ))
    (p : M 0)
    (_hfirst : (fun z => f 0 (z, a 0)) =ᶠ[𝓝 (0 : P)] fun _ => p)
    (C : ℝ) {V : Set P}
    (K : Fin (n + 1) → Set ℝ) (_hK : ∀ i, IsOpen (K i))
    (_hKconn : ∀ i, IsPreconnected (K i))
    (_ha : ∀ i, a i ∈ K i) (_hb : ∀ i, b i ∈ K i)
    (_hreg : ∀ i r, r ∈ K i → T - r ^ 2 ∈ (D i).regular)
    (q : M0 k) (B : P ≃L[ℝ] ThreeSpace)
    (_hexp : (fun z => g0 k (z, b (Fin.last n))) =ᶠ[𝓝 (0 : P)]
      (fun z => expMap ((S0 k).base.metric (T - (b (Fin.last n)) ^ 2))
        q (show TangentSpace ThreeModel q from B z)))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx ℝ P)
    (_hON : ∀ i j,
      ((S0 k).base.metric (T - (b (Fin.last n)) ^ 2)).inner q
        (show TangentSpace ThreeModel q from B (basis i)) (show TangentSpace ThreeModel q from B (basis j)) =
          if i = j then 1 else 0)
    {U : Set (M0 k × ℝ)}
    {psi : M0 k × ℝ → P} {F : M0 k × ℝ → ℝ}
    (_hU : IsOpen U) (_hqU : (q, b (Fin.last n)) ∈ U)
    (_hpsi : ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U)
    (_hF : ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U)
    (_hpsi0 : psi (q, b (Fin.last n)) = 0)
    (_hdata : ∀ z ∈ U, psi z ∈ V ∧ z.2 ∈ K (Fin.last n) ∧
      g0 k (psi z, z.2) = z.1 ∧
      F z = C + finiteJointAction S T f a b (psi z, z.2)),
    let v := b (Fin.last n)
    let g := (S0 k).base.metric (T - v ^ 2)
    let velocity : TangentSpace ThreeModel q :=
      show ThreeSpace from lVelocity (I := ThreeModel) (fun r => g0 k (0, r)) v
    let clock := 2 * v ^ 2 * (S0 k).scalar (T - v ^ 2) q -
      (1 / 2 : ℝ) * g.inner q velocity velocity
    HasMFDerivAt (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) F (q, v)
      ((g.inner q velocity).comp (ContinuousLinearMap.fst ℝ ThreeSpace ℝ) +
        clock • ContinuousLinearMap.snd ℝ ThreeSpace ℝ) ∧
    gradientFun g (fun y => F (y, v)) q = velocity ∧
    HasDerivAt (fun w => F (q, w)) clock v ∧
    (∀ ξ : P, abstractHessian g (fun y => F (y, v)) q
      (show TangentSpace ThreeModel q from B ξ) (show TangentSpace ThreeModel q from B ξ) =
        2 * ∑ i : Fin (n + 1), lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • ξ, r)) 0)
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • ξ, r)) 0) (a i) (b i)) ∧
    laplacian (LeviCivita g) g (fun y => F (y, v)) q =
      2 * ∑ i : Fin (n + 1), ∑ k : Idx,
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0)
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0) (a i) (b i) ∧
    (∀ ξ : P, (fun u : ℝ => F (expMap g q (u • (show TangentSpace ThreeModel q from B ξ)), v))
      =ᶠ[𝓝 0] (fun u => C + finiteJointAction S T f a b (u • ξ, v))) := by
  intro M D S f g0 hfamily hf a b hgeo Phi hmetric hjoin hvelocity p hfirst C V
    K hK hKconn ha hb hreg q B hexp Idx _ _ basis hON U psi F hU hqU hpsi hF hpsi0 hdata
  subst k
  have hfeq : f = fun i => g0 (rho i) := funext hfamily
  subst hfeq
  have hexp' : (fun z => g0 (rho (Fin.last n)) (z, b (Fin.last n))) =ᶠ[𝓝 (0 : P)]
      (fun z => expMap ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2))
        q (show TangentSpace ThreeModel q from B z)) := by
    exact hexp
  have hdata' : ∀ z ∈ U, psi z ∈ V ∧ z.2 ∈ K (Fin.last n) ∧
      g0 (rho (Fin.last n)) (psi z, z.2) = z.1 ∧
      F z = C + finiteJointAction S T (fun i => g0 (rho i)) a b (psi z, z.2) := by
    exact hdata
  exact
    finiteJointAction_endpoint_branch_jets S (fun i => hS0 (rho i)) T (fun i => g0 (rho i))
      hf a b hgeo
      Phi hmetric hjoin hvelocity p hfirst C K hK hKconn ha hb hreg q B hexp'
      basis hON hU hqU hpsi hF hpsi0 hdata'

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- One physical same-history cost support and all endpoint jets of its
unchanged function, received from one actual finite compatible joint family. -/
theorem exists_smooth_collar_cost_support_with_jets
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
      (_hcenter : ∀ i r, r ∈ Icc (a i) (b i) →
        (fun t => f i (0, t)) =ᶠ[nhds r] alpha i)
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
    ∀ {Idx : Type*} [Fintype Idx] [DecidableEq Idx] (basis : Module.Basis Idx ℝ P),
      (∀ i j, (ST.base.metric (T - v ^ (2 : ℕ))).inner (gamma jf v)
        (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis i))
        (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis j)) =
          if i = j then 1 else 0) →
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
    let clock := 2 * v ^ (2 : ℕ) * ST.scalar (T - v ^ (2 : ℕ)) q -
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
      2 * ∑ i : Fin (2 * N + 2), ∑ k : Idx,
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0)
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0) (a i) (b i) ∧
    (∀ ξ : P, (fun u : ℝ => F (expMap gphys q (u • (show TangentSpace ThreeModel q from Bframe ξ)), v))
      =ᶠ[nhds 0] (fun u => H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
        finiteJointAction S T f a b (u • ξ, v))) := by
  classical
  intro Jstage Eevent jo jn jf jl gamma lo hi hbounds hiv hprefixAC hInt hattain
    W FC DO DS DT SO SS ST hold hnew N j e s hs hslo hshi hsnew hsold
    hstail hsv alphaO alphaS alphaT Tag M0 D0 S0 alpha0 Q M D S alpha a b
    f hf hgeoO hgeoS hgeoT hcenter Phi hmetric hjoin hvelocity hfirst g ordinary survivor tail
    hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew
    V hV h0 KO KS KT hKO hKS hKT hregO hregS hregT
    hfix hjoinOld hjoinNew hjoinTail hcenterO hcenterOld hcenterNew hcenterTail
    Bframe hexp Idx _ _ basis hON action
  have hfamily (i : Fin (2 * N + 2)) : f i = g (Q.symm i) :=
    (Equiv.piCongrLeft'_symm_apply_apply (fun k => P × ℝ → M0 k) Q f i).symm
  have hOrdinary (k : Fin (N + 1)) : ordinary (j k) = g (.inl k) :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  have hSurvivor (k : Fin N) : survivor (e k) = g (.inr (.inl k)) :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  have htailQ : Q (.inr (.inr 0)) = Fin.last (2 * N + 1) :=
    (interleavedPieceEquiv_values N).2.2
  have htailIndex : Q.symm (Fin.last (2 * N + 1)) = (.inr (.inr 0) : Tag) := by
    rw [← htailQ]
    exact Q.symm_apply_apply _
  have hbLast : b (Fin.last (2 * N + 1)) = v := hsv
  obtain ⟨hS, _hSOeq, _hSSeq, _hSTeq, hmap⟩ :=
    H.interleaved_actual_flow_joint_families (P := P) first last j e (fun k => W (e k))
      (fun k => DO (j k)) (fun k => DS (e k)) DT (fun k => SO (j k))
      (fun k => SS (e k)) ST (fun k => hSO (j k)) (fun k => hSS (e k)) hST
      (fun k => alphaO (j k)) (fun k => alphaS (e k)) alphaT T s
  obtain ⟨_hmap, hSmooth, _hCenters, hSplit⟩ := hmap f
  have hOrd : ∀ x, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 (ordinary x) := by
    intro x
    obtain ⟨k, rfl⟩ := j.surjective x
    rw [hOrdinary]
    exact (hSmooth hf).1 k
  have hSurv : ∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 (survivor i) := by
    intro i
    obtain ⟨k, rfl⟩ := e.surjective i
    rw [hSurvivor]
    exact (hSmooth hf).2.1 k
  have hTail : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 tail :=
    (hSmooth hf).2.2
  have hAction (z : P) (w : ℝ) : action (z, w) =
      H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
        finiteJointAction S T f a b (z, w) := by
    have hOrdSum :
        (∑ x : Jstage, lRegularizedAction (SO x) T (fun r => ordinary x (z, r)) (lo x) (hi x)) =
        ∑ k : Fin (N + 1), lRegularizedAction (SO (j k)) T
          (fun r => g (.inl k) (z, r)) (lo (j k)) (hi (j k)) := by
      rw [← j.sum_comp (fun x => lRegularizedAction (SO x) T
        (fun r => ordinary x (z, r)) (lo x) (hi x))]
      simp only [hOrdinary]
    have hSurvSum :
        (∑ i : Eevent, lRegularizedAction (SS i) T (fun r => survivor i (z, r))
          (hi (jn i)) (lo (jo i))) =
        ∑ k : Fin N, lRegularizedAction (SS (e k)) T
          (fun r => g (.inr (.inl k)) (z, r)) (hi (jn (e k))) (lo (jo (e k))) := by
      rw [← e.sum_comp (fun i => lRegularizedAction (SS i) T
        (fun r => survivor i (z, r)) (hi (jn i)) (lo (jo i)))]
      simp only [hSurvivor]
    have hSplit' := hSplit z w
    change finiteJointAction S T f a b (z, w) = _ at hSplit'
    simp only [hslo, hshi, hsnew, hsold] at hSplit'
    have htailLower : s (⟨2 * N + 1, by omega⟩ : Fin (2 * N + 3)) = hi jf := hstail
    simp only [htailLower] at hSplit'
    dsimp only [action]
    rw [hOrdSum, hSurvSum, hSplit']
    simp only [add_assoc]
    rfl
  obtain ⟨Jclock, U, psi, F, hsupport⟩ :=
    H.exists_smooth_collar_cost_support first last hle hv hupper hpast Bfloor hscalar
      gamma lo hi hbounds hiv hprefixAC hInt hattain W FC DO DS DT SO SS ST hold hnew
      ordinary survivor tail hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew
      hOrd hSurv hTail V hV h0 KO KS KT hKO hKS hKT hregO hregS hregT
      hfix hjoinOld hjoinNew hjoinTail hcenterO hcenterOld hcenterNew hcenterTail Bframe hexp
  refine ⟨Jclock, U, psi, F, hsupport, hAction, ?_⟩
  rcases hsupport with ⟨_hJ, _hvJ, hJKT, _hJdomain, _hActionC2,
    hU, hqU, hpsi, hF, hpsi0, _hcontact, _hcostContact, hdata⟩
  have hS0 (k : Tag) : IsSolutionOn (S0 k) := by
    have key : ∀ k' : Tag, k' = k → IsSolutionOn (S0 k') → IsSolutionOn (S0 k) := by
      rintro k' rfl h
      exact h
    exact key (Q.symm (Q k)) (Q.symm_apply_apply k) (hS (Q k))
  have hgeoTag (k : Tag) : IsLRegularizedGeodesicOn (S0 k) T (alpha0 k)
      (Icc (s (Q k).castSucc) (s (Q k).succ)) := by
    rcases k with k | (k | k)
    · have h := hgeoO (j k)
      rw [← hslo k, ← hshi k] at h
      exact h
    · have h := hgeoS (e k)
      rw [← hsnew k, ← hsold k] at h
      exact h
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      have e1 : s (Q (.inr (.inr 0))).castSucc = hi jf := by
        rw [htailQ]
        exact hstail
      have e2 : s (Q (.inr (.inr 0))).succ = v := by
        rw [htailQ]
        exact hsv
      rw [e1, e2]
      exact hgeoT
  have hgeoAlpha (i : Fin (2 * N + 2)) :
      IsLRegularizedGeodesicOn (S i) T (alpha i) (Icc (a i) (b i)) := by
    simpa only [Q.apply_symm_apply] using hgeoTag (Q.symm i)
  have hab (i : Fin (2 * N + 2)) : a i < b i := hs i.castSucc_lt_succ
  have hgeo (i : Fin (2 * N + 2)) :
      IsLRegularizedGeodesicOn (S i) T (fun r => f i (0, r)) (uIcc (a i) (b i)) := by
    rw [uIcc_of_le (hab i).le]
    exact (hgeoAlpha i).congr_of_eventuallyEq (hcenter i)
  have hpoint (i : Fin (2 * N + 2)) (r : ℝ) (hr : r ∈ Icc (a i) (b i)) :
      f i (0, r) = alpha i r := (hcenter i r hr).self_of_nhds
  have hvel (i : Fin (2 * N + 2)) (r : ℝ) (hr : r ∈ Icc (a i) (b i)) :
      lVelocity (I := ThreeModel) (fun t => f i (0, t)) r =
        lVelocity (I := ThreeModel) (alpha i) r := by
    unfold lVelocity
    rw [(hcenter i r hr).mfderiv_eq]
    rfl
  have hvelocityF (i : Fin (2 * N + 1)) :
      (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ)
        (f i.castSucc (0, b i.castSucc))
        (lVelocity (I := ThreeModel) (fun r => f i.castSucc (0, r)) (b i.castSucc)) : ThreeSpace) =
          lVelocity (I := ThreeModel) (fun r => f i.succ (0, r)) (a i.succ) := by
    rw [hpoint i.castSucc _ ⟨(hab i.castSucc).le, le_rfl⟩,
      hvel i.castSucc _ ⟨(hab i.castSucc).le, le_rfl⟩,
      hvel i.succ _ ⟨le_rfl, (hab i.succ).le⟩]
    exact hvelocity i
  let K0 : Tag → Set ℝ := Sum.elim (fun k => KO (j k))
    (Sum.elim (fun k => KS (e k)) (fun _ => KT))
  let K : Fin (2 * N + 2) → Set ℝ := fun i => K0 (Q.symm i)
  have hK0 (k : Tag) : IsOpen (K0 k) ∧ IsPreconnected (K0 k) ∧
      s (Q k).castSucc ∈ K0 k ∧ s (Q k).succ ∈ K0 k := by
    rcases k with k | (k | k)
    · have h := hKO (j k)
      rw [← hslo k, ← hshi k] at h
      exact h
    · have h := hKS (e k)
      rw [← hsnew k, ← hsold k] at h
      exact h
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      have e1 : s (Q (.inr (.inr 0))).castSucc = hi jf := by
        rw [htailQ]
        exact hstail
      have e2 : s (Q (.inr (.inr 0))).succ = v := by
        rw [htailQ]
        exact hsv
      have h := hKT
      rw [← e1, ← e2] at h
      exact h
  have hK (i : Fin (2 * N + 2)) : IsOpen (K i) := (hK0 (Q.symm i)).1
  have hKconn (i : Fin (2 * N + 2)) : IsPreconnected (K i) := (hK0 (Q.symm i)).2.1
  have ha (i : Fin (2 * N + 2)) : a i ∈ K i := by
    simpa only [Q.apply_symm_apply] using (hK0 (Q.symm i)).2.2.1
  have hb (i : Fin (2 * N + 2)) : b i ∈ K i := by
    simpa only [Q.apply_symm_apply] using (hK0 (Q.symm i)).2.2.2
  have hreg0 (k : Tag) (r : ℝ) (hr : r ∈ K0 k) : T - r ^ 2 ∈ (D0 k).regular := by
    rcases k with k | (k | k)
    · exact hregO (j k) r hr
    · exact hregS (e k) r hr
    · exact hregT r hr
  have hreg (i : Fin (2 * N + 2)) (r : ℝ) (hr : r ∈ K i) :
      T - r ^ 2 ∈ (D i).regular := hreg0 (Q.symm i) r hr
  have hKLast : K (Fin.last (2 * N + 1)) = KT := by
    dsimp only [K]
    rw [htailIndex]
    rfl
  have hexp' : (fun z => g (.inr (.inr 0)) (z, b (Fin.last (2 * N + 1)))) =ᶠ[𝓝 (0 : P)]
      (fun z => expMap ((S0 (.inr (.inr 0))).base.metric
          (T - (b (Fin.last (2 * N + 1))) ^ 2)) (gamma jf v)
        (show TangentSpace ThreeModel (gamma jf v) from Bframe z)) := by
    rw [hbLast]
    exact hexp
  have hON' : ∀ i j,
      ((S0 (.inr (.inr 0))).base.metric (T - (b (Fin.last (2 * N + 1))) ^ 2)).inner
        (gamma jf v) (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis i))
        (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis j)) =
          if i = j then 1 else 0 := by
    rw [hbLast]
    exact hON
  have hqU' : (gamma jf v, b (Fin.last (2 * N + 1))) ∈ U := by
    simpa only [hbLast] using hqU
  have hpsi0' : psi (gamma jf v, b (Fin.last (2 * N + 1))) = 0 := by
    simpa only [hbLast] using hpsi0
  have hdata' : ∀ x ∈ U, psi x ∈ V ∧ x.2 ∈ K (Fin.last (2 * N + 1)) ∧
      g (.inr (.inr 0)) (psi x, x.2) = x.1 ∧
      F x = H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
        finiteJointAction S T f a b (psi x, x.2) := by
    intro x hx
    obtain ⟨hz, hw, he, hA, _hcost⟩ := hdata x hx
    refine ⟨hz, ?_, he, hA.trans (hAction (psi x) x.2)⟩
    rw [hKLast]
    exact hJKT hw
  have hjets := endpoint_branch_jets_of_reindex D0 S0 hS0 T Q.symm
    (.inr (.inr 0)) htailIndex f g hfamily hf a b hgeo Phi hmetric
    (Filter.Eventually.of_forall hjoin) hvelocityF (alpha 0 (a 0))
    (Filter.Eventually.of_forall hfirst) (H.stageRegularizedAction last T (gamma jl) 0 (lo jl))
    K hK hKconn ha hb hreg (gamma jf v) Bframe hexp' basis hON'
    hU hqU' hpsi hF hpsi0' hdata'
  rw [hbLast] at hjets
  exact hjets

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The actual terminal-stage supplier returns `hvelocityT` using only the
original terminal differentiability `hFirst v`. The joint central germ then
identifies the velocity in the support jets with that original velocity.
No derivative equality is inferred from equality on a one-sided interval. -/
theorem smooth_collar_original_velocity_of_terminal_germ
    {P : Type uP} [Zero P]
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (gamma alphaT : ℝ → (H.stage first).Carrier)
    (tail : P × ℝ → (H.stage first).Carrier) (v : ℝ)
    (hvelocityT : lVelocity (I := ThreeModel) alphaT v =
      lVelocity (I := ThreeModel) gamma v)
    (hcenter : (fun r => tail (0, r)) =ᶠ[𝓝 v] alphaT) :
    lVelocity (I := ThreeModel) (fun r => tail (0, r)) v =
      lVelocity (I := ThreeModel) gamma v := by
  have heq : lVelocity (I := ThreeModel) (fun r => tail (0, r)) v =
      lVelocity (I := ThreeModel) alphaT v := by
    unfold lVelocity
    rw [hcenter.mfderiv_eq]
    rfl
  exact heq.trans hvelocityT

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
