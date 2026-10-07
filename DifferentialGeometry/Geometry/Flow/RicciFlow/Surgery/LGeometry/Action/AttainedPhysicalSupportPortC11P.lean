import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothPhysicalCollarSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteAdaptedJointVariation
import Mathlib.LinearAlgebra.StdBasis

/-!
# S-CH11-FIX9 port of astra `AttainedPhysicalSupport`（`PortC11P`）

来源：donor `AttainedPhysicalSupport.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`；思路沿 S-CH11-FIX8 / FIX9 对 `SmoothCollarTraceEnergy` /
`SmoothPhysicalCollarSupport` 的修补）：
* `/-- docstring -/ attribute [-instance] … in theorem` 的顺序对调；
* 陈述里所有 `x ^ 2` 写成 `x ^ (2 : ℕ)`（同一个项）；
* 证明里一族 `simpa only [h₁, h₂] using X`：等式 `h` 的左端写在 `(fun i ↦ ⟨…⟩) i` / `⟨first, _⟩` /
  `s (Fin.last (2 * N + 1 + 1))` 形（beta-redex、字面量、`2 * N + 2` 与 `2 * N + 1 + 1`），而目标里是 `let`
  变量 `jn i` / `jf` / `tail` / `N`，simp 不做 zeta-delta 因而不匹配 → 改成先 `have e : 目标形 = … := h`
  （defeq）再 `rw [e]; exact …`：`hgeoS'` / `hgeoT'` / `hTCenter`（两处）/ `htailPacket`（两处，
  用 `hvalueT' : alphaT v = gamma jf v`）/ `hexp'` `hON'`（`hsv'`）/ `hbasisON` / `hfield'` /
  `hindexInt'`；
* `hfield'` / `hindexInt'` 的陈述里 `•`（`Pframe i k r : TangentSpace …`）触发
  `typeclass instance problem is stuck`（`HSMul ℝ (TangentSpace …) ThreeSpace`；FIX8 / FIX9 在
  TraceEnergy / SmoothPhysicalCollarSupport 里的同一处）→ 写成
  `SMul.smul (…) (Pframe i k r : ThreeSpace)`。

原路径 `AttainedPhysicalSupport` 是只 import 本文件的 re-export shim。
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

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- A fixed-endpoint attained actual-history curve with regular crossings gives
one physical cost upper support. Its collar reserve precedes the prefix choice,
and one compatible joint family supplies all jets of the same support. -/
theorem exists_physical_cost_upper_support_of_attained_action
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
          (Real.sqrt (T - H.time i.succ))))
    {etaError : ℝ} (hetaError : 0 < etaError) :
    let jf : H.StageInterval first last := ⟨first, le_rfl, hle⟩;
    let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩;
    let q := gamma jf v;
    let Loriginal := ∑ x : H.StageInterval first last,
      H.stageRegularizedAction x.val T (gamma x)
        (H.regularizedStageStart T 0 x.val) (H.regularizedStageEnd T v x.val);
    let gOriginal := H.stageMetric first (T - v ^ (2 : ℕ));
    let Vorig : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v;
    let Roriginal := metricScalarAt gOriginal q;
    ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen U ∧ (q, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      F (q, v) = Loriginal ∧
      H.regularizedCost first last hle T B 0 v (gamma jl 0) q = (F (q, v) : WithTop ℝ) ∧
      (∀ z ∈ U, H.regularizedCost first last hle T B 0 z.2 (gamma jl 0) z.1 ≤
        (F z : WithTop ℝ)) ∧
      gradientFun gOriginal (fun y => F (y, v)) q = Vorig ∧
      HasDerivAt (fun w => F (q, w))
        (2 * v ^ (2 : ℕ) * Roriginal - (1 / 2 : ℝ) * gOriginal.inner q Vorig Vorig) v ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q <
        3 / v - v * Roriginal - Loriginal / (2 * v ^ (2 : ℕ)) +
          gOriginal.inner q Vorig Vorig / (4 * v) + etaError / (2 * v) ∧
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < T ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (T - z.2)) ∈ U};
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (T - z.2) * F (z.1, Real.sqrt (T - z.2));
    IsOpen Omega ∧ (q, T - v ^ (2 : ℕ)) ∈ Omega ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega ∧
      Aphys (q, T - v ^ (2 : ℕ)) = 2 * v * Loriginal ∧
      (∀ z ∈ Omega, ∃ cost : ℝ,
        H.regularizedCost first last hle T B 0 (Real.sqrt (T - z.2))
          (gamma jl 0) z.1 = (cost : WithTop ℝ) ∧
        2 * Real.sqrt (T - z.2) * cost ≤ Aphys z) ∧
      H.regularizedCost first last hle T B 0
        (Real.sqrt (T - (T - v ^ (2 : ℕ)))) (gamma jl 0) q = (Loriginal : WithTop ℝ) ∧
      gradientFun gOriginal (fun y => Aphys (y, T - v ^ (2 : ℕ))) q = (2 * v) • Vorig ∧
      HasDerivAt (fun t => Aphys (q, t))
        (-Loriginal / v - 2 * v ^ (2 : ℕ) * Roriginal + gOriginal.inner q Vorig Vorig / 2)
        (T - v ^ (2 : ℕ)) ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, T - v ^ (2 : ℕ))) q =
        2 * v * laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q ∧
      -6 - etaError < deriv (fun t => Aphys (q, t)) (T - v ^ (2 : ℕ)) -
        laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, T - v ^ (2 : ℕ))) q := by
  classical
  intro jf jl q Loriginal gOriginal Vorig Roriginal
  let J := H.StageInterval first last
  let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last}
  let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
    i.val.castSucc_le_succ.trans i.property.2⟩
  let jn (i : E) : J := ⟨i.val.succ,
    i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩
  let N := last.val - first.val
  let P := Fin (Module.finrank ℝ ThreeSpace) → ℝ
  let basis : Module.Basis (Fin (Module.finrank ℝ ThreeSpace)) ℝ P :=
    Pi.basisFun ℝ (Fin (Module.finrank ℝ ThreeSpace))
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨DT, ST, b, lowT, highT, alphaT, hST, hmetricT, _hb0, hbv, _hmb,
      hlowT, hhighT, hregT, _hsmT, hgeoT, hcenterT, _hGermT, hvalueT, hvelocityT,
      _hactionT, C, D, hCs, hsD, W, FC, SS, hold, hnew, _c0, _d0, _lift, hraw,
      j, e, c, d, a0, hj0, _hjLast, _hjEvent, ha0, _ha0b, hcollar, _hstart, _hend,
      _hpositive, lowS, highS, alphaS, hsurvivorData, hpieces⟩ :=
    H.exists_smooth_physical_collar_geometry_of_attained_action first last hle hv hupper hpast
      hscalar gamma hgammaAC hgammaInt hgammaNodes hmin hC1Atv hcross
  choose _hw0 _hwv _hC _hD _hSource hSS hCross hmetricOld hmetricNew
    _hmetricEvent _hc00 _hc0w _hwd0 _hd0v _hnewClip _holdClip hrawPhysical
    _hACeta _hC1eta _hGeoeta _hProjNew _hProjOld _hInteta _hActioneta using hraw
  rcases hsurvivorData with ⟨hmarginS, hregS, _hsmS, _hGermEta, hgeoS,
    hcenterNew, hcenterOld, _hGermNew, _hGermOld, _hLagEta, _hIntS, _hActionS, _hWeightedS⟩
  obtain ⟨aCut, haCut, haReserve, _haV, _hupperCut, hReceive⟩ :=
    H.exists_smooth_physical_collar_cost_support (P := P) first last hle hv hupper hpast
      B hscalar gamma hgammaInt hmin (rho := a0) (eta := etaError) ha0 hetaError
  obtain ⟨lo, hi, s, hs, hs0, hsv, hsb, hsO, hsS, hlo, hhi, hjoin, hgap,
      _hupperCut, hboundsCut, hprefixAC, DO, SO, alphaO, lowO, highO,
      hordinaryData, hgeometry⟩ := hpieces aCut ⟨haCut, haReserve⟩
  rcases hordinaryData with ⟨hSO, hmetricO, _hsmO, hGermO, hcenterO, hgeoO,
    hmarginO, hregO, _hLagO, _hActionO, _hWeightedO⟩
  let DS : E → RealTimeInterval := fun i =>
    RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le
  let Tag := Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)
  let M0 : Tag → Type u := ActualPieceCarrier H first last j e (fun k => W (e k))
  let D0 : Tag → RealTimeInterval := Sum.elim (fun k => DO (j k))
    (Sum.elim (fun k => DS (e k)) (fun _ => DT))
  let S0 : (k : Tag) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k) :=
    Sum.rec (fun k => SO (j k)) (Sum.rec (fun k => SS (e k)) (fun _ => ST))
  let alpha0 : (k : Tag) → ℝ → M0 k :=
    Sum.rec (fun k => alphaO (j k)) (Sum.rec (fun k => alphaS (e k)) (fun _ => alphaT))
  let Q := interleavedPieceEquiv N
  let M : Fin (2 * N + 2) → Type u := fun i => M0 (Q.symm i)
  let Dpiece : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (Q.symm i)
  let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (Dpiece i) :=
    fun i => S0 (Q.symm i)
  let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (Q.symm i)
  let lowFlat : Fin (2 * N + 2) → ℝ := fun i =>
    Sum.elim (fun k => lowO (j k))
      (Sum.elim (fun k => lowS (e k)) (fun _ => lowT)) (Q.symm i)
  let highFlat : Fin (2 * N + 2) → ℝ := fun i =>
    Sum.elim (fun k => highO (j k))
      (Sum.elim (fun k => highS (e k)) (fun _ => highT)) (Q.symm i)
  obtain ⟨hS, hsmFlat, hmarginFlat, hregFlat, hgeoFlat, Phi, hPhi, hcompat⟩ := hgeometry
  have hsPos : 0 < s 0 := by simpa only [hs0] using haCut
  obtain ⟨_terminalBasis, Pframe, OmegaFrame, Bframe, f, _hBasisON, _hBasisSum,
      hOmegaFrame, _hPSmooth, hAdapted, _hPfinal, _hPjoin, hONframe,
      hLag, hHam, hregFrame, hP, hindexInt, hscalarJoin, hlagJoin,
      hf, hcenter, hfield, hfirst, hjoins, hexp, hON⟩ :=
    exists_compatible_joint_variation_of_smooth_geodesic_pieces
      (n := 2 * N + 1) S hS T alpha hsmFlat s hs hsPos lowFlat highFlat
      (fun i => (hmarginFlat i).1) (fun i => (hmarginFlat i).2) hregFlat hgeoFlat Phi
      (fun i => (hPhi i).1) (fun i => (hPhi i).2.1)
      (fun i => (hPhi i).2.2.2.1) (fun i => (hPhi i).2.2.2.2.1)
  let g := (Equiv.piCongrLeft' (fun k => P × ℝ → M0 k) Q).symm f
  let ordinary : (x : J) → P × ℝ → (H.stage x.val).Carrier :=
    (Equiv.piCongrLeft' (fun x : J => P × ℝ → (H.stage x.val).Carrier) j.symm).symm
      (fun k => g (.inl k))
  let survivor : (i : E) → P × ℝ → W i :=
    (Equiv.piCongrLeft' (fun i : E => P × ℝ → W i) e.symm).symm
      (fun k => g (.inr (.inl k)))
  let tail : P × ℝ → (H.stage first).Carrier := g (.inr (.inr 0))
  have hOeq (k) : ordinary (j k) = g (.inl k) :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  have hSeq (k) : survivor (e k) = g (.inr (.inl k)) :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  have hgeq (i : Fin (2 * N + 2)) : g (Q.symm i) = f i :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  have hOL (k : Fin (N + 1)) : s (Q (.inl k)).castSucc = lo (j k) := (hsO k).1
  have hOR (k : Fin (N + 1)) : s (Q (.inl k)).succ = hi (j k) := (hsO k).2
  have hSL (k : Fin N) : s (Q (.inr (.inl k))).castSucc = hi (jn (e k)) :=
    (hsS k).1.trans (hjoin (e k)).1.symm
  have hSR (k : Fin N) : s (Q (.inr (.inl k))).succ = lo (jo (e k)) :=
    (hsS k).2.trans (hjoin (e k)).2.symm
  have hTL : s (Fin.last (2 * N + 1)).castSucc = hi jf := hsb.trans hhi.symm
  have hTLlit : s ⟨2 * N + 1, by omega⟩ = hi jf := hTL
  have hqTail : Q (.inr (.inr 0)) = Fin.last (2 * N + 1) :=
    (interleavedPieceEquiv_values N).2.2
  have hqZero : Q (.inl 0) = 0 := rfl
  have htailIndex : Q.symm (Fin.last (2 * N + 1)) = .inr (.inr 0) := by
    rw [← hqTail, Q.symm_apply_apply]
  have hbounds (x : J) : H.regularizedStageStart T 0 x.val ≤ lo x ∧ lo x ≤ hi x ∧
      hi x ≤ H.regularizedStageEnd T v x.val :=
    ⟨(hgap x).1.le, (hgap x).2.1.le, (hgap x).2.2.le⟩
  have hgeoS' (i : E) : IsLRegularizedGeodesicOn (SS i) T (alphaS i)
      (Icc (hi (jn i)) (lo (jo i))) := by
    have e1 : hi (jn i) = c i := (hjoin i).1
    have e2 : lo (jo i) = d i := (hjoin i).2
    rw [e1, e2]
    exact hgeoS i
  have hgeoT' : IsLRegularizedGeodesicOn ST T alphaT (Icc (hi jf) v) := by
    have e : hi jf = b := hhi
    rw [e]
    exact hgeoT
  have hstrict (i : E) : hi (jn i) < Real.sqrt (T - H.time i.val.succ) ∧
      Real.sqrt (T - H.time i.val.succ) < lo (jo i) := by
    rw [(hjoin i).1, (hjoin i).2]
    exact ⟨(hcollar i).2.1, (hcollar i).2.2.1⟩
  have hphysical (i : E) (r : ℝ) (hr : r ∈ Icc (hi (jn i)) (lo (jo i))) :
      T - r ^ 2 ∈ Ioo (C i) (D i) := by
    rw [(hjoin i).1, (hjoin i).2] at hr
    exact hrawPhysical i r (Ioo_subset_Icc_self ((hcollar i).2.2.2.2 hr))
  have hc (i : E) : 0 ≤ hi (jn i) :=
    (Real.sqrt_nonneg _).trans ((hbounds (jn i)).1.trans (hbounds (jn i)).2.1)
  have hwclock (i : E) : T - (Real.sqrt (T - H.time i.val.succ)) ^ 2 = H.time i.val.succ := by
    rw [Real.sq_sqrt (sub_nonneg.mpr ((H.time_strictMono.monotone i.property.2).trans hupper.1.le))]
    ring
  have hOldHalf (i : E) (r : ℝ)
      (hr : r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i))) :
      (SS i).base.metric (T - r ^ 2) =
        localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
          (fun z : W i => z.val.val) (hold i) := by
    have hpr := hphysical i r ⟨((hstrict i).1.trans hr.1).le, hr.2.le⟩
    have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hr.1.le)).mpr hr.1
    have ht : T - r ^ 2 < H.time i.val.succ := by linarith only [hsq, hwclock i]
    exact hmetricOld i _ ⟨hpr.1.le, ht⟩
  have hNewHalf (i : E) (r : ℝ)
      (hr : r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ))) :
      (SS i).base.metric (T - r ^ 2) =
        localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
          (fun z : W i => FC i z.val) (hnew i) := by
    have hpr := hphysical i r ⟨hr.1.le, (hr.2.trans (hstrict i).2).le⟩
    have hsq := (sq_lt_sq₀ ((hc i).trans hr.1.le) (Real.sqrt_nonneg _)).mpr hr.2
    have ht : H.time i.val.succ < T - r ^ 2 := by linarith only [hsq, hwclock i]
    exact hmetricNew i _ ⟨ht.le, hpr.2.le⟩
  obtain ⟨_, _, _, _, hmap⟩ :=
    H.interleaved_actual_flow_joint_families (P := P) first last j e (fun k => W (e k))
      (fun k => DO (j k)) (fun k => DS (e k)) DT (fun k => SO (j k))
      (fun k => SS (e k)) ST (fun k => hSO (j k)) (fun k => hSS (e k)) hST
      (fun k => alphaO (j k)) (fun k => alphaS (e k)) alphaT T s
  obtain ⟨_, _, hCenters, _⟩ := hmap f
  have hgc := hCenters hcenter
  have hOCenter (x : J) (r : ℝ) (hr : r ∈ Icc (lo x) (hi x)) :
      ordinary x (0, r) = gamma x r := by
    obtain ⟨k, rfl⟩ := j.surjective x
    rw [hOeq]
    exact ((hgc.1 k r (by
      change r ∈ Icc (s (Q (.inl k)).castSucc) (s (Q (.inl k)).succ)
      simpa only [hOL, hOR] using hr)).self_of_nhds).trans (hcenterO _ hr)
  have hSCenter (i : E) (r : ℝ) (hr : r ∈ Icc (hi (jn i)) (lo (jo i))) :
      survivor i (0, r) = alphaS i r := by
    obtain ⟨k, rfl⟩ := e.surjective i
    rw [hSeq]
    exact (hgc.2.1 k r (by
      change r ∈ Icc (s (Q (.inr (.inl k))).castSucc) (s (Q (.inr (.inl k))).succ)
      simpa only [hSL, hSR] using hr)).self_of_nhds
  have hTCenter (r : ℝ) (hr : r ∈ Icc (hi jf) v) : tail (0, r) = gamma jf r :=
    (hgc.2.2 r ⟨(le_of_eq hTLlit).trans hr.1, hr.2.trans (le_of_eq hsv.symm)⟩).self_of_nhds.trans
      (hcenterT ⟨(le_of_eq hhi.symm).trans hr.1, hr.2⟩)
  have hFirstClock : lo jl = s 0 := hlo.trans hs0.symm
  have hFirstValue (z : P) : HEq (ordinary jl (z, lo jl)) (f 0 (z, s 0)) := by
    have hidx : Q.symm 0 = .inl 0 := by rw [← hqZero, Q.symm_apply_apply]
    have heq : g (Q.symm 0) (z, s 0) = f 0 (z, s 0) := congrFun (hgeq 0) (z, s 0)
    have hpoint := (congr_arg_heq (fun k => g k (z, s 0)) hidx.symm).trans (heq_of_eq heq)
    have hOzero : HEq (ordinary jl (z, lo jl)) (ordinary (j 0) (z, lo jl)) :=
      congr_arg_heq (fun x => ordinary x (z, lo jl)) hj0.symm
    rw [hOeq, hFirstClock] at hOzero
    simpa only [hFirstClock] using hOzero.trans hpoint
  have hFirstCenter : HEq (gamma jl (lo jl)) (alpha 0 (s 0)) := by
    have hidx : Q.symm 0 = .inl 0 := by rw [← hqZero, Q.symm_apply_apply]
    have hleft : HEq (alpha 0 (s 0)) (alphaO (j 0) (s 0)) := by
      change HEq (alpha0 (Q.symm 0) (s 0)) _
      exact congr_arg_heq (fun k => alpha0 k (s 0)) hidx
    have hv := hcenterO jl (left_mem_Icc.mpr (hgap jl).2.1.le)
    have hEq : HEq (gamma jl (lo jl)) (alphaO (j 0) (s 0)) := by
      have hpoint := congr_arg_heq (fun x => alphaO x (lo jl)) hj0.symm
      rw [hFirstClock] at hpoint
      exact (heq_of_eq hv.symm).trans (by simpa only [hFirstClock] using hpoint)
    exact hEq.trans hleft.symm
  have hfix (z : P) : ordinary jl (z, lo jl) = gamma jl (lo jl) :=
    eq_of_heq ((hFirstValue z).trans ((heq_of_eq (hfirst z)).trans hFirstCenter.symm))
  have hmatches (z : P) :
      (∀ i, ordinary (jn i) (z, hi (jn i)) = FC i (survivor i (z, hi (jn i))).val) ∧
      (∀ i, ordinary (jo i) (z, lo (jo i)) = (survivor i (z, lo (jo i))).val.val) ∧
      ordinary jf (z, hi jf) = tail (z, hi jf) :=
    hcompat P f z (hjoins z)
  have hexp' := hexp
  have hON' := hON
  have hsv' : s (Fin.last (2 * N + 1 + 1)) = v := hsv
  rw [hsv'] at hexp'
  rw [hsv'] at hON'
  rw [← hgeq (Fin.last (2 * N + 1))] at hexp'
  have htailPacket (k : Tag) (hk : k = .inr (.inr 0))
      (hexpK : (fun z => g k (z, v)) =ᶠ[𝓝 (0 : P)]
        (fun z => expMap ((S0 k).base.metric (T - v ^ 2)) (alpha0 k v)
          (show TangentSpace ThreeModel (alpha0 k v) from Bframe z)))
      (hONK : ∀ k1 k2,
        ((S0 k).base.metric (T - v ^ 2)).inner (alpha0 k v)
          (show TangentSpace ThreeModel (alpha0 k v) from Bframe (Pi.single k1 1))
          (show TangentSpace ThreeModel (alpha0 k v) from Bframe (Pi.single k2 1)) =
            if k1 = k2 then 1 else 0) :
      ((fun z => tail (z, v)) =ᶠ[𝓝 (0 : P)]
        (fun z => expMap (ST.base.metric (T - v ^ 2)) (gamma jf v)
          (show TangentSpace ThreeModel (gamma jf v) from Bframe z))) ∧
      (∀ k1 k2, (ST.base.metric (T - v ^ 2)).inner (gamma jf v)
        (show TangentSpace ThreeModel (gamma jf v) from Bframe (Pi.single k1 1))
        (show TangentSpace ThreeModel (gamma jf v) from Bframe (Pi.single k2 1)) =
          if k1 = k2 then 1 else 0) := by
    subst k
    have hvalueT' : alphaT v = gamma jf v := hvalueT
    constructor
    · have h : (fun z => tail (z, v)) =ᶠ[𝓝 (0 : P)]
          (fun z => expMap (ST.base.metric (T - v ^ 2)) (alphaT v)
            (show TangentSpace ThreeModel (alphaT v) from Bframe z)) := hexpK
      rw [hvalueT'] at h
      exact h
    · have h : ∀ k1 k2, (ST.base.metric (T - v ^ 2)).inner (alphaT v)
          (show TangentSpace ThreeModel (alphaT v) from Bframe (Pi.single k1 1))
          (show TangentSpace ThreeModel (alphaT v) from Bframe (Pi.single k2 1)) =
            if k1 = k2 then 1 else 0 := hONK
      rw [hvalueT'] at h
      exact h
  obtain ⟨hexpPhysical, hONPhysical⟩ := htailPacket _ htailIndex hexp' hON'
  have hbasisON : ∀ k1 k2, (ST.base.metric (T - v ^ 2)).inner (gamma jf v)
      (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis k1))
      (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis k2)) =
        if k1 = k2 then 1 else 0 := by
    intro k1 k2
    rw [show basis k1 = Pi.single k1 1 from Pi.basisFun_apply ℝ _ k1,
      show basis k2 = Pi.single k2 1 from Pi.basisFun_apply ℝ _ k2]
    exact hONPhysical k1 k2
  have hfield' : ∀ i k r, r ∈ Icc (s i.castSucc) (s i.succ) →
      Filter.EventuallyEq (β := ThreeSpace) (𝓝 r)
        (fun t => (mfderiv 𝓘(ℝ, P) ThreeModel (fun z => f i (z, t)) 0
          (basis k) : ThreeSpace))
        (fun t =>
          (SMul.smul ((t - s 0) / (v - s 0)) (Pframe i k t : ThreeSpace) : ThreeSpace)) := by
    intro i k r hr
    have h := hfield i k r hr
    rw [hsv'] at h
    rw [show basis k = Pi.single k 1 from Pi.basisFun_apply ℝ _ k]
    exact h
  have hindexInt' : ∀ i k, IntervalIntegrable
      (lRegularizedIndexIntegrand (S i) T (alpha i)
        (fun r => (SMul.smul ((r - s 0) / (v - s 0)) (Pframe i k r : ThreeSpace) : ThreeSpace))
        (fun r => (SMul.smul ((r - s 0) / (v - s 0)) (Pframe i k r : ThreeSpace) : ThreeSpace)))
      volume
      (s i.castSucc) (s i.succ) := by
    intro i k
    have h := hindexInt i k
    rw [hsv'] at h
    exact h
  let KO : J → Set ℝ := fun x => Ioo (lowO x) (highO x)
  let KS : E → Set ℝ := fun i => Ioo (lowS i) (highS i)
  let KT : Set ℝ := Ioo lowT highT
  have hKO (x : J) : IsOpen (KO x) ∧ IsPreconnected (KO x) ∧ lo x ∈ KO x ∧ hi x ∈ KO x :=
    ⟨isOpen_Ioo, isPreconnected_Ioo,
      ⟨(hmarginO x).1, (hgap x).2.1.trans (hmarginO x).2⟩,
      ⟨(hmarginO x).1.trans (hgap x).2.1, (hmarginO x).2⟩⟩
  have hKS (i : E) : IsOpen (KS i) ∧ IsPreconnected (KS i) ∧
      hi (jn i) ∈ KS i ∧ lo (jo i) ∈ KS i := by
    rw [(hjoin i).1, (hjoin i).2]
    have hcd := (hcollar i).2.1.trans (hcollar i).2.2.1
    exact ⟨isOpen_Ioo, isPreconnected_Ioo,
      ⟨(hmarginS i).1, hcd.trans (hmarginS i).2⟩,
      ⟨(hmarginS i).1.trans hcd, (hmarginS i).2⟩⟩
  have hKT : IsOpen KT ∧ IsPreconnected KT ∧ hi jf ∈ KT ∧ v ∈ KT := by
    rw [hhi]
    exact ⟨isOpen_Ioo, isPreconnected_Ioo, ⟨hlowT, hbv.trans hhighT⟩,
      ⟨hlowT.trans hbv, hhighT⟩⟩
  obtain ⟨Jclock, U, psi, F, hsupport, _hAction, hjets⟩ :=
    hReceive lo hi hbounds (by simpa only [hhi] using hbv)
      (by simpa only [hlo] using hprefixAC)
      W FC DO DS DT SO SS ST hold hnew j e s hs hs0 hOL hOR hSL hSR hTL hsv
      alphaO alphaS alphaT f hf hgeoO hgeoS' hgeoT' hcenter Phi
      (fun i => (hPhi i).2.2.2.1) hjoins (fun i => (hPhi i).2.2.2.2.1) hfirst
      hSO hSS hST hmetricO hmetricT hCross hOldHalf hNewHalf
      univ isOpen_univ (mem_univ _) KO KS KT hKO hKS hKT hregO hregS hregT
      (fun z _ => hfix z) (fun z _ => (hmatches z).2.1)
      (fun z _ => (hmatches z).1) (fun z _ => (hmatches z).2.2)
      hOCenter
      (fun i r hr => by
        change (survivor i (0, r)).val.val = gamma (jo i) r
        rw [hSCenter i r ⟨(hstrict i).1.le.trans hr.1, hr.2⟩]
        exact hcenterOld i (by simpa only [(hjoin i).2] using hr))
      (fun i r hr => by
        change FC i (survivor i (0, r)).val = gamma (jn i) r
        rw [hSCenter i r ⟨hr.1, hr.2.trans (hstrict i).2.le⟩]
        exact hcenterNew i (by simpa only [(hjoin i).1] using hr))
      hTCenter Bframe hexpPhysical basis hbasisON hFirstClock
      (by simpa only [hs0] using hboundsCut) Pframe hLag hHam hregFrame
      (fun i _ _ => (hsmFlat i).mdifferentiableAt (by simp)) hP
      (fun i k r hr => hAdapted i k r ((hOmegaFrame i).2.1 hr))
      (fun i k l => hONframe i (s i.succ) (right_mem_Icc.mpr
        (hs.monotone i.castSucc_le_succ)) k l)
      hindexInt' hscalarJoin hlagJoin hfield' hvelocityT
  obtain ⟨_hJ, _hvJ, _hJKT, _hJtimes, _hActionSmooth, hU, hqU, _hpsiSmooth,
      hFSmooth, _hpsiCenter, hFvalue, hcostF, hsupportNear⟩ := hsupport
  obtain ⟨hgradient, hclock, _htraceExact, htraceApprox, hphysicalSupport⟩ := hjets
  exact ⟨U, F, hU, hqU, hFSmooth, hFvalue, hcostF,
    (fun z hz => (hsupportNear z hz).2.2.2.2), hgradient, hclock, htraceApprox,
    hphysicalSupport⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
