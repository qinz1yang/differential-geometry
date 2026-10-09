import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointFirstVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointSecondVariation
import DifferentialGeometry.Geometry.Connection.Hessian.FiniteScalarTrace

/-!
# S-CH11-FIX4 `PortC11P` port

Module `Perelman.LGeometry.Action.Regularized.FiniteJointBranchJets`.

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (about 25 errors; the first is that
`open scoped Topology` inside the namespace is read as `_root_.DifferentialGeometry.Topology`).
Elaboration-level repairs, in the order of the file:
* `open scoped _root_.Topology`.  Both theorems: the docstring is moved below
  `attribute [-instance] .. in` (a docstring cannot precede `attribute .. in theorem`).
* `hA0`: `simp only [A, v, last, hpsi0]` (`v`/`last` are let-bound and `hpsi0` is stated with
  `b (Fin.last n)`).  `hgraphAction`: `rw [show A (G z) = z from hleftz]`.
* `hray`: `hcont : Continuous (fun u : ℝ => u • ξ)` then `hcont.tendsto 0`; the closing
  `simpa only [hexpu, map_smul] using hactu` becomes `h2 : f last (u • ξ, v) = expMap g q (u • ..)`
  (from `hexpu` by `simp only [Function.comp_apply, map_smul] at h3; exact h3`), `rw [h2] at hactu`.
* `hActD`: `simpa only [hcenter] using hh` becomes `hc' : f (Fin.last n) (0, b (Fin.last n)) = q
  := hcenter`, `rw [hc'] at hh`, `exact hh`.  `hcomposed`: `simpa only [zero_add] using hh` becomes
  `exact hh.congr_mfderiv (zero_add _)`.
* `hGD`: closing `rfl` after the `rw`.  `htime`: `simpa only [..] using map_smul ..` becomes
  `have h := map_smul ..; simp only [smul_eq_mul, mul_one] at h; exact h`.
* `hsum`: first summand ascribed `show TangentSpace I q from ..` (no `HAdd` between the tangent
  spaces at `f last (0, v)` and `q`).  `hinnerVal`: `simpa only [map_add, ..] using hinner`
  becomes `rw [map_add, map_smul, smul_eq_mul] at h; exact h`.
* `hspaceD`: `simp [dBranch, ..]` becomes `change g.inner q velocity X + clock • (0 : ℝ) = ..;
  rw [smul_zero, add_zero]`.
* `hclock`: `hh` gets its type `HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun w : ℝ => F (q, w)) v _` with
  `hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := I)`, and `hh.hasFDerivAt` becomes
  `hhF0 : HasFDerivAt .. (_ : ℝ →L[ℝ] ℝ) v := hasMFDerivAt_iff_hasFDerivAt.mp hh` (the instance
  problem `ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, ℝ) v)` was stuck).
No statement, definition or proof idea is altered.  The module
`Perelman.LGeometry.Action.Regularized.FiniteJointBranchJets` is a shim re-exporting this file.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology BigOperators

universe uM uE uH uP

variable {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
  {D : Fin (n + 1) → RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- All jets of one existing endpoint/action branch. The hypotheses are exactly
its local C2, inverse and action data; all first and second variations are derived
from the same finite family, genuine vector seams, and physical terminal exp. -/
theorem finiteJointAction_endpoint_branch_jets
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (f : (i : Fin (n + 1)) → P × ℝ → M i)
    (hf : ∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (f i))
    (a b : Fin (n + 1) → ℝ)
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T
      (fun r => f i (0, r)) (uIcc (a i) (b i)))
    (Phi : (i : Fin n) → PartialDiffeomorph I I (M i.castSucc) (M i.succ) ∞)
    (hmetric : ∀ (i : Fin n) (x : M i.castSucc), x ∈ (Phi i).source →
      ∀ V W : TangentSpace I x,
      ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner x V W =
        ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner (Phi i x)
          (mfderiv I I (Phi i : M i.castSucc → M i.succ) x V)
          (mfderiv I I (Phi i : M i.castSucc → M i.succ) x W))
    (hjoin : ∀ᶠ z in 𝓝 (0 : P), ∀ i : Fin n,
      f i.castSucc (z, b i.castSucc) ∈ (Phi i).source ∧
      Phi i (f i.castSucc (z, b i.castSucc)) = f i.succ (z, a i.succ))
    (hvelocity : ∀ i : Fin n,
      (mfderiv I I (Phi i : M i.castSucc → M i.succ)
        (f i.castSucc (0, b i.castSucc))
        (lVelocity (I := I) (fun r => f i.castSucc (0, r)) (b i.castSucc)) : E) =
          lVelocity (I := I) (fun r => f i.succ (0, r)) (a i.succ))
    (p : M 0)
    (hfirst : (fun z => f 0 (z, a 0)) =ᶠ[𝓝 (0 : P)] fun _ => p)
    (C : ℝ) {V : Set P}
    (K : Fin (n + 1) → Set ℝ) (hK : ∀ i, IsOpen (K i))
    (hKconn : ∀ i, IsPreconnected (K i))
    (ha : ∀ i, a i ∈ K i) (hb : ∀ i, b i ∈ K i)
    (hreg : ∀ i r, r ∈ K i → T - r ^ 2 ∈ (D i).regular)
    (q : M (Fin.last n)) (B : P ≃L[ℝ] E)
    (hexp : (fun z => f (Fin.last n) (z, b (Fin.last n))) =ᶠ[𝓝 (0 : P)]
      (fun z => expMap ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2))
        q (show TangentSpace I q from B z)))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx ℝ P)
    (hON : ∀ i j,
      ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2)).inner q
        (show TangentSpace I q from B (basis i)) (show TangentSpace I q from B (basis j)) =
          if i = j then 1 else 0)
    {U : Set (M (Fin.last n) × ℝ)}
    {psi : M (Fin.last n) × ℝ → P} {F : M (Fin.last n) × ℝ → ℝ}
    (hU : IsOpen U) (hqU : (q, b (Fin.last n)) ∈ U)
    (hpsi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U)
    (hpsi0 : psi (q, b (Fin.last n)) = 0)
    (hdata : ∀ z ∈ U, psi z ∈ V ∧ z.2 ∈ K (Fin.last n) ∧
      f (Fin.last n) (psi z, z.2) = z.1 ∧
      F z = C + finiteJointAction S T f a b (psi z, z.2)) :
    let v := b (Fin.last n)
    let g := (S (Fin.last n)).base.metric (T - v ^ 2)
    let velocity : TangentSpace I q :=
      show E from lVelocity (I := I) (fun r => f (Fin.last n) (0, r)) v
    let clock := 2 * v ^ 2 * (S (Fin.last n)).scalar (T - v ^ 2) q -
      (1 / 2 : ℝ) * g.inner q velocity velocity
    HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) F (q, v)
      ((g.inner q velocity).comp (ContinuousLinearMap.fst ℝ E ℝ) +
        clock • ContinuousLinearMap.snd ℝ E ℝ) ∧
    gradientFun g (fun y => F (y, v)) q = velocity ∧
    HasDerivAt (fun w => F (q, w)) clock v ∧
    (∀ ξ : P, abstractHessian g (fun y => F (y, v)) q
      (show TangentSpace I q from B ξ) (show TangentSpace I q from B ξ) =
        2 * ∑ i : Fin (n + 1), lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := I) (fun u => f i (u • ξ, r)) 0)
          (fun r => lVelocity (I := I) (fun u => f i (u • ξ, r)) 0) (a i) (b i)) ∧
    laplacian (LeviCivita g) g (fun y => F (y, v)) q =
      2 * ∑ i : Fin (n + 1), ∑ k : Idx,
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := I) (fun u => f i (u • basis k, r)) 0)
          (fun r => lVelocity (I := I) (fun u => f i (u • basis k, r)) 0) (a i) (b i) ∧
    (∀ ξ : P, (fun u : ℝ => F (expMap g q (u • (show TangentSpace I q from B ξ)), v))
      =ᶠ[𝓝 0] (fun u => C + finiteJointAction S T f a b (u • ξ, v))) := by
  classical
  let last := Fin.last n
  let v := b last
  let g := (S last).base.metric (T - v ^ 2)
  let velocity : TangentSpace I q :=
    show E from lVelocity (I := I) (fun r => f last (0, r)) v
  let clock := 2 * v ^ 2 * (S last).scalar (T - v ^ 2) q -
    (1 / 2 : ℝ) * g.inner q velocity velocity
  let J := 𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)
  let L := I.prod 𝓘(ℝ, ℝ)
  let G : P × ℝ → M last × ℝ := fun z => (f last z, z.2)
  let A : M last × ℝ → P × ℝ := fun z => (psi z, z.2)
  let Act := finiteJointAction S T f a b
  have hf2 : ContMDiffAt J I 2 (f last) (0, v) :=
    (hf last).contMDiffAt.of_le (by norm_num)
  obtain ⟨hcenter, hloc⟩ :=
    DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_parameter_graph_of_exponential_germ_two
      g q B hf2 hexp
  have hG0 : G (0, v) = (q, v) := by simp only [G, hcenter]
  have hA0 : A (q, v) = (0, v) := by simp only [A, v, last, hpsi0]
  have hA2 : ContMDiffAt L J 2 A (q, v) :=
    (hpsi.contMDiffAt (hU.mem_nhds hqU)).prodMk contMDiffAt_snd
  have hF2 : ContMDiffAt L 𝓘(ℝ, ℝ) 2 F (q, v) :=
    hF.contMDiffAt (hU.mem_nhds hqU)
  have hG2 : ContMDiffAt J L 2 G (0, v) := hf2.prodMk contMDiffAt_snd
  have hright : (G ∘ A) =ᶠ[𝓝 (q, v)] id := by
    filter_upwards [hU.mem_nhds hqU] with z hz
    exact Prod.ext (hdata z hz).2.2.1 rfl
  have hActEq : F =ᶠ[𝓝 (q, v)] (fun z => C + Act (A z)) := by
    filter_upwards [hU.mem_nhds hqU] with z hz
    exact (hdata z hz).2.2.2
  have hGt : Tendsto G (𝓝 (0, v)) (𝓝 (q, v)) := by
    simpa only [hG0] using hG2.continuousAt.tendsto
  have hAGt : Tendsto (A ∘ G) (𝓝 (0, v)) (𝓝 (0, v)) := by
    simpa only [hA0] using hA2.continuousAt.tendsto.comp hGt
  have hleft : (A ∘ G) =ᶠ[𝓝 ((0 : P), v)] id := by
    have hW := hloc.localInverse.open_target.mem_nhds hloc.localInverse_mem_target
    filter_upwards [hW, hAGt.eventually hW, hGt.eventually (hU.mem_nhds hqU)] with z hz hAz hGz
    have hGA : G (A (G z)) = G z := Prod.ext (hdata (G z) hGz).2.2.1 rfl
    calc
      A (G z) = hloc.localInverse (G (A (G z))) :=
        (hloc.localInverse_left_inv hAz).symm
      _ = hloc.localInverse (G z) := congrArg hloc.localInverse hGA
      _ = z := hloc.localInverse_left_inv hz
  have hgraphAction : (F ∘ G) =ᶠ[𝓝 ((0 : P), v)] (fun z => C + Act z) := by
    filter_upwards [hleft, hGt.eventually (hU.mem_nhds hqU)] with z hleftz hGz
    change F (G z) = C + Act z
    rw [(hdata (G z) hGz).2.2.2]
    change C + Act (A (G z)) = C + Act z
    rw [show A (G z) = z from hleftz]
  have hray (ξ : P) :
      (fun u : ℝ => F (expMap g q (u • (show TangentSpace I q from B ξ)), v))
        =ᶠ[𝓝 0] (fun u => C + Act (u • ξ, v)) := by
    have ht : Tendsto (fun u : ℝ => u • ξ) (𝓝 0) (𝓝 (0 : P)) := by
      have hcont : Continuous (fun u : ℝ => u • ξ) := continuous_id.smul continuous_const
      simpa only [zero_smul] using hcont.tendsto 0
    have hpairt : Tendsto (fun u : ℝ => (u • ξ, v)) (𝓝 0) (𝓝 ((0 : P), v)) :=
      ht.prodMk_nhds tendsto_const_nhds
    filter_upwards [hgraphAction.comp_tendsto hpairt, hexp.comp_tendsto ht] with u hactu hexpu
    change F (f last (u • ξ, v), v) = C + Act (u • ξ, v) at hactu
    have h2 : f last (u • ξ, v) = expMap g q (u • (show TangentSpace I q from B ξ)) := by
      have h3 := hexpu
      simp only [Function.comp_apply, map_smul] at h3
      exact h3
    rw [h2] at hactu
    exact hactu
  let dAct : P × ℝ →L[ℝ] ℝ :=
    ((g.inner q velocity).comp (mfderiv 𝓘(ℝ, P) I (fun z => f last (z, v)) 0)).comp
      (ContinuousLinearMap.fst ℝ P ℝ) +
      (lRegularizedLagrangian (S last) T (fun r => f last (0, r)) v) •
        ContinuousLinearMap.snd ℝ P ℝ
  have hActD : HasMFDerivAt J 𝓘(ℝ, ℝ) Act (0, v) dAct := by
    have hh := (hasFDerivAt_finiteJointAction S hS T f hf a b hgeo Phi hmetric
      hjoin hvelocity p hfirst K hK hKconn ha hb hreg).hasMFDerivAt
    have hc' : f (Fin.last n) (0, b (Fin.last n)) = q := hcenter
    rw [hc'] at hh
    exact hh
  have hGMD : MDifferentiableAt J L G (A (q, v)) := by
    rw [hA0]
    exact hG2.mdifferentiableAt (by norm_num)
  have hAMD : MDifferentiableAt L J A (q, v) := hA2.mdifferentiableAt (by norm_num)
  have hrightD : (mfderiv J L G (0, v)).comp (mfderiv L J A (q, v)) =
      ContinuousLinearMap.id ℝ (E × ℝ) := by
    have hd := hright.mfderiv_eq (I := L) (I' := L)
    rw [mfderiv_comp (q, v) hGMD hAMD, mfderiv_id, hA0] at hd
    exact hd
  have hcomposed : HasMFDerivAt L 𝓘(ℝ, ℝ) (fun z => C + Act (A z)) (q, v)
      (dAct.comp (mfderiv L J A (q, v))) := by
    have hActAt : HasMFDerivAt J 𝓘(ℝ, ℝ) Act (A (q, v)) dAct := by
      rw [hA0]
      exact hActD
    have hh := (hasMFDerivAt_const (I := L) C (q, v)).add
      (hActAt.comp (q, v) hAMD.hasMFDerivAt)
    exact hh.congr_mfderiv (zero_add _)
  let dBranch : E × ℝ →L[ℝ] ℝ :=
    (g.inner q velocity).comp (ContinuousLinearMap.fst ℝ E ℝ) +
      clock • ContinuousLinearMap.snd ℝ E ℝ
  have hdBranch : dAct.comp (mfderiv L J A (q, v)) = dBranch := by
    ext w
    let z : P × ℝ := mfderiv L J A (q, v) w
    have hrightVal : mfderiv J L G (0, v) z = w := by
      have hh := congrArg (fun Q : E × ℝ →L[ℝ] E × ℝ => Q w) hrightD
      exact hh
    have hfMD : MDifferentiableAt J I (f last) (0, v) :=
      hf2.mdifferentiableAt (by norm_num)
    have hGD : mfderiv J L G (0, v) =
        (mfderiv J I (f last) (0, v)).prod (ContinuousLinearMap.snd ℝ P ℝ) := by
      rw [show G = (fun z => (f last z, z.2)) from rfl,
        mfderiv_prodMk hfMD mdifferentiableAt_snd, mfderiv_snd]
      rfl
    rw [hGD] at hrightVal
    change (mfderiv J I (f last) (0, v) z, z.2) = w at hrightVal
    have hspaceVal := congrArg Prod.fst hrightVal
    have hclockVal : z.2 = w.2 := congrArg Prod.snd hrightVal
    have hsplit := mfderiv_prod_eq_add_apply hfMD (v := z)
    have htime : mfderiv 𝓘(ℝ, ℝ) I (fun r => f last (0, r)) v z.2 =
        z.2 • velocity := by
      change mfderiv 𝓘(ℝ, ℝ) I (fun r => f last (0, r)) v z.2 =
        z.2 • mfderiv 𝓘(ℝ, ℝ) I (fun r => f last (0, r)) v (1 : ℝ)
      have h := map_smul (mfderiv 𝓘(ℝ, ℝ) I (fun r => f last (0, r)) v) z.2 (1 : ℝ)
      simp only [smul_eq_mul, mul_one] at h
      exact h
    have hsum : (show TangentSpace I q from mfderiv 𝓘(ℝ, P) I (fun x => f last (x, v)) 0 z.1) +
        z.2 • velocity = w.1 := by
      rw [← htime]
      exact hsplit.symm.trans hspaceVal
    have hinner := congrArg (g.inner q velocity) hsum
    have hinnerVal : g.inner q velocity
        (mfderiv 𝓘(ℝ, P) I (fun x => f last (x, v)) 0 z.1) =
          g.inner q velocity w.1 - z.2 * g.inner q velocity velocity := by
      apply (eq_sub_iff_add_eq).2
      have h := hinner
      rw [map_add, map_smul, smul_eq_mul] at h
      exact h
    change g.inner q velocity
        (mfderiv 𝓘(ℝ, P) I (fun x => f last (x, v)) 0 z.1) +
        lRegularizedLagrangian (S last) T (fun r => f last (0, r)) v * z.2 =
      g.inner q velocity w.1 + clock * w.2
    rw [hinnerVal, hclockVal]
    dsimp only [lRegularizedLagrangian, clock]
    rw [hcenter]
    change g.inner q velocity w.1 - w.2 * g.inner q velocity velocity +
        ((1 / 2 : ℝ) * g.inner q velocity velocity +
          2 * v ^ 2 * (S last).scalar (T - v ^ 2) q) * w.2 =
      g.inner q velocity w.1 +
        (2 * v ^ 2 * (S last).scalar (T - v ^ 2) q -
          (1 / 2 : ℝ) * g.inner q velocity velocity) * w.2
    ring
  have hFD : HasMFDerivAt L 𝓘(ℝ, ℝ) F (q, v) dBranch := by
    rw [hdBranch] at hcomposed
    exact hcomposed.congr_of_eventuallyEq_abuse hActEq
  have hspaceD : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => F (y, v)) q
      (g.inner q velocity) := by
    have hh := hFD.comp q ((hasMFDerivAt_id q).prodMk (hasMFDerivAt_const v q))
    apply hh.congr_mfderiv
    ext X
    change g.inner q velocity X + clock • (0 : ℝ) = g.inner q velocity X
    rw [smul_zero, add_zero]
  have hgradient : gradientFun g (fun y => F (y, v)) q = velocity := by
    apply gradientFun_eq_of_flat
    ext X
    change mvfderiv (I := I) (fun y => F (y, v)) q X = _
    rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv, hspaceD.mfderiv]
    rfl
  have hclock : HasDerivAt (fun w => F (q, w)) clock v := by
    have hh : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun w : ℝ => F (q, w)) v _ :=
      hFD.comp v ((hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := I) q v).prodMk (hasMFDerivAt_id v))
    have hhF0 : HasFDerivAt (fun w : ℝ => F (q, w)) (_ : ℝ →L[ℝ] ℝ) v :=
      hasMFDerivAt_iff_hasFDerivAt.mp hh
    have hhF := hhF0.hasDerivAt
    apply hhF.congr_deriv
    change g.inner q velocity 0 + clock * 1 = clock
    simp
  have hslice : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => F (y, v)) q :=
    hF2.comp q (contMDiffAt_id.prodMk contMDiffAt_const)
  have hhessian (ξ : P) : abstractHessian g (fun y => F (y, v)) q
      (show TangentSpace I q from B ξ) (show TangentSpace I q from B ξ) =
        2 * ∑ i : Fin (n + 1), lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := I) (fun u => f i (u • ξ, r)) 0)
          (fun r => lVelocity (I := I) (fun u => f i (u • ξ, r)) 0) (a i) (b i) := by
    rw [abstractHessian_eq_deriv_deriv_expMap_of_contMDiffAt_two g hslice]
    rw [(hray ξ).deriv.deriv_eq, deriv_const_add']
    exact (hasDerivAt_deriv_finiteJointAction_line S hS T f hf a b hgeo Phi hmetric
      hjoin hvelocity p hfirst q B.toContinuousLinearMap hexp ξ).deriv
  have hlap : laplacian (LeviCivita g) g (fun y => F (y, v)) q =
      2 * ∑ i : Fin (n + 1), ∑ k : Idx,
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := I) (fun u => f i (u • basis k, r)) 0)
          (fun r => lVelocity (I := I) (fun u => f i (u • basis k, r)) 0) (a i) (b i) := by
    let frame : Module.Basis Idx ℝ (TangentSpace I q) := basis.map B.toLinearEquiv
    have hframe : ∀ i j, g.inner q (frame i) (frame j) = if i = j then 1 else 0 := hON
    rw [laplacian_eq_sum_abstractHessian_of_contMDiffAt_two g hslice frame hframe]
    change (∑ k : Idx, abstractHessian g (fun y => F (y, v)) q
      (show TangentSpace I q from B (basis k)) (show TangentSpace I q from B (basis k))) = _
    simp_rw [hhessian]
    rw [← Finset.mul_sum, Finset.sum_comm]
  exact ⟨hFD, hgradient, hclock, hhessian, hlap, hray⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Construct one finite endpoint/action branch and retain its full original
identities together with all its derived jets. -/
theorem exists_finiteJointAction_endpoint_branch_with_jets
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (f : (i : Fin (n + 1)) → P × ℝ → M i)
    (hf : ∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (f i))
    (a b : Fin (n + 1) → ℝ)
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T
      (fun r => f i (0, r)) (uIcc (a i) (b i)))
    (Phi : (i : Fin n) → PartialDiffeomorph I I (M i.castSucc) (M i.succ) ∞)
    (hmetric : ∀ (i : Fin n) (x : M i.castSucc), x ∈ (Phi i).source →
      ∀ V W : TangentSpace I x,
      ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner x V W =
        ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner (Phi i x)
          (mfderiv I I (Phi i : M i.castSucc → M i.succ) x V)
          (mfderiv I I (Phi i : M i.castSucc → M i.succ) x W))
    (hjoin : ∀ᶠ z in 𝓝 (0 : P), ∀ i : Fin n,
      f i.castSucc (z, b i.castSucc) ∈ (Phi i).source ∧
      Phi i (f i.castSucc (z, b i.castSucc)) = f i.succ (z, a i.succ))
    (hvelocity : ∀ i : Fin n,
      (mfderiv I I (Phi i : M i.castSucc → M i.succ)
        (f i.castSucc (0, b i.castSucc))
        (lVelocity (I := I) (fun r => f i.castSucc (0, r)) (b i.castSucc)) : E) =
          lVelocity (I := I) (fun r => f i.succ (0, r)) (a i.succ))
    (p : M 0)
    (hfirst : (fun z => f 0 (z, a 0)) =ᶠ[𝓝 (0 : P)] fun _ => p)
    (C : ℝ) {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    (K : Fin (n + 1) → Set ℝ) (hK : ∀ i, IsOpen (K i))
    (hKconn : ∀ i, IsPreconnected (K i))
    (ha : ∀ i, a i ∈ K i) (hb : ∀ i, b i ∈ K i)
    (hreg : ∀ i r, r ∈ K i → T - r ^ 2 ∈ (D i).regular)
    (q : M (Fin.last n)) (B : P ≃L[ℝ] E)
    (hexp : (fun z => f (Fin.last n) (z, b (Fin.last n))) =ᶠ[𝓝 (0 : P)]
      (fun z => expMap ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2))
        q (show TangentSpace I q from B z)))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx ℝ P)
    (hON : ∀ i j,
      ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2)).inner q
        (show TangentSpace I q from B (basis i)) (show TangentSpace I q from B (basis j)) =
          if i = j then 1 else 0)
    : ∃ (U : Set (M (Fin.last n) × ℝ)) (psi : M (Fin.last n) × ℝ → P)
      (F : M (Fin.last n) × ℝ → ℝ),
      IsOpen U ∧ (q, b (Fin.last n)) ∈ U ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      psi (q, b (Fin.last n)) = 0 ∧
      F (q, b (Fin.last n)) = C + finiteJointAction S T f a b (0, b (Fin.last n)) ∧
      (∀ z ∈ U, psi z ∈ V ∧ z.2 ∈ K (Fin.last n) ∧
        f (Fin.last n) (psi z, z.2) = z.1 ∧
        F z = C + finiteJointAction S T f a b (psi z, z.2)) ∧
    let v := b (Fin.last n)
    let g := (S (Fin.last n)).base.metric (T - v ^ 2)
    let velocity : TangentSpace I q :=
      show E from lVelocity (I := I) (fun r => f (Fin.last n) (0, r)) v
    let clock := 2 * v ^ 2 * (S (Fin.last n)).scalar (T - v ^ 2) q -
      (1 / 2 : ℝ) * g.inner q velocity velocity
    HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) F (q, v)
      ((g.inner q velocity).comp (ContinuousLinearMap.fst ℝ E ℝ) +
        clock • ContinuousLinearMap.snd ℝ E ℝ) ∧
    gradientFun g (fun y => F (y, v)) q = velocity ∧
    HasDerivAt (fun w => F (q, w)) clock v ∧
    (∀ ξ : P, abstractHessian g (fun y => F (y, v)) q
      (show TangentSpace I q from B ξ) (show TangentSpace I q from B ξ) =
        2 * ∑ i : Fin (n + 1), lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := I) (fun u => f i (u • ξ, r)) 0)
          (fun r => lVelocity (I := I) (fun u => f i (u • ξ, r)) 0) (a i) (b i)) ∧
    laplacian (LeviCivita g) g (fun y => F (y, v)) q =
      2 * ∑ i : Fin (n + 1), ∑ k : Idx,
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := I) (fun u => f i (u • basis k, r)) 0)
          (fun r => lVelocity (I := I) (fun u => f i (u • basis k, r)) 0) (a i) (b i) ∧
    (∀ ξ : P, (fun u : ℝ => F (expMap g q (u • (show TangentSpace I q from B ξ)), v))
      =ᶠ[𝓝 0] (fun u => C + finiteJointAction S T f a b (u • ξ, v))) := by
  obtain ⟨U, psi, F, hU, hqU, hpsi, hF, hpsi0, hF0, hdata⟩ :=
    exists_finiteJointAction_endpoint_branch S hS T C f a b hV h0 K hK hKconn ha hb
      (fun i => (hf i).contMDiffOn) hreg q B hexp
  exact ⟨U, psi, F, hU, hqU, hpsi, hF, hpsi0, hF0, hdata,
    finiteJointAction_endpoint_branch_jets S hS T f hf a b hgeo Phi hmetric hjoin
      hvelocity p hfirst C K hK hKconn ha hb hreg q B hexp basis hON
      hU hqU hpsi hF hpsi0 hdata⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
