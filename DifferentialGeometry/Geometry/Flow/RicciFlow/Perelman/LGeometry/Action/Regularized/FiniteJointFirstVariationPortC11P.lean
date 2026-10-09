import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FirstVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FamilyContinuity

/-!
# S-CH11-FIX4 `PortC11P` port

Module `Perelman.LGeometry.Action.Regularized.FiniteJointFirstVariation`.

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (11 errors in the two theorems; the heartbeat
timeouts reported at the donor lines 144 and 232 are the same failing unification as below, not a
genuine budget problem: the repaired file compiles in a few seconds with the default budget and
no budget option).  Elaboration-level repairs:
* `open scoped _root_.Topology` instead of `open scoped Topology` (namespace clash, `𝓝` unknown).
* `hline` (line theorem): `hcont : Continuous (fun u : ℝ => u • ξ)` stated first, then
  `hcont.tendsto 0`.  `hjoinBeta`: `hline.eventually hjoin` for `hjoin.comp_tendsto hline`.
* `hvel`: `simpa only [left, beta, zero_smul] using hvelocity i` becomes
  `simp only [left, beta]; rw [zero_smul]; exact hvelocity i` (`zero_smul` is not a `simp` step
  inside the dependent `mfderiv` arguments; `rw` abstracts all occurrences at once).
* `hmatch`: a closing `rfl` after the `rw [..]` (the two sides differ in `TangentSpace`/`E`
  instance paths only).  Final step of the line theorem: `simpa only [pair, beta, zero_smul]
  using hresult` becomes `have h := hresult; simp only [pair, beta] at h; rw [zero_smul] at h;
  exact h`.
* `hspace`: `simpa only [one_smul, id_eq]` in `hline`; `hlineAct := hbase.comp_hasDerivAt_of_eq ..`
  by `exact` (the `simpa` check saw `Real.instAddCommGroup` vs `normedAddCommGroup` paths as
  different); `hendAt` by `rw [zero_smul]; exact ..`; `hcomp` gets its type
  `HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u => f last (u • ξ, v)) 0 _` and `HasMFDerivAt.comp` gets
  `(g := endMap) (f := fun u : ℝ => u • ξ)` (the same repair as `FiniteJointRayTrace`, so that
  `rw [hcomp.mfderiv]` finds the syntactic form).
* `hlagK`: `hcomp := hlag.comp (f := fun r : ℝ => ((0 : P), r)) ..` then `exact hcomp` (the one-term
  `exact` made the unifier expand `lRegularizedLagrangian` until the heartbeat limit).
* `hfd`: `refine ContinuousLinearMap.ext fun z => ?_` replaces `ext z` (the current `ext` lemma
  splits `P × ℝ` and introduces `z : P`).
No statement, definition or proof idea is altered.  The module
`Perelman.LGeometry.Action.Regularized.FiniteJointFirstVariation` is a shim re-exporting this file.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff _root_.Topology BigOperators

universe uM uE uH uP

variable {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
  {D : Fin (n + 1) → RealTimeInterval}

/-- First variation of the same finite action along a parameter line.
Only endpoint parameter germs and genuine vector transmission are used at seams. -/
theorem hasDerivAt_finiteJointAction_line
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
    (ξ : P) :
    HasDerivAt (fun u : ℝ => finiteJointAction S T f a b (u • ξ, b (Fin.last n)))
      (((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2)).inner
        (f (Fin.last n) (0, b (Fin.last n)))
        (lVelocity (I := I) (fun u => f (Fin.last n) (u • ξ, b (Fin.last n))) 0)
        (lVelocity (I := I) (fun r => f (Fin.last n) (0, r)) (b (Fin.last n)))) 0 := by
  let beta : (i : Fin (n + 1)) → ℝ → ℝ → M i := fun i u r => f i (u • ξ, r)
  have hbeta (i : Fin (n + 1)) : IsSmoothVariation (I := I) (beta i) :=
    (hf i).comp ((contMDiff_fst.smul contMDiff_const).prodMk contMDiff_snd)
  have hgeoBeta (i : Fin (n + 1)) :
      IsLRegularizedGeodesicOn (S i) T (beta i 0) (uIcc (a i) (b i)) := by
    simpa only [beta, zero_smul] using hgeo i
  have hline : Tendsto (fun u : ℝ => u • ξ) (𝓝 0) (𝓝 (0 : P)) := by
    have hcont : Continuous (fun u : ℝ => u • ξ) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hcont.tendsto 0
  have hjoinBeta : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ i : Fin n,
      beta i.castSucc u (b i.castSucc) ∈ (Phi i).source ∧
      Phi i (beta i.castSucc u (b i.castSucc)) = beta i.succ u (a i.succ) :=
    hline.eventually hjoin
  let pair (i : Fin (n + 1)) (r : ℝ) :=
    ((S i).base.metric (T - r ^ 2)).inner (beta i 0 r)
      (lVelocity (I := I) (fun u => beta i u r) 0)
      (lVelocity (I := I) (beta i 0) r)
  have hmatch (i : Fin n) : pair i.castSucc (b i.castSucc) = pair i.succ (a i.succ) := by
    let left : ℝ → M i.castSucc := fun u => beta i.castSucc u (b i.castSucc)
    let right : ℝ → M i.succ := fun u => beta i.succ u (a i.succ)
    have hj : ∀ᶠ u in 𝓝 (0 : ℝ), left u ∈ (Phi i).source ∧ Phi i (left u) = right u :=
      hjoinBeta.mono (fun _ hu => hu i)
    have hpoint : Phi i (left 0) = right 0 := hj.self_of_nhds.2
    have heq : right =ᶠ[𝓝 (0 : ℝ)] (Phi i : M i.castSucc → M i.succ) ∘ left :=
      hj.mono (fun _ hu => hu.2.symm)
    have hl : MDifferentiableAt 𝓘(ℝ, ℝ) I left 0 :=
      (((hbeta i.castSucc : ContMDiff _ _ (8 : ℕ) _).comp
        (contMDiff_id.prodMk contMDiff_const)).contMDiffAt).mdifferentiableAt (by norm_num)
    have hvar : (lVelocity (I := I) right 0 : E) =
        mfderiv I I (Phi i : M i.castSucc → M i.succ) (left 0)
          (lVelocity (I := I) left 0) := by
      unfold lVelocity
      rw [heq.mfderiv_eq,
        mfderiv_comp 0 ((Phi i).mdifferentiableAt (by simp) hj.self_of_nhds.1) hl]
      rfl
    have hvel : (mfderiv I I (Phi i : M i.castSucc → M i.succ) (left 0)
        (lVelocity (I := I) (beta i.castSucc 0) (b i.castSucc)) : E) =
          lVelocity (I := I) (beta i.succ 0) (a i.succ) := by
      simp only [left, beta]
      rw [zero_smul]
      exact hvelocity i
    change ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner (left 0)
        (lVelocity (I := I) left 0) (lVelocity (I := I) (beta i.castSucc 0) (b i.castSucc)) =
      ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner (right 0)
        (lVelocity (I := I) right 0) (lVelocity (I := I) (beta i.succ 0) (a i.succ))
    rw [hmetric i (left 0) hj.self_of_nhds.1, hvel, hpoint, hvar]
    rfl
  have hfirstBeta : (fun u => beta 0 u (a 0)) =ᶠ[𝓝 (0 : ℝ)] fun _ => p :=
    hfirst.comp_tendsto hline
  have hfirstVel : lVelocity (I := I) (fun u => beta 0 u (a 0)) 0 = 0 := by
    unfold lVelocity
    rw [hfirstBeta.mfderiv_eq, mfderiv_const]
    rfl
  have hfirstPair : pair 0 (a 0) = 0 := by
    simp only [pair, hfirstVel, map_zero, zero_apply]
  have hboundary : (∑ i : Fin (n + 1), (pair i (b i) - pair i (a i))) =
      pair (Fin.last n) (b (Fin.last n)) := by
    rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp_rw [hmatch]
    rw [hfirstPair]
    ring
  have hEuler (i : Fin (n + 1)) :
      (∫ r in (a i)..(b i), lRegularizedEulerPair (S i) T (beta i 0) r
        (lVelocity (I := I) (fun u => beta i u r) 0)) = 0 := by
    have heq : (∫ r in (a i)..(b i), lRegularizedEulerPair (S i) T (beta i 0) r
        (lVelocity (I := I) (fun u => beta i u r) 0)) = ∫ _r in (a i)..(b i), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      simp only [lRegularizedEulerPair, (hgeoBeta i r hr).2.2.2, sub_self, map_zero]
    rw [heq, intervalIntegral.integral_zero]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    lRegularizedAction_first_variation (S i) (hS i) T (beta i) (hbeta i)
      (a i) (b i) (fun r hr => (hgeoBeta i r hr).1))
  have haction : (fun u : ℝ => finiteJointAction S T f a b (u • ξ, b (Fin.last n))) =
      (fun u => ∑ i : Fin (n + 1), lRegularizedAction (S i) T (beta i u) (a i) (b i)) := by
    funext u
    rw [Fin.sum_univ_castSucc]
    rfl
  have hresult : HasDerivAt
      (fun u : ℝ => finiteJointAction S T f a b (u • ξ, b (Fin.last n)))
      (pair (Fin.last n) (b (Fin.last n))) 0 := by
    rw [haction]
    apply hsum.congr_deriv
    simp_rw [hEuler, sub_zero]
    exact hboundary
  have h := hresult
  simp only [pair, beta] at h
  rw [zero_smul] at h
  exact h

/-- Joint first derivative of the same finite action. The clock derivative is
its actual terminal Lagrangian, and the parameter derivative is its actual
terminal momentum. -/
theorem hasFDerivAt_finiteJointAction
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
    (K : Fin (n + 1) → Set ℝ) (hK : ∀ i, IsOpen (K i))
    (hKconn : ∀ i, IsPreconnected (K i))
    (ha : ∀ i, a i ∈ K i) (hb : ∀ i, b i ∈ K i)
    (hreg : ∀ i r, r ∈ K i → T - r ^ 2 ∈ (D i).regular) :
    HasFDerivAt (finiteJointAction S T f a b)
      (((((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2)).inner
        (f (Fin.last n) (0, b (Fin.last n)))
        (lVelocity (I := I) (fun r => f (Fin.last n) (0, r)) (b (Fin.last n)))).comp
        (mfderiv 𝓘(ℝ, P) I (fun z => f (Fin.last n) (z, b (Fin.last n))) 0)).comp
          (ContinuousLinearMap.fst ℝ P ℝ) +
        (lRegularizedLagrangian (S (Fin.last n)) T
          (fun r => f (Fin.last n) (0, r)) (b (Fin.last n))) •
          ContinuousLinearMap.snd ℝ P ℝ) (0, b (Fin.last n)) := by
  let last := Fin.last n
  let Act := finiteJointAction S T f a b
  let v := b last
  let endMap : P → M last := fun z => f last (z, v)
  let g := (S last).base.metric (T - v ^ 2)
  let velocity := lVelocity (I := I) (fun r => f last (0, r)) v
  let Lsp : P →L[ℝ] ℝ := (g.inner (f last (0, v)) velocity).comp
    (mfderiv 𝓘(ℝ, P) I endMap 0)
  let lag : ℝ → ℝ := lRegularizedLagrangian (S last) T (fun r => f last (0, r))
  have hAct2 : ContDiffOn ℝ 2 Act (Set.univ ×ˢ K last) :=
    contDiffOn_finiteJointAction S hS T f a b isOpen_univ K hK hKconn ha hb
      (fun i => (hf i).contMDiffOn) hreg
  have hbase : HasFDerivAt Act (fderiv ℝ Act (0, v)) (0, v) :=
    ((hAct2.contDiffAt ((isOpen_univ.prod (hK last)).mem_nhds
      ⟨mem_univ 0, hb last⟩)).differentiableAt (by norm_num)).hasFDerivAt
  have hendMD : MDifferentiableAt 𝓘(ℝ, P) I endMap 0 :=
    (((hf last).comp (contMDiff_id.prodMk contMDiff_const)).contMDiffAt).mdifferentiableAt
      (by norm_num)
  have hspace (ξ : P) : fderiv ℝ Act (0, v) (ξ, 0) = Lsp ξ := by
    have hline : HasDerivAt (fun u : ℝ => u • ξ) ξ 0 := by
      simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const ξ
    have hincl : HasDerivAt (fun u : ℝ => (u • ξ, v)) (ξ, 0) 0 :=
      hline.prodMk (hasDerivAt_const 0 v)
    have hlineAct : HasDerivAt (fun u : ℝ => Act (u • ξ, v))
        (fderiv ℝ Act (0, v) (ξ, 0)) 0 := by
      exact hbase.comp_hasDerivAt_of_eq 0 hincl (by simp only [zero_smul])
    have hvelocityLine : lVelocity (I := I) (fun u => f last (u • ξ, v)) 0 =
        mfderiv 𝓘(ℝ, P) I endMap 0 ξ := by
      unfold lVelocity
      have hendAt : HasMFDerivAt 𝓘(ℝ, P) I endMap ((0 : ℝ) • ξ)
          (mfderiv 𝓘(ℝ, P) I endMap 0) := by
        rw [zero_smul]
        exact hendMD.hasMFDerivAt
      have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f last (u • ξ, v)) 0 _ :=
        HasMFDerivAt.comp (g := endMap) (f := fun u : ℝ => u • ξ) 0 hendAt
          hline.hasFDerivAt.hasMFDerivAt
      rw [hcomp.mfderiv]
      change mfderiv 𝓘(ℝ, P) I endMap 0
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ξ) 1) = _
      simp
    have hboundary := hasDerivAt_finiteJointAction_line
      S hS T f hf a b hgeo Phi hmetric hjoin hvelocity p hfirst ξ
    have heq := hlineAct.unique hboundary
    rw [hvelocityLine] at heq
    exact heq.trans (g.symm (f last (0, v)) _ _)
  have hlagK : ContinuousOn lag (K last) := by
    have hlag := continuousOn_lRegularizedLagrangian_family_of_contMDiffOn_one
      (S last) (hS last) T isOpen_univ (hK last)
      (((hf last).of_le (by norm_num)).contMDiffOn) (Subset.refl (K last))
      (fun r hr => (D last).regular_subset (hreg last r hr))
    have hcomp := hlag.comp (f := fun r : ℝ => ((0 : P), r))
      (continuousOn_const.prodMk continuousOn_id) (fun r hr => ⟨mem_univ (0 : P), hr⟩)
    exact hcomp
  have hlagI : ContinuousOn lag (uIcc (a last) v) :=
    hlagK.mono ((hKconn last).ordConnected.uIcc_subset (ha last) (hb last))
  have hupper : HasDerivAt (fun w : ℝ => ∫ r in (a last)..w, lag r) (lag v) v :=
    intervalIntegral.integral_hasDerivAt_right hlagI.intervalIntegrable
      (hlagK.stronglyMeasurableAtFilter (hK last) v (hb last))
      (hlagK.continuousAt ((hK last).mem_nhds (hb last)))
  have htime : HasDerivAt (fun w : ℝ => Act (0, w)) (lag v) v := by
    simpa only [Act, finiteJointAction, lRegularizedAction, lag, last] using
      hupper.const_add (∑ i : Fin n, lRegularizedAction (S i.castSucc) T
        (fun r => f i.castSucc (0, r)) (a i.castSucc) (b i.castSucc))
  have htins : HasFDerivAt (fun w : ℝ => ((0 : P), w))
      (ContinuousLinearMap.inr ℝ P ℝ) v := hasFDerivAt_prodMk_right 0 v
  have htimeEq := (hbase.comp v htins).hasDerivAt.unique htime
  have htimeVal : fderiv ℝ Act (0, v) (0, (1 : ℝ)) = lag v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using htimeEq
  have hfd : fderiv ℝ Act (0, v) =
      Lsp.comp (ContinuousLinearMap.fst ℝ P ℝ) + lag v • ContinuousLinearMap.snd ℝ P ℝ := by
    refine ContinuousLinearMap.ext fun z => ?_
    calc
      fderiv ℝ Act (0, v) z =
          fderiv ℝ Act (0, v) (z.1, 0) + fderiv ℝ Act (0, v) (0, z.2) := by
        rw [← map_add]
        congr 1
        ext <;> simp
      _ = Lsp z.1 + z.2 * lag v := by
        rw [show ((0 : P), z.2) = z.2 • ((0 : P), (1 : ℝ)) by ext <;> simp,
          map_smul, htimeVal, hspace]
        simp only [smul_eq_mul]
      _ = (Lsp.comp (ContinuousLinearMap.fst ℝ P ℝ) +
          lag v • ContinuousLinearMap.snd ℝ P ℝ) z := by
        change Lsp z.1 + z.2 * lag v = Lsp z.1 + lag v * z.2
        ring
  rw [hfd] at hbase
  exact hbase

end DifferentialGeometry.PDE.RicciFlow.Perelman
