import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PullbackField
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1ApproxIso
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1MetricIntrinsic

set_option autoImplicit false

/-!
# Step-B1 metric carriers

This file performs the final generic assembly from localized intrinsic
metric-error estimates to the existing `PreApproxIsoDataOn` interface.  The
forward and reverse metrics are genuine smooth pullback-field extensions on a
compact collar.  The reverse map is the exact `Function.invFunOn` of the
forward map; an independently constructed reverse stage map is not used.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Filter Bundle Manifold
open scoped ContDiff Manifold

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- Assemble the two localized pre-approximate-isometry carriers from a
compact source collar, an injective local diffeomorphism, and intrinsic
metric-error bounds for the forward map and its exact local inverse. -/
theorem preapprox_pair
    {M N : Type u}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
    [IsManifold I ∞ N] [SigmaCompactSpace N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [Nonempty M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    {K K' U : Set M} {eps : Real} {p : Nat} (F : M → N)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hU : IsOpen U) (hK'c : IsCompact K')
    (hKK' : K ⊆ K') (hK'U : K' ⊆ U)
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U)
    (hfwd : ∀ (G : SmoothRiemannianMetric I M),
      (∀ x ∈ K', ∀ v w : TangentSpace I x,
        G.inner x v w = h.inner (F x)
          (mfderiv I I F x v) (mfderiv I I F x w)) →
      ∀ a ≤ p, ∀ x ∈ K,
        metricDerivNorm (I := I) a G g g x ≤ eps)
    (hrev : ∀ (G : SmoothRiemannianMetric I N),
      (∀ y ∈ F '' K', ∀ v w : TangentSpace I y,
        G.inner y v w = g.inner (Function.invFunOn F U y)
          (mfderiv I I (Function.invFunOn F U) y v)
          (mfderiv I I (Function.invFunOn F U) y w)) →
      ∀ a ≤ p, ∀ y ∈ F '' K,
        metricDerivNorm (I := I) a G h h y ≤ eps) :
    Nonempty (PreApproxIsoDataOn (I := I) K eps p F g h) ∧
      Nonempty (PreApproxIsoDataOn (I := I) (F '' K) eps p
        (Function.invFunOn F U) h g) := by
  classical
  obtain ⟨Φ, hsrc, htgt, hEq⟩ :=
    Geometry.Riemannian.exists_diffeo_of_injOn hloc hU hinj
  have hK'src : K' ⊆ Φ.source := by
    rw [hsrc]
    exact hK'U
  have hKsrc : K ⊆ Φ.source := hKK'.trans hK'src
  obtain ⟨Pf, Gf, hPf, hGfΦ, hTfΦ⟩ :=
    exists_pullbackField (I := I) Φ hK'c hK'src h g
  have hevF : ∀ x ∈ K', (Φ : M → N) =ᶠ[nhds x] F := by
    intro x hx
    exact Filter.eventuallyEq_of_mem (hU.mem_nhds (hK'U hx)) hEq
  have hGfF : ∀ x ∈ K', ∀ v w : TangentSpace I x,
      Gf.inner x v w = h.inner (F x)
        (mfderiv I I F x v) (mfderiv I I F x w) := by
    intro x hx v w
    have hout := hGfΦ x hx v w
    rw [(hevF x hx).self_of_nhds, (hevF x hx).mfderiv_eq] at hout
    exact hout
  have hTf : ∀ x ∈ K, ∀ v : Fin 2 → TangentSpace I x,
      Tensor0SBundle.metricTensorField (I := I) Gf x v =
        h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x (v 0))
          (mfderiv I I (Φ : M → N) x (v 1)) := by
    intro x hx v
    rw [← hPf]
    exact hTfΦ x (hKK' hx) v
  have hfwdΦ : PreApproxIsoDataOn (I := I) K eps p
      (Φ : M → N) g h :=
    PreApproxIsoDataOn.of_metric (I := I) Gf g h heps heps1
      (Φ.contMDiffOn_toFun.mono hKsrc) hTf (hfwd Gf hGfF)
  have hfwdF : PreApproxIsoDataOn (I := I) K eps p F g h :=
    hfwdΦ.congr (fun x hx ↦ (hevF x (hKK' hx)).symm)

  have himage : (Φ : M → N) '' K' = F '' K' :=
    Set.EqOn.image_eq (fun x hx ↦ hEq (hK'U hx))
  have hFK'c : IsCompact (F '' K') := by
    rw [← himage]
    exact hK'c.image_of_continuousOn
      (Φ.contMDiffOn_toFun.continuousOn.mono hK'src)
  have hFK'tgt : F '' K' ⊆ Φ.target := by
    rw [htgt]
    exact Set.image_mono hK'U
  have hFK'src : F '' K' ⊆ Φ.symm.source := by
    simpa only using hFK'tgt
  obtain ⟨Pr, Gr, hPr, hGrΦ, hTrΦ⟩ :=
    exists_pullbackField (I := I) Φ.symm hFK'c hFK'src g h
  have hsymmEq : Set.EqOn (Φ.symm : N → M)
      (Function.invFunOn F U) Φ.target := by
    intro z hz
    rw [htgt] at hz
    obtain ⟨x, hxU, rfl⟩ := hz
    have hΦx : (Φ : M → N) x = F x := hEq hxU
    have hleft : (Φ.symm : N → M) (F x) = x := by
      rw [← hΦx]
      exact Φ.toPartialEquiv.left_inv (by rw [hsrc]; exact hxU)
    have hinv : Function.invFunOn F U (F x) = x :=
      hinj.leftInvOn_invFunOn hxU
    rw [hleft, hinv]
  have hevR : ∀ y ∈ F '' K', (Φ.symm : N → M) =ᶠ[nhds y]
      Function.invFunOn F U := by
    intro y hy
    exact Filter.eventuallyEq_of_mem
      (Φ.open_target.mem_nhds (hFK'tgt hy)) hsymmEq
  have hGrInv : ∀ y ∈ F '' K', ∀ v w : TangentSpace I y,
      Gr.inner y v w = g.inner (Function.invFunOn F U y)
        (mfderiv I I (Function.invFunOn F U) y v)
        (mfderiv I I (Function.invFunOn F U) y w) := by
    intro y hy v w
    have hout := hGrΦ y hy v w
    rw [(hevR y hy).self_of_nhds, (hevR y hy).mfderiv_eq] at hout
    exact hout
  have hFKtgt : F '' K ⊆ Φ.target :=
    (Set.image_mono hKK').trans hFK'tgt
  have hFKsrc : F '' K ⊆ Φ.symm.source := by
    simpa only using hFKtgt
  have hTr : ∀ y ∈ F '' K, ∀ v : Fin 2 → TangentSpace I y,
      Tensor0SBundle.metricTensorField (I := I) Gr y v =
        g.inner ((Φ.symm : N → M) y)
          (mfderiv I I (Φ.symm : N → M) y (v 0))
          (mfderiv I I (Φ.symm : N → M) y (v 1)) := by
    intro y hy v
    rw [← hPr]
    exact hTrΦ y (Set.image_mono hKK' hy) v
  have hrevΦ : PreApproxIsoDataOn (I := I) (F '' K) eps p
      (Φ.symm : N → M) h g :=
    PreApproxIsoDataOn.of_metric (I := I) Gr h g heps heps1
      (Φ.symm.contMDiffOn_toFun.mono hFKsrc) hTr (hrev Gr hGrInv)
  have hrevF : PreApproxIsoDataOn (I := I) (F '' K) eps p
      (Function.invFunOn F U) h g :=
    hrevΦ.congr (fun y hy ↦
      (hevR y (Set.image_mono hKK' hy)).symm)
  exact ⟨⟨hfwdF⟩, ⟨hrevF⟩⟩

variable [NeZero (Module.finrank Real E)]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- The stage-jet package produces the two native Step-B1 metric carriers on
one rectangular pair-index tail.  All auxiliary partial diffeomorphisms and
smooth pullback-field extensions remain internal to the proof. -/
theorem HasStageJetData.preapprox_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {s : Real} (hs : 0 ≤ s)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack s → Set E)
    (aInf : (alpha : LiveSlot L inp.pack s) →
      Fin (inp.pack.A s) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack s) →
      InterSlot L inp.pack s alpha → E → E)
    (gInf : LiveSlot L inp.pack s →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hs phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    {R S T Vrad : Real} (hRS : R < S) (hST : S < T)
    (hroom : T + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < Vrad)
    (hVr : Vrad < s)
    (p : Nat) (eps : Real) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
      let F := stageComparisonMap inp P Lphi s hs hconn k l
      Nonempty (PreApproxIsoDataOn (I := I)
          (Metric.closedBall Yk.basepoint R) eps p F Yk.metric Yl.metric) ∧
        Nonempty (PreApproxIsoDataOn (I := I)
          (F '' Metric.closedBall Yk.basepoint R) eps p
          (Function.invFunOn F (Metric.ball Yk.basepoint T))
          Yl.metric Yk.metric) := by
  classical
  have hgap : 0 ≤
      (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 :=
    mul_nonneg (by positivity) (inp.decay.lambda_pos inp.hD 0).le
  have hTr : T < s := by linarith
  have hSr : S < s := hST.trans hTr
  obtain ⟨Nfwd, hfwd⟩ :=
    hstage.fwd_norm_tail inp P L hs phi hphi hconn U C0 C1 aInf
      Jinf Jbarinf gInf hRS hSr p eps heps
  obtain ⟨Nrev, hrev⟩ :=
    hstage.inv_norm_tail inp P L hs phi hphi hcomplete hconn U C0 C1
      aInf Jinf Jbarinf gInf hRS hST hroom hVr p eps heps
  obtain ⟨Nloc, hloc⟩ :=
    hstage.hloc_tail inp P L hs phi hphi hconn U C0 C1 aInf
      Jinf Jbarinf gInf T hTr
  obtain ⟨Ninj, hinj⟩ :=
    hstage.inj_tail inp P L hs phi hphi hcomplete hconn U C0 C1 aInf
      Jinf Jbarinf gInf T Vrad hroom hVr
  let N := max Nfwd (max Nrev (max Nloc Ninj))
  refine ⟨N, ?_⟩
  intro k hk l hl
  have hkFwd : Nfwd ≤ k := (Nat.le_max_left _ _).trans hk
  have hlFwd : Nfwd ≤ l := (Nat.le_max_left _ _).trans hl
  have hkRev : Nrev ≤ k :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right Nfwd _).trans hk)
  have hlRev : Nrev ≤ l :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right Nfwd _).trans hl)
  have hkLoc : Nloc ≤ k :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right Nrev _).trans ((Nat.le_max_right Nfwd _).trans hk))
  have hlLoc : Nloc ≤ l :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right Nrev _).trans ((Nat.le_max_right Nfwd _).trans hl))
  have hkInj : Ninj ≤ k :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right Nrev _).trans ((Nat.le_max_right Nfwd _).trans hk))
  have hlInj : Ninj ≤ l :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right Nrev _).trans ((Nat.le_max_right Nfwd _).trans hl))
  dsimp only
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
  let F := stageComparisonMap inp P Lphi s hs hconn k l
  let K : Set Yk.M := Metric.closedBall Yk.basepoint R
  let K' : Set Yk.M := Metric.closedBall Yk.basepoint S
  let W : Set Yk.M := Metric.ball Yk.basepoint T
  have hlocKL := hloc k hkLoc l hlLoc
  have hinjKL := hinj k hkInj l hlInj
  have hfwdKL := hfwd k hkFwd l hlFwd
  have hrevKL := hrev k hkRev l hlRev
  have hlocW : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F W := by
    intro x
    have hxhat : (x : Yk.M) ∈
        Lphi.hatSourceBall inp.decay P T k := by
      simpa only [W, NetLimitData.hatSourceBall, Yk, Lphi] using
        Metric.ball_subset_closedBall x.2
    simpa only [F, Yk, Yl, Lphi] using hlocKL ⟨x, hxhat⟩
  have hinjW : Set.InjOn F W := by
    intro x hx y hy hxy
    apply hinjKL
    · simpa only [W, NetLimitData.hatSourceBall, Yk, Lphi] using
        Metric.ball_subset_closedBall hx
    · simpa only [W, NetLimitData.hatSourceBall, Yk, Lphi] using
        Metric.ball_subset_closedBall hy
    · exact hxy
  have hWopen : IsOpen W := by
    have hb :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          W := by
      simpa only [W] using (Metric.isOpen_ball :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.ball Yk.basepoint T))
    rw [ProperMetricOn.top_eq Yk (P (Lphi.φ k))] at hb
    exact hb
  have hK'c : IsCompact K' := by
    simpa only [K', NetLimitData.hatSourceBall, Yk, Lphi] using
      Lphi.hatSourceCompact inp.decay P S k
  have hKK' : K ⊆ K' := Metric.closedBall_subset_closedBall hRS.le
  have hK'W : K' ⊆ W := Metric.closedBall_subset_ball hST
  apply preapprox_pair Yk.metric Yl.metric F heps heps1 hWopen hK'c
    hKK' hK'W hlocW hinjW
  · intro G hG a ha x hx
    apply hfwdKL G
    · simpa only [K', NetLimitData.hatSourceBall, F, Yk, Yl, Lphi] using hG
    · exact ha
    · simpa only [K, NetLimitData.hatSourceBall, F, Yk, Yl, Lphi] using hx
  · intro G hG a ha y hy
    apply hrevKL G
    · simpa only [K', W, NetLimitData.hatSourceBall, F, Yk, Yl, Lphi] using hG
    · exact ha
    · simpa only [K, W, NetLimitData.hatSourceBall, F, Yk, Yl, Lphi] using hy

end HCGCompactness
end DifferentialGeometry
