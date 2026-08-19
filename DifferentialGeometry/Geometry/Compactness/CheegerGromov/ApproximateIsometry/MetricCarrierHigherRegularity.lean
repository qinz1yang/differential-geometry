import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricCarrier



import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricIntrinsicHigherRegularity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.InjectivityHigherRegularity

set_option autoImplicit false

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
variable [NeZero (Module.finrank Real E)]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

theorem BoundedGeometryNormalData.preapprox_tail
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {s : Real} (hs : 0 ≤ s)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (Vmetric U C0 C1 : LiveSlot L inp.pack s → Set E)
    (aInf : (alpha : LiveSlot L inp.pack s) →
      Fin (inp.pack.A s) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack s) →
      InterSlot L inp.pack s alpha → E → E)
    (gInf : LiveSlot L inp.pack s →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetDataOn (I := I) inp P L hs phi hphi hconn
      d.chart Vmetric U C0 C1 aInf Jinf Jbarinf gInf)
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
        (chart := d.chart)
      Nonempty (MapMetricApproximationOn (I := I)
          (Metric.closedBall Yk.basepoint R) eps p F Yk.metric Yl.metric) ∧
        Nonempty (MapMetricApproximationOn (I := I)
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
    d.fwd_norm_tail inp P L hs phi hphi hconn Vmetric U C0 C1 aInf
      Jinf Jbarinf gInf hstage hRS hSr p eps heps
  obtain ⟨Nrev, hrev⟩ :=
    d.inv_norm_tail inp P L hs phi hphi hcomplete hconn Vmetric U C0 C1
      aInf Jinf Jbarinf gInf hstage hRS hST hroom hVr p eps heps
  obtain ⟨Nloc, hloc⟩ :=
    hstage.hloc_tail inp P L hs phi hphi hconn d.chart Vmetric
      U C0 C1 aInf Jinf Jbarinf gInf T hTr
  obtain ⟨Ninj, hinj⟩ :=
    d.inj_tail inp P L hs phi hphi hcomplete hconn Vmetric
      U C0 C1 aInf Jinf Jbarinf gInf hstage T Vrad hroom hVr
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
    (chart := d.chart)
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
