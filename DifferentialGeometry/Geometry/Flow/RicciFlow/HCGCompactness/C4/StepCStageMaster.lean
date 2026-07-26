import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageDiagonal
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageInjectivity

set_option autoImplicit false

/-!
# Master-subsequence stage geometry

The integer-radius diagonal records each fixed-radius stage package on a tail
of one master selector.  This file transports the already proved local
diffeomorphism, injectivity, and pointedness tails to the manifolds indexed
directly by that master selector.  Only point/manifold indices are transported;
the radius-local `LiveSlot` and `InterSlot` types are never identified across
subsequences.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Filter Topology Bundle Manifold
open scoped ContDiff Manifold Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- Transport a finite-stage comparison map along equalities of its two
ambient sequence indices. -/
noncomputable def stageMapCast
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l K L' : Nat) (hk : L.φ k = K) (hl : L.φ l = L') :
    (X.obj K).M → (X.obj L').M := by
  subst K
  subst L'
  exact stageComparisonMap inp P L s hs hconn k l

private theorem cast_geom
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l K L' : Nat) (hk : L.φ k = K) (hl : L.φ l = L') (R : Real)
    (hgeom :
      let Yk := X.obj (L.φ k)
      let Yl := X.obj (L.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      letI : MetricSpace Yk.M := (P (L.φ k)).ms
      letI : MetricSpace Yl.M := (P (L.φ l)).ms
      IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞)
          (stageComparisonMap inp P L s hs hconn k l)
          (Metric.closedBall Yk.basepoint R) ∧
        Set.InjOn (stageComparisonMap inp P L s hs hconn k l)
          (Metric.closedBall Yk.basepoint R) ∧
        stageComparisonMap inp P L s hs hconn k l Yk.basepoint =
          Yl.basepoint) :
    let YK := X.obj K
    let YL := X.obj L'
    letI : TopologicalSpace YK.M := YK.topology
    letI : ChartedSpace H YK.M := YK.charted
    letI : IsManifold I ∞ YK.M := YK.smooth
    letI : T2Space YK.M := YK.t2
    letI : T2Space (TangentBundle I YK.M) := YK.t2TangentBundle
    letI : TopologicalSpace YL.M := YL.topology
    letI : ChartedSpace H YL.M := YL.charted
    letI : IsManifold I ∞ YL.M := YL.smooth
    letI : T2Space YL.M := YL.t2
    letI : T2Space (TangentBundle I YL.M) := YL.t2TangentBundle
    letI : MetricSpace YK.M := (P K).ms
    letI : MetricSpace YL.M := (P L').ms
    IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞)
        (stageMapCast inp P L s hs hconn k l K L' hk hl)
        (Metric.closedBall YK.basepoint R) ∧
      Set.InjOn (stageMapCast inp P L s hs hconn k l K L' hk hl)
        (Metric.closedBall YK.basepoint R) ∧
      stageMapCast inp P L s hs hconn k l K L' hk hl YK.basepoint =
        YL.basepoint := by
  subst K
  subst L'
  simpa only [stageMapCast] using hgeom

/-- A fixed integer-radius tail supplies the first three Step-B1 comparison
fields directly on the master sequence: local diffeomorphism on the retained
open ball, global injectivity there, and exact basepoint preservation.  The
witnessed radius-tail selector and index equality are retained so downstream
metric estimates can use the very same transported map. -/
theorem HasRadiusTail.geom_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn)
    (psi : Nat → Nat) (q : Nat)
    (htail : HasRadiusTail inp P L0 hconn hseed psi q)
    (R0 R1 : Real)
    (hroom : R0 + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < R1)
    (hR1q : R1 < (q : Real)) :
    let S := stageStates inp P L0 hconn hseed q
    let d := radiusPayload inp P L0 hconn hseed q
    ∃ (rho : Nat → Nat) (hrho : StrictMono rho)
        (hindex : ∀ n,
          (((L0.subseq S.sigma_strict).subseq
            (d.phi_strict.comp hrho)).φ n) = psi (q + n)),
      HasStageJetData inp P (L0.subseq S.sigma_strict)
          (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
          hconn d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf ∧
        ∃ (N : Nat) (hNq : q ≤ N), ∀ (k : Nat) (hk : N ≤ k)
          (l : Nat) (hl : N ≤ l),
        let Xpsi := X.subseq psi
        let Ppsi : ∀ n : Nat, ProperMetricOn (I := I) (Xpsi.obj n) :=
          fun n => P (psi n)
        let Yk := Xpsi.obj k
        let Yl := Xpsi.obj l
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : T2Space Yl.M := Yl.t2
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        letI : MetricSpace Yk.M := (Ppsi k).ms
        letI : MetricSpace Yl.M := (Ppsi l).ms
        let Lq := (L0.subseq S.sigma_strict).subseq
          (d.phi_strict.comp hrho)
        let hkq : q ≤ k := hNq.trans hk
        let hlq : q ≤ l := hNq.trans hl
        let hki : Lq.φ (k - q) = psi k :=
          (hindex (k - q)).trans
            (congrArg psi (Nat.add_sub_of_le hkq))
        let hli : Lq.φ (l - q) = psi l :=
          (hindex (l - q)).trans
            (congrArg psi (Nat.add_sub_of_le hlq))
        let F : Yk.M → Yl.M :=
          stageMapCast inp P Lq q (Nat.cast_nonneg q) hconn
            (k - q) (l - q) (psi k) (psi l) hki hli
        IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F
            (Metric.closedBall Yk.basepoint R0) ∧
          Set.InjOn F (Metric.closedBall Yk.basepoint R0) ∧
          F Yk.basepoint = Yl.basepoint := by
  classical
  dsimp only
  obtain ⟨rho, hrho, hindex, hstage⟩ := htail
  let S := stageStates inp P L0 hconn hseed q
  let d := radiusPayload inp P L0 hconn hseed q
  let Lbase := L0.subseq S.sigma_strict
  let Lq := Lbase.subseq (d.phi_strict.comp hrho)
  have hR0q : R0 < (q : Real) := by
    have hlam : 0 ≤ inp.decay.lambda inp.D 0 :=
      (inp.decay.lambda_pos inp.hD 0).le
    have hcoef : 0 ≤
        (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 := by
      positivity
    linarith
  obtain ⟨Nloc, hloc⟩ := hstage.hloc_tail inp P Lbase
    (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      hconn d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf R0 hR0q
  obtain ⟨Ninj, hinj⟩ := hstage.inj_tail inp P Lbase
    (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      hcomplete hconn d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf
      R0 R1 hroom hR1q
  rcases hstage with ⟨_hdata, _hmetric, _hjets, hbase⟩
  dsimp only [HasStageBaseTail] at hbase
  obtain ⟨Nbase, hbase⟩ := eventually_atTop.mp hbase
  let Nt := max Nloc (max Ninj Nbase)
  refine ⟨rho, hrho, hindex, ?_, q + Nt, Nat.le_add_right q Nt, ?_⟩
  · exact ⟨_hdata, _hmetric, _hjets, by
      dsimp only [HasStageBaseTail]
      exact eventually_atTop.mpr ⟨Nbase, hbase⟩⟩
  intro k hk l hl
  have hkq : q ≤ k := (Nat.le_add_right q Nt).trans hk
  have hlq : q ≤ l := (Nat.le_add_right q Nt).trans hl
  have hkNt : Nt ≤ k - q := by omega
  have hlNt : Nt ≤ l - q := by omega
  have hkLoc : Nloc ≤ k - q := (le_max_left _ _).trans hkNt
  have hlLoc : Nloc ≤ l - q := (le_max_left _ _).trans hlNt
  have hkInj : Ninj ≤ k - q :=
    (le_max_left _ _).trans ((le_max_right Nloc (max Ninj Nbase)).trans hkNt)
  have hlInj : Ninj ≤ l - q :=
    (le_max_left _ _).trans ((le_max_right Nloc (max Ninj Nbase)).trans hlNt)
  have hkBase : Nbase ≤ k - q :=
    (le_max_right _ _).trans ((le_max_right Nloc (max Ninj Nbase)).trans hkNt)
  have hki : Lq.φ (k - q) = psi k := by
    exact (hindex (k - q)).trans (congrArg psi (Nat.add_sub_of_le hkq))
  have hli : Lq.φ (l - q) = psi l := by
    exact (hindex (l - q)).trans (congrArg psi (Nat.add_sub_of_le hlq))
  have hloc0 := hloc (k - q) hkLoc (l - q) hlLoc
  have hinj0 := hinj (k - q) hkInj (l - q) hlInj
  have hbase0 := hbase (k - q) hkBase (l - q)
  apply cast_geom inp P Lq q (Nat.cast_nonneg q) hconn
    (k - q) (l - q) (psi k) (psi l) hki hli R0
  dsimp only
  exact ⟨by
    simpa only [Lq, Lbase, NetLimitData.hatSourceBall] using hloc0,
    by simpa only [Lq, Lbase, NetLimitData.hatSourceBall] using hinj0,
    by simpa only [Lq, Lbase] using hbase0⟩

end HCGCompactness
end DifferentialGeometry
