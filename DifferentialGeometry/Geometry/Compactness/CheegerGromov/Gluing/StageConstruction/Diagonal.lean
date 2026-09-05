import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.StageConstruction.Seed


open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

private structure NestedSubseq where
  sigma : Nat → Nat → Nat
  tau : Nat → Nat → Nat
  sigma_strict : ∀ m, StrictMono (sigma m)
  tau_strict : ∀ m, StrictMono (tau m)
  sigma_zero : sigma 0 = id
  sigma_succ : ∀ m, sigma (m + 1) = sigma m ∘ tau m

namespace NestedSubseq

private def diag (T : NestedSubseq) (m : Nat) : Nat := T.sigma (m + 1) m

private def tailComp (T : NestedSubseq) (q : Nat) : Nat → (Nat → Nat)
  | 0 => id
  | n + 1 => T.tailComp q n ∘ T.tau (q + 1 + n)

private def tailFactor (T : NestedSubseq) (q n : Nat) : Nat :=
  T.tailComp q n (q + n)

private theorem tailComp_strict (T : NestedSubseq) (q : Nat) :
    ∀ n, StrictMono (T.tailComp q n) := by
  intro n
  induction n with
  | zero => exact strictMono_id
  | succ n ih =>
      exact ih.comp (T.tau_strict (q + 1 + n))

private theorem sigma_factor (T : NestedSubseq) (q n : Nat) :
    T.sigma (q + n + 1) = T.sigma (q + 1) ∘ T.tailComp q n := by
  induction n with
  | zero =>
      simp only [Nat.add_zero, tailComp, Function.comp_id]
  | succ n ih =>
      rw [show q + (n + 1) + 1 = (q + n + 1) + 1 by omega]
      rw [T.sigma_succ (q + n + 1), ih]
      ext x
      simp only [tailComp, Function.comp_apply]
      rw [show q + n + 1 = q + 1 + n by omega]

private theorem tailFactor_strict (T : NestedSubseq) (q : Nat) :
    StrictMono (T.tailFactor q) := by
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp only [tailFactor]
  rw [tailComp]
  simp only [Function.comp_apply]
  apply T.tailComp_strict q n
  have hlt : q + n < q + (n + 1) := by omega
  have hle := (T.tau_strict (q + 1 + n)).id_le (q + (n + 1))
  exact hlt.trans_le hle

private theorem diag_strict (T : NestedSubseq) : StrictMono T.diag := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [diag, diag, T.sigma_succ (n + 1)]
  simp only [Function.comp_apply]
  apply T.sigma_strict (n + 1)
  have hle := (T.tau_strict (n + 1)).id_le (n + 1)
  exact (Nat.lt_succ_self n).trans_le hle

private theorem diag_step_factor (T : NestedSubseq) (q n : Nat) :
    T.diag (q + n) =
      T.sigma q (T.tau q (T.tailFactor q n)) := by
  have hfactor := congrFun (T.sigma_factor q n) (q + n)
  rw [T.sigma_succ q] at hfactor
  simpa only [diag, tailFactor, Function.comp_apply] using hfactor

end NestedSubseq

structure StageConvergenceSelection
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r) where
  phi : Nat → Nat
  phi_strict : StrictMono phi
  U : LiveSlot L inp.pack r → Set E
  C0 : LiveSlot L inp.pack r → Set E
  C1 : LiveSlot L inp.pack r → Set E
  aInf : (alpha : LiveSlot L inp.pack r) →
    Fin (inp.pack.A r) → E → Real
  Jinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  Jbarinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  gInf : LiveSlot L inp.pack r →
    E → (E →L[Real] E →L[Real] Real)
  convergence : HasStageJetConvergence inp P L hr phi phi_strict U C0 C1
    aInf Jinf Jbarinf gInf

private theorem HasStageRefine.payload_nonempty
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    (h : HasStageRefine inp P L r hr) :
    Nonempty (StageConvergenceSelection inp P L r hr) := by
  rcases h with ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩
  exact ⟨⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩⟩

structure StageConvergenceSelectionOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (r : Real) (hr : 0 ≤ r) where
  phi : Nat → Nat
  phi_strict : StrictMono phi
  V : LiveSlot L inp.pack r → Set E
  U : LiveSlot L inp.pack r → Set E
  C0 : LiveSlot L inp.pack r → Set E
  C1 : LiveSlot L inp.pack r → Set E
  aInf : (alpha : LiveSlot L inp.pack r) →
    Fin (inp.pack.A r) → E → Real
  Jinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  Jbarinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  gInf : LiveSlot L inp.pack r →
    E → (E →L[Real] E →L[Real] Real)
  convergence : HasStageJetConvergenceOn inp P L hr phi phi_strict chart
    V U C0 C1 aInf Jinf Jbarinf gInf

private theorem HasStageRefineOn.payload_nonempty
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (r : Real) (hr : 0 ≤ r)
    (h : HasStageRefineOn inp P L chart r hr) :
    Nonempty (StageConvergenceSelectionOn inp P L chart r hr) := by
  rcases h with
    ⟨phi, hphi, V, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩
  exact
    ⟨⟨phi, hphi, V, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩⟩

structure StageSubsequence where
  sigma : Nat → Nat
  sigma_strict : StrictMono sigma

private noncomputable def choosePayload
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0)
    (S : StageSubsequence) (m : Nat) :
    StageConvergenceSelection inp P (L0.subseq S.sigma_strict) (m : Real)
      (Nat.cast_nonneg m) :=
  Classical.choice <| HasStageRefine.payload_nonempty inp P
    (L0.subseq S.sigma_strict) (m : Real) (Nat.cast_nonneg m) <|
      hseed.refine inp P L0 (L0.subseq S.sigma_strict)
        (NetLimitData.stable_subseq inp.decay P L0 S.sigma_strict hseed.1)
        (m : Real) (Nat.cast_nonneg m)

private noncomputable def nextState
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0)
    (S : StageSubsequence) (m : Nat) : StageSubsequence :=
  let d := choosePayload inp P L0 hseed S m
  ⟨S.sigma ∘ d.phi, S.sigma_strict.comp d.phi_strict⟩

noncomputable def stageSubsequence
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0) : Nat → StageSubsequence
  | 0 => ⟨id, strictMono_id⟩
  | m + 1 => nextState inp P L0 hseed
      (stageSubsequence inp P L0 hseed m) m

noncomputable def radiusConvergenceSelection
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0) (m : Nat) :=
  choosePayload inp P L0 hseed
    (stageSubsequence inp P L0 hseed m) m

private noncomputable def stageNested
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0) : NestedSubseq where
  sigma m := (stageSubsequence inp P L0 hseed m).sigma
  tau m := (radiusConvergenceSelection inp P L0 hseed m).phi
  sigma_strict m := (stageSubsequence inp P L0 hseed m).sigma_strict
  tau_strict m := (radiusConvergenceSelection inp P L0 hseed m).phi_strict
  sigma_zero := rfl
  sigma_succ m := by
    rw [stageSubsequence]
    rfl

def HasRadiusTail
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0)
    (psi : Nat → Nat) (q : Nat) : Prop :=
  let S := stageSubsequence inp P L0 hseed q
  let d := radiusConvergenceSelection inp P L0 hseed q
  ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetConvergence inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf

theorem HasStageSeed.exists_radius_diag
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0) :
    ∃ (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat, HasRadiusTail inp P L0 hseed psi q := by
  let T := stageNested inp P L0 hseed
  let psi := L0.φ ∘ T.diag
  have hpsi : StrictMono psi := L0.φ_mono.comp T.diag_strict
  refine ⟨psi, hpsi, ?_⟩
  intro q
  let S := stageSubsequence inp P L0 hseed q
  let d := radiusConvergenceSelection inp P L0 hseed q
  let rho := T.tailFactor q
  have hrho : StrictMono rho := T.tailFactor_strict q
  change ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetConvergence inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf
  refine ⟨rho, hrho, ?_, ?_⟩
  · intro n
    have hfactor := congrArg L0.φ (T.diag_step_factor q n)
    simpa only [NetLimitData.subseq_phi, Function.comp_apply, psi, T, S, d,
      rho, stageNested] using hfactor.symm
  · exact d.convergence.subseq inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) d.phi_strict d.U d.C0 d.C1 d.aInf
      d.Jinf d.Jbarinf d.gInf hrho

private noncomputable def choosePayloadOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart)
    (S : StageSubsequence) (m : Nat) :
    StageConvergenceSelectionOn inp P (L0.subseq S.sigma_strict) chart
      (m : Real) (Nat.cast_nonneg m) :=
  Classical.choice <| HasStageRefineOn.payload_nonempty inp P
    (L0.subseq S.sigma_strict) chart (m : Real)
    (Nat.cast_nonneg m) <|
      hseed.refine inp P L0 chart (L0.subseq S.sigma_strict)
        (NetLimitData.stable_subseq inp.decay P L0 S.sigma_strict hseed.1)
        (m : Real) (Nat.cast_nonneg m)

private noncomputable def nextStateOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart)
    (S : StageSubsequence) (m : Nat) : StageSubsequence :=
  let d := choosePayloadOn inp P L0 chart hseed S m
  ⟨S.sigma ∘ d.phi, S.sigma_strict.comp d.phi_strict⟩

noncomputable def stageSubsequenceOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart) : Nat → StageSubsequence
  | 0 => ⟨id, strictMono_id⟩
  | m + 1 => nextStateOn inp P L0 chart hseed
      (stageSubsequenceOn inp P L0 chart hseed m) m

noncomputable def radiusConvergenceSelectionOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart) (m : Nat) :=
  choosePayloadOn inp P L0 chart hseed
    (stageSubsequenceOn inp P L0 chart hseed m) m

private noncomputable def stageNestedOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart) : NestedSubseq where
  sigma m := (stageSubsequenceOn inp P L0 chart hseed m).sigma
  tau m := (radiusConvergenceSelectionOn inp P L0 chart hseed m).phi
  sigma_strict m :=
    (stageSubsequenceOn inp P L0 chart hseed m).sigma_strict
  tau_strict m :=
    (radiusConvergenceSelectionOn inp P L0 chart hseed m).phi_strict
  sigma_zero := rfl
  sigma_succ m := by
    rw [stageSubsequenceOn]
    rfl

def HasRadiusTailOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart)
    (psi : Nat → Nat) (q : Nat) : Prop :=
  let S := stageSubsequenceOn inp P L0 chart hseed q
  let d := radiusConvergenceSelectionOn inp P L0 chart hseed q
  ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetConvergenceOn inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      chart d.V d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf

theorem HasStageSeedOn.exists_radius_diag
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart) :
    ∃ (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat, HasRadiusTailOn inp P L0 chart hseed psi q := by
  let T := stageNestedOn inp P L0 chart hseed
  let psi := L0.φ ∘ T.diag
  have hpsi : StrictMono psi := L0.φ_mono.comp T.diag_strict
  refine ⟨psi, hpsi, ?_⟩
  intro q
  let S := stageSubsequenceOn inp P L0 chart hseed q
  let d := radiusConvergenceSelectionOn inp P L0 chart hseed q
  let rho := T.tailFactor q
  have hrho : StrictMono rho := T.tailFactor_strict q
  change ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetConvergenceOn inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      chart d.V d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf
  refine ⟨rho, hrho, ?_, ?_⟩
  · intro n
    have hfactor := congrArg L0.φ (T.diag_step_factor q n)
    simpa only [NetLimitData.subseq_phi, Function.comp_apply, psi, T, S, d,
      rho, stageNestedOn] using hfactor.symm
  · exact d.convergence.subseq inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) d.phi_strict chart d.V d.U d.C0 d.C1
      d.aInf d.Jinf d.Jbarinf d.gInf hrho

theorem MetricCompactBase.exists_stage_diag
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    ∃ (inp : MetricCompactnessAssumptions (I := I) X)
        (L0 : NetLimitData inp.decay inp.D
          (properMetricsOfCompleteConnected (I := I) hcomplete hconn))
        (hseed : HasStageSeed inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn) L0)
        (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat, HasRadiusTail inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
        L0 hseed psi q := by
  obtain ⟨inp, L0, hseed⟩ := b.exists_stage_seed hcomplete hconn
  obtain ⟨psi, hpsi, htail⟩ :=
    hseed.exists_radius_diag inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
      L0
  exact ⟨inp, L0, hseed, psi, hpsi, htail⟩

end CheegerGromovCompactness
end DifferentialGeometry
