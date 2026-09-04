import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.RadialBump


import DifferentialGeometry.Analysis.Calculus.MapConvergence.TwoParameter
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterMap.Convergence.Support
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Topology
open scoped ContDiff

universe u uE uH

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace Real X]
  [NormedAddCommGroup Y] [NormedSpace Real Y]

def safeFill (cut : Y → Real) (safe : Y → Y)
    (F : X → Y) (R : Y → X) (x : X) : X :=
  x + cut (F x) • (R (safe (F x)) - x)

theorem safeFill_smooth
    {U : Set X} {V : Set Y} {cut : Y → Real} {safe : Y → Y}
    {F : X → Y} {R : Y → X}
    (hcut : ContDiff Real (∞ : WithTop ℕ∞) cut)
    (hsafe : ContDiff Real (∞ : WithTop ℕ∞) safe)
    (hF : ContDiffOn Real (∞ : WithTop ℕ∞) F U)
    (hR : ContDiffOn Real (∞ : WithTop ℕ∞) R V)
    (hsafeV : MapsTo (fun x => safe (F x)) U V) :
    ContDiffOn Real (∞ : WithTop ℕ∞) (safeFill cut safe F R) U := by
  have hsafeF : ContDiffOn Real (∞ : WithTop ℕ∞) (fun x => safe (F x)) U :=
    hsafe.contDiffOn.comp hF (fun _ _ => Set.mem_univ _)
  have hback : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun x => R (safe (F x))) U := hR.comp hsafeF hsafeV
  exact contDiffOn_id.add
    ((hcut.contDiffOn.comp hF (fun _ _ => Set.mem_univ _)).smul
      (hback.sub contDiffOn_id))

theorem safeFill_diag
    [ProperSpace X] [ProperSpace Y]
    {U : Set X} {V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    {F : Nat → X → Y} {Finf : X → Y}
    {R : Nat → Y → X} {Rinf : Y → X}
    (hF : MapCInfConvOnCompacts U F Finf)
    (hR : MapCInfConvOnCompacts V R Rinf)
    (hFc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (F k) U)
    (hFinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Finf U)
    (hRc : ∀ l, ContDiffOn Real (∞ : WithTop ℕ∞) (R l) V)
    (hRinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Rinf V)
    (cut : Y → Real) (safe : Y → Y)
    (hcut : ContDiff Real (∞ : WithTop ℕ∞) cut)
    (hsafe : ContDiff Real (∞ : WithTop ℕ∞) safe)
    (hsafeV : MapsTo safe Set.univ V)
    (hdiag : ∀ x ∈ U,
      x + cut (Finf x) • (Rinf (safe (Finf x)) - x) = x)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    MapCInfConvOnCompacts U
      (fun m => safeFill cut safe (F (kn m)) (R (ln m))) id := by
  let safeF : Nat → X → Y := fun m x => safe (F (kn m) x)
  let safeFinf : X → Y := fun x => safe (Finf x)
  have hFk : MapCInfConvOnCompacts U (fun m => F (kn m)) Finf :=
    hF.comp_tendsto_atTop hkn
  have hRl : MapCInfConvOnCompacts V (fun m => R (ln m)) Rinf :=
    hR.comp_tendsto_atTop hln
  have hsafeF : MapCInfConvOnCompacts U safeF safeFinf := by
    apply MapCInfConvOnCompacts.comp hU isOpen_univ hFk
      (mapCInfConv_const (U := (Set.univ : Set Y)) safe)
      (fun m => hFc (kn m)) hFinfc
      (fun _ => hsafe.contDiffOn) hsafe.contDiffOn
    · exact fun _ _ => Set.mem_univ _
    · exact fun _ _ _ => Set.mem_univ _
  have hsafeFc : ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞) (safeF m) U := by
    intro m
    exact hsafe.contDiffOn.comp (hFc (kn m)) (fun _ _ => Set.mem_univ _)
  have hsafeFinfc :
      ContDiffOn Real (∞ : WithTop ℕ∞) safeFinf U :=
    hsafe.contDiffOn.comp hFinfc (fun _ _ => Set.mem_univ _)
  have hsafeMap : MapsTo safeFinf U V := by
    intro x _hx
    exact hsafeV (Set.mem_univ (Finf x))
  have hsafeMapk : ∀ m, MapsTo (safeF m) U V := by
    intro m x _hx
    exact hsafeV (Set.mem_univ (F (kn m) x))
  let back : Nat → X → X := fun m x => R (ln m) (safeF m x)
  let backInf : X → X := fun x => Rinf (safeFinf x)
  have hback : MapCInfConvOnCompacts U back backInf := by
    exact MapCInfConvOnCompacts.comp hU hV hsafeF hRl hsafeFc
      hsafeFinfc (fun m => hRc (ln m)) hRinfc hsafeMap hsafeMapk
  have hbackc : ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞) (back m) U := by
    intro m
    exact (hRc (ln m)).comp (hsafeFc m) (hsafeMapk m)
  have hbackInfc :
      ContDiffOn Real (∞ : WithTop ℕ∞) backInf U :=
    hRinfc.comp hsafeFinfc hsafeMap
  let targets : Nat → X → Y × X := fun m x => (F (kn m) x, back m x)
  let targetsInf : X → Y × X := fun x => (Finf x, backInf x)
  have htargets : MapCInfConvOnCompacts U targets targetsInf :=
    mapCInfConv_prodMk hU hFk hback (fun m => hFc (kn m)) hFinfc
      hbackc hbackInfc
  have htargetsc : ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞) (targets m) U :=
    fun m => (hFc (kn m)).prodMk (hbackc m)
  have htargetsInfc :
      ContDiffOn Real (∞ : WithTop ℕ∞) targetsInf U :=
    hFinfc.prodMk hbackInfc
  let outer : X × (Y × X) → X := fun q =>
    q.1 + cut q.2.1 • (q.2.2 - q.1)
  have houter : ContDiff Real (∞ : WithTop ℕ∞) outer := by
    fun_prop
  have hconv := mapCInfConvOnCompacts_comp_prodMk_id
    (E' := X) (P := X) (Q := Y × X)
    hU (isOpen_univ : IsOpen (Set.univ : Set (X × (Y × X))))
    (mapCInfConv_const (U := U) id) htargets
    (fun _ => contDiffOn_id) contDiffOn_id htargetsc htargetsInfc
    houter.contDiffOn
    (fun _ _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    (fun x hx => hdiag x hx)
  change MapCInfConvOnCompacts U
    (fun m y => y + cut (F (kn m) y) •
      (R (ln m) (safe (F (kn m) y)) - y)) (fun y => y)
  simpa only [safeF, safeFinf, back, backInf, targets,
    targetsInf, outer, id_eq] using hconv

section Slots

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

noncomputable def stageTotal
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r)
    (pairPts : InterSlot L pb r alpha → Nat → Nat → E → E)
    (a b : Nat) (z : E) (gamma : Fin (pb.A r)) : E :=
  match interSlot? alpha gamma with
  | some target => pairPts target a b z
  | none => z

omit [CompleteSpace E] in
theorem stageTotal_smooth
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r)
    (pairPts : InterSlot L pb r alpha → Nat → Nat → E → E)
    {U : Set E} (a b : Nat)
    (hpair : ∀ target,
      ContDiffOn Real (∞ : WithTop ℕ∞) (pairPts target a b) U)
    (gamma : Fin (pb.A r)) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => stageTotal alpha pairPts a b z gamma) U := by
  classical
  unfold stageTotal
  cases hlookup : interSlot? alpha gamma with
  | none => exact contDiffOn_id
  | some target => exact hpair target

omit [CompleteSpace E] in
theorem stageTotal_conv
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r)
    (pairPts : InterSlot L pb r alpha → Nat → Nat → E → E)
    {U : Set E} (kn ln : Nat → Nat)
    (hpair : ∀ target,
      MapCInfConvOnCompacts U
        (fun m => pairPts target (kn m) (ln m)) id)
    (gamma : Fin (pb.A r)) :
    MapCInfConvOnCompacts U
      (fun m z => stageTotal alpha pairPts (kn m) (ln m) z gamma) id := by
  classical
  unfold stageTotal
  cases hlookup : interSlot? alpha gamma with
  | none => exact mapCInfConv_const (U := U) id
  | some target => exact hpair target

omit [CompleteSpace E] in
theorem stageTotal_pi_conv
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r)
    (pairPts : InterSlot L pb r alpha → Nat → Nat → E → E)
    {U : Set E} (hU : IsOpen U) (kn ln : Nat → Nat)
    (hpair : ∀ target,
      MapCInfConvOnCompacts U
        (fun m => pairPts target (kn m) (ln m)) id)
    (hpairc : ∀ target m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (pairPts target (kn m) (ln m)) U) :
    MapCInfConvOnCompacts U
      (fun m z gamma => stageTotal alpha pairPts
        (kn m) (ln m) z gamma)
      (fun z _ => z) := by
  apply mapCInfConv_pi hU
  · exact fun gamma => stageTotal_conv alpha pairPts kn ln hpair gamma
  · exact fun gamma m => stageTotal_smooth alpha pairPts (kn m) (ln m)
      (fun target => hpairc target m) gamma
  · exact fun _ => contDiffOn_id

end Slots

section Bumps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [HasContDiffBump E]

noncomputable def activityBump (lam : Real) (hlam : 0 < lam) :
    ContDiffBump (0 : E) where
  rIn := 6 * lam
  rOut := 7 * lam
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def safetyBump (lam : Real) (hlam : 0 < lam) :
    ContDiffBump (0 : E) where
  rIn := 7 * lam
  rOut := 8 * lam
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def stageClamp (lam : Real) (hlam : 0 < lam) : E → E :=
  (safetyBump (E := E) lam hlam).radial

noncomputable def stageFill (lam : Real) (hlam : 0 < lam)
    (F R : E → E) : E → E :=
  safeFill (activityBump (E := E) lam hlam)
    (stageClamp (E := E) lam hlam) F R

theorem activity_one (lam : Real) (hlam : 0 < lam) {y : E}
    (hy : y ∈ Metric.closedBall 0 (6 * lam)) :
    activityBump (E := E) lam hlam y = 1 := by
  exact (activityBump (E := E) lam hlam).one_of_mem_closedBall hy

theorem stageClamp_eq (lam : Real) (hlam : 0 < lam) {y : E}
    (hy : y ∈ Metric.closedBall 0 (7 * lam)) :
    stageClamp (E := E) lam hlam y = y := by
  exact (safetyBump (E := E) lam hlam).radial_eq_self hy

theorem stageClamp_mapsTo (lam : Real) (hlam : 0 < lam) :
    MapsTo (stageClamp (E := E) lam hlam) Set.univ
      (Metric.ball 0 (8 * lam)) := by
  exact (safetyBump (E := E) lam hlam).radial_mapsTo

theorem stageFill_eq_raw (lam : Real) (hlam : 0 < lam)
    (F R : E → E) {x : E}
    (hx : F x ∈ Metric.closedBall 0 (6 * lam)) :
    stageFill lam hlam F R x = R (F x) := by
  have hx7 : F x ∈ Metric.closedBall 0 (7 * lam) :=
    Metric.closedBall_subset_closedBall (by linarith) hx
  rw [stageFill, safeFill, activity_one lam hlam hx,
    stageClamp_eq lam hlam hx7, one_smul]
  exact add_sub_cancel x (R (F x))

theorem stageFill_eq_self (lam : Real) (hlam : 0 < lam)
    (F R : E → E) {x : E}
    (hx : activityBump (E := E) lam hlam (F x) = 0) :
    stageFill lam hlam F R x = x := by
  simp only [stageFill, safeFill, hx, zero_smul, add_zero]

theorem stageFill_conv [ProperSpace E]
    (lam : Real) (hlam : 0 < lam) {U : Set E} (hU : IsOpen U)
    {F R : Nat → E → E} {Finf Rinf : E → E}
    (hF : MapCInfConvOnCompacts U F Finf)
    (hR : MapCInfConvOnCompacts (Metric.ball 0 (8 * lam)) R Rinf)
    (hFc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (F k) U)
    (hFinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Finf U)
    (hRc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (R k)
      (Metric.ball 0 (8 * lam)))
    (hRinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Rinf
      (Metric.ball 0 (8 * lam)))
    (hinv : ∀ z ∈ U, Finf z ∈ Metric.ball 0 (8 * lam) →
      Rinf (Finf z) = z)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    MapCInfConvOnCompacts U
      (fun m => stageFill lam hlam (F (kn m)) (R (ln m))) id := by
  have hdiag : ∀ z ∈ U,
      z + activityBump (E := E) lam hlam (Finf z) •
        (Rinf (stageClamp (E := E) lam hlam (Finf z)) - z) = z := by
    intro z hz
    by_cases hcut : activityBump (E := E) lam hlam (Finf z) = 0
    · simp only [hcut, zero_smul, add_zero]
    · have hz7 : Finf z ∈ Metric.ball 0 (7 * lam) := by
        have hzout : Finf z ∈ Metric.ball 0
            (activityBump (E := E) lam hlam).rOut := by
          rw [← (activityBump (E := E) lam hlam).support_eq]
          exact hcut
        simpa only [activityBump] using hzout
      have hsafe : stageClamp (E := E) lam hlam (Finf z) = Finf z :=
        stageClamp_eq lam hlam (Metric.ball_subset_closedBall hz7)
      have hz8 : Finf z ∈ Metric.ball 0 (8 * lam) :=
        Metric.ball_subset_ball (by linarith) hz7
      rw [hsafe, hinv z hz hz8, sub_self, smul_zero, add_zero]
  simpa only [stageFill] using
    (safeFill_diag hU Metric.isOpen_ball hF hR hFc hFinfc hRc hRinfc
      (activityBump (E := E) lam hlam) (stageClamp (E := E) lam hlam)
      (activityBump (E := E) lam hlam).contDiff
      (safetyBump (E := E) lam hlam).radial_contDiff
      (stageClamp_mapsTo (E := E) lam hlam) hdiag kn ln hkn hln)

end Bumps

section StagePairs

open DifferentialGeometry.Geometry.Riemannian

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

noncomputable def pairStageFill
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha) (k l : Nat) : E → E := by
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
  exact stageFill (L.lamInf (target.1.1 : Nat))
    (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
    (normalTransition (I := I) Yk
      (seqCenterD inp.decay P L k (alpha.1 : Nat))
      (seqCenterD inp.decay P L k (target.1.1 : Nat)))
    (normalTransition (I := I) Yl
      (seqCenterD inp.decay P L l (target.1.1 : Nat))
      (seqCenterD inp.decay P L l (alpha.1 : Nat)))

noncomputable def stagePts
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (alpha : LiveSlot L inp.pack r) (k l : Nat)
    (z : E) (gamma : Fin (inp.pack.A r)) : E :=
  stageTotal alpha (pairStageFill inp P L alpha) k l z gamma

noncomputable def stageWeight
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (alpha : LiveSlot L inp.pack r) (k : Nat)
    (z : E) (gamma : Fin (inp.pack.A r)) : Real :=
  let beta := fun j => seqCenterD inp.decay P L j (alpha.1 : Nat)
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  rawWeights
    (cutRaw
      (seqAtomChart (I := I) inp.decay inp.hD P L inp.pack r beta i0 k)
      (fun target => seqAtomChart (I := I) inp.decay inp.hD P L
        inp.pack r beta target k)
      i0) z gamma

noncomputable def stageCfg
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (alpha : LiveSlot L inp.pack r) (k l : Nat) (z : E) :
    (Fin (inp.pack.A r) → Real) × (Fin (inp.pack.A r) → E) :=
  (stageWeight inp P L hr alpha k z, stagePts inp P L alpha k l z)

noncomputable def pairStageFillSub
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha) (k l : Nat)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) : E → E := by
  let _ := hphi
  let Yk := X.obj (L.φ (phi k))
  let Yl := X.obj (L.φ (phi l))
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
  exact stageFill (L.lamInf (target.1.1 : Nat))
    (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
    (chart.transition (L.φ (phi k))
      (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
      (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
    (chart.transition (L.φ (phi l))
      (seqCenterD inp.decay P L (phi l) (target.1.1 : Nat))
      (seqCenterD inp.decay P L (phi l) (alpha.1 : Nat)))

noncomputable def stagePtsSub
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r) (k l : Nat)
    (z : E) (gamma : Fin (inp.pack.A r))
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) : E :=
  stageTotal alpha
    (pairStageFillSub inp P L phi hphi alpha (chart := chart)) k l z gamma

noncomputable def stageWeightSub
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r) (k : Nat)
    (z : E) (gamma : Fin (inp.pack.A r))
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) : Real := by
  let _ := hphi
  let beta := fun j => seqCenterD inp.decay P L j (alpha.1 : Nat)
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  exact rawWeights
    (cutRaw
      (seqAtomOn (I := I) chart inp.decay inp.hD P L inp.pack r
        beta i0 (phi k))
      (fun target => seqAtomOn (I := I) chart inp.decay inp.hD P L
        inp.pack r beta target (phi k))
      i0) z gamma

theorem stageWeightSub_eq
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r) (k : Nat)
    (z : E) (gamma : Fin (inp.pack.A r))
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) :
    stageWeightSub inp P L hr phi hphi alpha k z gamma (chart := chart) =
      let Y := X.obj (L.φ (phi k))
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      let i0 := baseIndex inp.decay inp.realizes inp.pack hr
      rawWeights
        (cutRaw
          (seqAtom inp.decay inp.hD P L inp.pack r (phi k) i0)
          (seqAtom inp.decay inp.hD P L inp.pack r (phi k))
          i0)
        (chart.hom (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z)
        gamma := by
  simp only [stageWeightSub, seqAtomOn, NormalChartFamily.hom,
    rawWeights, cutRaw]

noncomputable def stageCfgSub
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r) (k l : Nat) (z : E)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) :
    (Fin (inp.pack.A r) → Real) × (Fin (inp.pack.A r) → E) :=
  (stageWeightSub inp P L hr phi hphi alpha k z (chart := chart),
    stagePtsSub inp P L phi hphi alpha k l z (chart := chart))

theorem HasSuppConvDataOn.weightSub_ev_raw
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf) :
    ∀ᶠ k in Filter.atTop, ∀ alpha : LiveSlot L inp.pack r,
      centerAverage.WeightDataOn (U alpha)
        (fun _ : Fin (inp.pack.A r) => Set.univ)
        (stageWeightSub inp P L hr phi hphi alpha k (chart := chart)) := by
  classical
  dsimp only [HasSuppConvDataOn] at hdata
  rcases hdata with
    ⟨_hUopen, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, hgeom, _hlim, _hweightData, _htrans, _hstage⟩
  refine Filter.Eventually.of_forall fun k alpha => ?_
  let Y := X.obj (L.φ (phi k))
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := (P (L.φ (phi k))).ms
  let f : E → Y.M := chart.hom (L.φ (phi k))
    (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let s : Set Y.M := ⋃ gamma : Fin (inp.pack.A r),
    L.innerBall inp.decay inp.D P inp.pack r (phi k) gamma
  have hf : Set.MapsTo f (U alpha) s := by
    intro z hz
    exact (((hgeom k).1 alpha).2 hz).2
  have hw := seqWeights_data_raw (I := I) inp.decay inp.hD P L inp.pack r (phi k)
    i0 (s := s) Set.Subset.rfl
  have hpull := hw.comp hf
  have hweight : centerAverage.WeightDataOn (U alpha)
      (fun gamma => f ⁻¹' L.hatBall inp.decay inp.D P inp.pack r (phi k) gamma)
      (stageWeightSub inp P L hr phi hphi alpha k (chart := chart)) := by
    simpa only [stageWeightSub_eq, f, i0] using hpull
  exact ⟨hweight.nonneg, hweight.pos, hweight.sum_one,
    fun z _hz _gamma _hne => Set.mem_univ z⟩

theorem HasSuppConvDataOn.weightSub_ev
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf) :
    ∀ᶠ k in Filter.atTop, ∀ alpha : LiveSlot L inp.pack r,
      centerAverage.WeightDataOn (U alpha)
        (fun _ : Fin (inp.pack.A r) => Set.univ)
        (stageWeightSub inp P L hr phi hphi alpha k (chart := chart)) := by
  exact hdata.weightSub_ev_raw inp P L hr phi hphi chart
    U C0 C1 aInf Jinf Jbarinf

theorem HasSuppConvData.weightSub_ev
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf) :
    ∀ᶠ k in Filter.atTop, ∀ alpha : LiveSlot L inp.pack r,
      centerAverage.WeightDataOn (U alpha)
        (fun _ : Fin (inp.pack.A r) => Set.univ)
        (stageWeightSub inp P L hr phi hphi alpha k) := by
  classical
  dsimp only [HasSuppConvData] at hdata
  rcases hdata with
    ⟨_hUopen, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, hgeom, _hlim, _hweightData, _htrans, _hstage⟩
  filter_upwards with k
  intro alpha
  let Y := X.obj (L.φ (phi k))
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := (P (L.φ (phi k))).ms
  let f : E → Y.M :=
    (c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
      (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let s : Set Y.M := ⋃ gamma : Fin (inp.pack.A r),
    L.innerBall inp.decay inp.D P inp.pack r (phi k) gamma
  have hf : Set.MapsTo f (U alpha) s := by
    intro z hz
    exact (((hgeom k).1 alpha).2.2 hz).2
  have hw := seqWeights_data (I := I) inp.decay inp.hD P L inp.pack r (phi k)
    i0 (s := s) Set.Subset.rfl
  have hpull := hw.comp hf
  have hweight : centerAverage.WeightDataOn (U alpha)
      (fun gamma => f ⁻¹' L.hatBall inp.decay inp.D P inp.pack r (phi k) gamma)
      (stageWeightSub inp P L hr phi hphi alpha k) := by
    simpa only [stageWeightSub_eq, MetricCompactnessInputs.toCore, f, i0] using hpull
  exact ⟨hweight.nonneg, hweight.pos, hweight.sum_one,
    fun z _hz _gamma _hne => Set.mem_univ z⟩

theorem stageWeight_small
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (alpha : LiveSlot L inp.pack r) (k : Nat)
    (hgp : ExponentialRadiusScaleAt (I := I) inp.decay inp.D P L inp.pack r k)
    (gamma : Fin (inp.pack.A r))
    (hC2 :
      letI : TopologicalSpace (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      8 * L.lamInf (gamma : Nat) ≤
        expMapC2Radius (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (gamma : Nat)))
    (z : E) (hweight : stageWeight inp P L hr alpha k z gamma ≠ 0) :
    letI : TopologicalSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    normalTransition (I := I) (X.obj (L.φ k))
        (seqCenterD inp.decay P L k (alpha.1 : Nat))
        (seqCenterD inp.decay P L k (gamma : Nat)) z ∈
      Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  let beta := fun j => seqCenterD inp.decay P L j (alpha.1 : Nat)
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  apply Metric.ball_subset_closedBall
  apply inp.weight_trans_small P L r k hgp beta i0 gamma hC2 z
  simpa only [stageWeight, beta, i0] using hweight

theorem HasAtomWeightLim.stageWeight_data
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L
      inp.realizes inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf := fun z gamma =>
      rawWeights (cutRaw (aInf i0) aInf i0) z gamma
    (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (stageWeight inp P L hr alpha k) U) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) weightInf U ∧
      MapCInfConvOnCompacts U
        (fun k => stageWeight inp P L hr alpha k) weightInf := by
  dsimp only [HasAtomWeightLim] at hlim
  simpa only [stageWeight] using
    ⟨hlim.2.2.2.2.1, hlim.2.2.2.2.2.1, hlim.2.2.2.2.2.2⟩

theorem stageCfg_conv
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (alpha : LiveSlot L inp.pack r) (U : Set E) (hU : IsOpen U)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L
      inp.realizes inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hpts : MapCInfConvOnCompacts U
      (fun m z => stagePts inp P L alpha (kn m) (ln m) z)
      (fun z _ => z))
    (hptsc : ∀ m, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => stagePts inp P L alpha (kn m) (ln m) z) U) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf := fun z gamma =>
      rawWeights (cutRaw (aInf i0) aInf i0) z gamma
    MapCInfConvOnCompacts U
      (fun m => stageCfg inp P L hr alpha (kn m) (ln m))
      (fun z => (weightInf z, fun _ => z)) := by
  dsimp only
  obtain ⟨hweightc, hweightInfc, hweight⟩ :=
    hlim.stageWeight_data inp P L hr alpha U aInf
  have hweightKn := hweight.comp_tendsto_atTop hkn
  have hdiagc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z : E => fun _ : Fin (inp.pack.A r) => z) U :=
    contDiffOn_pi.mpr fun _ => contDiffOn_id
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let weightInf := fun z gamma =>
    rawWeights (cutRaw (aInf i0) aInf i0) z gamma
  change MapCInfConvOnCompacts U
    (fun m z =>
      (stageWeight inp P L hr alpha (kn m) z,
        stagePts inp P L alpha (kn m) (ln m) z))
    (fun z => (weightInf z, fun _ => z))
  exact mapCInfConv_prodMk hU hweightKn hpts
    (fun m => hweightc (kn m)) hweightInfc hptsc hdiagc

theorem HasAtomWeightLimOn.stageWeightSub_data
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLimOn (I := I) chart inp.decay inp.hD P
      (L.subseq hphi) inp.realizes inp.pack r hr
      (fun k => seqCenterD inp.decay P (L.subseq hphi) k
        (alpha.1 : Nat)) U aInf) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf := fun z gamma =>
      rawWeights (cutRaw (aInf i0) aInf i0) z gamma
    (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (stageWeightSub inp P L hr phi hphi alpha k
        (chart := chart)) U) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) weightInf U ∧
      MapCInfConvOnCompacts U
        (fun k => stageWeightSub inp P L hr phi hphi alpha k
          (chart := chart))
        weightInf := by
  change HasAtomWeightLimOn (I := I) chart inp.decay inp.hD P
    (L.subseq hphi) inp.realizes inp.pack r hr
    (fun k => seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) U aInf at hlim
  dsimp only [HasAtomWeightLimOn] at hlim
  have hatom (gamma : Fin (inp.pack.A r)) (k : Nat) :
      seqAtomOn (I := I) chart inp.decay inp.hD P (L.subseq hphi)
          inp.pack r
          (fun j => seqCenterD inp.decay P L (phi j) (alpha.1 : Nat))
          gamma k =
        seqAtomOn (I := I) chart inp.decay inp.hD P L inp.pack r
          (fun j => seqCenterD inp.decay P L j (alpha.1 : Nat))
          gamma (phi k) := by
    simpa only using
      (seqAtomOn_subseq (I := I) chart inp.decay inp.hD P L inp.pack r
        (fun j => seqCenterD inp.decay P L j (alpha.1 : Nat)) gamma hphi k)
  simp only [hatom] at hlim
  simpa only [stageWeightSub] using
    ⟨hlim.2.2.2.2.1, hlim.2.2.2.2.2.1, hlim.2.2.2.2.2.2⟩

theorem HasAtomWeightLim.stageWeightSub_data
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P
      (L.subseq hphi) inp.realizes inp.pack r hr
      (fun k => seqCenterD inp.decay P (L.subseq hphi) k
        (alpha.1 : Nat)) U aInf) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf := fun z gamma =>
      rawWeights (cutRaw (aInf i0) aInf i0) z gamma
    (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (stageWeightSub inp P L hr phi hphi alpha k) U) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) weightInf U ∧
      MapCInfConvOnCompacts U
        (fun k => stageWeightSub inp P L hr phi hphi alpha k)
        weightInf := by
  change HasAtomWeightLim (I := I) inp.decay inp.hD P
    (L.subseq hphi) inp.realizes inp.pack r hr
    (fun k => seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) U aInf at hlim
  dsimp only [HasAtomWeightLim] at hlim
  have hatom (gamma : Fin (inp.pack.A r)) (k : Nat) :
      seqAtomChart (I := I) inp.decay inp.hD P (L.subseq hphi)
          inp.pack r
          (fun j => seqCenterD inp.decay P L (phi j) (alpha.1 : Nat))
          gamma k =
        seqAtomOn (I := I) (c2RadiusNormalChartFamily (I := I) X)
          inp.decay inp.hD P L inp.pack r
          (fun j => seqCenterD inp.decay P L j (alpha.1 : Nat))
          gamma (phi k) := by
    calc
      _ = seqAtomChart (I := I) inp.decay inp.hD P L inp.pack r
          (fun j => seqCenterD inp.decay P L j (alpha.1 : Nat))
          gamma (phi k) := by
        simpa only using
          (seqAtomChart_subseq (I := I) inp.decay inp.hD P L inp.pack r
            (fun j => seqCenterD inp.decay P L j (alpha.1 : Nat))
            gamma hphi k)
      _ = _ := by
        funext z
        simp only [seqAtomChart, seqAtomOn,           c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_apply]
  simp only [hatom] at hlim
  simpa only [stageWeightSub, MetricCompactnessInputs.toCore] using
    ⟨hlim.2.2.2.2.1, hlim.2.2.2.2.2.1, hlim.2.2.2.2.2.2⟩

theorem stageCfgSub_conv_on
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (alpha : LiveSlot L inp.pack r) (U : Set E) (hU : IsOpen U)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLimOn (I := I) chart inp.decay inp.hD P
      (L.subseq hphi) inp.realizes inp.pack r hr
      (fun k => seqCenterD inp.decay P (L.subseq hphi) k
        (alpha.1 : Nat)) U aInf)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hpts : MapCInfConvOnCompacts U
      (fun m z => stagePtsSub inp P L phi hphi alpha
        (kn m) (ln m) z (chart := chart))
      (fun z _ => z))
    (hptsc : ∀ m, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => stagePtsSub inp P L phi hphi alpha
        (kn m) (ln m) z (chart := chart)) U) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf := fun z gamma =>
      rawWeights (cutRaw (aInf i0) aInf i0) z gamma
    MapCInfConvOnCompacts U
      (fun m => stageCfgSub inp P L hr phi hphi alpha
        (kn m) (ln m) (chart := chart))
      (fun z => (weightInf z, fun _ => z)) := by
  dsimp only
  obtain ⟨hweightc, hweightInfc, hweight⟩ :=
    hlim.stageWeightSub_data inp P L hr phi hphi chart alpha U aInf
  have hweightKn := hweight.comp_tendsto_atTop hkn
  have hdiagc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z : E => fun _ : Fin (inp.pack.A r) => z) U :=
    contDiffOn_pi.mpr fun _ => contDiffOn_id
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let weightInf := fun z gamma =>
    rawWeights (cutRaw (aInf i0) aInf i0) z gamma
  change MapCInfConvOnCompacts U
    (fun m z =>
      (stageWeightSub inp P L hr phi hphi alpha (kn m) z
          (chart := chart),
        stagePtsSub inp P L phi hphi alpha (kn m) (ln m) z
          (chart := chart)))
    (fun z => (weightInf z, fun _ => z))
  exact mapCInfConv_prodMk hU hweightKn hpts
    (fun m => hweightc (kn m)) hweightInfc hptsc hdiagc

theorem stageCfgSub_conv
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r) (U : Set E) (hU : IsOpen U)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P
      (L.subseq hphi) inp.realizes inp.pack r hr
      (fun k => seqCenterD inp.decay P (L.subseq hphi) k
        (alpha.1 : Nat)) U aInf)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hpts : MapCInfConvOnCompacts U
      (fun m z => stagePtsSub inp P L phi hphi alpha
        (kn m) (ln m) z)
      (fun z _ => z))
    (hptsc : ∀ m, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => stagePtsSub inp P L phi hphi alpha
        (kn m) (ln m) z) U) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf := fun z gamma =>
      rawWeights (cutRaw (aInf i0) aInf i0) z gamma
    MapCInfConvOnCompacts U
      (fun m => stageCfgSub inp P L hr phi hphi alpha (kn m) (ln m))
      (fun z => (weightInf z, fun _ => z)) := by
  dsimp only
  obtain ⟨hweightc, hweightInfc, hweight⟩ :=
    hlim.stageWeightSub_data inp P L hr phi hphi alpha U aInf
  have hweightKn := hweight.comp_tendsto_atTop hkn
  have hdiagc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z : E => fun _ : Fin (inp.pack.A r) => z) U :=
    contDiffOn_pi.mpr fun _ => contDiffOn_id
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let weightInf := fun z gamma =>
    rawWeights (cutRaw (aInf i0) aInf i0) z gamma
  change MapCInfConvOnCompacts U
    (fun m z =>
      (stageWeightSub inp.toCore P L hr phi hphi alpha (kn m) z,
        stagePtsSub inp.toCore P L phi hphi alpha (kn m) (ln m) z))
    (fun z => (weightInf z, fun _ => z))
  exact mapCInfConv_prodMk hU hweightKn hpts
    (fun m => hweightc (kn m)) hweightInfc hptsc hdiagc

theorem stagePts_eq_raw
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha) (k l : Nat) (z : E)
    (hsmall : normalTransition (I := I) (X.obj (L.φ k))
      (seqCenterD inp.decay P L k (alpha.1 : Nat))
      (seqCenterD inp.decay P L k (target.1.1 : Nat)) z ∈
        Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat))) :
    stagePts inp P L alpha k l z target.1.1 =
      normalTransition (I := I) (X.obj (L.φ l))
        (seqCenterD inp.decay P L l (target.1.1 : Nat))
        (seqCenterD inp.decay P L l (alpha.1 : Nat))
        (normalTransition (I := I) (X.obj (L.φ k))
          (seqCenterD inp.decay P L k (alpha.1 : Nat))
          (seqCenterD inp.decay P L k (target.1.1 : Nat)) z) := by
  classical
  have hlookup : interSlot? alpha target.1.1 = some target := by
    unfold interSlot?
    split
    next h =>
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact Classical.choose_spec h
    next h =>
      exact (h ⟨target, rfl⟩).elim
  simp only [stagePts, stageTotal, hlookup]
  simpa only [pairStageFill] using
    (stageFill_eq_raw (E := E) (L.lamInf (target.1.1 : Nat))
      (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
      (normalTransition (I := I) (X.obj (L.φ k))
        (seqCenterD inp.decay P L k (alpha.1 : Nat))
        (seqCenterD inp.decay P L k (target.1.1 : Nat)))
      (normalTransition (I := I) (X.obj (L.φ l))
        (seqCenterD inp.decay P L l (target.1.1 : Nat))
        (seqCenterD inp.decay P L l (alpha.1 : Nat))) hsmall)

theorem stagePts_eq_weight
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha) (k l : Nat)
    (hgp : ExponentialRadiusScaleAt (I := I) inp.decay inp.D P L inp.pack r k)
    (hC2 :
      letI : TopologicalSpace (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      8 * L.lamInf (target.1.1 : Nat) ≤
        expMapC2Radius (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (target.1.1 : Nat)))
    (z : E)
    (hweight : stageWeight inp P L hr alpha k z target.1.1 ≠ 0) :
    stagePts inp P L alpha k l z target.1.1 =
      normalTransition (I := I) (X.obj (L.φ l))
        (seqCenterD inp.decay P L l (target.1.1 : Nat))
        (seqCenterD inp.decay P L l (alpha.1 : Nat))
        (normalTransition (I := I) (X.obj (L.φ k))
          (seqCenterD inp.decay P L k (alpha.1 : Nat))
          (seqCenterD inp.decay P L k (target.1.1 : Nat)) z) := by
  exact stagePts_eq_raw inp P L alpha target k l z
    (stageWeight_small inp P L hr alpha k hgp target.1.1 hC2 z hweight)

theorem stagePtsSub_eq_raw
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha) (k l : Nat)
    (z : E)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X)
    (hsmall : chart.transition (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)) z ∈
        Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat))) :
    stagePtsSub inp P L phi hphi alpha k l z target.1.1
        (chart := chart) =
      chart.transition (L.φ (phi l))
        (seqCenterD inp.decay P L (phi l) (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi l) (alpha.1 : Nat))
        (chart.transition (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)) z) := by
  classical
  have hlookup : interSlot? alpha target.1.1 = some target := by
    unfold interSlot?
    split
    next h =>
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact Classical.choose_spec h
    next h =>
      exact (h ⟨target, rfl⟩).elim
  simp only [stagePtsSub, stageTotal, hlookup]
  simpa only [pairStageFillSub, NormalChartFamily.transition,
    c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_transition] using
    (stageFill_eq_raw (E := E) (L.lamInf (target.1.1 : Nat))
      (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
      (chart.transition (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
      (chart.transition (L.φ (phi l))
        (seqCenterD inp.decay P L (phi l) (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi l) (alpha.1 : Nat))) hsmall)


theorem stagePtsSub_eq_ne
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha) (k l : Nat)
    (hgp : ExponentialRadiusScaleAt (I := I) inp.decay inp.D P
      L inp.pack r (phi k))
    (hC2 :
      let Y := X.obj (L.φ (phi k))
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      8 * L.lamInf (target.1.1 : Nat) ≤
        expMapC2Radius (I := I) Y.metric
          (seqCenterD inp.decay P L (phi k)
            (target.1.1 : Nat)))
    (z : E)
    (hweight : stageWeightSub inp.toCore P L hr phi hphi alpha k z
      target.1.1 ≠ 0) :
    stagePtsSub inp.toCore P L phi hphi alpha k l z target.1.1 =
      normalTransition (I := I) (X.obj (L.φ (phi l)))
        (seqCenterD inp.decay P L (phi l)
          (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi l)
          (alpha.1 : Nat))
        (normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k)
            (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k)
            (target.1.1 : Nat)) z) := by
  classical
  have hweight' : stageWeight inp P L hr alpha (phi k) z target.1.1 ≠ 0 := by
    simpa only [stageWeight, stageWeightSub_eq, rawWeights, cutRaw,
      seqAtomChart,
      NormalChartFamily.hom, c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_apply,
      MetricCompactnessInputs.toCore] using hweight
  have hsmall : normalTransition (I := I) (X.obj (L.φ (phi k)))
      (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
      (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)) z ∈
        Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat)) := by
    exact stageWeight_small inp P L hr alpha (phi k) hgp target.1.1 hC2 z hweight'
  simpa only [NormalChartFamily.transition, c2RadiusNormalChartFamily,
    c2_radius_normal_ball_chart_transition, MetricCompactnessInputs.toCore] using
      (stagePtsSub_eq_raw inp.toCore P L phi hphi alpha target k l z
        (chart := c2RadiusNormalChartFamily (I := I) X) (hsmall := by
          simpa only [NormalChartFamily.transition, c2RadiusNormalChartFamily,
            c2_radius_normal_ball_chart_transition, MetricCompactnessInputs.toCore] using hsmall))

theorem pairStageFill_conv
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha)
    (J Jbar : E → E)
    (hJc : ContDiffOn Real (∞ : WithTop ℕ∞) J
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))))
    (hJbarc : ContDiffOn Real (∞ : WithTop ℕ∞) Jbar
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))))
    (hJ : MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun k => normalTransition (I := I) (X.obj (L.φ k))
        (seqCenterD inp.decay P L k (alpha.1 : Nat))
        (seqCenterD inp.decay P L k (target.1.1 : Nat))) J)
    (hJbar : MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
      (fun k => normalTransition (I := I) (X.obj (L.φ k))
        (seqCenterD inp.decay P L k (target.1.1 : Nat))
        (seqCenterD inp.decay P L k (alpha.1 : Nat))) Jbar)
    (hstage : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj (L.φ k))
        (seqCenterD inp.decay P L k (alpha.1 : Nat))
        (seqCenterD inp.decay P L k (target.1.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))))
    (hstageBar : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj (L.φ k))
        (seqCenterD inp.decay P L k (target.1.1 : Nat))
        (seqCenterD inp.decay P L k (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))))
    (hinv : ∀ z,
      z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
      J z ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
      Jbar (J z) = z)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun m => pairStageFill inp P L alpha target (kn m) (ln m)) id := by
  simpa only [pairStageFill] using
    (stageFill_conv (E := E) (L.lamInf (target.1.1 : Nat))
      (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
      Metric.isOpen_ball hJ hJbar hstage hJc hstageBar hJbarc hinv
      kn ln hkn hln)

theorem pairStageSub_conv
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha)
    (J Jbar : E → E)
    (hJc : ContDiffOn Real (∞ : WithTop ℕ∞) J
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))))
    (hJbarc : ContDiffOn Real (∞ : WithTop ℕ∞) Jbar
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))))
    (hJ : MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun k => normalTransition (I := I)
        (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat))) J)
    (hJbar : MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
      (fun k => normalTransition (I := I)
        (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (alpha.1 : Nat))) Jbar)
    (hstage : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))))
    (hstageBar : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))))
    (hinv : ∀ z,
      z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
      J z ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
      Jbar (J z) = z)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun m => pairStageFillSub inp P L phi hphi alpha target
        (kn m) (ln m)) id := by
  simpa only [pairStageFillSub, NormalChartFamily.transition,
    c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_transition] using
    (stageFill_conv (E := E) (L.lamInf (target.1.1 : Nat))
      (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
      Metric.isOpen_ball hJ hJbar hstage hJc hstageBar hJbarc hinv
      kn ln hkn hln)

theorem pairSub_conv_on
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha)
    (J Jbar : E → E)
    (hJc : ContDiffOn Real (∞ : WithTop ℕ∞) J
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))))
    (hJbarc : ContDiffOn Real (∞ : WithTop ℕ∞) Jbar
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))))
    (hJ : MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun k => NormalChartFamily.transition (I := I) chart
        (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat))) J)
    (hJbar : MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
      (fun k => NormalChartFamily.transition (I := I) chart
        (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (alpha.1 : Nat))) Jbar)
    (hstage : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (NormalChartFamily.transition (I := I) chart
        (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))))
    (hstageBar : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (NormalChartFamily.transition (I := I) chart
        (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))))
    (hinv : ∀ z,
      z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
      J z ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
      Jbar (J z) = z)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun m => pairStageFillSub inp P L phi hphi alpha target
        (kn m) (ln m) (chart := chart)) id := by
  simpa only [pairStageFillSub, NormalChartFamily.transition] using
    (stageFill_conv (E := E) (L.lamInf (target.1.1 : Nat))
      (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
      Metric.isOpen_ball hJ hJbar hstage hJc hstageBar hJbarc hinv
      kn ln hkn hln)

theorem pairStageSub_smooth
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha) (k l : Nat)
    (hstage : ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))))
    (hstageBar : ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj (L.φ (phi l)))
        (seqCenterD inp.decay P L (phi l)
          (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi l)
          (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (pairStageFillSub inp P L phi hphi alpha target k l)
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) := by
  have hsafe : MapsTo
      (fun z => stageClamp (E := E)
        (L.lamInf (target.1.1 : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
        (normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k)
            (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k)
            (target.1.1 : Nat)) z))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
    intro z _hz
    exact stageClamp_mapsTo
      (E := E) (L.lamInf (target.1.1 : Nat))
      (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
      (Set.mem_univ _)
  simpa only [pairStageFillSub, NormalChartFamily.transition,
    c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_transition, stageFill, stageClamp] using
    (safeFill_smooth
      (activityBump (E := E) (L.lamInf (target.1.1 : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))).contDiff
      (safetyBump (E := E) (L.lamInf (target.1.1 : Nat))
        (inp.decay.lambda_pos inp.hD
          (L.rInf (target.1.1 : Nat)))).radial_contDiff
      hstage hstageBar hsafe)

theorem pairSub_smooth_on
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha) (k l : Nat)
    (hstage : ContDiffOn Real (∞ : WithTop ℕ∞)
      (NormalChartFamily.transition (I := I) chart
        (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k)
          (target.1.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))))
    (hstageBar : ContDiffOn Real (∞ : WithTop ℕ∞)
      (NormalChartFamily.transition (I := I) chart
        (L.φ (phi l))
        (seqCenterD inp.decay P L (phi l)
          (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi l)
          (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (pairStageFillSub inp P L phi hphi alpha target k l
        (chart := chart))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) := by
  have hsafe : MapsTo
      (fun z => stageClamp (E := E)
        (L.lamInf (target.1.1 : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
        (NormalChartFamily.transition (I := I) chart
          (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k)
            (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k)
            (target.1.1 : Nat)) z))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
    intro z _hz
    exact stageClamp_mapsTo
      (E := E) (L.lamInf (target.1.1 : Nat))
      (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
      (Set.mem_univ _)
  simpa only [pairStageFillSub, NormalChartFamily.transition, stageFill,
    stageClamp] using
    (safeFill_smooth
      (activityBump (E := E) (L.lamInf (target.1.1 : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))).contDiff
      (safetyBump (E := E) (L.lamInf (target.1.1 : Nat))
        (inp.decay.lambda_pos inp.hD
          (L.rInf (target.1.1 : Nat)))).radial_contDiff
      hstage hstageBar hsafe)

theorem stagePtsSub_conv
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r) {U : Set E} (hU : IsOpen U)
    (kn ln : Nat → Nat)
    (hpair : ∀ target : InterSlot L inp.pack r alpha,
      MapCInfConvOnCompacts U
        (fun m => pairStageFillSub inp P L phi hphi alpha target
          (kn m) (ln m)) id)
    (hpairc : ∀ target : InterSlot L inp.pack r alpha, ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (pairStageFillSub inp P L phi hphi alpha target
          (kn m) (ln m)) U) :
    MapCInfConvOnCompacts U
      (fun m z => stagePtsSub inp P L phi hphi alpha
        (kn m) (ln m) z)
      (fun z _ => z) := by
  exact stageTotal_pi_conv alpha
    (pairStageFillSub inp P L phi hphi alpha) hU kn ln hpair hpairc

theorem ptsSub_conv_on
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (alpha : LiveSlot L inp.pack r) {U : Set E} (hU : IsOpen U)
    (kn ln : Nat → Nat)
    (hpair : ∀ target : InterSlot L inp.pack r alpha,
      MapCInfConvOnCompacts U
        (fun m => pairStageFillSub inp P L phi hphi alpha target
          (kn m) (ln m) (chart := chart)) id)
    (hpairc : ∀ target : InterSlot L inp.pack r alpha, ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (pairStageFillSub inp P L phi hphi alpha target
          (kn m) (ln m) (chart := chart)) U) :
    MapCInfConvOnCompacts U
      (fun m z => stagePtsSub inp P L phi hphi alpha
        (kn m) (ln m) z (chart := chart))
      (fun z _ => z) := by
  exact stageTotal_pi_conv alpha
    (pairStageFillSub inp P L phi hphi alpha (chart := chart))
    hU kn ln hpair hpairc

theorem HasSuppConvDataOn.ptsSub_conv
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    ∀ alpha,
      MapCInfConvOnCompacts (U alpha)
        (fun m z => stagePtsSub inp P L phi hphi alpha
          (kn m) (ln m) z (chart := chart))
        (fun z _ => z) := by
  dsimp only [HasSuppConvDataOn] at hdata
  rcases hdata with
    ⟨hUopen, hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hgeom, _hlim, _hweightData, htrans, hstage⟩
  intro alpha
  have hpair : ∀ target : InterSlot L inp.pack r alpha,
      MapCInfConvOnCompacts (U alpha)
        (fun m => pairStageFillSub inp P L phi hphi alpha target
          (kn m) (ln m) (chart := chart)) id := by
    intro target
    have hJ : MapCInfConvOnCompacts
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
        (fun k => NormalChartFamily.transition (I := I) chart
          (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k)
            (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k)
            (target.1.1 : Nat)))
        (Jinf alpha target) := by
      simpa only [NormalChartFamily.transition] using
        (htrans alpha target).2.2.2.2.1
    have hJbar : MapCInfConvOnCompacts
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
        (fun k => NormalChartFamily.transition (I := I) chart
          (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k)
            (target.1.1 : Nat))
          (seqCenterD inp.decay P L (phi k)
            (alpha.1 : Nat)))
        (Jbarinf alpha target) := by
      simpa only [NormalChartFamily.transition] using
        (htrans alpha target).2.2.2.2.2.1
    have hstageF : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
        (NormalChartFamily.transition (I := I) chart
          (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k)
            (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k)
            (target.1.1 : Nat)))
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) := by
      intro k
      simpa only [NormalChartFamily.transition] using
        (hstage alpha target k).1
    have hstageR : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
        (NormalChartFamily.transition (I := I) chart
          (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k)
            (target.1.1 : Nat))
          (seqCenterD inp.decay P L (phi k)
            (alpha.1 : Nat)))
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
      intro k
      simpa only [NormalChartFamily.transition] using
        (hstage alpha target k).2
    have hball := pairSub_conv_on inp P L phi hphi chart alpha target
      (Jinf alpha target) (Jbarinf alpha target)
      (htrans alpha target).1
      (htrans alpha target).2.1
      hJ hJbar hstageF hstageR
      (htrans alpha target).2.2.2.2.2.2.1
      kn ln hkn hln
    exact fun K hK hKU p => hball K hK (hKU.trans (hU8 alpha)) p
  have hpairc : ∀ target : InterSlot L inp.pack r alpha, ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (pairStageFillSub inp P L phi hphi alpha target
          (kn m) (ln m) (chart := chart)) (U alpha) := by
    intro target m
    have hstageF : ContDiffOn Real (∞ : WithTop ℕ∞)
        (NormalChartFamily.transition (I := I) chart
          (L.φ (phi (kn m)))
          (seqCenterD inp.decay P L (phi (kn m))
            (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi (kn m))
            (target.1.1 : Nat)))
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) := by
      simpa only [NormalChartFamily.transition] using
        (hstage alpha target (kn m)).1
    have hstageR : ContDiffOn Real (∞ : WithTop ℕ∞)
        (NormalChartFamily.transition (I := I) chart
          (L.φ (phi (ln m)))
          (seqCenterD inp.decay P L (phi (ln m))
            (target.1.1 : Nat))
          (seqCenterD inp.decay P L (phi (ln m))
            (alpha.1 : Nat)))
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
      simpa only [NormalChartFamily.transition] using
        (hstage alpha target (ln m)).2
    exact (pairSub_smooth_on inp P L phi hphi chart alpha target
      (kn m) (ln m) hstageF hstageR).mono (hU8 alpha)
  exact ptsSub_conv_on inp P L phi hphi chart alpha
    (hUopen alpha) kn ln hpair hpairc

theorem HasSuppConvDataOn.pts_coord_tail
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      ∀ gamma : Fin (inp.pack.A r),
        dist z
          (stagePtsSub inp P L phi hphi alpha k l z gamma
            (chart := chart)) < eps := by
  have hconv := hdata.ptsSub_conv inp P L hr phi hphi chart
    U C0 C1 aInf Jinf Jbarinf
  dsimp only [HasSuppConvDataOn] at hdata
  rcases hdata with
    ⟨_hUopen, _hU8, hC0, _hC1, hC01, hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hgeom, _hlim, _hweightData, _htrans, _hstage⟩
  let PhiPts : Nat → Nat → Nat → E → (Fin (inp.pack.A r) → E) :=
    fun _ k l z => stagePtsSub inp P L phi hphi alpha k l z
      (chart := chart)
  have hconv3 : ∀ an kn ln : Nat → Nat,
      Tendsto an atTop atTop → Tendsto kn atTop atTop →
        Tendsto ln atTop atTop →
          MapCInfConvOnCompacts (U alpha)
            (fun m => PhiPts (an m) (kn m) (ln m))
            (fun z _ => z) := by
    intro _an kn ln _han hkn hln
    exact hconv kn ln hkn hln alpha
  have hepsHalf : 0 < eps / 2 := by positivity
  obtain ⟨N, hN⟩ := MapCInfConvOnCompacts.three_tail hconv3
    (hC0 alpha) ((hC01 alpha).trans (interior_subset.trans (hC1U alpha)))
    0 (eps / 2) hepsHalf
  refine ⟨N, ?_⟩
  intro k hk l hl z hz gamma
  have htuple :
      ‖(fun gamma =>
          stagePtsSub inp P L phi hphi alpha k l z gamma
            (chart := chart) - z)‖ ≤ eps / 2 := by
    change ‖(fun gamma => stagePtsSub inp P L phi hphi alpha k l z gamma
      (chart := chart)) - (fun _ => z)‖ ≤ eps / 2
    simpa only [PhiPts, mapDerivNorm, norm_iteratedFDeriv_zero] using
      hN N le_rfl k hk l hl 0 le_rfl z hz
  have hcomp :
      ‖stagePtsSub inp P L phi hphi alpha k l z gamma
          (chart := chart) - z‖ ≤ eps / 2 :=
    (norm_le_pi_norm
      (fun gamma => stagePtsSub inp P L phi hphi alpha k l z gamma
        (chart := chart) - z) gamma).trans htuple
  have hcoord : dist z
      (stagePtsSub inp P L phi hphi alpha k l z gamma
        (chart := chart)) ≤ eps / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hcomp
  exact hcoord.trans_lt (by linarith)


theorem HasSuppConvData.cfgSub_conv
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    ∀ alpha,
      let i0 := baseIndex inp.decay inp.realizes inp.pack hr
      let weightInf := fun z gamma =>
        rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
      MapCInfConvOnCompacts (U alpha)
        (fun m => stageCfgSub inp.toCore P L hr phi hphi alpha
          (kn m) (ln m))
        (fun z => (weightInf z, fun _ => z)) := by
  dsimp only [HasSuppConvData] at hdata
  rcases hdata with
    ⟨hUopen, hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hgeom, hlim, _hweightData, htrans, hstage⟩
  intro alpha
  dsimp only
  have hpair : ∀ target : InterSlot L inp.pack r alpha,
      MapCInfConvOnCompacts (U alpha)
        (fun m => pairStageFillSub inp.toCore P L phi hphi alpha target
          (kn m) (ln m)) id := by
    intro target
    have hball := pairStageSub_conv inp.toCore P L phi hphi alpha target
      (Jinf alpha target) (Jbarinf alpha target)
      (htrans alpha target).1
      (htrans alpha target).2.1
      (htrans alpha target).2.2.2.2.1
      (htrans alpha target).2.2.2.2.2.1
      (fun k => (hstage alpha target k).1)
      (fun k => (hstage alpha target k).2)
      (htrans alpha target).2.2.2.2.2.2.1
      kn ln hkn hln
    exact fun K hK hKU p => hball K hK (hKU.trans (hU8 alpha)) p
  have hpairc : ∀ target : InterSlot L inp.pack r alpha, ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (pairStageFillSub inp.toCore P L phi hphi alpha target
          (kn m) (ln m)) (U alpha) := by
    intro target m
    exact (pairStageSub_smooth inp.toCore P L phi hphi alpha target
      (kn m) (ln m) (hstage alpha target (kn m)).1
      (hstage alpha target (ln m)).2).mono (hU8 alpha)
  have hpts := stagePtsSub_conv inp.toCore P L phi hphi alpha
    (hUopen alpha) kn ln hpair hpairc
  have hptsc : ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z => stagePtsSub inp.toCore P L phi hphi alpha
          (kn m) (ln m) z) (U alpha) := by
    intro m
    change ContDiffOn Real (∞ : WithTop ℕ∞)
      (stageTotal alpha
        (pairStageFillSub inp.toCore P L phi hphi alpha)
        (kn m) (ln m)) (U alpha)
    exact contDiffOn_pi.mpr fun gamma =>
      stageTotal_smooth alpha
        (pairStageFillSub inp.toCore P L phi hphi alpha)
        (kn m) (ln m) (fun target => hpairc target m) gamma
  exact stageCfgSub_conv inp P L hr phi hphi alpha (U alpha)
    (hUopen alpha) (aInf alpha) (hlim alpha) kn ln hkn hpts hptsc

theorem HasSuppConvDataOn.cfgSub_data
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    ∀ alpha,
      let i0 := baseIndex inp.decay inp.realizes inp.pack hr
      let weightInf := fun z gamma =>
        rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
      (∀ m, ContDiffOn Real (∞ : WithTop ℕ∞)
        (stageCfgSub inp P L hr phi hphi alpha (kn m) (ln m)
          (chart := chart))
        (U alpha)) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z => (weightInf z,
          fun _ : Fin (inp.pack.A r) => z)) (U alpha) ∧
      MapCInfConvOnCompacts (U alpha)
        (fun m => stageCfgSub inp P L hr phi hphi alpha
          (kn m) (ln m) (chart := chart))
        (fun z => (weightInf z,
          fun _ : Fin (inp.pack.A r) => z)) := by
  have hpts := hdata.ptsSub_conv inp P L hr phi hphi chart
    U C0 C1 aInf Jinf Jbarinf kn ln hkn hln
  dsimp only [HasSuppConvDataOn] at hdata
  rcases hdata with
    ⟨hUopen, hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hgeom, hlim, _hweightData, _htrans, hstage⟩
  intro alpha
  dsimp only
  obtain ⟨hweightc, hweightInfc, _hweight⟩ :=
    (hlim alpha).stageWeightSub_data inp P L hr phi hphi chart alpha
      (U alpha) (aInf alpha)
  have hpairc : ∀ target : InterSlot L inp.pack r alpha, ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (pairStageFillSub inp P L phi hphi alpha target
          (kn m) (ln m) (chart := chart)) (U alpha) := by
    intro target m
    have hstageF : ContDiffOn Real (∞ : WithTop ℕ∞)
        (NormalChartFamily.transition (I := I) chart
          (L.φ (phi (kn m)))
          (seqCenterD inp.decay P L (phi (kn m))
            (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi (kn m))
            (target.1.1 : Nat)))
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) := by
      simpa only [NormalChartFamily.transition] using
        (hstage alpha target (kn m)).1
    have hstageR : ContDiffOn Real (∞ : WithTop ℕ∞)
        (NormalChartFamily.transition (I := I) chart
          (L.φ (phi (ln m)))
          (seqCenterD inp.decay P L (phi (ln m))
            (target.1.1 : Nat))
          (seqCenterD inp.decay P L (phi (ln m))
            (alpha.1 : Nat)))
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
      simpa only [NormalChartFamily.transition] using
        (hstage alpha target (ln m)).2
    exact (pairSub_smooth_on inp P L phi hphi chart alpha target
      (kn m) (ln m) hstageF hstageR).mono (hU8 alpha)
  have hptsc : ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z => stagePtsSub inp P L phi hphi alpha
          (kn m) (ln m) z (chart := chart)) (U alpha) := by
    intro m
    simpa only [stagePtsSub, MetricCompactnessInputs.toCore] using
      (contDiffOn_pi.mpr fun gamma =>
        stageTotal_smooth alpha
          (pairStageFillSub inp P L phi hphi alpha (chart := chart))
          (kn m) (ln m) (fun target => hpairc target m) gamma)
  have hdiagc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z : E => fun _ : Fin (inp.pack.A r) => z) (U alpha) :=
    contDiffOn_pi.mpr fun _ => contDiffOn_id
  have hconv := stageCfgSub_conv_on inp P L hr phi hphi chart alpha
    (U alpha) (hUopen alpha) (aInf alpha) (hlim alpha)
    kn ln hkn (hpts alpha) hptsc
  refine ⟨?_, hweightInfc.prodMk hdiagc, hconv⟩
  intro m
  simpa only [stageCfgSub] using
    (hweightc (kn m)).prodMk (hptsc m)


theorem HasSuppConvData.cfgSub_data
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    ∀ alpha,
      let i0 := baseIndex inp.decay inp.realizes inp.pack hr
      let weightInf := fun z gamma =>
        rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
      (∀ m, ContDiffOn Real (∞ : WithTop ℕ∞)
        (stageCfgSub inp.toCore P L hr phi hphi alpha (kn m) (ln m))
        (U alpha)) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z => (weightInf z,
          fun _ : Fin (inp.pack.A r) => z)) (U alpha) ∧
      MapCInfConvOnCompacts (U alpha)
        (fun m => stageCfgSub inp.toCore P L hr phi hphi alpha
          (kn m) (ln m))
        (fun z => (weightInf z,
          fun _ : Fin (inp.pack.A r) => z)) := by
  have hconv := hdata.cfgSub_conv inp P L hr phi hphi U C0 C1
    aInf Jinf Jbarinf kn ln hkn hln
  dsimp only [HasSuppConvData] at hdata
  rcases hdata with
    ⟨hUopen, hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hgeom, hlim, _hweightData, _htrans, hstage⟩
  intro alpha
  dsimp only
  obtain ⟨hweightc, hweightInfc, _hweight⟩ :=
    (hlim alpha).stageWeightSub_data inp P L hr phi hphi alpha
      (U alpha) (aInf alpha)
  have hpairc : ∀ target : InterSlot L inp.pack r alpha, ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (pairStageFillSub inp.toCore P L phi hphi alpha target
          (kn m) (ln m)) (U alpha) := by
    intro target m
    exact (pairStageSub_smooth inp.toCore P L phi hphi alpha target
      (kn m) (ln m) (hstage alpha target (kn m)).1
      (hstage alpha target (ln m)).2).mono (hU8 alpha)
  have hptsc : ∀ m,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z => stagePtsSub inp.toCore P L phi hphi alpha
          (kn m) (ln m) z) (U alpha) := by
    intro m
    change ContDiffOn Real (∞ : WithTop ℕ∞)
      (stageTotal alpha
        (pairStageFillSub inp.toCore P L phi hphi alpha)
        (kn m) (ln m)) (U alpha)
    exact contDiffOn_pi.mpr fun gamma =>
      stageTotal_smooth alpha
        (pairStageFillSub inp.toCore P L phi hphi alpha)
        (kn m) (ln m) (fun target => hpairc target m) gamma
  have hdiagc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z : E => fun _ : Fin (inp.pack.A r) => z) (U alpha) :=
    contDiffOn_pi.mpr fun _ => contDiffOn_id
  refine ⟨?_, hweightInfc.prodMk hdiagc, hconv alpha⟩
  intro m
  simpa only [stageCfgSub] using
    (hweightc (kn m)).prodMk (hptsc m)

theorem HasSuppConvData.ptsSub_conv
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (kn ln : Nat → Nat) (hkn : Tendsto kn atTop atTop)
    (hln : Tendsto ln atTop atTop) :
    ∀ alpha,
      MapCInfConvOnCompacts (U alpha)
        (fun m z => stagePtsSub inp.toCore P L phi hphi alpha
          (kn m) (ln m) z)
        (fun z _ => z) := by
  intro alpha
  obtain ⟨hU, _hC0, _hC1, _hC01, _hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hcfg, hdiag, hconv⟩ :=
    hdata.cfgSub_data inp P L hr phi hphi U C0 C1 aInf Jinf Jbarinf
      kn ln hkn hln alpha
  let proj := ContinuousLinearMap.snd Real
    (Fin (inp.pack.A r) → Real) (Fin (inp.pack.A r) → E)
  have hp := mapCInfConv_clm hU proj hconv hcfg hdiag
  have hproj (q : (Fin (inp.pack.A r) → Real) ×
      (Fin (inp.pack.A r) → E)) : proj q = q.2 := rfl
  simp only [hproj, stageCfgSub, MetricCompactnessInputs.toCore] at hp
  exact hp

theorem HasSuppConvData.pts_eq_ne
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.metricCoerciveRatio * inp.D)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf) :
    ∀ᶠ k in atTop, ∀ (alpha : LiveSlot L inp.pack r) (l : Nat)
        (z : E), z ∈ U alpha → ∀ gamma : Fin (inp.pack.A r),
      stageWeightSub inp.toCore P L hr phi hphi alpha k z gamma ≠ 0 →
        ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma ∧
          stagePtsSub inp.toCore P L phi hphi alpha k l z gamma =
            normalTransition (I := I) (X.obj ((L.subseq hphi).φ l))
              (seqCenterD inp.decay P (L.subseq hphi) l
                (target.1.1 : Nat))
              (seqCenterD inp.decay P (L.subseq hphi) l
                (alpha.1 : Nat))
              (normalTransition (I := I)
                (X.obj ((L.subseq hphi).φ k))
                (seqCenterD inp.decay P (L.subseq hphi) k
                  (alpha.1 : Nat))
                (seqCenterD inp.decay P (L.subseq hphi) k
                  (target.1.1 : Nat)) z) := by
  classical
  let Lphi := L.subseq hphi
  dsimp only [HasSuppConvData] at hdata
  rcases hdata with
    ⟨_hUopen, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, hgeom, _hlim, _hweightData, _htrans, _hstage⟩
  obtain ⟨hgp, hrad⟩ := inp.exponential_scale_tails h8 hradRatio P L r
  have hgpPhi : ExponentialRadiusScaleTail (I := I) inp.decay inp.D P
      Lphi inp.pack r :=
    hgp.subseq inp.decay inp.D P L inp.pack r hphi
  have hradPhi : ExponentialBallRadiusTail (I := I) inp.decay inp.D P
      Lphi inp.pack r (exponentialBallRadiusFactor inp.decay inp.D) :=
    hrad.subseq inp.decay inp.D P L inp.pack r
      (exponentialBallRadiusFactor inp.decay inp.D) hphi
  have hcenters : ∀ᶠ k in atTop, ∀ beta : LiveSlot L inp.pack r,
      seqCenter inp.decay inp.D P (Lphi.φ k) (beta.1 : Nat) =
        some (seqCenterD inp.decay P Lphi k (beta.1 : Nat)) :=
    Filter.eventually_all.mpr fun beta =>
      seqCenterD_live inp.decay P Lphi (beta.1 : Nat) (by
        simpa only [Lphi, NetLimitData.subseq] using beta.2)
  have hslots : ∀ᶠ k in atTop, ∀ (alpha : LiveSlot L inp.pack r)
      (gamma : Fin (inp.pack.A r)),
      BInter inp.decay inp.D P L.lamInf
          (alpha.1 : Nat) (gamma : Nat) (L.φ (phi k)) →
        ∃ target : InterSlot L inp.pack r alpha, target.1.1 = gamma :=
    Filter.eventually_all.mpr fun alpha =>
      Filter.eventually_all.mpr fun gamma => by
        rcases hstable (alpha.1 : Nat) (gamma : Nat) with hinter | hdisjoint
        · have hstatus := hphi.tendsto_atTop.eventually
            (L.alive_eventually (gamma : Nat))
          filter_upwards [hstatus] with k hstatusK
          intro hcurrent
          exact inter_slot_of_binter inp.decay P L inp.pack r alpha
            hstatusK (by
              exact hcurrent) hinter
        · have hdisjointPhi := hphi.tendsto_atTop.eventually hdisjoint
          filter_upwards [hdisjointPhi] with k hdisjointK
          intro hcurrent
          exact (hdisjointK hcurrent).elim
  have hfactor : (8 : Real) ≤ exponentialBallRadiusFactor inp.decay inp.D := by
    have hExp : (1 : Real) ≤
        Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) := by
      rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr
        (mul_nonneg inp.decay.C_nonneg
          (by nlinarith [(inp.decay.lambda_pos inp.hD 0).le]))
    rw [exponentialBallRadiusFactor]
    nlinarith
  filter_upwards [hgpPhi, hradPhi, hcenters, hslots]
    with k hgpK hradK hcentersK hslotsK
  let Y := X.obj (L.φ (phi k))
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := (P (L.φ (phi k))).ms
  intro alpha l z hz gamma hweight
  let q := NormalCoordinates.expMapDiffeo (I := I) Y.metric
    (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z
  have hhatAlpha : q ∈
      L.hatBall inp.decay inp.D P inp.pack r (phi k) alpha.1 := by
    have hmem := ((hgeom k).1 alpha).2.2 hz
    simpa only [q, MetricCompactnessInputs.toCore,
      NormalChartFamily.hom, c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_apply] using hmem.1
  have hnum : seqAtom inp.decay inp.hD P L inp.pack r (phi k) gamma q ≠ 0 := by
    simpa only [stageWeightSub_eq, seqAtomOn, q, Y,
      MetricCompactnessInputs.toCore, NormalChartFamily.hom,
      c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_apply] using
      (num_ne_of_cut_ne (num_ne_of_raw_ne hweight))
  have hhatGamma : q ∈
      L.hatBall inp.decay inp.D P inp.pack r (phi k) gamma :=
    seqAtom_mem_hat inp.decay inp.hD P L inp.pack r (phi k) gamma hnum
  have hcurrent := L.binter_of_mem_hat inp.decay inp.hD P inp.pack r (phi k)
    hhatAlpha hhatGamma
  obtain ⟨target, htarget⟩ := hslotsK alpha gamma hcurrent
  have hC2gamma : 8 * L.lamInf (gamma : Nat) ≤
      expMapC2Radius (I := I) Y.metric
        (seqCenterD inp.decay P L (phi k) (gamma : Nat)) := by
    have hscale : 8 * L.lamInf (gamma : Nat) ≤
        exponentialBallRadiusFactor inp.decay inp.D * L.lamInf (gamma : Nat) :=
      mul_le_mul_of_nonneg_right hfactor
        (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat))).le
    have hcenter := hcentersK target.1
    have hradTarget := hradK gamma
      (seqCenterD inp.decay P Lphi k (gamma : Nat)) (by
        simpa only [htarget] using hcenter)
    simpa only [Y, Lphi, NetLimitData.subseq_lamInf, seqCenterD_subseq,
      NetLimitData.subseq_phi, Function.comp_apply] using
      hscale.trans hradTarget.2
  refine ⟨target, htarget, ?_⟩
  simpa only [htarget, Lphi, NetLimitData.subseq_phi,
    seqCenterD_subseq, Function.comp_apply] using
    (stagePtsSub_eq_ne inp P L hr phi hphi alpha target k l hgpK (by
      simpa only [htarget] using hC2gamma) z (by
      simpa only [htarget] using hweight))

theorem pairFill_smooth
    (inp : MetricCompactnessInputs (I := I) X)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (alpha : LiveSlot L inp.pack r)
    (target : InterSlot L inp.pack r alpha) :
    ∀ᶠ k in atTop, ∀ᶠ l in atTop,
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (pairStageFill inp P L alpha target k l)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) := by
  have hinterRev : ∀ᶠ n in atTop,
      BInter inp.decay inp.D P L.lamInf
        (target.1.1 : Nat) (alpha.1 : Nat) (L.φ n) :=
    target.2.mono fun _ hn =>
      BInter.symm inp.decay inp.D P L.lamInf hn
  have hforward := inp.pair_overlap_tail hradRatio P L r
    alpha target.1 target.2
  have hreverse := inp.pair_overlap_tail hradRatio P L r
    target.1 alpha hinterRev
  filter_upwards [hforward] with k hk
  filter_upwards [hreverse] with l hl
  have hsafe : MapsTo
      (fun z => stageClamp (E := E)
        (L.lamInf (target.1.1 : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
        (normalTransition (I := I) (X.obj (L.φ k))
          (seqCenterD inp.decay P L k (alpha.1 : Nat))
          (seqCenterD inp.decay P L k (target.1.1 : Nat)) z))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
    intro z _hz
    exact stageClamp_mapsTo
      (E := E) (L.lamInf (target.1.1 : Nat))
      (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))
      (Set.mem_univ _)
  simpa only [pairStageFill, stageFill, stageClamp] using
    (safeFill_smooth
      (activityBump (E := E) (L.lamInf (target.1.1 : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat)))).contDiff
      (safetyBump (E := E) (L.lamInf (target.1.1 : Nat))
        (inp.decay.lambda_pos inp.hD
          (L.rInf (target.1.1 : Nat)))).radial_contDiff
      hk.2.2.2.2.1 hl.2.2.2.2.1 hsafe)

end StagePairs

end HCGCompactness
end DifferentialGeometry
