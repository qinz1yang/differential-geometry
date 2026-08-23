import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.GoodCoveringSeq



set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open Set
open scoped Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

noncomputable def seqCenterD
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (k gamma : Nat) : (X.obj (L.φ k)).M :=
  (seqCenter hd D P (L.φ k) gamma).getD (X.obj (L.φ k)).basepoint

omit [CompleteSpace E] in
theorem seqCenterD_dist_eq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (k gamma : Nat) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    seqRadius hd D P (L.φ k) gamma =
      dist (seqCenterD hd P L k gamma) (X.obj (L.φ k)).basepoint := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  unfold seqRadius seqCenterD seqCenter OrderedNet.netRadius
  cases OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
      (hd.lambda_continuous D) gamma <;> simp

omit [CompleteSpace E] in
@[simp] theorem seqCenterD_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) {ψ : Nat → Nat} (hψ : StrictMono ψ)
    (k gamma : Nat) :
    seqCenterD hd P (L.subseq hψ) k gamma = seqCenterD hd P L (ψ k) gamma := rfl

def LiveSlot
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :=
  {gamma : Fin (pb.A r) // L.alive (gamma : Nat) = true}

noncomputable instance liveSlotFintype
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :
    Fintype (LiveSlot L pb r) := by
  letI : Finite (LiveSlot L pb r) :=
    Finite.of_injective (fun gamma : LiveSlot L pb r => gamma.1)
      Subtype.val_injective
  exact Fintype.ofFinite (LiveSlot L pb r)

omit [CompleteSpace E] in
theorem seqCenterD_some
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (k gamma : Nat)
    (h : (seqCenter hd D P (L.φ k) gamma).isSome = true) :
    seqCenter hd D P (L.φ k) gamma = some (seqCenterD hd P L k gamma) := by
  cases hc : seqCenter hd D P (L.φ k) gamma with
  | none => simp [hc] at h
  | some c => simp [seqCenterD, hc]

omit [CompleteSpace E] in
theorem seqCenterD_live
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat) (hgamma : L.alive gamma = true) :
    ∀ᶠ k in Filter.atTop,
      seqCenter hd D P (L.φ k) gamma = some (seqCenterD hd P L k gamma) :=
  (L.alive_eventually gamma).mono fun k hk =>
    seqCenterD_some hd P L k gamma (hk.trans hgamma)

omit [CompleteSpace E] in
theorem seqCenter_dead
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat) (hgamma : L.alive gamma = false) :
    ∀ᶠ k in Filter.atTop, seqCenter hd D P (L.φ k) gamma = none :=
  (L.alive_eventually gamma).mono fun k hk => by
    cases hc : seqCenter hd D P (L.φ k) gamma with
    | none => rfl
    | some c => simp [hc, hgamma] at hk

end HCGCompactness
end DifferentialGeometry
