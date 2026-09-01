import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.MetricCompactness.Inputs

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace MetricCompactnessInputs

theorem cap_four
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    (4 : Real) * inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.hD 0).le
  have hle :
      (4 : Real) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_left _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.covering_scale_le_volume_radius

theorem cap_four_of_nonneg
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) {R : Real} (hR : 0 <= R) :
    (4 : Real) * inp.decay.lambda inp.D R <= inp.volume.r0 := by
  have hlam : inp.decay.lambda inp.D R <= inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_antitone inp.hD hR
  have hmul :
      (4 : Real) * inp.decay.lambda inp.D R <=
        (4 : Real) * inp.decay.lambda inp.D 0 :=
    mul_le_mul_of_nonneg_left hlam (by norm_num)
  exact hmul.trans inp.cap_four

theorem cap_inter
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) *
        inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.hD 0).le
  have hle :
      50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_right _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.covering_scale_le_volume_radius

theorem net_mult
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) (k : Nat) {R : Real}
    (hR : 0 <= R) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (inp.decay.lambdaBall inp.D k))
    (hSR : ∀ x ∈ S, inp.decay.dist k x (X.obj k).basepoint <= R)
    (z : (X.obj k).M) (J : Finset ((X.obj k).M)) (hJS : ↑J ⊆ S)
    (hJz : ∀ x ∈ J, inp.decay.dist k x z <= 4 * inp.decay.lambda inp.D R) :
    J.card <= inp.volume.multiplicity 4 := by
  exact InjectivityRadiusDecay.net_multiplicity
    inp.decay inp.D k inp.hD inp.realizes inp.volume inp.dist_eq R
    (inp.cap_four_of_nonneg hR) hS hSR z J hJS hJz

theorem inter_count
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (α : Nat) :
    ∀ᶠ k in atTop,
      ∀ xα : (X.obj (L.φ k)).M,
        seqCenter inp.decay inp.D P (L.φ k) α = some xα →
      ∀ J : Finset Nat,
        (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
        J.card <=
          inp.volume.multiplicity
            (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) := by
  exact NetLimitData.inter_count inp.decay inp.hD P L inp.realizes inp.pack
    inp.volume inp.dist_eq inp.cap_inter α

theorem exists_net_data
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    Nonempty (NetLimitData inp.decay inp.D P) :=
  exists_netLimitData inp.decay inp.hD P

theorem exists_stable_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      ∀ α β : Nat,
        (∀ᶠ k in atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k)) :=
  exists_stableNetData inp.decay inp.hD P

theorem exists_stable_net_with_intersection_bound
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      (∀ α β : Nat,
        (∀ᶠ k in atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D P (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.multiplicity
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) := by
  obtain ⟨L, hstable⟩ := inp.exists_stable_net P
  exact ⟨L, hstable, fun α => inp.inter_count P L α⟩

theorem exists_stable_net_with_intersection_bound_of_complete_connected
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ L : NetLimitData inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn),
      (∀ α β : Nat,
        (∀ᶠ k in atTop,
          BInter inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop,
          ¬ BInter inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
              (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
                L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.multiplicity
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) :=
  inp.exists_stable_net_with_intersection_bound (properMetricsOfCompleteConnected (I := I) hcomplete hconn)

theorem exists_stable_net_with_intersection_bound_subsequence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (f : Nat -> Nat) :
    ∃ L : NetLimitData (inp.subseq f).decay (inp.subseq f).D
        (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
          (X.connected_subseq hconn f)),
      (∀ α β : Nat,
        (∀ᶠ k in atTop,
          BInter (inp.subseq f).decay (inp.subseq f).D
            (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
              (X.connected_subseq hconn f))
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop,
          ¬ BInter (inp.subseq f).decay (inp.subseq f).D
            (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
              (X.connected_subseq hconn f))
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : ((X.subseq f).obj (L.φ k)).M,
            seqCenter (inp.subseq f).decay (inp.subseq f).D
              (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
                (X.connected_subseq hconn f))
              (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter (inp.subseq f).decay (inp.subseq f).D
                (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
                  (X.connected_subseq hconn f))
                L.lamInf α β (L.φ k)) →
            J.card <=
              (inp.subseq f).volume.multiplicity
                (50 * Real.exp
                  ((inp.subseq f).decay.C *
                    (20 * (inp.subseq f).decay.lambda (inp.subseq f).D 0)))) := by
  exact (inp.subseq f).exists_stable_net_with_intersection_bound_of_complete_connected (hcomplete.subseq f)
    (X.connected_subseq hconn f)

end MetricCompactnessInputs


end HCGCompactness
end DifferentialGeometry
