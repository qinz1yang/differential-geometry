import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Metric.Pullback.LocalRestriction

/-!
# Compatible common flows from a traced region (chapters 9–10, adapter A12, errata form)

The second external review (task 37, §7; dispositions D7) generalises A12 to per-radius depths
`τ k` and bounds `K k`: the common flow `S k` lives on `[a k, t]`, `a k = t - τ k`, and two of
them agree on `U k ⊓ U l` for `v ∈ [max (a k) (a l), t]`.

The reason is not that the terminal metrics agree.  Two families of stage maps with the same
endpoint and the same `RegularCrossing` data are equal on every common stage, by
`BackwardPointTrace.point_unique`; so the two flows are local pull-backs of the same stage metric
by maps that agree on the overlap.

* `ObservedHistory.backwardMaps_comp_inclusion_eq`: the public copy of the private
  `comp_inclusion_eq_of_backward_maps` (`ST/TracedRegionAncientLimit.lean`; two start times).
* `ObservedHistory.restrictOpenOfSubset_eq_of_backward_maps`: the two-flow lemma.  It takes two
  metric families, each the local pull-back of the stage metrics by its own backward maps, and
  needs no family; a consumer with `∀ k, eventually n` inputs chooses the flows per `(k, n)` and
  applies it for fixed `k, ℓ` on the intersection of the two eventual sets.
* `FILL910.A12_compatible_common_flows`: the family version (errata form), for one history.
* `FILL910.A12_eventually_compatible_common_flows`: the family version for a sequence of histories
  with the quantifier order of the review kept: inputs `∀ k, ∀ᶠ n`, flows chosen separately for
  every `(k, n)`, compatibility `∀ k l, ∀ᶠ n` on the intersection of the two eventual sets.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

open DifferentialGeometry.Geometry.Curvature

/-- Two families of backward stage maps with the same endpoint and `RegularCrossing` data agree
on the overlap of their domains, at every common stage (two start times `a, b`). -/
theorem backwardMaps_comp_inclusion_eq (H : ObservedHistory.{u})
    {a b t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t) (hbt : b ≤ t)
    {U V : Opens (H.stageAt t).Carrier}
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier)
    (hcf : ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t), ∀ x : U,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlf : ∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val)
    (g : (j : H.StageInterval (H.activeStage b) (H.activeStage t)) → V → (H.stage j.val).Carrier)
    (hcg : ∀ (i : Fin H.eventCount) (hi : H.activeStage b ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t), ∀ x : V,
      (H.event i).RegularCrossing (g ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (g ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlg : ∀ x : V, g ⟨H.activeStage t, H.activeStage_mono hbt, le_rfl⟩ x = x.val)
    (j : Fin (H.eventCount + 1)) (hja : H.activeStage a ≤ j) (hjb : H.activeStage b ≤ j)
    (hjt : j ≤ H.activeStage t) :
    f ⟨j, hja, hjt⟩ ∘ Opens.inclusion (inf_le_left : U ⊓ V ≤ U) =
      g ⟨j, hjb, hjt⟩ ∘ Opens.inclusion (inf_le_right : U ⊓ V ≤ V) := by
  funext z
  let A : BackwardPointTrace H j (H.activeStage t) hjt (z : (H.stageAt t).Carrier) :=
    { point := fun i hi hl => f ⟨i, hja.trans hi, hl⟩ (Opens.inclusion inf_le_left z)
      endpoint_eq := hlf _
      crossing := fun i hi hl => hcf i (hja.trans hi) hl _ }
  let B : BackwardPointTrace H j (H.activeStage t) hjt (z : (H.stageAt t).Carrier) :=
    { point := fun i hi hl => g ⟨i, hjb.trans hi, hl⟩ (Opens.inclusion inf_le_right z)
      endpoint_eq := hlg _
      crossing := fun i hi hl => hcg i (hjb.trans hi) hl _ }
  exact A.point_unique B j le_rfl hjt

/-- The two-flow lemma (D7).  Two metric families on `U` and `V` that are, on `[a, t]` and
`[b, t]` respectively, the local pull-backs of the stage metrics by backward stage maps with the
same endpoint and `RegularCrossing` data, agree on `U ⊓ V` at every `v ∈ [max a b, t]`. -/
theorem restrictOpenOfSubset_eq_of_backward_maps (H : ObservedHistory.{u})
    {a b t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t) (hbt : b ≤ t)
    {U V : Opens (H.stageAt t).Carrier}
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcf : ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t), ∀ x : U,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlf : ∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val)
    (g : (j : H.StageInterval (H.activeStage b) (H.activeStage t)) → V → (H.stage j.val).Carrier)
    (hg : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (g j))
    (hcg : ∀ (i : Fin H.eventCount) (hi : H.activeStage b ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t), ∀ x : V,
      (H.event i).RegularCrossing (g ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (g ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlg : ∀ x : V, g ⟨H.activeStage t, H.activeStage_mono hbt, le_rfl⟩ x = x.val)
    (S : ℝ → SmoothRiemannianMetric ThreeModel U) (T : ℝ → SmoothRiemannianMetric ThreeModel V)
    (hS : ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
        S v = localPullMetric (H.stageMetric j.val v) (f j) (hf j))
    (hT : ∀ j : H.StageInterval (H.activeStage b) (H.activeStage t),
      ∀ v ∈ Icc b.val t.val, v ∈ H.stageDomain j.val →
        T v = localPullMetric (H.stageMetric j.val v) (g j) (hg j)) :
    ∀ v ∈ Icc (max a.val b.val) t.val,
      (S v).restrictOpenOfSubset (inf_le_left : U ⊓ V ≤ U) =
        (T v).restrictOpenOfSubset (inf_le_right : U ⊓ V ≤ V) := by
  intro v hv
  have hav : a.val ≤ v := (le_max_left _ _).trans hv.1
  have hbv : b.val ≤ v := (le_max_right _ _).trans hv.1
  let v' : Icc (0 : ℝ) H.horizon := ⟨v, a.property.1.trans hav, hv.2.trans t.property.2⟩
  have hja : H.activeStage a ≤ H.activeStage v' := H.activeStage_mono (show a ≤ v' from hav)
  have hjb : H.activeStage b ≤ H.activeStage v' := H.activeStage_mono (show b ≤ v' from hbv)
  have hjt : H.activeStage v' ≤ H.activeStage t := H.activeStage_mono (show v' ≤ t from hv.2)
  have hdom : v ∈ H.stageDomain (H.activeStage v') := H.activeStage_mem v'
  rw [hS ⟨_, hja, hjt⟩ v ⟨hav, hv.2⟩ hdom, hT ⟨_, hjb, hjt⟩ v ⟨hbv, hv.2⟩ hdom]
  exact localPullMetric_restrictOpenOfSubset_eq_of_comp_eq _ _ _ _ _ _ _
    (H.backwardMaps_comp_inclusion_eq hat hbt f hcf hlf g hcg hlg _ hja hjb hjt)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle

/-- A12 (I12 overlap compatibility, M; errata form after the second review): per-radius depths
`τ k` and bounds `K k`.  For each `k` the common flow `S k` on `U k = B(p, ρ k)` lives on
`[a k, t]`, `a k = t - τ k`; it is the current-stage metric where defined, it has `|Rm| ≤ K k`, and
two of them agree on `U k ⊓ U l` for `v ∈ [max (a k) (a l), t]`.  This is the `hcompat` input of
`exists_pointed_local_flow_limits_of_local_solutions` before rescaling. -/
theorem A12_compatible_common_flows (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (ρ τ K : ℕ → ℝ)
    (h : ∀ k, H.isTracedRegion t p (ρ k) (τ k) (K k)) :
    ∃ (a : ℕ → Icc (0 : ℝ) H.horizon) (hat : ∀ k, a k ≤ t), (∀ k, (a k).val = t.val - τ k) ∧
      ∃ (U : ℕ → Opens (H.stageAt t).Carrier)
        (S : ∀ k, SolutionOn (I := ThreeModel) (M := U k)
          (RealTimeInterval.closed (a k).val t.val (hat k))),
        (∀ k, (U k : Set (H.stageAt t).Carrier) =
          riemannianBallOf (H.stageMetric (H.activeStage t) t) p (ρ k)) ∧
        (∀ k, IsSolutionOn (S k)) ∧
        (∀ k, ∀ v ∈ Icc (a k).val t.val, v ∈ H.stageDomain (H.activeStage t) →
          (S k).base.metric v = (H.stageMetric (H.activeStage t) v).restrictOpen (U k)) ∧
        (∀ k, ∀ v ∈ Icc (a k).val t.val, ∀ x : U k,
          normSq0S ((S k).base.metric v) x 4 ((S k).base.rm04 v x) ≤ K k ^ 2) ∧
        ∀ k l, ∀ v ∈ Icc (max (a k).val (a l).val) t.val,
          ((S k).base.metric v).restrictOpenOfSubset (inf_le_left : U k ⊓ U l ≤ U k) =
            ((S l).base.metric v).restrictOpenOfSubset (inf_le_right : U k ⊓ U l ≤ U l) := by
  have hflows := fun k =>
    H.exists_common_flow_with_compact_neighborhood_of_isTracedRegion t p (h k)
  choose a hat ha U hU f hf _ hcross hlast S hS hmetric hRm hcurrent _ using hflows
  refine ⟨a, hat, ha, U, S, hU, hS, hcurrent, hRm, ?_⟩
  intro k l v hv
  exact H.restrictOpenOfSubset_eq_of_backward_maps (hat k) (hat l) (f k) (hf k) (hcross k)
    (hlast k) (f l) (hf l) (hcross l) (hlast l) _ _ (hmetric k) (hmetric l) v hv

/-- A12 for a sequence of histories, keeping the quantifier order `∀ k, ∀ᶠ n` (review §7, D7).
The common flow of the `k`-th window is chosen separately for every `n` (a placeholder flow on the
trivial window `[t n, t n]` where the traced region is not available); for fixed `k, l` the two
flows agree on the overlap for all large `n`, on `[max (a k n) (a l n), t n]`. -/
theorem A12_eventually_compatible_common_flows (H : ℕ → ObservedHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (H n).horizon) (p : ∀ n, ((H n).stageAt (t n)).Carrier)
    (ρ τ K : ℕ → ℝ)
    (h : ∀ k, ∀ᶠ n in atTop, (H n).isTracedRegion (t n) (p n) (ρ k) (τ k) (K k)) :
    ∃ (a : ∀ (_ : ℕ) (n : ℕ), Icc (0 : ℝ) (H n).horizon) (hat : ∀ k n, a k n ≤ t n)
      (U : ∀ (_ : ℕ) (n : ℕ), Opens ((H n).stageAt (t n)).Carrier)
      (S : ∀ k n, SolutionOn (I := ThreeModel) (M := U k n)
        (RealTimeInterval.closed (a k n).val (t n).val (hat k n))),
      (∀ k, ∀ᶠ n in atTop, (a k n).val = (t n).val - τ k ∧
        (U k n : Set ((H n).stageAt (t n)).Carrier) =
          riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (p n) (ρ k) ∧
        IsSolutionOn (S k n) ∧
        (∀ v ∈ Icc (a k n).val (t n).val, v ∈ (H n).stageDomain ((H n).activeStage (t n)) →
          (S k n).base.metric v =
            ((H n).stageMetric ((H n).activeStage (t n)) v).restrictOpen (U k n)) ∧
        (∀ v ∈ Icc (a k n).val (t n).val, ∀ x : U k n,
          normSq0S ((S k n).base.metric v) x 4 ((S k n).base.rm04 v x) ≤ K k ^ 2)) ∧
      ∀ k l, ∀ᶠ n in atTop, ∀ v ∈ Icc (max (a k n).val (a l n).val) (t n).val,
        ((S k n).base.metric v).restrictOpenOfSubset (inf_le_left : U k n ⊓ U l n ≤ U k n) =
          ((S l n).base.metric v).restrictOpenOfSubset
            (inf_le_right : U k n ⊓ U l n ≤ U l n) := by
  classical
  have key : ∀ (k n : ℕ), ∃ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n)
      (U : Opens ((H n).stageAt (t n)).Carrier)
      (S : SolutionOn (I := ThreeModel) (M := U)
        (RealTimeInterval.closed a.val (t n).val hat)),
      (H n).isTracedRegion (t n) (p n) (ρ k) (τ k) (K k) →
        a.val = (t n).val - τ k ∧
        (U : Set ((H n).stageAt (t n)).Carrier) =
          riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (p n) (ρ k) ∧
        IsSolutionOn S ∧
        (∀ v ∈ Icc a.val (t n).val, v ∈ (H n).stageDomain ((H n).activeStage (t n)) →
          S.base.metric v = ((H n).stageMetric ((H n).activeStage (t n)) v).restrictOpen U) ∧
        (∀ v ∈ Icc a.val (t n).val, ∀ x : U,
          normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K k ^ 2) ∧
        ∃ f : (j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n))) → U →
            ((H n).stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ (i : Fin (H n).eventCount) (hi : (H n).activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ (H n).activeStage (t n)), ∀ x : U,
              ((H n).event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨(H n).activeStage (t n), (H n).activeStage_mono hat, le_rfl⟩ x =
              x.val) ∧
            (∀ j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)),
              ∀ v ∈ Icc a.val (t n).val, v ∈ (H n).stageDomain j.val →
                S.base.metric v = localPullMetric ((H n).stageMetric j.val v) (f j) (hf j)) := by
    intro k n
    by_cases hP : (H n).isTracedRegion (t n) (p n) (ρ k) (τ k) (K k)
    · obtain ⟨a, hat, ha, U, hU, f, hf, -, hcross, hlast, S, hS, hmetric, hRm, hcurrent, -⟩ :=
        (H n).exists_common_flow_with_compact_neighborhood_of_isTracedRegion (t n) (p n) hP
      exact ⟨a, hat, U, S, fun _ => ⟨ha, hU, hS, hcurrent, hRm, f, hf, hcross, hlast, hmetric⟩⟩
    · exact ⟨t n, le_rfl, ⊤,
        { base := { metric := fun _ =>
            ((H n).stageMetric ((H n).activeStage (t n)) (t n)).restrictOpen ⊤ } },
        fun hP' => absurd hP' hP⟩
  choose a hat U S hprop using key
  refine ⟨a, hat, U, S, fun k => ?_, fun k l => ?_⟩
  · filter_upwards [h k] with n hn
    obtain ⟨ha, hU, hS, hcurrent, hRm, -⟩ := hprop k n hn
    exact ⟨ha, hU, hS, hcurrent, hRm⟩
  · filter_upwards [h k, h l] with n hk hl
    obtain ⟨-, -, -, -, -, f, hf, hcf, hlf, hmf⟩ := hprop k n hk
    obtain ⟨-, -, -, -, -, g, hg, hcg, hlg, hmg⟩ := hprop l n hl
    exact (H n).restrictOpenOfSubset_eq_of_backward_maps (hat k n) (hat l n) f hf hcf hlf
      g hg hcg hlg _ _ hmf hmg

end FILL910
