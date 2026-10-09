import DifferentialGeometry.Geometry.Metric.Isometry.Topology
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.UniformSpace.Ascoli

namespace ContinuousMap

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem isCompact_setOf_isometry_surjective (o : X) {K : Set X} (hK : IsCompact K) :
    IsCompact {f : C(X, X) | Isometry f ∧ Function.Surjective f ∧ f o ∈ K} := by
  let S : Set ((X → X) × (X → X)) := {p |
    (∀ x y, dist (p.1 x) (p.1 y) = dist x y) ∧
    (∀ x y, dist (p.1 x) y = dist x (p.2 y)) ∧ p.1 o ∈ K}
  have hclosed : IsClosed S := by
    simp only [S, Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_iInter fun x => isClosed_iInter fun y => ?_).inter
      ((isClosed_iInter fun x => isClosed_iInter fun y => ?_).inter ?_)
    · exact isClosed_eq
        (((continuous_apply x).comp continuous_fst).dist
          ((continuous_apply y).comp continuous_fst)) continuous_const
    · exact isClosed_eq (((continuous_apply x).comp continuous_fst).dist continuous_const)
        (continuous_const.dist ((continuous_apply y).comp continuous_snd))
    · exact hK.isClosed.preimage ((continuous_apply o).comp continuous_fst)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall o
  let B : Set (X → X) := {f | ∀ x, f x ∈ Metric.closedBall o (dist x o + R)}
  have hB : IsCompact B := isCompact_pi_infinite fun x => isCompact_closedBall o (dist x o + R)
  have hS : IsCompact S := (hB.prod hB).of_isClosed_subset hclosed (by
    intro p hp
    constructor
    · intro x
      change dist (p.1 x) o ≤ dist x o + R
      calc
        dist (p.1 x) o ≤ dist (p.1 x) (p.1 o) + dist (p.1 o) o := dist_triangle _ _ _
        _ = dist x o + dist (p.1 o) o := by rw [hp.1]
        _ ≤ dist x o + R := add_le_add le_rfl (hR hp.2.2)
    · intro x
      change dist (p.2 x) o ≤ dist x o + R
      calc
        dist (p.2 x) o = dist o (p.2 x) := dist_comm _ _
        _ = dist (p.1 o) x := (hp.2.1 o x).symm
        _ ≤ dist (p.1 o) o + dist o x := dist_triangle _ _ _
        _ ≤ R + dist o x := add_le_add (hR hp.2.2) le_rfl
        _ = dist x o + R := by rw [dist_comm o x, add_comm])
  have himage : ContinuousMap.toFun ''
      {f : C(X, X) | Isometry f ∧ Function.Surjective f ∧ f o ∈ K} = Prod.fst '' S := by
    ext f
    constructor
    · rintro ⟨f, ⟨hi, hs, hk⟩, rfl⟩
      let e : X ≃ᵢ X :=
        { toEquiv := Equiv.ofBijective f ⟨hi.injective, hs⟩
          isometry_toFun := hi }
      refine ⟨(f, e.symm), ⟨hi.dist_eq, ?_, hk⟩, rfl⟩
      intro x y
      change dist (e x) y = dist x (e.symm y)
      rw [← e.apply_symm_apply y, e.dist_eq, e.symm_apply_apply]
    · rintro ⟨p, hp, rfl⟩
      have hi : Isometry p.1 := Isometry.of_dist_eq hp.1
      refine ⟨⟨p.1, hi.continuous⟩, ⟨hi, ?_, hp.2.2⟩, rfl⟩
      intro y
      refine ⟨p.2 y, ?_⟩
      change p.1 (p.2 y) = y
      exact dist_eq_zero.mp (by simpa only [dist_self] using hp.2.1 (p.2 y) y)
  apply ArzelaAscoli.isCompact_of_equicontinuous _
  · rw [himage]
    exact hS.image continuous_fst
  · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => r) Filter.tendsto_id
    intro x y f
    exact (f.property.1.dist_eq x y).le

end ContinuousMap

namespace IsometryEquiv

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem isCompact_setOf_apply_mem (o : X) {K : Set X} (hK : IsCompact K) :
    IsCompact {f : X ≃ᵢ X | f o ∈ K} := by
  have hemb : Topology.IsEmbedding (fun f : X ≃ᵢ X => (f : C(X, X))) :=
    isEmbedding_toContinuousMap
  apply hemb.isCompact_iff.mpr
  have himage : (fun f : X ≃ᵢ X => (f : C(X, X))) '' {f | f o ∈ K} =
      {f : C(X, X) | Isometry f ∧ Function.Surjective f ∧ f o ∈ K} := by
    ext f
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.isometry, e.surjective, he⟩
    · rintro ⟨hi, hs, hk⟩
      let e : X ≃ᵢ X :=
        { toEquiv := Equiv.ofBijective f ⟨hi.injective, hs⟩
          isometry_toFun := hi }
      exact ⟨e, hk, rfl⟩
  rw [himage]
  exact ContinuousMap.isCompact_setOf_isometry_surjective o hK

theorem isCompact_setOf_dist_apply_le (o : X) (r : ℝ) :
    IsCompact {f : X ≃ᵢ X | dist (f o) o ≤ r} :=
  isCompact_setOf_apply_mem o (isCompact_closedBall o r)

end IsometryEquiv
