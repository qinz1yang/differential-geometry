import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.ContinuousMap.Basic
import DifferentialGeometry.Topology.LoopSpace.SpanningDisk
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section

open Set Metric
open scoped Topology

theorem UniformContinuousOn.exists_continuous_extension_of_boundary_approach
    {X Y : Type*} [PseudoMetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    {s t : Set X} (hst : s ⊆ t) (hts : t ⊆ closure s)
    {v η : X → Y} (hv : UniformContinuousOn v s)
    (happroach : ∀ p ∈ t, p ∉ s → ∀ ε > 0, ∀ R > 0,
      ∃ z ∈ s, dist z p < R ∧ dist (v z) (η p) < ε) :
    ∃ q : C(t, Y), UniformContinuous q ∧
      (∀ z : s, q (Set.inclusion hst z) = v z) ∧
      (∀ (p : X) (hp : p ∈ t), p ∉ s → q ⟨p, hp⟩ = η p) ∧
      ∀ K : Set Y, IsClosed K → MapsTo v s K → range q ⊆ K := by
  let i : s → t := Set.inclusion hst
  have hi : Isometry i := fun _ _ => rfl
  have hdense : DenseRange i := (denseRange_inclusion_iff hst).mpr hts
  have hv' : UniformContinuous (fun z : s => v z) := hv.restrict
  let q₀ := (hi.isUniformInducing.isDenseInducing hdense).extend (fun z : s => v z)
  have hq₀ : UniformContinuous q₀ :=
    uniformContinuous_uniformly_extend hi.isUniformInducing hdense hv'
  have heq (z : s) : q₀ (i z) = v z :=
    uniformly_extend_of_ind hi.isUniformInducing hdense hv' z
  let q : C(t, Y) := ⟨q₀, hq₀.continuous⟩
  refine ⟨q, hq₀, heq, ?_, ?_⟩
  · intro p hp hps
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δ, hδ, hqδ⟩ := (Metric.uniformContinuous_iff.mp hq₀) (ε / 2) (half_pos hε)
    obtain ⟨z, hz, hzp, hvz⟩ := happroach p hp hps (ε / 2) (half_pos hε) δ hδ
    have hdist : dist (q₀ (⟨p, hp⟩ : t)) (q₀ (i ⟨z, hz⟩)) < ε / 2 :=
      hqδ (by change dist p z < δ; rwa [dist_comm])
    rw [heq] at hdist
    change dist (q ⟨p, hp⟩) (v z) < ε / 2 at hdist
    exact (dist_triangle (q ⟨p, hp⟩) (v z) (η p)).trans
      ((add_lt_add hdist hvz).trans_eq (add_halves ε)).le
  · intro K hK hvK y hy
    obtain ⟨z, rfl⟩ := hy
    refine hdense.induction_on (p := fun x : t => q x ∈ K) z
      (hK.preimage q.continuous) ?_
    intro x
    change q₀ (i x) ∈ K
    rw [heq]
    exact hvK x.property

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

theorem exists_continuous_disk_extension_of_uniformContinuousOn_of_boundary_approach
    {v η : ℂ → F} (hv : UniformContinuousOn v (ball (0 : ℂ) 1))
    (happroach : ∀ p ∈ sphere (0 : ℂ) 1, ∀ ε > 0, ∀ R > 0,
      ∃ z ∈ ball (0 : ℂ) 1, dist z p < R ∧ ‖v z - η p‖ < ε) :
    ∃ q : C(closedDisk, F), UniformContinuous q ∧
      (∀ z (hz : z ∈ ball (0 : ℂ) 1), q ⟨z, ball_subset_closedBall hz⟩ = v z) ∧
      (∀ p (hp : p ∈ sphere (0 : ℂ) 1), q ⟨p, sphere_subset_closedBall hp⟩ = η p) ∧
      ∀ K : Set F, IsClosed K → MapsTo v (ball (0 : ℂ) 1) K → range q ⊆ K := by
  have hdense : closedBall (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
  have hboundary : ∀ p ∈ closedBall (0 : ℂ) 1, p ∉ ball (0 : ℂ) 1 →
      ∀ ε > 0, ∀ R > 0, ∃ z ∈ ball (0 : ℂ) 1,
        dist z p < R ∧ dist (v z) (η p) < ε := by
    intro p hp hpn ε hε R hR
    have hps : p ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere]
      exact le_antisymm hp (not_lt.mp hpn)
    simpa only [dist_eq_norm] using happroach p hps ε hε R hR
  obtain ⟨q, hq, hi, hb, hK⟩ :=
    hv.exists_continuous_extension_of_boundary_approach ball_subset_closedBall hdense hboundary
  refine ⟨q, hq, (fun z hz => hi ⟨z, hz⟩), ?_, hK⟩
  intro p hp
  apply hb p (sphere_subset_closedBall hp)
  intro hpin
  have heq : dist p (0 : ℂ) = 1 := hp
  exact (ne_of_lt hpin) heq

end DifferentialGeometry.Topology

end
