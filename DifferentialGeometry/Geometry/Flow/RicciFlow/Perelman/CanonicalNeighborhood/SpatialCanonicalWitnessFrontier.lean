import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessUniverseTransport

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps C1 C2 : ℝ} {x : M} {U : Set M}

private theorem preconnectedSpace_sphereTwo : PreconnectedSpace (Sphere 2) :=
  Subtype.preconnectedSpace (isConnected_sphere (by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by norm_num : (1 : ℕ) < 2 + 1)) 0 zero_le_one).isPreconnected

omit [SigmaCompactSpace M] in
theorem SpatialLocalNeck.not_isPreconnected_frontier (n : SpatialLocalNeck g eps x U) :
    ¬ IsPreconnected (frontier U) := by
  have hi : (11 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) n.neck.eps_pos).mpr (by linarith [n.neck.eps_small])
  have hsrc : ∀ a : ℝ, |a| ≤ 10 → (univ ×ˢ {a} : Set Cylinder) ⊆ n.neck.map.source := by
    intro a ha z hz
    refine n.neck.domain ⟨trivial, ?_, ?_⟩
    · rw [hz.2]
      linarith [(abs_le.mp ha).1]
    · rw [hz.2]
      linarith [(abs_le.mp ha).2]
  have hcont := n.neck.map.contMDiffOn_toFun.continuousOn
  have hcpt : ∀ a : ℝ, |a| ≤ 10 → IsCompact (n.neck.map '' (univ ×ˢ {a})) := fun a ha =>
    (isCompact_univ.prod isCompact_singleton).image_of_continuousOn (hcont.mono (hsrc a ha))
  have hm : |(-10 : ℝ)| ≤ 10 := by norm_num
  have hp : |(10 : ℝ)| ≤ 10 := by norm_num
  set A := n.neck.map '' (univ ×ˢ {(-10 : ℝ)}) with hA
  set B := n.neck.map '' (univ ×ˢ {(10 : ℝ)}) with hB
  have hfr : frontier U = A ∪ B := by
    rw [n.boundary_eq, hA, hB, ← image_union, ← prod_union]
    rfl
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩
    have heq := n.neck.map.injOn (hsrc 10 hp hw) (hsrc (-10) hm hz) hzw
    have h2 := congrArg Prod.snd heq
    rw [hw.2, hz.2] at h2
    norm_num at h2
  have hne : ∀ a : ℝ, (n.neck.map '' (univ ×ˢ {a})).Nonempty := fun a =>
    ⟨_, ⟨(n.neck.center, a), ⟨trivial, rfl⟩, rfl⟩⟩
  intro hconn
  rw [hfr] at hconn
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn A B (hcpt _ hm).isClosed
      (hcpt _ hp).isClosed subset_rfl (by rw [hdisj.inter_eq, inter_empty]) with h | h
  · obtain ⟨b, hb⟩ := hne 10
    exact hdisj.le_bot ⟨h (Or.inr hb), hb⟩
  · obtain ⟨a, ha⟩ := hne (-10)
    exact hdisj.le_bot ⟨ha, h (Or.inl ha)⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem SpatialLocalCap.isPreconnected_frontier (c : SpatialLocalCap g eps x U) :
    IsPreconnected (frontier U) := by
  have := preconnectedSpace_sphereTwo
  rw [← c.outer_boundary]
  refine (isPreconnected_univ.prod isPreconnected_singleton).image _ ?_
  exact c.tubeMap.contMDiffOn_toFun.continuousOn.mono fun z hz =>
    c.tube_domain ⟨hz.1, by rw [hz.2]; exact ⟨zero_le_one, le_rfl⟩⟩

theorem SpatialCanonicalWitness.alternative_ne_neck_of_isPreconnected_frontier
    (W : SpatialCanonicalWitness g eps C1 C2 x) (h : IsPreconnected (frontier W.domain.carrier))
    (n : SpatialLocalNeck g eps x W.domain.carrier) : W.alternative ≠ .neck n :=
  fun _ => n.not_isPreconnected_frontier h

theorem SpatialCanonicalWitness.isPreconnected_frontier_of_alternative_eq_cap
    (W : SpatialCanonicalWitness g eps C1 C2 x) {c : SpatialLocalCap g eps x W.domain.carrier}
    {d : ∀ y ∈ c.tube, 10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y}
    (_h : W.alternative = .cap c d) : IsPreconnected (frontier W.domain.carrier) :=
  c.isPreconnected_frontier

theorem SpatialCanonicalWitness.domain_scaleMetric (W : SpatialCanonicalWitness g eps C1 C2 x)
    (c : ℝ) (hc : 0 < c) : (W.scaleMetric c hc).domain = W.domain :=
  rfl

theorem SpatialCanonicalWitness.domain_enlargeConstants (W : SpatialCanonicalWitness g eps C1 C2 x)
    {C1' C2' : ℝ} (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') : (W.enlargeConstants h1 h2).domain = W.domain :=
  rfl

section Pushforward

universe v

attribute [local instance] DifferentialGeometry.Topology.uliftChartedSpace

variable {P : Type (max u v)} [TopologicalSpace P] [ChartedSpace ThreeSpace P]
  [IsManifold I3 ∞ P] [T2Space P] [SigmaCompactSpace P] {gP : SmoothRiemannianMetric I3 P}
  {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

theorem SpatialCanonicalWitness.pushforwardOfInjectiveULift_domain_carrier {f : N → P}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Function.Injective f) {z : N}
    (W : SpatialCanonicalWitness (localPullMetric gP f hf) eps C1 C2 z) {R : ℝ}
    (hR : 2 * W.radius < R)
    (hcpt : IsCompact (riemannianClosedBallOf (localPullMetric gP f hf) z R)) :
    (W.pushforwardOfInjectiveULift hf hinj hR hcpt).domain.carrier = f '' W.domain.carrier := by
  have key : ∀ {a b : P} (h : a = b) (W' : SpatialCanonicalWitness gP eps C1 C2 a),
      (h ▸ W').domain.carrier = W'.domain.carrier := by
    intro a b h W'
    subst h
    rfl
  unfold SpatialCanonicalWitness.pushforwardOfInjectiveULift
  rw [key]
  exact congrArg (fun F : N → P => F '' W.domain.carrier)
    (Classical.choose_spec
      (p := fun e : PartialDiffeomorph I3 I3 N P ∞ => e.source = univ ∧ (e : N → P) = f) _).2

omit [IsManifold I3 ∞ P] [SigmaCompactSpace P] [IsManifold I3 ∞ N] [SigmaCompactSpace N] in
theorem isPreconnected_frontier_image_of_injective {f : N → P}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Function.Injective f) {D : Set N}
    (hD : IsCompact D) (h : IsPreconnected (frontier D)) : IsPreconnected (frontier (f '' D)) := by
  have he : Topology.IsOpenEmbedding f :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj
      hf.isOpenMap
  have hc : IsClosed (f '' D) := (hD.image he.continuous).isClosed
  rcases isEmpty_or_nonempty N with hN | hN
  · rw [Set.eq_empty_of_isEmpty D, image_empty, frontier_empty]
    exact isPreconnected_empty
  have himg := (he.toOpenPartialHomeomorph f).image_frontier_of_subset_source (s := D)
    (by simp) hD.isClosed (by simpa using hc)
  simp only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply] at himg
  rw [← himg]
  exact h.image _ he.continuous.continuousOn

theorem SpatialCanonicalWitness.isPreconnected_frontier_pushforwardOfInjectiveULift
    {f : N → P} (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Function.Injective f) {z : N}
    (W : SpatialCanonicalWitness (localPullMetric gP f hf) eps C1 C2 z) {R : ℝ}
    (hR : 2 * W.radius < R)
    (hcpt : IsCompact (riemannianClosedBallOf (localPullMetric gP f hf) z R))
    (h : IsPreconnected (frontier W.domain.carrier)) :
    IsPreconnected (frontier (W.pushforwardOfInjectiveULift hf hinj hR hcpt).domain.carrier) := by
  rw [W.pushforwardOfInjectiveULift_domain_carrier hf hinj hR hcpt]
  exact isPreconnected_frontier_image_of_injective hf hinj W.domain.compact h

end Pushforward

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
