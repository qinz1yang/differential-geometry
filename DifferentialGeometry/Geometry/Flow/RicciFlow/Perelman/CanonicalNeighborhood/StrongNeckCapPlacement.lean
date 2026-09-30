import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckCompactPlacement
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOrderedSides

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation (axialZero)
open KappaSolutions

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [RiemannianBundle (fun q : M => TangentSpace I3 q)]
  [IsRiemannianManifold I3 M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {h : SmoothRiemannianMetric I3 M}
  {mark : SpatialNeckSphere} {centers : ℕ → M} {eps eta t : ℝ}

theorem exists_oriented_strongNeck_of_disjoint_escaping_neckWitnesses
    (strong : ∀ i, StrongNeckWitness S mark (centers i) t eps)
    (spatial : ∀ i, SpatialNeckWitness h mark (centers i) eta)
    (hsphere : ∀ i, (strong i).embedding '' spatialNeckCentralDomain eps = (spatial i).centralSphere)
    (hEnorm : IsMetricNorm h) (heta : eta ≤ spatialNeckControlEpsilon) (heps : eps < 1 / 11)
    (hsec : Geometry.HasPositiveSectionalCurvature h)
    {c : ℝ≥0 → M} (hc : Isometry c)
    (hcores : Pairwise fun i j => Disjoint (spatial i).core (spatial j).core)
    (hescape : Tendsto centers atTop (cocompact M))
    (psi : M ≃ₘ⟮I3, I3⟯ ThreeSpace) (p : M) (K : Set M) (hK : IsCompact K) :
    ∃ (i : ℕ) (nk : StrongNeck S eps (centers i) t),
      nk.map.source = spatialNeckBuffer eps ∧ nk.map.target = range (strong i).embedding ∧
      nk.center = mark ∧ (∀ z : spatialNeckBuffer eps, nk.map z.val = (strong i).embedding z) ∧
      nk.map '' (univ ×ˢ ({0} : Set ℝ)) = (spatial i).centralSphere ∧
      ∃ neck : StrongNeck S eps (centers i) t,
        (neck = nk ∨ neck = nk.axialReflection) ∧
        DifferentialGeometry.Topology.SphereSeparation.IsAxiallyOriented neck.bicollar (neck.bicollarSides psi) ∧
        insert p K ⊆ (neck.bicollarSides psi (axialZero (inv_pos.mpr neck.eps_pos))).compactSide := by
  choose spatial' _hchoice hcentral hcore _himage hside using fun i =>
    (spatial i).exists_ordered_compact_end_sides hsec
  let sides : ∀ i, SpatialNeckSideData (spatial' i) := fun i => Classical.choice (hside i)
  have hsphere' (i : ℕ) : (strong i).embedding '' spatialNeckCentralDomain eps = (spatial' i).centralSphere :=
    (hsphere i).trans (hcentral i).symm
  have hcores' : Pairwise fun i j => Disjoint (spatial' i).core (spatial' j).core := by
    intro i j hij
    rw [hcore i, hcore j]
    exact hcores hij
  obtain ⟨i, nk, hinside, hsrc, htgt, hcenter, hmap, hcentralNk⟩ :=
    exists_strongNeck_compactSide_contains_compact_of_disjoint_escaping_family spatial' sides strong
      hsphere' hEnorm heta heps hsec.toNonnegative hc hcores' hescape psi (insert p K) (hK.insert p)
  obtain ⟨neck, hneck, ho⟩ := nk.exists_axially_oriented psi
  have hside : (neck.bicollarSides psi (axialZero (inv_pos.mpr neck.eps_pos))).compactSide =
      (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).compactSide := by
    rcases hneck with rfl | rfl
    · rfl
    · exact (nk.axialReflection_bicollar_zero_sides psi).1
  exact ⟨i, nk, hsrc, htgt, hcenter, hmap, hcentralNk.trans (hcentral i), neck, hneck, ho,
    hside.symm ▸ hinside⟩

theorem exists_localCap_of_disjoint_escaping_neckWitnesses
    (strong : ∀ i, StrongNeckWitness S mark (centers i) t eps)
    (spatial : ∀ i, SpatialNeckWitness h mark (centers i) eta)
    (hsphere : ∀ i, (strong i).embedding '' spatialNeckCentralDomain eps = (spatial i).centralSphere)
    (hEnorm : IsMetricNorm h) (heta : eta ≤ spatialNeckControlEpsilon) (heps : eps < 1 / 11)
    (hsec : Geometry.HasPositiveSectionalCurvature h)
    {c : ℝ≥0 → M} (hc : Isometry c)
    (hcores : Pairwise fun i j => Disjoint (spatial i).core (spatial j).core)
    (hescape : Tendsto centers atTop (cocompact M))
    (psi : M ≃ₘ⟮I3, I3⟯ ThreeSpace) (p : M) (K : Set M) (hK : IsCompact K) :
    ∃ (i : ℕ) (nk : StrongNeck S eps (centers i) t),
      nk.map.source = spatialNeckBuffer eps ∧ nk.map.target = range (strong i).embedding ∧
      nk.center = mark ∧ (∀ z : spatialNeckBuffer eps, nk.map z.val = (strong i).embedding z) ∧
      nk.map '' (univ ×ˢ ({0} : Set ℝ)) = (spatial i).centralSphere ∧
      ∃ (neck : StrongNeck S eps (centers i) t) (U : Set M) (cap : LocalCap S eps p t U),
        (neck = nk ∨ neck = nk.axialReflection) ∧
        K ⊆ interior cap.core.carrier ∧
        cap.core.carrier = closure (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∧
        U = cap.core.carrier ∪ neck.map '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
        cap.tube = neck.map '' (univ ×ˢ Icc (0 : ℝ) 1) ∧ cap.tubeMap = neck.map ∧
        ∃ j : Fin cap.chain.count, cap.chain.centers j = centers i ∧ HEq (cap.chain.necks j) neck ∧
          cap.chain.lo j = 0 ∧ cap.chain.hi j = 1 ∧ centers i ∈ cap.tube := by
  obtain ⟨i, nk, hsrc, htgt, hcenter, hmap, hcentralNk, _neck, _hneck, _ho, hinside'⟩ :=
    exists_oriented_strongNeck_of_disjoint_escaping_neckWitnesses strong spatial hsphere
      hEnorm heta heps hsec hc hcores hescape psi p K hK
  have hside : (_neck.bicollarSides psi (axialZero (inv_pos.mpr _neck.eps_pos))).compactSide =
      (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).compactSide := by
    rcases _hneck with rfl | rfl
    · rfl
    · exact (nk.axialReflection_bicollar_zero_sides psi).1
  have hinside : insert p K ⊆ (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).compactSide :=
    hside ▸ hinside'
  have hp : p ∈ (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).compactSide := hinside (mem_insert p K)
  obtain ⟨neck, U, cap, hneck, hU, hcapcore, htube, hcapmap, hchain⟩ := nk.exists_localCap_of_mem_compactSide psi p hp
  refine ⟨i, nk, hsrc, htgt, hcenter, hmap, hcentralNk, neck, U, cap,
    hneck, ?_, hcapcore, ?_, htube, hcapmap, hchain⟩
  · rw [hcapcore]
    intro y hy
    exact (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).isOpen_compactSide.subset_interior_closure
      (hinside (mem_insert_of_mem p hy))
  · rw [hcapcore]
    exact hU


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
