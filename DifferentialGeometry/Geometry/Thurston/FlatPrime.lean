import DifferentialGeometry.Topology.Covering.SphericalBall
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.PrimeOfIrreducible
import DifferentialGeometry.Geometry.Thurston.ConstantCurvatureAtlas
import DifferentialGeometry.Geometry.Exponential.RadialFlat

/-!
# Closed flat `3`-manifolds are prime

Chapter 7, survey packet P7 (`docs/geometrization/handoffs/20261003-survey-chapter7.md`, §6).

* `sphereBoundsBall_euclidean`: every smoothly embedded `2`-sphere in `ℝ³` bounds a ball
  (smooth Schoenflies, `smooth_schoenflies_three`).
* `sphereBoundsBall_of_isCoveringMap`: if `p : ℝ³ → M` is a surjective covering map and a local
  diffeomorphism, every smoothly embedded `2`-sphere in `M` bounds a ball (Hatcher, Prop. 1.6).
  The sphere has pairwise disjoint lifts (`exists_disjoint_smooth_sphere_lifts`). Fibres are
  discrete, so only finitely many lifts start in the closed compact side of a fixed lift; one of
  them is innermost (`exists_sphereSides_compactSide_disjoint_iUnion`), and its compact side
  meets no lift at all. The covering map is injective on the closure of that side
  (`IsCoveringMap.injOn_closure_of_lifted_frontier`), so its Schoenflies ball filling descends
  to a ball chart in `M`. Hence `isIrreducible_of_isCoveringMap` and `isPrime_of_isCoveringMap`,
  also for a cover that is only diffeomorphic to `ℝ³`
  (`isIrreducible_of_isCoveringMap_of_diffeomorph`).
* `exists_isCoveringMap_of_euclidean`: a Euclidean structure has curvature zero
  (`hasConstantSectionalCurvature_of_hasThurstonAtlas_euclidean`), so the exponential map at any
  point is a covering `ℝ³ → M` and a local diffeomorphism
  (`expMapIntrinsic_isCoveringMap_of_riemannOp_eq_zero`), surjective by Hopf–Rinow. No developing
  map is needed.
* `flatStructurePrime` is the statement of `FlatStructurePrime`: a closed connected oriented
  `3`-manifold with a Euclidean structure is irreducible, hence prime (`isPrime_of_isIrreducible`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Topology

namespace GC.Endpoint

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem sphereBoundsBall_euclidean (e : sphere (0 : E3) 1 → E3)
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) : SphereBoundsBall e := by
  obtain ⟨Φ, hΦ⟩ := ThreeManifold.smooth_schoenflies_three e he
  exact ⟨Φ.toPartialDiffeomorph, subset_univ _, hΦ⟩

private theorem exists_innermost_lift {ι : Type*} [Nonempty ι]
    (f : ι → sphere (0 : E3) 1 → E3)
    (hf : ∀ i, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hdis : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (z₀ : sphere (0 : E3) 1)
    (hfin : ∀ K : Set E3, IsCompact K → {i | f i z₀ ∈ K}.Finite) :
    ∃ i, ∃ D : E3 ≃ₘ[ℝ] E3, D '' sphere 0 1 = range (f i) ∧
      Disjoint (D '' ball 0 1) (⋃ j, range (f j)) := by
  classical
  let _ : ConnectedSpace (sphere (0 : E3) 1) := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) (0 : E3) zero_le_one)
  have hconn (i : ι) : IsConnected (range (f i)) :=
    isConnected_range (hf i).contMDiff.continuous
  let d (i : ι) := (SphereSeparation.smoothSphereSidesOpenThreeSpace (f i) (hf i)
    (Diffeomorph.refl (𝓡 3) E3 ∞)).toSphereSides
  have hcl (i : ι) : range (f i) ⊆ closure (d i).compactSide := by
    intro x hx
    rw [(d i).closure_compactSide]
    exact Or.inr hx
  obtain ⟨a₀⟩ := (inferInstance : Nonempty ι)
  let K₀ := closure (d a₀).compactSide
  let κ := {i // f i z₀ ∈ K₀}
  have : Finite κ := (hfin K₀ (d a₀).isCompact_closure_compactSide).to_subtype
  let k₀ : κ := ⟨a₀, hcl a₀ (mem_range_self z₀)⟩
  have : Nonempty κ := ⟨k₀⟩
  obtain ⟨i, hi, hin⟩ := SphereSeparation.exists_sphereSides_compactSide_disjoint_iUnion
    (fun k : κ => d k.1) (fun k => hconn k.1)
    (fun k l hkl => hdis (fun h => hkl (Subtype.ext h)))
  have hside (j : ι) (hj : j ≠ a₀) (x : E3) (hxj : x ∈ range (f j))
      (hx : x ∈ (d a₀).compactSide) : range (f j) ⊆ (d a₀).compactSide := by
    rcases (d a₀).subset_compactSide_or_subset_endSide (hconn j).isPreconnected
      (fun y hy hy' => (hdis hj).le_bot ⟨hy, hy'⟩) with h | h
    · exact h
    · exact (Set.disjoint_left.mp (d a₀).disjoint hx (h hxj)).elim
  have hsub : (d i.1).compactSide ⊆ (d a₀).compactSide := by
    by_cases hia : i.1 = a₀
    · rw [hia]
    · have hfi : f i.1 z₀ ∈ (d a₀).compactSide := by
        have h := i.2
        change f i.1 z₀ ∈ closure (d a₀).compactSide at h
        rw [(d a₀).closure_compactSide] at h
        exact h.resolve_right (fun h' => (hdis hia).le_bot ⟨mem_range_self z₀, h'⟩)
      have hmeet : ((d i.1).compactSide ∩ (d a₀).compactSide).Nonempty := by
        obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp (hcl i.1 (mem_range_self z₀)) _
          (d a₀).isOpen_compactSide hfi
        exact ⟨y, hy2, hy1⟩
      rcases (d i.1).disjoint_sides_nested (d a₀) (hdis hia) (hconn a₀) hmeet with
        ⟨h, -⟩ | ⟨h, -⟩
      · exact subset_closure.trans h
      · exfalso
        have hk : k₀ ≠ i := fun h' => hia (congrArg Subtype.val h').symm
        exact (hin k₀ hk).le_bot
          ⟨subset_closure (h (hcl a₀ (mem_range_self z₀))), mem_range_self z₀⟩
  have havoid : Disjoint (d i.1).compactSide (⋃ j, range (f j)) := by
    rw [Set.disjoint_left]
    intro x hx hxU
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxU
    by_cases hjK : f j z₀ ∈ K₀
    · exact hi.le_bot ⟨hx, mem_iUnion.mpr ⟨⟨j, hjK⟩, hj⟩⟩
    · apply hjK
      have hja : j ≠ a₀ := fun h => hjK (h ▸ hcl a₀ (mem_range_self z₀))
      exact subset_closure (hside j hja x hj (hsub hx) (mem_range_self z₀))
  have hSch : SphereSeparation.smoothSchoenfliesThree := by
    intro e he
    obtain ⟨D, hD⟩ := ThreeManifold.smooth_schoenflies_three e he
    exact ⟨D.toPartialDiffeomorph, subset_univ _, hD⟩
  obtain ⟨D, hD⟩ :=
    (SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp hSch)
      (f i.1) (hf i.1)
  refine ⟨i.1, D, ?_, ?_⟩
  · calc D '' sphere (0 : E3) 1 = D.toHomeomorph '' frontier (ball (0 : E3) 1) := by
          rw [frontier_ball (0 : E3) one_ne_zero]
          rfl
      _ = frontier (D '' ball (0 : E3) 1) := D.toHomeomorph.image_frontier _
      _ = range (f i.1) := by
          rw [hD]
          exact (d i.1).frontier_compactSide
  · rw [hD]
    exact havoid

theorem sphereBoundsBall_of_isCoveringMap {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {p : E3 → M} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (e : sphere (0 : E3) 1 → M) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    SphereBoundsBall e := by
  let z₀ : sphere (0 : E3) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨lifts, hbase, hemb, hproj, hdis, hcover⟩ :=
    exists_disjoint_smooth_sphere_lifts hp hlocal e he z₀
  have : Nonempty (p ⁻¹' {e z₀}) := by
    obtain ⟨y, hy⟩ := hsurj (e z₀)
    exact ⟨⟨y, hy⟩⟩
  have hfin (K : Set E3) (hK : IsCompact K) : {a | lifts a z₀ ∈ K}.Finite := by
    have : DiscreteTopology (p ⁻¹' {e z₀}) := (hp (e z₀)).discreteTopology_fiber
    have hclosed : IsClosed (p ⁻¹' {e z₀}) := isClosed_singleton.preimage hp.continuous
    have hc : IsCompact (((↑) : p ⁻¹' {e z₀} → E3) ⁻¹' K) :=
      hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    have hset : {a | lifts a z₀ ∈ K} = ((↑) : p ⁻¹' {e z₀} → E3) ⁻¹' K := by
      ext a
      change lifts a z₀ ∈ K ↔ (a : E3) ∈ K
      rw [hbase]
    rw [hset]
    exact hc.finite_of_discrete
  obtain ⟨a, D, hDsphere, hDavoid⟩ := exists_innermost_lift lifts hemb hdis z₀ hfin
  let B := D '' ball (0 : E3) 1
  have hBopen : IsOpen B := D.toHomeomorph.isOpenMap _ isOpen_ball
  have hBconn : IsPreconnected B :=
    (convex_ball (0 : E3) 1).isPreconnected.image D D.continuous.continuousOn
  have hBclosure : closure B = D '' closedBall (0 : E3) 1 := by
    rw [← closure_ball (0 : E3) one_ne_zero]
    exact (D.toHomeomorph.image_closure _).symm
  have hBfront : frontier B = range (lifts a) := by
    rw [← hDsphere, ← frontier_ball (0 : E3) one_ne_zero]
    exact (D.toHomeomorph.image_frontier _).symm
  have hBavoid : Disjoint B (p ⁻¹' range e) := by
    rw [hcover]
    exact hDavoid
  have hinj := IsCoveringMap.injOn_closure_of_lifted_frontier hp he.isEmbedding.injective
    (hproj a) hBopen hBconn hBfront hBavoid
  have hcompinj : InjOn (p ∘ D) (closedBall (0 : E3) 1) := by
    intro z hz w hw hzw
    apply D.injective
    apply hinj
    · rw [hBclosure]
      exact mem_image_of_mem _ hz
    · rw [hBclosure]
      exact mem_image_of_mem _ hw
    · exact hzw
  have hcompLocal :
      IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (p ∘ D) (closedBall (0 : E3) 1) := by
    intro z
    exact (D.isLocalDiffeomorph z.val).comp (𝓡 3) M (hlocal (D z.val))
  obtain ⟨G, hGsrc, hG⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
    hcompLocal (isCompact_closedBall (0 : E3) 1) ⟨0, mem_closedBall_self zero_le_one⟩ hcompinj
  refine ⟨G, hGsrc, ?_⟩
  rw [hG, image_comp, hDsphere, ← range_comp]
  exact congrArg range (funext (hproj a))

theorem isIrreducible_of_isCoveringMap (P : ConnectedClosedOrientedManifold.{u} 3)
    {p : E3 → P.Carrier} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) : IsIrreducible P :=
  fun e he => sphereBoundsBall_of_isCoveringMap hp hsurj hlocal e he

theorem isIrreducible_of_isCoveringMap_of_diffeomorph (P : ConnectedClosedOrientedManifold.{u} 3)
    {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
    (ψ : N ≃ₘ⟮𝓡 3, 𝓡 3⟯ E3) {p : N → P.Carrier} (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) (hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) :
    IsIrreducible P := by
  refine isIrreducible_of_isCoveringMap P (p := p ∘ ψ.symm)
    (hp.comp_homeomorph ψ.symm.toHomeomorph) (hsurj.comp ψ.symm.surjective) ?_
  intro z
  exact (ψ.symm.isLocalDiffeomorph z).comp (𝓡 3) P.Carrier (hlocal (ψ.symm z))

theorem isPrime_of_isCoveringMap (P : ConnectedClosedOrientedManifold.{u} 3)
    {p : E3 → P.Carrier} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) : IsPrime P :=
  isPrime_of_isIrreducible P (isIrreducible_of_isCoveringMap P hp hsurj hlocal)

open Bundle DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_isCoveringMap_of_euclidean (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .euclidean) :
    ∃ p : E3 → P.Carrier, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p := by
  have hA : GC.Geometry.HasThurstonAtlas g.metric .euclidean := hg ▸ g.atlas
  have hsec := GC.Geometry.hasConstantSectionalCurvature_of_hasThurstonAtlas_euclidean hA
  have hR : ∀ (x : P.Carrier) (X Y Z : TangentSpace (𝓡 3) x),
      riemannOp (LeviCivita (I := 𝓡 3) g.metric) x X Y Z = 0 := by
    intro x X Y Z
    rw [GC.Geometry.riemannOp_eq_smul_of_hasConstantSectionalCurvature hsec x X Y Z, zero_smul]
  let : IsManifold (𝓡 3) 1 P.Carrier :=
    IsManifold.of_le (I := 𝓡 3) (M := P.Carrier) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace (𝓡 3) P.Carrier
  let : T3Space P.Carrier := inferInstance
  let : RiemannianBundle (fun x : P.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨g.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E3 (fun x : P.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨⟨g.metric.inner, g.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace P.Carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) P.Carrier
  let : CompleteSpace P.Carrier := g.complete.complete
  have hEg : IsMetricNorm (I := 𝓡 3) (M := P.Carrier) g.metric := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓡 3) g.metric z v
  obtain ⟨x₀⟩ := (inferInstance : Nonempty P.Carrier)
  refine ⟨fun z => expMapIntrinsic (I := 𝓡 3) g.metric hEg x₀ z,
    expMapIntrinsic_isCoveringMap_of_riemannOp_eq_zero g.metric hEg hR x₀, ?_,
    expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero g.metric hEg hR x₀⟩
  intro q
  obtain ⟨v, hv, -⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing g.metric hEg x₀ q
  exact ⟨v, hv⟩

theorem isIrreducible_of_euclidean (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .euclidean) :
    IsIrreducible P := by
  obtain ⟨p, hp, hsurj, hlocal⟩ := exists_isCoveringMap_of_euclidean P g hg
  exact isIrreducible_of_isCoveringMap P hp hsurj hlocal

theorem flatStructurePrime :
    ∀ P : ConnectedClosedOrientedManifold.{u} 3,
      ∀ g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier, g.model = .euclidean → IsPrime P :=
  fun P g hg => isPrime_of_isIrreducible P (isIrreducible_of_euclidean P g hg)

end GC.Endpoint
