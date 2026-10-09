import DifferentialGeometry.Topology.Covering.PathLiftingCriterion
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Lift
import DifferentialGeometry.Geometry.Exponential.GaussLemma.Framed
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.CurvatureBound
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Agreement
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength
import DifferentialGeometry.Geometry.Thurston.FlatPrime
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.NoCuts
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Transport

/-!
# Closed hyperbolic `3`-manifolds are prime

Chapter 6, packet K18 (`docs/geometrization/handoffs/20261003-chapter6-design-v2.md`, §1 (b)).

* Cartan–Hadamard, `GC.Geometry.framedExpMap_isCoveringMap_of_nonpos`: on a complete connected
  Riemannian manifold with `⟪R(v, Y) Y, v⟫ ≤ 0` the framed exponential map at any point is a
  covering map. It is a local diffeomorphism because radial Jacobi fields vanishing at both
  ends vanish (`injective_mfderiv_expMap_of_curvature_upper_bound` with `κ = 0`) and it is
  onto by Hopf–Rinow. Smooth paths lift through it from every point: the Gauss lemma bounds
  the radial growth of a lift by the length of the path
  (`norm_sub_le_pathELength_framedExpMap`), which fences partial lifts in a compact ball
  (`isLiftOn.exists_of_compact`). The covering criterion
  `isCoveringMap_of_forall_smooth_path_lift` concludes.
* `exists_isCoveringMap_of_nonpos`, `isIrreducible_of_nonpos`: a closed connected oriented
  `3`-manifold with a complete metric of nonpositive curvature is covered by `ℝ³` and is
  irreducible (`isIrreducible_of_isCoveringMap`).
* `isPrime_of_hyperbolicStructure`: a hyperbolic structure has curvature `-1`
  (`hasConstantSectionalCurvature_of_hasThurstonAtlas_hyperbolic`), so `⟪R(v, Y) Y, v⟫ =
  ⟪v, Y⟫² - |v|²|Y|² ≤ 0`, and the manifold is prime (`isPrime_of_isIrreducible`).
  `hyperbolicStructurePrime` discharges the named statement `HyperbolicStructurePrime`.
* `geometricDecomposition_of_hyperbolicStructure`, `geometrizes_of_hyperbolicStructure`: the
  one-factor prime decomposition `PrimeDecomposition.ofIsPrime` with the no-cut geometric
  decomposition `NoCuts.geometricDecomposition`;
  `exists_prime_geometric_decomposition_of_hyperbolic_torusDecomposition` is the same
  certificate from a given torus decomposition (`TorusDecomposition.toGeometricDecomposition`),
  the conclusion shape of the hyperbolic branch of `GM/Refinement.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle
open scoped Manifold ContDiff Topology

namespace GC.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
  DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] in
theorem framedExpMap_isLocalDiffeomorph_of_nonpos (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (hR : ∀ (x : M) (v Y : TangentSpace I x),
      g.inner x (riemannOp (LeviCivita (I := I) g) x v Y Y) v ≤ 0) :
    IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ (framedExpMap (I := I) g p) := by
  have hdom : ∀ z : E, normalFrame (I := I) g p z ∈ expDomain (I := I) g p := fun z => by
    rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
    exact mem_univ _
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ]
  refine isLocalDiffeomorphOn_framedExpMap (I := I) g p isOpen_univ (fun z _ => hdom z) ?_
  intro z _
  rw [mfderiv_framedExpMap (I := I) g p (hdom z)]
  have hinj := injective_mfderiv_expMap_of_curvature_upper_bound (I := I) g p
    (normalFrame (I := I) g p z) (hdom z) (κ := 0) (by positivity)
    (fun t _ v => by rw [zero_mul]; exact hR _ v _)
  exact hinj.comp (normalFrame (I := I) g p).injective

theorem framedExpMap_surjective [ConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    Surjective (framedExpMap (I := I) g p) := by
  intro q
  obtain ⟨v, hv, -⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing g hEnorm p q
  refine ⟨(normalFrame (I := I) g p).symm v, ?_⟩
  rw [framedExpMap_apply, ContinuousLinearEquiv.apply_symm_apply,
    expMap_eq_expMapIntrinsic g hEnorm p]
  exact hv

theorem framedExpMap_isCoveringMap_of_nonpos [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (hR : ∀ (x : M) (v Y : TangentSpace I x),
      g.inner x (riemannOp (LeviCivita (I := I) g) x v Y Y) v ≤ 0) :
    IsCoveringMap (framedExpMap (I := I) g p) := by
  let F := framedExpMap (I := I) g p
  have hloc := framedExpMap_isLocalDiffeomorph_of_nonpos g hEnorm p hR
  have hlocU : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ F univ :=
    isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ.mp hloc
  have hdom : ∀ z : E, normalFrame (I := I) g p z ∈ expDomain (I := I) g p := fun z => by
    rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
    exact mem_univ _
  refine isCoveringMap_of_forall_smooth_path_lift (I := I) hloc.isLocalHomeomorph
    (framedExpMap_surjective g hEnorm p) ?_
  intro γ hγ z hz
  have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) := hγ.of_le (by simp)
  have hfin : Manifold.pathELength I γ 0 1 ≠ ⊤ := by
    rw [Geodesic.pathELength_eq_arcLength_of_enorm_eq (I := I) g zero_le_one
      ((Geodesic.speedSqrt_integrableOn_Icc_of_C1 (I := I) g zero_le_one hγ1).mono_set
        Ioo_subset_Icc_self) (fun t _ => hEnorm _ _)]
    exact ENNReal.ofReal_ne_top
  let L : ℝ := (Manifold.pathELength I γ 0 1).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hfence : ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) 1 → ∀ {η : ℝ → E},
      isLiftOn F γ univ z 0 t η → η t ∈ Metric.closedBall (0 : E) (‖z‖ + L) := by
    intro t ht η hη
    have hηcd : ContDiffOn ℝ 1 η (Icc 0 t) :=
      hη.contDiffOn hlocU (hγ1.mono (Icc_subset_Icc le_rfl ht.2))
    have hlen := norm_sub_le_pathELength_framedExpMap g hEnorm p ht.1 hηcd
      (fun s _ => hdom (η s))
    have hcongr : Manifold.pathELength I (framedExpMap (I := I) g p ∘ η) 0 t =
        Manifold.pathELength I γ 0 t := by
      apply Manifold.pathELength_congr
      intro s hs
      exact (hη.2.2 s hs).2
    have hmono : Manifold.pathELength I γ 0 t ≤ Manifold.pathELength I γ 0 1 :=
      Manifold.pathELength_mono le_rfl ht.2
    rw [hcongr, hη.2.1] at hlen
    have hle : ENNReal.ofReal (‖η t‖ - ‖z‖) ≤ ENNReal.ofReal L := by
      rw [ENNReal.ofReal_toReal hfin]
      exact hlen.trans hmono
    rw [ENNReal.ofReal_le_ofReal_iff hL] at hle
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  obtain ⟨η, hη⟩ := isLiftOn.exists_of_compact (F := F) (γ := γ) (U := univ) (e₀ := z)
    zero_le_one isOpen_univ hlocU hγ.continuousOn (mem_univ z) hz
    (isCompact_closedBall _ _) (subset_univ _) hfence
  exact ⟨η, hη.1, hη.2.1, fun t ht => (hη.2.2 t ht).2⟩

end GC.Geometry

namespace GC.Endpoint

open DifferentialGeometry DifferentialGeometry.Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_isCoveringMap_of_nonpos (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) P.Carrier)
    (hc : DifferentialGeometry.RiemannianMetricComplete g)
    (hR : ∀ (x : P.Carrier) (v Y : TangentSpace (𝓡 3) x),
      g.inner x (riemannOp (LeviCivita (I := 𝓡 3) g) x v Y Y) v ≤ 0) :
    ∃ p : E3 → P.Carrier, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p := by
  let : IsManifold (𝓡 3) 1 P.Carrier :=
    IsManifold.of_le (I := 𝓡 3) (M := P.Carrier) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace (𝓡 3) P.Carrier
  let : T3Space P.Carrier := inferInstance
  let : RiemannianBundle (fun x : P.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E3 (fun x : P.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace P.Carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) P.Carrier
  let : CompleteSpace P.Carrier := hc.complete
  have hEg : IsMetricNorm (I := 𝓡 3) (M := P.Carrier) g := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓡 3) g z v
  obtain ⟨x₀⟩ := (inferInstance : Nonempty P.Carrier)
  exact ⟨_, GC.Geometry.framedExpMap_isCoveringMap_of_nonpos g hEg x₀ hR,
    GC.Geometry.framedExpMap_surjective g hEg x₀,
    GC.Geometry.framedExpMap_isLocalDiffeomorph_of_nonpos g hEg x₀ hR⟩

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection in
theorem isIrreducible_of_nonpos (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) P.Carrier)
    (hc : DifferentialGeometry.RiemannianMetricComplete g)
    (hR : ∀ (x : P.Carrier) (v Y : TangentSpace (𝓡 3) x),
      g.inner x (riemannOp (LeviCivita (I := 𝓡 3) g) x v Y Y) v ≤ 0) :
    IsIrreducible P := by
  obtain ⟨p, hp, hsurj, hlocal⟩ := exists_isCoveringMap_of_nonpos P g hc hR
  exact isIrreducible_of_isCoveringMap P hp hsurj hlocal

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection in
theorem inner_riemannOp_le_zero_of_hyperbolic {P : ConnectedClosedOrientedManifold.{u} 3}
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .hyperbolic)
    (x : P.Carrier) (v Y : TangentSpace (𝓡 3) x) :
    g.metric.inner x (riemannOp (LeviCivita (I := 𝓡 3) g.metric) x v Y Y) v ≤ 0 := by
  have hA : GC.Geometry.HasThurstonAtlas g.metric .hyperbolic := hg ▸ g.atlas
  have hsec := GC.Geometry.hasConstantSectionalCurvature_of_hasThurstonAtlas_hyperbolic hA
  rw [GC.Geometry.riemannOp_eq_smul_of_hasConstantSectionalCurvature hsec x v Y Y]
  simp only [map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul]
  have hcs := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g.metric x v Y
  rw [g.metric.symm x Y v]
  nlinarith

theorem exists_isCoveringMap_of_hyperbolic (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .hyperbolic) :
    ∃ p : E3 → P.Carrier, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p :=
  exists_isCoveringMap_of_nonpos P g.metric g.complete
    (inner_riemannOp_le_zero_of_hyperbolic g hg)

theorem isIrreducible_of_hyperbolicStructure (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .hyperbolic) :
    IsIrreducible P := by
  obtain ⟨p, hp, hsurj, hlocal⟩ := exists_isCoveringMap_of_hyperbolic P g hg
  exact isIrreducible_of_isCoveringMap P hp hsurj hlocal

theorem isPrime_of_hyperbolicStructure (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .hyperbolic) :
    IsPrime P :=
  isPrime_of_isIrreducible P (isIrreducible_of_hyperbolicStructure P g hg)

def HyperbolicStructurePrime : Prop :=
  ∀ P : ConnectedClosedOrientedManifold.{u} 3,
    ∀ g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier, g.model = .hyperbolic → IsPrime P

theorem hyperbolicStructurePrime : HyperbolicStructurePrime.{u} :=
  fun P g hg => isPrime_of_hyperbolicStructure P g hg

theorem geometricDecomposition_of_hyperbolicStructure
    (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .hyperbolic) :
    ∃ D : PrimeDecomposition P,
      ∀ i : Fin D.factors.length, Nonempty (GeometricDecomposition (D.factors.get i)) := by
  refine ⟨PrimeDecomposition.ofIsPrime P (isPrime_of_hyperbolicStructure P g hg), ?_⟩
  rintro ⟨_ | n, hn⟩
  · exact ⟨NoCuts.geometricDecomposition P g⟩
  · exact absurd hn (by simp [PrimeDecomposition.ofIsPrime_factors])

theorem geometrizes_of_hyperbolicStructure (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .hyperbolic) :
    Geometrizes P := by
  obtain ⟨D, hD⟩ := geometricDecomposition_of_hyperbolicStructure P g hg
  exact ⟨{ primeData := D, geometricFactors := fun i => Classical.choice (hD i) }⟩

theorem exists_prime_geometric_decomposition_of_hyperbolic_torusDecomposition
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) M.Carrier) (hg : g.model = .hyperbolic)
    (D : GC.Topology.TorusDecomposition M)
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (geometry : D.components.Geometry) :
    ∃ P : PrimeDecomposition M,
      ∀ i : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get i)) := by
  refine ⟨PrimeDecomposition.ofIsPrime M (isPrime_of_hyperbolicStructure M g hg), ?_⟩
  rintro ⟨_ | n, hn⟩
  · exact ⟨D.toGeometricDecomposition incompressible geometry⟩
  · exact absurd hn (by simp [PrimeDecomposition.ofIsPrime_factors])

end GC.Endpoint
