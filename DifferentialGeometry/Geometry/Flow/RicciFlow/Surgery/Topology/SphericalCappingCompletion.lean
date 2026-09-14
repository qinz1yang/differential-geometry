import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BallDiffeomorph

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance : ChartedSpace (EuclideanHalfSpace 3)
    (DifferentialGeometry.Topology.ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance : IsManifold (𝓡∂ 3) ∞ (DifferentialGeometry.Topology.ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

private theorem linearEquiv_symm_trans_comp_eq {U V W X : Type*}
    [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup X] [Module ℝ X]
    (A : U →ₗ[ℝ] W) (B : U →ₗ[ℝ] X) (A' : V →ₗ[ℝ] W) (B' : V →ₗ[ℝ] X)
    (D : U →ₗ[ℝ] V) (hA : A = A'.comp D) (hB : B = B'.comp D)
    (hi : Function.Bijective A) (hi' : Function.Bijective A')
    (hj : Function.Bijective B) (hj' : Function.Bijective B') :
    (LinearEquiv.ofBijective A hi).symm.trans (LinearEquiv.ofBijective B hj) =
      (LinearEquiv.ofBijective A' hi').symm.trans (LinearEquiv.ofBijective B' hj') := by
  refine LinearEquiv.ext fun w => ?_
  have h1 : A' ((LinearEquiv.ofBijective A' hi').symm w) = w := by
    simpa only [LinearEquiv.ofBijective_apply] using
      LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective A' hi') w
  have h2 : A ((LinearEquiv.ofBijective A hi).symm w) = w := by
    simpa only [LinearEquiv.ofBijective_apply] using
      LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective A hi) w
  have hgen : ∀ y : U, A y = A' (D y) := fun y => by rw [hA]; rfl
  have key : (LinearEquiv.ofBijective A' hi').symm w =
      D ((LinearEquiv.ofBijective A hi).symm w) := by
    apply hi'.injective
    calc A' ((LinearEquiv.ofBijective A' hi').symm w)
        = w := h1
      _ = A ((LinearEquiv.ofBijective A hi).symm w) := h2.symm
      _ = A' (D ((LinearEquiv.ofBijective A hi).symm w)) := hgen _
  simp only [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply]
  rw [key, ← LinearMap.comp_apply, ← hB]

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

noncomputable def capClosedCell (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    C(DifferentialGeometry.Topology.ClosedCell 3, N.Carrier) :=
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  ⟨fun z => X.trace.capping.cap b (X.closedCellBallDiffeomorph z),
    (X.trace.capping.cap b).continuous.comp X.closedCellBallDiffeomorph.continuous⟩

theorem capClosedCell_apply (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) (z : DifferentialGeometry.Topology.ClosedCell 3) :
    X.capClosedCell b z = X.trace.capping.cap b (X.closedCellBallDiffeomorph z) := rfl

theorem range_capClosedCell (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    Set.range (X.capClosedCell b) = Set.range (X.trace.capping.cap b) :=
  Function.Surjective.range_comp (f := (X.closedCellBallDiffeomorph :
      DifferentialGeometry.Topology.ClosedCell 3 → ThreeBall))
    X.closedCellBallDiffeomorph.surjective ⇑(X.trace.capping.cap b)

theorem iUnion_range_capClosedCell (X : SmoothCutCapTransition P Q D N) :
    (⋃ b, Set.range (X.capClosedCell b)) =
      ⋃ b, Set.range (X.trace.capping.cap b) :=
  iUnion_congr fun b => range_capClosedCell X b

theorem capClosedCell_isSmoothEmbedding (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (X.capClosedCell b) :=
  X.cap_isSmoothEmbedding_closedCell b

theorem coreBoundarySphere_ofSmoothCutCapTransition (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    (SphericalTubeSystem.ofSmoothCutCapTransition X).coreBoundarySphere b =
      X.trace.tubes.coreBoundarySphere b := rfl

theorem capClosedCell_boundary_eq (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    X.capClosedCell b (DifferentialGeometry.Topology.sphereToClosedCell z) =
      X.trace.capping.coreInclusion
        ((SphericalTubeSystem.ofSmoothCutCapTransition X).coreBoundarySphere b
          (X.attaching b z)) := by
  rw [capClosedCell_apply, X.closedCellBallDiffeomorph_sphereToClosedCell,
    X.trace.capping.boundary_eq b z, coreBoundarySphere_ofSmoothCutCapTransition,
    ← X.attaching_eq b]
  rfl

theorem exhaustive_capClosedCell (X : SmoothCutCapTransition P Q D N) :
    Set.range (X.trace.capping.coreInclusion) ∪
        (⋃ b, Set.range (X.capClosedCell b)) = Set.univ := by
  rw [iUnion_range_capClosedCell]
  exact X.trace.capping.exhaustive

theorem core_cap_intersection_capClosedCell (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    Set.range (X.trace.capping.coreInclusion) ∩ Set.range (X.capClosedCell b) =
      Set.range (X.trace.capping.coreInclusion.comp
        ((SphericalTubeSystem.ofSmoothCutCapTransition X).coreBoundarySphere b)) := by
  rw [range_capClosedCell, coreBoundarySphere_ofSmoothCutCapTransition]
  exact X.trace.capping.core_cap_intersection b

theorem cap_disjoint_capClosedCell (X : SmoothCutCapTransition P Q D N) :
    Pairwise fun b b' => Disjoint (Set.range (X.capClosedCell b))
      (Set.range (X.capClosedCell b')) :=
  fun b b' hne => (X.trace.capping.cap_disjoint hne).mono
    (range_capClosedCell X b).le (range_capClosedCell X b').le

theorem capClosedCell_positive (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary)
    (x : DifferentialGeometry.Topology.ClosedCell 3)
    (hx : (𝓡∂ 3).IsInteriorPoint x) :
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x),
      ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (X.capClosedCell b) x),
        Orientation.map (Fin 3)
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
            (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
              EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
              (X.capClosedCell b) x).toLinearMap hj))
          ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
            (if b.2 then (1 : ℝˣ) else -1) •
              N.orientation.orientation (X.capClosedCell b x) :=
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  by
    have hmde : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x :=
      X.closedCellBallDiffeomorph.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hmdφ : MDifferentiableAt (𝓡∂ 3) (𝓡 3) (⇑(X.trace.capping.cap b))
        (X.closedCellBallDiffeomorph x) :=
      (X.cap_smooth b).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hmdψ : MDifferentiableAt (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3))
        (X.closedCellBallDiffeomorph x) :=
      X.ball_induced.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hy : (𝓡∂ 3).IsInteriorPoint (X.closedCellBallDiffeomorph x) :=
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (n := ∞) (by simp)
        (X.closedCellBallDiffeomorph.isLocalDiffeomorph x)).mp hx
    obtain ⟨hi', hj', hsign⟩ := X.cap_positive b (X.closedCellBallDiffeomorph x) hy
    have hchainCap : mfderiv (𝓡∂ 3) (𝓡 3)
        (fun z => X.trace.capping.cap b (X.closedCellBallDiffeomorph z)) x =
        (mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.trace.capping.cap b))
          (X.closedCellBallDiffeomorph x)).comp
          (mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x) :=
      mfderiv_comp x hmdφ hmde
    have hchainVal : mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x =
        (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3))
          (X.closedCellBallDiffeomorph x)).comp
          (mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x) :=
      mfderiv_comp x hmdψ hmde
    have hD : Function.Bijective (⇑(mfderiv (𝓡∂ 3) (𝓡∂ 3)
        (⇑X.closedCellBallDiffeomorph) x)) := by
      rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe (X.closedCellBallDiffeomorph) (by simp)]
      exact (X.closedCellBallDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).bijective
    have hA : (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x).toLinearMap =
        ((mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3))
          (X.closedCellBallDiffeomorph x)).toLinearMap).comp
          ((mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x).toLinearMap) := by
      rw [hchainVal]
      rfl
    have hcapfun : ⇑(X.capClosedCell b) =
        fun z => X.trace.capping.cap b (X.closedCellBallDiffeomorph z) := rfl
    have hB : (mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.capClosedCell b)) x).toLinearMap =
        ((mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.trace.capping.cap b))
          (X.closedCellBallDiffeomorph x)).toLinearMap).comp
          ((mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x).toLinearMap) := by
      rw [hcapfun, hchainCap]
      rfl
    have hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x) := by
      have h := hi'.comp hD
      rw [hchainVal]
      exact h
    have hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (X.capClosedCell b) x) := by
      have h := hj'.comp hD
      rw [hcapfun, hchainCap]
      exact h
    refine ⟨hi, hj, ?_⟩
    rw [linearEquiv_symm_trans_comp_eq
      ((mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x).toLinearMap)
      ((mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.capClosedCell b)) x).toLinearMap)
      ((mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3))
        (X.closedCellBallDiffeomorph x)).toLinearMap)
      ((mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.trace.capping.cap b))
        (X.closedCellBallDiffeomorph x)).toLinearMap)
      ((mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x).toLinearMap)
      hA hB hi hi' hj hj']
    exact hsign

def boundaryFrameReversing (X : SmoothCutCapTransition P Q D N) : Prop :=
  ∀ (b : (SphericalTubeSystem.ofSmoothCutCapTransition X).Boundary)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (v w : TangentSpace (𝓡 2) z),
    let f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
        P.toClosedOrientedManifold.Carrier :=
      (SphericalTubeSystem.ofSmoothCutCapTransition X).boundarySphere b ∘ X.attaching b
    let _ : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f z)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
    let d := mfderiv (𝓡 2) (𝓡 3) f z
    let e := mfderiv (𝓡 2) (𝓡 3)
      (Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
        EuclideanSpace ℝ (Fin 3)) z
    (0 < ((P.toClosedOrientedManifold.orientation.orientation (f z)).someBasis (by
      change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
      simp)).det
      (Fin.cons ((SphericalTubeSystem.ofSmoothCutCapTransition X).outwardVector b
          (X.attaching b z)) (Fin.cons (d v) (Fin.cons (d w) ![])))) ↔
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
        (Fin.cons z.1 (Fin.cons (e v) (Fin.cons (e w) ![]))) < 0

noncomputable def toSphericalCapping (X : SmoothCutCapTransition P Q D N)
    (hboundary : X.boundaryFrameReversing) :
    DifferentialGeometry.Topology.SphericalCapping P.toClosedOrientedManifold
      N.toClosedOrientedManifold (SphericalTubeSystem.ofSmoothCutCapTransition X) where
  coreCharts := X.coreCharts
  coreSmooth := X.coreSmooth
  core_induced := X.core_induced
  core_compact := isCompact_iff_compactSpace.mpr X.core_compact
  core_boundary := X.core_boundary
  coreInclusion := X.trace.capping.coreInclusion
  core_embedding := X.core_inclusion_smooth
  cap := fun b => X.capClosedCell b
  cap_embedding := fun b => X.capClosedCell_isSmoothEmbedding b
  attaching := X.attaching
  boundary_eq := fun b z => X.capClosedCell_boundary_eq b z
  exhaustive := X.exhaustive_capClosedCell
  core_cap_intersection := fun b => X.core_cap_intersection_capClosedCell b
  cap_disjoint := X.cap_disjoint_capClosedCell
  core_positive := X.core_positive
  cap_positive := fun b x hx => X.capClosedCell_positive b x hx
  boundary_orientation_reversing := hboundary

noncomputable def toSphericalCappingCompletion (X : SmoothCutCapTransition P Q D N)
    (hboundary : X.boundaryFrameReversing) : SphericalCappingCompletion X where
  capping := X.toSphericalCapping hboundary
  coreInclusion_eq := fun _ => rfl

noncomputable def toSmoothCutCapCompletion (X : SmoothCutCapTransition P Q D N)
    (hboundary : X.boundaryFrameReversing) : SmoothCutCapCompletion X :=
  SmoothCutCapCompletion.ofSphericalCappingCompletion X (X.toSphericalCappingCompletion hboundary)

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
