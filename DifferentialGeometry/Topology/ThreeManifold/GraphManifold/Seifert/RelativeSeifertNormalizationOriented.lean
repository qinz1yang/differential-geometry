import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationMerge
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import DifferentialGeometry.Topology.Manifold.InteriorBoundary
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# The oriented separating single-sphere reconstruction

Lane BR, tier R7 (review 26 §7.1). The diffeomorphism `K` of `exists_mergeDiffeomorph_core`
from `M` onto the smooth connected sum of the two capped sides preserves orientation: near an
interior core point `y` whose core image lies in the first side, `K ∘ val` agrees with
`interiorLeft ∘ g`, where `g` is the core inclusion read in the punctured first side. By the chain
rule `dK = d(interiorLeft) ∘ d(coreInclusion) ∘ d(val)⁻¹`; `core_positive` makes the last two
factors positive, the component orientation is the restriction of the capped orientation, and
`interiorLeft_preserves_orientation` makes the first factor positive. One point suffices on the
connected target (`Diffeomorph.preservesOrientation_of_eq_at`); interior core points with image
in the first side exist since interior points are dense and that set is open and contains the
first boundary sphere. Composing with the oriented change of ball charts gives
`M ≅⁺ A # B` (`orientedSingleSphere_of_ne`).
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function Filter
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem capComponentBallChart_ne_core {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) (y : E.tubes.core) (b : E.tubes.Boundary)
    (hy : ConnectedComponents.mk (E.capping.coreInclusion y) = E.cutCapVertex b.1 b.2)
    {z : E3} (hz : z ∈ closedBall (0 : E3) 2) :
    (E.capComponentBallChart b).chart z ≠ ⟨E.capping.coreInclusion y, hy⟩ := by
  intro h
  have h1 : ((E.capComponentBallChart b).chart z).val = E.capping.coreInclusion y :=
    congrArg Subtype.val h
  rw [E.capComponentBallChart_apply_closedBall b hz] at h1
  exact Set.disjoint_left.mp (E.capping.disjoint_capBallChart_closedBall_core b)
    ⟨z, hz, rfl⟩ ⟨y, h1.symm⟩

theorem orientation_map_trans' {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (e : A ≃ₗ[ℝ] B) (f : B ≃ₗ[ℝ] C) (o : Orientation ℝ A (Fin 3)) :
    Orientation.map (Fin 3) (e.trans f) o =
      Orientation.map (Fin 3) f (Orientation.map (Fin 3) e o) := by
  induction o using Module.Ray.ind with | h v hv => rfl

theorem mdifferentiableAt_of_bijective {X Y : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 3) X] [TopologicalSpace Y] [ChartedSpace E3 Y]
    {f : X → Y} {x : X} (h : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) f x)) :
    MDifferentiableAt (𝓡∂ 3) (𝓡 3) f x := by
  by_contra hf
  rw [mfderiv_zero_of_not_mdifferentiableAt hf] at h
  have h1 : (EuclideanSpace.single 0 1 : E3) ≠ 0 := by simp
  exact h1 (h.1 (by simp : (0 : E3 →L[ℝ] E3) (EuclideanSpace.single 0 1) = (0 : E3 →L[ℝ] E3) 0))

theorem exists_interior_core_mem {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) (b : E.tubes.Boundary) :
    let _ := E.capping.coreCharts
    ∃ y : E.tubes.core, (𝓡∂ 3).IsInteriorPoint y ∧
      ConnectedComponents.mk (E.capping.coreInclusion y) = E.cutCapVertex b.1 b.2 := by
  intro _
  let _ := E.capping.coreSmooth
  let W : Set E.tubes.core := {y | ConnectedComponents.mk (E.capping.coreInclusion y) =
    E.cutCapVertex b.1 b.2}
  have hW : IsOpen W :=
    (ClosedOrientedManifold.isOpen_componentSet E.capped _).preimage
      E.capping.coreInclusion.continuous
  have hne : W.Nonempty := ⟨E.tubes.coreBoundarySphere b sphereBasePoint, rfl⟩
  have : IsManifold (𝓡∂ 3) 1 E.tubes.core := IsManifold.of_le (n := ∞) (by norm_num)
  obtain ⟨y, hy, hyW⟩ := (ModelWithCorners.dense_interior (𝓡∂ 3)).exists_mem_open hW hne
  exact ⟨y, hy, hyW⟩

theorem mergeDiffeomorph_preservesOrientation {M : ConnectedClosedOrientedManifold.{u} 3}
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    (K : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (PairedBallGluing.mergeFactor E.capped.component
        E.cutCapVertex (fun a t => E.capComponentBallChart (a, t)) a boundaryAttachment
          none).Carrier)
    (hK : ∀ (y : E.tubes.core) (x : (E.capComponentBallChart (a, false)).interior),
        (x : (E.capped.component (E.cutCapVertex a false)).Carrier).val =
            E.capping.coreInclusion y →
          K y.val = ConnectedSumQuotient.interiorLeft (E.capComponentBallChart (a,
              false)).toBallChart
            (E.capComponentBallChart (a, true)).toBallChart boundaryAttachment.1 x) :
    K.preservesOrientation M.orientation (PairedBallGluing.mergeFactor E.capped.component
        E.cutCapVertex (fun a t => E.capComponentBallChart (a, t)) a boundaryAttachment
          none).orientation := by
  classical
  let _ := E.capping.coreCharts
  let _ := E.capping.coreSmooth
  obtain ⟨y, hint, hyA⟩ := exists_interior_core_mem E (a, false)
  have hmem : ∀ (y' : E.tubes.core)
      (h : ConnectedComponents.mk (E.capping.coreInclusion y') = E.cutCapVertex a false),
      (⟨E.capping.coreInclusion y', h⟩ : (E.capped.component (E.cutCapVertex a false)).Carrier) ∈
        (E.capComponentBallChart (a, false)).interior := by
    rintro y' h ⟨z, hz, hzy⟩
    exact capComponentBallChart_ne_core E y' (a, false) h
      (closedBall_subset_closedBall (by norm_num) hz) hzy
  let x₀ : (E.capComponentBallChart (a, false)).interior :=
    ⟨⟨E.capping.coreInclusion y, hyA⟩, hmem y hyA⟩
  let g : E.tubes.core → (E.capComponentBallChart (a, false)).interior := fun y' =>
    if h : ConnectedComponents.mk (E.capping.coreInclusion y') = E.cutCapVertex a false then
      ⟨⟨E.capping.coreInclusion y', h⟩, hmem y' h⟩ else x₀
  have hgW : ∀ (y' : E.tubes.core)
      (h : ConnectedComponents.mk (E.capping.coreInclusion y') = E.cutCapVertex a false),
      g y' = ⟨⟨E.capping.coreInclusion y', h⟩, hmem y' h⟩ := fun y' h => by
    simp only [g, h, dite_true]
  have hgy : g y = x₀ := hgW y hyA
  let W : Set E.tubes.core := {y' | ConnectedComponents.mk (E.capping.coreInclusion y') =
    E.cutCapVertex a false}
  have hW : IsOpen W :=
    (ClosedOrientedManifold.isOpen_componentSet E.capped _).preimage
      E.capping.coreInclusion.continuous
  have hWy : W ∈ 𝓝 y := hW.mem_nhds hyA
  let L := ConnectedSumQuotient.interiorLeft (E.capComponentBallChart (a, false)).toBallChart
    (E.capComponentBallChart (a, true)).toBallChart boundaryAttachment.1
  have hKg : (K ∘ Subtype.val : E.tubes.core → _) =ᶠ[𝓝 y] (L ∘ g) := by
    filter_upwards [hWy] with y' hy'
    exact hK y' (g y') (by rw [hgW y' hy'])
  have hjg : (E.capping.coreInclusion : E.tubes.core → E.capped.Carrier) =ᶠ[𝓝 y]
      (Subtype.val ∘ (Subtype.val ∘ g)) := by
    filter_upwards [hWy] with y' hy'
    change E.capping.coreInclusion y' = (g y').val.val
    rw [hgW y' hy']
  obtain ⟨hi, hj, hpos⟩ := E.capping.core_positive y hint
  have hval : MDifferentiableAt (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier) y :=
    mdifferentiableAt_of_bijective hi
  have hjd : MDifferentiableAt (𝓡∂ 3) (𝓡 3) E.capping.coreInclusion y :=
    mdifferentiableAt_of_bijective hj
  have hKd : MDifferentiableAt (𝓡 3) (𝓡 3) K y.val := K.mdifferentiable (by simp) _
  have hgd : MDifferentiableAt (𝓡∂ 3) (𝓡 3) g y := by
    have h1 := hjd.congr_of_eventuallyEq hjg.symm
    rw [mdifferentiableAt_subtypeVal_comp_iff] at h1
    exact (mdifferentiableAt_subtypeVal_comp_iff (E.capComponentBallChart (a, false)).interior g
      y).mp h1
  let s := smoothConnectedSum (E.capped.component (E.cutCapVertex a false))
    (E.capped.component (E.cutCapVertex a true)) (E.capComponentBallChart (a, false))
    (E.capComponentBallChart (a, true)) boundaryAttachment
  let _ := s.charts
  let _ := s.smooth
  have hLd : MDifferentiableAt (𝓡 3) (𝓡 3) L (g y) :=
    (s.interiorLeft_localDiffeomorph (g y)).mdifferentiableAt (by simp)
  have h1 : mfderiv (𝓡∂ 3) (𝓡 3) (K ∘ Subtype.val) y =
      (mfderiv (𝓡 3) (𝓡 3) K y.val).comp (mfderiv (𝓡∂ 3) (𝓡 3) Subtype.val y) :=
    mfderiv_comp y hKd hval
  have h2 : mfderiv (𝓡∂ 3) (𝓡 3) (L ∘ g) y =
      (mfderiv (𝓡 3) (𝓡 3) L (g y)).comp (mfderiv (𝓡∂ 3) (𝓡 3) g y) :=
    mfderiv_comp y hLd hgd
  have h3 := hKg.mfderiv_eq (I := 𝓡∂ 3) (I' := 𝓡 3)
  have h4 : mfderiv (𝓡∂ 3) (𝓡 3) E.capping.coreInclusion y = mfderiv (𝓡∂ 3) (𝓡 3) g y := by
    rw [hjg.mfderiv_eq, Topology.mfderiv_subtypeVal_comp]
    exact Topology.mfderiv_subtypeVal_comp (E.capComponentBallChart (a, false)).interior g y
  have hKy : K y.val = L (g y) := hK y (g y) (by rw [hgy])
  have hlin : ∀ v : E3, mfderiv (𝓡 3) (𝓡 3) K y.val (mfderiv (𝓡∂ 3) (𝓡 3) Subtype.val y v) =
      mfderiv (𝓡 3) (𝓡 3) L (g y) (mfderiv (𝓡∂ 3) (𝓡 3) E.capping.coreInclusion y v) := by
    intro v
    have h5 := congrArg (fun f : E3 →L[ℝ] E3 => f v) (h1.symm.trans (h3.trans h2))
    rw [h4]
    exact h5
  let eV : E3 ≃ₗ[ℝ] E3 := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier) y).toLinearMap hi
  let eJ : E3 ≃ₗ[ℝ] E3 := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) (𝓡 3) E.capping.coreInclusion y).toLinearMap hj
  let eL : E3 ≃ₗ[ℝ] E3 :=
    ((s.interiorLeft_localDiffeomorph).mfderivToContinuousLinearEquiv (by simp) (g y)).toLinearEquiv
  let eK : E3 ≃ₗ[ℝ] E3 := (K.mfderivToContinuousLinearEquiv (by simp) y.val).toLinearEquiv
  have heK : eK = (eV.symm.trans eJ).trans eL := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨w, rfl⟩ := eV.surjective v
    change mfderiv (𝓡 3) (𝓡 3) K y.val (eV w) = eL (eJ (eV.symm (eV w)))
    rw [LinearEquiv.symm_apply_apply]
    exact hlin w
  have hpL := s.interiorLeft_preserves_orientation (g y)
  have hv : (g y).val.val = E.capping.coreInclusion y := by rw [hgy]
  let Oc : E.capped.Carrier → Orientation ℝ E3 (Fin 3) := fun q =>
    E.capped.orientation.orientation q
  have hcomp : ((E.capped.component (E.cutCapVertex a false)).orientation.orientation (g y).val :
      Orientation ℝ E3 (Fin 3)) = E.capped.orientation.orientation (E.capping.coreInclusion y) :=
    (ClosedOrientedManifold.componentTangentOrientation_apply E.capped
      (E.cutCapVertex a false) (g y).val).trans (congrArg Oc hv)
  refine Diffeomorph.preservesOrientation_of_eq_at K _ _ y.val ?_
  change Orientation.map (Fin 3) eK (M.orientation.orientation y.val : Orientation ℝ E3 (Fin 3)) =
    (s.orientation.orientation (K y.val) : Orientation ℝ E3 (Fin 3))
  let O : (PairedBallGluing.mergeFactor E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a boundaryAttachment none).Carrier →
        Orientation ℝ E3 (Fin 3) := fun q => s.orientation.orientation q
  have hO : (s.orientation.orientation (K y.val) : Orientation ℝ E3 (Fin 3)) =
      s.orientation.orientation (L (g y)) := congrArg O hKy
  rw [hO, heK]
  have step1 := orientation_map_trans' (eV.symm.trans eJ) eL
    (M.orientation.orientation y.val : Orientation ℝ E3 (Fin 3))
  have step2 : Orientation.map (Fin 3) (eV.symm.trans eJ)
      (M.orientation.orientation y.val : Orientation ℝ E3 (Fin 3)) =
        (E.capped.orientation.orientation (E.capping.coreInclusion y) :
          Orientation ℝ E3 (Fin 3)) := hpos
  refine step1.trans ?_
  rw [step2, ← hcomp]
  exact hpL

theorem orientedSingleSphere_of_ne {M : ConnectedClosedOrientedManifold.{u} 3}
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hsep : E.cutCapVertex a false ≠ E.cutCapVertex a true) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (E.capped.component (E.cutCapVertex a false))
        (E.capped.component (E.cutCapVertex a true))).toClosedOrientedManifold
      M.toClosedOrientedManifold) := by
  obtain ⟨K, hK⟩ := exists_mergeDiffeomorph_core E a hsep
  have hKo := mergeDiffeomorph_preservesOrientation E a K hK
  obtain ⟨F⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    (E.capComponentBallChart (a, false))
    (orientedBallChart (E.capped.component (E.cutCapVertex a false)))
    (E.capComponentBallChart (a, true))
    (orientedBallChart (E.capped.component (E.cutCapVertex a true))) boundaryAttachment
  let K' : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
      (PairedBallGluing.mergeFactor E.capped.component E.cutCapVertex
        (fun a t => E.capComponentBallChart (a, t)) a boundaryAttachment
          none).toClosedOrientedManifold := ⟨K, hKo⟩
  exact ⟨(K'.trans F).symm⟩

end GC.Seifert.RelativeNormalization
