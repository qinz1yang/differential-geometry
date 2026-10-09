import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryCappingFactorMaps
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MarkedRestorationOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs

/-!
The same actual cap component chart becomes an oriented ball chart after physical restoration.
Its source, all subset images and the radial exterior point keep the original chosen chart.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u
namespace GC.Seifert.ElementaryPresentation
variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)
  (i : Fin 2) (M : ConnectedClosedOrientedManifold.{u} 3)
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
    (PlaneLift.{u} × Circle) M.Carrier ∞)
  (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)


local notation "Sᵢ" => E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "Pᵢ" => E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i

variable (K : CompactCarrier.{u}) (hK : K.kind = .withBoundary)
  (ι : K.Carrier → M.Carrier) (Γ : BoundaryTori K 1)
  (hι : ContMDiff K.model (𝓡 3) ∞ ι)
  (hΓ : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
    ι (Γ.collar 0 p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
  (hO : ∀ x, ∃ H : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
    H.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
    Orientation.map (Fin 3) H.toLinearEquiv (K.orientation.orientation x) =
      M.orientation.orientation (ι x))
  (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ
    i).model⟯ (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).Carrier)
  (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (ε : Bool)

variable (hrev :
  let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
  let : Nonempty (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).Carrier :=
    ⟨(E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i).chart 0⟩
  ReversesBoundaryOrientation (withBoundarySum K (E.plugComponentCapCarrier h hlin d hs hI heq
    hc hn hρ hρ1 havρ i) hK rfl)
    (boundaryPortLeftCollar K (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i)
    hK rfl Γ)
    (fun p => boundaryPortRightCollar K (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ
    hρ1 havρ i) hK rfl (markedSolidBoundary (E.plugComponentCapCarrier h hlin d hs hI heq hc hn
    hρ hρ1 havρ i) g ψ) 0
      (markedRestorationMatching ψ ε p.1, p.2)))

private theorem restoredPlugOrientation_point
    (N : ConnectedClosedOrientedManifold.{u} 3) (x y : N.Carrier) (hxy : x = y) :
    N.orientation.orientation x = N.orientation.orientation y := by
  subst y
  rfl

include h3 hι hΓ hO hrev in
theorem exists_restoredPlugOrientedBallChart :
    ∃ c : OrientedBallChart M.toClosedOrientedManifold,
      c.chart.source = Metric.ball 0 (5 / 2) ∧
      (∀ x, c.chart x = regularFibreRestorationFill M φ
        ((markedRestorationSolidMap (Sᵢ) g ε).symm ((Pᵢ).chart x))) ∧
      (∀ A : Set (EuclideanSpace ℝ (Fin 3)), c.chart '' A =
        (regularFibreRestorationFill M φ ∘ (markedRestorationSolidMap (Sᵢ) g ε).symm) ''
          ((Pᵢ).chart '' A)) ∧
      ∀ t : Torus, φ (ULift.up ((5 / 4 : ℝ) • (t.1 : ℂ)), t.2) ∈ c.toBallChart.interior := by
  let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
  let : Nonempty (Sᵢ).Carrier := ⟨(E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1
    havρ i).chart 0⟩
  obtain ⟨c, hcs, hcx, hcimage, hrad⟩ := E.exists_restoredPlugCapBallChart
    h hlin d hs hI heq hc hn hρ hρ1 havρ i M φ h3 g ε
  have hpositive : ∀ x, ∀ hx : x ∈ c.chart.source,
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv c.chart hx)
        (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
          (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation) =
        M.orientation.orientation (c.chart x) := by
    intro x hx
    have hp : x ∈ (Pᵢ).chart.source :=
      (E.plugComponentCapChart_source h hlin d hs hI heq hc hn hρ hρ1 havρ i).symm.subset
        (hcs.subset hx)
    let f := markedRestorationFill M φ (Sᵢ) g ε
    obtain ⟨H, hH, hHO⟩ := markedRestorationFill_positive M φ h3 K (Sᵢ) hK rfl
      ι Γ hι hΓ hO g ψ ε hrev ((Pᵢ).chart x)
    have hf : (c.chart : EuclideanSpace ℝ (Fin 3) → M.Carrier) = f ∘ (Pᵢ).chart :=
      funext hcx
    have hd : mfderiv (𝓡 3) (𝓡 3) c.chart x =
        (mfderiv (Sᵢ).model (𝓡 3) f ((Pᵢ).chart x)).comp
          (mfderiv (𝓡 3) (Sᵢ).model (Pᵢ).chart x) := by
      rw [hf]
      exact mfderiv_comp x
        ((markedRestorationFill_smooth M φ h3 (Sᵢ) g ε).mdifferentiableAt (by simp))
        ((Pᵢ).chart.mdifferentiableAt (by simp) hp)
    let H' : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := H.toLinearEquiv
    have hchain : carrierSurgeryPatchTangentEquiv c.chart hx =
        (carrierSurgeryPatchTangentEquiv (Pᵢ).chart hp).trans H' := by
      apply LinearEquiv.ext
      intro v
      change mfderiv (𝓡 3) (𝓡 3) c.chart x v =
        H.toContinuousLinearMap (mfderiv (𝓡 3) (Sᵢ).model (Pᵢ).chart x v)
      rw [hH]
      exact congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L v) hd
    have hstd : ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
        (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation =
        sphereCapEuclideanOrientation := by
      have hb : (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
          (NormedSpace.fromTangentSpace x).symm.toLinearEquiv =
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis := by
        ext k
        rfl
      exact congrArg Module.Basis.orientation hb
    have hP := E.plugComponentCapChart_positive h hlin d hs hI heq hc hn hρ hρ1 havρ i x hp
    have hH'O : Orientation.map (Fin 3) H' ((Sᵢ).orientation.orientation ((Pᵢ).chart x)) =
        M.orientation.orientation (f ((Pᵢ).chart x)) := hHO
    have htrans := DifferentialGeometry.orientation_map_trans
      (carrierSurgeryPatchTangentEquiv (Pᵢ).chart hp) H' sphereCapEuclideanOrientation
    have hmid := congrArg
      (fun o : Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3) =>
        Orientation.map (Fin 3) H' o) hP
    have ht : M.orientation.orientation (f ((Pᵢ).chart x)) =
        M.orientation.orientation (c.chart x) := by
      have hpoint : f ((Pᵢ).chart x) = c.chart x := (hcx x).symm
      exact restoredPlugOrientation_point M _ _ hpoint
    have hstart := congrArg
      (fun o : Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3) =>
        Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv c.chart hx) o) hstd
    have hLE := congrArg (fun L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ]
        EuclideanSpace ℝ (Fin 3) => Orientation.map (Fin 3) L sphereCapEuclideanOrientation) hchain
    exact hstart.trans (hLE.trans (htrans.trans (hmid.trans (hH'O.trans ht))))
  let c' : OrientedBallChart M.toClosedOrientedManifold :=
    { toBallChart := c
      preserves_orientation := hpositive }
  exact ⟨c', hcs, hcx, hcimage, hrad⟩

end GC.Seifert.ElementaryPresentation
