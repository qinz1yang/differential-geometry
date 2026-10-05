import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugConnected
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugMarkedRestoration
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugComponentCapCollarGerm
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugComponentCapCharts

/-!
# Chapter-14 assembly, relative COMPARE G4: the bounded fibre plug is a solid-cap plug

Lane ASM-L2e, group G4. The bounded fibre plug of the tree (`exists_connectedFibrePlug`: a pants
product filled along its fibre, `Raw` by `ElementaryPresentation.toRaw`, connected, with boundary),
cut along its bounded split sphere (`exists_boundedSplitSignedTube`), is an inhabitant of
`SolidCapPlug` (`exists_fibreSolidCapPlug`):

* the cut is the concrete bounded cut (`boundedSphereCutCapped`), its pieces the two capped
  components `fibrePlugCapComponents`;
* the solid tori are `exists_boundedPlugMeridionalDiffeomorph` (true side = component `0`);
* the cap ball charts are the plug cap charts `plugCapAmbientChart` precomposed with the linear
  extension of their attaching map (`capBallAmbientExtension`, the identity or `-id`), which turns
  the collar germ `exists_plugComponentCapCollarGerm` into the germ without attaching map;
* the ports are `fibrePlugSideExternalEquiv`, the markings `boundedPlugMeridionalMarking`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The linear extension of the attaching map of a cap is an involution. -/
theorem capBallAmbientExtension_involutive {C : CompactCarrier.{u}}
    (B : MixedBoundaryCertificate C) (i : Fin B.sphereCount) (x : E3) :
    B.capBallAmbientExtension i (B.capBallAmbientExtension i x) = x := by
  rcases B.capBallAmbientExtension_choices i with h | h
  · rw [h]
    rfl
  · rw [h]
    change -(-x) = x
    exact neg_neg x

theorem capBallAmbientExtension_smul {C : CompactCarrier.{u}}
    (B : MixedBoundaryCertificate C) (i : Fin B.sphereCount) (r : ℝ) (x : E3) :
    B.capBallAmbientExtension i (r • x) = r • B.capBallAmbientExtension i x := by
  rcases B.capBallAmbientExtension_choices i with h | h
  · rw [h]
    rfl
  · rw [h]
    change -(r • x) = r • -x
    exact (smul_neg r x).symm

theorem capBallAmbientExtension_sphere {C : CompactCarrier.{u}}
    (B : MixedBoundaryCertificate C) (i : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.capBallAmbientExtension i z.down.val = (B.sphereCapOrientationData.attaching i z).down.val := by
  have hv := B.capBallAmbientExtension_cell i (closureSphereToBall z)
  rw [B.sphereCapOrientationData.boundary] at hv
  exact hv

end GC.GraphManifold.Assembly

namespace GC.Seifert.ElementaryPresentation

open GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

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

theorem fibrePlug_boundary_eq :
    W.model.boundary W.Carrier = (E.toTorus.external.shrink hρ hρ1).image :=
  E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm

/-- The bounded fibre plug cut along its split sphere. -/
abbrev fibrePlugSphereCut : SphereCutCapped W (boundedSphereSeam d hs hI)
    (E.toTorus.external.shrink hρ hρ1) :=
  boundedSphereCutCapped d hs hI (E.toTorus.external.shrink hρ hρ1)
    (E.fibrePlug_boundary_eq hρ hρ1) havρ

/-- The normalized cap ball chart of side `i` (no attaching map). -/
def fibrePlugCapChart (i : Fin 2) :
    PartialDiffeomorph (𝓡 3) (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model
      E3 (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.Carrier ∞ :=
  ((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).capBallAmbientExtension i).toPartialDiffeomorph.trans
    (E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i)

theorem fibrePlugCapChart_apply (i : Fin 2) (x : E3) :
    E.fibrePlugCapChart h hlin d hs hI heq hρ hρ1 havρ i x =
      E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i
        ((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).capBallAmbientExtension i x) := rfl

theorem fibrePlugCapChart_source (i : Fin 2) :
    closedBall (0 : E3) 2 ⊆ (E.fibrePlugCapChart h hlin d hs hI heq hρ hρ1 havρ i).source := by
  intro x hx
  refine ⟨mem_univ _, ?_⟩
  change _ ∈ (boundedPlugCapBallChart d hs hI (E.toTorus.external.shrink hρ hρ1)
    (E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm)
    havρ E h hlin heq i).source
  rw [boundedPlugCapBallChart_source, mem_ball_zero_iff]
  have hn : ‖(E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).capBallAmbientExtension i x‖ = ‖x‖ :=
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).capBallAmbientExtension_norm i x
  have := mem_closedBall_zero_iff.mp hx
  exact lt_of_eq_of_lt hn (by linarith)

theorem fibrePlugCapChart_target_subset (i : Fin 2) :
    (E.fibrePlugCapChart h hlin d hs hI heq hρ hρ1 havρ i).target ⊆
      (E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i).target := fun _ hy => hy.1

theorem fibrePlugCapChart_unit (i : Fin 2) :
    E.fibrePlugCapChart h hlin d hs hI heq hρ hρ1 havρ i '' closedBall 0 1 =
      range ((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapReparameterizedCap i) := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
  let A := E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i
  have hunit : A '' closedBall 0 1 = range (B.sphereCapReparameterizedCap i) :=
    boundedPlugCapBallChart_closedUnit_image d hs hI (E.toTorus.external.shrink hρ hρ1)
      (E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm)
      havρ E h hlin heq i
  rw [← hunit]
  have hnorm : ∀ x : E3, ‖B.capBallAmbientExtension i x‖ = ‖x‖ :=
    fun x => B.capBallAmbientExtension_norm i x
  have hinv : ∀ x : E3, B.capBallAmbientExtension i (B.capBallAmbientExtension i x) = x :=
    fun x => capBallAmbientExtension_involutive B i x
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨B.capBallAmbientExtension i x, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, hnorm]
    exact mem_closedBall_zero_iff.mp hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨B.capBallAmbientExtension i x, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, hnorm]
      exact mem_closedBall_zero_iff.mp hx
    · change A (B.capBallAmbientExtension i (B.capBallAmbientExtension i x)) = A x
      rw [hinv]

theorem fibrePlugCapChart_germ {η : ℝ} (hη : η ≤ 1 / 4)
    (hg : ∀ (i : Fin 2) (z : ClosureSphere.{u}) (r : ℝ) (hr : 1 ≤ r), r < 1 + η →
      (E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i).chart
          (r • z.down.val) =
        (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).core
          ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).sphere 0
            ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).attaching 0 z,
              halfPoint (2 * r - 2) (by linarith))))
    (i : Fin 2) (z : sphere (0 : E3) 1) (r : ℝ) (hr : 1 ≤ r) (hrη : r < 1 + η) :
    E.fibrePlugCapChart h hlin d hs hI heq hρ hρ1 havρ i (r • (z : E3)) =
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCore
        ((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphere i
          (ULift.up z, halfPoint (2 * r - 2) (by linarith))) := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
  let R := B.capBallAmbientExtension i
  have hRz : ‖R (z : E3)‖ = 1 :=
    (B.capBallAmbientExtension_norm i (z : E3)).trans (mem_sphere_zero_iff_norm.mp z.property)
  let z' : ClosureSphere.{u} := ULift.up ⟨R (z : E3), mem_sphere_zero_iff_norm.mpr hRz⟩
  have hatt : B.sphereCapOrientationData.attaching i z' = ULift.up z := by
    apply ULift.ext
    apply Subtype.ext
    rw [← capBallAmbientExtension_sphere B i z']
    exact capBallAmbientExtension_involutive B i (z : E3)
  have hball : r • z'.down.val ∈ Metric.ball (0 : E3) (5 / 2) := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
      show ‖z'.down.val‖ = 1 from hRz]
    linarith
  have hhalf : (B.sphereCapOrientationData.attaching i z', halfPoint (2 * r - 2) (by linarith)) ∈
      sphereHalfCollarSource := by
    change 2 * r - 2 < 1
    linarith
  have h1 := congrArg Subtype.val (hg i z' r hr hrη)
  rw [E.plugSideCapping_core, E.plugSideBoundary_sphere_apply h hlin d hs hI heq hc hn hρ hρ1
    havρ i _ (by rw [E.plugSideCapping_attaching]; exact hhalf), E.plugSideCapping_attaching] at h1
  change (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i (r • z'.down.val)).val = _
    at h1
  rw [E.plugComponentCapChart_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i _ hball, hatt] at h1
  have hR : R (r • (z : E3)) = r • z'.down.val := capBallAmbientExtension_smul B i r (z : E3)
  have h2 : E.fibrePlugCapChart h hlin d hs hI heq hρ hρ1 havρ i (r • (z : E3)) =
      E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i (r • z'.down.val) := by
    change E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i (R (r • (z : E3))) = _
    rw [hR]
  exact h2.trans h1

end GC.Seifert.ElementaryPresentation

namespace GC.GraphManifold.Assembly

/-- **The bounded fibre plug is a solid-cap plug** (producer of `SolidCapPlug`). -/
theorem exists_fibreSolidCapPlug :
    ∃ (P : CompactCarrier.{u}) (_ : SolidCapPlug P), Nonempty (RawGraphPresentation P) ∧
      P.kind = .withBoundary ∧ ConnectedSpace P.Carrier := by
  obtain ⟨P, E, j, hconn, hPk, hc, hn, -, h, hlin⟩ := exists_connectedFibrePlug.{u}
  obtain ⟨d, hs, hI, heq, ρ, hρ, hρ1, hav⟩ := E.exists_boundedSplitSignedTube j true h hlin
  have havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target :=
    fun r => (hav r).symm
  obtain ⟨ε₀, f₀, -, σ₀, hσ₀, -, hc₀, -, -⟩ :=
    E.exists_boundedPlugMeridionalDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ true
  obtain ⟨ε₁, f₁, -, σ₁, hσ₁, -, hc₁, -, -⟩ :=
    E.exists_boundedPlugMeridionalDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ false
  obtain ⟨η, hη, hη1, hg⟩ :=
    E.exists_plugComponentCapCollarGerm h hlin d hs hI heq hc hn hρ hρ1 havρ
  have hport : Bijective (fun t : Fin 2 => Fin.cases (motive := fun _ => Fin E.toTorus.externalCount)
        (E.fibrePlugSideExternalEquiv h hc hn true)
      (fun _ => E.fibrePlugSideExternalEquiv h hc hn false) t) := by
    constructor
    · intro a a' haa
      fin_cases a <;> fin_cases a'
      · rfl
      · exact absurd ((E.fibrePlugSideExternalEquiv h hc hn).injective haa) (by decide)
      · exact absurd ((E.fibrePlugSideExternalEquiv h hc hn).injective haa) (by decide)
      · rfl
    · intro k
      obtain ⟨b', rfl⟩ := (E.fibrePlugSideExternalEquiv h hc hn).surjective k
      cases b'
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  have hcover : ((E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece (0 : Fin 2) :
      Set (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.Carrier) ∪
        (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece (1 : Fin 2) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, ((E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece i :
        Set (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.Carrier) :=
      (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).covers.symm ▸ mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  refine ⟨P,
    { seam := boundedSphereSeam d hs hI
      portCount := E.toTorus.externalCount
      ports := E.toTorus.external.shrink hρ hρ1
      cut := E.fibrePlugSphereCut d hs hI hρ hρ1 havρ
      piece := (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece
      piece_disjoint := (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).disjoint
        (show (0 : Fin 2) ≠ 1 by decide)
      piece_cover := hcover
      solid := fun t => Fin.cases (motive := fun t => solidSet.{u} ≃ₘ⟮𝓡∂ 3,
          (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model⟯
          ↥((E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece t)) f₀
        (Fin.cases (motive := fun k => solidSet.{u} ≃ₘ⟮𝓡∂ 3,
          (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model⟯
          ↥((E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece k.succ)) f₁
          (fun k => k.elim0)) t
      capChart := fun t => E.fibrePlugCapChart h hlin d hs hI heq hρ hρ1 havρ t
      capChart_source := fun t => E.fibrePlugCapChart_source h hlin d hs hI heq hρ hρ1 havρ t
      capChart_piece := fun t =>
        (E.fibrePlugCapChart_target_subset h hlin d hs hI heq hρ hρ1 havρ t).trans
          (E.plugCapAmbientChart_target_owned h hlin d hs hI heq hc hn hρ hρ1 havρ t)
      capChart_interior := fun t =>
        (E.fibrePlugCapChart_target_subset h hlin d hs hI heq hρ hρ1 havρ t).trans
          (boundedPlugCapBallChart_target_interior d hs hI (E.toTorus.external.shrink hρ hρ1)
            (E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm)
            havρ E h hlin heq t)
      capChart_unit := fun t => E.fibrePlugCapChart_unit h hlin d hs hI heq hρ hρ1 havρ t
      germ := η
      germ_pos := hη
      germ_le := hη1
      capChart_germ := fun t z r hr hrη =>
        E.fibrePlugCapChart_germ h hlin d hs hI heq hc hn hρ hρ1 havρ hη1 hg t z r hr hrη
      port := fun t => Fin.cases (motive := fun _ => Fin E.toTorus.externalCount)
        (E.fibrePlugSideExternalEquiv h hc hn true)
        (fun _ => E.fibrePlugSideExternalEquiv h hc hn false) t
      port_bijective := hport
      marking := fun t => Fin.cases (motive := fun _ => Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
        (E.boundedPlugMeridionalMarking h hlin ε₀)
        (fun _ => E.boundedPlugMeridionalMarking h hlin ε₁) t
      depth := min σ₀ σ₁
      depth_pos := lt_min hσ₀ hσ₁
      solid_collar := ?_
      boundary_eq := E.fibrePlug_boundary_eq hρ hρ1 }, ⟨E.toRaw⟩, hPk, hconn⟩
  intro t p s hs0 hsd
  fin_cases t
  · have h0 := hc₀ p s hs0 (lt_of_lt_of_le hsd (min_le_left _ _))
    cases ε₀ <;> exact h0
  · have h1 := hc₁ p s hs0 (lt_of_lt_of_le hsd (min_le_right _ _))
    cases ε₁ <;> exact h1

end GC.GraphManifold.Assembly
