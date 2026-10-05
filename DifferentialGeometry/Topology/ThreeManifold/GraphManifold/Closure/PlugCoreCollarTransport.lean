import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugSideCapping
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryCollarReversalTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePairingOrientation

/-!
The actual capped-side core is a partial diffeomorphism on the original core open set.
It transports the complete retained torus collar and its genuine positive interior point.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.GraphManifold.MixedBoundaryCertificate GC.Endpoint.CompactCarrier
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

local notation "B₀" => E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
local notation "D₀" => E.fibrePlugCutComponents h hlin hc hn d hs heq
local notation "D₁" => E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ
local notation "Cᵢ" i => E.plugComponentCutCarrier h hlin d hs heq hc hn i
local notation "Sᵢ" i => E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "Bᵢ" i => E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "Kᵢ" i => E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "port" => E.fibrePlugCutPortEquiv h hc hn

local instance plugCoreQuotientCharts :
    ChartedSpace (EuclideanHalfSpace 3) (B₀).SphereCapQuotient :=
  (B₀).sphereCapQuotientChartedSpace

local instance plugCoreCutNonempty (i : Fin 2) : Nonempty (Cᵢ i).Carrier :=
  ((D₀).connected i).toNonempty

local instance plugCoreCapNonempty (i : Fin 2) : Nonempty (Sᵢ i).Carrier :=
  ((D₁).connected i).toNonempty

private def plugCoreAmbient (i : Fin 2) :
    PartialDiffeomorph (boundedPlugCutCarrier d hs).model (B₀).sphereCapCarrier.model
      (boundedPlugCutCarrier d hs).Carrier (B₀).sphereCapCarrier.Carrier ∞ :=
  (B₀).sphereCapCoreOpenDiffeomorph (B₀).exists_sphereCapQuotientAtlas.choose_spec.2
    ((B₀).sphereCapRetainedPoint (port i))

private theorem plugCoreAmbient_source (i : Fin 2) :
    (E.plugCoreAmbient h d hs hI hc hn hρ hρ1 havρ i).source =
      (B₀).sphereCapCoreOpen :=
  (B₀).sphereCapCoreOpenDiffeomorph_source _ _

private theorem plugCoreAmbient_apply (i : Fin 2) (x : (boundedPlugCutCarrier d hs).Carrier)
    (hx : x ∈ (B₀).sphereCapCoreOpen) :
    E.plugCoreAmbient h d hs hI hc hn hρ hρ1 havρ i x = (B₀).sphereCapCore x :=
  (B₀).sphereCapCoreOpenDiffeomorph_apply _ _ hx

private def plugCoreComponentAmbient (i : Fin 2) :
    PartialDiffeomorph (Cᵢ i).model (B₀).sphereCapCarrier.model
      (Cᵢ i).Carrier (B₀).sphereCapCarrier.Carrier ∞ :=
  (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    (boundedPlugCutCarrier d hs).model ((D₀).piece i) ((D₀).connected i).toNonempty).trans
      (E.plugCoreAmbient h d hs hI hc hn hρ hρ1 havρ i)

private theorem plugCoreComponentAmbient_source (i : Fin 2) :
    (E.plugCoreComponentAmbient h hlin d hs hI heq hc hn hρ hρ1 havρ i).source =
      Subtype.val ⁻¹' (B₀).sphereCapCoreOpen := by
  ext x
  change (x ∈ univ ∧ x.val ∈
    (E.plugCoreAmbient h d hs hI hc hn hρ hρ1 havρ i).source) ↔ _
  rw [E.plugCoreAmbient_source h d hs hI hc hn hρ hρ1 havρ i]
  exact and_iff_right (mem_univ x)

private theorem plugCoreComponentAmbient_apply (i : Fin 2) (x : (Cᵢ i).Carrier)
    (hx : x.val ∈ (B₀).sphereCapCoreOpen) :
    E.plugCoreComponentAmbient h hlin d hs hI heq hc hn hρ hρ1 havρ i x =
      (B₀).sphereCapCore x.val :=
  E.plugCoreAmbient_apply h d hs hI hc hn hρ hρ1 havρ i x.val hx

private theorem plugCoreComponentAmbient_owned (i : Fin 2) :
    (E.plugCoreComponentAmbient h hlin d hs hI heq hc hn hρ hρ1 havρ i).target ⊆
      (D₁).piece i := by
  let P := E.plugCoreComponentAmbient h hlin d hs hI heq hc hn hρ hρ1 havρ i
  intro y hy
  let x := P.symm y
  have hx : x ∈ P.source := P.map_target hy
  have hxopen : x.val ∈ (B₀).sphereCapCoreOpen :=
    (E.plugCoreComponentAmbient_source h hlin d hs hI heq hc hn hρ hρ1 havρ i).subset hx
  have he := E.plugCoreComponentAmbient_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i x hxopen
  have hr : P x = y := P.right_inv hy
  rw [← hr, he]
  exact (E.fibrePlugCapComponents_core_mem h hlin hc hn d hs heq hρ hρ1 hI havρ i x.val).mpr
    x.property

def plugCoreCollarTransport (i : Fin 2) :
    PartialDiffeomorph (Cᵢ i).model (Sᵢ i).model (Cᵢ i).Carrier (Sᵢ i).Carrier ∞ :=
  codRestrictOpens (E.plugCoreComponentAmbient h hlin d hs hI heq hc hn hρ hρ1 havρ i)
    ((D₁).piece i) ((D₁).connected i).toNonempty

theorem plugCoreCollarTransport_source (i : Fin 2) :
    (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i).source =
      Subtype.val ⁻¹' (B₀).sphereCapCoreOpen := by
  rw [plugCoreCollarTransport, codRestrictOpens_source]
  · exact E.plugCoreComponentAmbient_source h hlin d hs hI heq hc hn hρ hρ1 havρ i
  · exact E.plugCoreComponentAmbient_owned h hlin d hs hI heq hc hn hρ hρ1 havρ i

theorem plugCoreCollarTransport_apply (i : Fin 2) (x : (Cᵢ i).Carrier)
    (hx : x ∈ (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i).source) :
    E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i x = (Kᵢ i).core x := by
  have hxopen : x.val ∈ (B₀).sphereCapCoreOpen :=
    (E.plugCoreCollarTransport_source h hlin d hs hI heq hc hn hρ hρ1 havρ i).subset hx
  apply Subtype.ext
  change (codRestrictOpens
    (E.plugCoreComponentAmbient h hlin d hs hI heq hc hn hρ hρ1 havρ i)
    ((D₁).piece i) _ x).val = _
  have hxP := (E.plugCoreComponentAmbient_source h hlin d hs hI heq hc hn
    hρ hρ1 havρ i).symm.subset hxopen
  have htP := E.plugCoreComponentAmbient_owned h hlin d hs hI heq hc hn
    hρ hρ1 havρ i
  exact (codRestrictOpens_apply
    (I := (Cᵢ i).model) (J := (B₀).sphereCapCarrier.model)
    (E.plugCoreComponentAmbient h hlin d hs hI heq hc hn hρ hρ1 havρ i)
    ((D₁).piece i) ((D₁).connected i).toNonempty
    (htP ((E.plugCoreComponentAmbient h hlin d hs hI heq hc hn
      hρ hρ1 havρ i).map_source hxP))).trans
    (E.plugCoreComponentAmbient_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i x hxopen)

theorem plugCoreCollarTransport_torus_target (i : Fin 2) :
    ((Bᵢ i).tori.collar 0).target ⊆
      (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i).source := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := ((Bᵢ i).tori.collar 0).image_source_eq_target.symm ▸ hx
  have hp' : p ∈ halfCollarSource := ((Bᵢ i).tori.source_eq 0).subset hp
  apply (E.plugCoreCollarTransport_source h hlin d hs hI heq hc hn hρ hρ1 havρ i).symm.subset
  change ((Bᵢ i).tori.collar 0 p).val ∈ (B₀).sphereCapCoreOpen
  rw [E.plugSideBoundary_torus_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i p hp']
  exact (B₀).torus_collar_mem_sphereCapCoreOpen (port i) p hp'

theorem plugCoreCollarTransport_collar_source (i : Fin 2) :
    (((Bᵢ i).tori.collar 0).trans
      (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i)).source =
        halfCollarSource := by
  ext p
  change (p ∈ ((Bᵢ i).tori.collar 0).source ∧
    (Bᵢ i).tori.collar 0 p ∈
      (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i).source) ↔ _
  rw [(Bᵢ i).tori.source_eq 0]
  exact ⟨And.left, fun hp => ⟨hp,
    E.plugCoreCollarTransport_torus_target h hlin d hs hI heq hc hn hρ hρ1 havρ i
      (((Bᵢ i).tori.collar 0).map_source ((Bᵢ i).tori.source_eq 0 |>.symm.subset hp))⟩⟩

theorem plugCoreCollarTransport_collar_apply (i : Fin 2)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    (((Bᵢ i).tori.collar 0).trans
      (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i)) p =
        (Kᵢ i).retained.collar 0 p := by
  change E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i
    ((Bᵢ i).tori.collar 0 p) = _
  rw [E.plugCoreCollarTransport_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i]
  · exact ((Kᵢ i).retained_collar 0 p hp).symm
  · exact E.plugCoreCollarTransport_torus_target h hlin d hs hI heq hc hn hρ hρ1 havρ i
      (((Bᵢ i).tori.collar 0).map_source ((Bᵢ i).tori.source_eq 0 |>.symm.subset hp))

theorem plugCoreCollarTransport_positive (i : Fin 2) :
    ∃ A : TangentSpace (Cᵢ i).model
        ((Bᵢ i).tori.collar 0 (torusBase, halfPoint (1 / 2) (by norm_num))) ≃ₗ[ℝ]
        TangentSpace (Sᵢ i).model
        (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i
          ((Bᵢ i).tori.collar 0 (torusBase, halfPoint (1 / 2) (by norm_num)))),
      (∀ v, A v = mfderiv (Cᵢ i).model (Sᵢ i).model
        (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i)
        ((Bᵢ i).tori.collar 0 (torusBase, halfPoint (1 / 2) (by norm_num))) v) ∧
      Orientation.map (Fin 3) A ((Cᵢ i).orientation.orientation
        ((Bᵢ i).tori.collar 0 (torusBase, halfPoint (1 / 2) (by norm_num)))) =
        (Sᵢ i).orientation.orientation
        (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i
          ((Bᵢ i).tori.collar 0 (torusBase, halfPoint (1 / 2) (by norm_num)))) := by
  let p : Torus × EuclideanHalfSpace 1 := (torusBase, halfPoint (1 / 2) (by norm_num))
  let x := (Bᵢ i).tori.collar 0 p
  let τ := E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i
  have hp : p ∈ halfCollarSource := by change (1 / 2 : ℝ) < 1; norm_num
  have hx : x ∈ τ.source :=
    E.plugCoreCollarTransport_torus_target h hlin d hs hI heq hc hn hρ hρ1 havρ i
      (((Bᵢ i).tori.collar 0).map_source ((Bᵢ i).tori.source_eq 0 |>.symm.subset hp))
  have hloc := ((Bᵢ i).tori.collar 0).isLocalDiffeomorphAt halfCollarModel (Cᵢ i).model ∞
    ((Bᵢ i).tori.source_eq 0 |>.symm.subset hp)
  have hxp : (Cᵢ i).model.IsInteriorPoint x :=
    (hloc.isInteriorPoint_iff (by simp)).mp
      (halfCollarModel_isInteriorPoint' (by change (0 : ℝ) < 1 / 2; norm_num))
  obtain ⟨hb, ho⟩ := (Kᵢ i).core_positive x hxp
  have he : τ =ᶠ[nhds x] (Kᵢ i).core := by
    filter_upwards [τ.open_source.mem_nhds hx] with y hy
    exact E.plugCoreCollarTransport_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i y hy
  have hd := he.mfderiv_eq (I := (Cᵢ i).model) (I' := (Sᵢ i).model)
  have hbτ : Bijective (mfderiv (Cᵢ i).model (Sᵢ i).model τ x) := hd ▸ hb
  refine ⟨LinearEquiv.ofBijective
    (mfderiv (Cᵢ i).model (Sᵢ i).model τ x).toLinearMap hbτ, fun v => rfl, ?_⟩
  have hLE : LinearEquiv.ofBijective
      (mfderiv (Cᵢ i).model (Sᵢ i).model τ x).toLinearMap hbτ =
      LinearEquiv.ofBijective
        (mfderiv (Cᵢ i).model (Sᵢ i).model (Kᵢ i).core x).toLinearMap hb := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => L v) hd
  rw [hLE, E.plugCoreCollarTransport_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i x hx]
  exact ho

theorem plugCoreCollarTransport_collar_target (i : Fin 2) :
    (((Bᵢ i).tori.collar 0).trans
      (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i)).target =
        ((Kᵢ i).retained.collar 0).target := by
  let A := ((Bᵢ i).tori.collar 0).trans
    (E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i)
  let R := (Kᵢ i).retained.collar 0
  rw [← A.image_source_eq_target, ← R.image_source_eq_target]
  rw [E.plugCoreCollarTransport_collar_source h hlin d hs hI heq hc hn hρ hρ1 havρ i,
    (Kᵢ i).retained.source_eq 0]
  apply image_congr
  intro p hp
  exact E.plugCoreCollarTransport_collar_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i p hp

variable {E h hlin d hs hI heq hc hn hρ hρ1 havρ}

theorem plugCoreCollarTransport_reversal_iff {i : Fin 2} {C1 : CompactCarrier.{u}}
    {hC1 : C1.kind = .withBoundary} [Nonempty C1.Carrier]
    {l : PartialDiffeomorph halfCollarModel C1.model
      (Torus × EuclideanHalfSpace 1) C1.Carrier ∞}
    (hl : l.source = halfCollarSource) {f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus} :
    ReversesBoundaryOrientation (withBoundarySum C1 (Cᵢ i) hC1 rfl)
      (l.trans (withBoundarySumLeft C1 (Cᵢ i) hC1 rfl))
      (fun p => (((Bᵢ i).tori.collar 0).trans
        (withBoundarySumRight C1 (Cᵢ i) hC1 rfl)) (f p.1, p.2)) ↔
    ReversesBoundaryOrientation (withBoundarySum C1 (Sᵢ i) hC1 rfl)
      (l.trans (withBoundarySumLeft C1 (Sᵢ i) hC1 rfl))
      (fun p => (((Kᵢ i).retained.collar 0).trans
        (withBoundarySumRight C1 (Sᵢ i) hC1 rfl)) (f p.1, p.2)) := by
  let τ := E.plugCoreCollarTransport h hlin d hs hI heq hc hn hρ hρ1 havρ i
  have hcR := boundaryCollarReversalTransport (C1 := C1) (C2 := Cᵢ i) (D := Sᵢ i)
    (hC1 := hC1) (hC2 := rfl) (hD := rfl) (l := l) (hl := hl)
    (r := (Bᵢ i).tori.collar 0) (hr := (Bᵢ i).tori.source_eq 0) (τ := τ)
    (ht := E.plugCoreCollarTransport_torus_target h hlin d hs hI heq hc hn hρ hρ1 havρ i)
    (f := f)
    (hpos := E.plugCoreCollarTransport_positive h hlin d hs hI heq hc hn hρ hρ1 havρ i)
  have he : EqOn
      (fun p => ((((Bᵢ i).tori.collar 0).trans τ).trans
        (withBoundarySumRight C1 (Sᵢ i) hC1 rfl)) (f p.1, p.2))
      (fun p => (((Kᵢ i).retained.collar 0).trans
        (withBoundarySumRight C1 (Sᵢ i) hC1 rfl)) (f p.1, p.2)) halfCollarSource := by
    intro p hp
    apply congrArg (withBoundarySumRight C1 (Sᵢ i) hC1 rfl)
    exact E.plugCoreCollarTransport_collar_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
      (f p.1, p.2) hp
  constructor
  · intro hrev
    exact reversesBoundaryOrientation_congrOn (hcR.mp hrev) (eqOn_refl _ _) he
  · intro hrev
    exact hcR.mpr (reversesBoundaryOrientation_congrOn hrev (eqOn_refl _ _) he.symm)

end GC.Seifert.ElementaryPresentation
