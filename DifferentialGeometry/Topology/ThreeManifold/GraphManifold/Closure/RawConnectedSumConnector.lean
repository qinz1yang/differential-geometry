import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestoredPlugCoreInterior
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestoredFactorPointOrientation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawPhysicalExcisionData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugSphereCollarCoordinates
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugPuncturedFactorBoundary
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestoredPlugRadialCoordinates
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ConnectedSumSphereCollarRegularity
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.DoubleBoundaryTorusCoordinates
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestoredFactorInteriorRegularity
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.DoubleBoundaryFoldGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CanonicalRestoredPlugData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugPhysicalFactorAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ConnectedSumFixedFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugConnected
/-!
Physical fibre excisions and the same twice-glued plug quotient give the fixed oriented connected
sum. Both puncture interiors, the signed sphere collar and a physical positive derivative are
constructed before transporting the resulting raw graph presentation.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold.RelativeSphereCapping
open scoped Manifold ContDiff Topology
universe u
namespace GC.GraphManifold
variable (M0 M1 : ConnectedClosedOrientedManifold.{u} 3)
  (φ0 : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
    (PlaneLift.{u} × Circle) M0.Carrier ∞)
  (h30 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ0.source)
  (K0 : CompactCarrier.{u}) (ι0 : K0.Carrier → M0.Carrier) (Γ0 : BoundaryTori K0 1)
  (hK0 : K0.kind = .withBoundary) [ConnectedSpace K0.Carrier]
  (hι0 : IsSmoothEmbedding K0.model (𝓡 3) ∞ ι0)
  (hr0 : range ι0 = (φ0 '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ)
  (hΓ0 : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
    ι0 (Γ0.collar 0 p) = φ0 (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
  (hb0 : K0.model.boundary K0.Carrier = Γ0.image)
  (hbij0 : ∀ x, Bijective (mfderiv K0.model (𝓡 3) ι0 x))
  (hO0 : ∀ x, ∃ H : TangentSpace K0.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι0 x),
    H.toContinuousLinearMap = mfderiv K0.model (𝓡 3) ι0 x ∧
    Orientation.map (Fin 3) H.toLinearEquiv (K0.orientation.orientation x) =
      M0.orientation.orientation (ι0 x))
  (φ1 : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
    (PlaneLift.{u} × Circle) M1.Carrier ∞)
  (h31 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ1.source)
  (K1 : CompactCarrier.{u}) (ι1 : K1.Carrier → M1.Carrier) (Γ1 : BoundaryTori K1 1)
  (hK1 : K1.kind = .withBoundary) [ConnectedSpace K1.Carrier]
  (hι1 : IsSmoothEmbedding K1.model (𝓡 3) ∞ ι1)
  (hr1 : range ι1 = (φ1 '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ)
  (hΓ1 : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
    ι1 (Γ1.collar 0 p) = φ1 (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
  (hb1 : K1.model.boundary K1.Carrier = Γ1.image)
  (hbij1 : ∀ x, Bijective (mfderiv K1.model (𝓡 3) ι1 x))
  (hO1 : ∀ x, ∃ H : TangentSpace K1.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι1 x),
    H.toContinuousLinearMap = mfderiv K1.model (𝓡 3) ι1 x ∧
    Orientation.map (Fin 3) H.toLinearEquiv (K1.orientation.orientation x) =
      M1.orientation.orientation (ι1 x))

include hK0 hK1 h30 h31 hι0 hι1 hr0 hr1 hΓ0 hΓ1 hb0 hb1 hbij0 hbij1 hO0 hO1 in
theorem exists_rawConnectedSumIdentification
    (R0 : RawGraphPresentation K0) (R1 : RawGraphPresentation K1) :
    ∃ Q : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (RawGraphPresentation (NoCuts.carrier Q)) ∧
      ∃ F : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum M0 M1).Carrier,
        F.preservesOrientation Q.orientation (connectedSum M0 M1).orientation := by
  obtain ⟨W, E, j, hconnW, hW, hc, hn, hext, h, hlin⟩ := exists_connectedFibrePlug.{u}
  let : ConnectedSpace W.Carrier := hconnW
  obtain ⟨d, hs, hI, heq, ρ, hρ, hρ1, hav⟩ := E.exists_boundedSplitSignedTube j true h hlin
  have havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target :=
    fun r => (hav r).symm
  obtain ⟨εs0, g0, ε0, σ0, hσ0, hσ01, hgc0, hrS0, hrC0, H0, c0, e0,
    hc0s, hc0x, hleft0, hright0, hcore0, hbound0, hrad0, hm0⟩ :=
    E.exists_canonicalRestoredPlugData h hlin d hs hI heq hc hn hρ hρ1 havρ true
      M0 φ0 h30 K0 ι0 Γ0 hK0 hι0 hr0 hΓ0 hb0 hbij0 hO0
  obtain ⟨εs1, g1, ε1, σ1, hσ1, hσ11, hgc1, hrS1, hrC1, H1, c1, e1,
    hc1s, hc1x, hleft1, hright1, hcore1, hbound1, hrad1, hm1⟩ :=
    E.exists_canonicalRestoredPlugData h hlin d hs hI heq hc hn hρ hρ1 havρ false
      M1 φ1 h31 K1 ι1 Γ1 hK1 hι1 hr1 hΓ1 hb1 hbij1 hO1
  let ψ0 := E.boundedPlugMeridionalMarking h hlin εs0
  let ψ1 := E.boundedPlugMeridionalMarking h hlin εs1
  let f0 := markedRestorationMatching ψ0 ε0
  let f1 := markedRestorationMatching ψ1 ε1
  obtain ⟨N, hN, hconnN, T1, δ1, hδ1, hδ11, hcut1, hcomp1, hrev0, hpair1, hen,
    hEN, hrev1, δ2, hδ2, hδ21, Q, T2, hcut2, hcomp2, hpair2, hzero, hraw,
    L, R, hiL, hiR, hL0, hL1, hR0, hR1, hcross, hcover⟩ :=
    E.exists_plugPhysicalFactorAssembly h hlin d hs hI heq hc hn hρ hρ1 havρ
      hW K0 K1 hK0 hK1 Γ0 Γ1 hb0 hb1 f0 f1 R0 R1 hrC0 hrC1
  let : ConnectedSpace N.Carrier := hconnN
  let fL : c0.Punctured → Q.Carrier := L ∘ e0.symm
  let fR : c1.Punctured → Q.Carrier := R ∘ e1.symm
  have hfiL : Injective fL := hiL.comp e0.symm.injective
  have hfiR : Injective fR := hiR.comp e1.symm.injective
  have hfcov : ∀ y : Q.Carrier, (∃ x, fL x = y) ∨ ∃ x, fR x = y := by
    intro y
    have hy : y ∈ range L ∪ range R := hcover.symm ▸ mem_univ y
    rcases hy with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨e0 x, (congrArg L (e0.symm_apply_apply x)).trans hx⟩
    · exact Or.inr ⟨e1 x, (congrArg R (e1.symm_apply_apply x)).trans hx⟩
  let A0 := doubleBoundaryLeftMap K0 W K1 N hK0 hW hK1 hN T1 hcut1 T2 hcut2
  let A1 := doubleBoundaryRightMap K1 N hK1 hN T2 hcut2
  let Mid := doubleBoundaryMiddleMap K0 W K1 N hK0 hW hK1 hN T1 hcut1 T2 hcut2
  let C0 := E.plugComponentCutCarrier h hlin d hs heq hc hn 0
  let C1 := E.plugComponentCutCarrier h hlin d hs heq hc hn 1
  let B0 := E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ 0
  let B1 := E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ 1
  let S0 := E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ 0
  let S1 := E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ 1
  let Ki0 := E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ 0
  let Ki1 := E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ 1
  let u0 := E.plugCutFactor h hlin d hs heq hc hn 0
  let u1 := E.plugCutFactor h hlin d hs heq hc hn 1
  let J0 : C0.Carrier → Q.Carrier := Mid ∘ u0
  let J1 : C1.Carrier → Q.Carrier := Mid ∘ u1
  have hsA0 : ContMDiff K0.model (𝓡 3) ∞ A0 :=
    doubleBoundaryLeftMap_smooth K0 W K1 N hK0 hW hK1 hN T1 hcut1 T2 hcut2
  have hsA1 : ContMDiff K1.model (𝓡 3) ∞ A1 :=
    doubleBoundaryRightMap_smooth K1 N hK1 hN T2 hcut2
  have hsMid : ContMDiff W.model (𝓡 3) ∞ Mid :=
    doubleBoundaryMiddleMap_smooth K0 W K1 N hK0 hW hK1 hN T1 hcut1 T2 hcut2
  have hsJ0 : ContMDiff C0.model (𝓡 3) ∞ J0 :=
    hsMid.comp (E.plugCutFactor_smooth h hlin d hs heq hc hn 0)
  have hsJ1 : ContMDiff C1.model (𝓡 3) ∞ J1 :=
    hsMid.comp (E.plugCutFactor_smooth h hlin d hs heq hc hn 1)
  have hpA0 : IsOrientedFold (C := K0) (W := NoCuts.carrier Q) A0 :=
    doubleBoundaryLeftMap_positive K0 W K1 N hK0 hW hK1 hN T1 hcut1 T2 hcut2
  have hpA1 : IsOrientedFold (C := K1) (W := NoCuts.carrier Q) A1 :=
    doubleBoundaryRightMap_positive K1 N hK1 hN T2 hcut2
  have hpMid : IsOrientedFold (C := W) (W := NoCuts.carrier Q) Mid :=
    doubleBoundaryMiddleMap_positive K0 W K1 N hK0 hW hK1 hN T1 hcut1 T2 hcut2
  have hpJ0 : IsOrientedFold (C := C0) (W := NoCuts.carrier Q) J0 :=
    doubleBoundaryFold_comp_positive hsMid
      (E.plugCutFactor_smooth h hlin d hs heq hc hn 0) hpMid
      (E.plugCutFactor_positive h hlin d hs heq hc hn 0)
  have hpJ1 : IsOrientedFold (C := C1) (W := NoCuts.carrier Q) J1 :=
    doubleBoundaryFold_comp_positive hsMid
      (E.plugCutFactor_smooth h hlin d hs heq hc hn 1) hpMid
      (E.plugCutFactor_positive h hlin d hs heq hc hn 1)
  have hinjFold {C Q' : CompactCarrier.{u}} {f : C.Carrier → Q'.Carrier}
      (hf : IsOrientedFold f) (x : C.Carrier) :
      Injective (mfderiv C.model Q'.model f x) := by
    obtain ⟨D, hD, hDO⟩ := hf x
    intro v w hvw
    apply D.injective
    exact (hD v).trans (hvw.trans (hD w).symm)
  let : Nonempty C0.Carrier := E.plugCoreCutNonempty h hlin d hs heq hc hn 0
  let : Nonempty C1.Carrier := E.plugCoreCutNonempty h hlin d hs heq hc hn 1
  let : Nonempty S0.Carrier := E.plugCoreCapNonempty h hlin d hs hI heq hc hn hρ hρ1 havρ 0
  let : Nonempty S1.Carrier := E.plugCoreCapNonempty h hlin d hs hI heq hc hn hρ hρ1 havρ 1
  let EN : BoundaryTori N 1 := hen ▸ T1.external
  let EW := E.plugCutBoundaryPorts h hc hn hρ hρ1
  obtain ⟨j1, j2, hj1, hj2, hqL, hqR, htL, htR, huL, huR⟩ :=
    exists_doubleBoundaryTorusCoordinates K0 W K1 hK0 hW hK1 hN T1 hcut1 Γ0 EW Γ1
      f0 f1 hrev0 hδ1 hδ11 hpair1 EN hEN hrev1 Q T2 hcut2 hcomp2 hδ2 hδ21 hpair2
  let qL := doubleBoundaryLeftSeamChart N K1 hN hK1 Q T2 hcut2 hcomp2 T1 j1
  let qR := seamFlipChart f1.symm (T2.seam j2)
  have hsp0 : ∀ (i : Fin B0.sphereCount) (z : ClosureSphere.{u}),
      e0 ((boundaryCappingUncappedPairing K0 C0 hK0 rfl B0 rfl Γ0 f0 hrC0).quotientMap
        (Sum.inr (B0.sphere i (Ki0.attaching i z, halfZero)))) = c0.boundaryMap z.down := by
    intro i z
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact hbound0 z
  have hsp1 : ∀ (i : Fin B1.sphereCount) (z : ClosureSphere.{u}),
      e1 ((boundaryCappingUncappedPairing K1 C1 hK1 rfl B1 rfl Γ1 f1 hrC1).quotientMap
        (Sum.inr (B1.sphere i (Ki1.attaching i z, halfZero)))) = c1.boundaryMap z.down := by
    intro i z
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact hbound1 z
  have hhalf0 : ∀ (t : Torus) (s : ℝ) (hs0 : 0 ≤ s), s < δ1 →
      J0 (B0.tori.collar 0 (f0 t, halfPoint s hs0)) = qL (t, s / δ1) := by
    intro t s hs0 hsδ
    have hp : (f0 t, halfPoint s hs0) ∈ halfCollarSource := hsδ.trans_le hδ11
    exact (congrArg Mid (E.plugCutFactor_collar h hlin d hs hI heq hc hn hρ hρ1 havρ
      0 (f0 t, halfPoint s hs0) hp)).trans (htR t s hs0 hsδ).symm
  have hhalf1 : ∀ (t : Torus) (s : ℝ) (hs0 : 0 ≤ s), s < δ1 * δ2 →
      J1 (B1.tori.collar 0 (f1 t, halfPoint s hs0)) = qR (t, s / (δ1 * δ2)) := by
    intro t s hs0 hsδ
    have hp : (f1 t, halfPoint s hs0) ∈ halfCollarSource :=
      hsδ.trans_le (by nlinarith [mul_le_mul hδ11 hδ21 hδ2.le (by norm_num : (0 : ℝ) ≤ 1)])
    exact (congrArg Mid (E.plugCutFactor_collar h hlin d hs hI heq hc hn hρ hρ1 havρ
      1 (f1 t, halfPoint s hs0) hp)).trans (huR t s hs0 hsδ).symm
  have hsL : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fL ∘ c0.toBallChart.interiorToPunctured) :=
    restoredFactorInterior_isLocalDiffeomorph M0 (NoCuts.carrier Q) φ0 h30 K0 C0 S0 hK0 rfl rfl
      ι0 Γ0 hι0 hbij0 hb0 hΓ0 B0 rfl Ki0 g0 ψ0 ε0 σ0 hσ0 hσ01 hgc0 hrC0 hrS0 H0 c0 e0
      hleft0 hright0 hcore0 hsp0 L A0 J0 hsA0 hsJ0
      (fun x hx => hinjFold hpA0 x) (fun x hx => hinjFold hpJ0 x) hL0 hL1 qL hqL
      (Diffeomorph.refl torusModel Torus ∞) δ1 hδ1 δ1 hδ1
      (fun t s hs0 hsδ => (htL t s hs0 hsδ).symm) hhalf0
  have hsR : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fR ∘ c1.toBallChart.interiorToPunctured) :=
    restoredFactorInterior_isLocalDiffeomorph M1 (NoCuts.carrier Q) φ1 h31 K1 C1 S1 hK1 rfl rfl
      ι1 Γ1 hι1 hbij1 hb1 hΓ1 B1 rfl Ki1 g1 ψ1 ε1 σ1 hσ1 hσ11 hgc1 hrC1 hrS1 H1 c1 e1
      hleft1 hright1 hcore1 hsp1 R A1 J1 hsA1 hsJ1
      (fun x hx => hinjFold hpA1 x) (fun x hx => hinjFold hpJ1 x) hR0 hR1 qR hqR
      (Diffeomorph.refl torusModel Torus ∞) (δ1 * δ2) (mul_pos hδ1 hδ2)
      (δ1 * δ2) (mul_pos hδ1 hδ2)
      (fun t s hs0 hsδ => (huL t s hs0 hsδ).symm) hhalf1
  have hcrossF : ∀ x y, fL x = fR y ↔ ∃ z,
      c0.toBallChart.boundaryMap z = x ∧
        c1.toBallChart.boundaryMap (boundaryAttachment.1 z) = y :=
    by
      intro x y
      exact ElementaryPresentation.plugPuncturedFactor_boundary_cross hbound0 hbound1 hcross
  obtain ⟨η0, hη0, hη01, hradial0⟩ := E.exists_restoredPlugRadialCoordinates
    h hlin d hs hI heq hc hn hρ hρ1 havρ 0 K0 hK0 Γ0 f0 hrC0 hrS0
      M0 φ0 g0 ε0 H0 hright0 c0 hc0x e0 hcore0
  obtain ⟨η1, hη1, hη11, hradial1⟩ := E.exists_restoredPlugRadialCoordinates
    h hlin d hs hI heq hc hn hρ hρ1 havρ 1 K1 hK1 Γ1 f1 hrC1 hrS1
      M1 φ1 g1 ε1 H1 hright1 c1 hc1x e1 hcore1
  let q := plugSphereCollarChart K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
    Q T2 hcut2 hcomp2 d hs hI
  let a0 := E.plugSphereAttaching h hlin d hs hI heq hc hn hρ hρ1 havρ 0
  let a1 := E.plugSphereAttaching h hlin d hs hI heq hc hn hρ hρ1 havρ 1
  let δ := min η0 η1
  have hδ : 0 < δ := lt_min hη0 hη1
  have hδhalf : δ ≤ 1 / 2 := (min_le_left η0 η1).trans (by linarith)
  have hqs : ∀ z : SphereTwo, ∀ s : ℝ, |s| < 2 * δ → (z, s) ∈ q.source := by
    intro z s hsmall
    rw [plugSphereCollarChart_source]
    exact ⟨mem_univ _, (abs_lt.mp (hsmall.trans_le (by linarith))).1,
      (abs_lt.mp (hsmall.trans_le (by linarith))).2⟩
  have hangle : ∀ z, a1 (boundaryAttachment.1 z) = a0 z :=
    E.plugSphereAttaching_antipodal h hlin d hs hI heq hc hn hρ hρ1 havρ
  have hradL : ∀ (z : SphereTwo) (s : ℝ) (hs0 : 0 ≤ s) (hsδ : s < δ),
      fL (c0.toBallChart.radialMap z (1 + s) ⟨by linarith, by linarith⟩) =
        q (a0 z, 2 * s) := by
    intro z s hs0 hsδ
    have hsη : s < η0 := hsδ.trans_le (min_le_left η0 η1)
    change L (e0.symm _) = _
    rw [← hradial0 z s hs0 hsη]
    apply (congrArg L (e0.symm_apply_apply _)).trans
    exact (hL1 _).trans (E.plugSphereCollarChart_positive
      h hlin d hs hI heq hc hn hρ hρ1 havρ K0 K1 hK0 hW hK1 hN
      T1 hcut1 hcomp1 Q T2 hcut2 hcomp2 z s hs0 (by linarith)).symm
  have hradR : ∀ (z : SphereTwo) (s : ℝ) (hs0 : 0 ≤ s) (hsδ : s < δ),
      fR (c1.toBallChart.radialMap z (1 + s) ⟨by linarith, by linarith⟩) =
        q (a1 z, -(2 * s)) := by
    intro z s hs0 hsδ
    have hsη : s < η1 := hsδ.trans_le (min_le_right η0 η1)
    change R (e1.symm _) = _
    rw [← hradial1 z s hs0 hsη]
    apply (congrArg R (e1.symm_apply_apply _)).trans
    exact (hR1 _).trans (E.plugSphereCollarChart_negative
      h hlin d hs hI heq hc hn hρ hρ1 havρ K0 K1 hK0 hW hK1 hN
      T1 hcut1 hcomp1 Q T2 hcut2 hcomp2 z s hs0 (by linarith)).symm
  have hsC : IsLocalDiffeomorph ((𝓡 2).prod (𝓘(ℝ))) (𝓡 3) ∞
      (connectedSumFoldCollar M0 M1 Q c0 c1 boundaryAttachment fL fR) :=
    connectedSumFoldCollar_isLocalDiffeomorph M0 M1 Q c0 c1 boundaryAttachment fL fR
      q a0 a1 hangle δ hδ hδhalf hqs hradL hradR hsL hsR
  obtain ⟨hmem0, heLeft0⟩ := E.restoredPlugCoreInterior
    h hlin d hs hI heq hc hn hρ hρ1 havρ 0 M0 φ0 K0 hK0 ι0 Γ0 f0 g0 ε0
      hrC0 hrS0 H0 c0 e0 hleft0 hright0 hc0x hcore0
  have hphys0 : ∀ k, (fL ∘ c0.toBallChart.interiorToPunctured) ⟨ι0 k, hmem0 k⟩ = A0 k := by
    intro k
    change L (e0.symm _) = A0 k
    rw [← heLeft0 k]
    exact (congrArg L (e0.symm_apply_apply _)).trans (hL0 k)
  let k0 := Γ0.collar 0 (torusBase, halfPoint (1 / 2) (by norm_num))
  have hp0 := restoredFactorPointOrientation M0 Q c0
    (fL ∘ c0.toBallChart.interiorToPunctured) hsL K0 ι0 hι0.contMDiff hO0
      hmem0 A0 hpA0 hphys0 k0
  refine ⟨Q, hraw, connectedSumFixedFoldDiffeomorph M0 M1 Q c0 c1 fL fR hcrossF
    hfiL hfiR hfcov hsL hsR hsC, ?_⟩
  exact connectedSumFixedFoldDiffeomorph_positive M0 M1 Q c0 c1 fL fR hcrossF
    hfiL hfiR hfcov hsL hsR hsC ⟨ι0 k0, hmem0 k0⟩ hp0

theorem rawGraphPresentation_connectedSum
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M))
    (H : RawGraphPresentation (NoCuts.carrier N)) :
    Nonempty (RawGraphPresentation (NoCuts.carrier (connectedSum M N))) := by
  obtain ⟨φ0, h30, K0, ι0, R0, hK0, hconn0, hι0, hr0, hbij0, hO0,
    he0, Γ0, hΓeq0, hb0, hΓ0⟩ := exists_rawPhysicalExcisionData M G
  obtain ⟨φ1, h31, K1, ι1, R1, hK1, hconn1, hι1, hr1, hbij1, hO1,
    he1, Γ1, hΓeq1, hb1, hΓ1⟩ := exists_rawPhysicalExcisionData N H
  let : ConnectedSpace K0.Carrier := hconn0
  let : ConnectedSpace K1.Carrier := hconn1
  obtain ⟨Q, hraw, F, hF⟩ := exists_rawConnectedSumIdentification M N
    φ0 h30 K0 ι0 Γ0 hK0 hι0 hr0 hΓ0 hb0 hbij0 hO0
    φ1 h31 K1 ι1 Γ1 hK1 hι1 hr1 hΓ1 hb1 hbij1 hO1 R0 R1
  exact rawGraphPresentation_of_diffeomorph (Classical.choice hraw) F

end GC.GraphManifold
