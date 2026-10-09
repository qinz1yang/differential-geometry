import DifferentialGeometry.Topology.ThreeManifold.NormalizedUncapping
import DifferentialGeometry.Topology.ThreeManifold.UncappingProjection
import DifferentialGeometry.Topology.Manifold.ImmersionInterior
import DifferentialGeometry.Topology.ThreeManifold.CapAnnulusInterior
import DifferentialGeometry.Topology.ThreeManifold.TubeReparametrization
import DifferentialGeometry.Topology.ThreeManifold.UncappingSeam
import DifferentialGeometry.Topology.ThreeManifold.CapAnnulusGluing
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

noncomputable section

open Set Metric Manifold Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Annulus" => S2 × Icc (1 / 4 : ℝ) 1
private local instance uncappingCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance uncappingCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def uncappingMap (H : C.UncappingQuotient ≃ₜ M.Carrier) :
    C(((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier), M.Carrier) :=
  ⟨H ∘ C.uncappingProjection, H.continuous.comp C.uncappingProjection.continuous⟩

theorem uncappingMap_core (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (hcore : ∀ x : T.core, H (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (x : T.core) (y : ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier))
    (hy : y.val = C.coreInclusion x) : C.uncappingMap H y = x.val := by
  change H (C.uncappingProjection y) = _
  rw [C.uncappingProjection_of_eq_coreInclusion x y hy]
  exact hcore x

def uncappingInterior : TopologicalSpace.Opens N.Carrier :=
  ⟨(⋃ b, (C.capBallChart b).chart '' closedBall (0 : E3) 1)ᶜ,
    (isClosed_iUnion_of_finite (fun b => (C.capBallChart b).toBallChart.isCompact_closedBall_image.isClosed)).isOpen_compl⟩

def uncappingInteriorInclusion (x : C.uncappingInterior) :
    ((⋃ b, (C.capBallChart b).chart '' ball (0 : E3) 1)ᶜ : Set N.Carrier) :=
  ⟨x.val, by
    intro h
    obtain ⟨b,y,hy,heq⟩ := mem_iUnion.mp h
    exact x.property (mem_iUnion.mpr ⟨b,y,ball_subset_closedBall hy,heq⟩)⟩

def uncappingInteriorMap (H : C.UncappingQuotient ≃ₜ M.Carrier) : C(C.uncappingInterior, M.Carrier) :=
  ⟨C.uncappingMap H ∘ C.uncappingInteriorInclusion,
    (C.uncappingMap H).continuous.comp (continuous_subtype_val.subtype_mk _)⟩

theorem coreInclusion_mem_uncappingInterior (x : T.core) : C.coreInclusion x ∈ C.uncappingInterior := by
  intro h
  obtain ⟨b,y,hy,heq⟩ := mem_iUnion.mp h
  exact Set.disjoint_left.mp (C.disjoint_capBallChart_closedBall_core b)
    ⟨y,closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hy,heq⟩ ⟨x,rfl⟩

theorem uncappingInteriorMap_core (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (hcore : ∀ x : T.core, H (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val) (x : T.core) :
    C.uncappingInteriorMap H ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩ = x.val :=
  C.uncappingMap_core H hcore x _ rfl

theorem isLocalDiffeomorphAt_uncappingInteriorMap_core
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (hcore : ∀ x : T.core, H (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val) (x : T.core) :
    letI := C.coreCharts
    (𝓡∂ 3).IsInteriorPoint x →
      IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (C.uncappingInteriorMap H)
        ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩ := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  intro hx
  have hc : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ C.coreInclusion x :=
    Manifold.isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
      C.core_embedding.contMDiff hx rfl
      ((C.core_embedding.isImmersion.isImmersionAt x).mfderiv_injective (by simp))
  have hs : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : T.core → M.Carrier) x :=
    Manifold.isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
      C.core_induced.contMDiff hx rfl
      ((C.core_induced.isImmersion.isImmersionAt x).mfderiv_injective (by simp))
  let f : T.core → C.uncappingInterior := fun y => ⟨C.coreInclusion y,C.coreInclusion_mem_uncappingInterior y⟩
  have hf : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ f x :=
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict (C.coreInclusion_mem_uncappingInterior) hc
  have heq : (C.uncappingInteriorMap H) ∘ f = (Subtype.val : T.core → M.Carrier) :=
    funext (C.uncappingInteriorMap_core H hcore)
  have hcomp : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ ((C.uncappingInteriorMap H) ∘ f) x :=
    heq.symm ▸ hs
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp hcomp hf

private theorem uncappingAnnulus_eq_radialTube
    (Ψ : T.Index → (S2 × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), (𝓡 2).prod (𝓡∂ 1)⟯
      (S2 × unitInterval))
    (hlo : ∀ a (t : unitInterval), t.val ≤ 1 / 3 → ∀ z,
      Ψ a (z, t) = (C.attaching (a, false) z, t))
    (hhi : ∀ a (t : unitInterval), 2 / 3 ≤ t.val → ∀ z,
      Ψ a (z, t) = (C.attaching (a, true) z, t))
    (ρ : ℝ → ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (ε : ℝ) (houter : ∀ r, 1 - ε ≤ r → ρ r = r)
    (b : T.Boundary) (v z : S2) (r : Icc (1 / 4 : ℝ) 1)
    (hr : max (1 - ε) (1 / 3) ≤ r.val) :
    T.cylinderMap b.1 (Ψ b.1 (z,
      ⟨(1 + (if b.2 then ρ r.val else -ρ r.val)) / 2, by
        have h := hρ r.property
        cases b.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
          constructor <;> linarith [h.1, h.2]⟩)) =
      T.radialTube b.1 (C.attaching b) b.2 v (r.val • z.val) := by
  have hrρ : ρ r.val = r.val := houter r.val ((le_max_left _ _).trans hr)
  have hthird : (1 / 3 : ℝ) ≤ r.val := (le_max_right _ _).trans hr
  let t : unitInterval := ⟨(1 + (if b.2 then ρ r.val else -ρ r.val)) / 2, by
    have h := hρ r.property
    cases b.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      constructor <;> linarith [h.1, h.2]⟩
  have ht : Ψ b.1 (z, t) = (C.attaching b z, t) := by
    cases hb : b.2 with
    | false =>
      have htb : t.val ≤ 1 / 3 := by
        change (1 + (if b.2 then ρ r.val else -ρ r.val)) / 2 ≤ 1 / 3
        simp only [hb, Bool.false_eq_true, ite_false, hrρ]
        linarith
      have hb' : (b.1, false) = b := Prod.ext rfl hb.symm
      simpa only [hb'] using hlo b.1 t htb z
    | true =>
      have htb : 2 / 3 ≤ t.val := by
        change 2 / 3 ≤ (1 + (if b.2 then ρ r.val else -ρ r.val)) / 2
        simp only [hb, ite_true, hrρ]
        linarith
      have hb' : (b.1, true) = b := Prod.ext rfl hb.symm
      simpa only [hb'] using hhi b.1 t htb z
  have hnorm : ‖r.val • z.val‖ = r.val := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [r.property.1]),
      norm_eq_of_mem_sphere, mul_one]
  change T.cylinderMap b.1 (Ψ b.1 (z, t)) = _
  rw [ht, T.radialTube_apply b.1 (C.attaching b) b.2 v
    (by rw [hnorm]; linarith [r.property.2]),
    Manifold.sphereDirection_pos_smul v z (by linarith [r.property.1])]
  apply congrArg (T.tube b.1)
  apply Prod.ext
  · rfl
  apply Subtype.ext
  change 2 * t.val - 1 = if b.2 then ‖r.val • z.val‖ else -‖r.val • z.val‖
  change 2 * ((1 + (if b.2 then ρ r.val else -ρ r.val)) / 2) - 1 = _
  rw [hrρ, hnorm]
  cases b.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring

private theorem uncappingMap_normalized_annulus
    (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
    (hboundary : ∀ b z, B b (sphereToClosedCell z) = sphereToClosedCell z)
    (Ψ : T.Index → (S2 × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), (𝓡 2).prod (𝓡∂ 1)⟯ (S2 × unitInterval))
    (ρ : ℝ → ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (hann : ∀ q : Σ _b : T.Boundary, Annulus,
      H (Quot.mk C.innerCapRelation (C.puncturedCappingReparametrization B hsmall hboundary
        (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q))) =
      T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1,
        ⟨(1 + (if q.1.2 then ρ q.2.2.val else -ρ q.2.2.val)) / 2, by
          have h := hρ q.2.2.property
          cases q.1.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
            constructor <;> linarith [h.1,h.2]⟩)))
    (b : T.Boundary) (z : S2) (r : Icc (1 / 4 : ℝ) 1)
    (y : ((⋃ b, (C.capBallChart b).chart '' ball (0 : E3) 1)ᶜ : Set N.Carrier))
    (hy : y.val = C.cap b (B b ⟨r.val • z.val, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [r.property.1]), norm_eq_of_mem_sphere,mul_one]
      exact r.property.2⟩)) :
    C.uncappingMap H y = T.cylinderMap b.1 (Ψ b.1 (z,
      ⟨(1 + (if b.2 then ρ r.val else -ρ r.val)) / 2, by
        have h := hρ r.property
        cases b.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
          constructor <;> linarith [h.1,h.2]⟩)) := by
  change H (C.uncappingProjection y) = _
  rw [C.uncappingProjection_cap_reparametrization B hsmall hboundary b (z,r) y hy]
  exact hann ⟨b,z,r⟩

private theorem uncappingInteriorMap_eq_radialTube_at_outer
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (hcore : ∀ x : T.core, H (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3) (b : T.Boundary) (v : S2)
    (e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell))
    (he : e.radius ≤ 1 / 2)
    (heq : ∀ (p : S2 × symmetricOpenInterval e.radius) (hp : 0 ≤ p.2.val),
      e.toFun p = C.coreInclusionHalfCollar b
        (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le he⟩))
    (V : Set E3)
    (hcap : ∀ x : ClosedCell 3, x.val ∈ V →
      C.cap b (B b x) = e.reverse.radialPartialDiffeomorph v x.val)
    (c : ℝ) (hc : 1 / 4 ≤ c)
    (hinner : ∀ (z : S2) (r : Icc (1 / 4 : ℝ) 1), c ≤ r.val →
      ∀ y : C.uncappingInterior, y.val = C.cap b (B b ⟨r.val • z.val, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [r.property.1]),norm_eq_of_mem_sphere,mul_one]
        exact r.property.2⟩) →
      C.uncappingInteriorMap H y = T.radialTube b.1 (C.attaching b) b.2 v (r.val • z.val))
    (y : C.uncappingInterior) (x : E3)
    (hx : x ∈ (e.reverse.radialPartialDiffeomorph v).source) (hxV : x ∈ V)
    (hxc : c ≤ ‖x‖) (hy : y.val = e.reverse.radialPartialDiffeomorph v x) :
    C.uncappingInteriorMap H y = T.radialTube b.1 (C.attaching b) b.2 v x := by
  have hxne := ((e.reverse.mem_radialPartialDiffeomorph_source_iff v x).mp hx).1
  have ht := ((e.reverse.mem_radialPartialDiffeomorph_source_iff v x).mp hx).2
  let z := Manifold.sphereDirection v x
  by_cases hin : ‖x‖ ≤ 1
  · let r : Icc (1 / 4 : ℝ) 1 := ⟨‖x‖, hc.trans hxc, hin⟩
    have hxrad : r.val • z.val = x := Manifold.norm_smul_sphereDirection v hxne
    have hycap : y.val = C.cap b (B b ⟨r.val • z.val, by
        rw [hxrad]; exact hin⟩) := by
      have h := hcap ⟨x,hin⟩ hxV
      rw [hy]
      exact h.symm.trans (congrArg (fun w : ClosedCell 3 => C.cap b (B b w))
        (Subtype.ext hxrad.symm))
    have hh := hinner z r hxc y hycap
    rwa [hxrad] at hh
  · have hpos : 0 < ‖x‖ - 1 := by linarith
    have hlt : ‖x‖ - 1 < e.radius := by
      change -e.radius < 1 - ‖x‖ ∧ 1 - ‖x‖ < e.radius at ht
      linarith [ht.1]
    let q : S2 × Ico (0 : ℝ) (1 / 2) := (z, ⟨‖x‖ - 1,hpos.le,hlt.trans_le he⟩)
    let p : S2 × symmetricOpenInterval e.radius :=
      (z, ⟨‖x‖ - 1, by constructor <;> linarith [e.radius_pos]⟩)
    have hrad : e.reverse.radialPartialDiffeomorph v x = e.toFun p := by
      have h := e.reverse.radialPartialDiffeomorph_apply v z ‖x‖ (norm_pos_iff.mpr hxne) ht
      rw [Manifold.norm_smul_sphereDirection v hxne] at h
      rw [h]
      erw [e.reverse_toFun]
      apply congrArg e.toFun
      apply Prod.ext
      · rfl
      · apply Subtype.ext; dsimp [p]; ring
    have hycore : y.val = C.coreInclusion (C.coreBoundaryHalfCollar b q) := by
      rw [hy,hrad,heq p hpos.le]
      rfl
    have hF : C.uncappingInteriorMap H y = (C.coreBoundaryHalfCollar b q).val :=
      C.uncappingMap_core H hcore (C.coreBoundaryHalfCollar b q) (C.uncappingInteriorInclusion y) hycore
    rw [hF,C.coreBoundaryHalfCollar_val]
    have hx2 : ‖x‖ < 2 := by linarith
    rw [T.radialTube_apply b.1 (C.attaching b) b.2 v hx2]
    apply congrArg (T.tube b.1)
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (SphericalTubeSystem.coreCollarParameter b.2 q.2).val = if b.2 then ‖x‖ else -‖x‖
      rw [SphericalTubeSystem.coreCollarParameter_val]
      cases b.2 <;> simp [SphericalTubeSystem.boundaryLevel,q]
      ring

private theorem isLocalDiffeomorphAt_uncappingInteriorMap_outer_of_eq
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (hcore : ∀ x : T.core, H (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3) (b : T.Boundary) (v : S2)
    (e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell))
    (he : e.radius ≤ 1 / 2)
    (heq : ∀ (p : S2 × symmetricOpenInterval e.radius) (hp : 0 ≤ p.2.val),
      e.toFun p = C.coreInclusionHalfCollar b
        (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le he⟩))
    (V : Set E3) (hV : IsOpen V) (hSV : sphere (0 : E3) 1 ⊆ V)
    (hcap : ∀ x : ClosedCell 3, x.val ∈ V →
      C.cap b (B b x) = e.reverse.radialPartialDiffeomorph v x.val)
    (c : ℝ) (hc : 1 / 4 ≤ c) (hc1 : c < 1)
    (hinner : ∀ (z : S2) (r : Icc (1 / 4 : ℝ) 1), c ≤ r.val →
      ∀ y : C.uncappingInterior, y.val = C.cap b (B b ⟨r.val • z.val, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [r.property.1]),norm_eq_of_mem_sphere,mul_one]
        exact r.property.2⟩) →
      C.uncappingInteriorMap H y = T.radialTube b.1 (C.attaching b) b.2 v (r.val • z.val))
    (z : S2) (y : C.uncappingInterior) (hy : y.val = C.cap b (sphereToClosedCell z)) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (C.uncappingInteriorMap H) y := by
  let Q := e.reverse.radialPartialDiffeomorph v
  have hzQ : z.val ∈ Q.source := e.reverse.sphere_subset_radialPartialDiffeomorph_source v z.property
  have hQz : Q z.val = y.val := (e.reverse.radialPartialDiffeomorph_sphere v z).trans hy.symm
  have hyQ : y.val ∈ Q.target := hQz ▸ Q.map_source hzQ
  have hQsymm : Q.symm y.val = z.val := hQz ▸ Q.left_inv hzQ
  have hcont : ContinuousAt (fun w : C.uncappingInterior => Q.symm w.val) y :=
    (Q.contMDiffOn_invFun.continuousOn.continuousAt (Q.open_target.mem_nhds hyQ)).comp
      continuous_subtype_val.continuousAt
  have hg := C.isLocalDiffeomorphAt_coreBoundaryExtension b e v z
  have hg' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (C.coreBoundaryExtension b e v) y.val := hy.symm ▸ hg
  have hloc := (DifferentialGeometry.isLocalDiffeomorph_subtype_val C.uncappingInterior y).comp
    (𝓡 3) M.Carrier hg'
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := (C.coreBoundaryExtension b e v) ∘ Subtype.val) _ hloc
  have htarget : ∀ᶠ w : C.uncappingInterior in 𝓝 y, w.val ∈ Q.target :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (Q.open_target.mem_nhds hyQ)
  have hVin : ∀ᶠ w : C.uncappingInterior in 𝓝 y, Q.symm w.val ∈ V :=
    hcont.preimage_mem_nhds (hV.mem_nhds (hQsymm ▸ hSV z.property))
  have hnorm : ∀ᶠ w : C.uncappingInterior in 𝓝 y, c < ‖Q.symm w.val‖ :=
    hcont.norm.preimage_mem_nhds (Ioi_mem_nhds (by rw [hQsymm,norm_eq_of_mem_sphere]; exact hc1))
  filter_upwards [htarget,hVin,hnorm] with w hwQ hwV hwc
  exact C.uncappingInteriorMap_eq_radialTube_at_outer H hcore B b v e he heq V hcap c hc hinner
    w (Q.symm w.val) (Q.symm.map_source hwQ) hwV hwc.le (Q.right_inv hwQ).symm

theorem isLocalDiffeomorphAt_uncappingInteriorMap_outer
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (hcore : ∀ x : T.core, H (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
    (hboundary : ∀ b z, B b (sphereToClosedCell z) = sphereToClosedCell z)
    (Ψ : T.Index → (S2 × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), (𝓡 2).prod (𝓡∂ 1)⟯ (S2 × unitInterval))
    (hlo : ∀ a (t : unitInterval), t.val ≤ 1 / 3 → ∀ z, Ψ a (z,t) = (C.attaching (a,false) z,t))
    (hhi : ∀ a (t : unitInterval), 2 / 3 ≤ t.val → ∀ z, Ψ a (z,t) = (C.attaching (a,true) z,t))
    (ρ : ℝ → ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hann : ∀ q : Σ _b : T.Boundary, Annulus,
      H (Quot.mk C.innerCapRelation (C.puncturedCappingReparametrization B hsmall hboundary
        (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q))) =
      T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1,
        ⟨(1 + (if q.1.2 then ρ q.2.2.val else -ρ q.2.2.val)) / 2, by
          have h := hρ q.2.2.property
          cases q.1.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
            constructor <;> linarith [h.1,h.2]⟩)))
    (ε : ℝ) (hε : 0 < ε) (houter : ∀ r, 1 - ε ≤ r → ρ r = r)
    (b : T.Boundary) (v : S2)
    (e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell))
    (he : e.radius ≤ 1 / 2)
    (heq : ∀ (p : S2 × symmetricOpenInterval e.radius) (hp : 0 ≤ p.2.val),
      e.toFun p = C.coreInclusionHalfCollar b
        (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le he⟩))
    (V : Set E3) (hV : IsOpen V) (hSV : sphere (0 : E3) 1 ⊆ V)
    (hcap : ∀ x : ClosedCell 3, x.val ∈ V →
      C.cap b (B b x) = e.reverse.radialPartialDiffeomorph v x.val)
    (z : S2) (y : C.uncappingInterior) (hy : y.val = C.cap b (sphereToClosedCell z)) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (C.uncappingInteriorMap H) y := by
  apply C.isLocalDiffeomorphAt_uncappingInteriorMap_outer_of_eq H hcore B b v e he heq V hV hSV hcap
    (max (1-ε) (1/3)) (by have h := le_max_right (1-ε) (1/3:ℝ); linarith)
    (max_lt (by linarith) (by norm_num)) _ z y hy
  intro w r hr p hp
  have hh := C.uncappingMap_normalized_annulus B hsmall hboundary Ψ ρ hρ H hann b w r
    (C.uncappingInteriorInclusion p) hp
  exact hh.trans (uncappingAnnulus_eq_radialTube C Ψ hlo hhi ρ hρ ε houter b v w r hr)

private theorem isLocalDiffeomorphAt_uncappingInteriorMap_annulus_of_eq
    (H : C.UncappingQuotient ≃ₜ M.Carrier) (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) (v : S2)
    (Ψ : (S2 × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), (𝓡 2).prod (𝓡∂ 1)⟯ (S2 × unitInterval))
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hmono : StrictMono (ρ : ℝ → ℝ))
    (hzero : ρ (1 / 4) = 0) (hone : ρ 1 = 1)
    (heq : ∀ (q : S2 × ℝ) (hq : q.2 ∈ Ioo (1 / 4 : ℝ) 1),
      C.uncappingInteriorMap H
        ⟨C.capAnnulusInteriorChart b B v q,
          C.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall b B hsmall v q hq⟩ =
        T.reparametrizedTube b.1 Ψ (q.1, if b.2 then ρ q.2 else -ρ q.2))
    (q : S2 × ℝ) (hq : q.2 ∈ Ioo (1 / 4 : ℝ) 1) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (C.uncappingInteriorMap H)
      ⟨C.capAnnulusInteriorChart b B v q,
        C.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall b B hsmall v q hq⟩ := by
  let U : TopologicalSpace.Opens (S2 × ℝ) := ⟨{q | q.2 ∈ Ioo (1 / 4 : ℝ) 1}, isOpen_Ioo.preimage continuous_snd⟩
  let f : U → C.uncappingInterior := fun p =>
    ⟨C.capAnnulusInteriorChart b B v p.val,
      C.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall b B hsmall v p.val p.property⟩
  have hfval : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ,ℝ)) (𝓡 3) ∞
      (fun p : U => C.capAnnulusInteriorChart b B v p.val) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open U
      (fun p => C.isLocalDiffeomorphAt_capAnnulusInteriorChart b B v ⟨by linarith [p.property.1],p.property.2⟩)
  have hf : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ,ℝ)) (𝓡 3) ∞ f ⟨q,hq⟩ :=
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (fun p : U => C.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall b B hsmall v p.val p.property)
      (hfval ⟨q,hq⟩)
  have hg : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ,ℝ)) (𝓡 3) ∞
      (fun p : U => T.reparametrizedTube b.1 Ψ (p.val.1,if b.2 then ρ p.val.2 else -ρ p.val.2)) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open U
      (fun p => T.isLocalDiffeomorphAt_reparametrizedTube_comp_radius_of_strictMono
        b.1 Ψ ρ hmono hzero hone b.2 p.property)
  have hfun : (C.uncappingInteriorMap H) ∘ f =
      (fun p : U => T.reparametrizedTube b.1 Ψ (p.val.1,if b.2 then ρ p.val.2 else -ρ p.val.2)) :=
    funext (fun p => heq p.val p.property)
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hfun.symm ▸ hg ⟨q,hq⟩) hf

theorem isLocalDiffeomorphAt_uncappingInteriorMap_annulus
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (B : T.Boundary → ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
    (hboundary : ∀ b z, B b (sphereToClosedCell z) = sphereToClosedCell z)
    (Ψ : T.Index → (S2 × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), (𝓡 2).prod (𝓡∂ 1)⟯ (S2 × unitInterval))
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hmono : StrictMono (ρ : ℝ → ℝ)) (hzero : ρ (1 / 4) = 0) (hone : ρ 1 = 1)
    (hann : ∀ q : Σ _b : T.Boundary, Annulus,
      H (Quot.mk C.innerCapRelation (C.puncturedCappingReparametrization
        (fun b => (B b).toHomeomorph) hsmall hboundary
        (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q))) =
      T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1,
        ⟨(1 + (if q.1.2 then ρ q.2.2.val else -ρ q.2.2.val)) / 2, by
          have h := hρ q.2.2.property
          cases q.1.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
            constructor <;> linarith [h.1,h.2]⟩)))
    (b : T.Boundary) (v : S2) (q : S2 × ℝ) (hq : q.2 ∈ Ioo (1 / 4 : ℝ) 1) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (C.uncappingInteriorMap H)
      ⟨C.capAnnulusInteriorChart b (B b) v q,
        C.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall b (B b) (hsmall b) v q hq⟩ := by
  apply C.isLocalDiffeomorphAt_uncappingInteriorMap_annulus_of_eq H b (B b) (hsmall b) v
    (Ψ b.1) ρ hmono hzero hone _ q hq
  intro p hp
  let r : Icc (1 / 4 : ℝ) 1 := ⟨p.2,hp.1.le,hp.2.le⟩
  let y : C.uncappingInterior := ⟨C.capAnnulusInteriorChart b (B b) v p,
    C.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall b (B b) (hsmall b) v p hp⟩
  have hh := C.uncappingMap_normalized_annulus (fun b => (B b).toHomeomorph) hsmall hboundary
    Ψ ρ hρ H hann b p.1 r (C.uncappingInteriorInclusion y)
    (C.capAnnulusInteriorChart_apply b (B b) v p ⟨by linarith [hp.1],hp.2⟩)
  have hlo : 0 < ρ p.2 := by have h := hmono hp.1; rwa [hzero] at h
  have hhi : ρ p.2 < 1 := by have h := hmono hp.2; rwa [hone] at h
  have hu : (if b.2 then ρ p.2 else -ρ p.2) ∈ Ioo (-1 : ℝ) 1 := by
    cases b.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true, mem_Ioo] <;> constructor <;> linarith
  rw [T.reparametrizedTube_apply b.1 (Ψ b.1) _ hu]
  exact hh.trans (by
    apply congrArg (T.cylinderMap b.1)
    apply congrArg (Ψ b.1)
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 + (if b.2 then ρ p.2 else -ρ p.2)) / 2 =
        ((if b.2 then ρ p.2 else -ρ p.2) + 1) / 2
      ring)

private theorem homeomorph_uncappingSeam_eq
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
    (hboundary : ∀ b z, B b (sphereToClosedCell z) = sphereToClosedCell z)
    (hhalf : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 2 → B b x = x)
    (Ψ : T.Index → (S2 × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), (𝓡 2).prod (𝓡∂ 1)⟯ (S2 × unitInterval))
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hmono : StrictMono (ρ : ℝ → ℝ)) (hzero : ρ (1 / 4) = 0) (hone : ρ 1 = 1)
    (hann : ∀ q : Σ _b : T.Boundary, Annulus,
      H (Quot.mk C.innerCapRelation (C.puncturedCappingReparametrization B hsmall hboundary
        (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q))) =
      T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1,
        ⟨(1 + (if q.1.2 then ρ q.2.2.val else -ρ q.2.2.val)) / 2, by
          have h := hρ q.2.2.property
          cases q.1.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
            constructor <;> linarith [h.1,h.2]⟩)))
    (a : T.Index) (p : ConnectedSumQuotient.CollarDomain) :
    H (C.uncappingSeam a p) = T.reparametrizedTube a (Ψ a)
      (-p.1, if 0 ≤ p.2.val then -ρ ((1 + p.2.val) / 4) else ρ ((1 - p.2.val) / 4)) := by
  have hfix := C.uncappingQuotientReparametrization_uncappingSeam B hsmall hboundary hhalf a p
  let R := C.uncappingQuotientReparametrization B hsmall hboundary
  by_cases ht : 0 ≤ p.2.val
  · have hbranch := congrArg (fun q : C.UncappingQuotient => H (R q))
      (C.uncappingSeam_of_nonneg a p ht)
    let q : Σ _b : T.Boundary, Annulus :=
      ⟨(a,false),-p.1,⟨(1 + p.2.val)/4, by constructor <;> linarith [p.2.property.2]⟩⟩
    have hR := C.uncappingQuotientReparametrization_mk B hsmall hboundary
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q)
    have hh := (congrArg H hfix).symm.trans (hbranch.trans ((congrArg H hR).trans (hann q)))
    rw [hh]
    have hlo : 0 ≤ ρ ((1 + p.2.val) / 4) := by
      have hh := hmono.monotone (by linarith : (1 / 4 : ℝ) ≤ (1 + p.2.val) / 4)
      rwa [hzero] at hh
    have hhi : ρ ((1 + p.2.val) / 4) < 1 := by
      have hh := hmono (by linarith [p.2.property.2] : (1 + p.2.val) / 4 < 1)
      rwa [hone] at hh
    rw [ite_eq_left ht, T.reparametrizedTube_apply a (Ψ a) _ (by
      change -ρ ((1 + p.2.val) / 4) ∈ Ioo (-1 : ℝ) 1
      constructor <;> linarith)]
    apply congrArg (T.cylinderMap a)
    apply congrArg (Ψ a)
    apply Prod.ext
    · rfl
    · apply Subtype.ext; dsimp only [q]; simp only [Bool.false_eq_true,ite_false]; ring
  · have hbranch := congrArg (fun q : C.UncappingQuotient => H (R q))
      (C.uncappingSeam_of_nonpos a p (le_of_not_ge ht))
    let q : Σ _b : T.Boundary, Annulus :=
      ⟨(a,true),-p.1,⟨(1 - p.2.val)/4, by constructor <;> linarith [p.2.property.1]⟩⟩
    have hR := C.uncappingQuotientReparametrization_mk B hsmall hboundary
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q)
    have hh := (congrArg H hfix).symm.trans (hbranch.trans ((congrArg H hR).trans (hann q)))
    rw [hh]
    have hlo : 0 ≤ ρ ((1 - p.2.val) / 4) := by
      have hh := hmono.monotone (by linarith : (1 / 4 : ℝ) ≤ (1 - p.2.val) / 4)
      rwa [hzero] at hh
    have hhi : ρ ((1 - p.2.val) / 4) < 1 := by
      have hh := hmono (by linarith [p.2.property.1] : (1 - p.2.val) / 4 < 1)
      rwa [hone] at hh
    rw [ite_eq_right ht, T.reparametrizedTube_apply a (Ψ a) _ (by
      change ρ ((1 - p.2.val) / 4) ∈ Ioo (-1 : ℝ) 1
      constructor <;> linarith)]
    apply congrArg (T.cylinderMap a)
    apply congrArg (Ψ a)
    apply Prod.ext
    · rfl
    · apply Subtype.ext; dsimp only [q]; simp only [ite_true]; ring

theorem isLocalDiffeomorphAt_homeomorph_uncappingSeam
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
    (hboundary : ∀ b z, B b (sphereToClosedCell z) = sphereToClosedCell z)
    (hhalf : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 2 → B b x = x)
    (Ψ : T.Index → (S2 × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), (𝓡 2).prod (𝓡∂ 1)⟯ (S2 × unitInterval))
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hmono : StrictMono (ρ : ℝ → ℝ)) (hzero : ρ (1 / 4) = 0) (hone : ρ 1 = 1)
    (hann : ∀ q : Σ _b : T.Boundary, Annulus,
      H (Quot.mk C.innerCapRelation (C.puncturedCappingReparametrization B hsmall hboundary
        (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q))) =
      T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1,
        ⟨(1 + (if q.1.2 then ρ q.2.2.val else -ρ q.2.2.val)) / 2, by
          have h := hρ q.2.2.property
          cases q.1.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
            constructor <;> linarith [h.1,h.2]⟩)))
    (hgerm : (ρ : ℝ → ℝ) =ᶠ[𝓝 (1 / 4 : ℝ)] (fun r => r - 1 / 4))
    (a : T.Index) (z : S2) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ,ℝ)) (𝓡 3) ∞
      (H ∘ C.uncappingSeam a) (z,(⟨0,by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)) := by
  let PI := ModelWithCorners.prod (𝓡 2) 𝓘(ℝ,ℝ)
  let j : PartialDiffeomorph PI PI ConnectedSumQuotient.CollarDomain (S2 × ℝ) ∞ :=
    PartialDiffeomorph.prod (Diffeomorph.refl (𝓡 2) S2 ∞).toPartialDiffeomorph
      (PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ,ℝ)) ConnectedSumQuotient.collarInterval
        ⟨(⟨0,by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)⟩)
  let F : S2 × ℝ → M.Carrier := fun p => T.reparametrizedTube a (Ψ a)
    (-p.1, if 0 ≤ p.2 then -ρ ((1 + p.2)/4) else ρ ((1 - p.2)/4))
  have hF : IsLocalDiffeomorphAt PI (𝓡 3) ∞ F (z,0) := by
    have h := T.isLocalDiffeomorphAt_annulus_seam_of_eventuallyEq a (Ψ a) 1 zero_lt_one ρ hgerm z
    have hfun : F = (fun p : S2 × ℝ => T.reparametrizedTube a (Ψ a)
        (-p.1,if 0 ≤ p.2 then -ρ ((1:ℝ)/4*(1+p.2)) else ρ ((1:ℝ)/4*(1-p.2)))) := by
      funext p
      change T.reparametrizedTube a (Ψ a) (-p.1,if 0 ≤ p.2 then -ρ ((1+p.2)/4) else ρ ((1-p.2)/4)) = _
      rw [show (1:ℝ)/4*(1+p.2)=(1+p.2)/4 by ring,
        show (1:ℝ)/4*(1-p.2)=(1-p.2)/4 by ring]
    exact hfun.symm ▸ h
  have hj := j.isLocalDiffeomorphAt PI PI ∞
    (show (z,(⟨0,by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)) ∈ j.source from ⟨trivial,trivial⟩)
  have hc := hj.comp (𝓡 3) M.Carrier hF
  have heq : H ∘ C.uncappingSeam a = F ∘ j := by
    funext p
    exact homeomorph_uncappingSeam_eq C H B hsmall hboundary hhalf Ψ ρ hρ hmono hzero hone hann a p
  exact heq.symm ▸ hc

end DifferentialGeometry.Topology.SphericalCapping
