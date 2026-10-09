import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreCollarAvoidance
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreExcisionWithBoundary

/-!
# Actual old and new boundary tori after excising a circle fibre
-/

set_option autoImplicit false

noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.CircleFibration

variable (C : CompactCarrier.{u})
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model
  (PlaneLift.{u} × Circle) C.Carrier ∞)
variable (hφ : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)

include hφ in
private theorem radiusTwoTube_compact :
    IsCompact (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2}) := by
  have hc : IsCompact {z : PlaneLift.{u} | ‖z.down‖ ≤ 2} := by
    have he : {z : PlaneLift.{u} | ‖z.down‖ ≤ 2} =
        (Homeomorph.ulift.symm : ℂ ≃ₜ PlaneLift.{u}) '' Metric.closedBall 0 2 := by
      ext z
      rcases z with ⟨z⟩
      simp [Metric.mem_closedBall, dist_zero_right, Homeomorph.ulift]
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) 2).image Homeomorph.ulift.symm.continuous
  have hp : IsCompact {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
    have he : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} =
        {z : PlaneLift.{u} | ‖z.down‖ ≤ 2} ×ˢ univ := by
      ext p
      simp
    rw [he]
    exact hc.prod isCompact_univ
  exact hp.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono
    (fun p hp => hφ (by change ‖p.1.down‖ ≤ 2 at hp; change ‖p.1.down‖ ≤ 3; linarith)))

include hφ in
private theorem radiusTwoTube_interior :
    φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} ⊆ C.interior := by
  rintro x ⟨p, hp, rfl⟩
  have hs : p ∈ φ.source := hφ (by
    change ‖p.1.down‖ ≤ 2 at hp
    change ‖p.1.down‖ ≤ 3
    linarith)
  have hl := φ.isLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model ∞ hs
  exact (hl.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp
    BoundarylessManifold.isInteriorPoint

variable (K : CompactCarrier.{u}) (ι : K.Carrier → C.Carrier)
variable (Γ : PartialDiffeomorph halfCollarModel K.model
  (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
variable (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)

private theorem radialCollar_radiusTwo
    (hΓs : Γ.source = halfCollarSource)
    (hΓ : ∀ p, p ∈ halfCollarSource →
      ι (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) :
    ι '' Γ.target ⊆ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
  rintro x ⟨y, hy, rfl⟩
  have hp : Γ.symm y ∈ halfCollarSource := hΓs ▸ Γ.map_target hy
  have he := hΓ (Γ.symm y) hp
  have he := (congrArg ι (Γ.right_inv hy)).symm.trans he
  refine ⟨(ULift.up ((1 + (Γ.symm y).2.val 0 / 2) •
    ((Γ.symm y).1.1 : ℂ)), (Γ.symm y).1.2), ?_, he.symm⟩
  change ‖(1 + (Γ.symm y).2.val 0 / 2) • ((Γ.symm y).1.1 : ℂ)‖ ≤ 2
  have hn := (Γ.symm y).2.property
  change (Γ.symm y).2.val 0 < 1 at hp
  rw [norm_smul, Real.norm_of_nonneg (by linarith), Circle.norm_coe, mul_one]
  linarith

include hφ in
theorem exists_boundaryTori_of_fibreExcision {n : ℕ}
    (hι : Injective ι) (hΓs : Γ.source = halfCollarSource)
    (hΓb : ∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero)))
    (hΓ : ∀ p, p ∈ halfCollarSource →
      ι (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (hb : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪
      range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)))
    (hOs : O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x)
    (E : BoundaryTori C n) (hE : C.model.boundary C.Carrier = E.image) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (E' : BoundaryTori K (n + 1)),
      K.model.boundary K.Carrier = E'.image ∧
      (∀ i : Fin n, E'.collar i.castSucc = ((E.shrink hδ hδ1).collar i).trans O) ∧
      E'.collar (Fin.last n) = Γ ∧
      (∀ i : Fin n, ∀ p, p ∈ halfCollarSource →
        ι (E'.collar i.castSucc p) = (E.shrink hδ hδ1).collar i p) ∧
      (∀ p, p ∈ halfCollarSource →
        ι (E'.collar (Fin.last n) p) =
          φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) := by
  obtain ⟨δ, hδ, hδ1, ha⟩ := E.exists_shrink_avoiding_compact
    (radiusTwoTube_compact C φ hφ) (radiusTwoTube_interior C φ hφ)
  let A := E.shrink hδ hδ1
  have hsrc (i : Fin n) (p : Torus × EuclideanHalfSpace 1)
      (hp : p ∈ halfCollarSource) : A.collar i p ∈ O.source := by
    rw [hOs]
    intro hm
    exact ha i p hp (image_mono (fun q hq => by
      change ‖q.1.down‖ ≤ 1 at hq
      change ‖q.1.down‖ ≤ 2
      linarith) hm)
  let L : Fin n → PartialDiffeomorph halfCollarModel K.model
      (Torus × EuclideanHalfSpace 1) K.Carrier ∞ := fun i => (A.collar i).trans O
  have hLs (i : Fin n) : (L i).source = halfCollarSource := by
    ext p
    change (p ∈ (A.collar i).source ∧ A.collar i p ∈ O.source) ↔ p ∈ halfCollarSource
    rw [A.source_eq]
    exact ⟨And.left, fun hp => ⟨hp, hsrc i p hp⟩⟩
  have hLi (i : Fin n) (p : Torus × EuclideanHalfSpace 1)
      (hp : p ∈ halfCollarSource) : ι (L i p) = A.collar i p := hO _ (hsrc i p hp)
  have hLt (i : Fin n) {y : K.Carrier} (hy : y ∈ (L i).target) :
      ι y ∈ (A.collar i).target := by
    have hp : (L i).symm y ∈ halfCollarSource := hLs i ▸ (L i).map_target hy
    have he := hLi i ((L i).symm y) hp
    have he := (congrArg ι ((L i).right_inv hy)).symm.trans he
    rw [he]
    exact (A.collar i).map_source (A.source_eq i ▸ hp)
  have hLa (i : Fin n) {y : K.Carrier} (hy : y ∈ (L i).target) :
      ι y ∉ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
    have hp : (L i).symm y ∈ halfCollarSource := hLs i ▸ (L i).map_target hy
    have he := hLi i ((L i).symm y) hp
    have he := (congrArg ι ((L i).right_inv hy)).symm.trans he
    rw [he]
    exact ha i _ hp
  have hLb (i : Fin n) (t : Torus) : K.model.IsBoundaryPoint (L i (t, halfZero)) := by
    have hz : (t, halfZero) ∈ halfCollarSource := zero_mem_halfCollarSource t
    have ho := O.isLocalDiffeomorphAt C.model K.model ∞ (hsrc i _ hz)
    exact (ho.isBoundaryPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp (A.boundary_zero i t)
  let E' : BoundaryTori K (n + 1) := {
    collar := Fin.lastCases Γ L
    source_eq i := by
      refine Fin.lastCases ?_ (fun a => ?_) i
      · simpa only [Fin.lastCases_last] using hΓs
      · simpa only [Fin.lastCases_castSucc] using hLs a
    boundary_zero i := by
      refine Fin.lastCases ?_ (fun a => ?_) i
      · simpa only [Fin.lastCases_last] using hΓb
      · simpa only [Fin.lastCases_castSucc] using hLb a
    disjoint := by
      intro i
      refine Fin.lastCases ?_ (fun a => ?_) i
      · intro j
        refine Fin.lastCases ?_ (fun b => ?_) j
        · intro hij
          exact False.elim (hij rfl)
        · intro hij
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
          apply Set.disjoint_left.mpr
          intro y hyΓ hyL
          exact hLa b hyL (radialCollar_radiusTwo C φ K ι Γ hΓs hΓ ⟨y, hyΓ, rfl⟩)
      · intro j
        refine Fin.lastCases ?_ (fun b => ?_) j
        · intro hij
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
          apply Set.disjoint_left.mpr
          intro y hyL hyΓ
          exact hLa a hyL (radialCollar_radiusTwo C φ K ι Γ hΓs hΓ ⟨y, hyΓ, rfl⟩)
        · intro hij
          simp only [Fin.lastCases_castSucc]
          apply Set.disjoint_left.mpr
          intro y hyA hyB
          exact Set.disjoint_left.mp (A.disjoint (by intro hab; exact hij (congrArg
            Fin.castSucc hab))) (hLt a hyA) (hLt b hyB) }
  have hcast (i : Fin n) : E'.collar i.castSucc = L i := by
    change Fin.lastCases Γ L i.castSucc = L i
    exact Fin.lastCases_castSucc i
  have hlast : E'.collar (Fin.last n) = Γ := by
    change Fin.lastCases Γ L (Fin.last n) = Γ
    exact Fin.lastCases_last
  have hzero (i : Fin n) (t : Torus) : ι (E'.torusMap i.castSucc t) = E.torusMap i t := by
    change ι (E'.collar i.castSucc (t, halfZero)) = E.torusMap i t
    rw [hcast, hLi i _ (zero_mem_halfCollarSource t)]
    exact congrFun (E.shrink_torusMap hδ hδ1 i) t
  have hnew (t : Torus) : ι (E'.torusMap (Fin.last n) t) =
      φ (ULift.up (t.1 : ℂ), t.2) := by
    change ι (E'.collar (Fin.last n) (t, halfZero)) = _
    rw [hlast, hΓ _ (zero_mem_halfCollarSource t)]
    change φ (ULift.up ((1 + (0 : ℝ) / 2) • (t.1 : ℂ)), t.2) = _
    simp
  refine ⟨δ, hδ, hδ1, E', ?_, hcast, hlast, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      have him : ι x ∈ C.model.boundary C.Carrier ∪
          range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)) := hb ▸ ⟨x, hx, rfl⟩
      rcases him with ho | hn
      · rw [hE] at ho
        obtain ⟨i, t, ht⟩ := Set.mem_iUnion.mp ho
        refine Set.mem_iUnion.mpr ⟨i.castSucc, t, hι ?_⟩
        rw [hzero, ht]
      · obtain ⟨t, ht⟩ := hn
        refine Set.mem_iUnion.mpr ⟨Fin.last n, t, hι ?_⟩
        exact (hnew t).trans ht
    · intro x hx
      obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hx
      exact E'.boundary_zero i t
  · intro i p hp
    rw [hcast]
    exact hLi i p hp
  · intro p hp
    rw [hlast]
    exact hΓ p hp

include hφ in
theorem exists_fibreExcisionBoundaryTori {n : ℕ}
    (E : BoundaryTori C n) (hE : C.model.boundary C.Carrier = E.image) :
    ∃ (K : CompactCarrier.{u}) (ι : K.Carrier → C.Carrier)
      (Γ : PartialDiffeomorph halfCollarModel K.model
        (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
      (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (E' : BoundaryTori K (n + 1)),
      K.kind = .withBoundary ∧
      IsSmoothEmbedding K.model C.model ∞ ι ∧
      range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
      (∀ x, Bijective (mfderiv K.model C.model ι x)) ∧
      (∀ x, ∃ D : TangentSpace K.model x ≃L[ℝ] TangentSpace C.model (ι x),
        D.toContinuousLinearMap = mfderiv K.model C.model ι x ∧
        Orientation.map (Fin 3) D.toLinearEquiv (K.orientation.orientation x) =
          C.orientation.orientation (ι x)) ∧
      Γ.source = halfCollarSource ∧
      (∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero))) ∧
      (∀ p, p ∈ halfCollarSource →
        ι (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) ∧
      ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪
        range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)) ∧
      Disjoint (C.model.boundary C.Carrier)
        (range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2))) ∧
      O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ ∧
      (∀ x, x ∈ O.source → ι (O x) = x) ∧
      O.target = ι ⁻¹' (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ ∧
      K.model.boundary K.Carrier = E'.image ∧
      (∀ i : Fin n, E'.collar i.castSucc = ((E.shrink hδ hδ1).collar i).trans O) ∧
      E'.collar (Fin.last n) = Γ ∧
      (∀ i : Fin n, ∀ p, p ∈ halfCollarSource →
        ι (E'.collar i.castSucc p) = (E.shrink hδ hδ1).collar i p) ∧
      (∀ p, p ∈ halfCollarSource →
        ι (E'.collar (Fin.last n) p) =
          φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) := by
  obtain ⟨K, ι, Γ, O, hk, hι, hr, hbij, hor, hΓs, hΓb, hΓ, hb, hd, hOs, hO, hOt⟩ :=
    exists_fibreExcisionWithBoundary C φ hφ
  obtain ⟨δ, hδ, hδ1, E', hE', hcast, hlast, hold, hnew⟩ :=
    exists_boundaryTori_of_fibreExcision C φ hφ K ι Γ O hι.isEmbedding.injective
      hΓs hΓb hΓ hb hOs hO E hE
  exact ⟨K, ι, Γ, O, δ, hδ, hδ1, E', hk, hι, hr, hbij, hor, hΓs, hΓb,
    hΓ, hb, hd, hOs, hO, hOt, hE', hcast, hlast, hold, hnew⟩

end GC.GraphManifold.CircleFibration
