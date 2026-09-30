import DifferentialGeometry.Topology.ThreeManifold.PuncturedCapping
import DifferentialGeometry.Topology.ThreeManifold.CappedCoreCylinderGluing
import DifferentialGeometry.Topology.Diffeomorph.IntervalGerm

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Annulus" => S2 × Icc (1 / 4 : ℝ) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)
local notation "Cylinder" => S2 × unitInterval

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private def annulusParameter (ρ : ℝ ≃ₘ[ℝ] ℝ)
    (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1)) (side : Bool)
    (r : Icc (1 / 4 : ℝ) 1) : unitInterval :=
  ⟨(1 + (if side then ρ r.val else -ρ r.val)) / 2, by
    have h := hρ r.property
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> constructor <;> linarith [h.1,h.2]⟩

private def uncappingAnnulusMap
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1)) :
    C((Σ _b : T.Boundary, Annulus), M.Carrier) where
  toFun q := T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1, annulusParameter ρ hρ q.1.2 q.2.2))
  continuous_toFun := continuous_sigma fun b => (T.cylinderMap b.1).continuous.comp
    ((Ψ b.1).continuous.comp (continuous_fst.prodMk (by
      apply Continuous.subtype_mk
      change Continuous (fun q : Annulus => (1 + (if b.2 then ρ q.2.val else -ρ q.2.val)) / 2)
      cases b.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop)))

private theorem cylinderMap_end (a : T.Index) (side : Bool) (z : S2) :
    T.cylinderMap a (z, if side then 1 else 0) = T.boundarySphere (a, side) z := by
  change T.tube a (z, _) = T.tube a (z, _)
  apply congrArg (T.tube a)
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    cases side <;> norm_num [SphericalTubeSystem.boundaryLevel]

private theorem uncappingAnnulusMap_outer
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a side z, Ψ a (z, if side then 1 else 0) = (C.attaching (a, side) z, if side then 1 else 0))
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hone : ρ 1 = 1) (b : T.Boundary) (z : S2) :
    uncappingAnnulusMap (T := T) Ψ ρ hρ ⟨b, z, ⟨1, by norm_num⟩⟩ =
      T.boundarySphere b (C.attaching b z) := by
  have ht : annulusParameter ρ hρ b.2 ⟨1, by norm_num⟩ = if b.2 then 1 else 0 := by
    apply Subtype.ext
    cases b.2 <;> simp [annulusParameter, hone]
  change T.cylinderMap b.1 (Ψ b.1 (z, annulusParameter ρ hρ b.2 _)) = _
  rw [ht, hΨ, cylinderMap_end]

private def puncturedUncappingMap
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a side z, Ψ a (z, if side then 1 else 0) = (C.attaching (a, side) z, if side then 1 else 0))
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hone : ρ 1 = 1) : C(C.PuncturedCapping, M.Carrier) := by
  let f : (Σ _b : T.Boundary, Annulus) ⊕ range C.coreInclusion → M.Carrier :=
    Sum.elim (uncappingAnnulusMap Ψ ρ hρ) (fun x => (C.coreImageHomeomorph.symm x).val)
  have hf : ∀ x y, adjunctionRel (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap x y → f x = f y := by
    rintro x y ⟨q, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · change uncappingAnnulusMap Ψ ρ hρ ⟨q.1, q.2, ⟨1, by norm_num⟩⟩ = _
      rw [uncappingAnnulusMap_outer C Ψ hΨ ρ hρ hone]
      change _ = (C.coreImageHomeomorph.symm (C.coreImageHomeomorph
        (T.coreBoundarySphere q.1 (C.attaching q.1 q.2)))).val
      rw [C.coreImageHomeomorph.symm_apply_apply]
      rfl
    · change _ = uncappingAnnulusMap Ψ ρ hρ ⟨q.1, q.2, ⟨1, by norm_num⟩⟩
      rw [uncappingAnnulusMap_outer C Ψ hΨ ρ hρ hone]
      change (C.coreImageHomeomorph.symm (C.coreImageHomeomorph
        (T.coreBoundarySphere q.1 (C.attaching q.1 q.2)))).val = _
      rw [C.coreImageHomeomorph.symm_apply_apply]
      rfl
  exact ⟨Quot.lift f hf, continuous_adjunction_lift _ _ hf
    ((uncappingAnnulusMap Ψ ρ hρ).continuous.sumElim
      (continuous_subtype_val.comp C.coreImageHomeomorph.symm.continuous))⟩

private theorem puncturedUncappingMap_core
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a side z, Ψ a (z, if side then 1 else 0) = (C.attaching (a, side) z, if side then 1 else 0))
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hone : ρ 1 = 1) (x : T.core) :
    C.puncturedUncappingMap Ψ hΨ ρ hρ hone
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x)) = x.val := by
  change (C.coreImageHomeomorph.symm (C.coreImageHomeomorph x)).val = x.val
  rw [C.coreImageHomeomorph.symm_apply_apply]

private theorem puncturedUncappingMap_inner
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a side z, Ψ a (z, if side then 1 else 0) = (C.attaching (a, side) z, if side then 1 else 0))
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hone : ρ 1 = 1) (hzero : ρ (1 / 4) = 0) (a : T.Index) (z : S2) :
    C.puncturedUncappingMap Ψ hΨ ρ hρ hone
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨(a, false), z, ⟨1 / 4, by norm_num⟩⟩) =
    C.puncturedUncappingMap Ψ hΨ ρ hρ hone
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨(a, true), z, ⟨1 / 4, by norm_num⟩⟩) := by
  change T.cylinderMap a (Ψ a (z, annulusParameter ρ hρ false _)) =
    T.cylinderMap a (Ψ a (z, annulusParameter ρ hρ true _))
  apply congrArg (fun t : unitInterval => T.cylinderMap a (Ψ a (z,t)))
  apply Subtype.ext
  change (1 + -ρ (1 / 4)) / 2 = (1 + ρ (1 / 4)) / 2
  rw [hzero]
  norm_num

private theorem puncturedUncappingMap_core_annulus
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a side z, Ψ a (z, if side then 1 else 0) = (C.attaching (a, side) z, if side then 1 else 0))
    (htime : ∀ a p, (Ψ a p).2 = p.2)
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hone : ρ 1 = 1) (x : T.core) (q : Σ _b : T.Boundary, Annulus)
    (heq : (C.puncturedUncappingMap Ψ hΨ ρ hρ hone)
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x)) =
      (C.puncturedUncappingMap Ψ hΨ ρ hρ hone)
        (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q)) :
    adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
      (C.coreImageHomeomorph x) =
      adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q := by
  rw [C.puncturedUncappingMap_core] at heq
  change x.val = T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1, annulusParameter ρ hρ q.1.2 q.2.2)) at heq
  let p := Ψ q.1.1 (q.2.1, annulusParameter ρ hρ q.1.2 q.2.2)
  let t : Icc (-2 : ℝ) 2 := ⟨2 * p.2.val - 1, by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩
  have hcore : T.tube q.1.1 (p.1,t) ∈ T.core := heq ▸ x.property
  have hband : -1 ≤ t.val ∧ t.val ≤ 1 := by dsimp [t]; constructor <;> linarith [p.2.property.1,p.2.property.2]
  have hend := T.eq_boundaryLevel_of_mem_band_of_mem_core hband hcore
  have hparam : p.2 = annulusParameter ρ hρ q.1.2 q.2.2 := htime _ _
  have hr : q.2.2.val = 1 := by
    apply ρ.injective
    change ρ q.2.2.val = ρ 1
    rw [hone]
    have hbound := hρ q.2.2.property
    have htval : t.val = if q.1.2 then ρ q.2.2.val else -ρ q.2.2.val := by
      change 2 * p.2.val - 1 = _
      rw [hparam]
      change 2 * ((1 + (if q.1.2 then ρ q.2.2.val else -ρ q.2.2.val))/2) - 1 = _
      ring
    change t.val = -1 ∨ t.val = 1 at hend
    rw [htval] at hend
    rcases hend with h | h <;>
      cases hs : q.1.2 <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at h <;> linarith [hbound.1,hbound.2]
  have htone : q.2.2 = (⟨1,by norm_num⟩ : Icc (1 / 4 : ℝ) 1) := Subtype.ext hr
  have hq : q = ⟨q.1,q.2.1,⟨1,by norm_num⟩⟩ :=
    congrArg (fun r : Icc (1 / 4 : ℝ) 1 => (⟨q.1,q.2.1,r⟩ : Σ _b : T.Boundary,Annulus)) htone
  rw [hq] at heq ⊢
  have hx : x = T.coreBoundarySphere q.1 (C.attaching q.1 q.2.1) := by
    apply Subtype.ext
    exact heq.trans (uncappingAnnulusMap_outer C Ψ hΨ ρ hρ hone q.1 q.2.1)
  rw [hx]
  exact (adjunction_coherence (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
    ⟨q.1,q.2.1⟩).symm

private theorem signed_annulus_parameter_eq_iff
    (ρ : ℝ ≃ₘ[ℝ] ℝ)
    (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hzero : ρ (1 / 4) = 0) (s t : Bool) (r r' : Icc (1 / 4 : ℝ) 1) :
    (1 + (if s then ρ r.val else -ρ r.val)) / 2 =
        (1 + (if t then ρ r'.val else -ρ r'.val)) / 2 ↔
      (s = t ∧ r = r') ∨ (r.val = 1 / 4 ∧ r'.val = 1 / 4) := by
  have hr : 0 ≤ ρ r.val := (hρ r.property).1
  have hr' : 0 ≤ ρ r'.val := (hρ r'.property).1
  constructor
  · intro h
    by_cases hst : s = t
    · refine Or.inl ⟨hst, ?_⟩
      apply Subtype.ext
      apply ρ.injective
      change ρ r.val = ρ r'.val
      subst t
      cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h <;> linarith
    · have hs : ρ r.val = 0 ∧ ρ r'.val = 0 := by
        cases s <;> cases t <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h <;>
          first | exact False.elim (hst rfl) | constructor <;> linarith
      exact Or.inr ⟨ρ.injective (hs.1.trans hzero.symm), ρ.injective (hs.2.trans hzero.symm)⟩
  · rintro (⟨hst, hrr⟩ | ⟨hr0, hr0'⟩)
    · rw [hst, hrr]
    · rw [hr0, hr0', hzero]
      simp only [neg_zero, ite_self]

private theorem uncappingAnnulusMap_eq_iff
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hzero : ρ (1 / 4) = 0) (q q' : Σ _b : T.Boundary, Annulus) :
    uncappingAnnulusMap (T := T) Ψ ρ hρ q = uncappingAnnulusMap Ψ ρ hρ q' ↔
      q = q' ∨ (q.1.1 = q'.1.1 ∧ q.2.1 = q'.2.1 ∧
        q.2.2.val = 1 / 4 ∧ q'.2.2.val = 1 / 4) := by
  constructor
  · intro h
    let p := Ψ q.1.1 (q.2.1,annulusParameter ρ hρ q.1.2 q.2.2)
    let p' := Ψ q'.1.1 (q'.2.1,annulusParameter ρ hρ q'.1.2 q'.2.2)
    have ha : q.1.1 = q'.1.1 := by
      by_contra hne
      exact Set.disjoint_left.mp (T.disjoint hne)
        ⟨_,rfl⟩ ⟨_,h.symm⟩
    have hpp : p = p' := by
      have h' : T.cylinderMap q.1.1 p = T.cylinderMap q.1.1 p' := by
        change T.cylinderMap q.1.1 p = T.cylinderMap q'.1.1 p' at h
        simpa only [ha] using h
      exact T.cylinderMap_injective q.1.1 h'
    have hinput : (q.2.1,annulusParameter ρ hρ q.1.2 q.2.2) =
        (q'.2.1,annulusParameter ρ hρ q'.1.2 q'.2.2) := by
      apply (Ψ q.1.1).injective
      change p = Ψ q.1.1 (q'.2.1,annulusParameter ρ hρ q'.1.2 q'.2.2)
      rw [ha]
      exact hpp
    have hz := congrArg (fun p : Cylinder => p.1) hinput
    have hs := congrArg (fun p : Cylinder => p.2.val) hinput
    rcases (signed_annulus_parameter_eq_iff ρ hρ hzero q.1.2 q'.1.2 q.2.2 q'.2.2).mp hs with
      ⟨hside,hr⟩ | ⟨hr,hr'⟩
    · left
      have hb : q.1 = q'.1 := Prod.ext ha hside
      have hq : q.2 = q'.2 := Prod.ext hz hr
      exact Sigma.ext hb (heq_of_eq hq)
    · exact Or.inr ⟨ha,hz,hr,hr'⟩
  · rintro (rfl | ⟨ha,hz,hr,hr'⟩)
    · rfl
    · change T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1,annulusParameter ρ hρ q.1.2 q.2.2)) =
        T.cylinderMap q'.1.1 (Ψ q'.1.1 (q'.2.1,annulusParameter ρ hρ q'.1.2 q'.2.2))
      rw [ha,hz]
      apply congrArg (fun t : unitInterval => T.cylinderMap q'.1.1 (Ψ q'.1.1 (q'.2.1,t)))
      apply Subtype.ext
      exact (signed_annulus_parameter_eq_iff ρ hρ hzero q.1.2 q'.1.2 q.2.2 q'.2.2).mpr
        (Or.inr ⟨hr,hr'⟩)

private theorem puncturedUncappingMap_surjective
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a side z, Ψ a (z, if side then 1 else 0) = (C.attaching (a, side) z, if side then 1 else 0))
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hone : ρ 1 = 1) (himage : ρ '' Icc (1 / 4 : ℝ) 1 = Icc (0 : ℝ) 1) :
    Function.Surjective (C.puncturedUncappingMap Ψ hΨ ρ hρ hone) := by
  intro x
  have hx : x ∈ T.core ∪ T.bandRange := T.core_union_bandRange ▸ mem_univ x
  rcases hx with hx | hx
  · exact ⟨adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
      (C.coreImageHomeomorph ⟨x,hx⟩), C.puncturedUncappingMap_core Ψ hΨ ρ hρ hone ⟨x,hx⟩⟩
  · obtain ⟨a, q, hq, hqx⟩ := mem_iUnion.mp hx
    let t : unitInterval := ⟨(q.2.val + 1) / 2, by constructor <;> linarith [hq.1,hq.2]⟩
    let p := (Ψ a).symm (q.1,t)
    have hcx : T.cylinderMap a (Ψ a p) = x := by
      rw [(Ψ a).apply_symm_apply]
      change T.tube a (q.1, _) = x
      have htq : (⟨2 * t.val - 1, by constructor <;> linarith [t.property.1,t.property.2]⟩ : Icc (-2 : ℝ) 2) = q.2 :=
        Subtype.ext (by dsimp [t]; ring)
      rw [htq]
      exact hqx
    by_cases hside : 1 / 2 ≤ p.2.val
    · have hmem : 2 * p.2.val - 1 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [p.2.property.2]
      rw [← himage] at hmem
      obtain ⟨r,hr,hrr⟩ := hmem
      refine ⟨adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨(a,true),p.1,⟨r,hr⟩⟩, ?_⟩
      change T.cylinderMap a (Ψ a (p.1,annulusParameter ρ hρ true ⟨r,hr⟩)) = x
      have heq : annulusParameter ρ hρ true ⟨r,hr⟩ = p.2 := by
        apply Subtype.ext
        change (1 + ρ r) / 2 = p.2.val
        rw [hrr]
        ring
      rw [heq]
      exact hcx
    · have hmem : 1 - 2 * p.2.val ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [p.2.property.1]
      rw [← himage] at hmem
      obtain ⟨r,hr,hrr⟩ := hmem
      refine ⟨adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨(a,false),p.1,⟨r,hr⟩⟩, ?_⟩
      change T.cylinderMap a (Ψ a (p.1,annulusParameter ρ hρ false ⟨r,hr⟩)) = x
      have heq : annulusParameter ρ hρ false ⟨r,hr⟩ = p.2 := by
        apply Subtype.ext
        change (1 + -ρ r) / 2 = p.2.val
        rw [hrr]
        ring
      rw [heq]
      exact hcx

def innerCapBoundary (a : T.Index) (side : Bool) (z : S2) : C.PuncturedCapping :=
  adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
    ⟨(a,side),z,⟨1 / 4,by norm_num⟩⟩

def innerCapRelation (x y : C.PuncturedCapping) : Prop :=
  ∃ a z, (x = C.innerCapBoundary a false z ∧ y = C.innerCapBoundary a true z) ∨
    (y = C.innerCapBoundary a false z ∧ x = C.innerCapBoundary a true z)

abbrev UncappingQuotient := Quot C.innerCapRelation

private theorem puncturedUncappingMap_eq_quotient
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a side z, Ψ a (z, if side then 1 else 0) = (C.attaching (a, side) z, if side then 1 else 0))
    (htime : ∀ a p, (Ψ a p).2 = p.2)
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hone : ρ 1 = 1) (hzero : ρ (1 / 4) = 0)
    (p q : C.PuncturedCapping)
    (heq : C.puncturedUncappingMap Ψ hΨ ρ hρ hone p = C.puncturedUncappingMap Ψ hΨ ρ hρ hone q) :
    Quot.mk C.innerCapRelation p = Quot.mk C.innerCapRelation q := by
  induction p using Quot.inductionOn with
  | h p =>
    induction q using Quot.inductionOn with
    | h q =>
      cases p with
      | inr x =>
        obtain ⟨x,rfl⟩ := C.coreImageHomeomorph.surjective x
        cases q with
        | inr y =>
          obtain ⟨y,rfl⟩ := C.coreImageHomeomorph.surjective y
          have hxy : x.val = y.val := by
            change (C.coreImageHomeomorph.symm (C.coreImageHomeomorph x)).val =
              (C.coreImageHomeomorph.symm (C.coreImageHomeomorph y)).val at heq
            simpa only [C.coreImageHomeomorph.symm_apply_apply] using heq
          have hh : x = y := Subtype.ext hxy
          subst y
          rfl
        | inl q =>
          exact congrArg (Quot.mk C.innerCapRelation)
            (C.puncturedUncappingMap_core_annulus Ψ hΨ htime ρ hρ hone x q heq)
      | inl p =>
        cases q with
        | inr y =>
          obtain ⟨y,rfl⟩ := C.coreImageHomeomorph.surjective y
          exact congrArg (Quot.mk C.innerCapRelation)
            (C.puncturedUncappingMap_core_annulus Ψ hΨ htime ρ hρ hone y p heq.symm).symm
        | inl q =>
          change uncappingAnnulusMap Ψ ρ hρ p = uncappingAnnulusMap Ψ ρ hρ q at heq
          rcases (uncappingAnnulusMap_eq_iff Ψ ρ hρ hzero p q).mp heq with hpq | ⟨ha,hz,hr,hr'⟩
          · subst q
            rfl
          · have hp : p = ⟨(p.1.1,p.1.2),p.2.1,⟨1 / 4,by norm_num⟩⟩ :=
              congrArg (fun r : Icc (1 / 4 : ℝ) 1 => (⟨p.1,p.2.1,r⟩ : Σ _b : T.Boundary,Annulus))
                (show p.2.2 = ⟨1 / 4,by norm_num⟩ from Subtype.ext hr)
            have hq : q = ⟨(p.1.1,q.1.2),p.2.1,⟨1 / 4,by norm_num⟩⟩ := by
              rw [ha,hz]
              exact congrArg (fun r : Icc (1 / 4 : ℝ) 1 => (⟨q.1,q.2.1,r⟩ : Σ _b : T.Boundary,Annulus))
                (show q.2.2 = ⟨1 / 4,by norm_num⟩ from Subtype.ext hr')
            change Quot.mk C.innerCapRelation (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap p) =
              Quot.mk C.innerCapRelation (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q)
            rw [hp,hq]
            cases p.1.2 <;> cases q.1.2
            · rfl
            · exact Quot.sound ⟨p.1.1,p.2.1,Or.inl ⟨rfl,rfl⟩⟩
            · exact Quot.sound ⟨p.1.1,p.2.1,Or.inr ⟨rfl,rfl⟩⟩
            · rfl

private def uncappingQuotientHomeomorph
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a side z, Ψ a (z, if side then 1 else 0) = (C.attaching (a, side) z, if side then 1 else 0))
    (htime : ∀ a p, (Ψ a p).2 = p.2)
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hone : ρ 1 = 1) (hzero : ρ (1 / 4) = 0)
    (himage : ρ '' Icc (1 / 4 : ℝ) 1 = Icc (0 : ℝ) 1) :
    C.UncappingQuotient ≃ₜ M.Carrier := by
  let F := C.puncturedUncappingMap Ψ hΨ ρ hρ hone
  have hrel : ∀ p q, C.innerCapRelation p q → F p = F q := by
    rintro p q ⟨a,z,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact C.puncturedUncappingMap_inner Ψ hΨ ρ hρ hone hzero a z
    · exact (C.puncturedUncappingMap_inner Ψ hΨ ρ hρ hone hzero a z).symm
  let G : C.UncappingQuotient → M.Carrier := Quot.lift F hrel
  have hG : Continuous G := continuous_quot_lift hrel F.continuous
  have hinj : Function.Injective G := by
    intro p q h
    induction p using Quot.inductionOn with
    | h p =>
      induction q using Quot.inductionOn with
      | h q => exact C.puncturedUncappingMap_eq_quotient Ψ hΨ htime ρ hρ hone hzero p q h
  have hsurj : Function.Surjective G := by
    intro y
    obtain ⟨p,hp⟩ := C.puncturedUncappingMap_surjective Ψ hΨ ρ hρ hone himage y
    exact ⟨Quot.mk _ p,hp⟩
  let _ : CompactSpace T.core := isCompact_iff_compactSpace.mp C.core_compact
  let _ : CompactSpace (range C.coreInclusion) :=
    isCompact_iff_compactSpace.mp (isCompact_range C.coreInclusion.continuous)
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G ⟨hinj,hsurj⟩) hG

private theorem uncappingQuotientHomeomorph_mk
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a side z, Ψ a (z, if side then 1 else 0) = (C.attaching (a, side) z, if side then 1 else 0))
    (htime : ∀ a p, (Ψ a p).2 = p.2)
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hone : ρ 1 = 1) (hzero : ρ (1 / 4) = 0)
    (himage : ρ '' Icc (1 / 4 : ℝ) 1 = Icc (0 : ℝ) 1) (p : C.PuncturedCapping) :
    C.uncappingQuotientHomeomorph Ψ hΨ htime ρ hρ hone hzero himage (Quot.mk _ p) =
      C.puncturedUncappingMap Ψ hΨ ρ hρ hone p := rfl

theorem exists_uncapping_homeomorph :
    ∃ (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder) (ρ : ℝ ≃ₘ[ℝ] ℝ)
      (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1)),
      ρ (1 / 4) = 0 ∧ ρ 1 = 1 ∧ (∀ r, 0 < deriv ρ r) ∧
      (∃ ε₀ ε₁ : ℝ, 0 < ε₀ ∧ 0 < ε₁ ∧
        (∀ r, |r - 1 / 4| ≤ ε₀ → ρ r = r - 1 / 4) ∧
        ∀ r, 1 - ε₁ ≤ r → ρ r = r) ∧
      (∀ a p, (Ψ a p).2 = p.2) ∧
      (∀ a (t : unitInterval), t.val ≤ 1 / 3 → ∀ z, Ψ a (z,t) = (C.attaching (a,false) z,t)) ∧
      (∀ a (t : unitInterval), 2 / 3 ≤ t.val → ∀ z, Ψ a (z,t) = (C.attaching (a,true) z,t)) ∧
      ∃ F : C(C.PuncturedCapping, M.Carrier), Function.Surjective F ∧
        (∀ x : T.core, F (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
          C.capAnnuliAttachingMap (C.coreImageHomeomorph x)) = x.val) ∧
        (∀ q : Σ _b : T.Boundary, Annulus,
          F (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q) =
            T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1,
              ⟨(1 + (if q.1.2 then ρ q.2.2.val else -ρ q.2.2.val)) / 2, by
                have h := hρ q.2.2.property
                cases q.1.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
                  constructor <;> linarith [h.1,h.2]⟩))) ∧
        (∀ a z, F (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
            ⟨(a,false),z,⟨1 / 4,by norm_num⟩⟩) =
          F (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
            ⟨(a,true),z,⟨1 / 4,by norm_num⟩⟩)) ∧
        ∃ H : C.UncappingQuotient ≃ₜ M.Carrier, ∀ p, H (Quot.mk C.innerCapRelation p) = F p := by
  choose Ψ hp hlo hhi using C.exists_cylinder_diffeomorph_attaching
  have hΨ (a : T.Index) (side : Bool) (z : S2) :
      Ψ a (z, if side then 1 else 0) = (C.attaching (a,side) z, if side then 1 else 0) := by
    cases side with
    | false => exact hlo a 0 (by norm_num) z
    | true => exact hhi a 1 (by norm_num) z
  obtain ⟨ρ, hzero, hone, hpos, himage, ε₀, ε₁, hε₀, hε₁, hloρ, hhiρ⟩ :=
    Diffeomorph.exists_interval_diffeomorph_eq_translation_near_endpoints
      (by norm_num : (1 / 4 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  have hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro r hr
    rw [← himage]
    exact ⟨r,hr,rfl⟩
  refine ⟨Ψ, ρ, hρ, hzero, hone, hpos, ?_, hp, hlo, hhi,
    C.puncturedUncappingMap Ψ hΨ ρ hρ hone,
    C.puncturedUncappingMap_surjective Ψ hΨ ρ hρ hone himage,
    C.puncturedUncappingMap_core Ψ hΨ ρ hρ hone, fun _ => rfl,
    C.puncturedUncappingMap_inner Ψ hΨ ρ hρ hone hzero,
    C.uncappingQuotientHomeomorph Ψ hΨ hp ρ hρ hone hzero himage,
    C.uncappingQuotientHomeomorph_mk Ψ hΨ hp ρ hρ hone hzero himage⟩
  exact ⟨ε₀, ε₁, hε₀, hε₁, fun r hr => (hloρ r hr).trans (by ring),
    fun r hr => (hhiρ r hr).trans (by ring)⟩

end DifferentialGeometry.Topology.SphericalCapping
