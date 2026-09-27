import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

def sphereMappingTorusRel (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) :
    SphereTwo × Set.Icc (0 : ℝ) 1 → SphereTwo × Set.Icc (0 : ℝ) 1 → Prop :=
  fun p q => (p.2 : ℝ) = 1 ∧ (q.2 : ℝ) = 0 ∧ q.1 = f p.1

def sphereMappingTorusSetoid (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) :
    Setoid (SphereTwo × Set.Icc (0 : ℝ) 1) :=
  Relation.EqvGen.setoid (sphereMappingTorusRel f)

abbrev SphereMappingTorus (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) :=
  Quotient (sphereMappingTorusSetoid f)

structure SphereMappingTorusIsotopy where
  target : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo
  isotopy : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo
  continuous_apply : Continuous fun p : SphereTwo × ℝ => isotopy p.2 p.1
  isotopy_zero : isotopy 0 = Diffeomorph.refl (𝓡 2) SphereTwo ∞
  isotopy_one : isotopy 1 = target

def sphereMappingTorusToCircle (D : SphereMappingTorusIsotopy) :
    SphereTwo × Set.Icc (0 : ℝ) 1 → SphereTwo × AddCircle (1 : ℝ) :=
  fun p => (D.isotopy (p.2 : ℝ) p.1, ((p.2 : ℝ) : AddCircle (1 : ℝ)))

theorem continuous_sphereMappingTorusToCircle (D : SphereMappingTorusIsotopy) :
    Continuous (sphereMappingTorusToCircle D) := by
  have hI : Continuous fun p : SphereTwo × Set.Icc (0 : ℝ) 1 => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hpair : Continuous fun p : SphereTwo × Set.Icc (0 : ℝ) 1 => (p.1, (p.2 : ℝ)) :=
    continuous_fst.prodMk hI
  refine Continuous.prodMk ?_ ?_
  · exact D.continuous_apply.comp hpair
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp hI

theorem sphereMappingTorusToCircle_eq_of_rel (D : SphereMappingTorusIsotopy)
    {p q : SphereTwo × Set.Icc (0 : ℝ) 1} (h : sphereMappingTorusRel D.target p q) :
    sphereMappingTorusToCircle D p = sphereMappingTorusToCircle D q := by
  obtain ⟨hp, hq, hpq⟩ := h
  simp only [sphereMappingTorusToCircle]
  rw [hp, hq, D.isotopy_one, D.isotopy_zero]
  simp only [Diffeomorph.coe_refl, id_eq, AddCircle.coe_period, AddCircle.coe_zero, hpq]

def sphereMappingTorusDescend (D : SphereMappingTorusIsotopy) :
    SphereMappingTorus D.target → SphereTwo × AddCircle (1 : ℝ) :=
  Quotient.lift (sphereMappingTorusToCircle D) fun _ _ h => by
    induction h with
    | rel x y hxy => exact sphereMappingTorusToCircle_eq_of_rel D hxy
    | refl x => rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

theorem continuous_sphereMappingTorusDescend (D : SphereMappingTorusIsotopy) :
    Continuous (sphereMappingTorusDescend D) :=
  Continuous.quotient_lift (continuous_sphereMappingTorusToCircle D) _

private lemma addCircle_one_coe_eq_coe {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h : ((s : ℝ) : AddCircle (1 : ℝ)) = ((t : ℝ) : AddCircle (1 : ℝ))) :
    s = t ∨ (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1) := by
  have h01 : ((0 : ℝ) : AddCircle (1 : ℝ)) = ((1 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_zero, AddCircle.coe_period]
  have h0I : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨le_refl _, by norm_num⟩
  rcases lt_or_eq_of_le hs.2 with hslt | hseq
  · rcases lt_or_eq_of_le ht.2 with htlt | hteq
    · have hsI : s ∈ Set.Ico (0 : ℝ) (0 + 1) :=
        ⟨hs.1, by simpa only [zero_add] using hslt⟩
      have htI : t ∈ Set.Ico (0 : ℝ) (0 + 1) :=
        ⟨ht.1, by simpa only [zero_add] using htlt⟩
      exact Or.inl ((AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ)) hsI htI).mp h)
    · have hsI : s ∈ Set.Ico (0 : ℝ) (0 + 1) :=
        ⟨hs.1, by simpa only [zero_add] using hslt⟩
      have hsz : s = 0 := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ)) hsI h0I).mp
        (h.trans (by rw [hteq]; exact h01.symm))
      exact Or.inr (Or.inr ⟨hsz, hteq⟩)
  · rcases lt_or_eq_of_le ht.2 with htlt | hteq
    · have htI : t ∈ Set.Ico (0 : ℝ) (0 + 1) :=
        ⟨ht.1, by simpa only [zero_add] using htlt⟩
      have htz : t = 0 := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ)) htI h0I).mp
        ((hseq ▸ h).symm.trans h01.symm)
      exact Or.inr (Or.inl ⟨hseq, htz⟩)
    · exact Or.inl (hseq.trans hteq.symm)

theorem sphereMappingTorusDescend_injective (D : SphereMappingTorusIsotopy) :
    Function.Injective (sphereMappingTorusDescend D) := by
  intro x y hxy
  revert hxy
  refine Quotient.inductionOn x ?_
  intro p
  refine Quotient.inductionOn y ?_
  intro q hpq
  have hfst : D.isotopy (p.2 : ℝ) p.1 = D.isotopy (q.2 : ℝ) q.1 := by
    simpa only [sphereMappingTorusDescend, Quotient.lift_mk, sphereMappingTorusToCircle]
      using congrArg Prod.fst hpq
  have hsnd : ((p.2 : ℝ) : AddCircle (1 : ℝ)) = ((q.2 : ℝ) : AddCircle (1 : ℝ)) := by
    simpa only [sphereMappingTorusDescend, Quotient.lift_mk, sphereMappingTorusToCircle]
      using congrArg Prod.snd hpq
  rcases addCircle_one_coe_eq_coe p.2.2 q.2.2 hsnd with hst | ⟨hp1, hq0⟩ | ⟨hp0, hq1⟩
  · have hz : p = q := by
      refine Prod.ext ?_ (Subtype.ext hst)
      exact (D.isotopy (p.2 : ℝ)).injective (by rw [← hst] at hfst; exact hfst)
    rw [hz]
  · have hrel : sphereMappingTorusRel D.target p q := by
      refine ⟨hp1, hq0, ?_⟩
      rw [hp1, hq0, D.isotopy_one, D.isotopy_zero] at hfst
      simpa only [Diffeomorph.coe_refl, id_eq] using hfst.symm
    exact Quotient.sound (Relation.EqvGen.rel _ _ hrel)
  · have hrel : sphereMappingTorusRel D.target q p := by
      refine ⟨hq1, hp0, ?_⟩
      rw [hp0, hq1, D.isotopy_one, D.isotopy_zero] at hfst
      simpa only [Diffeomorph.coe_refl, id_eq] using hfst
    exact Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hrel))

theorem sphereMappingTorusDescend_surjective (D : SphereMappingTorusIsotopy) :
    Function.Surjective (sphereMappingTorusDescend D) := by
  rintro ⟨w, u⟩
  obtain ⟨t, ht, htu⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) u
  let z : SphereTwo := (D.isotopy t).symm w
  let p : SphereTwo × Set.Icc (0 : ℝ) 1 := (z, ⟨t, ⟨ht.1, le_of_lt ht.2⟩⟩)
  refine ⟨Quotient.mk _ p, ?_⟩
  have hval : ((p.2 : ℝ)) = t := rfl
  rw [sphereMappingTorusDescend, Quotient.lift_mk, sphereMappingTorusToCircle, hval]
  refine Prod.ext ?_ htu
  exact (D.isotopy t).apply_symm_apply w

theorem sphereMappingTorusDescend_bijective (D : SphereMappingTorusIsotopy) :
    Function.Bijective (sphereMappingTorusDescend D) :=
  ⟨sphereMappingTorusDescend_injective D, sphereMappingTorusDescend_surjective D⟩

def sphereMappingTorusHomeomorph (D : SphereMappingTorusIsotopy) :
    SphereMappingTorus D.target ≃ₜ SphereTwo × AddCircle (1 : ℝ) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (sphereMappingTorusDescend_bijective D))
    (continuous_sphereMappingTorusDescend D)

@[simp]
theorem sphereMappingTorusHomeomorph_apply (D : SphereMappingTorusIsotopy)
    (x : SphereMappingTorus D.target) :
    sphereMappingTorusHomeomorph D x = sphereMappingTorusDescend D x := rfl

@[simp]
theorem sphereMappingTorusHomeomorph_mk (D : SphereMappingTorusIsotopy)
    (p : SphereTwo × Set.Icc (0 : ℝ) 1) :
    sphereMappingTorusHomeomorph D (Quotient.mk _ p) =
      (D.isotopy (p.2 : ℝ) p.1, ((p.2 : ℝ) : AddCircle (1 : ℝ))) := by
  rw [sphereMappingTorusHomeomorph_apply, sphereMappingTorusDescend, Quotient.lift_mk]
  rfl

def addCircleOneHomeomorphSphereOne :
    AddCircle (1 : ℝ) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) (by norm_num)).trans circleSphereOneHomeomorph

def sphereMappingTorusHomeomorphSphereTwoTimesCircle (D : SphereMappingTorusIsotopy) :
    SphereMappingTorus D.target ≃ₜ SphereTwoTimesCircle :=
  (sphereMappingTorusHomeomorph D).trans
    (Homeomorph.prodCongr (Homeomorph.refl SphereTwo) addCircleOneHomeomorphSphereOne)

theorem sphereMappingTorusHomeomorphSphereTwoTimesCircle_apply (D : SphereMappingTorusIsotopy)
    (p : SphereTwo × Set.Icc (0 : ℝ) 1) :
    sphereMappingTorusHomeomorphSphereTwoTimesCircle D (Quotient.mk _ p) =
      (D.isotopy (p.2 : ℝ) p.1,
        addCircleOneHomeomorphSphereOne ((p.2 : ℝ) : AddCircle (1 : ℝ))) := by
  rw [sphereMappingTorusHomeomorphSphereTwoTimesCircle, Homeomorph.trans_apply,
    sphereMappingTorusHomeomorph_mk]
  rfl

theorem sphereMappingTorusHomeomorph_symm_apply (D : SphereMappingTorusIsotopy)
    (w : SphereTwo) (u : AddCircle (1 : ℝ)) :
    (sphereMappingTorusHomeomorph D).symm (w, u) =
      Quotient.mk _
        ((D.isotopy (AddCircle.equivIco (1 : ℝ) 0 u).val).symm w,
          ⟨(AddCircle.equivIco (1 : ℝ) 0 u).val,
            ⟨(AddCircle.equivIco (1 : ℝ) 0 u).property.1,
              le_of_lt (by
                simpa only [zero_add] using
                  (AddCircle.equivIco (1 : ℝ) 0 u).property.2)⟩⟩) := by
  refine (Homeomorph.symm_apply_eq (sphereMappingTorusHomeomorph D)).mpr ?_
  rw [sphereMappingTorusHomeomorph_mk]
  dsimp only
  rw [Prod.mk.injEq]
  exact ⟨((D.isotopy (AddCircle.equivIco (1 : ℝ) 0 u).val).apply_symm_apply w).symm,
    (AddCircle.coe_equivIco (a := (0 : ℝ)) (y := u)).symm⟩

theorem sphereMappingTorusHomeomorphSphereTwoTimesCircle_circleExp
    (D : SphereMappingTorusIsotopy) (p : SphereTwo × Set.Icc (0 : ℝ) 1) :
    sphereMappingTorusHomeomorphSphereTwoTimesCircle D (Quotient.mk _ p) =
      (D.isotopy (p.2 : ℝ) p.1,
        circleSphereOneHomeomorph (Circle.exp (2 * Real.pi * (p.2 : ℝ)))) := by
  rw [sphereMappingTorusHomeomorphSphereTwoTimesCircle_apply, addCircleOneHomeomorphSphereOne,
    Homeomorph.trans_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  ring_nf


def sphereMappingTorusIsotopyRefl : SphereMappingTorusIsotopy where
  target := Diffeomorph.refl (𝓡 2) SphereTwo ∞
  isotopy := fun _ => Diffeomorph.refl (𝓡 2) SphereTwo ∞
  continuous_apply := by
    simpa only [Diffeomorph.coe_refl, id_eq] using
      (continuous_fst : Continuous fun p : SphereTwo × ℝ => p.1)
  isotopy_zero := rfl
  isotopy_one := rfl

theorem sphereMappingTorusHomeomorphSphereTwoTimesCircle_refl_apply
    (p : SphereTwo × Set.Icc (0 : ℝ) 1) :
    sphereMappingTorusHomeomorphSphereTwoTimesCircle sphereMappingTorusIsotopyRefl
        (Quotient.mk _ p) =
      (p.1, addCircleOneHomeomorphSphereOne ((p.2 : ℝ) : AddCircle (1 : ℝ))) := by
  rw [sphereMappingTorusHomeomorphSphereTwoTimesCircle_apply]
  rfl

theorem sphereMappingTorusHomeomorphSphereTwoTimesCircle_refl :
    Nonempty
      (SphereMappingTorus (Diffeomorph.refl (𝓡 2) SphereTwo ∞) ≃ₜ SphereTwoTimesCircle) :=
  ⟨sphereMappingTorusHomeomorphSphereTwoTimesCircle sphereMappingTorusIsotopyRefl⟩

end DifferentialGeometry.Topology
