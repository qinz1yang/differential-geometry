import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv

namespace DifferentialGeometry.Topology.Homotopy

universe u v

open ContinuousMap
open unitInterval

structure StrongDeformationRetract {X : Type u} [TopologicalSpace X] (A : Set X) where
  retraction : C(X, A)
  homotopy : ContinuousMap.HomotopyRel (ContinuousMap.id X)
    (((ContinuousMap.id X).restrict A).comp retraction) A

namespace StrongDeformationRetract

variable {X : Type u} [TopologicalSpace X] {A : Set X}

theorem homotopy_fixed_on (r : StrongDeformationRetract A) (t : I) {x : X} (hx : x ∈ A) :
    r.homotopy (t, x) = x :=
  r.homotopy.eq_fst t hx

theorem retraction_eq (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A) :
    (r.retraction x : X) = x :=
  (r.homotopy.apply_one x).symm.trans (r.homotopy_fixed_on 1 hx)

noncomputable def toHomotopyEquiv (r : StrongDeformationRetract A) : X ≃ₕ A where
  toFun := r.retraction
  invFun := (ContinuousMap.id X).restrict A
  left_inv := ⟨r.homotopy.toHomotopy.symm⟩
  right_inv := by
    have h : r.retraction.comp ((ContinuousMap.id X).restrict A) = ContinuousMap.id A := by
      ext a
      simpa using r.retraction_eq a.2
    simpa [h] using (Homotopic.refl (ContinuousMap.id A))

@[simp]
theorem toHomotopyEquiv_apply (r : StrongDeformationRetract A) (x : X) :
    (r.toHomotopyEquiv x : A) = r.retraction x :=
  rfl

@[simp]
theorem toHomotopyEquiv_symm_apply (r : StrongDeformationRetract A) (a : A) :
    (r.toHomotopyEquiv.symm a : X) = (a : X) :=
  rfl

variable {Y : Type v} [TopologicalSpace Y] {B : Set Y}

def prod (r₁ : StrongDeformationRetract A) (r₂ : StrongDeformationRetract B) :
    StrongDeformationRetract (A ×ˢ B : Set (X × Y)) where
  retraction := ⟨fun p => ⟨(r₁.retraction p.1, r₂.retraction p.2),
    ⟨(r₁.retraction p.1).2, (r₂.retraction p.2).2⟩⟩, by
      exact Continuous.subtype_mk
        ((continuous_subtype_val.comp (r₁.retraction.continuous.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp (r₂.retraction.continuous.comp continuous_snd)))
        (by
          intro p
          exact ⟨(r₁.retraction p.1).2, (r₂.retraction p.2).2⟩)⟩
  homotopy := {
    toHomotopy := {
      toContinuousMap := ⟨fun p : I × (X × Y) => (r₁.homotopy (p.1, p.2.1), r₂.homotopy (p.1, p.2.2)),
        by fun_prop⟩
      map_zero_left := by
        intro x
        ext <;> simp [r₁.homotopy.apply_zero, r₂.homotopy.apply_zero]
      map_one_left := by
        intro x
        ext <;> simp [r₁.homotopy.apply_one, r₂.homotopy.apply_one]
    }
    prop' := by
      intro t x hx
      ext <;> simp [r₁.homotopy.eq_fst t hx.1, r₂.homotopy.eq_fst t hx.2]
  }

@[simp]
theorem prod_retraction_apply (r₁ : StrongDeformationRetract A) (r₂ : StrongDeformationRetract B)
    (x : X) (y : Y) :
    (((StrongDeformationRetract.prod r₁ r₂).retraction (x, y) :
        {p : X × Y // p ∈ A ×ˢ B}) : X × Y) = ((r₁.retraction x : X), (r₂.retraction y : Y)) := by
  rfl

@[simp]
theorem prod_homotopy_apply (r₁ : StrongDeformationRetract A) (r₂ : StrongDeformationRetract B)
    (t : I) (x : X) (y : Y) :
    ((StrongDeformationRetract.prod r₁ r₂).homotopy (t, (x, y)) : X × Y) =
      (r₁.homotopy (t, x), r₂.homotopy (t, y)) := by
  rfl

def refl (X : Type u) [TopologicalSpace X] : StrongDeformationRetract (Set.univ : Set X) where
  retraction := ⟨fun x => ⟨x, trivial⟩,
    continuous_id.subtype_mk (p := fun x : X => x ∈ Set.univ) (fun x => trivial)⟩
  homotopy := {
    toHomotopy := ContinuousMap.Homotopy.refl (ContinuousMap.id X)
    prop' := by
      intro t x hx
      rfl
  }

@[simp]
theorem refl_retraction_apply (x : X) :
    (((StrongDeformationRetract.refl X).retraction x : Set.univ) : X) = x := by
  rfl

@[simp]
theorem refl_homotopy_apply (t : I) (x : X) :
    (StrongDeformationRetract.refl X).homotopy (t, x) = x := by
  rfl

def congr {A B : Set X} (h : A = B) (r : StrongDeformationRetract A) : StrongDeformationRetract B := by
  let retraction : C(X, B) := ⟨fun x => ⟨(r.retraction x : X), by simpa [h] using (r.retraction x).2⟩,
    (continuous_subtype_val.comp r.retraction.continuous).subtype_mk
      (p := fun x : X => x ∈ B) (fun x => by simpa [h] using (r.retraction x).2)⟩
  have h₁ : ((ContinuousMap.id X).restrict A).comp r.retraction =
      ((ContinuousMap.id X).restrict B).comp retraction := by
    ext x
    simp [retraction]
  exact {
    retraction := retraction
    homotopy := {
      toHomotopy := r.homotopy.toHomotopy.cast rfl h₁
      prop' := by
        intro t x hx
        exact r.homotopy.eq_fst t (by simpa [h] using hx)
    }
  }

@[simp]
theorem congr_retraction_apply {A B : Set X} (h : A = B) (r : StrongDeformationRetract A) (x : X) :
    (((StrongDeformationRetract.congr h r).retraction x : B) : X) = (r.retraction x : X) := by
  rfl

@[simp]
theorem congr_homotopy_apply {A B : Set X} (h : A = B) (r : StrongDeformationRetract A) (t : I)
    (x : X) :
    (StrongDeformationRetract.congr h r).homotopy (t, x) = r.homotopy (t, x) := by
  rfl

end StrongDeformationRetract

end DifferentialGeometry.Topology.Homotopy
