import DifferentialGeometry.Geometry.Metric.TwoRayConeData

set_option autoImplicit false

namespace GC.MetricGeometry

open Set
open scoped NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X]

private theorem exists_isometry_of_surjective_dist_eq {A Z : Type*} [MetricSpace Z]
    (f : A → X) (g : A → Z) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a b, dist (f a) (f b) = dist (g a) (g b)) :
    ∃ e : X ≃ᵢ Z, ∀ a, e (f a) = g a := by
  classical
  let F (x : X) : Z := g (hf x).choose
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (g (hf x).choose) (g (hf y).choose) = dist x y
    rw [← h, (hf x).choose_spec, (hf y).choose_spec]
  have hFa (a : A) : F (f a) = g a := by
    apply dist_eq_zero.mp
    change dist (g (hf (f a)).choose) (g a) = 0
    rw [← h, (hf (f a)).choose_spec, dist_self]
  have hsur : Function.Surjective F := by
    intro y
    obtain ⟨a, rfl⟩ := hg y
    exact ⟨f a, hFa a⟩
  exact ⟨⟨Equiv.ofBijective F ⟨hF.injective, hsur⟩, hF⟩, hFa⟩

private theorem planar_same_ray_dist (u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖ = 1)
    (s t : ℝ≥0) : dist ((s : ℝ) • u) ((t : ℝ) • u) = dist s t := by
  rw [dist_eq_norm, ← sub_smul, norm_smul, hu, mul_one, Real.norm_eq_abs]
  rfl

namespace TwoRayConeData

variable {p : X} (C : TwoRayConeData p)

theorem exists_pair_union_isometry {γ η : ℝ≥0 → X} (hγ : γ ∈ C.rays) (hη : η ∈ C.rays) :
    ∃ u v : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      ∃ e : ↥(Set.range γ ∪ Set.range η) ≃ᵢ
          ↥(Set.range (fun t : ℝ≥0 => (t : ℝ) • u) ∪
            Set.range (fun t : ℝ≥0 => (t : ℝ) • v)),
        (∀ t, (e ⟨γ t, Or.inl ⟨t, rfl⟩⟩).val = (t : ℝ) • u) ∧
        (∀ t, (e ⟨η t, Or.inr ⟨t, rfl⟩⟩).val = (t : ℝ) • v) := by
  obtain ⟨u, v, hu, hv, hpair⟩ := C.pair_distance γ hγ η hη
  let f : (ℝ≥0 ⊕ ℝ≥0) → ↥(Set.range γ ∪ Set.range η) :=
    Sum.elim (fun t => ⟨γ t, Or.inl ⟨t, rfl⟩⟩) (fun t => ⟨η t, Or.inr ⟨t, rfl⟩⟩)
  let g : (ℝ≥0 ⊕ ℝ≥0) →
      ↥(Set.range (fun t : ℝ≥0 => (t : ℝ) • u) ∪
        Set.range (fun t : ℝ≥0 => (t : ℝ) • v)) :=
    Sum.elim (fun t => ⟨(t : ℝ) • u, Or.inl ⟨t, rfl⟩⟩)
      (fun t => ⟨(t : ℝ) • v, Or.inr ⟨t, rfl⟩⟩)
  have hf : Function.Surjective f := by
    intro x
    rcases x.property with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨Sum.inl t, Subtype.ext ht⟩
    · exact ⟨Sum.inr t, Subtype.ext ht⟩
  have hg : Function.Surjective g := by
    intro x
    rcases x.property with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨Sum.inl t, Subtype.ext ht⟩
    · exact ⟨Sum.inr t, Subtype.ext ht⟩
  have hdist : ∀ a b, dist (f a) (f b) = dist (g a) (g b) := by
    intro a b
    rcases a with s | s <;> rcases b with t | t
    · exact ((C.isometry γ hγ).dist_eq s t).trans (planar_same_ray_dist u hu s t).symm
    · exact hpair s t
    · exact (dist_comm _ _).trans ((hpair t s).trans (dist_comm _ _))
    · exact ((C.isometry η hη).dist_eq s t).trans (planar_same_ray_dist v hv s t).symm
  obtain ⟨e, he⟩ := exists_isometry_of_surjective_dist_eq f g hf hg hdist
  exact ⟨u, v, hu, hv, e, fun t => congrArg Subtype.val (he (Sum.inl t)),
    fun t => congrArg Subtype.val (he (Sum.inr t))⟩

noncomputable def ofPairUnionIsometries (p : X) (rays : Set (ℝ≥0 → X))
    (hiso : ∀ γ ∈ rays, Isometry γ) (hbase : ∀ γ ∈ rays, γ 0 = p)
    (hcover : ∀ x, ∃ γ ∈ rays, ∃ t, γ t = x)
    (hpair : ∀ γ ∈ rays, ∀ η ∈ rays,
      ∃ u v : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
        ∃ e : ↥(Set.range γ ∪ Set.range η) ≃ᵢ
            ↥(Set.range (fun t : ℝ≥0 => (t : ℝ) • u) ∪
              Set.range (fun t : ℝ≥0 => (t : ℝ) • v)),
          (∀ t, (e ⟨γ t, Or.inl ⟨t, rfl⟩⟩).val = (t : ℝ) • u) ∧
          (∀ t, (e ⟨η t, Or.inr ⟨t, rfl⟩⟩).val = (t : ℝ) • v)) : TwoRayConeData p where
  rays := rays
  isometry := hiso
  basepoint := hbase
  coverage := hcover
  pair_distance γ hγ η hη := by
    obtain ⟨u, v, hu, hv, e, heγ, heη⟩ := hpair γ hγ η hη
    refine ⟨u, v, hu, hv, fun s t => ?_⟩
    have hh := e.dist_eq ⟨γ s, Or.inl ⟨s, rfl⟩⟩ ⟨η t, Or.inr ⟨t, rfl⟩⟩
    change dist (e ⟨γ s, Or.inl ⟨s, rfl⟩⟩).val (e ⟨η t, Or.inr ⟨t, rfl⟩⟩).val =
      dist (γ s) (η t) at hh
    rw [heγ, heη] at hh
    exact hh.symm


end TwoRayConeData
end GC.MetricGeometry
