import DifferentialGeometry.Topology.Homotopy.RayComplement
import Mathlib.Topology.Clopen
import DifferentialGeometry.Topology.Homology.LiftedSphere
import DifferentialGeometry.Topology.Homology.SubspaceCarriers

noncomputable section

open Set ContinuousMap

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

abbrev puncturedPlane := ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0))

def planeNegativeDiagonalRayComplement : Set (liftedSphereSpace.{u} 0) :=
  {x | ¬ ∃ r : ℝ, r ≤ 0 ∧ ∀ i : Fin 2, x.down i = r}

def planePositiveDiagonalRayComplement : Set (liftedSphereSpace.{u} 0) :=
  {x | ¬ ∃ r : ℝ, 0 ≤ r ∧ ∀ i : Fin 2, x.down i = r}

def puncturedPlanePositiveRayComplement : Set puncturedPlane.{u} :=
  {x | x.val ∈ planePositiveDiagonalRayComplement}

def puncturedPlaneNegativeRayComplement : Set puncturedPlane.{u} :=
  {x | x.val ∈ planeNegativeDiagonalRayComplement}

private def planeDiagonalVector : liftedSphereSpace.{u} 0 :=
  ULift.up (WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ)))

private theorem planeDiagonalVector_ne_zero : planeDiagonalVector.{u} ≠ 0 := by
  intro h
  have hc := congrArg (fun x : liftedSphereSpace.{u} 0 => x.down 0) h
  norm_num [planeDiagonalVector] at hc

private theorem planeNegativeDiagonalRayComplement_eq :
    planeNegativeDiagonalRayComplement.{u} =
      (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ¬ ∃ c : ℝ, 0 ≤ c ∧ x = -c • planeDiagonalVector) := by
  ext x
  apply not_congr
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨-r, by linarith, ?_⟩
    apply ULift.ext
    ext i
    change x.down i = -(-r) * 1
    rw [hx]
    ring
  · rintro ⟨c, hc, rfl⟩
    exact ⟨-c, by linarith, fun i => by simp [planeDiagonalVector]⟩

private theorem planePositiveDiagonalRayComplement_eq :
    planePositiveDiagonalRayComplement.{u} =
      (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ¬ ∃ c : ℝ, 0 ≤ c ∧ x = -c • (-planeDiagonalVector)) := by
  ext x
  apply not_congr
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨r, hr, ?_⟩
    apply ULift.ext
    ext i
    change x.down i = (-r) * (-1)
    rw [hx]
    ring
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, fun i => by simp [planeDiagonalVector]⟩

private theorem planeNegativeDiagonalRayComplement_ne_zero
    (x : planeNegativeDiagonalRayComplement.{u}) : x.val ≠ 0 := by
  intro h
  exact x.property ⟨0, le_rfl, by rw [h]; exact fun _ => rfl⟩

private theorem planePositiveDiagonalRayComplement_ne_zero
    (x : planePositiveDiagonalRayComplement.{u}) : x.val ≠ 0 := by
  intro h
  exact x.property ⟨0, le_rfl, by rw [h]; exact fun _ => rfl⟩

private def planeNegativeRayPuncturedHomeomorph :
    puncturedPlaneNegativeRayComplement.{u} ≃ₜ planeNegativeDiagonalRayComplement.{u} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, planeNegativeDiagonalRayComplement_ne_zero x⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def planePositiveRayPuncturedHomeomorph :
    puncturedPlanePositiveRayComplement.{u} ≃ₜ planePositiveDiagonalRayComplement.{u} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, planePositiveDiagonalRayComplement_ne_zero x⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem puncturedPlaneNegativeRayComplement_contractibleSpace :
    ContractibleSpace puncturedPlaneNegativeRayComplement.{u} := by
  have : ContractibleSpace planeNegativeDiagonalRayComplement.{u} := by
    rw [planeNegativeDiagonalRayComplement_eq]
    exact contractibleSpace_compl_nonpositive_ray planeDiagonalVector planeDiagonalVector_ne_zero
  exact planeNegativeRayPuncturedHomeomorph.contractibleSpace

theorem puncturedPlanePositiveRayComplement_contractibleSpace :
    ContractibleSpace puncturedPlanePositiveRayComplement.{u} := by
  have : ContractibleSpace planePositiveDiagonalRayComplement.{u} := by
    rw [planePositiveDiagonalRayComplement_eq]
    exact contractibleSpace_compl_nonpositive_ray (-planeDiagonalVector) (neg_ne_zero.mpr planeDiagonalVector_ne_zero)
  exact planePositiveRayPuncturedHomeomorph.contractibleSpace


private theorem isClosed_plane_diagonal :
    IsClosed (Set.ofPred fun x : liftedSphereSpace.{u} 0 =>
      ∀ i : Fin 2, x.down i = x.down 0) := by
  have hc (i : Fin 2) : Continuous (fun x : liftedSphereSpace.{u} 0 => x.down i) := by fun_prop
  have heq : (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ∀ i : Fin 2,
      x.down i = x.down 0) = ⋂ i, {y | y.down i = y.down 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_eq (hc i) (hc 0)

theorem isOpen_planeNegativeDiagonalRayComplement :
    IsOpen planeNegativeDiagonalRayComplement.{u} := by
  have he : planeNegativeDiagonalRayComplement.{u} =
      ((Set.ofPred fun x : liftedSphereSpace.{u} 0 => x.down 0 ≤ 0) ∩
        (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ∀ i : Fin 2, x.down i = x.down 0))ᶜ := by
    ext x
    apply not_congr
    constructor
    · rintro ⟨r, hr, hx⟩
      exact ⟨by change x.down 0 ≤ 0; rw [hx]; exact hr, fun i => (hx i).trans (hx 0).symm⟩
    · rintro ⟨h, hx⟩
      exact ⟨x.down 0, h, hx⟩
  rw [he]
  exact ((isClosed_le (show Continuous (fun x : liftedSphereSpace.{u} 0 => x.down 0) by
    fun_prop) continuous_const).inter isClosed_plane_diagonal).isOpen_compl

theorem isOpen_planePositiveDiagonalRayComplement :
    IsOpen planePositiveDiagonalRayComplement.{u} := by
  have he : planePositiveDiagonalRayComplement.{u} =
      ((Set.ofPred fun x : liftedSphereSpace.{u} 0 => 0 ≤ x.down 0) ∩
        (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ∀ i : Fin 2, x.down i = x.down 0))ᶜ := by
    ext x
    apply not_congr
    constructor
    · rintro ⟨r, hr, hx⟩
      exact ⟨by change 0 ≤ x.down 0; rw [hx]; exact hr, fun i => (hx i).trans (hx 0).symm⟩
    · rintro ⟨h, hx⟩
      exact ⟨x.down 0, h, hx⟩
  rw [he]
  exact ((isClosed_le continuous_const (show Continuous (fun x : liftedSphereSpace.{u} 0 => x.down 0) by
    fun_prop)).inter isClosed_plane_diagonal).isOpen_compl

theorem isOpen_puncturedPlaneNegativeRayComplement : IsOpen puncturedPlaneNegativeRayComplement.{u} :=
  isOpen_planeNegativeDiagonalRayComplement.preimage continuous_subtype_val

theorem isOpen_puncturedPlanePositiveRayComplement : IsOpen puncturedPlanePositiveRayComplement.{u} :=
  isOpen_planePositiveDiagonalRayComplement.preimage continuous_subtype_val

theorem puncturedPlaneRayComplements_cover :
    puncturedPlanePositiveRayComplement.{u} ∪ puncturedPlaneNegativeRayComplement = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra h
  have hp : ¬ x ∈ puncturedPlanePositiveRayComplement := fun hx => h (Or.inl hx)
  have hn : ¬ x ∈ puncturedPlaneNegativeRayComplement := fun hx => h (Or.inr hx)
  obtain ⟨r, hr, hx⟩ := Classical.not_not.mp hp
  obtain ⟨s, hs, hy⟩ := Classical.not_not.mp hn
  have hrs : r = s := (hx 0).symm.trans (hy 0)
  have hr0 : r = 0 := by linarith
  apply x.property
  apply ULift.ext
  ext i
  exact (hx i).trans hr0


theorem puncturedPlaneRayOverlap_coordinate_ne
    (x : subspaceIntersection puncturedPlanePositiveRayComplement.{u}
      puncturedPlaneNegativeRayComplement) :
    x.val.val.val.down 0 ≠ x.val.val.val.down 1 := by
  intro h
  have he (i : Fin 2) : x.val.val.val.down i = x.val.val.val.down 0 := by
    fin_cases i
    · rfl
    · exact h.symm
  rcases le_total (0 : ℝ) (x.val.val.val.down 0) with hp | hn
  · exact x.property ⟨x.val.val.val.down 0, hp, he⟩
  · exact x.val.property ⟨x.val.val.val.down 0, hn, he⟩

private theorem continuous_decide_lt_of_ne {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hne : ∀ x, f x ≠ g x) :
    Continuous (fun x => decide (f x < g x)) := by
  rw [continuous_bool_rng true]
  have hset : (fun x => decide (f x < g x)) ⁻¹' {true} = {x | f x < g x} := by
    ext x
    simp
  rw [hset]
  constructor
  · have hlt : {x | f x < g x} = {x | f x ≤ g x} := by
      ext x
      exact lt_iff_le_and_ne.trans (and_iff_left (hne x))
    rw [hlt]
    exact isClosed_le hf hg
  · exact isOpen_lt hf hg

def puncturedPlaneRayOverlapSign :
    C(subspaceIntersection puncturedPlanePositiveRayComplement.{u}
      puncturedPlaneNegativeRayComplement, ULift.{u} Bool) where
  toFun x := ULift.up (decide (x.val.val.val.down 0 < x.val.val.val.down 1))
  continuous_toFun := continuous_uliftUp.comp (continuous_decide_lt_of_ne
    (by fun_prop) (by fun_prop) puncturedPlaneRayOverlap_coordinate_ne)

theorem puncturedPlaneRayOverlapSign_apply
    (x : subspaceIntersection puncturedPlanePositiveRayComplement.{u}
      puncturedPlaneNegativeRayComplement) :
    puncturedPlaneRayOverlapSign x =
      ULift.up (decide (x.val.val.val.down 0 < x.val.val.val.down 1)) := rfl

end DifferentialGeometry.Topology.SimplexDegree

