import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation
import DifferentialGeometry.Topology.VanKampen.TorsionFreeCover
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnectedComponents
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open Set
open scoped ContinuousMap

namespace Poincare.Topology.ThreeManifold.TwoSidedCollar

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  {e : B → X} (c : TwoSidedCollar e)

def domainNeighborhood (K : Set X) : Set X := interior K ∪ c.range

theorem isOpen_domainNeighborhood (K : Set X) : IsOpen (c.domainNeighborhood K) :=
  isOpen_interior.union c.isOpen_range

theorem subset_domainNeighborhood {K : Set X} (hK : IsClosed K)
    (hfront : frontier K ⊆ Set.range e) : K ⊆ c.domainNeighborhood K := by
  intro x hx
  by_cases hi : x ∈ interior K
  · exact Or.inl hi
  · obtain ⟨b, hb⟩ := hfront ⟨hK.closure_eq.symm ▸ hx, hi⟩
    exact Or.inr ⟨(b, 0), (c.zero_eq b).trans hb⟩

def domainInclusion {K : Set X} (hK : IsClosed K)
    (hfront : frontier K ⊆ Set.range e) : C(K, c.domainNeighborhood K) :=
  ⟨fun x ↦ ⟨x.val, c.subset_domainNeighborhood hK hfront x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

private def domainRetractionValue (K : Set X) (x : c.domainNeighborhood K) : X := by
  classical
  exact if hx : x.val ∈ c.range then
    let p := c.homeomorphRange.symm ⟨x.val, hx⟩
    c.toFun (p.1, min p.2 0)
  else x.val

private theorem domainRetractionValue_eq_of_mem {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (x : c.domainNeighborhood K) (hx : x.val ∈ K) :
    c.domainRetractionValue K x = x.val := by
  classical
  unfold domainRetractionValue
  split_ifs with hxc
  · let p := c.homeomorphRange.symm ⟨x.val, hxc⟩
    have hp : c.toFun p = x.val :=
      congrArg Subtype.val (c.homeomorphRange.apply_symm_apply ⟨x.val, hxc⟩)
    have ht : p.2 ≤ 0 := (hside p).mp (hp.symm ▸ hx)
    change c.toFun (p.1, min p.2 0) = x.val
    rw [min_eq_left ht]
    exact hp
  · rfl

private theorem domainRetractionValue_mem {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (x : c.domainNeighborhood K) : c.domainRetractionValue K x ∈ K := by
  classical
  unfold domainRetractionValue
  split_ifs with hx
  · exact (hside _).mpr (min_le_right _ _)
  · exact interior_subset (x.property.resolve_right hx)

private theorem continuous_domainRetractionValue {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) :
    Continuous (c.domainRetractionValue K) := by
  let A : Set (c.domainNeighborhood K) := Subtype.val ⁻¹' interior K
  let C : Set (c.domainNeighborhood K) := Subtype.val ⁻¹' c.range
  have hA : IsOpen A := isOpen_interior.preimage continuous_subtype_val
  have hC : IsOpen C := c.isOpen_range.preimage continuous_subtype_val
  have hcover : A ∪ C = univ := eq_univ_of_forall fun x ↦ x.property
  rw [← continuousOn_univ, ← hcover, continuousOn_union_iff_of_isOpen hA hC]
  constructor
  · exact continuous_subtype_val.continuousOn.congr
      (fun x hx ↦ c.domainRetractionValue_eq_of_mem hside x (interior_subset hx))
  · rw [continuousOn_iff_continuous_domRestrict]
    let j : C → c.range := fun x ↦ ⟨x.val.val, x.property⟩
    have hj : Continuous j :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hp := c.homeomorphRange.symm.continuous.comp hj
    have hg : Continuous (fun x : C ↦ c.toFun
        ((c.homeomorphRange.symm (j x)).1, min (c.homeomorphRange.symm (j x)).2 0)) :=
      c.isOpenEmbedding_toFun.continuous.comp
        ((continuous_fst.comp hp).prodMk ((continuous_snd.comp hp).min continuous_const))
    exact hg.congr (fun x ↦ by
      classical
      change c.toFun ((c.homeomorphRange.symm (j x)).1,
        min (c.homeomorphRange.symm (j x)).2 0) = c.domainRetractionValue K x.val
      unfold domainRetractionValue
      rw [dif_pos (show x.val.val ∈ c.range from x.property)])

def domainRetraction {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) :
    C(c.domainNeighborhood K, K) :=
  ⟨fun x ↦ ⟨c.domainRetractionValue K x, c.domainRetractionValue_mem hside x⟩,
    (c.continuous_domainRetractionValue hside).subtype_mk _⟩

theorem domainRetraction_leftInverse {K : Set X} (hK : IsClosed K)
    (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) :
    Function.LeftInverse (c.domainRetraction hside) (c.domainInclusion hK hfront) := by
  intro x
  exact Subtype.ext (c.domainRetractionValue_eq_of_mem hside _ x.property)

theorem pathConnectedSpace_domainNeighborhood {K : Set X} [PathConnectedSpace K]
    (hK : IsClosed K) (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) :
    PathConnectedSpace (c.domainNeighborhood K) := by
  let i := c.domainInclusion hK hfront
  have hpoint (x : c.domainNeighborhood K) : ∃ k : K, Joined x (i k) := by
    by_cases hx : x.val ∈ K
    · exact ⟨⟨x.val, hx⟩, Joined.refl x⟩
    · have hxc : x.val ∈ c.range := x.property.resolve_left (fun hi ↦ hx (interior_subset hi))
      let p := c.homeomorphRange.symm ⟨x.val, hxc⟩
      have hp : c.toFun p = x.val :=
        congrArg Subtype.val (c.homeomorphRange.apply_symm_apply ⟨x.val, hxc⟩)
      let k : K := ⟨c.toFun (p.1, 0), (hside (p.1, 0)).mpr le_rfl⟩
      refine ⟨k, ⟨{
        toFun := fun t ↦ ⟨c.toFun (p.1, (1 - t.val) * p.2),
          Or.inr ⟨(p.1, (1 - t.val) * p.2), rfl⟩⟩
        continuous_toFun :=
          (c.isOpenEmbedding_toFun.continuous.comp
            (continuous_const.prodMk
              ((continuous_const.sub continuous_subtype_val).mul continuous_const))).subtype_mk _
        source' := ?_
        target' := ?_ }⟩⟩
      · apply Subtype.ext
        simpa using hp
      · apply Subtype.ext
        simp [i, k, domainInclusion]
  refine { nonempty := Nonempty.map i inferInstance, joined := ?_ }
  intro x y
  obtain ⟨kx, hx⟩ := hpoint x
  obtain ⟨ky, hy⟩ := hpoint y
  exact Joined.trans hx (Joined.trans
    ⟨(PathConnectedSpace.somePath kx ky).map i.continuous⟩ hy.symm)

theorem domainNeighborhood_inter_compl {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) :
    c.domainNeighborhood K ∩ Kᶜ = c.toFun '' ((univ : Set B) ×ˢ Ioi 0) := by
  ext x
  constructor
  · rintro ⟨hxA, hxK⟩
    have hxC : x ∈ c.range := hxA.resolve_left (fun hi ↦ hxK (interior_subset hi))
    obtain ⟨p, rfl⟩ := hxC
    exact ⟨p, ⟨mem_univ _, lt_of_not_ge (fun hp ↦ hxK ((hside p).mpr hp))⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Or.inr ⟨p, rfl⟩, fun h ↦ (not_le_of_gt hp.2) ((hside p).mp h)⟩

private theorem subsingleton_overlap_paths {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (hB : ∀ x y : B, Subsingleton (Path.Homotopic.Quotient x y))
    (x y : ↑(c.domainNeighborhood K ∩ Kᶜ)) :
    Subsingleton (Path.Homotopic.Quotient x y) := by
  let E₁ : ↑(c.domainNeighborhood K ∩ Kᶜ) ≃ₜ B × Ioi (0 : ℝ) :=
    (Homeomorph.setCongr (c.domainNeighborhood_inter_compl hside)).trans
      ((c.isOpenEmbedding_toFun.toIsEmbedding.homeomorphImage
        ((univ : Set B) ×ˢ Ioi (0 : ℝ))).symm.trans
        ((Homeomorph.Set.prod univ (Ioi (0 : ℝ))).trans
          ((Homeomorph.Set.univ B).prodCongr (Homeomorph.refl _))))
  let _ : ContractibleSpace (Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
  let E₂ : B × Ioi (0 : ℝ) ≃ₕ B :=
    ((ContinuousMap.HomotopyEquiv.refl B).prodCongr
      (ContractibleSpace.hequiv_unit (Ioi (0 : ℝ))).some).trans
        (Homeomorph.prodUnique B Unit).toHomotopyEquiv
  exact Poincare.Topology.subsingleton_pathHomotopicQuotient_of_homotopyEquiv
    (E₁.toHomotopyEquiv.trans E₂) hB x y

theorem injective_fundamentalGroup_map_domain {K : Set X} [PathConnectedSpace K]
    (hK : IsClosed K) (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (hB : ∀ x y : B, Subsingleton (Path.Homotopic.Quotient x y)) (x₀ : K) :
    Function.Injective (FundamentalGroup.map (VanKampen.subsetToAmbient K) x₀) := by
  let _ := c.pathConnectedSpace_domainNeighborhood hK hfront hside
  let i := c.domainInclusion hK hfront
  have hi := Poincare.Topology.injective_fundamentalGroup_map_of_leftInverse
    i (c.domainRetraction hside) (c.domainRetraction_leftInverse hK hfront hside) x₀
  have hcover : c.domainNeighborhood K ∪ Kᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl (c.subset_domainNeighborhood hK hfront hx)
    · exact Or.inr hx
  have hA := VanKampen.injective_fundamentalGroup_map_of_open_cover_of_overlap_components
    (c.domainNeighborhood K) Kᶜ (c.isOpen_domainNeighborhood K) hK.isOpen_compl hcover
    (c.subsingleton_overlap_paths hside hB) (i x₀)
  have hcomp := hA.comp hi
  intro p q hpq
  apply hcomp
  change (Path.Homotopic.Quotient.map p i).map
      (VanKampen.subsetToAmbient (c.domainNeighborhood K)) =
    (Path.Homotopic.Quotient.map q i).map
      (VanKampen.subsetToAmbient (c.domainNeighborhood K))
  rw [← Path.Homotopic.Quotient.map_comp, ← Path.Homotopic.Quotient.map_comp]
  exact hpq

end Poincare.Topology.ThreeManifold.TwoSidedCollar
