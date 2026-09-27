/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.BallComplement
import DifferentialGeometry.Topology.PiecewiseLinear.HandleDecompositionOfEdgeCollars
import DifferentialGeometry.Topology.PlanarJordan.Innermost
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem subset_inside_or_subset_outside {γ S : Set Schoenflies.Plane}
    (hγ : Schoenflies.IsJordanCurve γ) (hS : IsPreconnected S) (hSγ : Disjoint S γ) :
    S ⊆ Schoenflies.inside γ ∨ S ⊆ Schoenflies.outside γ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl (empty_subset _)
  obtain ⟨W, V, hWV, hSW⟩ :=
    (Schoenflies.jordan_curve_theorem hγ).exists_isRegionPair_subset hS hne hSγ
  rcases hWV with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl hSW
  · exact Or.inr hSW

theorem closure_inside_eq_union {γ : Set Schoenflies.Plane} (hγ : Schoenflies.IsJordanCurve γ) :
    closure (Schoenflies.inside γ) = Schoenflies.inside γ ∪ γ :=
  (Schoenflies.IsRegionOf.inside γ).closure_eq (Schoenflies.jordan_curve_theorem hγ)

theorem compl_closure_inside {γ : Set Schoenflies.Plane} (hγ : Schoenflies.IsJordanCurve γ) :
    (closure (Schoenflies.inside γ))ᶜ = Schoenflies.outside γ := by
  rw [closure_inside_eq_union hγ]
  ext z
  constructor
  · intro hz
    have hzγ : z ∈ γᶜ := fun h => hz (Or.inr h)
    rw [← Schoenflies.inside_union_outside] at hzγ
    exact hzγ.resolve_left fun h => hz (Or.inl h)
  · rintro hz (h | h)
    · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside h hz
    · exact Schoenflies.outside_subset_compl hz h

theorem closure_inside_subset_inside_of_subset_inside {γ γ' : Set Schoenflies.Plane}
    (hγ : Schoenflies.IsJordanCurve γ) (hγ' : Schoenflies.IsJordanCurve γ')
    (h : γ' ⊆ Schoenflies.inside γ) : closure (Schoenflies.inside γ') ⊆ Schoenflies.inside γ := by
  rw [closure_inside_eq_union hγ']
  exact union_subset (PlanarJordan.inside_subset_of_subset_closure_inside
    (Schoenflies.jordan_curve_theorem hγ) (Schoenflies.jordan_curve_theorem hγ')
    (h.trans subset_closure)) h

theorem disjoint_closure_inside_of_not_subset_inside {γ γ' : Set Schoenflies.Plane}
    (hγ : Schoenflies.IsJordanCurve γ) (hγ' : Schoenflies.IsJordanCurve γ')
    (hdisj : Disjoint γ γ') (h₁ : ¬ γ' ⊆ Schoenflies.inside γ)
    (h₂ : ¬ γ ⊆ Schoenflies.inside γ') :
    Disjoint (closure (Schoenflies.inside γ)) (closure (Schoenflies.inside γ')) := by
  have hout : γ ⊆ Schoenflies.outside γ' :=
    (subset_inside_or_subset_outside hγ' hγ.isConnected.isPreconnected hdisj).resolve_left h₂
  have hout' : γ' ⊆ Schoenflies.outside γ :=
    (subset_inside_or_subset_outside hγ hγ'.isConnected.isPreconnected
      hdisj.symm).resolve_left h₁
  have hsep := Schoenflies.jordan_curve_theorem hγ
  have hd : Disjoint (Schoenflies.inside γ) γ' :=
    Set.disjoint_left.mpr fun z hz hz' =>
      Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz (hout' hz')
  have hin : Schoenflies.inside γ ⊆ Schoenflies.outside γ' := by
    refine (subset_inside_or_subset_outside hγ' hsep.isConnected_inside.isPreconnected
      hd).resolve_left fun hsub => h₂ fun z hz => ?_
    have hzcl : z ∈ closure (Schoenflies.inside γ') :=
      closure_mono hsub (frontier_subset_closure (hsep.frontier_inside.symm.subset hz))
    rw [closure_inside_eq_union hγ'] at hzcl
    exact hzcl.resolve_right (Set.disjoint_left.mp hdisj hz)
  rw [← Set.subset_compl_iff_disjoint_right, compl_closure_inside hγ',
    closure_inside_eq_union hγ]
  exact union_subset hin hout

theorem isPreconnected_compl_union_iUnion_closure_inside (𝒞 : Finset (Set Schoenflies.Plane))
    (h𝒞 : ∀ γ ∈ 𝒞, Schoenflies.IsJordanCurve γ)
    (hdisj : ∀ γ ∈ 𝒞, ∀ γ' ∈ 𝒞, γ ≠ γ' → Disjoint γ γ') {F₀ : Set Schoenflies.Plane}
    (hF₀ : IsClosed F₀) (hF₀c : IsPreconnected F₀ᶜ)
    (hF₀𝒞 : ∀ γ ∈ 𝒞, Disjoint F₀ (closure (Schoenflies.inside γ))) :
    IsPreconnected (F₀ ∪ ⋃ γ ∈ 𝒞, closure (Schoenflies.inside γ))ᶜ := by
  classical
  let D : Set Schoenflies.Plane → Set Schoenflies.Plane := fun γ =>
    closure (Schoenflies.inside γ)
  let 𝒞m := 𝒞.filter fun γ => ∀ γ' ∈ 𝒞, ¬ γ ⊆ Schoenflies.inside γ'
  have hmax : ∀ γ ∈ 𝒞, ∃ γm ∈ 𝒞m, D γ ⊆ D γm := by
    intro γ hγ
    obtain ⟨γm, hm⟩ := (𝒞.filter fun γ' => D γ ⊆ D γ').exists_maximalFor D
      ⟨γ, Finset.mem_filter.mpr ⟨hγ, Subset.rfl⟩⟩
    obtain ⟨hγm, hγγm⟩ := Finset.mem_filter.mp hm.1
    refine ⟨γm, Finset.mem_filter.mpr ⟨hγm, fun γ' hγ' hsub => ?_⟩, hγγm⟩
    have hDm : D γm ⊆ Schoenflies.inside γ' :=
      closure_inside_subset_inside_of_subset_inside (h𝒞 γ' hγ') (h𝒞 γm hγm) hsub
    have hle : D γm ⊆ D γ' := hDm.trans subset_closure
    have hback : D γ' ⊆ D γm := hm.2 (Finset.mem_filter.mpr ⟨hγ', hγγm.trans hle⟩) hle
    obtain ⟨z, hz⟩ := (h𝒞 γ' hγ').isConnected.nonempty
    have hzD : z ∈ D γ' := by
      change z ∈ closure (Schoenflies.inside γ')
      rw [closure_inside_eq_union (h𝒞 γ' hγ')]
      exact Or.inr hz
    exact Schoenflies.inside_subset_compl (hDm (hback hzD)) hz
  have hunion : (⋃ γ ∈ 𝒞, D γ) = ⋃ γ ∈ 𝒞m, D γ := by
    apply Subset.antisymm
    · refine iUnion₂_subset fun γ hγ => ?_
      obtain ⟨γm, hγm, hsub⟩ := hmax γ hγ
      exact hsub.trans (subset_iUnion₂ (s := fun γ (_ : γ ∈ 𝒞m) => D γ) γm hγm)
    · exact iUnion₂_subset fun γ hγ =>
        subset_iUnion₂ (s := fun γ (_ : γ ∈ 𝒞) => D γ) γ (Finset.mem_filter.mp hγ).1
  let F : Option 𝒞m → Set Schoenflies.Plane := fun o =>
    match o with
    | none => F₀
    | some γ => D γ.1
  have hFcl : ∀ o, IsClosed (F o) := by
    rintro (_ | γ)
    · exact hF₀
    · exact isClosed_closure
  have hFd : Pairwise fun o o' => Disjoint (F o) (F o') := by
    rintro (_ | γ) (_ | γ') hne
    · exact (hne rfl).elim
    · exact hF₀𝒞 γ'.1 (Finset.mem_filter.mp γ'.2).1
    · exact (hF₀𝒞 γ.1 (Finset.mem_filter.mp γ.2).1).symm
    · have hne' : γ.1 ≠ γ'.1 := fun h => hne (congrArg some (Subtype.ext h))
      obtain ⟨hγ, hγmax⟩ := Finset.mem_filter.mp γ.2
      obtain ⟨hγ', hγ'max⟩ := Finset.mem_filter.mp γ'.2
      exact disjoint_closure_inside_of_not_subset_inside (h𝒞 _ hγ) (h𝒞 _ hγ')
        (hdisj _ hγ _ hγ' hne') (hγ'max _ hγ) (hγmax _ hγ')
  have hFc : ∀ o, IsPreconnected (F o)ᶜ := by
    rintro (_ | γ)
    · exact hF₀c
    · have hJ := h𝒞 _ (Finset.mem_filter.mp γ.2).1
      change IsPreconnected (closure (Schoenflies.inside γ.1))ᶜ
      rw [compl_closure_inside hJ]
      exact (Schoenflies.jordan_curve_theorem hJ).isConnected_outside.isPreconnected
  have hmain := isPreconnected_compl_iUnion_of_isPreconnected_compl hFcl hFd hFc
  have heq : (⋃ o, F o) = F₀ ∪ ⋃ γ ∈ 𝒞, D γ := by
    rw [iUnion_option, hunion]
    congr 1
    ext z
    simp only [mem_iUnion, Subtype.exists, exists_prop]
    exact ⟨fun ⟨a, b, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨a, b, h⟩⟩
  rw [heq] at hmain
  exact hmain

theorem closure_inside_subset_ball {γ : Set Schoenflies.Plane}
    (hγ : Schoenflies.IsJordanCurve γ) {r : ℝ} (hγr : γ ⊆ Metric.ball 0 r) :
    closure (Schoenflies.inside γ) ⊆ Metric.ball 0 r := by
  obtain ⟨r', hr', hγr'⟩ := exists_lt_subset_ball hγ.isClosed hγr
  have hrank : 1 < Module.rank ℝ Schoenflies.Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have hS : IsPreconnected (Metric.closedBall (0 : Schoenflies.Plane) r')ᶜ :=
    (Topology.isPathConnected_compl_closedBall hrank 0 r').isConnected.isPreconnected
  have hSγ : Disjoint (Metric.closedBall (0 : Schoenflies.Plane) r')ᶜ γ :=
    Set.disjoint_left.mpr fun z hz hzγ => hz (Metric.ball_subset_closedBall (hγr' hzγ))
  have hout : (Metric.closedBall (0 : Schoenflies.Plane) r')ᶜ ⊆ Schoenflies.outside γ := by
    refine (subset_inside_or_subset_outside hγ hS hSγ).resolve_left fun hin => ?_
    apply NormedSpace.unbounded_univ ℝ Schoenflies.Plane
    have hb := (Metric.isBounded_closedBall (x := (0 : Schoenflies.Plane)) (r := r')).union
      ((Schoenflies.jordan_curve_theorem hγ).isBounded_inside.subset hin)
    rwa [union_compl_self] at hb
  rw [closure_inside_eq_union hγ]
  refine union_subset (fun z hz => ?_) (hγr'.trans (Metric.ball_subset_ball hr'.le))
  by_contra hzb
  have hzc : z ∈ (Metric.closedBall (0 : Schoenflies.Plane) r')ᶜ := fun hz' =>
    hzb (Metric.closedBall_subset_ball hr' hz')
  exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz (hout hzc)

theorem exists_innermost_jordanCurve_of_sides (𝒞 : Finset (Set Schoenflies.Plane))
    (h𝒞 : ∀ γ ∈ 𝒞, Schoenflies.IsJordanCurve γ)
    (hdisj : ∀ γ ∈ 𝒞, ∀ γ' ∈ 𝒞, γ ≠ γ' → Disjoint γ γ') {C : Set Schoenflies.Plane}
    (hC : IsCompact C) (hCo : IsOpen (C \ ⋃ γ ∈ 𝒞, γ)) (h𝒞C : ∀ γ ∈ 𝒞, γ ⊆ C)
    {c : Schoenflies.Plane} (hc : c ∈ C) (hc𝒞 : ∀ γ ∈ 𝒞, c ∉ γ)
    (hside : ∀ γ ∈ 𝒞, ∀ q ∈ γ, ∃ V S₁ S₂ : Set Schoenflies.Plane, IsOpen V ∧ q ∈ V ∧
      V \ (⋃ γ' ∈ 𝒞, γ') ⊆ S₁ ∪ S₂ ∧ Disjoint S₁ γ ∧ Disjoint S₂ C ∧
        IsPreconnected S₁ ∧ IsPreconnected S₂ ∧ q ∈ closure S₂) :
    ∃ γ ∈ 𝒞, c ∈ Schoenflies.inside γ ∧
      ∀ q ∈ γ, ∃ V ∈ 𝓝 q, C ∩ V = (Schoenflies.inside γ ∪ γ) ∩ V := by
  classical
  have hcU : c ∉ ⋃ γ ∈ 𝒞, γ := by
    simp only [mem_iUnion, not_exists]
    exact fun γ hγ => hc𝒞 γ hγ
  have hkey : ∀ A : Set Schoenflies.Plane, IsPreconnected A → Disjoint A (⋃ γ ∈ 𝒞, γ) →
      c ∈ A → A ⊆ C := by
    intro A hA hAU hcA
    have hsub := hA.subset_left_of_subset_union hCo hC.isClosed.isOpen_compl
      (Set.disjoint_left.mpr fun z hz hz' => hz' hz.1)
      (fun z hz => by
        by_cases hzC : z ∈ C
        · exact Or.inl ⟨hzC, Set.disjoint_left.mp hAU hz⟩
        · exact Or.inr hzC)
      ⟨c, hcA, hc, hcU⟩
    exact hsub.trans sdiff_subset
  have hne : (𝒞.filter fun γ => c ∈ Schoenflies.inside γ).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hempty
    have hA := isPreconnected_compl_union_iUnion_closure_inside 𝒞 h𝒞 hdisj isClosed_empty
      (by rw [compl_empty]; exact isPreconnected_univ) (fun γ _ => Set.empty_disjoint _)
    rw [empty_union] at hA
    have hcA : c ∈ (⋃ γ ∈ 𝒞, closure (Schoenflies.inside γ))ᶜ := by
      simp only [mem_compl_iff, mem_iUnion, not_exists]
      intro γ hγ hcγ
      rw [closure_inside_eq_union (h𝒞 γ hγ)] at hcγ
      rcases hcγ with h | h
      · exact hempty hγ h
      · exact hc𝒞 γ hγ h
    have hAU : Disjoint (⋃ γ ∈ 𝒞, closure (Schoenflies.inside γ))ᶜ (⋃ γ ∈ 𝒞, γ) := by
      rw [Set.disjoint_compl_left_iff_subset]
      exact iUnion₂_mono fun γ hγ => by
        rw [closure_inside_eq_union (h𝒞 γ hγ)]
        exact subset_union_right
    have hsub := hkey _ hA hAU hcA
    have hcpt : IsCompact (C ∪ ⋃ γ ∈ 𝒞, closure (Schoenflies.inside γ)) :=
      hC.union (𝒞.isCompact_biUnion fun γ hγ =>
        (Schoenflies.jordan_curve_theorem (h𝒞 γ hγ)).isBounded_inside.isCompact_closure)
    obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem _).mp hcpt.ne_univ
    exact hz (Or.inl (hsub fun hz' => hz (Or.inr hz')))
  obtain ⟨γ₀, hmin⟩ := (𝒞.filter fun γ => c ∈ Schoenflies.inside γ).exists_minimalFor
    Schoenflies.inside hne
  obtain ⟨hγ₀, hcγ₀⟩ := Finset.mem_filter.mp hmin.1
  have hJ₀ := h𝒞 γ₀ hγ₀
  have hsep₀ := Schoenflies.jordan_curve_theorem hJ₀
  let 𝒞₀ := 𝒞.filter fun γ => γ ⊆ Schoenflies.inside γ₀
  have hD₀ : ∀ γ ∈ 𝒞₀, closure (Schoenflies.inside γ) ⊆ Schoenflies.inside γ₀ := fun γ hγ =>
    closure_inside_subset_inside_of_subset_inside hJ₀ (h𝒞 γ (Finset.mem_filter.mp hγ).1)
      (Finset.mem_filter.mp hγ).2
  have hcD : ∀ γ ∈ 𝒞₀, c ∉ closure (Schoenflies.inside γ) := by
    intro γ hγ hcγ
    obtain ⟨hγ𝒞, hγin⟩ := Finset.mem_filter.mp hγ
    rw [closure_inside_eq_union (h𝒞 γ hγ𝒞)] at hcγ
    rcases hcγ with hcin | hcon
    · have hle : Schoenflies.inside γ ⊆ Schoenflies.inside γ₀ :=
        subset_closure.trans (hD₀ γ hγ)
      have hge := hmin.2 (Finset.mem_filter.mpr ⟨hγ𝒞, hcin⟩) hle
      obtain ⟨z, hz⟩ := (h𝒞 γ hγ𝒞).isConnected.nonempty
      exact Schoenflies.inside_subset_compl (hge (hγin hz)) hz
    · exact hc𝒞 γ hγ𝒞 hcon
  have hA := isPreconnected_compl_union_iUnion_closure_inside 𝒞₀
    (fun γ hγ => h𝒞 γ (Finset.mem_filter.mp hγ).1)
    (fun γ hγ γ' hγ' => hdisj γ (Finset.mem_filter.mp hγ).1 γ' (Finset.mem_filter.mp hγ').1)
    hsep₀.isOpen_inside.isClosed_compl
    (by rw [compl_compl]; exact hsep₀.isConnected_inside.isPreconnected)
    (fun γ hγ => Set.disjoint_compl_left_iff_subset.mpr (hD₀ γ hγ))
  have hmemA : ∀ z, z ∈ ((Schoenflies.inside γ₀)ᶜ ∪
      ⋃ γ ∈ 𝒞₀, closure (Schoenflies.inside γ))ᶜ ↔
        z ∈ Schoenflies.inside γ₀ ∧ ∀ γ ∈ 𝒞₀, z ∉ closure (Schoenflies.inside γ) := by
    intro z
    simp only [mem_compl_iff, mem_union, mem_iUnion, not_or, not_not, not_exists]
  have hAC : ((Schoenflies.inside γ₀)ᶜ ∪ ⋃ γ ∈ 𝒞₀, closure (Schoenflies.inside γ))ᶜ ⊆ C := by
    refine hkey _ hA ?_ ((hmemA c).mpr ⟨hcγ₀, hcD⟩)
    refine Set.disjoint_left.mpr fun z hz hzU => ?_
    obtain ⟨hzin, hzD⟩ := (hmemA z).mp hz
    obtain ⟨γ, hγ, hzγ⟩ := mem_iUnion₂.mp hzU
    by_cases hγγ₀ : γ = γ₀
    · rw [hγγ₀] at hzγ
      exact Schoenflies.inside_subset_compl hzin hzγ
    · rcases subset_inside_or_subset_outside hJ₀ (h𝒞 γ hγ).isConnected.isPreconnected
        (hdisj γ hγ γ₀ hγ₀ hγγ₀) with hin | hout
      · refine hzD γ (Finset.mem_filter.mpr ⟨hγ, hin⟩) ?_
        rw [closure_inside_eq_union (h𝒞 γ hγ)]
        exact Or.inr hzγ
      · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hzin (hout hzγ)
  refine ⟨γ₀, hγ₀, hcγ₀, fun q hq => ?_⟩
  obtain ⟨V, S₁, S₂, hV, hqV, hcov, hS₁γ, hS₂C, hS₁, hS₂, hqS₂⟩ := hside γ₀ hγ₀ q hq
  let V' := (⋃ γ ∈ 𝒞₀, closure (Schoenflies.inside γ))ᶜ ∩ (⋃ γ ∈ 𝒞.erase γ₀, γ)ᶜ
  have hV'o : IsOpen V' :=
    (isClosed_biUnion_finset fun γ _ => isClosed_closure).isOpen_compl.inter
      (isClosed_biUnion_finset fun γ hγ =>
        (h𝒞 γ (Finset.mem_of_mem_erase hγ)).isClosed).isOpen_compl
  have hqV' : q ∈ V' := by
    refine ⟨fun hqD => ?_, fun hqE => ?_⟩
    · obtain ⟨γ, hγ, hqγ⟩ := mem_iUnion₂.mp hqD
      exact Schoenflies.inside_subset_compl (hD₀ γ hγ hqγ) hq
    · obtain ⟨γ, hγ, hqγ⟩ := mem_iUnion₂.mp hqE
      exact Set.disjoint_left.mp (hdisj γ (Finset.mem_of_mem_erase hγ) γ₀ hγ₀
        (Finset.ne_of_mem_erase hγ)) hqγ hq
  have hinC : Schoenflies.inside γ₀ ∩ V' ⊆ C := fun z hz =>
    hAC ((hmemA z).mpr ⟨hz.1, fun γ hγ hzγ => hz.2.1 (mem_iUnion₂.mpr ⟨γ, hγ, hzγ⟩)⟩)
  have hoff : ∀ z ∈ V ∩ V', z ∉ γ₀ → z ∈ S₁ ∪ S₂ := by
    intro z hz hzγ
    refine hcov ⟨hz.1, fun hzU => ?_⟩
    obtain ⟨γ, hγ, hzγ'⟩ := mem_iUnion₂.mp hzU
    by_cases hγγ₀ : γ = γ₀
    · rw [hγγ₀] at hzγ'
      exact hzγ hzγ'
    · exact hz.2.2 (mem_iUnion₂.mpr ⟨γ, Finset.mem_erase.mpr ⟨hγγ₀, hγ⟩, hzγ'⟩)
  have hS₂out : S₂ ⊆ Schoenflies.outside γ₀ := by
    refine (subset_inside_or_subset_outside hJ₀ hS₂
      (hS₂C.mono_right (h𝒞C γ₀ hγ₀))).resolve_left fun hin => ?_
    obtain ⟨z, hzV', hzS₂⟩ := mem_closure_iff_nhds.mp hqS₂ V' (hV'o.mem_nhds hqV')
    exact Set.disjoint_left.mp hS₂C hzS₂ (hinC ⟨hin hzS₂, hzV'⟩)
  have hS₁in : S₁ ⊆ Schoenflies.inside γ₀ := by
    refine (subset_inside_or_subset_outside hJ₀ hS₁ hS₁γ).resolve_right fun hout => ?_
    have hqcl : q ∈ closure (Schoenflies.inside γ₀) :=
      frontier_subset_closure (hsep₀.frontier_inside.symm.subset hq)
    obtain ⟨z, hzW, hzin⟩ := mem_closure_iff_nhds.mp hqcl (V ∩ V')
      (Filter.inter_mem (hV.mem_nhds hqV) (hV'o.mem_nhds hqV'))
    rcases hoff z hzW (Schoenflies.inside_subset_compl hzin) with hz | hz
    · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hzin (hout hz)
    · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hzin (hS₂out hz)
  refine ⟨V ∩ V', Filter.inter_mem (hV.mem_nhds hqV) (hV'o.mem_nhds hqV'), ?_⟩
  ext z
  constructor
  · rintro ⟨hzC, hzW⟩
    refine ⟨?_, hzW⟩
    by_cases hzγ : z ∈ γ₀
    · exact Or.inr hzγ
    · rcases hoff z hzW hzγ with hz | hz
      · exact Or.inl (hS₁in hz)
      · exact (Set.disjoint_left.mp hS₂C hz hzC).elim
  · rintro ⟨hz | hz, hzW⟩
    · exact ⟨hinC ⟨hz, hzW.2⟩, hzW⟩
    · exact ⟨h𝒞C γ₀ hγ₀ hz, hzW⟩

end DifferentialGeometry.Topology.PiecewiseLinear
