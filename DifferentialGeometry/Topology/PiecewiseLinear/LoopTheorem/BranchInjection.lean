/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchDescent
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDeletion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem subset_or_disjoint_of_isPreconnected_of_three_closed {X : Type*} [TopologicalSpace X]
    {S U₁ U₂ U₃ : Set X} (h₁ : IsClosed U₁) (h₂ : IsClosed U₂) (h₃ : IsClosed U₃)
    (hS : IsPreconnected S) (hcover : S ⊆ U₁ ∪ U₂ ∪ U₃)
    (h₁₂ : Disjoint S (U₁ ∩ U₂)) (h₂₃ : Disjoint S (U₂ ∩ U₃)) :
    Disjoint S U₂ ∨ S ⊆ U₂ := by
  by_cases hmid : (S ∩ U₂).Nonempty
  · refine Or.inr fun x hxS => ?_
    by_contra hxU₂
    have houter : (S ∩ (U₁ ∪ U₃)).Nonempty := by
      refine ⟨x, hxS, ?_⟩
      rcases hcover hxS with h | h
      · rcases h with h | h
        · exact Or.inl h
        · exact absurd h hxU₂
      · exact Or.inr h
    have hcover' : S ⊆ U₂ ∪ (U₁ ∪ U₃) := by
      intro z hz
      rcases hcover hz with h | h
      · rcases h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
      · exact Or.inr (Or.inr h)
    obtain ⟨z, hzS, hz₂, hzouter⟩ :=
      isPreconnected_closed_iff.mp hS _ _ h₂ (h₁.union h₃) hcover' hmid houter
    rcases hzouter with h | h
    · exact Set.disjoint_left.mp h₁₂ hzS ⟨h, hz₂⟩
    · exact Set.disjoint_left.mp h₂₃ hzS ⟨hz₂, h⟩
  · exact Or.inl (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmid))

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B : Set M}

theorem branchCarrier_subset_image_branchPreimage (hD : NormalSingularCellData D BdM B)
    (b : hD.singularSet.Branch) :
    hD.singularSet.branchCarrier b ⊆ D '' hD.branchPreimage b := by
  intro y hy
  obtain ⟨x, hx, -, -, -, hxy, -⟩ :=
    hD.singularSet.branchCarrier_subset_doublePointSet b hy
  refine ⟨x, ⟨hx, ?_⟩, hxy⟩
  change D x ∈ hD.singularSet.branchCarrier b
  rw [hxy]
  exact hy

theorem branchCarrier_subset_doublePointSet_of_branchPreimage_subset
    (hD : NormalSingularCellData D BdM B) (b : hD.singularSet.Branch)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : hD.branchPreimage b ⊆ P) :
    hD.singularSet.branchCarrier b ⊆ doublePointSet D P := by
  intro y hy
  obtain ⟨x, hx, z, hz, hxz, hxy, hzy⟩ :=
    hD.singularSet.branchCarrier_subset_doublePointSet b hy
  refine ⟨x, hP ⟨hx, ?_⟩, z, hP ⟨hz, ?_⟩, hxz, hxy, hzy⟩
  · change D x ∈ hD.singularSet.branchCarrier b
    rw [hxy]
    exact hy
  · change D z ∈ hD.singularSet.branchCarrier b
    rw [hzy]
    exact hy

theorem disjoint_branchCarrier_doublePointSet_of_subset_image
    (hD : NormalSingularCellData D BdM B) (b : hD.singularSet.Branch)
    {S P : Set (EuclideanSpace ℝ (Fin 2))} (hSD : S ⊆ D.domain) (hPD : P ⊆ D.domain)
    (hcover : hD.singularSet.branchCarrier b ⊆ D '' S) (hSP : Disjoint S P) :
    Disjoint (hD.singularSet.branchCarrier b) (doublePointSet D P) := by
  refine Set.disjoint_left.mpr fun y hy hdouble => ?_
  obtain ⟨w, hwS, hwy⟩ := hcover hy
  obtain ⟨u, hu, v, hv, huv, huy, hvy⟩ := hdouble
  have hfiber : ({u, v} : Set (EuclideanSpace ℝ (Fin 2))) = D.domain ∩ D ⁻¹' {y} := by
    refine ((Set.finite_singleton v).insert u).eq_of_subset_of_encard_le ?_ ?_
    · rintro t (rfl | rfl)
      · exact ⟨hPD hu, huy⟩
      · exact ⟨hPD hv, hvy⟩
    · rw [Set.encard_pair huv]
      exact hD.fiber_le_two y
  have hw : w ∈ ({u, v} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hfiber]
    exact ⟨hSD hwS, hwy⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · exact Set.disjoint_left.mp hSP hwS hu
  · exact Set.disjoint_left.mp hSP hwS hv

end NormalSingularCellData

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D D' : SingularTwoCell M} {BdM BdM' : Set M}

theorem exists_branchCarrier_subset_of_doublePointSet_subset [T2Space M]
    (T : NormalSingularSetTriangulation D BdM) (S : NormalSingularSetTriangulation D' BdM')
    (hsub : doublePointSet D' D'.domain ⊆ doublePointSet D D.domain) (b : S.Branch) :
    ∃ a : T.Branch, S.branchCarrier b ⊆ T.branchCarrier a := by
  let _ : Finite T.Branch := T.finite_branch
  refine subset_of_isPreconnected_of_iUnion_isClosed (fun a => T.isClosed_branchCarrier a)
    T.pairwise_disjoint_branchCarrier (S.branchCarrier_isConnected b).isPreconnected
    (S.branchCarrier_isConnected b).nonempty ?_
  rw [T.iUnion_branchCarrier]
  exact (S.branchCarrier_subset_doublePointSet b).trans hsub

noncomputable def branchOrigin [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (S : NormalSingularSetTriangulation D' BdM')
    (hsub : doublePointSet D' D'.domain ⊆ doublePointSet D D.domain) (b : S.Branch) :
    T.Branch :=
  (T.exists_branchCarrier_subset_of_doublePointSet_subset S hsub b).choose

theorem branchCarrier_subset_branchOrigin [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (S : NormalSingularSetTriangulation D' BdM')
    (hsub : doublePointSet D' D'.domain ⊆ doublePointSet D D.domain) (b : S.Branch) :
    S.branchCarrier b ⊆ T.branchCarrier (T.branchOrigin S hsub b) :=
  (T.exists_branchCarrier_subset_of_doublePointSet_subset S hsub b).choose_spec

theorem branchOrigin_ne [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (S : NormalSingularSetTriangulation D' BdM')
    (hsub : doublePointSet D' D'.domain ⊆ doublePointSet D D.domain) {c : T.Branch}
    (hc : Disjoint (doublePointSet D' D'.domain) (T.branchCarrier c)) (b : S.Branch) :
    T.branchOrigin S hsub b ≠ c := by
  intro hbc
  obtain ⟨y, hy⟩ := (S.branchCarrier_isConnected b).nonempty
  refine Set.disjoint_left.mp hc (S.branchCarrier_subset_doublePointSet b hy) ?_
  rw [← hbc]
  exact T.branchCarrier_subset_branchOrigin S hsub b hy

theorem injective_branchOrigin [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (S : NormalSingularSetTriangulation D' BdM')
    (hsub : doublePointSet D' D'.domain ⊆ doublePointSet D D.domain)
    (hconn : ∀ a : T.Branch,
      IsPreconnected (T.branchCarrier a ∩ doublePointSet D' D'.domain)) :
    Function.Injective (T.branchOrigin S hsub) := by
  let _ : Finite S.Branch := S.finite_branch
  intro b₁ b₂ hb
  have hsub₁ : S.branchCarrier b₁ ⊆
      T.branchCarrier (T.branchOrigin S hsub b₁) ∩ doublePointSet D' D'.domain :=
    subset_inter (T.branchCarrier_subset_branchOrigin S hsub b₁)
      (S.branchCarrier_subset_doublePointSet b₁)
  have hsub₂ : S.branchCarrier b₂ ⊆
      T.branchCarrier (T.branchOrigin S hsub b₁) ∩ doublePointSet D' D'.domain := by
    refine subset_inter ?_ (S.branchCarrier_subset_doublePointSet b₂)
    rw [hb]
    exact T.branchCarrier_subset_branchOrigin S hsub b₂
  obtain ⟨y₁, hy₁⟩ := (S.branchCarrier_isConnected b₁).nonempty
  obtain ⟨b, hb'⟩ := subset_of_isPreconnected_of_iUnion_isClosed
    (fun b => S.isClosed_branchCarrier b) S.pairwise_disjoint_branchCarrier
    (hconn (T.branchOrigin S hsub b₁)) ⟨y₁, hsub₁ hy₁⟩ (by
      rw [S.iUnion_branchCarrier]
      exact inter_subset_right)
  have heq : ∀ b' : S.Branch, S.branchCarrier b' ⊆
      T.branchCarrier (T.branchOrigin S hsub b₁) ∩ doublePointSet D' D'.domain → b' = b := by
    intro b' hb''
    by_contra hne
    obtain ⟨y, hy⟩ := (S.branchCarrier_isConnected b').nonempty
    exact Set.disjoint_left.mp (S.pairwise_disjoint_branchCarrier hne) hy (hb' (hb'' hy))
  rw [heq b₁ hsub₁, heq b₂ hsub₂]

theorem injective_branchOrigin_of_subset_or_disjoint [T2Space M]
    (T : NormalSingularSetTriangulation D BdM) (S : NormalSingularSetTriangulation D' BdM')
    (hsub : doublePointSet D' D'.domain ⊆ doublePointSet D D.domain)
    (hwhole : ∀ a : T.Branch, T.branchCarrier a ⊆ doublePointSet D' D'.domain ∨
      Disjoint (T.branchCarrier a) (doublePointSet D' D'.domain)) :
    Function.Injective (T.branchOrigin S hsub) := by
  refine T.injective_branchOrigin S hsub fun a => ?_
  rcases hwhole a with h | h
  · rw [Set.inter_eq_self_of_subset_left h]
    exact (T.branchCarrier_isConnected a).isPreconnected
  · rw [Set.disjoint_iff_inter_eq_empty.mp h]
    exact isPreconnected_empty

end NormalSingularSetTriangulation

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B : Set M}

namespace DescendingSurgery

def ofBranchInjection (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hG : NormalSingularCellData G BdM B)
    (origin : hG.singularSet.Branch → hD.singularSet.Branch)
    (hinj : Function.Injective origin) (hmiss : ∀ b, origin b ≠ c) :
    hD.DescendingSurgery where
  cell := G
  normal := hG
  complexity_lt :=
    hD.singularSet.complexity_lt_of_injective_origin hG.singularSet c origin hinj hmiss

theorem ofBranchInjection_cell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hG : NormalSingularCellData G BdM B)
    (origin : hG.singularSet.Branch → hD.singularSet.Branch)
    (hinj : Function.Injective origin) (hmiss : ∀ b, origin b ≠ c) :
    (ofBranchInjection hD hG origin hinj hmiss).cell = G :=
  rfl

theorem ofBranchInjection_normal (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hG : NormalSingularCellData G BdM B)
    (origin : hG.singularSet.Branch → hD.singularSet.Branch)
    (hinj : Function.Injective origin) (hmiss : ∀ b, origin b ≠ c) :
    (ofBranchInjection hD hG origin hinj hmiss).normal = hG :=
  rfl

end DescendingSurgery

theorem branchCarrier_subset_or_disjoint_doublePointSet [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {A C P U₁ U₂ U₃ : Set (EuclideanSpace ℝ (Fin 2))}
    (h₁ : IsClosed U₁) (h₂ : IsClosed U₂) (h₃ : IsClosed U₃)
    (hpre : hD.branchPreimage c = A ∪ C)
    (hunion : U₁ ∪ U₂ ∪ U₃ = D.domain) (h₁₂ : U₁ ∩ U₂ = A) (h₂₃ : U₂ ∩ U₃ = C)
    (hPD : P ⊆ D.domain) (hout : D.domain \ U₂ ⊆ P) (hin : Disjoint P (U₂ \ A))
    {b : hD.singularSet.Branch} (hb : b ≠ c) :
    hD.singularSet.branchCarrier b ⊆ doublePointSet D P ∨
      Disjoint (hD.singularSet.branchCarrier b) (doublePointSet D P) := by
  have hdisjpre : Disjoint (hD.branchPreimage b) (hD.branchPreimage c) :=
    hD.pairwise_disjoint_branchPreimage hb
  have hpreD : hD.branchPreimage b ⊆ D.domain := fun _ hx => hx.1
  have hpiece : ∀ V : Set (EuclideanSpace ℝ (Fin 2)), V ⊆ hD.branchPreimage b →
      IsPreconnected V → V ⊆ P ∨ Disjoint V P := by
    intro V hV hVconn
    have hVD : V ⊆ D.domain := hV.trans hpreD
    have hVA : Disjoint V A := by
      refine Set.disjoint_left.mpr fun x hx hxA => ?_
      have hxc : x ∈ hD.branchPreimage c := by
        rw [hpre]
        exact Or.inl hxA
      exact Set.disjoint_left.mp hdisjpre (hV hx) hxc
    have hVC : Disjoint V C := by
      refine Set.disjoint_left.mpr fun x hx hxC => ?_
      have hxc : x ∈ hD.branchPreimage c := by
        rw [hpre]
        exact Or.inr hxC
      exact Set.disjoint_left.mp hdisjpre (hV hx) hxc
    rcases subset_or_disjoint_of_isPreconnected_of_three_closed h₁ h₂ h₃ hVconn
      (by rw [hunion]; exact hVD) (by rw [h₁₂]; exact hVA) (by rw [h₂₃]; exact hVC) with h | h
    · exact Or.inl fun x hx => hout ⟨hVD hx, Set.disjoint_left.mp h hx⟩
    · refine Or.inr (Set.disjoint_left.mpr fun x hx hxP => ?_)
      exact Set.disjoint_left.mp hin hxP ⟨h hx, Set.disjoint_left.mp hVA hx⟩
  rcases hD.branchProjection_connected_or_two_components b with hconn | hcomp
  · have hpreconn : IsPreconnected (hD.branchPreimage b) :=
      (isConnected_iff_connectedSpace.mpr hconn).isPreconnected
    rcases hpiece (hD.branchPreimage b) Subset.rfl hpreconn with h | h
    · exact Or.inl (hD.branchCarrier_subset_doublePointSet_of_branchPreimage_subset b h)
    · exact Or.inr (hD.disjoint_branchCarrier_doublePointSet_of_subset_image b hpreD hPD
        (hD.branchCarrier_subset_image_branchPreimage b) h)
  · obtain ⟨x, y, -, hunivcc, ⟨e₁, he₁⟩, e₂, he₂⟩ := hcomp
    have hcomponent : ∀ (z : hD.branchPreimage b)
        (e : connectedComponent z ≃ₜ (hD.singularSet.branchComplex b).space),
        (∀ w : connectedComponent z, e w = hD.branchProjection b w) →
        hD.singularSet.branchCarrier b ⊆ D '' (Subtype.val '' connectedComponent z) := by
      intro z e he w hw
      obtain ⟨t, ht, htw⟩ := (hD.singularSet.branchPieceIn b).bijOn.surjOn hw
      obtain ⟨v, hv⟩ : ∃ v : connectedComponent z, e v = ⟨t, ht⟩ :=
        ⟨e.symm ⟨t, ht⟩, e.apply_symm_apply _⟩
      have hproj : hD.branchProjection b (v : hD.branchPreimage b) = ⟨t, ht⟩ :=
        (he v).symm.trans hv
      have hcoord : hD.branchCoordinate b
          ((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2)) = t :=
        congrArg Subtype.val hproj
      have hmem : ((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2)) ∈
          hD.branchPreimage b := (v : hD.branchPreimage b).2
      refine ⟨((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2)),
        ⟨(v : hD.branchPreimage b), v.2, rfl⟩, ?_⟩
      calc D ((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2))
          = (hD.singularSet.branchPieceIn b).map
              (hD.branchCoordinate b
                ((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2))) :=
            (hD.branchPieceIn_map_branchCoordinate b hmem).symm
        _ = (hD.singularSet.branchPieceIn b).map t := by rw [hcoord]
        _ = w := htw
    have hsubcc : ∀ z : hD.branchPreimage b,
        Subtype.val '' connectedComponent z ⊆ hD.branchPreimage b := by
      rintro z - ⟨w, -, rfl⟩
      exact w.2
    have hconncc : ∀ z : hD.branchPreimage b,
        IsPreconnected (Subtype.val '' connectedComponent z) := fun z =>
      isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
    have hunioncc : Subtype.val '' connectedComponent x ∪ Subtype.val '' connectedComponent y =
        hD.branchPreimage b := by
      rw [← Set.image_union, hunivcc]
      simp
    rcases hpiece _ (hsubcc x) (hconncc x) with hx' | hx'
    · rcases hpiece _ (hsubcc y) (hconncc y) with hy' | hy'
      · refine Or.inl (hD.branchCarrier_subset_doublePointSet_of_branchPreimage_subset b ?_)
        rw [← hunioncc]
        exact Set.union_subset hx' hy'
      · exact Or.inr (hD.disjoint_branchCarrier_doublePointSet_of_subset_image b
          ((hsubcc y).trans hpreD) hPD (hcomponent y e₂ he₂) hy')
    · exact Or.inr (hD.disjoint_branchCarrier_doublePointSet_of_subset_image b
        ((hsubcc x).trans hpreD) hPD (hcomponent x e₁ he₁) hx')

theorem exists_middleCell_branchCarrier_subset_or_disjoint_of_boundaryBranch [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ (A : Set (EuclideanSpace ℝ (Fin 2))) (D₂ : SingularTwoCell M),
      A ⊆ hD.branchPreimage c ∧
      ∀ b : hD.singularSet.Branch, b ≠ c →
        hD.singularSet.branchCarrier b ⊆
            doublePointSet D (D.domain \ (D₂.domain \ A)) ∨
          Disjoint (hD.singularSet.branchCarrier b)
            (doublePointSet D (D.domain \ (D₂.domain \ A))) := by
  obtain ⟨A, C, -, -, -, hpre, -, -,
    -, -, -, -, -, -, -,
    D₁, D₂, D₃, hunion, h₁₂, h₂₃,
    -, -, -, -, -, -, -, -, -, -, -, -⟩ := hD.exists_three_cells_of_boundaryBranch hc
  refine ⟨A, D₂, ?_, fun b hb => ?_⟩
  · rw [hpre]
    exact Set.subset_union_left
  · exact hD.branchCarrier_subset_or_disjoint_doublePointSet
      D₁.isPLBall_domain.isPolyhedron.isCompact.isClosed
      D₂.isPLBall_domain.isPolyhedron.isCompact.isClosed
      D₃.isPLBall_domain.isPolyhedron.isCompact.isClosed
      hpre hunion h₁₂ h₂₃ Set.sdiff_subset
      (Set.sdiff_subset_sdiff_right Set.sdiff_subset) Set.disjoint_sdiff_left hb

namespace DescendingSurgery

noncomputable def ofBoundarySurgery [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hG : NormalSingularCellData G BdM B)
    {A C U₁ U₂ U₃ : Set (EuclideanSpace ℝ (Fin 2))}
    {pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (h₁ : IsClosed U₁) (h₂ : IsClosed U₂) (h₃ : IsClosed U₃)
    (hpre : hD.branchPreimage c = A ∪ C)
    (hunion : U₁ ∪ U₂ ∪ U₃ = D.domain) (h₁₂ : U₁ ∩ U₂ = A) (h₂₃ : U₂ ∩ U₃ = C)
    (hmaps : MapsTo pullback G.domain D.domain) (hinj : InjOn pullback G.domain)
    (heq : EqOn (D ∘ pullback) G G.domain)
    (hout : D.domain \ U₂ ⊆ pullback '' G.domain)
    (hin : Disjoint (pullback '' G.domain) (U₂ \ A))
    (hmiss : Disjoint (doublePointSet G G.domain) (hD.singularSet.branchCarrier c)) :
    hD.DescendingSurgery := by
  have hPD : pullback '' G.domain ⊆ D.domain := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps hx
  have hdps : doublePointSet G G.domain = doublePointSet D (pullback '' G.domain) :=
    doublePointSet_eq_image_of_pullback hinj heq
  have hsub : doublePointSet G G.domain ⊆ doublePointSet D D.domain := by
    rw [hdps]
    rintro z ⟨u, hu, v, hv, huv, huz, hvz⟩
    exact ⟨u, hPD hu, v, hPD hv, huv, huz, hvz⟩
  have hwhole : ∀ a : hD.singularSet.Branch,
      hD.singularSet.branchCarrier a ⊆ doublePointSet G G.domain ∨
        Disjoint (hD.singularSet.branchCarrier a) (doublePointSet G G.domain) := by
    intro a
    by_cases hac : a = c
    · refine Or.inr ?_
      rw [hac]
      exact hmiss.symm
    · rw [hdps]
      exact hD.branchCarrier_subset_or_disjoint_doublePointSet h₁ h₂ h₃ hpre hunion h₁₂ h₂₃
        hPD hout hin hac
  exact ofBranchInjection hD hG (hD.singularSet.branchOrigin hG.singularSet hsub)
    (hD.singularSet.injective_branchOrigin_of_subset_or_disjoint hG.singularSet hsub hwhole)
    (hD.singularSet.branchOrigin_ne hG.singularSet hsub hmiss)

end DescendingSurgery

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
