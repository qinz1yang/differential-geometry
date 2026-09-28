/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartTransitionRealisation
import DifferentialGeometry.Topology.PiecewiseLinear.CrossHalfPlaneCharts
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.MarkedBranchChartPL
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarSourceCharts
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarQuarterReading

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_marked_branchSurface_disks
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
        {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
        {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)},
        hD.IsBranchDeckInvolution c J τ → hD.IsTwoSidedBranchCollar c J Q C ρ →
        ∀ a ∈ J,
          ∃ (ψ : (ℝ × ℝ) × ℝ → E) (V : Set ((ℝ × ℝ) × ℝ)) (Ω W : Set E)
            (A : Bool → Set (EuclideanSpace ℝ (Fin 2)))
            (P : Fin 4 → Set E) (q : Fin 4 → (Fin 3 → ℝ) → E),
            IsOpen V ∧ IsOpen Ω ∧ IsOpen W ∧ ((D a : L.space) : E) ∈ W ∧ W ⊆ Ω ∧
            IsPLHomeomorphOn ψ V (L.space ∩ Ω) ∧
            (∀ p ∈ V, ψ p ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes) ∧
            (∀ p ∈ V,
              ψ p ∈ Subtype.val '' hD.singularSet.branchCarrier c ↔ p.1 = 0) ∧
            (∀ b, IsCompact (A b) ∧ A b ⊆ C ∧ InjOn D (A b)) ∧ Disjoint (A false) (A true) ∧
            a ∈ A false ∧ τ a ∈ A true ∧
            (∀ x ∈ D.domain, ((D x : L.space) : E) ∈ W → x ∈ A false ∪ A true) ∧
            (∀ b, ∀ y ∈ hD.singularSet.branchCarrier c,
              (y : E) ∈ W → y ∈ D '' (A b ∩ J)) ∧
            (∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P i) ∧
              P i ⊆ L.space ∩ Subtype.val '' (D '' D.domain)) ∧
            (∀ x ∈ L.space ∩ W, ∀ i,
              x ∈ P i ↔ Function.invFunOn ψ V x ∈ crossHalfPlane i) ∧
            (∀ x ∈ L.space ∩ W, ∀ i,
              x ∈ P i ↔ x ∈ (Subtype.val ∘ D) ''
                (A (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2)) ∧
            ∀ x ∈ L.space ∩ W, ∀ i,
              x ∈ q i '' stdSimplexBoundary 2 ↔
                x ∈ Subtype.val '' hD.singularSet.branchCarrier c := by
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc J Q C τ ρ hτ hρ a ha
  obtain ⟨e, he, e₀, he₀, g, hg, heq⟩ :=
    hD.exists_markedCrossingChartAt_with_pl_transition hc hτ hρ ha
  obtain ⟨Ω₀, hΩ₀, hΩ₀eq, hφ⟩ :=
    exists_isPLHomeomorphOn_val_symm_of_pl_transition L hL he₀ g hg
  rw [← heq] at hΩ₀eq hφ
  obtain ⟨A₀, A₁, U, hA₀, hA₁, hA₀C, hA₁C, hAA, haA₀, hτaA₁, hinj₀, hinj₁,
    hU, haU, hUe, hpre, hread₀, hread₁, hreadΓ, hpos₀, hpos₁⟩ :=
      hD.exists_compact_source_sheets_of_markedCrossingChart hτ hρ he
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
  let A : Bool → Set (EuclideanSpace ℝ (Fin 2)) := fun b => if b then A₁ else A₀
  have hAC : ∀ b, A b ⊆ C := by intro b; cases b <;> assumption
  have hAdom : ∀ b, A b ⊆ D.domain := fun b => (hAC b).trans (hρ.2.2.1.trans interior_subset)
  let Z := e.target ∩ (fun z => (e.symm z : E)) ⁻¹' O
  have hZ : IsOpen Z :=
    hφ.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage e.open_target hO
  have hφZ : IsPLHomeomorphOn (fun z => (e.symm z : E)) Z (L.space ∩ (Ω₀ ∩ O)) := by
    simpa only [inter_assoc] using hφ.restrict_preimage_isOpen e.open_target hO
  obtain ⟨hV, hnormal⟩ := isPLHomeomorphOn_linearEquiv_image crossNormalFormEquiv hZ
  let V := crossNormalFormEquiv '' Z
  have hninv : IsPLHomeomorphOn crossNormalFormEquiv.symm V Z := by
    apply hnormal.symm.congr
    intro p hp
    apply crossNormalFormEquiv.injective
    exact (crossNormalFormEquiv.apply_symm_apply p).trans
      (hnormal.bijOn.invOn_invFunOn.2 hp).symm
  let ψ : (ℝ × ℝ) × ℝ → E := fun p => (e.symm (crossNormalFormEquiv.symm p) : E)
  have hψ : IsPLHomeomorphOn ψ V (L.space ∩ (Ω₀ ∩ O)) := hninv.trans hφZ
  have hpZ : ∀ p ∈ V, crossNormalFormEquiv.symm p ∈ Z := fun p hp => hninv.bijOn.mapsTo hp
  have hyU : ∀ p ∈ V, e.symm (crossNormalFormEquiv.symm p) ∈ U := by
    intro p hp
    rw [← hOU]
    exact (hpZ p hp).2
  have hnormalE : ∀ p ∈ V, crossNormalFormEquiv (e (e.symm (crossNormalFormEquiv.symm p))) = p := by
    intro p hp
    rw [e.right_inv (hpZ p hp).1, crossNormalFormEquiv.apply_symm_apply]
  have hF : ∀ p ∈ V, ψ p ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes := by
    intro p hp
    change (e.symm (crossNormalFormEquiv.symm p) : E) ∈ Subtype.val '' (D '' D.domain) ↔ _
    rw [Subtype.val_injective.mem_set_image]
    have hunion : ∀ y ∈ U, y ∈ D '' D.domain ↔ y ∈ D '' A₀ ∪ D '' A₁ := by
      intro y hy
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hpre x hx hy with hxA | hxA
        · exact Or.inl ⟨x, interior_subset hxA, rfl⟩
        · exact Or.inr ⟨x, interior_subset hxA, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨x, hAdom false hx, rfl⟩
        · exact ⟨x, hAdom true hx, rfl⟩
    rw [hunion _ (hyU p hp), mem_union, hread₀ _ (hyU p hp), hread₁ _ (hyU p hp),
      e.right_inv (hpZ p hp).1]
    exact or_comm
  have hΓ : ∀ p ∈ V, ψ p ∈ Subtype.val '' hD.singularSet.branchCarrier c ↔ p.1 = 0 := by
    intro p hp
    change (e.symm (crossNormalFormEquiv.symm p) : E) ∈ Subtype.val '' _ ↔ _
    rw [Subtype.val_injective.mem_set_image, hreadΓ _ (hyU p hp), e.right_inv (hpZ p hp).1]
    rfl
  have haΩ : ((D a : L.space) : E) ∈ L.space ∩ (Ω₀ ∩ O) := by
    refine ⟨(D a).2, ?_, ?_⟩
    · change D a ∈ Subtype.val ⁻¹' Ω₀
      rw [hΩ₀eq]
      exact he.2.1
    · change D a ∈ Subtype.val ⁻¹' O
      rwa [hOU]
  have haΓ : ((D a : L.space) : E) ∈ Subtype.val '' hD.singularSet.branchCarrier c :=
    ⟨D a, (show a ∈ hD.branchPreimage c from hτ.1.symm ▸ ha).2, rfl⟩
  obtain ⟨W, P, q, hW, haW, hWΩ, hq, hP, hread, hbd⟩ :=
    hψ.exists_crossHalfPlane_disks hV (hΩ₀.inter hO) hF hΓ haΩ haΓ
  have hWU : ∀ y : L.space, (y : E) ∈ W → y ∈ U := by
    intro y hy
    rw [← hOU]
    exact (hWΩ hy).2
  refine ⟨ψ, V, Ω₀ ∩ O, W, A, P, q, hV, hΩ₀.inter hO, hW, haW, hWΩ, hψ, hF, hΓ,
    ?_, hAA, interior_subset haA₀, interior_subset hτaA₁, ?_, ?_,
    fun i => ⟨hq i, hP i⟩, hread, ?_, hbd⟩
  · intro b
    cases b
    · exact ⟨hA₀, hA₀C, hinj₀⟩
    · exact ⟨hA₁, hA₁C, hinj₁⟩
  · intro x hx hxW
    exact (hpre x hx (hWU _ hxW)).elim (fun h => Or.inl (interior_subset h))
      (fun h => Or.inr (interior_subset h))
  · intro b y hy hyW
    have hey : (e y).2 = 0 := (hreadΓ y (hWU y hyW)).mp hy
    have hyA : y ∈ D '' A b := by
      cases b
      · exact (hread₀ y (hWU y hyW)).mpr (congrArg Prod.snd hey)
      · exact (hread₁ y (hWU y hyW)).mpr (congrArg Prod.fst hey)
    obtain ⟨x, hx, hxy⟩ := hyA
    refine ⟨x, ⟨hx, hτ.1 ▸ (show x ∈ hD.branchPreimage c from ⟨hAdom b hx, ?_⟩)⟩, hxy⟩
    change D x ∈ hD.singularSet.branchCarrier c
    rwa [hxy]
  · intro x hx i
    obtain ⟨p, hp, hpx⟩ := hψ.bijOn.surjOn ⟨hx.1, hWΩ hx.2⟩
    have hquarter := hD.mem_source_quarter_iff_crossHalfPlane hρ hAC
      (fun b y hy => by cases b <;> first | exact hread₀ y hy | exact hread₁ y hy)
      hreadΓ (fun b y hy => by cases b <;> first | exact hpos₀ y hy | exact hpos₁ y hy)
      i (hyU p hp)
    rw [hnormalE p hp] at hquarter
    rw [hread x hx i, ← hpx, hψ.bijOn.invOn_invFunOn.1 hp]
    have himage : ψ p ∈ (Subtype.val ∘ D) ''
        (A (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2) ↔
        e.symm (crossNormalFormEquiv.symm p) ∈ D ''
          (A (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2) := by
      rw [image_comp, Subtype.val_injective.mem_set_image]
    exact hquarter.symm.trans himage.symm

end DifferentialGeometry.Topology.PiecewiseLinear
