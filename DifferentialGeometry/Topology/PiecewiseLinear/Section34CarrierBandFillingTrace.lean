import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandTargetTrace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsTopologicalSolidTorus.nonempty_cap_sdiff_of_carrier
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {T D J C : Set M} {d : ℕ}
    (hT : IsTopologicalSolidTorus T) (hD : IsPLCellOn d D J)
    (hcarry : CarriesFundamentalGroupOnto J T) (hJ : J.Nonempty) (hCT : C ⊆ T) :
    (D \ C).Nonempty := by
  by_contra hnone
  have hDC : D ⊆ C := by
    intro x hx
    by_contra hxC
    exact hnone ⟨x, hx, hxC⟩
  exact hT.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD
    (hDC.trans hCT) hJ hD.boundary_subset hcarry

theorem IsPLCellOn.exists_annular_band_with_carrier_trace {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J L T : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hL : IsPolyhedralSphere (n := 3) 1 L) (hJA : J ⊆ A) (hLA : L ⊆ A)
    (hJL : Disjoint J L) (hJend : Disjoint J (A₀ ∪ A₁))
    (hLend : Disjoint L (A₀ ∪ A₁))
    (hT : IsTopologicalSolidTorus T) (hAT : A ⊆ T)
    (hJcarry : CarriesFundamentalGroupOnto J T)
    (hLcarry : CarriesFundamentalGroupOnto L T) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (φ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = L ∧
      ∀ C : Set M, (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ C →
        frontier C ∩ B ⊆ (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) →
        C ⊆ T →
          B ∩ C = (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  have hJne : J.Nonempty := by
    obtain ⟨p, hp⟩ := hJ
    exact p.piece.bijOn.image_eq ▸ hp.nonempty.image p.piece.map
  have hLne : L.Nonempty := by
    obtain ⟨p, hp⟩ := hL
    exact p.piece.bijOn.image_eq ▸ hp.nonempty.image p.piece.map
  have hJess : ¬ ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A := by
    rintro ⟨D, hD, hDA⟩
    exact hT.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD
      (hDA.trans hAT) hJne hD.boundary_subset hJcarry
  have hLess : ¬ ∃ D : Set M, IsPLCellOn 2 D L ∧ D ⊆ A := by
    rintro ⟨D, hD, hDA⟩
    exact hT.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD
      (hDA.trans hAT) hLne hD.boundary_subset hLcarry
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hAP : A ⊆ u '' P := hAB.trans (hB ▸ image_mono hfront)
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτc : ContinuousOn τ (u '' P) := (hu.isPLOn_inverse hleft).continuousOn
  have hτi : InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hA' := hA.image_of_continuousOn_injOn (hτc.mono hAP) (hτi.mono hAP)
  have hA'S : τ '' A ⊆ frontier P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hAB hx
    rw [hleft (hfront hz)]
    exact hz
  have hback (X : Set M) (hXA : X ⊆ A) : u '' (τ '' X) = X := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hAP (hXA hx))).trans (image_id' X)
  have hdisj {X Y : Set M} (hXA : X ⊆ A) (hYA : Y ⊆ A) (hXY : Disjoint X Y) :
      Disjoint (τ '' X) (τ '' Y) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have heq := hτi (hAP (hXA hx)) (hAP (hYA hy)) hxy.symm
    exact disjoint_left.mp hXY hx (heq ▸ hy)
  have hess {X : Set M} (hXA : X ⊆ A)
      (hXess : ¬ ∃ D : Set M, IsPLCellOn 2 D X ∧ D ⊆ A) :
      ¬ ∃ (D : Set (EuclideanSpace ℝ (Fin 3)))
        (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ τ '' A ∧
          q '' stdSimplexBoundary 2 = τ '' X := by
    rintro ⟨D, q, hq, hDA, hqb⟩
    have hDP := (hDA.trans hA'S).trans hfront
    have hpoly : IsPolyhedron D := IsPLBall.isPolyhedron ⟨q, hq⟩
    have huD : IsPLHomeomorphInto 3 u D :=
      (hu.isPLOn.mono_of_isPolyhedron hpoly hDP).isPLHomeomorphInto_model
        hpoly.isCompact (hu.injOn.mono hDP)
    have hc := (isPLCellOn_id_of_isPLBall hq).image huD
    rw [hqb, hback X hXA] at hc
    exact hXess ⟨u '' D, hc, hback A Subset.rfl ▸ image_mono hDA⟩
  have hendA := union_subset hA.first_subset hA.second_subset
  obtain ⟨D₀, D₁, r₀, r₁, φ, hr₀, hr₁, hb₀, hb₁, hD₀S, hD₁S, -, hends,
    hφ, hφA, hφ₀, hφ₁, hF₀, hF₁, hcover⟩ :=
    hP.isPLSphere_frontier.exists_annular_band_with_end_caps hA' hA'S
      (hu.isPLSphere_invFunOn_image hJ (hJA.trans hAP))
      (hu.isPLSphere_invFunOn_image hL (hLA.trans hAP))
      (image_mono hJA) (image_mono hLA) (hdisj hJA hLA hJL)
      (by rw [← image_union]; exact hdisj hJA hendA hJend)
      (by rw [← image_union]; exact hdisj hLA hendA hLend)
      (hess hJA hJess) (hess hLA hLess)
  have hφP := (hφA.trans hA'S).trans hfront
  have hbandA : (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A := by
    rw [image_comp]
    exact hback A Subset.rfl ▸ image_mono hφA
  refine ⟨P, u, φ, hP, hu, hφ, hφP, hbandA, ?_, ?_, ?_⟩
  · rw [image_comp, hφ₀, hback J hJA]
  · rw [image_comp, hφ₁, hback L hLA]
  intro C hFC hCfront hCT
  have hcell {D : Set (EuclideanSpace ℝ (Fin 3))} {X : Set M}
      {q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
      (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDS : D ⊆ frontier P)
      (hXA : X ⊆ A) (hqb : q '' stdSimplexBoundary 2 = τ '' X) :
      IsPLCellOn 2 (u '' D) X := by
    have hpoly : IsPolyhedron D := IsPLBall.isPolyhedron ⟨q, hq⟩
    have huD : IsPLHomeomorphInto 3 u D :=
      (hu.isPLOn.mono_of_isPolyhedron hpoly (hDS.trans hfront)).isPLHomeomorphInto_model
        hpoly.isCompact (hu.injOn.mono (hDS.trans hfront))
    have hc := (isPLCellOn_id_of_isPLBall hq).image huD
    rwa [hqb, hback X hXA] at hc
  have hD₀B : u '' D₀ ⊆ B := by rw [hB]; exact image_mono hD₀S
  have hD₁B : u '' D₁ ⊆ B := by rw [hB]; exact image_mono hD₁S
  have hcover' : B ⊆ u '' D₀ ∪ u '' D₁ ∪
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rw [hB, image_comp, ← image_union, ← image_union]
    exact image_mono hcover
  have hmeet₀ : ((u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ u '' D₀ = J := by
    rw [image_comp, ← hu.injOn.image_inter hφP (hD₀S.trans hfront), hF₀, hback J hJA]
  have hmeet₁ : ((u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ u '' D₁ = L := by
    rw [image_comp, ← hu.injOn.image_inter hφP (hD₁S.trans hfront), hF₁, hback L hLA]
  have hout : (u '' D₀ \ C).Nonempty ∧ (u '' D₁ \ C).Nonempty := by
    constructor
    · exact hT.nonempty_cap_sdiff_of_carrier (hcell hr₀ hD₀S hJA hb₀) hJcarry hJne hCT
    · exact hT.nonempty_cap_sdiff_of_carrier (hcell hr₁ hD₁S hLA hb₁) hLcarry hLne hCT
  exact inter_eq_band_of_end_caps (hbandA.trans hAB) hFC hD₀B hD₁B hcover'
    (hcell hr₀ hD₀S hJA hb₀).isConnected_sdiff_boundary.isPreconnected
    (hcell hr₁ hD₁S hLA hb₁).isConnected_sdiff_boundary.isPreconnected
    hmeet₀ hmeet₁ hout.1 hout.2 hCfront


end DifferentialGeometry.Topology.PiecewiseLinear
