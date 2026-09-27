/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCrossingChart
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def HasPLTwoSidedDoubleCrossingAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (P : Set E) (y : F) : Prop :=
  ∃ (a b : E) (A B : Set E), a ∈ A ∧ b ∈ B ∧ f a = y ∧ f b = y ∧
    A ⊆ P ∧ B ⊆ P ∧ Disjoint A B ∧ A ∈ 𝓝[P] a ∧ B ∈ 𝓝[P] b ∧
      IsPLHomeomorphOn f A (f '' A) ∧ IsPLHomeomorphOn f B (f '' B) ∧
        HasPLTwoSidedCrossingAt (f '' A) (f '' B) y ∧ ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} ⊆ A ∪ B

theorem HasPLTwoSidedDoubleCrossingAt.hasPLDoubleCrossingAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {P : Set E} {y : F} (hc : HasPLTwoSidedDoubleCrossingAt f P y) :
    HasPLDoubleCrossingAt f P y := by
  obtain ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAnhds, hBnhds, hfA, hfB,
    hcross, hfiber⟩ := hc
  exact ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAnhds, hBnhds, hfA, hfB,
    hcross.hasPLCrossingAt, hfiber⟩

theorem mem_frontier_of_halfPlane_sheet_model {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hEdim : Module.finrank ℝ E = 2) {f : E → F} {P C : Set E}
    {a : E} {y : F} (haC : a ∈ C) (hCP : C ⊆ P) (hCnhds : C ∈ 𝓝[P] a) (hfay : f a = y)
    (hfC : IsPLHomeomorphOn f C (f '' C)) {U V : Set F} {h : F → F} {R : Submodule ℝ F}
    {ℓ : F →ₗ[ℝ] ℝ} (hU : IsOpen U) (hyU : y ∈ U) (hh : IsPLHomeomorphOn h U V)
    (hhy : h y = 0) (hRdim : Module.finrank ℝ R = 2) {u : F} (huR : u ∈ R) (hℓu : ℓ u ≠ 0)
    (hlocal : ∀ᶠ z in 𝓝 y, z ∈ f '' C ↔ h z ∈ R ∧ 0 ≤ ℓ (h z)) :
    a ∈ frontier P := by
  obtain ⟨w, hwR, hℓw⟩ : ∃ w ∈ R, ℓ w = 1 := by
    refine ⟨(ℓ u)⁻¹ • u, R.smul_mem _ huR, ?_⟩
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hℓu]
  have haP : a ∈ P := hCP haC
  refine (mem_frontier_iff_notMem_interior haP).mpr ?_
  intro haInt
  have hCnhds' : C ∈ 𝓝 a := by
    obtain ⟨O, hO, hOP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hCnhds
    refine Filter.mem_of_superset (Filter.inter_mem hO (isOpen_interior.mem_nhds haInt)) ?_
    intro x hx
    exact hOP ⟨hx.1, interior_subset hx.2⟩
  have hfcont : ContinuousAt f a :=
    (hfC.isPiecewiseAffineOn.continuousOn a haC).continuousAt hCnhds'
  let L : Set F := {z | z ∈ f '' C ↔ h z ∈ R ∧ 0 ≤ ℓ (h z)}
  have hL : L ∈ 𝓝 y := by
    change ∀ᶠ z in 𝓝 y, z ∈ f '' C ↔ h z ∈ R ∧ 0 ≤ ℓ (h z)
    exact hlocal
  have hUpre : f ⁻¹' U ∈ 𝓝 a := by
    apply hfcont
    rw [hfay]
    exact hU.mem_nhds hyU
  have hLpre : f ⁻¹' L ∈ 𝓝 a := by
    apply hfcont
    rw [hfay]
    exact hL
  have hsource : C ∩ f ⁻¹' U ∩ f ⁻¹' L ∈ 𝓝 a :=
    Filter.inter_mem (Filter.inter_mem hCnhds' hUpre) hLpre
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.mp hsource
  let e : R ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hRdim)
  let g : E → EuclideanSpace ℝ (Fin 2) := fun x ↦ e (R.orthogonalProjectionOnto (h (f x)))
  have hWdata (x : E) (hxW : x ∈ W) :
      x ∈ C ∧ f x ∈ U ∧ h (f x) ∈ R ∧ 0 ≤ ℓ (h (f x)) := by
    have hx := hWsub hxW
    have hxlocal : f x ∈ f '' C ↔ h (f x) ∈ R ∧ 0 ≤ ℓ (h (f x)) := hx.2
    exact ⟨hx.1.1, hx.1.2, hxlocal.mp ⟨x, hx.1.1, rfl⟩⟩
  have hgcont : ContinuousOn g W := by
    have hfW : ContinuousOn f W :=
      hfC.isPiecewiseAffineOn.continuousOn.mono fun x hx ↦ (hWdata x hx).1
    have hhW : ContinuousOn (h ∘ f) W :=
      hh.isPiecewiseAffineOn.continuousOn.comp hfW fun x hx ↦ (hWdata x hx).2.1
    have hproj : Continuous fun z : F ↦ e (R.orthogonalProjectionOnto z) :=
      e.continuous.comp R.orthogonalProjectionOnto.continuous
    simpa only [g, Function.comp_apply, Function.comp_def] using
      hproj.continuousOn.comp hhW (fun _ _ ↦ mem_univ _)
  have hginj : InjOn g W := by
    intro x hx z hz hxz
    obtain ⟨hxC, hxU, hxR, -⟩ := hWdata x hx
    obtain ⟨hzC, hzU, hzR, -⟩ := hWdata z hz
    have hprojx : R.orthogonalProjectionOnto (h (f x)) = (⟨h (f x), hxR⟩ : R) :=
      R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨h (f x), hxR⟩
    have hprojz : R.orthogonalProjectionOnto (h (f z)) = (⟨h (f z), hzR⟩ : R) :=
      R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨h (f z), hzR⟩
    have hsub : (⟨h (f x), hxR⟩ : R) = ⟨h (f z), hzR⟩ := by
      apply e.injective
      simpa only [g, hprojx, hprojz] using hxz
    have hhfz : h (f x) = h (f z) := congrArg Subtype.val hsub
    have hfz : f x = f z := hh.bijOn.injOn hxU hzU hhfz
    exact hfC.bijOn.injOn hxC hzC hfz
  have hgopen : IsOpen (g '' W) :=
    DifferentialGeometry.Topology.invariance_of_domain_isOpen_image_of_finrank_eq
      (by simp [hEdim]) hWopen hgcont hginj
  have hga : g a = 0 := by simp only [g, hfay, hhy, map_zero]
  have hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ g '' W := ⟨a, haW, hga⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hgopen 0 hzero
  let wR : R := ⟨w, hwR⟩
  have hwRne : wR ≠ 0 := by
    intro hzerow
    have hw0 : w = 0 := congrArg Subtype.val hzerow
    rw [hw0, map_zero] at hℓw
    norm_num at hℓw
  have hewne : e wR ≠ 0 := by simpa using e.injective.ne hwRne
  have hewpos : 0 < ‖e wR‖ := norm_pos_iff.mpr hewne
  let δ : ℝ := ε / (2 * ‖e wR‖)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hewpos)
  let z : EuclideanSpace ℝ (Fin 2) := (-δ) • e wR
  have hzball : z ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]
    change ‖(-δ) • e wR‖ < ε
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδ]
    change ε / (2 * ‖e wR‖) * ‖e wR‖ < ε
    field_simp
    nlinarith
  obtain ⟨x, hxW, hgxz⟩ := hball hzball
  obtain ⟨-, -, hxR, hxnonneg⟩ := hWdata x hxW
  have hprojx : R.orthogonalProjectionOnto (h (f x)) = (⟨h (f x), hxR⟩ : R) :=
    R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨h (f x), hxR⟩
  have hcoord : e (⟨h (f x), hxR⟩ : R) = (-δ) • e wR := by
    simpa only [g, hprojx, z] using hgxz
  have hsub : (⟨h (f x), hxR⟩ : R) = (-δ) • wR := by
    apply e.injective
    simpa only [map_smul] using hcoord
  have hvalue := congrArg (fun v : R ↦ ℓ (v : F)) hsub
  change ℓ (h (f x)) = ℓ ((-δ) • w) at hvalue
  rw [map_smul, hℓw, smul_eq_mul, mul_one] at hvalue
  linarith

theorem HasPLDoubleCrossingAt.hasPLTwoSidedDoubleCrossingAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (hEdim : Module.finrank ℝ E = 2)
    {f : E → F} {P : Set E} {y : F} (hc : HasPLDoubleCrossingAt f P y)
    (hi : P ∩ f ⁻¹' {y} ⊆ interior P) :
    HasPLTwoSidedDoubleCrossingAt f P y := by
  obtain ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAnhds, hBnhds, hfA, hfB,
    hcross, hfiber⟩ := hc
  obtain ⟨U, V, h, R, S, α, β, hU, hV, hyU, hh, hhy, hRdim, hSdim, hIdim, hsup, hα, hβ,
    -, hlocal⟩ := hcross
  have hlocalA : ∀ᶠ z in 𝓝 y, z ∈ f '' A ↔ h z ∈ R ∧ 0 ≤ α (h z) :=
    hlocal.mono fun _ hz ↦ hz.1
  have hlocalB : ∀ᶠ z in 𝓝 y, z ∈ f '' B ↔ h z ∈ S ∧ 0 ≤ β (h z) :=
    hlocal.mono fun _ hz ↦ hz.2
  have hnotfront : ∀ x ∈ P, f x = y → x ∉ frontier P := by
    intro x hxP hxy hxfront
    exact (mem_frontier_iff_notMem_interior hxP).mp hxfront (hi ⟨hxP, hxy⟩)
  have hαzero : α = 0 := by
    rcases hα with hα0 | ⟨v, hvRS, hαv⟩
    · exact hα0
    · exact absurd (mem_frontier_of_halfPlane_sheet_model hEdim haA hAP hAnhds hfa hfA hU
        hyU hh hhy hRdim hvRS.1 hαv hlocalA) (hnotfront a (hAP haA) hfa)
  have hβzero : β = 0 := by
    rcases hβ with hβ0 | ⟨v, hvRS, hβv⟩
    · exact hβ0
    · exact absurd (mem_frontier_of_halfPlane_sheet_model hEdim hbB hBP hBnhds hfb hfB hU
        hyU hh hhy hSdim hvRS.2 hβv hlocalB) (hnotfront b (hBP hbB) hfb)
  refine ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAnhds, hBnhds, hfA, hfB,
    ⟨U, V, h, R, S, hU, hV, hyU, hh, hhy, hRdim, hSdim, hIdim, hsup, ?_⟩, hfiber⟩
  filter_upwards [hlocal] with z hz
  refine ⟨?_, ?_⟩
  · rw [hz.1, hαzero]
    simp
  · rw [hz.2, hβzero]
    simp

theorem NormalSingularCellData.mem_interior_domain_of_notMem_boundary {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M}
    {BdM B : Set M} (hD : NormalSingularCellData D BdM B) {y : M} (hyBd : y ∉ BdM)
    {x : EuclideanSpace ℝ (Fin 2)} (hxdom : x ∈ D.domain) (hxy : D x = y) :
    x ∈ interior D.domain := by
  by_contra hxnot
  have hxfront : x ∈ frontier D.domain := (mem_frontier_iff_notMem_interior hxdom).mpr hxnot
  have hmemrange : D x ∈ Set.range D.boundary := ⟨⟨x, hxfront⟩, rfl⟩
  rw [← hD.image_inter_boundary] at hmemrange
  exact hyBd (hxy ▸ hmemrange.2)

theorem NormalSingularCellData.hasPLTwoSidedDoubleCrossingAt_of_notMem_boundary {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M}
    {BdM B : Set M} (hD : NormalSingularCellData D BdM B) {y : M}
    (hy : y ∈ doublePointSet D D.domain) (hyBd : y ∉ BdM) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLTwoSidedDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source) (e y) := by
  obtain ⟨e, he, hye, hcross⟩ := hD.crossing y hy
  refine ⟨e, he, hye, ?_⟩
  rcases hcross with ⟨hmem, -⟩ | ⟨-, hdouble⟩
  · exfalso
    obtain ⟨z, ⟨hzsrc, hzBd⟩, hze⟩ := hmem
    exact hyBd (e.injOn hzsrc hye hze ▸ hzBd)
  · have hEdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
    refine hdouble.hasPLTwoSidedDoubleCrossingAt hEdim ?_
    rintro x ⟨⟨hxdom, hxsrc⟩, hxy⟩
    have hxy' : e (D x) = e y := hxy
    have hxDy : D x = y := e.injOn hxsrc hye hxy'
    have hxint : x ∈ interior D.domain :=
      hD.mem_interior_domain_of_notMem_boundary hyBd hxdom hxDy
    have hdomnhds : D.domain ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxint
    have hcont : ContinuousAt D x := (D.continuousOn x hxdom).continuousAt hdomnhds
    have hpre : D ⁻¹' e.source ∈ 𝓝 x := hcont (e.open_source.mem_nhds hxsrc)
    exact mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hdomnhds hpre)

end DifferentialGeometry.Topology.PiecewiseLinear
