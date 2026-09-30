import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem ContinuousWithinAt.mem_frontier_of_mem_frontier_inter_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {P : Set X} {U : Set Y} {x : X}
    (hf : ContinuousWithinAt f P x) (hxP : x ∈ P)
    (hU : IsOpen U) (hfx : f x ∈ U)
    (hx : x ∈ frontier (P ∩ f ⁻¹' U)) :
    x ∈ frontier P := by
  apply (mem_frontier_iff_notMem_interior hxP).mpr
  intro hxInt
  have hfAt : ContinuousAt f x :=
    hf.continuousAt (mem_interior_iff_mem_nhds.mp hxInt)
  have hpre : f ⁻¹' U ∈ nhds x := hfAt (hU.mem_nhds hfx)
  have hinter : x ∈ interior (P ∩ f ⁻¹' U) :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.inter_mem (mem_interior_iff_mem_nhds.mp hxInt) hpre)
  have hxInter : x ∈ P ∩ f ⁻¹' U := ⟨hxP, hfx⟩
  exact (mem_frontier_iff_notMem_interior hxInter).mp hx hinter

open Classical in
private theorem mem_frontier_of_boundary_crossing_sheet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : EuclideanSpace ℝ (Fin 2) → E}
    {P C : Set (EuclideanSpace ℝ (Fin 2))} {a : EuclideanSpace ℝ (Fin 2)}
    {y : E} (haC : a ∈ C) (hCP : C ⊆ P) (hCnhds : C ∈ nhdsWithin a P)
    (hfay : f a = y) (hfC : IsPLHomeomorphOn f C (f '' C))
    {U V : Set E} {h : E → E} {R : Submodule ℝ E} {ℓ : E →ₗ[ℝ] ℝ}
    (hU : IsOpen U) (hyU : y ∈ U) (hh : IsPLHomeomorphOn h U V)
    (hhy : h y = 0) (hRdim : Module.finrank ℝ R = 2)
    {u : E} (huR : u ∈ R) (hℓu : ℓ u = 1)
    (hlocal : ∀ᶠ z in nhds y, z ∈ f '' C ↔ h z ∈ R ∧ 0 ≤ ℓ (h z)) :
    a ∈ frontier P := by
  have haP : a ∈ P := hCP haC
  apply (mem_frontier_iff_notMem_interior haP).mpr
  intro haInt
  have hCnhds' : C ∈ nhds a := by
    obtain ⟨O, hO, hOP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hCnhds
    apply Filter.mem_of_superset
      (Filter.inter_mem hO (isOpen_interior.mem_nhds haInt))
    intro x hx
    exact hOP ⟨hx.1, interior_subset hx.2⟩
  have hfcont : ContinuousAt f a :=
    (hfC.isPiecewiseAffineOn.continuousOn a haC).continuousAt hCnhds'
  let L : Set E := {z | z ∈ f '' C ↔ h z ∈ R ∧ 0 ≤ ℓ (h z)}
  have hL : L ∈ nhds y := by
    change ∀ᶠ z in nhds y, z ∈ f '' C ↔ h z ∈ R ∧ 0 ≤ ℓ (h z)
    exact hlocal
  have hUpre : f ⁻¹' U ∈ nhds a := by
    apply hfcont
    rw [hfay]
    exact hU.mem_nhds hyU
  have hLpre : f ⁻¹' L ∈ nhds a := by
    apply hfcont
    rw [hfay]
    exact hL
  have hsource : (C ∩ f ⁻¹' U) ∩ f ⁻¹' L ∈ nhds a :=
    Filter.inter_mem (Filter.inter_mem hCnhds' hUpre) hLpre
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.mp hsource
  let e : R ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hRdim)
  let g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun x ↦ e (R.orthogonalProjectionOnto (h (f x)))
  have hWdata (x : EuclideanSpace ℝ (Fin 2)) (hxW : x ∈ W) :
      x ∈ C ∧ f x ∈ U ∧ h (f x) ∈ R ∧ 0 ≤ ℓ (h (f x)) := by
    have hx := hWsub hxW
    have hxlocal : f x ∈ f '' C ↔ h (f x) ∈ R ∧ 0 ≤ ℓ (h (f x)) := hx.2
    exact ⟨hx.1.1, hx.1.2, hxlocal.mp ⟨x, hx.1.1, rfl⟩⟩
  have hgcont : ContinuousOn g W := by
    have hfW : ContinuousOn f W :=
      hfC.isPiecewiseAffineOn.continuousOn.mono fun x hx ↦ (hWdata x hx).1
    have hhW : ContinuousOn (h ∘ f) W :=
      hh.isPiecewiseAffineOn.continuousOn.comp hfW fun x hx ↦ (hWdata x hx).2.1
    have hproj : Continuous fun z : E ↦ e (R.orthogonalProjectionOnto z) :=
      e.continuous.comp R.orthogonalProjectionOnto.continuous
    simpa only [g, Function.comp_apply, Function.comp_def] using
      hproj.continuousOn.comp hhW (fun _ _ ↦ mem_univ _)
  have hginj : InjOn g W := by
    intro x hx z hz hxz
    obtain ⟨hxC, hxU, hxR, -⟩ := hWdata x hx
    obtain ⟨hzC, hzU, hzR, -⟩ := hWdata z hz
    have hprojx : R.orthogonalProjectionOnto (h (f x)) =
        (⟨h (f x), hxR⟩ : R) :=
      R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨h (f x), hxR⟩
    have hprojz : R.orthogonalProjectionOnto (h (f z)) =
        (⟨h (f z), hzR⟩ : R) :=
      R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨h (f z), hzR⟩
    have hsub : (⟨h (f x), hxR⟩ : R) = ⟨h (f z), hzR⟩ := by
      apply e.injective
      simpa only [g, hprojx, hprojz] using hxz
    have hhfz : h (f x) = h (f z) := congrArg Subtype.val hsub
    have hfz : f x = f z := hh.bijOn.injOn hxU hzU hhfz
    exact hfC.bijOn.injOn hxC hzC hfz
  have hgopen : IsOpen (g '' W) :=
    DifferentialGeometry.Topology.invariance_of_domain_isOpen_image hWopen hgcont hginj
  have hga : g a = 0 := by simp only [g, hfay, hhy, map_zero]
  have hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ g '' W := ⟨a, haW, hga⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hgopen 0 hzero
  let uR : R := ⟨u, huR⟩
  have huRne : uR ≠ 0 := by
    intro hu
    have hu0 : u = 0 := congrArg Subtype.val hu
    rw [hu0, map_zero] at hℓu
    norm_num at hℓu
  have heune : e uR ≠ 0 := by simpa using e.injective.ne huRne
  have heupos : 0 < ‖e uR‖ := norm_pos_iff.mpr heune
  let δ : ℝ := ε / (2 * ‖e uR‖)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) heupos)
  let z : EuclideanSpace ℝ (Fin 2) := (-δ) • e uR
  have hzball : z ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]
    change ‖(-δ) • e uR‖ < ε
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδ]
    change ε / (2 * ‖e uR‖) * ‖e uR‖ < ε
    field_simp
    nlinarith
  obtain ⟨x, hxW, hgxz⟩ := hball hzball
  obtain ⟨-, -, hxR, hxnonneg⟩ := hWdata x hxW
  have hprojx : R.orthogonalProjectionOnto (h (f x)) =
      (⟨h (f x), hxR⟩ : R) :=
    R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨h (f x), hxR⟩
  have hcoord : e (⟨h (f x), hxR⟩ : R) = (-δ) • e uR := by
    simpa only [g, hprojx, z] using hgxz
  have hsub : (⟨h (f x), hxR⟩ : R) = (-δ) • uR := by
    apply e.injective
    simpa only [map_smul] using hcoord
  have hvalue := congrArg (fun v : R ↦ ℓ (v : E)) hsub
  change ℓ (h (f x)) = ℓ ((-δ) • u) at hvalue
  rw [map_smul, hℓu, smul_eq_mul, mul_one] at hvalue
  linarith

open Classical in
theorem HasPLBoundaryDoubleCrossingAt.fiber_subset_frontier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : EuclideanSpace ℝ (Fin 2) → E}
    {P : Set (EuclideanSpace ℝ (Fin 2))} {M : Set E} {y : E}
    (hcrossing : HasPLBoundaryDoubleCrossingAt f P M y)
    (hfiber : (P ∩ f ⁻¹' {y}).encard ≤ 2) :
    P ∩ f ⁻¹' {y} ⊆ frontier P := by
  obtain ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hdisjoint,
    hAnhds, hBnhds, hfA, hfB, hcross, -⟩ := hcrossing
  obtain ⟨U, V, h, R, S, ℓ, hU, -, hyU, hh, hhy, hRdim, hSdim, -, -,
    ⟨u, hu, hℓu⟩, hlocal⟩ := hcross
  have hlocalA : ∀ᶠ z in nhds y,
      z ∈ f '' A ↔ h z ∈ R ∧ 0 ≤ ℓ (h z) :=
    hlocal.mono fun _ hz ↦ hz.2.1
  have hlocalB : ∀ᶠ z in nhds y,
      z ∈ f '' B ↔ h z ∈ S ∧ 0 ≤ ℓ (h z) :=
    hlocal.mono fun _ hz ↦ hz.2.2
  have haFrontier : a ∈ frontier P :=
    mem_frontier_of_boundary_crossing_sheet haA hAP hAnhds hfa hfA hU hyU hh hhy
      hRdim hu.1 hℓu hlocalA
  have hbFrontier : b ∈ frontier P :=
    mem_frontier_of_boundary_crossing_sheet hbB hBP hBnhds hfb hfB hU hyU hh hhy
      hSdim hu.2 hℓu hlocalB
  have hab : a ≠ b := by
    intro hab
    subst b
    exact Set.disjoint_left.mp hdisjoint haA hbB
  have hp : P ∩ f ⁻¹' {y} = {a, b} :=
    fiber_eq_pair_of_encard_le_two f P (hAP haA) (hBP hbB) hab hfa hfb hfiber
  intro x hx
  rw [hp] at hx
  rcases hx with rfl | rfl
  · exact haFrontier
  · exact hbFrontier

open Classical in
theorem HasPLBoundaryDoubleCrossingAt.fiber_subset_frontier_of_comp_openPartialHomeomorph
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : EuclideanSpace ℝ (Fin 2) → X}
    {P : Set (EuclideanSpace ℝ (Fin 2))} {e : OpenPartialHomeomorph X E}
    {M : Set E} {y : X} (hf : ContinuousOn f P) (hy : y ∈ e.source)
    (hcrossing : HasPLBoundaryDoubleCrossingAt (e ∘ f)
      (P ∩ f ⁻¹' e.source) M (e y))
    (hfiber : (P ∩ f ⁻¹' {y}).encard ≤ 2) :
    P ∩ f ⁻¹' {y} ⊆ frontier P := by
  have hrestricted :
      ((P ∩ f ⁻¹' e.source) ∩ (e ∘ f) ⁻¹' {e y}).encard ≤ 2 := by
    apply (encard_mono ?_).trans hfiber
    rintro x ⟨⟨hxP, hxe⟩, hx⟩
    refine ⟨hxP, ?_⟩
    change f x = y
    apply e.injOn hxe hy
    exact hx
  have hfrontier := hcrossing.fiber_subset_frontier hrestricted
  intro x hx
  have hfx : f x = y := hx.2
  have hxe : f x ∈ e.source := hfx.symm ▸ hy
  have hxrestricted :
      x ∈ (P ∩ f ⁻¹' e.source) ∩ (e ∘ f) ⁻¹' {e y} := by
    exact ⟨⟨hx.1, hxe⟩, congrArg e hfx⟩
  exact ContinuousWithinAt.mem_frontier_of_mem_frontier_inter_preimage
    (hf x hx.1) hx.1 e.open_source hxe (hfrontier hxrestricted)

namespace NormalSingularCellData

universe u

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  {D : SingularTwoCell X} {BdM B : Set X}

open Classical in
theorem fiber_subset_frontier_of_boundary_crossing
    (hD : NormalSingularCellData D BdM B) {y : X}
    {e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3))}
    {N : Set (EuclideanSpace ℝ (Fin 3))} (hy : y ∈ e.source)
    (hcrossing : HasPLBoundaryDoubleCrossingAt (e ∘ D)
      (D.domain ∩ D ⁻¹' e.source) N (e y)) :
    D.domain ∩ D ⁻¹' {y} ⊆ frontier D.domain :=
  hcrossing.fiber_subset_frontier_of_comp_openPartialHomeomorph
    D.continuousOn hy (hD.fiber_le_two y)

open Classical in
theorem exists_boundary_crossing_chart
    (hD : NormalSingularCellData D BdM B) {y : X}
    (hy : y ∈ doublePointSet D D.domain ∩ BdM) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) X, y ∈ e.source ∧
      ∃ N : Set (EuclideanSpace ℝ (Fin 3)),
        HasPLBoundaryDoubleCrossingAt (e ∘ D)
          (D.domain ∩ D ⁻¹' e.source) N (e y) := by
  obtain ⟨e, he, hye, hcross⟩ := hD.crossing y hy.1
  refine ⟨e, he, hye, ?_⟩
  rcases hcross with ⟨-, N, hcross⟩ | ⟨hnot, -⟩
  · exact ⟨N, hcross⟩
  · exact (hnot ⟨y, ⟨hye, hy.2⟩, rfl⟩).elim

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
