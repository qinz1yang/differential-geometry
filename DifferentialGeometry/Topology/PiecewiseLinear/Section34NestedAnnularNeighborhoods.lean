/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SmallSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOnCompact

/-! # Section34Nested Annular Neighborhoods -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLDerivedNeighborhoodExhaustion.exists_nested_piercing_annuli
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D F₀ F₁ : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O)
    (hF₀ : IsPolyhedralSphere (n := 3) 2 F₀) (hF₁ : IsPolyhedralSphere (n := 3) 2 F₁)
    (hF₀U : F₀ ⊆ U) (hF₁U : F₁ ⊆ U) (hCF₀ : C ⊆ F₀) (hCF₁ : C ⊆ F₁) :
    ∃ S T A A₀ A₁ B B₀ B₁ L L₀ L₁ : Set X,
      IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsLocallyFiniteRegularNeighborhoodOf (n := 3) T C U ∧
      T ⊆ interior S ∧ IsTopologicalSolidTorus S ∧ IsTopologicalSolidTorus T ∧ S ⊆ O ∧
      (A = F₀ ∩ T ∧ IsAnnulusOn A A₀ A₁ ∧ C ⊆ A \ (A₀ ∪ A₁)) ∧
      (B ⊆ F₁ ∧ IsAnnulusOn B B₀ B₁) ∧
      T ∩ F₁ ⊆ B \ (B₀ ∪ B₁) ∧
      (B ⊆ interior S ∧ B₀ ∪ B₁ ⊆ S \ T) ∧
      (IsAnnulusOn L L₀ L₁ ∧ L ⊆ B ∩ interior T) ∧ C ⊆ L \ (L₀ ∪ L₁) := by
  obtain ⟨S, hS, htS, hSO⟩ :=
    h.exists_solidTorus_regularNeighborhood_subset_open hU hC hD hDU hCD hO hCO
  have hCS : C ⊆ interior S := subset_interior_iff_mem_nhdsSet.mpr hS.mem_nhdsSet
  obtain ⟨V, hV, -, hVS, hVB⟩ := h.exists_solidTorus_regularNeighborhood_with_annular_cores
    hU hC hD hDU hCD isOpen_interior hCS (fun _ : Unit => F₁)
    (fun _ => hF₁) (fun _ => hF₁U) (fun _ => hCF₁)
  obtain ⟨B₀, B₁, hB, hCB⟩ := hVB ()
  have hCV : C ⊆ interior V := subset_interior_iff_mem_nhdsSet.mpr hV.mem_nhdsSet
  have hBV : B₀ ∪ B₁ ⊆ V ∩ F₁ := union_subset hB.first_subset hB.second_subset
  have hBo : IsOpen (B₀ ∪ B₁)ᶜ :=
    (hB.isCompact_first.isClosed.union hB.isCompact_second.isClosed).isOpen_compl
  have hCO' : C ⊆ interior V ∩ (B₀ ∪ B₁)ᶜ := fun x hx => ⟨hCV hx, (hCB hx).2⟩
  obtain ⟨T, hT, htT, hTV, hTA⟩ := h.exists_solidTorus_regularNeighborhood_with_annular_cores
    hU hC hD hDU hCD (isOpen_interior.inter hBo) hCO' (fun _ : Unit => F₀)
    (fun _ => hF₀) (fun _ => hF₀U) (fun _ => hCF₀)
  obtain ⟨A₀, A₁, hA, hCA⟩ := hTA ()
  have hCT : C ⊆ interior T := subset_interior_iff_mem_nhdsSet.mpr hT.mem_nhdsSet
  obtain ⟨W, -, -, hWT, hWL⟩ := h.exists_solidTorus_regularNeighborhood_with_annular_cores
    hU hC hD hDU hCD isOpen_interior hCT (fun _ : Unit => F₁)
    (fun _ => hF₁) (fun _ => hF₁U) (fun _ => hCF₁)
  obtain ⟨L₀, L₁, hL, hCL⟩ := hWL ()
  have hTS : T ⊆ interior S := fun x hx => (hVS (interior_subset (hTV hx).1.1)).1
  refine ⟨S, T, T ∩ F₀, A₀, A₁, V ∩ F₁, B₀, B₁, W ∩ F₁, L₀, L₁,
    hS, hT, hTS, htS, htT, hSO.trans inter_subset_left,
    ⟨inter_comm _ _, hA, hCA⟩, ⟨inter_subset_right, hB⟩, ?_, ?_, ?_, hCL⟩
  · intro x hx
    exact ⟨⟨interior_subset (hTV hx.1).1.1, hx.2⟩, (hTV hx.1).1.2⟩
  · refine ⟨fun x hx => (hVS hx.1).1, fun x hx => ?_⟩
    exact ⟨interior_subset (hVS (hBV hx).1).1, fun hxT => (hTV hxT).1.2 hx⟩
  · refine ⟨hL, fun x hx => ?_⟩
    have hxT : x ∈ interior T := (hWT hx.1).1
    exact ⟨⟨interior_subset (hTV (interior_subset hxT)).1.1, hx.2⟩, hxT⟩

end DifferentialGeometry.Topology.PiecewiseLinear
