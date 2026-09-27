/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskLocalChartsCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.ArcPatternBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.LateralAnnulusLevels

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsBridgeDisk.exists_arcPatternChart
    {C A B : Set E} {a b : E} (h : IsBridgeDisk C A B a b)
    (hdim : Module.finrank ℝ E = 3) (hC : IsPLBall 3 C) :
    ∃ (Φ : (ℝ × ℝ) × ℝ → E) (N : Set ((ℝ × ℝ) × ℝ)) (Ω : Set E) (τ : ℝ),
      IsOpen N ∧ IsOpen Ω ∧ IsPLHomeomorphOn Φ N Ω ∧ 0 < τ ∧
      coreSegment τ ⊆ N ∧ Φ '' coreSegment τ = B ∩ frontier C ∧
      Φ 0 = a ∧ Φ ((0, 0), τ) = b ∧
      (∀ p ∈ N, Φ p ∈ C ↔ 0 ≤ p.1.2) ∧
      (∀ p ∈ N, Φ p ∈ frontier C ↔ p.1.2 = 0) ∧
      (∀ p ∈ N, Φ p ∈ B ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ 0 ≤ p.2 ∧ p.2 ≤ τ) ∧
      (∀ p ∈ N, Φ p ∈ B ∩ frontier C ↔ p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ τ) ∧
      ∀ p ∈ N, Φ p ∈ A ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ (p.2 = 0 ∨ p.2 = τ) := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := h.exists_frontier_parametrization
  obtain ⟨U₀, V₀, f₀, hU₀, hV₀, haU₀, h0V₀, hf₀, hf₀a, hflags₀⟩ :=
    h.exists_left_endpoint_chart hdim hC
  obtain ⟨U₁, V₁, f₁, hU₁, hV₁, hbU₁, h0V₁, hf₁, hf₁b, hflags₁⟩ :=
    h.exists_right_endpoint_chart hdim hC
  let ψ₀ := Function.invFunOn f₀ U₀
  let ψ₁ := Function.invFunOn f₁ U₁
  have hψ₀ : IsPLHomeomorphOn ψ₀ V₀ (univ ∩ U₀) := by
    simpa only [univ_inter] using hf₀.symm
  have hψ₁ : IsPLHomeomorphOn ψ₁ V₁ (univ ∩ U₁) := by
    simpa only [univ_inter] using hf₁.symm
  have hleft : ∀ p ∈ V₀,
      (ψ₀ p ∈ C ↔ 0 ≤ p.1.2) ∧ (ψ₀ p ∈ frontier C ↔ p.1.2 = 0) ∧
      (ψ₀ p ∈ B ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ 0 ≤ p.2) ∧
      (ψ₀ p ∈ B ∩ frontier C ↔ p.1.1 = 0 ∧ p.1.2 = 0 ∧ 0 ≤ p.2) ∧
      (ψ₀ p ∈ A ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.2 = 0) := by
    intro p hp
    have hflags := hflags₀ (ψ₀ p) (hf₀.bijOn.surjOn.mapsTo_invFunOn hp)
    have heq : f₀ (ψ₀ p) = p := hf₀.bijOn.invOn_invFunOn.2 hp
    simpa only [heq] using hflags
  have hright : ∀ p ∈ V₁,
      (ψ₁ p ∈ C ↔ 0 ≤ p.1.2) ∧ (ψ₁ p ∈ frontier C ↔ p.1.2 = 0) ∧
      (ψ₁ p ∈ B ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.2 ≤ 0) ∧
      (ψ₁ p ∈ B ∩ frontier C ↔ p.1.1 = 0 ∧ p.1.2 = 0 ∧ p.2 ≤ 0) ∧
      (ψ₁ p ∈ A ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.2 = 0) := by
    intro p hp
    have hflags := hflags₁ (ψ₁ p) (hf₁.bijOn.surjOn.mapsTo_invFunOn hp)
    have heq : f₁ (ψ₁ p) = p := hf₁.bijOn.invOn_invFunOn.2 hp
    simpa only [heq] using hflags
  have hψ₀0 : ψ₀ 0 = γ 0 := by
    rw [hγ0, ← hf₀a]
    exact hf₀.bijOn.invOn_invFunOn.1 haU₀
  let P : Bool → Set (ℝ × ℝ) := fun i => if i then {p | p.2 = 0} else {p | 0 ≤ p.2}
  let Z : Bool → Set E := fun i => if i then frontier C else C
  let H : Set (ℝ × ℝ) := {p | p.1 = 0 ∧ 0 ≤ p.2}
  have hP : ∀ i v (t : ℝ), 0 < t → (t • v ∈ P i ↔ v ∈ P i) := by
    intro i v t ht
    cases i
    · exact mul_nonneg_iff_of_pos_left ht
    · change t * v.2 = 0 ↔ v.2 = 0
      simp only [mul_eq_zero, ht.ne', false_or]
  have hH : ∀ v (t : ℝ), 0 < t → (t • v ∈ H ↔ v ∈ H) := by
    intro v t ht
    change t * v.1 = 0 ∧ 0 ≤ t * v.2 ↔ v.1 = 0 ∧ 0 ≤ v.2
    rw [mul_eq_zero, or_iff_right ht.ne', mul_nonneg_iff_of_pos_left ht]
  have hγA : γ 1 ∈ A := by
    rw [hγ1]
    exact (h.inter_frontier.symm.subset (mem_insert_of_mem a (mem_singleton b))).1
  have hleftD (p : (ℝ × ℝ) × ℝ) (hp : p ∈ V₀) :
      ψ₀ p ∈ B ∩ frontier C ↔ p.1 = 0 ∧ 0 ≤ p.2 := by
    simpa only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, and_assoc] using
      (hleft p hp).2.2.2.1
  have hrightD (p : (ℝ × ℝ) × ℝ) (hp : p ∈ V₁) :
      ψ₁ p ∈ B ∩ frontier C ↔ p.1 = 0 ∧ p.2 ≤ 0 := by
    simpa only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, and_assoc] using
      (hright p hp).2.2.2.1
  have hint : ∀ r ∈ Ioo (0 : ℝ) 1, ∃ (ψ : (ℝ × ℝ) × ℝ → E)
      (V : Set ((ℝ × ℝ) × ℝ)) (U : Set E),
      IsOpen V ∧ IsOpen U ∧ IsPLHomeomorphOn ψ V (univ ∩ U) ∧ γ r ∈ U ∧
      (∀ p ∈ V, ψ p ∈ B ↔ p.1 ∈ H) ∧
      (∀ p ∈ V, ψ p ∈ B ∩ frontier C ↔ p.1 = 0) ∧
      (∀ i p, p ∈ V → (ψ p ∈ Z i ↔ p.1 ∈ P i)) ∧ ∀ p ∈ V, ψ p ∉ A := by
    intro r hr
    have hrI := Ioo_subset_Icc_self hr
    have hnot : γ r ∉ ({a, b} : Set E) := by
      intro hx
      rcases hx with hx | hx
      · exact hr.1.ne' (hγ.bijOn.injOn hrI ⟨le_rfl, zero_le_one⟩ (hx.trans hγ0.symm))
      · exact hr.2.ne (hγ.bijOn.injOn hrI ⟨zero_le_one, le_rfl⟩ (hx.trans hγ1.symm))
    obtain ⟨U, V, f, hU, hV, hxU, h0V, hf, hfx, hflags⟩ :=
      h.exists_frontier_chart hdim hC (hγ.bijOn.mapsTo hrI) hnot
    let ψ := Function.invFunOn f U
    have hlocal (p : (ℝ × ℝ) × ℝ) (hp : p ∈ V) :
        (ψ p ∈ C ↔ 0 ≤ p.1.2) ∧ (ψ p ∈ frontier C ↔ p.1.2 = 0) ∧
        (ψ p ∈ B ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2) ∧
        (ψ p ∈ B ∩ frontier C ↔ p.1.1 = 0 ∧ p.1.2 = 0) ∧ ψ p ∉ A := by
      have hg := hflags (ψ p) (hf.bijOn.surjOn.mapsTo_invFunOn hp)
      have heq : f (ψ p) = p := hf.bijOn.invOn_invFunOn.2 hp
      simpa only [heq] using hg
    refine ⟨ψ, V, U, hV, hU, by simpa only [univ_inter] using hf.symm, hxU,
      fun p hp => (hlocal p hp).2.2.1, ?_, ?_, fun p hp => (hlocal p hp).2.2.2.2⟩
    · intro p hp
      simpa only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using
        (hlocal p hp).2.2.2.1
    · intro i p hp
      cases i
      · exact (hlocal p hp).1
      · exact (hlocal p hp).2.1
  obtain ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hcoreimg, hB, hD, hZ, hA, hstart, hend⟩ :=
    exists_arcPatternStraightening_with_ends P hP H hH hγ.isPiecewiseAffineOn.continuousOn
      hγ.bijOn.injOn (fun _ _ => mem_univ _) (fun _ hr => hγ.bijOn.mapsTo hr) hγA
      hV₀ hU₀ hψ₀ h0V₀ hψ₀0 (fun p hp => by simpa only [H, mem_ofPred_eq, and_assoc]
        using (hleft p hp).2.2.1) hleftD
      (fun i p hp => by
        cases i with
        | false => exact (hleft p hp).1
        | true => exact (hleft p hp).2.1)
      (fun p hp => by simpa only [H, mem_ofPred_eq, and_assoc] using (hleft p hp).2.2.2.2)
      hV₁ hU₁ hψ₁ (hγ1.symm ▸ hbU₁)
      (fun p hp => by simpa only [H, mem_ofPred_eq, and_assoc] using (hright p hp).2.2.1)
      hrightD
      (fun i p hp => by
        cases i with
        | false => exact (hright p hp).1
        | true => exact (hright p hp).2.1)
      (fun p hp => by simpa only [H, mem_ofPred_eq, and_assoc] using (hright p hp).2.2.2.2) hint
  refine ⟨Φ, N, Ω, τ, hN, hΩ, by simpa only [univ_inter] using hΦ, hτ, hcore,
    hcoreimg.trans hγ.image_eq, hstart.trans hγ0, hend.trans hγ1,
    hZ false, hZ true, ?_, hD, ?_⟩
  · simpa only [H, mem_ofPred_eq, and_assoc] using hB
  · simpa only [H, mem_ofPred_eq, and_assoc] using hA

theorem IsBridgeDisk.exists_boundary_collar
    {C A B : Set E} {a b : E} (h : IsBridgeDisk C A B a b)
    (hdim : Module.finrank ℝ E = 3) (hC : IsPLBall 3 C) :
    ∃ (W : Set E) (c : E × ℝ → E), IsPolyhedron W ∧ W ⊆ C ∧
      W ∈ 𝓝ˢ[C] (frontier C) ∧
      IsPLHomeomorphOn c (frontier C ×ˢ Icc (0 : ℝ) 2) W ∧
      (∀ x ∈ frontier C, c (x, 0) = x) ∧ W ∩ frontier C = frontier C ∧
      B ∩ W = c '' ((B ∩ frontier C) ×ˢ Icc (0 : ℝ) 2) ∧
      c '' ({a, b} ×ˢ Icc (0 : ℝ) 2) ⊆ A := by
  classical
  obtain ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hβ, hstart, hend,
    hΦC, hΦF, hΦB, -, hΦA⟩ := h.exists_arcPatternChart hdim hC
  obtain ⟨K, hKfin, hKspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 3 K.space := hKspace.symm ▸ hC
  have hfront : (boundaryComplex 3 K).space = frontier C := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K
      hK.isCombinatorialManifoldWithBoundary, hKspace]
  obtain ⟨q, hq, -, -, -, -, -⟩ := h
  have hB : IsPLBall 2 B := ⟨q, hq⟩
  obtain ⟨ε, W, ρ, hε, hW, hWK, hWnhds, hρ, hbase, hWF, hWB, hends⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_collar_with_trace_of_arcPatternChart K
      (isPLSphere_boundaryComplex_space_of_isPLBall K hK) (subset_univ _)
      hB.isPolyhedron.isClosed (by rw [hfront]) hN hΩ
      (by simpa only [univ_inter] using hΦ) hτ hcore hβ
      (by simpa only [hKspace] using hΦC) (by simpa only [hfront] using hΦF) hΦB
      (fun p hp hu hv hz => (hΦA p hp).mpr ⟨hu, hv, hz⟩)
  simp only [hfront, hKspace] at hWK hWnhds hρ hbase hWF hWB
  rw [hstart, hend] at hends
  let u : ℝ → ℝ := fun t => (ε / 2) * t
  have hu : IsPLHomeomorphOn u (Icc (0 : ℝ) 2) (Icc (0 : ℝ) ε) := by
    simpa only [add_zero] using isPLHomeomorphOn_mul_add_Icc (half_pos hε)
      (a := 0) (b := 2) (c := 0) (a' := 0) (b' := ε) (by ring) (by ring)
  have hFpoly : IsPolyhedron (frontier C) := by
    rw [← hfront]
    exact isPolyhedron_space _
  let c : E × ℝ → E := ρ ∘ Prod.map id u
  have hc : IsPLHomeomorphOn c (frontier C ×ˢ Icc (0 : ℝ) 2) W :=
    (hFpoly.isPLHomeomorphOn_id.prodMap hu).trans hρ
  have himage (P : Set E) : c '' (P ×ˢ Icc (0 : ℝ) 2) = ρ '' (P ×ˢ Icc (0 : ℝ) ε) := by
    change (ρ ∘ Prod.map id u) '' (P ×ˢ Icc (0 : ℝ) 2) = _
    rw [image_comp, prodMap_image_prod, image_id, hu.image_eq]
  refine ⟨W, c, hW, hWK, hWnhds, hc, ?_, hWF, ?_, ?_⟩
  · intro x hx
    simpa only [c, Function.comp_apply, Prod.map_apply, id_eq, u, mul_zero] using hbase x hx
  · rw [inter_comm, himage]
    exact hWB
  · rw [himage]
    exact hends

end DifferentialGeometry.Topology.PiecewiseLinear
