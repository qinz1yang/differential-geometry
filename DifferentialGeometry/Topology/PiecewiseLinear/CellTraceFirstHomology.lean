/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import DifferentialGeometry.Topology.Simplex.NormedBall
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.MetricSpace.Thickening

open Set Metric DifferentialGeometry.Simplex

universe u

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Cell

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.exists_homeomorph {d : ℕ} {S B : Set M} (h : IsPLCellOn d S B) :
    ∃ Φ : Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)) ≃ₜ S,
      ∀ x, ((Φ x : S) : M) ∈ B ↔ (x : Fin (d + 1) → ℝ) ∈ stdSimplexBoundary d := by
  obtain ⟨P, r, u, hr, hu, rfl, rfl⟩ := h
  have hmaps : ∀ x : Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)), u (r x) ∈ u '' P :=
    fun x => ⟨r x, hr.bijOn.mapsTo x.2, rfl⟩
  let f : Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)) → u '' P := fun x => ⟨u (r x), hmaps x⟩
  have hcont : Continuous f :=
    ((hu.continuousOn.comp hr.isPiecewiseAffineOn.continuousOn hr.bijOn.mapsTo).comp_continuous
      continuous_subtype_val Subtype.property).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (hr.bijOn.injOn x.2 y.2
      (hu.injOn (hr.bijOn.mapsTo x.2) (hr.bijOn.mapsTo y.2) (congrArg Subtype.val hxy)))
  have hsurj : Function.Surjective f := by
    rintro ⟨_, p, hp, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hr.bijOn.surjOn hp
    exact ⟨⟨x, hx⟩, rfl⟩
  have : CompactSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) :=
    isCompact_iff_compactSpace.mp (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin (d + 1)))
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) hcont,
    fun x => ?_⟩
  change u (r x) ∈ u '' (r '' stdSimplexBoundary d) ↔ _
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
    have hxy : (x : Fin (d + 1) → ℝ) = y := (hr.bijOn.injOn hy.1 x.2
      (hu.injOn (hr.bijOn.mapsTo hy.1) (hr.bijOn.mapsTo x.2) hyx)).symm
    rw [hxy]
    exact hy
  · intro hx
    exact ⟨r x, ⟨x, hx, rfl⟩, rfl⟩

end Cell

section Homology

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.subsingleton_integralSingularHomology_one {d : ℕ} {S B : Set M}
    (h : IsPLCellOn d S B) : Subsingleton (integralSingularHomology 1 S) := by
  obtain ⟨Φ, -⟩ := h.exists_homeomorph
  have : ContractibleSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) :=
    (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin (d + 1))).contractibleSpace
      ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin (d + 1))⟩
  have : ContractibleSpace S := Φ.symm.contractibleSpace
  exact integralSingularHomology_subsingleton_of_contractible 1 one_ne_zero S

theorem IsPLCellOn.subsingleton_integralSingularHomology_one_boundary {S B : Set M}
    (h : IsPLCellOn 3 S B) : Subsingleton (integralSingularHomology 1 B) := by
  obtain ⟨Φ, hΦ⟩ := h.exists_homeomorph
  have hBS : B ⊆ S := h.boundary_subset
  let Ψ₁ : boundary (Fin 4) ≃ₜ {s : S // (s : M) ∈ B} :=
    Φ.subtype fun x => ⟨fun hx => (hΦ x).mpr ⟨x.2, hx⟩, fun hx => ((hΦ x).mp hx).2⟩
  let Ψ₂ : {s : S // (s : M) ∈ B} ≃ₜ B :=
    { toFun := fun s => ⟨s.1.1, s.2⟩
      invFun := fun b => ⟨⟨b.1, hBS b.2⟩, b.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (ULift.{u} (Fin 3))) = 2 + 1 := by simp
  let eU : (Fin 3 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (ULift.{u} (Fin 3)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let Ψ : B ≃ₜ sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin 3))) 1 :=
    (Ψ₂.symm.trans Ψ₁.symm).trans (stdSimplexNormedBoundarySphereHomeomorph eU)
  have := integralSphereHomology_subsingleton 2 1 (EuclideanSpace ℝ (ULift.{u} (Fin 3))) hdim
    one_ne_zero (by norm_num)
  exact (integralSingularHomologyHomotopyEquiv 1 Ψ.toHomotopyEquiv).toEquiv.subsingleton

end Homology

theorem dist_radialDeformation_le (p : punctured (Fin 4)) (t : unitInterval)
    (hp : minimumCoordinate p.val ≤ 1 / 8) :
    dist (radialDeformation (t, p)).val p.val ≤ 6 * minimumCoordinate p.val := by
  have hm0 : 0 ≤ minimumCoordinate p.val := minimumCoordinate_nonneg p.val
  rw [Subtype.dist_eq, dist_pi_le_iff (by positivity)]
  intro i
  have hxi0 : 0 ≤ p.val.val i := p.val.property.1 i
  have hxi1 : p.val.val i ≤ 1 :=
    (Finset.single_le_sum (fun j _ => p.val.property.1 j) (Finset.mem_univ i)).trans_eq
      p.val.property.2
  change dist ((1 - (t : ℝ)) * p.val.val i + (t : ℝ) * ((p.val.val i - minimumCoordinate p.val) /
    (1 - (Fintype.card (Fin 4) : ℝ) * minimumCoordinate p.val))) (p.val.val i) ≤ _
  simp only [Fintype.card_fin, Nat.cast_ofNat, Real.dist_eq]
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hD : (1 : ℝ) / 2 ≤ 1 - 4 * minimumCoordinate p.val := by linarith
  have hDne : 1 - 4 * minimumCoordinate p.val ≠ 0 := by linarith
  have hI : (1 - 4 * minimumCoordinate p.val) * (1 - 4 * minimumCoordinate p.val)⁻¹ = 1 :=
    mul_inv_cancel₀ hDne
  have key : (1 - (t : ℝ)) * p.val.val i + t * ((p.val.val i - minimumCoordinate p.val) /
      (1 - 4 * minimumCoordinate p.val)) - p.val.val i =
        t * minimumCoordinate p.val * (4 * p.val.val i - 1) /
          (1 - 4 * minimumCoordinate p.val) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination ((t : ℝ) * p.val.val i) * hI
  rw [key, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - 4 * minimumCoordinate p.val),
    div_le_iff₀ (by linarith), abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg hm0]
  have h4 : |4 * p.val.val i - 1| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod : (t : ℝ) * minimumCoordinate p.val * |4 * p.val.val i - 1| ≤
      1 * minimumCoordinate p.val * 3 :=
    mul_le_mul (mul_le_mul_of_nonneg_right ht1 hm0) h4 (abs_nonneg _) (by positivity)
  nlinarith

section Trace

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.carriesFirstHomologyOnto_inter_interior {C Bd C' T R : Set M}
    (hC : IsPLCellOn 3 C Bd) (hC' : IsCompact C')
    (hC'1 : Subsingleton (integralSingularHomology 1 C')) (hRC' : R ⊆ C')
    (hRC : R ⊆ interior C) (hCC' : C ∩ C' ⊆ interior T) (hR : CarriesFirstHomologyOnto R T) :
    CarriesFirstHomologyOnto (Bd ∩ interior T) T := by
  obtain ⟨Φ, hΦ⟩ := hC.exists_homeomorph
  have : CompactSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) :=
    isCompact_iff_compactSpace.mp (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 4))
  have he : Continuous fun x : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) => ((Φ x : C) : M) :=
    continuous_subtype_val.comp Φ.continuous
  have hK : IsCompact (C ∩ C') := hC.isCompact.inter_right hC'.isClosed
  obtain ⟨ε, hε, hKε⟩ := hK.exists_thickening_subset_open isOpen_interior hCC'
  obtain ⟨η, hη, hunif⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous he) ε hε
  obtain ⟨δ, hδ, hδ8, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ 6 * δ < η :=
    ⟨min (1 / 8) (η / 8), by positivity, min_le_left _ _, by
      have := min_le_right (1 / 8 : ℝ) (η / 8)
      linarith⟩
  obtain ⟨Cm, hCmdef⟩ : ∃ Cm : Set M, Cm = (fun x : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) => ((Φ x : C) : M)) ''
      {x | δ ≤ minimumCoordinate x} := ⟨_, rfl⟩
  have hCmc : IsCompact Cm := by
    rw [hCmdef]
    exact (isClosed_le continuous_const continuous_minimumCoordinate).isCompact.image he
  have hCmC : Cm ⊆ interior C := by
    rw [hCmdef, ← hC.sdiff_boundary_eq_interior]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(Φ x).2, fun hB => ?_⟩
    obtain ⟨-, i, hi⟩ := (hΦ x).mp hB
    have hle := minimumCoordinate_le x i
    change minimumCoordinate x ≤ (x : Fin 4 → ℝ) i at hle
    rw [hi] at hle
    change δ ≤ minimumCoordinate x at hx
    linarith
  obtain ⟨A, hAdef⟩ : ∃ A : Set M, A = interior C ∩ (C' \ interior T)ᶜ := ⟨_, rfl⟩
  have hA : IsOpen A := by
    rw [hAdef]
    exact isOpen_interior.inter (hC'.isClosed.sdiff isOpen_interior).isOpen_compl
  have hB : IsOpen Cmᶜ := hCmc.isClosed.isOpen_compl
  have hint : ∀ {z}, z ∈ C → z ∈ C' → z ∉ C' \ interior T :=
    fun hzC hzC' hz => hz.2 (hCC' ⟨hzC, hzC'⟩)
  have hZ : C' ⊆ A ∪ Cmᶜ := by
    intro z hz
    by_cases hzm : z ∈ Cm
    · left
      rw [hAdef]
      exact ⟨hCmC hzm, hint (interior_subset (hCmC hzm)) hz⟩
    · exact Or.inr hzm
  have hPZA : R ⊆ C' ∩ A := by
    intro z hz
    refine ⟨hRC' hz, ?_⟩
    rw [hAdef]
    exact ⟨hRC hz, hint (interior_subset (hRC hz)) (hRC' hz)⟩
  have hZAT : C' ∩ A ⊆ T := by
    rintro z ⟨hz, hzA⟩
    rw [hAdef] at hzA
    by_contra hzT
    exact hzA.2 ⟨hz, fun hi => hzT (interior_subset hi)⟩
  have h1 := hR.of_mayerVietoris hA hB hZ hC'1 hPZA hZAT
  obtain ⟨S, hSdef⟩ : ∃ S : Set M, S = C' ∩ A ∩ Cmᶜ := ⟨_, rfl⟩
  rw [← hSdef] at h1
  have hSmem : ∀ z ∈ S, z ∈ C' ∩ A ∩ Cmᶜ := by
    intro z hz
    rw [hSdef] at hz
    exact hz
  have hSC : ∀ w ∈ S, w ∈ C := by
    intro w hw
    have hw' := (hSmem w hw).1.2
    rw [hAdef] at hw'
    exact interior_subset hw'.1
  have hSK : ∀ w ∈ S, w ∈ C ∩ C' := fun w hw => ⟨hSC w hw, (hSmem w hw).1.1⟩
  let x : S → Convexity.StdSimplex.coordinateSet ℝ (Fin 4) := fun w => Φ.symm ⟨w.1, hSC w.1 w.2⟩
  have hx : Continuous x := Φ.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hex : ∀ w : S, ((Φ (x w) : C) : M) = w := by
    intro w
    change ((Φ (Φ.symm ⟨w.1, hSC w.1 w.2⟩) : C) : M) = w
    rw [Φ.apply_symm_apply]
  have hxm : ∀ w : S, minimumCoordinate (x w) < δ := by
    intro w
    by_contra hle
    refine (hSmem w w.2).2 ?_
    rw [hCmdef]
    exact ⟨x w, le_of_not_gt hle, hex w⟩
  have hxp : ∀ w : S, x w ∈ punctured (Fin 4) := by
    intro w hbar
    have hlt := hxm w
    rw [hbar] at hlt
    obtain ⟨i, hi⟩ := exists_minimumCoordinate (Convexity.StdSimplex.coordinateBarycenter : Convexity.StdSimplex.coordinateSet ℝ (Fin 4))
    rw [hi, Convexity.StdSimplex.coordinateBarycenter_apply] at hlt
    norm_num at hlt
    linarith
  let p : S → punctured (Fin 4) := fun w => ⟨x w, hxp w⟩
  have hp : Continuous p := hx.subtype_mk _
  let F : unitInterval × S → M := fun q => ((Φ (radialDeformation (q.1, p q.2)).val : C) : M)
  have hF : Continuous F :=
    he.comp (continuous_subtype_val.comp (radialDeformation.continuous.comp
      (continuous_fst.prodMk (hp.comp continuous_snd))))
  have hFK : ∀ q, F q ∈ thickening ε (C ∩ C') := by
    intro q
    refine mem_thickening_iff.mpr ⟨q.2, hSK q.2 q.2.2, ?_⟩
    have hdist : dist (radialDeformation (q.1, p q.2)).val (x q.2) < η :=
      (dist_radialDeformation_le (p q.2) q.1 ((hxm q.2).le.trans hδ8)).trans_lt
        (by linarith [hxm q.2])
    have hlt := hunif hdist
    rw [hex q.2] at hlt
    exact hlt
  have hFT : ∀ q, F q ∈ T := fun q => interior_subset (hKε (hFK q))
  have hF1 : ∀ w : S, F (1, w) ∈ Bd := by
    intro w
    have h1w : (radialDeformation (1, p w)).val = (radialRetraction (p w)).val :=
      congrArg Subtype.val (radialDeformation.apply_one (p w))
    change ((Φ (radialDeformation (1, p w)).val : C) : M) ∈ Bd
    rw [h1w]
    exact (hΦ _).mpr ⟨(radialRetraction (p w)).val.2, (radialRetraction (p w)).2⟩
  have hF0 : ∀ w : S, F (0, w) = w := by
    intro w
    have h0w : (radialDeformation (0, p w)).val = x w :=
      congrArg Subtype.val (radialDeformation.apply_zero (p w))
    change ((Φ (radialDeformation (0, p w)).val : C) : M) = w
    rw [h0w]
    exact hex w
  have hS'T : Bd ∩ thickening ε (C ∩ C') ⊆ T := fun z hz => interior_subset (hKε hz.2)
  let g : C(S, ↥(Bd ∩ thickening ε (C ∩ C'))) :=
    ⟨fun w => ⟨F (1, w), hF1 w, hFK (1, w)⟩,
      (hF.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  have hg : ContinuousMap.Homotopic (⟨inclusion h1.1, continuous_inclusion h1.1⟩ : C(S, T))
      ((⟨inclusion hS'T, continuous_inclusion hS'T⟩ : C(↥(Bd ∩ thickening ε (C ∩ C')), T)).comp
        g) :=
    ⟨{ toFun := fun q => ⟨F q, hFT q⟩
       continuous_toFun := hF.subtype_mk _
       map_zero_left := fun w => Subtype.ext (hF0 w)
       map_one_left := fun _ => rfl }⟩
  exact (h1.of_homotopic hS'T g hg).mono
    (fun z hz => ⟨hz.1, hKε hz.2⟩) (fun z hz => interior_subset hz.2)

end Trace

section Frontier

variable {Y : Type u} [TopologicalSpace Y]

theorem CarriesFirstHomologyOnto.inter_frontier_of_homotopic {S T N : Set Y}
    (h : CarriesFirstHomologyOnto (S ∩ interior T) T) (hS : IsClosed S) (hT : IsClosed T)
    (hS1 : Subsingleton (integralSingularHomology 1 S)) (hN : IsOpen N)
    (hSN : S ∩ frontier T ⊆ N) (g : C(↥(S ∩ interior T ∩ N), ↥(S ∩ frontier T)))
    (hg : ContinuousMap.Homotopic
      (⟨inclusion fun _ hx => interior_subset hx.1.2, continuous_inclusion _⟩ :
        C(↥(S ∩ interior T ∩ N), T))
      ((⟨inclusion fun _ hx => hT.frontier_subset hx.2, continuous_inclusion _⟩ :
        C(↥(S ∩ frontier T), T)).comp g)) :
    CarriesFirstHomologyOnto (S ∩ frontier T) T := by
  have hB : IsOpen ((T ∩ S) \ N)ᶜ := ((hT.inter hS).sdiff hN).isOpen_compl
  have hZ : S ⊆ interior T ∪ ((T ∩ S) \ N)ᶜ := by
    intro z hz
    by_cases hzi : z ∈ interior T
    · exact Or.inl hzi
    · right
      rintro ⟨⟨hzT, -⟩, hzN⟩
      refine hzN (hSN ⟨hz, ?_⟩)
      rw [hT.frontier_eq]
      exact ⟨hzT, hzi⟩
  have h1 := h.of_mayerVietoris isOpen_interior hB hZ hS1 subset_rfl
    (fun z hz => interior_subset hz.2)
  have heq : S ∩ interior T ∩ ((T ∩ S) \ N)ᶜ = S ∩ interior T ∩ N := by
    ext z
    constructor
    · rintro ⟨⟨hzS, hzT⟩, hzN⟩
      refine ⟨⟨hzS, hzT⟩, ?_⟩
      by_contra hn
      exact hzN ⟨⟨interior_subset hzT, hzS⟩, hn⟩
    · rintro ⟨⟨hzS, hzT⟩, hzN⟩
      exact ⟨⟨hzS, hzT⟩, fun hc => hc.2 hzN⟩
  rw [heq] at h1
  exact h1.of_homotopic (fun _ hx => hT.frontier_subset hx.2) g hg

end Frontier

end DifferentialGeometry.Topology.PiecewiseLinear
