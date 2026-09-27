/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskLocalChartsInterior
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskLocalChartsOpen
import DifferentialGeometry.Topology.PiecewiseLinear.ConicalHalfArcPair
import DifferentialGeometry.Topology.PiecewiseLinear.ConicalCrosscutPair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
theorem segment_subset_coneSet_of_mem {S : Set E} {z : E} (p : E) (hz : z ∈ S) :
    segment ℝ p z ⊆ coneSet p S := by
  have h := coneSet_mono p (singleton_subset_iff.mpr hz)
  simpa only [coneSet_eq_iUnion_segment (singleton_nonempty z), biUnion_singleton] using h

theorem IsBridgeDisk.exists_local_equivalence_at_endpoints
    {C A B : Set E} {a b x : E} (h : IsBridgeDisk C A B a b)
    {C' A' B' : Set F} {a' b' y : F} (h' : IsBridgeDisk C' A' B' a' b')
    (hdim : Module.finrank ℝ E = 3) (hdim' : Module.finrank ℝ F = 3)
    (hC : IsPLBall 3 C) (hC' : IsPLBall 3 C')
    (hx : x ∈ ({a, b} : Set E)) (hy : y ∈ ({a', b'} : Set F)) :
    ∃ (U : Set E) (V : Set F) (f : E → F),
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ IsPLHomeomorphOn f U V ∧ f x = y ∧
      f '' (U ∩ C) = V ∩ C' ∧ f '' (U ∩ frontier C) = V ∩ frontier C' ∧
      f '' (U ∩ B) = V ∩ B' ∧ f '' (U ∩ (B ∩ frontier C)) = V ∩ (B' ∩ frontier C') ∧
      f '' (U ∩ A) = V ∩ A' := by
  obtain ⟨S, D, J, r, η, hSfin, hScone, hS, hSnhds, hDS, hr, hη, hJD, hmeet,
    hCgerm, hFgerm, hBgerm, hβgerm, hAgerm⟩ := h.exists_conical_endpoint_model hdim hC hx
  obtain ⟨S', D', J', r', η', hSfin', hScone', hS', hSnhds', hDS', hr', hη', hJD', hmeet',
    hCgerm', hFgerm', hBgerm', hβgerm', hAgerm'⟩ :=
      h'.exists_conical_endpoint_model hdim' hC' hy
  let _ : Finite S.faces := hSfin.to_subtype
  let _ : Finite S'.faces := hSfin'.to_subtype
  obtain ⟨f, hf, hfx, hfC, hfF, hfB, hfβ, hfA⟩ :=
    exists_isPLHomeomorphOn_cone_disk_arc_pair_of_boundary_singleton hScone hScone' hS hS'
      hDS hDS' hr hη hJD hmeet hr' hη' hJD' hmeet'
  let P : Fin 5 → Set E := ![coneSet x D, coneSet x (r '' stdSimplexBoundary 2),
    coneSet x J, segment ℝ x (η 0), segment ℝ x (η 1)]
  let Q : Fin 5 → Set F := ![coneSet y D', coneSet y (r' '' stdSimplexBoundary 2),
    coneSet y J', segment ℝ y (η' 0), segment ℝ y (η' 1)]
  let Z : Fin 5 → Set E := ![C, frontier C, B, B ∩ frontier C, A]
  let Z' : Fin 5 → Set F := ![C', frontier C', B', B' ∩ frontier C', A']
  have hPsub : ∀ i, P i ⊆ coneSet x S.space := by
    intro i
    fin_cases i <;> dsimp [P]
    · exact coneSet_mono x hDS
    · exact coneSet_mono x (((image_mono (fun _ hz => hz.1)).trans hr.image_eq.subset).trans hDS)
    · exact coneSet_mono x (hJD.trans hDS)
    · exact segment_subset_coneSet_of_mem x (hDS (hJD (hη.bijOn.mapsTo (by norm_num))))
    · exact segment_subset_coneSet_of_mem x (hDS (hJD (hη.bijOn.mapsTo (by norm_num))))
  have hmap : ∀ i, f '' P i = Q i := by
    intro i
    fin_cases i
    · exact hfC
    · exact hfF
    · exact hfB
    · exact hfβ
    · exact hfA
  have hsource : ∀ i, ∀ᶠ z in 𝓝 x, z ∈ P i ↔ z ∈ Z i := by
    intro i
    fin_cases i
    · exact hCgerm
    · exact hFgerm
    · exact hBgerm
    · exact hβgerm
    · exact hAgerm
  have htarget : ∀ i, ∀ᶠ z in 𝓝 y, z ∈ Q i ↔ z ∈ Z' i := by
    intro i
    fin_cases i
    · exact hCgerm'
    · exact hFgerm'
    · exact hBgerm'
    · exact hβgerm'
    · exact hAgerm'
  obtain ⟨U, V, hU, hV, hxU, hyV, _, _, hfUV, hflags⟩ :=
    hf.exists_open_restriction_of_finite_germs (hdim.trans hdim'.symm) hSnhds hfx
      hPsub hmap hsource htarget
  exact ⟨U, V, f, hU, hV, hxU, hyV, hfUV, hfx,
    hflags 0, hflags 1, hflags 2, hflags 3, hflags 4⟩

theorem IsBridgeDisk.exists_local_equivalence_at_frontier
    {C A B : Set E} {a b x : E} (h : IsBridgeDisk C A B a b)
    {C' A' B' : Set F} {a' b' y : F} (h' : IsBridgeDisk C' A' B' a' b')
    (hdim : Module.finrank ℝ E = 3) (hdim' : Module.finrank ℝ F = 3)
    (hC : IsPLBall 3 C) (hC' : IsPLBall 3 C')
    (hxβ : x ∈ B ∩ frontier C) (hyβ : y ∈ B' ∩ frontier C')
    (hx : x ∉ ({a, b} : Set E)) (hy : y ∉ ({a', b'} : Set F)) :
    ∃ (U : Set E) (V : Set F) (f : E → F),
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ IsPLHomeomorphOn f U V ∧ f x = y ∧
      f '' (U ∩ C) = V ∩ C' ∧ f '' (U ∩ frontier C) = V ∩ frontier C' ∧
      f '' (U ∩ B) = V ∩ B' ∧ f '' (U ∩ (B ∩ frontier C)) = V ∩ (B' ∩ frontier C') ∧
      f '' (U ∩ A) = V ∩ A' := by
  obtain ⟨S, D, J, r, η, hSfin, hScone, hS, hSnhds, hDS, hr, hη, hJD, hmeet,
    hCgerm, hFgerm, hBgerm, hβgerm, hAgerm⟩ := h.exists_conical_frontier_model hdim hC hxβ hx
  obtain ⟨S', D', J', r', η', hSfin', hScone', hS', hSnhds', hDS', hr', hη', hJD', hmeet',
    hCgerm', hFgerm', hBgerm', hβgerm', hAgerm'⟩ :=
      h'.exists_conical_frontier_model hdim' hC' hyβ hy
  let _ : Finite S.faces := hSfin.to_subtype
  let _ : Finite S'.faces := hSfin'.to_subtype
  obtain ⟨f, hf, hfx, hfC, hfF, hfB, hfβ₀, hfβ₁⟩ :=
    exists_isPLHomeomorphOn_cone_disk_crosscut_pair hScone hScone' hS hS'
      hDS hDS' hr hη hJD hmeet hr' hη' hJD' hmeet'
  let P : Fin 5 → Set E := ![coneSet x D, coneSet x (r '' stdSimplexBoundary 2),
    coneSet x J, segment ℝ x (η 0) ∪ segment ℝ x (η 1), ∅]
  let Q : Fin 5 → Set F := ![coneSet y D', coneSet y (r' '' stdSimplexBoundary 2),
    coneSet y J', segment ℝ y (η' 0) ∪ segment ℝ y (η' 1), ∅]
  let Z : Fin 5 → Set E := ![C, frontier C, B, B ∩ frontier C, A]
  let Z' : Fin 5 → Set F := ![C', frontier C', B', B' ∩ frontier C', A']
  have hPsub : ∀ i, P i ⊆ coneSet x S.space := by
    intro i
    fin_cases i <;> dsimp [P]
    · exact coneSet_mono x hDS
    · exact coneSet_mono x (((image_mono (fun _ hz => hz.1)).trans hr.image_eq.subset).trans hDS)
    · exact coneSet_mono x (hJD.trans hDS)
    · exact union_subset
        (segment_subset_coneSet_of_mem x (hDS (hJD (hη.bijOn.mapsTo (by norm_num)))))
        (segment_subset_coneSet_of_mem x (hDS (hJD (hη.bijOn.mapsTo (by norm_num)))))
    · exact empty_subset _
  have hmap : ∀ i, f '' P i = Q i := by
    intro i
    fin_cases i
    · exact hfC
    · exact hfF
    · exact hfB
    · exact (image_union _ _ _).trans (congrArg₂ (· ∪ ·) hfβ₀ hfβ₁)
    · exact image_empty f
  have hsource : ∀ i, ∀ᶠ z in 𝓝 x, z ∈ P i ↔ z ∈ Z i := by
    intro i
    fin_cases i
    · exact hCgerm
    · exact hFgerm
    · exact hBgerm
    · exact hβgerm
    · filter_upwards [hAgerm] with z hz
      exact ⟨fun hz => hz.elim, fun hA => (hz hA).elim⟩
  have htarget : ∀ i, ∀ᶠ z in 𝓝 y, z ∈ Q i ↔ z ∈ Z' i := by
    intro i
    fin_cases i
    · exact hCgerm'
    · exact hFgerm'
    · exact hBgerm'
    · exact hβgerm'
    · filter_upwards [hAgerm'] with z hz
      exact ⟨fun hz => hz.elim, fun hA => (hz hA).elim⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, _, _, hfUV, hflags⟩ :=
    hf.exists_open_restriction_of_finite_germs (hdim.trans hdim'.symm) hSnhds hfx
      hPsub hmap hsource htarget
  exact ⟨U, V, f, hU, hV, hxU, hyV, hfUV, hfx,
    hflags 0, hflags 1, hflags 2, hflags 3, hflags 4⟩

end DifferentialGeometry.Topology.PiecewiseLinear
