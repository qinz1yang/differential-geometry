/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryHomology

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private abbrev SurfaceFace (K : Geometry.SimplicialComplex ℝ E) :=
  {s : Finset E // s ∈ K.faces ∧ s.card = 3}

private abbrev SurfaceEdge (K : Geometry.SimplicialComplex ℝ E) :=
  {s : Finset E // s ∈ K.faces ∧ s.card = 2}

open Classical in
private noncomputable def surfaceChainCoeff
    (K : Geometry.SimplicialComplex ℝ E) (c : SurfaceFace K → ℚ) : Finset E → ℚ :=
  fun s => if hs : s ∈ K.faces ∧ s.card = 3 then c ⟨s, hs⟩ else 0

private noncomputable def surfaceOrientationChain
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (o : CoherentOrientation 2 K) : SurfaceFace K → ℚ :=
  fun s => o.sign s.1

open Classical in
private theorem orderedNormalizedBoundary_surfaceOrientationChain
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (o : CoherentOrientation 2 K) :
    let _ := o.vertexOrder
    SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
      K.toPreAbstractSimplicialComplex 1 (surfaceOrientationChain K o) = 0 := by
  dsimp
  let _ := o.vertexOrder
  change SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
    K.toPreAbstractSimplicialComplex 1 (fun s => (o.sign s.1 : ℚ)) = 0
  ext t
  simp only [Pi.zero_apply]
  rw [orderedNormalizedBoundary_intCast_apply]
  exact_mod_cast o.coherent t.1 t.2.1 t.2.2 (by
    rw [hK.card_faceCofaces_eq_two K t.2.1 t.2.2]
    omega)

open Classical in
private theorem surfaceOrientationChain_ne_zero
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 2 K) : surfaceOrientationChain K o ≠ 0 := by
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨s, hs, -⟩ := K.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htcard⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq hs
  intro hzero
  have hz := congrFun hzero ⟨t, ht, by simpa using htcard⟩
  rcases o.sign_top t ht (by simpa using htcard) with h | h <;>
    simp [surfaceOrientationChain, h] at hz

open Classical in
private theorem surfaceCycle_weighted_eq_of_dualGraph_adj
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (o : CoherentOrientation 2 K)
    (c : SurfaceFace K → ℚ)
    (hcycle : let _ := o.vertexOrder
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 1 c = 0)
    {s t : SurfaceFace K} (hadj : (dualGraph 2 K).Adj s t) :
    c s * (o.sign s.1 : ℚ) = c t * (o.sign t.1 : ℚ) := by
  obtain ⟨hne, f, hf, hfcard, hfs, hft⟩ := hadj
  have hst : s.1 ≠ t.1 := fun h => hne (Subtype.ext h)
  have hsco : s.1 ∈ faceCofaces K f 3 :=
    (mem_faceCofaces K).mpr ⟨s.2.1, s.2.2, hfs⟩
  have htco : t.1 ∈ faceCofaces K f 3 :=
    (mem_faceCofaces K).mpr ⟨t.2.1, t.2.2, hft⟩
  have hsub : ({s.1, t.1} : Finset (Finset E)) ⊆ faceCofaces K f 3 := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hsco, htco⟩
  have hpair : faceCofaces K f 3 = {s.1, t.1} := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hK.card_faceCofaces_eq_two K hf hfcard, Finset.card_pair hst]
  let f' : SurfaceEdge K := ⟨f, hf, hfcard⟩
  let _ := o.vertexOrder
  have hzero := congrFun hcycle f'
  simp only [Pi.zero_apply] at hzero
  have hc : (fun u => surfaceChainCoeff K c u.1) = c := by
    funext u
    simp [surfaceChainCoeff, u.2.1, u.2.2]
  rw [← hc] at hzero
  have hformula :
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 1
            (fun u => surfaceChainCoeff K c u.1) f' =
        ∑ u ∈ faceCofaces K f'.1 3,
          surfaceChainCoeff K c u *
            (simplexBoundaryCoefficient o.vertexOrder u f'.1 : ℚ) :=
    orderedNormalizedBoundary_apply_eq_sum_faceCofaces o.vertexOrder K 1
      (surfaceChainCoeff K c) f'
  have hsum :
      (∑ u ∈ faceCofaces K f'.1 3,
          surfaceChainCoeff K c u *
            (simplexBoundaryCoefficient o.vertexOrder u f'.1 : ℚ)) = 0 :=
    hformula.symm.trans hzero
  change (∑ u ∈ faceCofaces K f 3,
      surfaceChainCoeff K c u *
        (simplexBoundaryCoefficient o.vertexOrder u f : ℚ)) = 0 at hsum
  rw [hpair] at hsum
  have hsum' : c s * (simplexBoundaryCoefficient o.vertexOrder s.1 f : ℚ) +
      c t * (simplexBoundaryCoefficient o.vertexOrder t.1 f : ℚ) = 0 := by
    simpa [surfaceChainCoeff, s.2.1, s.2.2, t.2.1, t.2.2, hst] using hsum
  have hcancel := o.pair_cancel_of_faceCofaces_eq hf hfcard hst hpair
  rcases o.sign_top s.1 s.2.1 s.2.2 with hs | hs <;>
    rcases o.sign_top t.1 t.2.1 t.2.2 with ht | ht <;>
      rcases simplexBoundaryCoefficient_eq_one_or_neg_one o.vertexOrder hfs (by omega)
        with hsi | hsi <;>
        rcases simplexBoundaryCoefficient_eq_one_or_neg_one o.vertexOrder hft (by omega)
          with hti | hti <;>
          norm_num [hs, ht, hsi, hti] at hcancel <;>
          norm_num [hs, ht, hsi, hti] at hsum' ⊢ <;>
          linarith

open Classical in
private theorem surfaceCycle_weighted_eq_of_dualGraph_reachable
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (o : CoherentOrientation 2 K)
    (c : SurfaceFace K → ℚ)
    (hcycle : let _ := o.vertexOrder
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 1 c = 0)
    {s t : SurfaceFace K} (hreach : (dualGraph 2 K).Reachable s t) :
    c s * (o.sign s.1 : ℚ) = c t * (o.sign t.1 : ℚ) := by
  obtain ⟨w⟩ := hreach
  induction w with
  | nil => rfl
  | cons h _ ih =>
      exact (surfaceCycle_weighted_eq_of_dualGraph_adj K hK o c hcycle h).trans ih

open Classical in
private theorem finrank_ker_surfaceBoundary_eq_one
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 2 K) :
    let _ := o.vertexOrder
    Module.finrank ℚ (LinearMap.ker
      (SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 1)) = 1 := by
  dsimp
  let _ := o.vertexOrder
  let _ : Finite (SurfaceFace K) := Finite.of_injective
    (fun s => (⟨s.1, s.2.1⟩ : K.faces))
    (fun _ _ h => Subtype.ext (congrArg (fun u : K.faces => u.1) h))
  let _ : FiniteDimensional ℚ (SurfaceFace K → ℚ) := by infer_instance
  let D := SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
    K.toPreAbstractSimplicialComplex 1
  let z : LinearMap.ker D :=
    ⟨surfaceOrientationChain K o,
      orderedNormalizedBoundary_surfaceOrientationChain K hK o⟩
  have hz : z ≠ 0 := by
    intro hz
    apply surfaceOrientationChain_ne_zero K hK hconn o
    exact congrArg Subtype.val hz
  have hpos : 0 < Module.finrank ℚ (LinearMap.ker D) :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℚ)).mpr ⟨z, hz⟩
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨s, hs, -⟩ := K.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htcard⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq hs
  let t₀ : SurfaceFace K := ⟨t, ht, by simpa using htcard⟩
  let ev : LinearMap.ker D →ₗ[ℚ] ℚ := {
    toFun := fun c => c.1 t₀
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }
  have hev : Function.Injective ev := by
    intro a b hab
    apply Subtype.ext
    funext u
    have hcycle : D (a.1 - b.1) = 0 := by
      rw [map_sub, a.2, b.2, sub_self]
    have hreach : (dualGraph 2 K).Reachable u t₀ :=
      hK.isCombinatorialManifoldWithBoundary.dualGraph_preconnected
        hconn.isPreconnected u t₀
    have heq := surfaceCycle_weighted_eq_of_dualGraph_reachable
      K hK o (a.1 - b.1) hcycle hreach
    have hbase : (a.1 - b.1) t₀ = 0 := by
      apply sub_eq_zero.mpr
      exact hab
    have hsign : (o.sign u.1 : ℚ) ≠ 0 := by
      rcases o.sign_top u.1 u.2.1 u.2.2 with h | h <;> simp [h]
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_right hsign
    calc
      (a.1 u - b.1 u) * (o.sign u.1 : ℚ) =
          (a.1 - b.1) u * (o.sign u.1 : ℚ) := by rfl
      _ = (a.1 - b.1) t₀ * (o.sign t₀.1 : ℚ) := heq
      _ = 0 := by rw [hbase, zero_mul]
  have hle := ev.finrank_le_finrank_of_injective hev
  have heq : Module.finrank ℚ (LinearMap.ker D) = 1 :=
    Nat.le_antisymm (by simpa using hle) hpos
  simpa [D] using heq

open Classical in
private theorem surfaceCycle_sq_eq_of_dualGraph_adj
    [FiniteDimensional ℝ E]
    (r : LinearOrder E)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (c : SurfaceFace K → ℚ)
    (hcycle : let _ := r
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 1 c = 0)
    {s t : SurfaceFace K} (hadj : (dualGraph 2 K).Adj s t) :
    c s ^ 2 = c t ^ 2 := by
  obtain ⟨hne, f, hf, hfcard, hfs, hft⟩ := hadj
  have hst : s.1 ≠ t.1 := fun h => hne (Subtype.ext h)
  have hsco : s.1 ∈ faceCofaces K f 3 :=
    (mem_faceCofaces K).mpr ⟨s.2.1, s.2.2, hfs⟩
  have htco : t.1 ∈ faceCofaces K f 3 :=
    (mem_faceCofaces K).mpr ⟨t.2.1, t.2.2, hft⟩
  have hsub : ({s.1, t.1} : Finset (Finset E)) ⊆ faceCofaces K f 3 := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hsco, htco⟩
  have hpair : faceCofaces K f 3 = {s.1, t.1} := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hK.card_faceCofaces_eq_two K hf hfcard, Finset.card_pair hst]
  let f' : SurfaceEdge K := ⟨f, hf, hfcard⟩
  let _ := r
  have hzero := congrFun hcycle f'
  simp only [Pi.zero_apply] at hzero
  have hc : (fun u => surfaceChainCoeff K c u.1) = c := by
    funext u
    simp [surfaceChainCoeff, u.2.1, u.2.2]
  rw [← hc] at hzero
  have hformula :
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 1
            (fun u => surfaceChainCoeff K c u.1) f' =
        ∑ u ∈ faceCofaces K f'.1 3,
          surfaceChainCoeff K c u *
            (simplexBoundaryCoefficient r u f'.1 : ℚ) :=
    orderedNormalizedBoundary_apply_eq_sum_faceCofaces r K 1
      (surfaceChainCoeff K c) f'
  have hsum :
      (∑ u ∈ faceCofaces K f'.1 3,
          surfaceChainCoeff K c u *
            (simplexBoundaryCoefficient r u f'.1 : ℚ)) = 0 :=
    hformula.symm.trans hzero
  change (∑ u ∈ faceCofaces K f 3,
      surfaceChainCoeff K c u *
        (simplexBoundaryCoefficient r u f : ℚ)) = 0 at hsum
  rw [hpair] at hsum
  have hsum' : c s * (simplexBoundaryCoefficient r s.1 f : ℚ) +
      c t * (simplexBoundaryCoefficient r t.1 f : ℚ) = 0 := by
    simpa [surfaceChainCoeff, s.2.1, s.2.2, t.2.1, t.2.2, hst] using hsum
  rcases simplexBoundaryCoefficient_eq_one_or_neg_one r hfs (by omega) with hs | hs
  · rcases simplexBoundaryCoefficient_eq_one_or_neg_one r hft (by omega) with ht | ht
    · have heq : c s = -c t := by
        norm_num [hs, ht] at hsum'
        linarith
      rw [heq]
      ring
    · have heq : c s = c t := by
        norm_num [hs, ht] at hsum'
        linarith
      rw [heq]
  · rcases simplexBoundaryCoefficient_eq_one_or_neg_one r hft (by omega) with ht | ht
    · have heq : c s = c t := by
        norm_num [hs, ht] at hsum'
        linarith
      rw [heq]
    · have heq : c s = -c t := by
        norm_num [hs, ht] at hsum'
        linarith
      rw [heq]
      ring

open Classical in
private theorem surfaceCycle_sq_eq_of_dualGraph_reachable
    [FiniteDimensional ℝ E]
    (r : LinearOrder E)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (c : SurfaceFace K → ℚ)
    (hcycle : let _ := r
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 1 c = 0)
    {s t : SurfaceFace K} (hreach : (dualGraph 2 K).Reachable s t) :
    c s ^ 2 = c t ^ 2 := by
  obtain ⟨w⟩ := hreach
  induction w with
  | nil => rfl
  | cons h _ ih =>
      exact (surfaceCycle_sq_eq_of_dualGraph_adj r K hK c hcycle h).trans ih

open Classical in
private theorem isOrientable_of_surfaceCycle_ne_zero
    [FiniteDimensional ℝ E]
    (r : LinearOrder E)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (c : SurfaceFace K → ℚ)
    (hcycle : let _ := r
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 1 c = 0)
    (hc : c ≠ 0) : IsOrientable 2 K := by
  have hexists : ∃ s, c s ≠ 0 := by
    by_contra h
    apply hc
    funext s
    exact not_ne_iff.mp (fun hs => h ⟨s, hs⟩)
  obtain ⟨s₀, hs₀⟩ := hexists
  let a := c s₀
  let sign : Finset E → ℤ := fun s =>
    if hs : s ∈ K.faces ∧ s.card = 3 then
      if c ⟨s, hs⟩ = a then 1 else -1
    else 0
  have hdual : (dualGraph 2 K).Preconnected :=
    hK.isCombinatorialManifoldWithBoundary.dualGraph_preconnected hconn.isPreconnected
  have hchoice : ∀ s : SurfaceFace K, c s = a ∨ c s = -a := by
    intro s
    exact eq_or_eq_neg_of_sq_eq_sq (c s) a
      (surfaceCycle_sq_eq_of_dualGraph_reachable r K hK c hcycle (hdual s s₀))
  have hchain : c = a • fun s : SurfaceFace K => (sign s.1 : ℚ) := by
    funext s
    rcases hchoice s with h | h
    · simp [sign, s.2.1, s.2.2, h]
    · simp [sign, s.2.1, s.2.2, h]
  refine ⟨{
    vertexOrder := r
    sign := sign
    sign_top := ?_
    coherent := ?_
  }⟩
  · intro s hs hscard
    by_cases hsa : c ⟨s, ⟨hs, hscard⟩⟩ = a
    · exact Or.inl (by simp [sign, hs, hscard, hsa])
    · exact Or.inr (by simp [sign, hs, hscard, hsa])
  · intro t ht htcard _
    let _ := r
    let D := SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
      K.toPreAbstractSimplicialComplex 1
    let d : SurfaceFace K → ℚ := fun s => (sign s.1 : ℚ)
    have hboundary : D d = 0 := by
      have hscaled : a • D d = 0 := by
        rw [← map_smul, ← hchain]
        exact hcycle
      exact (smul_eq_zero.mp hscaled).resolve_left hs₀
    let t' : SurfaceEdge K := ⟨t, ht, htcard⟩
    have hvalue := congrFun hboundary t'
    simp only [Pi.zero_apply] at hvalue
    have hcast := orderedNormalizedBoundary_intCast_apply (k := ℚ) r K 1 sign t'
    have : (orientedBoundary r K 2 sign t : ℚ) = 0 := by
      change SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 1
          (fun s => (sign s.1 : ℚ)) t' = 0 at hvalue
      exact hcast.symm.trans hvalue
    exact_mod_cast this

open Classical in
private theorem finrank_ker_surfaceBoundary_eq_zero_of_not_isOrientable
    [FiniteDimensional ℝ E]
    (r : LinearOrder E)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : ¬ IsOrientable 2 K) :
    let _ := r
    Module.finrank ℚ (LinearMap.ker
      (SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 1)) = 0 := by
  dsimp
  let _ := r
  let D := SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
    K.toPreAbstractSimplicialComplex 1
  let _ : Subsingleton (LinearMap.ker D) := ⟨by
    intro x y
    apply Subtype.ext
    apply sub_eq_zero.mp
    by_contra hne
    have hcycle : D (x.1 - y.1) = 0 := by
      rw [map_sub, x.2, y.2, sub_self]
    exact ho (isOrientable_of_surfaceCycle_ne_zero r K hK hconn (x.1 - y.1) hcycle hne)⟩
  have heq : Module.finrank ℚ (LinearMap.ker D) = 0 :=
    Module.finrank_zero_of_subsingleton
  simpa [D] using heq

open Classical in
private theorem bettiNumber_two_eq_finrank_ker_surfaceBoundary
    (r : LinearOrder E)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hd : ∀ s ∈ K.faces, s.card ≤ 3) :
    let _ := r
    Homology.bettiNumber ℚ (TopCat.of K.space) 2 =
      Module.finrank ℚ (LinearMap.ker
        (SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 1)) := by
  dsimp
  let _ := r
  let X := SimplicialComplex.orderedSimplicialSet K.toPreAbstractSimplicialComplex
  let R := ModuleCat.of ℚ ℚ
  let C := X.normalizedChainComplex R
  let e₁ := SimplicialComplex.orderedNormalizedChainEquiv (k := ℚ)
    K.toPreAbstractSimplicialComplex 1
  let e₂ := SimplicialComplex.orderedNormalizedChainEquiv (k := ℚ)
    K.toPreAbstractSimplicialComplex 2
  let D := SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
    K.toPreAbstractSimplicialComplex 1
  let eKer : LinearMap.ker (C.d 2 1).hom ≃ₗ[ℚ] LinearMap.ker D := {
    toFun := fun z => ⟨e₂ z.1, by
      change e₁ ((C.d 2 1).hom (e₂.symm (e₂ z.1))) = 0
      rw [e₂.symm_apply_apply, z.2, map_zero]⟩
    invFun := fun z => ⟨e₂.symm z.1, by
      apply e₁.injective
      change e₁ ((C.d 2 1).hom (e₂.symm z.1)) = e₁ 0
      simpa [D, SimplicialComplex.orderedNormalizedBoundary, X, C, e₁, e₂] using z.2⟩
    left_inv := fun z => by
      apply Subtype.ext
      exact e₂.symm_apply_apply z.1
    right_inv := fun z => by
      apply Subtype.ext
      exact e₂.apply_symm_apply z.1
    map_add' := fun _ _ => by
      apply Subtype.ext
      exact map_add e₂ _ _
    map_smul' := fun _ _ => by
      apply Subtype.ext
      exact map_smul e₂ _ _
  }
  let _ : FiniteDimensional ℚ (C.X 2) :=
    DifferentialGeometry.SSet.finiteDimensional_normalizedChainComplex_X X R 2
  let _ : FiniteDimensional ℚ (C.sc' 3 2 1).X₂ := by
    change FiniteDimensional ℚ (C.X 2)
    infer_instance
  let _ : X.HasDimensionLT 3 :=
    SimplicialComplex.orderedSimplicialSet_hasDimensionLT
      K.toPreAbstractSimplicialComplex 3 hd
  let _ : Subsingleton (C.X 3) := ModuleCat.subsingleton_of_isZero
    (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R 3 3)
  have hd₃ : (C.d 3 2).hom = 0 := by
    ext x
    rw [show x = 0 from Subsingleton.elim _ _, map_zero]
    rfl
  have hker := DifferentialGeometry.ShortComplex.finrank_ker_eq_homology_add_range
    (C.sc' 3 2 1)
  change Module.finrank ℚ (LinearMap.ker (C.d 2 1).hom) =
    Module.finrank ℚ (C.sc' 3 2 1).homology +
      Module.finrank ℚ (LinearMap.range (C.d 3 2).hom) at hker
  have hsc := (CategoryTheory.ShortComplex.homologyMapIso
    (C.isoSc' 3 2 1 (by simp) (by simp))).toLinearEquiv.finrank_eq
  change Module.finrank ℚ (C.homology 2) =
    Module.finrank ℚ (C.sc' 3 2 1).homology at hsc
  rw [hd₃, LinearMap.range_zero, finrank_bot, add_zero, ← hsc] at hker
  have hnorm := (isoOfQuasiIsoAt (X.toNormalizedChainComplex R) 2).toLinearEquiv.finrank_eq
  change Module.finrank ℚ ((X.chainComplex R).homology 2) =
    Module.finrank ℚ (C.homology 2) at hnorm
  have hreal := (DifferentialGeometry.SSet.realizationHomologyIso R X 2).toLinearEquiv.finrank_eq
  let F := (singularHomologyFunctor (ModuleCat ℚ) 2).obj R
  let e : _root_.SSet.toTop.obj X ≅ TopCat.of K.space :=
    TopCat.isoOfHomeo (by simpa [X] using
      SimplicialComplex.geometricRealizationHomeomorphism K)
  have hhomeo := (F.mapIso e).toLinearEquiv.finrank_eq
  have hbetti : Module.finrank ℚ (C.homology 2) =
      Homology.bettiNumber ℚ (TopCat.of K.space) 2 := by
    calc
      Module.finrank ℚ (C.homology 2) =
          Module.finrank ℚ ((X.chainComplex R).homology 2) := hnorm.symm
      _ = Module.finrank ℚ (((singularHomologyFunctor (ModuleCat ℚ) 2).obj R).obj
          (_root_.SSet.toTop.obj X)) := hreal
      _ = Module.finrank ℚ (((singularHomologyFunctor (ModuleCat ℚ) 2).obj R).obj
          (TopCat.of K.space)) := by simpa [F, X] using hhomeo
      _ = Homology.bettiNumber ℚ (TopCat.of K.space) 2 := rfl
  calc
    Homology.bettiNumber ℚ (TopCat.of K.space) 2 =
        Module.finrank ℚ (C.homology 2) := hbetti.symm
    _ = Module.finrank ℚ (LinearMap.ker (C.d 2 1).hom) := hker.symm
    _ = Module.finrank ℚ (LinearMap.ker D) := eKer.finrank_eq
    _ = Module.finrank ℚ (LinearMap.ker
        (SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 1)) := rfl

open Classical in
theorem IsCombinatorialManifold.bettiNumber_two_eq_one_of_isOrientable
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : IsOrientable 2 K) :
    Homology.bettiNumber ℚ (TopCat.of K.space) 2 = 1 := by
  obtain ⟨o⟩ := ho
  rw [bettiNumber_two_eq_finrank_ker_surfaceBoundary o.vertexOrder K
    (fun s hs => hK.card_le K hs)]
  exact finrank_ker_surfaceBoundary_eq_one K hK hconn o

open Classical in
theorem IsCombinatorialManifold.bettiNumber_two_eq_zero_of_not_isOrientable
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : ¬ IsOrientable 2 K) :
    Homology.bettiNumber ℚ (TopCat.of K.space) 2 = 0 := by
  let r := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  rw [bettiNumber_two_eq_finrank_ker_surfaceBoundary r K
    (fun s hs => hK.card_le K hs)]
  exact finrank_ker_surfaceBoundary_eq_zero_of_not_isOrientable r K hK hconn ho

open Classical in
theorem IsCombinatorialManifold.eulerChar_eq_two_sub_bettiOne_of_isOrientable
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : IsOrientable 2 K) :
    eulerChar K = 2 - (Homology.bettiOne K.space : ℤ) := by
  have hEuler := eulerChar_eq_one_sub_bettiOne_add_bettiTwo K
    (fun s hs => hK.card_le K hs) hconn
  rw [hK.bettiNumber_two_eq_one_of_isOrientable K hconn ho] at hEuler
  omega

open Classical in
theorem IsCombinatorialManifold.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : IsOrientable 2 K) (hEuler : eulerChar K ≠ 2) :
    0 < Homology.bettiOne K.space := by
  have hformula := hK.eulerChar_eq_two_sub_bettiOne_of_isOrientable K hconn ho
  by_contra hpos
  have hb : Homology.bettiOne K.space = 0 := Nat.eq_zero_of_not_pos hpos
  exact hEuler (by omega)

open Classical in
theorem IsCombinatorialManifold.eulerChar_eq_one_sub_bettiOne_of_not_isOrientable
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : ¬ IsOrientable 2 K) :
    eulerChar K = 1 - (Homology.bettiOne K.space : ℤ) := by
  have hEuler := eulerChar_eq_one_sub_bettiOne_add_bettiTwo K
    (fun s hs => hK.card_le K hs) hconn
  rw [hK.bettiNumber_two_eq_zero_of_not_isOrientable K hconn ho] at hEuler
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
