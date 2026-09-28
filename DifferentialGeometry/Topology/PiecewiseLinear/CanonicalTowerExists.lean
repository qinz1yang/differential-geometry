/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SplitDiskCylinderCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.InnerSolidTorusToroidalShell
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorusOfCylindricalDiagram

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_fits_image_annulus_of_isRevolvedTorusChain
    {P : Fin 4 → E3} {Dp Dpint : Fin 3 → Set E3} {J : Fin 4 → Set E3}
    {A S T : Fin 3 → Set E3} {φ : E3 → E3}
    (hc : IsRevolvedTorusChain P Dp Dpint J A S T)
    (he : IsEmbedding ((⋃ j, S j).domRestrict φ)) (h307 : Moise307) (j : Fin 3) :
    ∃ R, Fits (φ '' A j) (interior (φ '' S j)) R := by
  have heS : IsEmbedding ((S j).domRestrict φ) :=
    he.comp (IsEmbedding.inclusion (subset_iUnion S j))
  let e : S j ≃ₜ φ '' S j :=
    heS.toHomeomorph.trans (Homeomorph.setCongr (range_domRestrict φ (S j)))
  have hS : IsTopologicalSolidTorus (φ '' S j) :=
    ⟨e.symm.trans (Classical.choice (hc.isSolidTorus j))⟩
  obtain ⟨S₁, hS₁, hAS₁, hS₁S, hshell⟩ :=
    exists_innerSolidTorus_toroidalShell_of_annulusImage hc rfl he j
  obtain ⟨R, hR, hS₁R, hRS⟩ := h307 S₁ (φ '' S j) hS₁ hS hS₁S hshell
  exact ⟨R, isCombinatorialSolidTorus_of_hasCylindricalDiagram hR,
    hAS₁.trans (interior_subset.trans hS₁R), hRS⟩

theorem exists_fits_family_pairGP_succ {A U : ℤ → Set E3}
    (hA : ∀ i, IsCompact (A i)) (hU : ∀ i, IsOpen (U i))
    (hseed : ∀ i, ∃ R, Fits (A i) (U i) R) :
    ∃ S : ℤ → Set E3, (∀ i, Fits (A i) (U i) (S i)) ∧ ∀ i, PairGP (S i) (S (i + 1)) := by
  classical
  choose R hR using hseed
  have hodd : ∀ k : ℤ, ∃ Q, Fits (A (2 * k + 1)) (U (2 * k + 1)) Q ∧
      PairGP Q (R (2 * k)) ∧ PairGP Q (R (2 * k + 2)) := by
    intro k
    obtain ⟨Q, hQ, hGP⟩ := exists_generalPosition_solidTorus_relative (hA (2 * k + 1))
      (hU (2 * k + 1)) (hR (2 * k + 1)) ![R (2 * k), R (2 * k + 2)]
      (fun j => by fin_cases j <;> exact (hR _).1)
    exact ⟨Q, hQ, hGP 0, hGP 1⟩
  choose Q hQ hleft hright using hodd
  let S : ℤ → Set E3 := fun i => if i % 2 = 0 then R i else Q (i / 2)
  have heven : ∀ k : ℤ, S (2 * k) = R (2 * k) := by
    intro k
    simp [S]
  have hodd' : ∀ k : ℤ, S (2 * k + 1) = Q k := by
    intro k
    have hm : (2 * k + 1) % 2 ≠ 0 := by omega
    have hd : (2 * k + 1) / 2 = k := by omega
    simp only [S, ite_eq_right hm, hd]
  refine ⟨S, ?_, ?_⟩
  · intro i
    by_cases hi : i % 2 = 0
    · simpa only [S, ite_eq_left hi] using hR i
    · have heq : i = 2 * (i / 2) + 1 := by omega
      rw [heq, hodd']
      exact hQ _
  · intro i
    by_cases hi : i % 2 = 0
    · have heq : i = 2 * (i / 2) := by omega
      rw [heq, heven, hodd']
      exact (hleft _).symm
    · have heq : i = 2 * (i / 2) + 1 := by omega
      have hs : i + 1 = 2 * (i / 2 + 1) := by omega
      rw [hs, heq, hodd', heven]
      convert hright (i / 2) using 1
      congr 1
      omega

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

open Classical in
theorem exists_canonicalTower (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v) (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id)) (hW : IsClosed W)
    (hWint : h '' (D {u, v} \ Dbd {u, v}) \ {P'} ⊆ interior W)
    (hWsub : W ⊆ h '' C u ∪ h '' C v)
    (hWfr : W ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd {u, v})
    (hWK : W ∩ h '' K.space = {P'}) (h307 : Moise307) {Z : Set E3} (hZ : IsClosed Z)
    (hZD : Disjoint Z (h '' D {u, v})) :
    ∃ (φ : E3 → E3) (Pt : ℤ → E3) (Dp Dpint J A S T S'' T'' : ℤ → Set E3),
      IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
        (interior (h '' C u ∪ h '' C v)) P' ∧ ∀ i, Disjoint (φ '' S i) Z := by
  let _ := hW
  let _ := hWsub
  let _ := hWK
  obtain ⟨φ, hφc, hφi, hφY, hφD, hφR, hφ0⟩ :=
    ht.exists_unitSolidCylinder_coordinates hu hv huv he
  rw [← hP'] at hφ0
  have hint : interior (h '' C u ∪ h '' C v) = φ '' interior unitSolidCylinder := by
    rw [← hφY]
    exact interior_image_eq_image_interior_of_isCompact isCompact_unitSolidCylinder hφc hφi
  have hDcyl : unitMeridianDisk ⊆ unitSolidCylinder := unitMeridianDisk_subset_unitSolidCylinder
  have hRcyl : unitMeridianCircle ⊆ unitSolidCylinder :=
    unitMeridianCircle_subset_unitMeridianDisk.trans hDcyl
  have h0cyl : (0 : E3) ∈ unitSolidCylinder := interior_subset zero_mem_interior_unitSolidCylinder
  have hO : IsOpen (interior unitSolidCylinder ∩ φ ⁻¹' (interior W ∩ Zᶜ)) :=
    (hφc.mono interior_subset).isOpen_inter_preimage isOpen_interior
      (isOpen_interior.inter hZ.isOpen_compl)
  have hMO : unitMeridianDisk \ (unitMeridianCircle ∪ {0}) ⊆
      interior unitSolidCylinder ∩ φ ⁻¹' (interior W ∩ Zᶜ) := by
    intro x hx
    have hxD : x ∈ unitMeridianDisk := hx.1
    have hφxD : φ x ∈ h '' D {u, v} := hφD ▸ mem_image_of_mem φ hxD
    refine ⟨unitMeridianDisk_sdiff_subset_interior hx, hWint ⟨?_, ?_⟩,
      fun hxZ => disjoint_left.mp hZD hxZ hφxD⟩
    · obtain ⟨d, hd, hdx⟩ := hφxD
      refine ⟨d, ⟨hd, fun hdb => hx.2 (Or.inl ?_)⟩, hdx⟩
      obtain ⟨y, hy, hyx⟩ : φ x ∈ φ '' unitMeridianCircle := hφR ▸ ⟨d, hdb, hdx⟩
      rw [← hφi (hRcyl hy) (hDcyl hxD) hyx]
      exact hy
    · intro hxP
      exact hx.2 (Or.inr (hφi (hDcyl hxD) h0cyl ((mem_singleton_iff.mp hxP).trans hφ0.symm)))
  obtain ⟨Pt, Dp, Dpint, J, A, S, T, hbase, hSO, hAc, hapart, hAun, hlow, hup, hlf⟩ :=
    exists_isRevolvedTorusChain_tower hO hMO
  have hScyl : ∀ i, S i ⊆ unitSolidCylinder := fun i =>
    (hSO i).trans (inter_subset_left.trans interior_subset)
  have hAS : ∀ i, A i ⊆ S i := fun i => by
    have h1 := ((hbase i).annulusSubset 0).trans interior_subset
    simpa using h1
  have hemb : IsEmbedding (unitSolidCylinder.domRestrict φ) := by
    have : CompactSpace unitSolidCylinder :=
      isCompact_iff_compactSpace.mp isCompact_unitSolidCylinder
    exact ((continuousOn_iff_continuous_domRestrict.mp hφc).isClosedEmbedding
      hφi.injective).toIsEmbedding
  have hembi : ∀ i, IsEmbedding ((⋃ j : Fin 3, S (i + ((j : ℕ) : ℤ))).domRestrict φ) :=
    fun i => hemb.comp (IsEmbedding.inclusion (iUnion_subset fun _ => hScyl _))
  have hclos : ∀ X ⊆ unitSolidCylinder, closure (φ '' X) = φ '' closure X := by
    intro X hX
    have hcl : closure X ⊆ unitSolidCylinder :=
      closure_minimal hX isCompact_unitSolidCylinder.isClosed
    exact (image_closure_of_isCompact
      (isCompact_unitSolidCylinder.of_isClosed_subset isClosed_closure hcl) (hφc.mono hcl)).symm
  have hAcpt : ∀ i, IsCompact (φ '' A i) := fun i =>
    (hAc i).image_of_continuousOn (hφc.mono ((hAS i).trans (hScyl i)))
  have hφS : ∀ i, φ '' S i ⊆ interior W ∩ Zᶜ := fun i => by
    rintro _ ⟨x, hx, rfl⟩
    exact (hSO i hx).2
  have hφSI : ∀ i, φ '' S i ⊆ interior (h '' C u ∪ h '' C v) := fun i => by
    rw [hint]
    exact image_mono fun x hx => (hSO i hx).1
  have hP'I : P' ∈ interior (h '' C u ∪ h '' C v) := by
    rw [hint, ← hφ0]
    exact mem_image_of_mem φ zero_mem_interior_unitSolidCylinder
  have hapart' : ∀ i k : ℤ, 2 ≤ |i - k| → Disjoint (φ '' S i) (φ '' S k) := fun i k hik =>
    (hapart i k hik).image hφi (hScyl i) (hScyl k)
  have h0D : (0 : E3) ∈ unitMeridianDisk := ⟨by simp, by simp⟩
  have hann : φ '' (⋃ i, A i) = h '' D {u, v} \ (h '' Dbd {u, v} ∪ {P'}) := by
    rw [hAun, (hφi.mono hDcyl).image_sdiff_subset
      (union_subset unitMeridianCircle_subset_unitMeridianDisk (singleton_subset_iff.mpr h0D)),
      image_union, image_singleton, hφD, hφR, hφ0]
  have hlow' : ∀ m : ℤ, closure (⋃ i, ⋃ (_ : i ≤ m), φ '' S i) =
      (⋃ i, ⋃ (_ : i ≤ m), φ '' S i) ∪ {P'} := by
    intro m
    have hsub : (⋃ i, ⋃ (_ : i ≤ m), S i) ⊆ unitSolidCylinder :=
      iUnion₂_subset fun i _ => hScyl i
    have himg : (⋃ i, ⋃ (_ : i ≤ m), φ '' S i) = φ '' ⋃ i, ⋃ (_ : i ≤ m), S i := by
      simp only [image_iUnion]
    rw [himg, hclos _ hsub, hlow m, image_union, image_singleton, hφ0]
  have hup' : ∀ m : ℤ, closure (⋃ i, ⋃ (_ : m ≤ i), φ '' S i) =
      (⋃ i, ⋃ (_ : m ≤ i), φ '' S i) ∪ h '' Dbd {u, v} := by
    intro m
    have hsub : (⋃ i, ⋃ (_ : m ≤ i), S i) ⊆ unitSolidCylinder :=
      iUnion₂_subset fun i _ => hScyl i
    have himg : (⋃ i, ⋃ (_ : m ≤ i), φ '' S i) = φ '' ⋃ i, ⋃ (_ : m ≤ i), S i := by
      simp only [image_iUnion]
    rw [himg, hclos _ hsub, hup m, image_union, hφR]
  have hlf' : ∀ x ∈ interior (h '' C u ∪ h '' C v), x ≠ P' →
      ∃ U ∈ 𝓝 x, {i | (φ '' S i ∩ U).Nonempty}.Finite := by
    intro x hx hxP
    have hx' := hx
    rw [hint] at hx'
    obtain ⟨y, hyI, rfl⟩ := hx'
    have hyC : y ∈ unitSolidCylinder := interior_subset hyI
    have hy0 : y ≠ 0 := fun h0 => hxP (by rw [h0, hφ0])
    have hyR : y ∉ unitMeridianCircle := by
      intro hyR
      have h1 : φ y ∈ h '' Dbd {u, v} := hφR ▸ mem_image_of_mem φ hyR
      rw [← hWfr] at h1
      exact disjoint_left.mp disjoint_interior_frontier hx h1.2
    obtain ⟨U, hU, hfin⟩ := hlf y hyC hy0 hyR
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
    have hK : IsClosed (φ '' (unitSolidCylinder \ Metric.ball y δ)) :=
      ((isCompact_unitSolidCylinder.diff Metric.isOpen_ball).image_of_continuousOn
        (hφc.mono sdiff_subset)).isClosed
    refine ⟨(φ '' (unitSolidCylinder \ Metric.ball y δ))ᶜ, hK.isOpen_compl.mem_nhds ?_,
      hfin.subset ?_⟩
    · rintro ⟨z, ⟨hzC, hzB⟩, hzy⟩
      have hzy' := hφi hzC hyC hzy
      subst hzy'
      exact hzB (Metric.mem_ball_self hδ)
    · rintro i ⟨_, ⟨z, hz, rfl⟩, hzV⟩
      refine ⟨z, hz, hball ?_⟩
      by_contra hzB
      exact hzV ⟨z, ⟨hScyl i hz, hzB⟩, rfl⟩
  have hseed : ∀ i, ∃ R, Fits (φ '' A i) (interior (φ '' S i)) R := fun i => by
    simpa using exists_fits_image_annulus_of_isRevolvedTorusChain (hbase i) (hembi i) h307
      (0 : Fin 3)
  obtain ⟨R, hR, hGP⟩ := exists_fits_family_pairGP_succ hAcpt (fun _ => isOpen_interior) hseed
  refine ⟨φ, Pt, Dp, Dpint, J, A, S, T, R, fun i => frontier (R i),
    { config := ?_
      apart := hapart'
      annuliEq := hann
      subsetW := fun i => (hφS i).trans (inter_subset_left.trans interior_subset)
      subsetInterior := hφSI
      centerMemInterior := hP'I
      closureLower := hlow'
      closureUpper := hup'
      locallyFinite := hlf' }, fun i => ?_⟩
  · intro i
    refine
      { base := hbase i
        unionEq := rfl
        isEmbedding := hembi i
        isPolyhedralSolidTorus := fun j => (hR _).1
        boundaryEq := fun _ => rfl
        annulusImageSubset := fun j => (hR _).2.1
        innerSubset := fun j => (hR _).2.2
        crossing := ?_
        polygons := ?_ }
    · intro j
      fin_cases j
      · simpa using (hGP i).1
      · simpa [add_assoc] using (hGP (i + 1)).1
    · intro j
      fin_cases j
      · simpa using (hGP i).2
      · simpa [add_assoc] using (hGP (i + 1)).2
  · rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxZ
    exact (hSO i hx).2.2 hxZ

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
