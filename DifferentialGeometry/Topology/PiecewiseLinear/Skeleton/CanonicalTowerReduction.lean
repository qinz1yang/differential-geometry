/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.InnerSolidTorusToroidalShell
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorusOfCylindricalDiagram
import DifferentialGeometry.Topology.Connected.PhragmenBrouwer

/-!
# Controlled torus towers and locally finite surgery

Unreviewed reconnaissance interfaces. The two open leaves construct split-disk cylinder
coordinates and controlled outer tori. The single-torus supply and even/odd selection assemble
the tower. The descent section separates four local transition specifications from proved
conditional operations, finite-rank termination, and local stabilization. Its geometric
transition suppliers and the full descent endpoint remain absent. No declaration in this file
is an accepted producer.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerReduction

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def cylinder : Set E3 := {x | x 0 ^ 2 + x 2 ^ 2 ≤ 1 ∧ |x 1| ≤ 1}

def meridianDisk : Set E3 := {x | x 0 ^ 2 + x 2 ^ 2 ≤ 1 ∧ x 1 = 0}

def meridianRim : Set E3 := {x | x 0 ^ 2 + x 2 ^ 2 = 1 ∧ x 1 = 0}

structure DiskCoordinates (φ : E3 → E3) (Dimg Dbdimg Y : Set E3) (P' : E3) : Prop where
  embedding : IsEmbedding (cylinder.domRestrict φ)
  imageCylinder : φ '' cylinder = Y
  imageDisk : φ '' meridianDisk = Dimg
  imageRim : φ '' meridianRim = Dbdimg
  center : φ 0 = P'

structure ControlledRevolvedTower (φ : E3 → E3) (Pt : ℤ → E3)
    (Dp Dpint J A S T : ℤ → Set E3) (Dimg Dbdimg W I Z : Set E3) (P' : E3) : Prop where
  base : ∀ i : ℤ, IsRevolvedTorusChain (fun j : Fin 4 => Pt (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 3 => Dp (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 3 => Dpint (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 4 => J (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 3 => A (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 3 => S (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 3 => T (i + ((j : ℕ) : ℤ)))
  embedding : ∀ i : ℤ, IsEmbedding
    ((⋃ j : Fin 3, S (i + ((j : ℕ) : ℤ))).domRestrict φ)
  compactAnnulus : ∀ i, IsCompact (φ '' A i)
  apart : ∀ i k : ℤ, 2 ≤ |i - k| → Disjoint (φ '' S i) (φ '' S k)
  annuliEq : φ '' (⋃ i, A i) = Dimg \ (Dbdimg ∪ {P'})
  subsetW : ∀ i, φ '' S i ⊆ W
  subsetInterior : ∀ i, φ '' S i ⊆ I
  centerMemInterior : P' ∈ I
  closureLower : ∀ m : ℤ,
    closure (⋃ i, ⋃ (_ : i ≤ m), φ '' S i) = (⋃ i, ⋃ (_ : i ≤ m), φ '' S i) ∪ {P'}
  closureUpper : ∀ m : ℤ,
    closure (⋃ i, ⋃ (_ : m ≤ i), φ '' S i) = (⋃ i, ⋃ (_ : m ≤ i), φ '' S i) ∪ Dbdimg
  locallyFinite : ∀ x ∈ I, x ≠ P' → ∃ U ∈ 𝓝 x, {i | (φ '' S i ∩ U).Nonempty}.Finite
  avoids : ∀ i, Disjoint (φ '' S i) Z

section Tower

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}

open Classical in
theorem exists_splitDisk_cylinder_coordinates (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id)) :
    ∃ φ : E3 → E3,
      DiskCoordinates φ (h '' D {u, v}) (h '' Dbd {u, v}) (h '' C u ∪ h '' C v) P' := by
  sorry

open Classical in
theorem exists_controlled_revolved_tower {φ : E3 → E3}
    (hc : DiskCoordinates φ (h '' D {u, v}) (h '' Dbd {u, v}) (h '' C u ∪ h '' C v) P')
    (hW : IsClosed W) (hWint : h '' (D {u, v} \ Dbd {u, v}) \ {P'} ⊆ interior W)
    (hWsub : W ⊆ h '' C u ∪ h '' C v)
    (hWfr : W ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd {u, v})
    (hWK : W ∩ h '' K.space = {P'}) {Z : Set E3} (hZ : IsClosed Z)
    (hZD : Disjoint Z (h '' D {u, v})) :
    ∃ (Pt : ℤ → E3) (Dp Dpint J A S T : ℤ → Set E3),
      ControlledRevolvedTower φ Pt Dp Dpint J A S T (h '' D {u, v}) (h '' Dbd {u, v}) W
        (interior (h '' C u ∪ h '' C v)) Z P' := by
  sorry

theorem exists_fitting_solidTorus {A S : Set E3} (hS : IsTopologicalSolidTorus S)
    (hA : IsCompact A) (hAS : A ⊆ interior S) (h307 : Moise307) :
    ∃ R, Fits A (interior S) R := by
  obtain ⟨S₁, hS₁, hAS₁, hS₁S, hshell⟩ :=
    hS.exists_toroidalShell_of_isCompact_subset_interior hA hAS
  obtain ⟨R, hR, hS₁R, hRS⟩ := h307 S₁ S hS₁ hS hS₁S hshell
  exact ⟨R, isCombinatorialSolidTorus_of_hasCylindricalDiagram hR,
    hAS₁.trans (interior_subset.trans hS₁R), hRS⟩

theorem exists_fitting_annulus_image
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

theorem exists_adjacent_generalPosition_family {A U : ℤ → Set E3}
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
    simp only [S, if_neg hm, hd]
  refine ⟨S, ?_, ?_⟩
  · intro i
    by_cases hi : i % 2 = 0
    · simpa only [S, if_pos hi] using hR i
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

theorem ControlledRevolvedTower.exists_canonicalTower
    {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T : ℤ → Set E3}
    {Dimg Dbdimg W I Z : Set E3} {P' : E3}
    (hc : ControlledRevolvedTower φ Pt Dp Dpint J A S T Dimg Dbdimg W I Z P')
    (h307 : Moise307) :
    ∃ S'' T'' : ℤ → Set E3,
      IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P' := by
  have hseed : ∀ i, ∃ R, Fits (φ '' A i) (interior (φ '' S i)) R := by
    intro i
    simpa using exists_fitting_annulus_image (hc.base i) (hc.embedding i) h307 (0 : Fin 3)
  obtain ⟨R, hR, hGP⟩ := exists_adjacent_generalPosition_family hc.compactAnnulus
    (fun _ => isOpen_interior) hseed
  refine ⟨R, fun i => frontier (R i),
    { config := ?_
      apart := hc.apart
      annuliEq := hc.annuliEq
      subsetW := hc.subsetW
      subsetInterior := hc.subsetInterior
      centerMemInterior := hc.centerMemInterior
      closureLower := hc.closureLower
      closureUpper := hc.closureUpper
      locallyFinite := hc.locallyFinite }⟩
  intro i
  refine
    { base := hc.base i
      unionEq := rfl
      isEmbedding := hc.embedding i
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
  obtain ⟨φ, hφ⟩ := exists_splitDisk_cylinder_coordinates ht hu hv huv he hP'
  obtain ⟨Pt, Dp, Dpint, J, A, S, T, hc⟩ :=
    exists_controlled_revolved_tower hφ hW hWint hWsub hWfr hWK hZ hZD
  obtain ⟨S'', T'', htw⟩ := hc.exists_canonicalTower h307
  exact ⟨φ, Pt, Dp, Dpint, J, A, S, T, S'', T'', htw, hc.avoids⟩

end Tower

section DescentStages

def traceCircles (L T : Set E3) : Set (Set E3) :=
  {G | ∃ x ∈ L ∩ T, G = connectedComponentIn (L ∩ T) x ∧ IsPLSphere 1 G}

def boundsDiskIn (G T : Set E3) : Prop :=
  ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3),
    IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧ Δ ⊆ T ∧
      G = r '' stdSimplexBoundary 2

noncomputable def nullTraceCount (L T : Set E3) : ℕ :=
  {G ∈ traceCircles L T | boundsDiskIn G T}.ncard

def IsProtectedReplacement (X Y F Ω : Set E3) : Prop :=
  Y \ Ω = X \ Ω ∧ Y ∩ F = X ∩ F

def IsSeparatorIn (I M H K : Set E3) : Prop :=
  IsClosed (((↑) : I → E3) ⁻¹' M) ∧
    Separates (((↑) : I → E3) ⁻¹' M) (((↑) : I → E3) ⁻¹' H)
      (((↑) : I → E3) ⁻¹' K)

def IsInnermostSplitStep (I H K C C' L L' T F Ω : Set E3) : Prop :=
  IsSeparatorIn I C' H K ∧ IsProtectedReplacement C C' F Ω ∧
    C' = T ∪ L' ∧ T ⊆ C' ∧ (traceCircles L T).Finite ∧ (traceCircles L' T).Finite ∧
      nullTraceCount L' T < nullTraceCount L T

def IsTypeOneDeletion (I H K C R X X' F : Set E3) : Prop :=
  X = C ∪ R ∧ Disjoint C R ∧ IsClosed (((↑) : I → E3) ⁻¹' C) ∧
    IsClosed (((↑) : I → E3) ⁻¹' R) ∧
    ¬ Separates (((↑) : I → E3) ⁻¹' C) (((↑) : I → E3) ⁻¹' H)
      (((↑) : I → E3) ⁻¹' K) ∧
    X' = R ∧ IsSeparatorIn I X' H K ∧ X' ∩ F = X ∩ F

def IsTypeTwoDeletion (I H K C J₀ J₁ T B₀ B₁ X X' F : Set E3) : Prop :=
  IsPLAnnulusWithEnds C J₀ J₁ ∧ IsPLAnnulusWithEnds B₀ J₀ J₁ ∧
    IsPLAnnulusWithEnds B₁ J₀ J₁ ∧ T = B₀ ∪ B₁ ∧ B₀ ∩ B₁ = J₀ ∪ J₁ ∧
    C ∩ T = J₀ ∪ J₁ ∧ C ⊆ X ∧ T ⊆ X ∧
    X' = X \ (C \ (J₀ ∪ J₁)) ∧ IsSeparatorIn I X' H K ∧ X' ∩ F = X ∩ F

def IsTypeThreeDeletion (I H K X X' F : Set E3) (n : ℕ)
    (B Jlo Jhi : Fin n → Set E3) (keep discard : Fin n) : Prop :=
  keep ≠ discard ∧ (∀ j, IsPLAnnulusWithEnds (B j) (Jlo j) (Jhi j)) ∧
    (∀ j, B j ⊆ X) ∧ X' = X \ (B discard \ (Jlo discard ∪ Jhi discard)) ∧
    B keep ⊆ X' ∧ IsSeparatorIn I X' H K ∧ X' ∩ F = X ∩ F

theorem isProtectedReplacement_of_eq_outside {X Y F Ω : Set E3}
    (heq : Y \ Ω = X \ Ω) (hF : Disjoint F Ω) : IsProtectedReplacement X Y F Ω := by
  refine ⟨heq, ?_⟩
  ext x
  constructor
  · intro hx
    have hxΩ : x ∉ Ω := disjoint_left.mp hF hx.2
    have hxX : x ∈ X \ Ω := heq ▸ show x ∈ Y \ Ω from ⟨hx.1, hxΩ⟩
    exact ⟨hxX.1, hx.2⟩
  · intro hx
    have hxΩ : x ∉ Ω := disjoint_left.mp hF hx.2
    have hxY : x ∈ Y \ Ω := heq.symm ▸ show x ∈ X \ Ω from ⟨hx.1, hxΩ⟩
    exact ⟨hxY.1, hx.2⟩

theorem exists_disk_split_preserving_seams (h303 : Moise303)
    (M H K C Δ D₁ D₂ Ω F : Set E3) (r r₁ r₂ : (Fin 3 → ℝ) → E3)
    (hM : IsOpen M) (hMc : IsConnected M) (hHM : H ⊆ M) (hKM : K ⊆ M)
    (hHK : Disjoint H K) (hH : IsClosed (((↑) : M → E3) ⁻¹' H))
    (hK : IsClosed (((↑) : M → E3) ⁻¹' K)) (hCM : C ⊆ M)
    (hC : IsClosed (((↑) : M → E3) ⁻¹' C))
    (hsep : Separates (((↑) : M → E3) ⁻¹' C) (((↑) : M → E3) ⁻¹' H)
      (((↑) : M → E3) ⁻¹' K))
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ) (hΔC : Δ ⊆ C)
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁)
    (hr₂ : IsPLHomeomorphOn r₂ (stdSimplex ℝ (Fin 3)) D₂)
    (hinter : D₁ ∩ D₂ = Δ) (hsub : D₁ ∪ D₂ ⊆ C) (hnear : D₁ ∪ D₂ ∈ 𝓝ˢ[C] Δ)
    (hΔ₁ : Δ ⊆ D₁ \ r₁ '' stdSimplexBoundary 2)
    (hΔ₂ : Δ ⊆ D₂ \ r₂ '' stdSimplexBoundary 2)
    (hΩ : IsOpen Ω) (hΔΩ : Δ ⊆ Ω) (hΩM : Ω ⊆ M) (hΩHK : Disjoint Ω (H ∪ K))
    (hF : Disjoint F Ω) :
    ∃ (C' A₁ Δ₁ J₁ : Set E3) (r' : (Fin 3 → ℝ) → E3),
      IsClosed (((↑) : M → E3) ⁻¹' C') ∧ C' ⊆ M ∧
      Separates (((↑) : M → E3) ⁻¹' C') (((↑) : M → E3) ⁻¹' H)
        (((↑) : M → E3) ⁻¹' K) ∧
      IsProtectedReplacement C C' F Ω ∧ D₂ ⊆ C' ∧
      IsPLAnnulusWithEnds A₁ (r '' stdSimplexBoundary 2) J₁ ∧ A₁ ⊆ D₁ ∩ Ω ∧
      A₁ ∩ Δ = r '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn r' (stdSimplex ℝ (Fin 3)) Δ₁ ∧ J₁ = r' '' stdSimplexBoundary 2 ∧
      Δ₁ ⊆ Ω ∧ Δ₁ ∩ C = J₁ ∧
      C' = (C \ (A₁ \ (r '' stdSimplexBoundary 2 ∪ J₁))) ∪ Δ₁ := by
  obtain ⟨C', A₁, Δ₁, J₁, r', hC', hC'M, hsep', hout, hD₂, hrest⟩ :=
    h303 M H K C Δ D₁ D₂ Ω r r₁ r₂ hM hMc hHM hKM hHK hH hK hCM hC hsep hr hΔC
      hr₁ hr₂ hinter hsub hnear hΔ₁ hΔ₂ hΩ hΔΩ hΩM hΩHK
  exact ⟨C', A₁, Δ₁, J₁, r', hC', hC'M, hsep',
    isProtectedReplacement_of_eq_outside hout hF, hD₂, hrest⟩

theorem separates_after_delete_type_one {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {C R H K : Set X} (hC : IsClosed C) (hR : IsClosed R) (hCR : Disjoint C R)
    (hH : IsPreconnected H) (hK : IsPreconnected K)
    (hsep : Separates (C ∪ R) H K) (hCnon : ¬ Separates C H K) :
    Separates R H K :=
  (phragmen_brouwer hC hR hCR hH hK hsep).resolve_left hCnon

open Classical in
theorem exists_annular_component_of_essential_seams (h286 : Moise286)
    (S : Set E3) (hS : IsCombinatorialSolidTorus S) (n : ℕ) (G : Fin n → Set E3)
    (hn : 1 < n) (hG : ∀ i, IsPLSphere 1 (G i)) (hGS : ∀ i, G i ⊆ frontier S)
    (hdis : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hess : ∀ i, ¬ ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧ Δ ⊆ frontier S ∧
        G i = r '' stdSimplexBoundary 2)
    {x : E3} (hx : x ∈ frontier S \ ⋃ i, G i) :
    ∃ i j : Fin n, i ≠ j ∧
      IsPLAnnulusWithEnds (closure (connectedComponentIn (frontier S \ ⋃ i, G i) x))
        (G i) (G j) :=
  h286 S hS n G hn hG hGS hdis hess x hx

open Classical in
theorem exists_type_two_bounded_side (h267 : Moise267)
    (M : Fin 3 → Geometry.SimplicialComplex ℝ E3) (hfin : ∀ i, (M i).faces.Finite)
    (hman : ∀ i, IsCombinatorialManifoldWithBoundary 2 (M i))
    (hconn : ∀ i, IsConnected (M i).space)
    (hbd : ∀ i j, (boundaryComplex 2 (M i)).space = (boundaryComplex 2 (M j)).space)
    (hne : (boundaryComplex 2 (M 0)).space.Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint ((M i).space \ (boundaryComplex 2 (M i)).space)
      ((M j).space \ (boundaryComplex 2 (M j)).space))
    {x : E3} (hx : x ∉ ⋃ i, (M i).space)
    (hunbounded : ¬ Bornology.IsBounded (connectedComponentIn (⋃ i, (M i).space)ᶜ x)) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      frontier (connectedComponentIn (⋃ i, (M i).space)ᶜ x) = (M i).space ∪ (M j).space ∧
      ∀ y ∈ (M k).space \ (boundaryComplex 2 (M k)).space,
        Bornology.IsBounded (connectedComponentIn ((M i).space ∪ (M j).space)ᶜ y) :=
  h267 M hfin hman hconn hbd hne hdis x hx hunbounded

def deletionCandidate (C J₀ J₁ : Set E3) : Set E3 := C \ (J₀ ∪ J₁)

theorem delete_preserves_protected_seams {M C J₀ J₁ F : Set E3}
    (hF : Disjoint F (deletionCandidate C J₀ J₁)) :
    (M \ deletionCandidate C J₀ J₁) ∩ F = M ∩ F := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1.1, hx.2⟩
  · intro hx
    exact ⟨⟨hx.1, disjoint_left.mp hF hx.2⟩, hx.2⟩

theorem finite_bridge_count_decreases {ι : Type*} [DecidableEq ι]
    (bridges : Finset ι) {discard keep : ι} (hdiscard : discard ∈ bridges)
    (hkeep : keep ∈ bridges) (hne : keep ≠ discard) :
    keep ∈ bridges.erase discard ∧ (bridges.erase discard).card < bridges.card := by
  exact ⟨Finset.mem_erase.mpr ⟨hne, hkeep⟩, Finset.card_erase_lt_of_mem hdiscard⟩

theorem exists_terminal_of_strict_finite_rank {α : Type*} (rank : α → ℕ)
    (valid terminal : α → Prop) (step : α → α → Prop)
    (hstep : ∀ a, valid a → ¬ terminal a →
      ∃ b, valid b ∧ step a b ∧ rank b < rank a) :
    ∀ a, valid a → ∃ b, valid b ∧ terminal b ∧ Relation.ReflTransGen step a b := by
  intro a
  induction hn : rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    intro ha
    by_cases ht : terminal a
    · exact ⟨a, ha, ht, Relation.ReflTransGen.refl⟩
    · obtain ⟨b, hb, hab, hba⟩ := hstep a ha ht
      obtain ⟨c, hc, htc, hbc⟩ := ih (rank b) (hn ▸ hba) b rfl hb
      exact ⟨c, hc, htc, (Relation.ReflTransGen.single hab).trans hbc⟩

theorem exists_compatible_sequence {α : Type*} (a₀ : α) (valid : ℕ → α → Prop)
    (step : ℕ → α → α → Prop) (h₀ : valid 0 a₀)
    (hnext : ∀ n a, valid n a → ∃ b, valid (n + 1) b ∧ step n a b) :
    ∃ a : ℕ → α, a 0 = a₀ ∧ (∀ n, valid n (a n)) ∧ ∀ n, step n (a n) (a (n + 1)) := by
  classical
  let next : ∀ n, {a // valid n a} → {a // valid (n + 1) a} := fun n a =>
    ⟨(hnext n a.1 a.2).choose, (hnext n a.1 a.2).choose_spec.1⟩
  let a : ∀ n, {a // valid n a} := fun n => Nat.rec ⟨a₀, h₀⟩ next n
  refine ⟨fun n => (a n).1, rfl, fun n => (a n).2, ?_⟩
  intro n
  exact (hnext n (a n).1 (a n).2).choose_spec.2

theorem locally_eventually_eq_iUnion_of_finite_support {ι : Type*}
    {S Qlimit : ι → Set E3} {Q : ℕ → ι → Set E3} {I : Set E3} {P : E3}
    (hQ : ∀ n i, Q n i ⊆ S i) (hlimit : ∀ i, Qlimit i ⊆ S i)
    (hevent : ∀ i, ∃ N : ℕ, ∀ n ≥ N, Q n i = Qlimit i)
    (hfinite : ∀ x ∈ I, x ≠ P → ∃ U ∈ 𝓝 x, {i | (S i ∩ U).Nonempty}.Finite) :
    ∀ x ∈ I, x ≠ P → ∃ U ∈ 𝓝 x, ∃ N : ℕ, ∀ n ≥ N,
      (⋃ i, Q n i) ∩ U = (⋃ i, Qlimit i) ∩ U := by
  classical
  choose cutoff hcutoff using hevent
  intro x hx hxP
  obtain ⟨U, hU, hfin⟩ := hfinite x hx hxP
  refine ⟨U, hU, hfin.toFinset.sup cutoff, ?_⟩
  intro n hn
  ext y
  constructor
  · rintro ⟨hy, hyU⟩
    obtain ⟨i, hiy⟩ := mem_iUnion.mp hy
    have himem : i ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨y, hQ n i hiy, hyU⟩
    have heq := hcutoff i n ((Finset.le_sup himem).trans hn)
    exact ⟨mem_iUnion.mpr ⟨i, heq ▸ hiy⟩, hyU⟩
  · rintro ⟨hy, hyU⟩
    obtain ⟨i, hiy⟩ := mem_iUnion.mp hy
    have himem : i ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨y, hlimit i hiy, hyU⟩
    have heq := hcutoff i n ((Finset.le_sup himem).trans hn)
    exact ⟨mem_iUnion.mpr ⟨i, heq.symm ▸ hiy⟩, hyU⟩

theorem isClosed_of_locally_eventually_eq_off_point {X : Type*} [TopologicalSpace X]
    {M : ℕ → Set X} {L : Set X} {p : X} (hM : ∀ n, IsClosed (M n)) (hp : p ∈ L)
    (hlocal : ∀ x, x ≠ p → ∃ U ∈ 𝓝 x, ∃ n : ℕ, M n ∩ U = L ∩ U) : IsClosed L := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hxp : x ≠ p := fun h => hx (h.symm ▸ hp)
  obtain ⟨U, hU, n, heq⟩ := hlocal x hxp
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hxM : x ∉ M n := by
    intro hxM
    have hxL : x ∈ L ∩ U := heq ▸ show x ∈ M n ∩ U from ⟨hxM, hxU⟩
    exact hx hxL.1
  refine Filter.mem_of_superset (Filter.inter_mem hU ((hM n).isOpen_compl.mem_nhds hxM)) ?_
  intro y hy hyL
  have hyM : y ∈ M n ∩ U := heq.symm ▸ show y ∈ L ∩ U from ⟨hyL, hy.1⟩
  exact hy.2 hyM.1

end DescentStages

end DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerReduction
