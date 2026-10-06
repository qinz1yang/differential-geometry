import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFrontierJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCircleDescentJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankKernel74

/-!
# Draft 74, `local_faces`, step 1: the local datum from one or two face functions, `dT ≠ 0`

Lane S-JUNCTIONS (by S-JUNCTIONS4), G23 part 2 (suffix `_JN74`). On any rows `R`:

* `StageCutRows74.localFaces_one_JN74`, `StageCutRows74.localFaces_two_JN74`: the datum of
  `JunctionRimFacts74.local_faces` at a point `c` (open `U`, label set `L` of one or two labels,
  face functions `φ`) from one resp. two smooth functions `f` on an open `N ∋ c` with `f c = 0`,
  independent differentials, the face-set clause and the sign model `C₁ ∩ N = {f ≤ 0}`;
* `exists_open_preconnected_subset_JN74`: a point of the interior of a set of a one-dimensional
  manifold has a preconnected open neighbourhood inside the set;
* `StageCutRows74.mfderiv_cornerT_ne_zero_JN74`: at a point of the circle domain on the rim level
  the differential of `T = cornerT` is not zero (rank two of the edge bundle).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A}

/-- **A point of the interior of a set of a locally connected space has a preconnected open
neighbourhood inside the set.** -/
theorem exists_open_preconnected_subset_JN74 {Y : Type*} [TopologicalSpace Y]
    [LocallyConnectedSpace Y] {S : Set Y} {c : Y} (hc : c ∈ interior S) :
    ∃ V : Set Y, IsOpen V ∧ c ∈ V ∧ IsPreconnected V ∧ V ⊆ S :=
  ⟨connectedComponentIn (interior S) c, isOpen_interior.connectedComponentIn,
    mem_connectedComponentIn hc, isPreconnected_connectedComponentIn,
    (connectedComponentIn_subset _ _).trans interior_subset⟩

namespace StageCutRows74

variable (R : StageCutRows74 A D)

/-- **The local datum of `local_faces` from one face function.** -/
theorem localFaces_one_JN74 {c : R.circle.Base} (N : TopologicalSpace.Opens R.circle.Base)
    (hcN : c ∈ N)
    (l : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent)
    (f : R.circle.Base → ℝ) (hf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ f N) (hfc : f c = 0)
    (hdf : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f c ≠ 0)
    (hface : {c' | c' ∈ N ∧ c' ∈ R.circle.cbase ∧ f c' = 0} =
      {c' | c' ∈ N ∧ c' ∈ R.circle.cbase ∧
        R.circle.fibre c' ⊆ circleFaceSet R.slimPieces R.edge l})
    (hsign : R.circle.cbase ∩ N = {c' | c' ∈ N ∧ f c' ≤ 0}) :
    ∃ U : TopologicalSpace.Opens R.circle.Base, c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent →
          R.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ R.circle.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ R.circle.cbase ∧
              R.circle.fibre c' ⊆ circleFaceSet R.slimPieces R.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        R.circle.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  classical
  refine ⟨N, hcN, {l}, fun _ => f, by simp, by simp, ?_, ?_, ?_⟩
  · intro l' hl'
    rw [Finset.mem_singleton] at hl'
    subst hl'
    exact ⟨hf, hfc, hface⟩
  · intro g
    have hsurj : Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f c) := surjective_of_ne_zero_JN74 hdf
    obtain ⟨w, hw⟩ := hsurj (g ⟨l, Finset.mem_singleton_self l⟩)
    refine ⟨w, funext fun l' => ?_⟩
    have : l'.1 = l := Finset.mem_singleton.mp l'.2
    have hl' : l' = ⟨l, Finset.mem_singleton_self l⟩ := Subtype.ext this
    subst hl'
    exact hw
  · ext c'
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_singleton, forall_eq]
    exact (Set.ext_iff.1 hsign c')

/-- **The local datum of `local_faces` from two independent face functions.** -/
theorem localFaces_two_JN74 {c : R.circle.Base} (N : TopologicalSpace.Opens R.circle.Base)
    (hcN : c ∈ N)
    (l₁ l₂ : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent) (hne : l₁ ≠ l₂)
    (f₁ f₂ : R.circle.Base → ℝ) (hf₁ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ f₁ N)
    (hf₂ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ f₂ N) (hfc₁ : f₁ c = 0) (hfc₂ : f₂ c = 0)
    (hrank : Surjective fun w : TangentSpace (𝓡 2) c =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f₁ c w, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f₂ c w))
    (hface₁ : {c' | c' ∈ N ∧ c' ∈ R.circle.cbase ∧ f₁ c' = 0} =
      {c' | c' ∈ N ∧ c' ∈ R.circle.cbase ∧
        R.circle.fibre c' ⊆ circleFaceSet R.slimPieces R.edge l₁})
    (hface₂ : {c' | c' ∈ N ∧ c' ∈ R.circle.cbase ∧ f₂ c' = 0} =
      {c' | c' ∈ N ∧ c' ∈ R.circle.cbase ∧
        R.circle.fibre c' ⊆ circleFaceSet R.slimPieces R.edge l₂})
    (hsign : R.circle.cbase ∩ N = {c' | c' ∈ N ∧ f₁ c' ≤ 0 ∧ f₂ c' ≤ 0}) :
    ∃ U : TopologicalSpace.Opens R.circle.Base, c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent →
          R.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ R.circle.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ R.circle.cbase ∧
              R.circle.fibre c' ⊆ circleFaceSet R.slimPieces R.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        R.circle.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  classical
  let φ : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent →
      R.circle.Base → ℝ := fun l => if l = l₁ then f₁ else f₂
  have hφ₁ : φ l₁ = f₁ := by simp [φ]
  have hφ₂ : φ l₂ = f₂ := by simp [φ, hne.symm]
  have hcard : ({l₁, l₂} : Finset _).card = 2 := Finset.card_pair hne
  refine ⟨N, hcN, {l₁, l₂}, φ, by omega, by omega, ?_, ?_, ?_⟩
  · intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · rw [hφ₁]
      exact ⟨hf₁, hfc₁, hface₁⟩
    · rw [Finset.mem_singleton.mp hl, hφ₂]
      exact ⟨hf₂, hfc₂, hface₂⟩
  · intro g
    obtain ⟨w, hw⟩ := hrank (g ⟨l₁, by simp⟩, g ⟨l₂, by simp⟩)
    refine ⟨w, funext fun l => ?_⟩
    rcases Finset.mem_insert.mp l.2 with h | h
    · have hl : l = ⟨l₁, by simp⟩ := Subtype.ext h
      subst hl
      show mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ l₁) c w = _
      rw [hφ₁]
      exact congrArg Prod.fst hw
    · have h2 : l.1 = l₂ := Finset.mem_singleton.mp h
      have hl : l = ⟨l₂, by simp⟩ := Subtype.ext h2
      subst hl
      show mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ l₂) c w = _
      rw [hφ₂]
      exact congrArg Prod.snd hw
  · ext c'
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq]
    rw [hφ₁, hφ₂]
    exact (Set.ext_iff.1 hsign c').trans (by
      simp only [mem_ofPred_eq])

/-- **At a rim-level point of the circle domain the differential of `T` is not zero.** -/
theorem mfderiv_cornerT_ne_zero_JN74 (p : R.circle.domain)
    (hpS : (p : W.Carrier) ∈ R.edge.source)
    (hph : R.edge.height ⟨p, hpS⟩ = R.edge.level) :
    mfderiv W.model 𝓘(ℝ, ℝ) R.cornerT p ≠ 0 := by
  classical
  let T : W.Carrier → ℝ := fun z =>
    if hz : z ∈ R.edge.source then R.edge.height ⟨z, hz⟩ - R.edge.level else 0
  have hTfun : (fun y : R.edge.source => T y) = fun y => R.edge.height y - R.edge.level := by
    funext y
    simp only [T, y.2, ↓reduceDIte]
  have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) T (p : W.Carrier) := by
    refine (mdifferentiableAt_subtype_iff (U := R.edge.source) (f := T)
      (x := ⟨p, hpS⟩)).mp ?_
    rw [hTfun]
    exact ((R.edge.height_smooth.sub contMDiff_const).contMDiffAt).mdifferentiableAt
      (by decide)
  have e2 : mfderiv W.model 𝓘(ℝ, ℝ) T (p : W.Carrier) =
      mfderiv W.model 𝓘(ℝ, ℝ) R.edge.height ⟨p, hpS⟩ := by
    have := mfderiv_restrict_open (I := W.model) (J := 𝓘(ℝ, ℝ)) T R.edge.source ⟨p, hpS⟩
    rw [hTfun, mfderiv_sub_const_JN74] at this
    exact this.symm
  have hrest := mfderiv_restrict_open (I := W.model) (J := 𝓘(ℝ, ℝ)) T R.circle.domain p
  have hfun : (R.cornerT : R.circle.domain → ℝ) = fun z : R.circle.domain => T z := rfl
  rw [hfun, hrest, e2]
  intro h0
  obtain ⟨v, hv⟩ := R.edge.rank_two ⟨p, hpS⟩ hph (0, 1)
  have h1 : mfderiv W.model 𝓘(ℝ, ℝ) R.edge.height ⟨p, hpS⟩ v = 1 := congrArg Prod.snd hv
  rw [h0] at h1
  exact (zero_ne_one : (0 : ℝ) ≠ 1) (show (0 : ℝ) = 1 from h1)

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
