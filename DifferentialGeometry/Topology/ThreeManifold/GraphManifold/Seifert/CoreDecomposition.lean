import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabUniqueness
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BaseMorseBicollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Elementary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingDisc
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.ModelImmersion
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleClassification
import DifferentialGeometry.Topology.Manifold.MFDeriv.Interior
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabUniquenessProof

/-!
# Decomposition of the core of a Morse base

Lane MD3 of the P1 Morse-decomposition plan. The interior of a compact surface `B` is a
boundaryless manifold `Ambient B` modelled on `ℝ²`. A compact component `K` of a regular slab
`f⁻¹ [a, b]` with `0 < a` is the whole slab of the restriction of `f` to an open set
`N' ⊆ Ambient B` (`componentOpens`), so the slab lemmas of `SaddleSlabUniqueness.lean` apply to
it; with its slab charts translated so that no chart sends its centre to `0` (`shiftAtlas`), its
inclusion into the core `D.core` of Morse data `D` is a smooth embedding
(`isSmoothEmbedding_pieceToCore`). Nondegeneracy and index of critical points pass from `B` to
`N'` (`isNondegenerateCriticalPointAt_piece_iff`, `chartHessianAt_piece_eq`).

Pieces (`SlabPiece`: a model planar base, a diffeomorphism onto `K`, and the level of each
boundary circle): a component without critical points is an annulus
(`nonempty_slabPiece_of_regular`, by the classification of compact connected one-manifolds), a
component containing an extremum is the disc of `D.thin` (`nonempty_slabPiece_of_extremum`), and
a component containing a saddle whose lower or upper level is disconnected is the pants
(`nonempty_slabPiece_of_saddle`, by lane MD2's slab uniqueness). Every boundary circle of a piece
is a whole component of its level set (`range_pieceGamma`).

Assembly: cuts are MD1's level bicollars at the levels `1, …, m - 1`, shrunk by a common factor
and viewed in the core (`coreCut`); same-level bicollars meet only along common flow lines by ODE
uniqueness (`eq_of_bicollar_eq`). The collars of every piece are replaced by halves of these
bicollars (`halfCollar`, `matchDiffeo`, `exists_recollared_of_data`); the bottom circles use the
unshrunk level-`0` bicollars. `exists_planarDecomposition_of_pieces` builds the planar
decomposition of `D.core` with the frozen collar clause, given `D.κ < D.level 1 - D.level 0` and
a piece for every slab component, and `exists_planarDecomposition_core_of_gap` discharges the
pieces when every saddle component has a disconnected lower or upper level. Shrinking `κ`
(`withKappa`) gives the gap for free: `exists_planarDecomposition_core_of_shrink`.
-/

set_option autoImplicit false

noncomputable section
open Set Function TopologicalSpace Topology Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.CoreDecomposition

abbrev E2 := EuclideanSpace ℝ (Fin 2)

variable (B : CompactSurface.{u})

abbrev interiorOpens : Opens B.Carrier :=
  DifferentialGeometry.Manifold.intrinsicInterior (SurfaceModel.model B.kind) ∞ (by simp)

def Ambient : Type u := interiorOpens B

instance : TopologicalSpace (Ambient B) := inferInstanceAs (TopologicalSpace (interiorOpens B))

instance : ChartedSpace E2 (Ambient B) :=
  DifferentialGeometry.Manifold.interiorChartedSpace (SurfaceModel.model B.kind) ∞
    (M := interiorOpens B)

instance : IsManifold 𝓘(ℝ, E2) ∞ (Ambient B) :=
  DifferentialGeometry.Manifold.interiorIsManifold (SurfaceModel.model B.kind) ∞
    (M := interiorOpens B)

instance : T2Space (Ambient B) := inferInstanceAs (T2Space (interiorOpens B))

instance : SecondCountableTopology (Ambient B) :=
  inferInstanceAs (SecondCountableTopology (interiorOpens B))

variable {B}

def ambientVal (x : Ambient B) : B.Carrier := Subtype.val (show interiorOpens B from x)

def toAmbient (x : interiorOpens B) : Ambient B := x

theorem ambientVal_toAmbient (x : interiorOpens B) : ambientVal (toAmbient x) = x.val := rfl

theorem ambientVal_mem (x : Ambient B) : ambientVal x ∈ interiorOpens B :=
  (show interiorOpens B from x).2

theorem ambientVal_injective : Injective (ambientVal (B := B)) := Subtype.val_injective

theorem isOpenEmbedding_ambientVal : IsOpenEmbedding (ambientVal (B := B)) :=
  (interiorOpens B).isOpen.isOpenEmbedding_subtypeVal

theorem contMDiff_ambientVal :
    ContMDiff 𝓘(ℝ, E2) (SurfaceModel.model B.kind) ∞ (ambientVal (B := B)) := by
  have h := DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val
    (SurfaceModel.model B.kind) ∞ (M := B.Carrier) (by simp)
  exact h

theorem contMDiff_toAmbient :
    ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, E2) ∞ (toAmbient (B := B)) := by
  have h := DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas
    (SurfaceModel.model B.kind) ∞ (M := interiorOpens B)
  exact h

section Lift

variable {F' G' X : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [TopologicalSpace G']
  {J : ModelWithCorners ℝ F' G'} [TopologicalSpace X] [ChartedSpace G' X]

theorem contMDiffOn_ambient_iff (g : X → Ambient B) (s : Set X) :
    ContMDiffOn J 𝓘(ℝ, E2) ∞ g s ↔
      ContMDiffOn J (SurfaceModel.model B.kind) ∞ (ambientVal ∘ g) s := by
  constructor
  · intro h
    exact contMDiff_ambientVal.comp_contMDiffOn h
  · intro h
    have h' : ContMDiffOn J (SurfaceModel.model B.kind) ∞
        (fun x => (show interiorOpens B from g x)) s :=
      (DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff (interiorOpens B) _ s).mp h
    exact contMDiff_toAmbient.comp_contMDiffOn h'

theorem contMDiffOn_opens_ambient_iff (N' : Opens (Ambient B)) (g : X → N') (s : Set X) :
    ContMDiffOn J 𝓘(ℝ, E2) ∞ g s ↔
      ContMDiffOn J (SurfaceModel.model B.kind) ∞ (fun x => ambientVal (g x).val) s := by
  rw [← DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff N' g s]
  exact contMDiffOn_ambient_iff _ s

end Lift

section Opens

variable (N' : Opens (Ambient B))

def opensVal (x : N') : B.Carrier := ambientVal x.val

theorem isOpenEmbedding_opensVal : IsOpenEmbedding (opensVal N') :=
  isOpenEmbedding_ambientVal.comp N'.isOpen.isOpenEmbedding_subtypeVal

theorem contMDiff_opensVal :
    ContMDiff 𝓘(ℝ, E2) (SurfaceModel.model B.kind) ∞ (opensVal N') :=
  contMDiff_ambientVal.comp contMDiff_subtype_val

def opensRange : Set B.Carrier := range (opensVal N')

theorem isOpen_opensRange : IsOpen (opensRange N') := (isOpenEmbedding_opensVal N').isOpen_range

theorem exists_opensVal_eq {y : B.Carrier} (hy : y ∈ opensRange N') :
    ∃ x : N', opensVal N' x = y := hy

open Classical in
def opensInv (x₀ : N') (y : B.Carrier) : N' :=
  if h : y ∈ opensRange N' then Classical.choose h else x₀

theorem opensVal_opensInv (x₀ : N') {y : B.Carrier} (hy : y ∈ opensRange N') :
    opensVal N' (opensInv N' x₀ y) = y := by
  unfold opensInv
  split_ifs with h
  · exact Classical.choose_spec h
  · exact absurd hy h

theorem opensInv_opensVal (x₀ x : N') : opensInv N' x₀ (opensVal N' x) = x :=
  (isOpenEmbedding_opensVal N').injective (opensVal_opensInv N' x₀ ⟨x, rfl⟩)

theorem contMDiffOn_opensInv (x₀ : N') :
    ContMDiffOn (SurfaceModel.model B.kind) 𝓘(ℝ, E2) ∞ (opensInv N' x₀) (opensRange N') := by
  rw [contMDiffOn_opens_ambient_iff]
  exact contMDiffOn_id.congr fun y hy => opensVal_opensInv N' x₀ hy

theorem mfderiv_opens_ne_zero {f : B.Carrier → ℝ}
    (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (x : N')
    (h : mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f (opensVal N' x) ≠ 0) :
    mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) (fun z : N' => f (opensVal N' z)) x ≠ 0 := by
  have hO : opensRange N' ∈ 𝓝 (opensVal N' x) :=
    (isOpen_opensRange N').mem_nhds ⟨x, rfl⟩
  have hs : MDifferentiableAt (SurfaceModel.model B.kind) 𝓘(ℝ, E2) (opensInv N' x)
      (opensVal N' x) :=
    ((contMDiffOn_opensInv N' x).contMDiffAt hO).mdifferentiableAt (by simp)
  have hG : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) ∞ (fun z : N' => f (opensVal N' z)) :=
    hf.comp (contMDiff_opensVal N')
  have heq : (fun z : N' => f (opensVal N' z)) ∘ opensInv N' x =ᶠ[𝓝 (opensVal N' x)] f := by
    filter_upwards [hO] with y hy
    change f (opensVal N' (opensInv N' x y)) = f y
    rw [opensVal_opensInv N' x hy]
  have h' : mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ)
      ((fun z : N' => f (opensVal N' z)) ∘ opensInv N' x) (opensVal N' x) ≠ 0 := by
    rwa [heq.mfderiv_eq]
  have hx : opensInv N' x (opensVal N' x) = x := opensInv_opensVal N' x x
  have hres := mfderiv_ne_zero_of_comp (hG.mdifferentiableAt (by simp)) hs h'
  rwa [hx] at hres

end Opens

theorem image_connectedComponentIn_of_isEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e : X → Y} (he : IsEmbedding e) (S : Set X) (x : X) :
    e '' connectedComponentIn S x = connectedComponentIn (e '' S) (e x) := by
  by_cases hx : x ∈ S
  · apply Subset.antisymm
    · refine (isPreconnected_connectedComponentIn.image e he.continuous.continuousOn)
        |>.subset_connectedComponentIn (mem_image_of_mem e (mem_connectedComponentIn hx))
        (image_mono (connectedComponentIn_subset S x))
    · have hsub : connectedComponentIn (e '' S) (e x) ⊆ range e :=
        (connectedComponentIn_subset _ _).trans (image_subset_range e S)
      have hpre : IsPreconnected (e ⁻¹' connectedComponentIn (e '' S) (e x)) := by
        rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hsub]
        exact isPreconnected_connectedComponentIn
      have hS : e ⁻¹' connectedComponentIn (e '' S) (e x) ⊆ S := by
        intro z hz
        obtain ⟨w, hw, hwz⟩ := connectedComponentIn_subset _ _ hz
        rwa [← he.injective hwz]
      have hxmem : x ∈ e ⁻¹' connectedComponentIn (e '' S) (e x) :=
        mem_connectedComponentIn (mem_image_of_mem e hx)
      have h := hpre.subset_connectedComponentIn hxmem hS
      calc connectedComponentIn (e '' S) (e x)
          = e '' (e ⁻¹' connectedComponentIn (e '' S) (e x)) :=
            (image_preimage_eq_of_subset hsub).symm
        _ ⊆ e '' connectedComponentIn S x := image_mono h
  · rw [connectedComponentIn_eq_empty hx, image_empty, connectedComponentIn_eq_empty]
    rintro ⟨w, hw, hwx⟩
    exact hx (he.injective hwx ▸ hw)

section Shift

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E2 H} [TopologicalSpace M]
  [ChartedSpace H M] {K : Set M}

def shiftAtlas (C : SmoothBoundaryAtlas I 2 K) : SmoothBoundaryAtlas I 2 K where
  ambientChart y := (C.ambientChart y).trans (SmoothBoundaryAtlas.affineDiffeomorph
    (ContinuousLinearEquiv.refl ℝ E2)
    ((1 - C.ambientChart y y.val 1) • EuclideanSpace.single 1 1)).toPartialDiffeomorph
  mem_source y := ⟨C.mem_source y, mem_univ _⟩
  mem_iff y z hz := by
    rw [C.mem_iff y z hz.1]
    change 0 ≤ C.ambientChart y z 0 ↔
      0 ≤ (C.ambientChart y z + (1 - C.ambientChart y y.val 1) • EuclideanSpace.single 1 1 : E2) 0
    simp

theorem shiftAtlas_apply_self (C : SmoothBoundaryAtlas I 2 K) (y : K) :
    (shiftAtlas C).ambientChart y y.val 1 = 1 := by
  change (C.ambientChart y y.val + (1 - C.ambientChart y y.val 1) • EuclideanSpace.single 1 1 :
    E2) 1 = 1
  simp

end Shift

section Slab

variable {f : B.Carrier → ℝ} {a b : ℝ}

def ambientFun (f : B.Carrier → ℝ) (x : Ambient B) : ℝ := f (ambientVal x)

theorem contMDiff_ambientFun (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) ∞ (ambientFun f) :=
  hf.comp contMDiff_ambientVal

open Classical in
def ambientInv (x₀ : Ambient B) (y : B.Carrier) : Ambient B :=
  if h : y ∈ interiorOpens B then toAmbient ⟨y, h⟩ else x₀

theorem ambientVal_ambientInv (x₀ : Ambient B) {y : B.Carrier} (hy : y ∈ interiorOpens B) :
    ambientVal (ambientInv x₀ y) = y := by
  unfold ambientInv
  split_ifs with h
  · rfl
  · exact absurd hy h

theorem contMDiffOn_ambientInv (x₀ : Ambient B) :
    ContMDiffOn (SurfaceModel.model B.kind) 𝓘(ℝ, E2) ∞ (ambientInv x₀)
      (interiorOpens B : Set B.Carrier) := by
  rw [contMDiffOn_ambient_iff]
  exact contMDiffOn_id.congr fun y hy => ambientVal_ambientInv x₀ hy

theorem mfderiv_ambientFun_ne_zero (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (x : Ambient B) (h : mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f (ambientVal x) ≠ 0) :
    mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) (ambientFun f) x ≠ 0 := by
  have hO : (interiorOpens B : Set B.Carrier) ∈ 𝓝 (ambientVal x) :=
    (interiorOpens B).isOpen.mem_nhds (ambientVal_mem x)
  have hs : MDifferentiableAt (SurfaceModel.model B.kind) 𝓘(ℝ, E2) (ambientInv x)
      (ambientVal x) :=
    ((contMDiffOn_ambientInv x).contMDiffAt hO).mdifferentiableAt (by simp)
  have heq : ambientFun f ∘ ambientInv x =ᶠ[𝓝 (ambientVal x)] f := by
    filter_upwards [hO] with y hy
    change f (ambientVal (ambientInv x y)) = f y
    rw [ambientVal_ambientInv x hy]
  have h' : mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) (ambientFun f ∘ ambientInv x)
      (ambientVal x) ≠ 0 := by
    rwa [heq.mfderiv_eq]
  have hx : ambientInv x (ambientVal x) = x := ambientVal_injective
    (ambientVal_ambientInv x (ambientVal_mem x))
  have hres := mfderiv_ne_zero_of_comp
    ((contMDiff_ambientFun hf).mdifferentiableAt (by simp)) hs h'
  rwa [hx] at hres

theorem ambientFun_regular (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0) :
    ∀ x, ambientFun f x = a ∨ ambientFun f x = b →
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) (ambientFun f) x ≠ 0 :=
  fun x hx => mfderiv_ambientFun_ne_zero hf x (hreg (ambientVal x) hx)

def ambientSlabAtlas (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0) :
    SmoothBoundaryAtlas 𝓘(ℝ, E2) 2 (slabSet (ambientFun f) a b) :=
  slabAtlas finrank_euclideanSpace_fin (contMDiff_ambientFun hf) hab (ambientFun_regular hf hreg)

theorem isClosed_ambientSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b) : IsClosed (slabSet (ambientFun f) a b) := by
  rw [slabSet_eq hab.le]
  exact isClosed_Icc.preimage (contMDiff_ambientFun hf).continuous

theorem isClosed_slab_diff_component (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (x₀ : Ambient B) :
    IsClosed (slabSet (ambientFun f) a b \
      connectedComponentIn (slabSet (ambientFun f) a b) x₀) := by
  have hSc := isClosed_ambientSlab hf hab
  by_cases hx : x₀ ∈ slabSet (ambientFun f) a b
  · let := (ambientSlabAtlas hf hab hreg).toChartedSpace
    have : LocallyConnectedSpace (slabSet (ambientFun f) a b) :=
      ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) _
    have hc : IsClosed (connectedComponent
        (⟨x₀, hx⟩ : slabSet (ambientFun f) a b))ᶜ :=
      (isOpen_connectedComponent).isClosed_compl
    have himg := hSc.isClosedEmbedding_subtypeVal.isClosedMap _ hc
    rwa [image_compl_eq_range_sdiff_image Subtype.val_injective, Subtype.range_coe,
      ← connectedComponentIn_eq_image hx] at himg
  · rw [connectedComponentIn_eq_empty hx, sdiff_empty]
    exact hSc

def componentOpens (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (x₀ : Ambient B) : Opens (Ambient B) :=
  ⟨(slabSet (ambientFun f) a b \ connectedComponentIn (slabSet (ambientFun f) a b) x₀)ᶜ,
    (isClosed_slab_diff_component hf hab hreg x₀).isOpen_compl⟩

def pieceFun (f : B.Carrier → ℝ) (N' : Opens (Ambient B)) (z : N') : ℝ := f (opensVal N' z)

theorem contMDiff_pieceFun (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (N' : Opens (Ambient B)) : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) ∞ (pieceFun f N') :=
  hf.comp (contMDiff_opensVal N')

theorem pieceFun_regular (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (N' : Opens (Ambient B)) :
    ∀ z, pieceFun f N' z = a ∨ pieceFun f N' z = b →
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) (pieceFun f N') z ≠ 0 :=
  fun z hz => mfderiv_opens_ne_zero N' hf z (hreg (opensVal N' z) hz)

theorem val_image_pieceSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (x₀ : Ambient B) :
    Subtype.val '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b =
      connectedComponentIn (slabSet (ambientFun f) a b) x₀ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwS : w.val ∈ slabSet (ambientFun f) a b := by
      rw [mem_slabSet_iff hab.le] at hw ⊢
      exact hw
    by_contra hK
    exact w.2 ⟨hwS, hK⟩
  · intro hz
    have hzN : z ∈ componentOpens hf hab hreg x₀ := fun h => h.2 hz
    refine ⟨⟨z, hzN⟩, ?_, rfl⟩
    have hzS : z ∈ slabSet (ambientFun f) a b := connectedComponentIn_subset _ _ hz
    rw [mem_slabSet_iff hab.le] at hzS ⊢
    exact hzS

theorem pieceSlab_eq_preimage (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (x₀ : Ambient B) :
    slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b =
      Subtype.val ⁻¹' connectedComponentIn (slabSet (ambientFun f) a b) x₀ := by
  rw [← val_image_pieceSlab hf hab hreg x₀, preimage_image_eq _ Subtype.val_injective]

theorem isCompact_ambientSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b) (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) :
    IsCompact (slabSet (ambientFun f) a b) := by
  have hK : IsCompact (f ⁻¹' Icc a b) :=
    (isClosed_Icc.preimage hf.continuous).isCompact
  have hsub : f ⁻¹' Icc a b ⊆ range (ambientVal (B := B)) := by
    intro y hy
    exact ⟨toAmbient ⟨y, hint y hy.1⟩, rfl⟩
  rw [slabSet_eq hab.le]
  exact isOpenEmbedding_ambientVal.isInducing.isCompact_preimage' hK hsub

theorem isCompact_component (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b) (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) (x₀ : Ambient B) :
    IsCompact (connectedComponentIn (slabSet (ambientFun f) a b) x₀) := by
  by_cases hx : x₀ ∈ slabSet (ambientFun f) a b
  · have : CompactSpace (slabSet (ambientFun f) a b) :=
      isCompact_iff_compactSpace.mp (isCompact_ambientSlab hf hab hint)
    rw [connectedComponentIn_eq_image hx]
    exact (isClosed_connectedComponent.isCompact).image continuous_subtype_val
  · rw [connectedComponentIn_eq_empty hx]
    exact isCompact_empty

theorem isCompact_pieceSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) (x₀ : Ambient B) :
    IsCompact (slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) := by
  rw [pieceSlab_eq_preimage hf hab hreg x₀]
  refine (componentOpens hf hab hreg x₀).isOpen.isOpenEmbedding_subtypeVal.isInducing
    |>.isCompact_preimage' (isCompact_component hf hab hint x₀) ?_
  rw [Subtype.range_coe]
  intro z hz h
  exact h.2 hz

theorem isConnected_pieceSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    {x₀ : Ambient B} (hx₀ : x₀ ∈ slabSet (ambientFun f) a b) :
    IsConnected (slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) := by
  have h := isConnected_connectedComponentIn_iff.mpr hx₀
  rw [← val_image_pieceSlab hf hab hreg x₀] at h
  exact ⟨h.nonempty.of_image,
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp h.isPreconnected⟩

def pieceAtlas (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (x₀ : Ambient B) :
    SmoothBoundaryAtlas 𝓘(ℝ, E2) 2
      (slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :=
  slabAtlas finrank_euclideanSpace_fin (contMDiff_pieceFun hf _) hab (pieceFun_regular hf hreg _)

def slabSurface (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun f) a b) : CompactSurface.{u} where
  kind := .withBoundary
  Carrier := slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b
  charts := (pieceAtlas hf hab hreg x₀).toChartedSpace
  smooth := (pieceAtlas hf hab hreg x₀).isManifold
  compact := isCompact_iff_compactSpace.mp (isCompact_pieceSlab hf hab hreg hint x₀)
  connected := isConnected_iff_connectedSpace.mp (isConnected_pieceSlab hf hab hreg hx₀)

theorem mem_component_of_mem_pieceSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (x₀ : Ambient B) (z : componentOpens hf hab hreg x₀)
    (hz : pieceFun f (componentOpens hf hab hreg x₀) z ∈ Icc a b) :
    z.val ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀ := by
  rw [← val_image_pieceSlab hf hab hreg x₀]
  exact ⟨z, (mem_slabSet_iff hab.le z).mpr hz, rfl⟩

theorem exists_annulus_pieceSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun f) a b)
    (hnc : ∀ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀,
      mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f (ambientVal y) ≠ 0)
    (ha : ∃ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀, ambientFun f y = a)
    (hb : ∃ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀, ambientFun f y = b) :
    letI := (pieceAtlas hf hab hreg x₀).toChartedSpace
    ∃ e : planarSet.{u} 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b,
      (∀ x, pieceFun f (componentOpens hf hab hreg x₀) (e x).val =
        a + (b - a) * annulusLevel x) ∧
      (∀ t, pieceFun f (componentOpens hf hab hreg x₀)
        (e (annulusPlanarBase.{u}.collar 1 (t, halfZero))).val = a) ∧
      ∀ t, pieceFun f (componentOpens hf hab hreg x₀)
        (e (annulusPlanarBase.{u}.collar 0 (t, halfZero))).val = b := by
  set N' := componentOpens hf hab hreg x₀
  have hreg' : ∀ z, pieceFun f N' z ∈ Icc a b →
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) (pieceFun f N') z ≠ 0 := fun z hz =>
    mfderiv_opens_ne_zero N' hf z (hnc z.val (mem_component_of_mem_pieceSlab hf hab hreg x₀ z hz))
  have hcpt : IsCompact (pieceFun f N' ⁻¹' Icc a b) := by
    rw [← slabSet_eq hab.le]
    exact isCompact_pieceSlab hf hab hreg hint x₀
  have hconn : IsConnected (pieceFun f N' ⁻¹' Icc a b) := by
    rw [← slabSet_eq hab.le]
    exact isConnected_pieceSlab hf hab hreg hx₀
  have hN (y : Ambient B) (hy : y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀) :
      y ∈ N' := fun h => h.2 hy
  obtain ⟨ya, hya, hfa⟩ := ha
  obtain ⟨yb, hyb, hfb⟩ := hb
  exact exists_annulus_of_surfaceSlab
    DifferentialGeometry.Topology.Manifold.OneManifold.nonempty_circle_diffeomorph_of_finrank_eq_one
    finrank_euclideanSpace_fin (contMDiff_pieceFun hf N') hab hreg' hcpt hconn
    ⟨⟨ya, hN ya hya⟩, hfa⟩ ⟨⟨yb, hN yb hyb⟩, hfb⟩

theorem exists_annulus_pieceSlab_shift {f : B.Carrier → ℝ}
    (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun f) a b)
    (hnc : ∀ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀,
      mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f (ambientVal y) ≠ 0)
    (ha : ∃ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀, ambientFun f y = a)
    (hb : ∃ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀, ambientFun f y = b) :
    letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
    ∃ e : planarSet.{u} 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b,
      (∀ x, pieceFun f (componentOpens hf hab hreg x₀) (e x).val =
        a + (b - a) * annulusLevel x) ∧
      (∀ t, pieceFun f (componentOpens hf hab hreg x₀)
        (e (annulusPlanarBase.{u}.collar 1 (t, halfZero))).val = a) ∧
      ∀ t, pieceFun f (componentOpens hf hab hreg x₀)
        (e (annulusPlanarBase.{u}.collar 0 (t, halfZero))).val = b := by
  obtain ⟨e, h1, h2, h3⟩ := exists_annulus_pieceSlab hf hab hreg hint hx₀ hnc ha hb
  exact ⟨@Diffeomorph.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pieceAtlas hf hab hreg x₀).toChartedSpace _ _
    (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace _ e
    ((pieceAtlas hf hab hreg x₀).diffeomorphOfAmbient (shiftAtlas (pieceAtlas hf hab hreg x₀))
      (Diffeomorph.refl 𝓘(ℝ, E2) (componentOpens hf hab hreg x₀) ∞) (by intro z; exact Iff.rfl)),
    h1, h2, h3⟩

end Slab

section Immersion

theorem contMDiffOn_trans_partialHomeomorph {E₁ E₂ E₃ H₁ H₂ H₃ M₁ M₂ M₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace H₃] {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {I₃ : ModelWithCorners ℝ E₃ H₃} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
    {e : OpenPartialHomeomorph M₁ M₂} {e' : OpenPartialHomeomorph M₂ M₃}
    (he : ContMDiffOn I₁ I₂ ∞ e e.source) (he' : ContMDiffOn I₂ I₃ ∞ e' e'.source) :
    ContMDiffOn I₁ I₃ ∞ (e.trans e') (e.trans e').source :=
  he'.comp (he.mono inter_subset_left) (by intro y hy; exact hy.2)

theorem contMDiffOn_trans_symm_partialHomeomorph {E₁ E₂ E₃ H₁ H₂ H₃ M₁ M₂ M₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace H₃] {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {I₃ : ModelWithCorners ℝ E₃ H₃} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
    {e : OpenPartialHomeomorph M₁ M₂} {e' : OpenPartialHomeomorph M₂ M₃}
    (he : ContMDiffOn I₂ I₁ ∞ e.symm e.target) (he' : ContMDiffOn I₃ I₂ ∞ e'.symm e'.target) :
    ContMDiffOn I₃ I₁ ∞ (e.trans e').symm (e.trans e').target :=
  he.comp (he'.mono inter_subset_left) (by intro y hy; exact hy.2)

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
  [IsManifold (𝓡∂ 2) ∞ X] [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
  [IsManifold (𝓡∂ 2) ∞ Y]

def localInverseHomeomorph (ι : X → Y) (hι : Continuous ι) (hinj : Injective ι) {U : Set Y}
    (hU : IsOpen U) {g : Y → X} (hg : ContinuousOn g U) (hιg : ∀ y ∈ U, ι (g y) = y) :
    OpenPartialHomeomorph X Y where
  toFun := ι
  invFun := g
  source := ι ⁻¹' U
  target := U
  map_source' _ hz := hz
  map_target' y hy := by
    change ι (g y) ∈ U
    rw [hιg y hy]
    exact hy
  left_inv' z hz := hinj (hιg (ι z) hz)
  right_inv' y hy := hιg y hy
  open_source := hU.preimage hι
  open_target := hU
  continuousOn_toFun := hι.continuousOn
  continuousOn_invFun := hg

theorem isImmersionAtOfComplement_of_localInverse (ι : X → Y)
    (hι : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ ι) (hinj : Injective ι) (x : X) {U : Set Y}
    (hU : IsOpen U) (hxU : ι x ∈ U) {g : Y → X} (hg : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ g U)
    (hιg : ∀ y ∈ U, ι (g y) = y) :
    Manifold.IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) (𝓡∂ 2) ∞ ι x := by
  let R := localInverseHomeomorph ι hι.continuous hinj hU hg.continuousOn hιg
  let ψ := chartAt (EuclideanHalfSpace 2) (ι x)
  let φ := R.trans ψ
  have hφ : φ ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ X := by
    refine DifferentialGeometry.OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn φ ?_ ?_
    · exact contMDiffOn_trans_partialHomeomorph (e := R) (e' := ψ) hι.contMDiffOn
        contMDiffOn_chart
    · exact contMDiffOn_trans_symm_partialHomeomorph (e := R) (e' := ψ) hg contMDiffOn_chart_symm
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt hι.continuous.continuousAt
    (ContinuousLinearEquiv.prodUnique ℝ E2 PUnit.{1}) φ ψ ⟨hxU, mem_chart_source _ _⟩
    (mem_chart_source _ _) hφ (IsManifold.chart_mem_maximalAtlas _) ?_
  intro u hu
  rw [OpenPartialHomeomorph.extend_target] at hu
  obtain ⟨hφt, hrange⟩ := hu
  have hψt : (𝓡∂ 2).symm u ∈ ψ.target := hφt.1
  have hU' : ψ.symm ((𝓡∂ 2).symm u) ∈ U := hφt.2
  change (𝓡∂ 2) (ψ (ι (g (ψ.symm ((𝓡∂ 2).symm u))))) = u
  rw [hιg _ hU', ψ.right_inv hψt, (𝓡∂ 2).right_inv hrange]

end Immersion

section Core

variable (D : BaseMorseData B) {a b : ℝ}

def pieceToCore (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a)
    (x : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b) : D.core.Carrier :=
  ⟨opensVal _ x.val, ha.trans ((mem_slabSet_iff hab.le x.val).mp x.2).1⟩

theorem val_pieceToCore (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a)
    (x : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b) :
    (pieceToCore D hab hreg x₀ ha x).val = opensVal _ x.val := rfl

theorem injective_pieceToCore (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a) : Injective (pieceToCore D hab hreg x₀ ha) := by
  intro x y h
  have h' := congrArg Subtype.val h
  exact Subtype.val_injective ((isOpenEmbedding_opensVal _).injective h')

theorem contMDiff_pieceToCore (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a) :
    letI := (pieceAtlas D.smooth hab hreg x₀).toChartedSpace
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (pieceToCore D hab hreg x₀ ha) := by
  let := (pieceAtlas D.smooth hab hreg x₀).toChartedSpace
  exact (D.coreAtlas.contMDiff_iff_subtype_val _).mpr
    ((contMDiff_opensVal _).comp (pieceAtlas D.smooth hab hreg x₀).contMDiff_subtype_val)

theorem isEmbedding_pieceToCore (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a) : IsEmbedding (pieceToCore D hab hreg x₀ ha) := by
  have h : IsEmbedding (Subtype.val ∘ pieceToCore D hab hreg x₀ ha) :=
    (isOpenEmbedding_opensVal _).isEmbedding.comp IsEmbedding.subtypeVal
  exact IsEmbedding.of_comp (continuous_induced_rng.mpr h.continuous) continuous_subtype_val h

open Classical in
def coreToPiece (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (z : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b)
    (y : D.core.Carrier) : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b :=
  if h : y.val ∈ opensRange (componentOpens D.smooth hab hreg x₀) ∧ a ≤ D.f y.val ∧
      D.f y.val ≤ b then
    ⟨opensInv _ z.val y.val, (mem_slabSet_iff hab.le _).mpr (by
      change D.f (opensVal _ (opensInv _ z.val y.val)) ∈ Icc a b
      rw [opensVal_opensInv _ _ h.1]
      exact ⟨h.2.1, h.2.2⟩)⟩
  else z

def coreLocalSet (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) : Set D.core.Carrier :=
  {y | y.val ∈ opensRange (componentOpens D.smooth hab hreg x₀) ∧ D.f y.val < b ∧
    (a < D.f y.val ∨ a ≤ D.level 0)}

theorem isOpen_coreLocalSet (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) : IsOpen (coreLocalSet D hab hreg x₀) := by
  have hc : Continuous fun y : D.core.Carrier => D.f y.val :=
    D.smooth.continuous.comp continuous_subtype_val
  exact ((isOpen_opensRange _).preimage continuous_subtype_val).inter
    ((isOpen_lt hc continuous_const).inter ((isOpen_lt continuous_const hc).union isOpen_const))

theorem coreLocalSet_cond (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) {y : D.core.Carrier} (hy : y ∈ coreLocalSet D hab hreg x₀) :
    y.val ∈ opensRange (componentOpens D.smooth hab hreg x₀) ∧ a ≤ D.f y.val ∧
      D.f y.val ≤ b := by
  refine ⟨hy.1, ?_, hy.2.1.le⟩
  rcases hy.2.2 with h | h
  · exact h.le
  · exact h.trans y.2

theorem pieceToCore_coreToPiece (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a)
    (z : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b)
    {y : D.core.Carrier} (hy : y ∈ coreLocalSet D hab hreg x₀) :
    pieceToCore D hab hreg x₀ ha (coreToPiece D hab hreg x₀ z y) = y := by
  apply Subtype.ext
  rw [val_pieceToCore]
  unfold coreToPiece
  split_ifs with h
  · exact opensVal_opensInv _ _ h.1
  · exact absurd (coreLocalSet_cond D hab hreg x₀ hy) h

theorem contMDiffOn_coreToPiece (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (z : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b) :
    letI := (pieceAtlas D.smooth hab hreg x₀).toChartedSpace
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (coreToPiece D hab hreg x₀ z) (coreLocalSet D hab hreg x₀) := by
  let := (pieceAtlas D.smooth hab hreg x₀).toChartedSpace
  refine ((pieceAtlas D.smooth hab hreg x₀).contMDiffOn_iff_subtype_val _ _).mpr ?_
  have hv : ContMDiff (𝓡∂ 2) (SurfaceModel.model B.kind) ∞
      (fun y : D.core.Carrier => y.val) :=
    (D.coreAtlas.contMDiff_iff_subtype_val (fun y : D.core.Carrier => y)).mp contMDiff_id
  have h := (contMDiffOn_opensInv (componentOpens D.smooth hab hreg x₀) z.val).comp
    hv.contMDiffOn (fun y hy => (coreLocalSet_cond D hab hreg x₀ hy).1)
  refine h.congr fun y hy => ?_
  change (coreToPiece D hab hreg x₀ z y).val = opensInv _ z.val y.val
  unfold coreToPiece
  split_ifs with h'
  · rfl
  · exact absurd (coreLocalSet_cond D hab hreg x₀ hy) h'

theorem isImmersionAt_pieceToCore_of_mem (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a)
    (x : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b)
    (hx : pieceToCore D hab hreg x₀ ha x ∈ coreLocalSet D hab hreg x₀) :
    letI := (pieceAtlas D.smooth hab hreg x₀).toChartedSpace
    Manifold.IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) (𝓡∂ 2) ∞
      (pieceToCore D hab hreg x₀ ha) x := by
  let := (pieceAtlas D.smooth hab hreg x₀).toChartedSpace
  have := (pieceAtlas D.smooth hab hreg x₀).isManifold
  exact isImmersionAtOfComplement_of_localInverse _ (contMDiff_pieceToCore D hab hreg x₀ ha)
    (injective_pieceToCore D hab hreg x₀ ha) x (isOpen_coreLocalSet D hab hreg x₀) hx
    (contMDiffOn_coreToPiece D hab hreg x₀ x)
    (fun y hy => pieceToCore_coreToPiece D hab hreg x₀ ha x hy)

end Core

section CoreChart

variable (D : BaseMorseData B) (N' : Opens (Ambient B))

def coreInteriorSet (x₀ : N')
    (A : PartialDiffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) N' E2 ∞) : Set D.core.Carrier :=
  {y | D.level 0 < D.f y.val ∧ y.val ∈ opensRange N' ∧ opensInv N' x₀ y.val ∈ A.source}

theorem isOpen_coreInteriorSet (x₀ : N')
    (A : PartialDiffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) N' E2 ∞) :
    IsOpen (coreInteriorSet D N' x₀ A) := by
  have hc : Continuous fun y : D.core.Carrier => D.f y.val :=
    D.smooth.continuous.comp continuous_subtype_val
  have hO : IsOpen {y : D.core.Carrier | y.val ∈ opensRange N'} :=
    (isOpen_opensRange N').preimage continuous_subtype_val
  have hinv : ContinuousOn (fun y : D.core.Carrier => opensInv N' x₀ y.val)
      {y : D.core.Carrier | y.val ∈ opensRange N'} :=
    (contMDiffOn_opensInv N' x₀).continuousOn.comp continuous_subtype_val.continuousOn
      fun y hy => hy
  have h2 := hinv.isOpen_inter_preimage hO A.open_source
  have h3 := (isOpen_lt (continuous_const (y := D.level 0)) hc).inter h2
  convert h3 using 1
  ext y
  simp only [coreInteriorSet, mem_ofPred_eq, mem_inter_iff, mem_preimage]

theorem coreVal_contMDiff : ContMDiff (𝓡∂ 2) (SurfaceModel.model B.kind) ∞
    (fun y : D.core.Carrier => y.val) :=
  (D.coreAtlas.contMDiff_iff_subtype_val (fun y : D.core.Carrier => y)).mp contMDiff_id

open Classical in
def coreChartInv (y₀ : D.core.Carrier) (A : PartialDiffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) N' E2 ∞)
    (v : E2) : D.core.Carrier :=
  if h : D.level 0 ≤ D.f (opensVal N' (A.symm v)) then ⟨opensVal N' (A.symm v), h⟩ else y₀

theorem coreChartInv_val (y₀ : D.core.Carrier)
    (A : PartialDiffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) N' E2 ∞) {v : E2}
    (hv : D.level 0 ≤ D.f (opensVal N' (A.symm v))) :
    (coreChartInv D N' y₀ A v).val = opensVal N' (A.symm v) := by
  simp only [coreChartInv, hv, ↓reduceDIte]

def coreChartE (x₀ : N') (y₀ : D.core.Carrier)
    (A : PartialDiffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) N' E2 ∞) :
    PartialDiffeomorph (𝓡∂ 2) 𝓘(ℝ, E2) D.core.Carrier E2 ∞ where
  toFun y := A (opensInv N' x₀ y.val)
  invFun := coreChartInv D N' y₀ A
  source := coreInteriorSet D N' x₀ A
  target := A.target ∩ A.symm ⁻¹' {z | D.level 0 < D.f (opensVal N' z)}
  map_source' y hy := by
    refine ⟨A.map_source hy.2.2, ?_⟩
    have h1 : A.symm (A (opensInv N' x₀ y.val)) = opensInv N' x₀ y.val := A.left_inv hy.2.2
    have h2 : opensVal N' (opensInv N' x₀ y.val) = y.val := opensVal_opensInv _ _ hy.2.1
    change D.level 0 < D.f (opensVal N' (A.symm (A (opensInv N' x₀ y.val))))
    rw [h1, h2]
    exact hy.1
  map_target' v hv := by
    refine ⟨?_, ?_, ?_⟩
    · change D.level 0 < D.f (coreChartInv D N' y₀ A v).val
      rw [coreChartInv_val D N' y₀ A hv.2.le]
      exact hv.2
    · rw [coreChartInv_val D N' y₀ A hv.2.le]
      exact ⟨A.symm v, rfl⟩
    · rw [coreChartInv_val D N' y₀ A hv.2.le, opensInv_opensVal]
      exact A.map_target hv.1
  left_inv' y hy := by
    have h1 : A.symm (A (opensInv N' x₀ y.val)) = opensInv N' x₀ y.val := A.left_inv hy.2.2
    have h2 : opensVal N' (opensInv N' x₀ y.val) = y.val := opensVal_opensInv _ _ hy.2.1
    have h : D.level 0 ≤ D.f (opensVal N' (A.symm (A (opensInv N' x₀ y.val)))) := by
      rw [h1, h2]
      exact y.2
    apply Subtype.ext
    rw [coreChartInv_val D N' y₀ A h, h1, h2]
  right_inv' v hv := by
    rw [coreChartInv_val D N' y₀ A hv.2.le, opensInv_opensVal]
    exact A.right_inv hv.1
  open_source := isOpen_coreInteriorSet D N' x₀ A
  open_target := A.toOpenPartialHomeomorph.isOpen_inter_preimage_symm (isOpen_lt continuous_const
    (D.smooth.continuous.comp (isOpenEmbedding_opensVal N').continuous))
  contMDiffOn_toFun := by
    refine A.contMDiffOn.comp ((contMDiffOn_opensInv N' x₀).comp
      (coreVal_contMDiff D).contMDiffOn fun y hy => hy.2.1) fun y hy => hy.2.2
  contMDiffOn_invFun := by
    refine (D.coreAtlas.contMDiffOn_iff_subtype_val _ _).mpr ?_
    refine ((contMDiff_opensVal N').comp_contMDiffOn
      (A.symm.contMDiffOn.mono inter_subset_left)).congr fun v hv => ?_
    exact coreChartInv_val D N' y₀ A hv.2.le

def halfInteriorInverse :
    PartialDiffeomorph 𝓘(ℝ, E2) (𝓡∂ 2) E2 (EuclideanHalfSpace 2) ∞ where
  toFun := (𝓡∂ 2).symm
  invFun := 𝓡∂ 2
  source := interior (range (𝓡∂ 2))
  target := (𝓡∂ 2) ⁻¹' interior (range (𝓡∂ 2))
  map_source' v hv := by
    change (𝓡∂ 2) ((𝓡∂ 2).symm v) ∈ interior (range (𝓡∂ 2))
    rwa [(𝓡∂ 2).right_inv (interior_subset hv)]
  map_target' _ hy := hy
  left_inv' _ hv := (𝓡∂ 2).right_inv (interior_subset hv)
  right_inv' y _ := (𝓡∂ 2).left_inv y
  open_source := isOpen_interior
  open_target := isOpen_interior.preimage (𝓡∂ 2).continuous
  contMDiffOn_toFun := ((𝓡∂ 2).contMDiffOn_symm (n := ∞)).mono interior_subset
  contMDiffOn_invFun := (𝓡∂ 2).contMDiff.contMDiffOn

end CoreChart

section CaseC

variable (D : BaseMorseData B) {a b : ℝ}

theorem exists_interior_halfSpace_ne_zero :
    ∃ w ∈ interior (range (𝓡∂ 2)), w ≠ (0 : E2) := by
  obtain ⟨p, hp⟩ := (𝓡∂ 2).nonempty_interior
  by_cases hp0 : p = 0
  · have h1 : ∀ᶠ y in 𝓝[≠] p, y ∈ interior (range (𝓡∂ 2)) :=
      nhdsWithin_le_nhds (isOpen_interior.mem_nhds hp)
    have h2 : ∀ᶠ y in 𝓝[≠] p, y ≠ p := self_mem_nhdsWithin
    obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
    exact ⟨y, hy1, hp0 ▸ hy2⟩
  · exact ⟨p, hp, hp0⟩

theorem isImmersionAt_pieceToCore_of_lt (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a)
    (x : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b)
    (hx : D.level 0 < D.f (opensVal _ x.val)) :
    letI := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
    Manifold.IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) (𝓡∂ 2) ∞
      (pieceToCore D hab hreg x₀ ha) x := by
  let C := shiftAtlas (pieceAtlas D.smooth hab hreg x₀)
  let inst : ChartedSpace (EuclideanHalfSpace 2) _ := C.toChartedSpace
  have instM : IsManifold (𝓡∂ 2) ∞ _ := C.isManifold
  let N' := componentOpens D.smooth hab hreg x₀
  let A := C.ambientChart x
  have hAx : A x.val ≠ 0 := by
    intro h
    have h1 : A x.val 1 = 1 := shiftAtlas_apply_self (pieceAtlas D.smooth hab hreg x₀) x
    rw [h] at h1
    exact zero_ne_one h1
  obtain ⟨w, hw, hw0⟩ := exists_interior_halfSpace_ne_zero
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := ℝ) hAx hw0
  let y₀ := pieceToCore D hab hreg x₀ ha x
  let bb := ((coreChartE D N' x.val y₀ A).trans L.toDiffeomorph.toPartialDiffeomorph).trans
    halfInteriorInverse
  have hinv : opensInv N' x.val (opensVal N' x.val) = x.val := opensInv_opensVal N' x.val x.val
  have hbx : y₀ ∈ bb.source := by
    refine ⟨⟨⟨(show D.level 0 < D.f y₀.val from hx), ⟨x.val, rfl⟩, ?_⟩, mem_univ _⟩, ?_⟩
    · change opensInv N' x.val (opensVal N' x.val) ∈ A.source
      rw [hinv]
      exact C.mem_source x
    · change L (A (opensInv N' x.val (opensVal N' x.val))) ∈ interior (range (𝓡∂ 2))
      rw [hinv, hL]
      exact hw
  have hbmax : bb.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ D.core.Carrier :=
    bb.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      bb.contMDiffOn_toFun bb.contMDiffOn_invFun
  let s : Set (slabSet (pieceFun D.f N') a b) := pieceToCore D hab hreg x₀ ha ⁻¹' bb.source
  have hs : IsOpen s :=
    bb.open_source.preimage (isEmbedding_pieceToCore D hab hreg x₀ ha).continuous
  let d := (C.chart x).restr s
  have hdsource : d.source = (C.chart x).source ∩ s := by
    rw [OpenPartialHomeomorph.restr_source, hs.interior_eq]
  have hdmax : d ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ (slabSet (pieceFun D.f N') a b) :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ 2)) (IsManifold.chart_mem_maximalAtlas x) hs
  have hformula (y : slabSet (pieceFun D.f N') a b) (hy : y ∈ (C.chart x).source)
      (hyb : y ∈ s) : bb.toOpenPartialHomeomorph.extend (𝓡∂ 2) (pieceToCore D hab hreg x₀ ha y) =
        L ((C.chart x).extend (𝓡∂ 2) y) := by
    have hyb' : L (A (opensInv N' x.val (opensVal N' y.val))) ∈ interior (range (𝓡∂ 2)) :=
      hyb.2
    change (𝓡∂ 2) ((𝓡∂ 2).symm (L (A (opensInv N' x.val (opensVal N' y.val))))) =
      L ((C.chart x y).val)
    rw [(𝓡∂ 2).right_inv (interior_subset hyb'), opensInv_opensVal]
    exact congrArg L (OpenPartialHomeomorph.restrictSubtypes_apply
      (C.ambientChart x).toOpenPartialHomeomorph (slabSet (pieceFun D.f N') a b)
      {v : EuclideanSpace ℝ (Fin 2) | 0 ≤ v 0} x (0 : EuclideanHalfSpace 2)
      (C.mem_iff x) y hy).symm
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 2)) PUnit.{1}).trans L)
    d bb.toOpenPartialHomeomorph (by rw [hdsource]; exact ⟨C.mem_source x, hbx⟩) hbx hdmax hbmax
    (fun y hy => by rw [hdsource] at hy; exact hy.2) ?_
  intro u hu
  let y := (d.extend (𝓡∂ 2)).symm u
  have hy : y ∈ d.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (d.extend (𝓡∂ 2)).map_target hu
  rw [hdsource] at hy
  change bb.toOpenPartialHomeomorph.extend (𝓡∂ 2) (pieceToCore D hab hreg x₀ ha y) = L u
  rw [hformula y hy.1 hy.2]
  exact congrArg L ((d.extend (𝓡∂ 2)).right_inv hu)

theorem contMDiff_pieceToCore_shift (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a) :
    letI := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (pieceToCore D hab hreg x₀ ha) := by
  let := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
  exact (D.coreAtlas.contMDiff_iff_subtype_val _).mpr
    ((contMDiff_opensVal _).comp
      (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).contMDiff_subtype_val)

theorem contMDiffOn_coreToPiece_shift (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (z : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b) :
    letI := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (coreToPiece D hab hreg x₀ z) (coreLocalSet D hab hreg x₀) := by
  let := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
  refine ((shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).contMDiffOn_iff_subtype_val _ _).mpr ?_
  have h := (contMDiffOn_coreToPiece D hab hreg x₀ z)
  exact ((pieceAtlas D.smooth hab hreg x₀).contMDiffOn_iff_subtype_val _ _).mp h

theorem isImmersionAt_pieceToCore_of_mem_shift (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a)
    (x : slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀)) a b)
    (hx : pieceToCore D hab hreg x₀ ha x ∈ coreLocalSet D hab hreg x₀) :
    letI := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
    Manifold.IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) (𝓡∂ 2) ∞
      (pieceToCore D hab hreg x₀ ha) x := by
  let := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
  have := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).isManifold
  exact isImmersionAtOfComplement_of_localInverse _ (contMDiff_pieceToCore_shift D hab hreg x₀ ha)
    (injective_pieceToCore D hab hreg x₀ ha) x (isOpen_coreLocalSet D hab hreg x₀) hx
    (contMDiffOn_coreToPiece_shift D hab hreg x₀ x)
    (fun y hy => pieceToCore_coreToPiece D hab hreg x₀ ha x hy)

theorem isSmoothEmbedding_pieceToCore (hab : a < b)
    (hreg : ∀ y, D.f y = a ∨ D.f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0)
    (x₀ : Ambient B) (ha : D.level 0 ≤ a) :
    letI := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
    Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 2) ∞ (pieceToCore D hab hreg x₀ ha) := by
  let := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
  refine ⟨Manifold.IsImmersionOfComplement.isImmersion (F := PUnit.{1}) fun x => ?_,
    isEmbedding_pieceToCore D hab hreg x₀ ha⟩
  by_cases hx : D.level 0 < D.f (opensVal _ x.val)
  · exact isImmersionAt_pieceToCore_of_lt D hab hreg x₀ ha x hx
  · have hxm := (mem_slabSet_iff hab.le x.val).mp x.2
    refine isImmersionAt_pieceToCore_of_mem_shift D hab hreg x₀ ha x ⟨⟨x.val, rfl⟩, ?_, ?_⟩
    · change D.f (opensVal _ x.val) < b
      have h1 : D.f (opensVal _ x.val) ≤ D.level 0 := not_lt.mp hx
      exact lt_of_le_of_lt (h1.trans ha) hab
    · exact Or.inr (hxm.1.trans (not_lt.mp hx))

end CaseC

section Transport

variable {k : ℕ} (P : PlanarBase.{u} k) (X : Type u) [TopologicalSpace X]
  [hX : ChartedSpace (SurfaceModel.Space P.surface.kind) X]
  [hXm : IsManifold (SurfaceModel.model P.surface.kind) ∞ X] [T2Space X] [CompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]

def transportSurface : CompactSurface.{u} where
  kind := P.surface.kind
  Carrier := X

def transportBase
    (e : P.surface.Carrier ≃ₘ⟮SurfaceModel.model P.surface.kind,
      SurfaceModel.model P.surface.kind⟯ X) : PlanarBase.{u} k where
  surface := transportSurface P X
  collar j := (P.collar j).trans e.toPartialDiffeomorph
  source_eq j := by
    change (P.collar j).source ∩ (P.collar j) ⁻¹' univ = circleCollarSource
    rw [preimage_univ, inter_univ, P.source_eq j]
  boundary_zero j t := by
    have h := P.boundary_zero j t
    have himg := e.image_boundary (by simp)
    have hmem : e (P.collar j (t, halfZero)) ∈
        (SurfaceModel.model P.surface.kind).boundary X := by
      rw [← himg]
      exact mem_image_of_mem e h
    exact hmem
  disjoint i j hij := by
    have h := P.disjoint hij
    change Disjoint (univ ∩ e.symm ⁻¹' (P.collar i).target)
      (univ ∩ e.symm ⁻¹' (P.collar j).target)
    rw [univ_inter, univ_inter]
    exact h.preimage _
  boundary_exhausted := by
    have himg := e.image_boundary (by simp)
    change (SurfaceModel.model P.surface.kind).boundary X =
      ⋃ j, range fun t => e (P.collar j (t, halfZero))
    rw [← himg, P.boundary_exhausted, image_iUnion]
    congr 1
    ext j
    rw [← range_comp]
    rfl
  embedding x := P.embedding (e.symm x)
  isSmoothEmbedding := by
    have h := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
      P.embedding P.isSmoothEmbedding e.symm
    exact h
  range_embedding := by
    rw [← P.range_embedding]
    exact (e.symm.surjective.range_comp P.embedding)
  embedding_collar j t := by
    change P.embedding (e.symm (e (P.collar j (t, halfZero)))) = _
    rw [e.symm_apply_apply]
    exact P.embedding_collar j t

end Transport

section AnnulusPiece

variable {f : B.Carrier → ℝ} {a b : ℝ}

theorem compactSpace_pieceSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) (x₀ : Ambient B) :
    CompactSpace (slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :=
  isCompact_iff_compactSpace.mp (isCompact_pieceSlab hf hab hreg hint x₀)

theorem connectedSpace_pieceSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    {x₀ : Ambient B} (hx₀ : x₀ ∈ slabSet (ambientFun f) a b) :
    ConnectedSpace (slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :=
  isConnected_iff_connectedSpace.mp (isConnected_pieceSlab hf hab hreg hx₀)

theorem exists_annulus_planarBase (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun f) a b)
    (hnc : ∀ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀,
      mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f (ambientVal y) ≠ 0)
    (ha : ∃ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀, ambientFun f y = a)
    (hb : ∃ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀, ambientFun f y = b) :
    ∃ (Q : PlanarBase.{u} 2)
      (h : Q.surface.Carrier = slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b),
      (∀ x, pieceFun f (componentOpens hf hab hreg x₀) (cast h x).val ∈ Icc a b) ∧
      (∀ t, pieceFun f (componentOpens hf hab hreg x₀)
        (cast h (Q.collar 1 (t, halfZero))).val = a) ∧
      ∀ t, pieceFun f (componentOpens hf hab hreg x₀)
        (cast h (Q.collar 0 (t, halfZero))).val = b := by
  let C := shiftAtlas (pieceAtlas hf hab hreg x₀)
  have hc := compactSpace_pieceSlab hf hab hreg hint x₀
  have hcn := connectedSpace_pieceSlab hf hab hreg hx₀
  obtain ⟨e, h1, h2, h3⟩ := exists_annulus_pieceSlab_shift hf hab hreg hint hx₀ hnc ha hb
  refine ⟨@transportBase 2 annulusPlanarBase.{u} _ _ C.toChartedSpace C.isManifold _ hc _ hcn e,
    rfl, fun x => ?_, h2, h3⟩
  exact (mem_slabSet_iff hab.le x.val).mp x.2

end AnnulusPiece

section Disc

def planeToE2 : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr

def discScale (R : ℝ) (z : discSet.{u}) : E2 := (R / 3) • planeToE2 z.val.down

theorem norm_discScale {R : ℝ} (hR : 0 < R) (z : discSet.{u}) : ‖discScale R z‖ ≤ R := by
  have hz := (mem_discSet_iff z.val).mp z.2
  rw [discScale, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (by positivity)]
  calc R / 3 * ‖z.val.down‖ ≤ R / 3 * 3 := by gcongr
    _ = R := by ring

theorem contMDiff_discScale (R : ℝ) :
    ContMDiff (𝓡∂ 2) 𝓘(ℝ, E2) ∞ (discScale.{u} R) := by
  have h1 : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ (fun z : discSet.{u} => z.val.down) :=
    (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm.contMDiff.comp discAtlas.contMDiff_subtype_val
  have h2 : ContDiff ℝ ∞ (fun w : ℂ => (R / 3) • planeToE2 w) :=
    planeToE2.toContinuousLinearEquiv.contDiff.const_smul (R / 3)
  exact h2.contMDiff.comp h1

variable {f : B.Carrier → ℝ} {a b : ℝ}
  (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
  (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
  (x₀ : Ambient B) {R : ℝ}
  (χ : PartialDiffeomorph 𝓘(ℝ, E2) (SurfaceModel.model B.kind) E2 B.Carrier ∞)

theorem exists_piece_of_mem_ball
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b)
    {w : E2} (hw : w ∈ closedBall 0 R) :
    ∃ y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b,
      opensVal _ y.val = χ w := by
  have h : χ w ∈ χ '' closedBall 0 R := mem_image_of_mem χ hw
  rw [himg] at h
  obtain ⟨y, hy, hyw⟩ := h
  exact ⟨⟨y, hy⟩, hyw⟩

def discToPiece (hR : 0 < R)
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b)
    (z : discSet.{u}) : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b :=
  Classical.choose (exists_piece_of_mem_ball hf hab hreg x₀ χ himg
    (mem_closedBall_zero_iff.mpr (norm_discScale hR z)))

theorem opensVal_discToPiece (hR : 0 < R)
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b)
    (z : discSet.{u}) :
    opensVal _ (discToPiece hf hab hreg x₀ χ hR himg z).val = χ (discScale R z) :=
  Classical.choose_spec (exists_piece_of_mem_ball hf hab hreg x₀ χ himg
    (mem_closedBall_zero_iff.mpr (norm_discScale hR z)))

theorem exists_ball_of_piece
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b)
    (y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :
    ∃ w ∈ closedBall (0 : E2) R, χ w = opensVal _ y.val := by
  have h : opensVal _ y.val ∈ χ '' closedBall 0 R := by
    rw [himg]
    exact mem_image_of_mem _ y.2
  exact h

theorem symm_opensVal_mem_ball (hball : closedBall 0 R ⊆ χ.source)
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b)
    (y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :
    χ.symm (opensVal _ y.val) ∈ closedBall (0 : E2) R ∧ opensVal _ y.val ∈ χ.target := by
  obtain ⟨w, hw, hwy⟩ := exists_ball_of_piece hf hab hreg x₀ χ himg y
  have hl : χ.symm (χ w) = w := χ.left_inv (hball hw)
  rw [← hwy, hl]
  exact ⟨hw, χ.map_source (hball hw)⟩

def pieceToDisc (hR : 0 < R) (hball : closedBall 0 R ⊆ χ.source)
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b)
    (y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) : discSet.{u} :=
  ⟨ULift.up (planeToE2.symm ((3 / R) • χ.symm (opensVal _ y.val))), by
    rw [mem_discSet_iff]
    have h := mem_closedBall_zero_iff.mp (symm_opensVal_mem_ball hf hab hreg x₀ χ hball himg y).1
    change ‖planeToE2.symm ((3 / R) • χ.symm (opensVal _ y.val))‖ ≤ 3
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc 3 / R * ‖χ.symm (opensVal _ y.val)‖ ≤ 3 / R * R := by gcongr
      _ = 3 := by field_simp⟩

theorem pieceToDisc_discToPiece (hR : 0 < R) (hball : closedBall 0 R ⊆ χ.source)
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b)
    (z : discSet.{u}) :
    pieceToDisc hf hab hreg x₀ χ hR hball himg (discToPiece hf hab hreg x₀ χ hR himg z) = z := by
  apply Subtype.ext
  apply ULift.ext
  change planeToE2.symm ((3 / R) • χ.symm (opensVal _
    (discToPiece hf hab hreg x₀ χ hR himg z).val)) = z.val.down
  rw [opensVal_discToPiece]
  have hl : χ.symm (χ (discScale R z)) = discScale R z :=
    χ.left_inv (hball (mem_closedBall_zero_iff.mpr (norm_discScale hR z)))
  rw [hl, discScale, smul_smul, div_mul_div_comm, mul_comm 3 R, div_self (by positivity),
    one_smul, LinearIsometryEquiv.symm_apply_apply]

theorem discToPiece_pieceToDisc (hR : 0 < R) (hball : closedBall 0 R ⊆ χ.source)
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b)
    (y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :
    discToPiece hf hab hreg x₀ χ hR himg (pieceToDisc hf hab hreg x₀ χ hR hball himg y) = y := by
  apply Subtype.ext
  apply (isOpenEmbedding_opensVal _).injective
  rw [opensVal_discToPiece]
  change χ ((R / 3) • planeToE2 (planeToE2.symm ((3 / R) • χ.symm (opensVal _ y.val)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, smul_smul, div_mul_div_comm, mul_comm R 3,
    div_self (by positivity), one_smul]
  exact χ.right_inv (symm_opensVal_mem_ball hf hab hreg x₀ χ hball himg y).2

theorem contMDiff_discToPiece (hR : 0 < R) (hball : closedBall 0 R ⊆ χ.source)
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :
    letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (discToPiece hf hab hreg x₀ χ hR himg) := by
  let := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
  refine ((shiftAtlas (pieceAtlas hf hab hreg x₀)).contMDiff_iff_subtype_val _).mpr ?_
  rw [← contMDiffOn_univ, contMDiffOn_opens_ambient_iff, contMDiffOn_univ]
  have h : ContMDiff (𝓡∂ 2) (SurfaceModel.model B.kind) ∞ (fun z => χ (discScale.{u} R z)) :=
    χ.contMDiffOn.comp_contMDiff (contMDiff_discScale R)
      fun z => hball (mem_closedBall_zero_iff.mpr (norm_discScale hR z))
  refine h.congr fun z => ?_
  exact opensVal_discToPiece hf hab hreg x₀ χ hR himg z

theorem contMDiff_pieceToDisc (hR : 0 < R) (hball : closedBall 0 R ⊆ χ.source)
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :
    letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (pieceToDisc hf hab hreg x₀ χ hR hball himg) := by
  let := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
  refine (discAtlas.contMDiff_iff_subtype_val _).mpr ?_
  have h1 : ContMDiff (𝓡∂ 2) (SurfaceModel.model B.kind) ∞
      (fun y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b => opensVal _ y.val) :=
    (contMDiff_opensVal _).comp (shiftAtlas (pieceAtlas hf hab hreg x₀)).contMDiff_subtype_val
  have h2 := χ.symm.contMDiffOn.comp_contMDiff h1
    fun y => (symm_opensVal_mem_ball hf hab hreg x₀ χ hball himg y).2
  have h3 : ContDiff ℝ ∞ (fun w : E2 => planeToE2.symm ((3 / R) • w)) :=
    planeToE2.symm.toContinuousLinearEquiv.contDiff.comp (contDiff_id.const_smul (3 / R))
  exact (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).contMDiff.comp (h3.contMDiff.comp h2)

def discPieceDiffeo (hR : 0 < R) (hball : closedBall 0 R ⊆ χ.source)
    (himg : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :
    letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
    discSet.{u} ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b :=
  letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
  { toFun := discToPiece hf hab hreg x₀ χ hR himg
    invFun := pieceToDisc hf hab hreg x₀ χ hR hball himg
    left_inv := pieceToDisc_discToPiece hf hab hreg x₀ χ hR hball himg
    right_inv := discToPiece_pieceToDisc hf hab hreg x₀ χ hR hball himg
    contMDiff_toFun := contMDiff_discToPiece hf hab hreg x₀ χ hR hball himg
    contMDiff_invFun := contMDiff_pieceToDisc hf hab hreg x₀ χ hR hball himg }

end Disc

section DiscPiece

theorem shiftAtlas_isBoundaryPoint_iff {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E2 H} [TopologicalSpace M] [ChartedSpace H M] {K : Set M}
    (C : SmoothBoundaryAtlas I 2 K) (x : K) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ E2 _ _ (EuclideanHalfSpace 2) _ (𝓡∂ 2) K _
      (shiftAtlas C).toChartedSpace x ↔
    @ModelWithCorners.IsBoundaryPoint ℝ _ E2 _ _ (EuclideanHalfSpace 2) _ (𝓡∂ 2) K _
      C.toChartedSpace x := by
  rw [(shiftAtlas C).isBoundaryPoint_iff, C.isBoundaryPoint_iff]
  change (C.ambientChart x x.val + (1 - C.ambientChart x x.val 1) • EuclideanSpace.single 1 1 :
    E2) 0 = 0 ↔ _
  simp

variable {f : B.Carrier → ℝ} {a b : ℝ}

theorem opensVal_image_pieceSlab (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) (x₀ : Ambient B) :
    opensVal _ '' slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b =
      connectedComponentIn (f ⁻¹' Icc a b) (ambientVal x₀) := by
  have h1 : opensVal (componentOpens hf hab hreg x₀) = ambientVal ∘ Subtype.val := rfl
  have h2 : ambientVal '' slabSet (ambientFun f) a b = f ⁻¹' Icc a b := by
    rw [slabSet_eq hab.le]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨toAmbient ⟨y, hint y hy.1⟩, hy, rfl⟩
  rw [h1, image_comp, val_image_pieceSlab, image_connectedComponentIn_of_isEmbedding
    isOpenEmbedding_ambientVal.isEmbedding, h2]

theorem pieceSlab_boundary_iff (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (x₀ : Ambient B) (x : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :
    letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
    (𝓡∂ 2).IsBoundaryPoint x ↔
      pieceFun f (componentOpens hf hab hreg x₀) x.val = a ∨
        pieceFun f (componentOpens hf hab hreg x₀) x.val = b := by
  rw [shiftAtlas_isBoundaryPoint_iff]
  exact slab_isBoundaryPoint x

theorem pos_radius_of_image_eq (hf : Continuous f) {p : B.Carrier} (hp : f p ∈ Ioo a b) {R : ℝ}
    (χ : PartialDiffeomorph 𝓘(ℝ, E2) (SurfaceModel.model B.kind) E2 B.Carrier ∞)
    (hχ0 : χ 0 = p) (hball : closedBall 0 R ⊆ χ.source)
    (himg : χ '' closedBall 0 R = connectedComponentIn (f ⁻¹' Icc a b) p) : 0 < R := by
  have hpK : p ∈ connectedComponentIn (f ⁻¹' Icc a b) p :=
    mem_connectedComponentIn (Ioo_subset_Icc_self hp)
  have hR0 : 0 ≤ R := by
    by_contra h
    rw [closedBall_eq_empty.mpr (not_le.mp h), image_empty] at himg
    rw [← himg] at hpK
    exact hpK
  have h0 : (0 : E2) ∈ χ.source := hball (mem_closedBall_self hR0)
  have hev : ∀ᶠ w in 𝓝 (0 : E2), w ∈ χ.source ∧ f (χ w) ∈ Ioo a b := by
    refine Filter.Eventually.and (χ.open_source.mem_nhds h0) ?_
    have hc : ContinuousAt (fun w => f (χ w)) 0 :=
      hf.continuousAt.comp (χ.contMDiffOn.continuousOn.continuousAt (χ.open_source.mem_nhds h0))
    have hIoo : Ioo a b ∈ 𝓝 (f (χ 0)) := by
      rw [hχ0]
      exact isOpen_Ioo.mem_nhds hp
    exact hc hIoo
  obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hpre : IsPreconnected (χ '' ball (0 : E2) r) :=
    (convex_ball (0 : E2) r).isPreconnected.image _
      (χ.contMDiffOn.continuousOn.mono fun w hw => (hsub w hw).1)
  have hsubK : χ '' ball (0 : E2) r ⊆ connectedComponentIn (f ⁻¹' Icc a b) p := by
    refine hpre.subset_connectedComponentIn ⟨0, mem_ball_self hr, hχ0⟩ ?_
    rintro z ⟨w, hw, rfl⟩
    exact Ioo_subset_Icc_self (hsub w hw).2
  set w : E2 := (r / 2) • EuclideanSpace.single 0 1
  have hwn : ‖w‖ = r / 2 := by
    rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_of_nonneg (by linarith)]
  have hw : w ∈ ball (0 : E2) r := by
    rw [mem_ball_zero_iff, hwn]
    linarith
  have hχw : χ w ∈ χ '' closedBall 0 R := by
    rw [himg]
    exact hsubK (mem_image_of_mem _ hw)
  obtain ⟨w', hw', hww'⟩ := hχw
  have heq : w' = w := χ.injOn (hball hw') (hsub w hw).1 hww'
  rw [heq, mem_closedBall_zero_iff, hwn] at hw'
  linarith

end DiscPiece

section MorseSlab

variable (D : BaseMorseData B)

theorem level_castSucc_lt_succ (i : Fin D.m) : D.level i.castSucc < D.level i.succ :=
  D.level_strictMono Fin.castSucc_lt_succ

theorem mfderiv_ne_zero_of_eq_level (j : Fin (D.m + 1)) {y : B.Carrier}
    (hy : D.f y = D.level j) : mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0 := by
  intro h
  have h1 := D.field_unit j y (by rw [hy, sub_self, abs_zero]; linarith [D.κ_pos])
  rw [h] at h1
  have h2 : (0 : ℝ) = 1 := h1
  norm_num at h2

theorem slab_regular (i : Fin D.m) :
    ∀ y, D.f y = D.level i.castSucc ∨ D.f y = D.level i.succ →
      mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f y ≠ 0 := by
  rintro y (hy | hy)
  · exact mfderiv_ne_zero_of_eq_level D _ hy
  · exact mfderiv_ne_zero_of_eq_level D _ hy

theorem slab_interior (i : Fin D.m) :
    ∀ y, D.level i.castSucc ≤ D.f y → y ∈ interiorOpens B := fun y hy =>
  D.isInteriorPoint_of_pos (x := y) (D.level_zero_pos.trans_le
    ((D.level_strictMono.monotone (Fin.zero_le _)).trans hy))

abbrev slabOpens (i : Fin D.m) (x₀ : Ambient B) : Opens (Ambient B) :=
  componentOpens D.smooth (level_castSucc_lt_succ D i) (slab_regular D i) x₀

theorem eq_or_eq_of_two_valued {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {g : X → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b) (h : ∀ x, g x = a ∨ g x = b) :
    (∀ x, g x = a) ∨ ∀ x, g x = b := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hne
  have h₁ : g x₁ = b := (h x₁).resolve_left hx₁
  have h₂ : g x₂ = a := (h x₂).resolve_right hx₂
  have hm : (a + b) / 2 ∈ range g :=
    (isPreconnected_range hg).Icc_subset ⟨x₂, h₂⟩ ⟨x₁, h₁⟩ ⟨by linarith, by linarith⟩
  obtain ⟨x, hx⟩ := hm
  rcases h x with h' | h' <;> rw [h'] at hx <;> linarith

theorem exists_disc_planarBase {p : B.Carrier} (hp : p ∈ D.crit)
    (hidx : sigNeg (chartHessianAt
      (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
      (extChartAt (SurfaceModel.model B.kind) p p)) ≠ 1)
    (i : Fin D.m) (hpi : D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ)) :
    ∃ (x₀ : Ambient B) (Q : PlanarBase.{u} 1)
      (h : Q.surface.Carrier =
        slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ)),
      ambientVal x₀ = p ∧
        ((∀ t, pieceFun D.f (slabOpens D i x₀) (cast h (Q.collar 0 (t, halfZero))).val =
            D.level i.castSucc) ∨
          ∀ t, pieceFun D.f (slabOpens D i x₀) (cast h (Q.collar 0 (t, halfZero))).val =
            D.level i.succ) := by
  obtain ⟨R, χ, hχ0, hball, himg⟩ := D.thin p hp hidx i hpi
  have hab := level_castSucc_lt_succ D i
  have hreg := slab_regular D i
  have hint := slab_interior D i
  set x₀ : Ambient B := toAmbient ⟨p, hint p hpi.1.le⟩
  have hR : 0 < R := pos_radius_of_image_eq D.smooth.continuous hpi χ hχ0 hball himg
  have himg' : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀))
        (D.level i.castSucc) (D.level i.succ) := by
    rw [himg, opensVal_image_pieceSlab D.smooth hab hreg hint x₀]
    rfl
  have hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ) :=
    (mem_slabSet_iff hab.le x₀).mpr (Ioo_subset_Icc_self hpi)
  let C := shiftAtlas (pieceAtlas D.smooth hab hreg x₀)
  have hc := compactSpace_pieceSlab D.smooth hab hreg hint x₀
  have hcn := connectedSpace_pieceSlab D.smooth hab hreg hx₀
  let E := discPieceDiffeo D.smooth hab hreg x₀ χ hR hball himg'
  let Q := @transportBase 1 (discPlanarBase.{u} 1) _ _ C.toChartedSpace C.isManifold _ hc _ hcn E
  refine ⟨x₀, Q, rfl, rfl, ?_⟩
  have hcont : Continuous fun t : Circle =>
      pieceFun D.f (componentOpens D.smooth hab hreg x₀) (Q.collar 0 (t, halfZero)).val := by
    have hcol : Continuous fun t : Circle => Q.collar 0 (t, halfZero) := by
      refine (Q.collar 0).contMDiffOn.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) fun t => ?_
      rw [Q.source_eq 0]
      exact halfZero_mem_circleCollarSource t
    exact (contMDiff_pieceFun D.smooth _).continuous.comp (continuous_subtype_val.comp hcol)
  refine eq_or_eq_of_two_valued hcont hab fun t => ?_
  have hbd := Q.boundary_zero 0 t
  exact (pieceSlab_boundary_iff D.smooth hab hreg x₀ (Q.collar 0 (t, halfZero))).mp hbd

end MorseSlab

section LevelsMet

variable {f : B.Carrier → ℝ} {a b : ℝ}

theorem exists_open_inter_slab_eq_component
    (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    {x₀ : Ambient B} (hx₀ : x₀ ∈ slabSet (ambientFun f) a b) :
    ∃ W : Set (Ambient B), IsOpen W ∧
      W ∩ slabSet (ambientFun f) a b = connectedComponentIn (slabSet (ambientFun f) a b) x₀ := by
  let := (ambientSlabAtlas hf hab hreg).toChartedSpace
  have : LocallyConnectedSpace (slabSet (ambientFun f) a b) :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) _
  have ho : IsOpen (connectedComponent (⟨x₀, hx₀⟩ : slabSet (ambientFun f) a b)) :=
    isOpen_connectedComponent
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp ho
  refine ⟨W, hW, ?_⟩
  rw [connectedComponentIn_eq_image hx₀, ← hWeq]
  ext z
  constructor
  · rintro ⟨hzW, hzS⟩
    exact ⟨⟨z, hzS⟩, hzW, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.2⟩

theorem exists_min_level_mem_component
    (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B)
    {x₀ : Ambient B} (hx₀ : x₀ ∈ slabSet (ambientFun f) a b)
    (hnmin : ∀ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀,
      ¬ IsLocalMin (ambientFun f) y) :
    ∃ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀, ambientFun f y = a := by
  set K := connectedComponentIn (slabSet (ambientFun f) a b) x₀
  have hK : IsCompact K := isCompact_component hf hab hint x₀
  have hne : K.Nonempty := ⟨x₀, mem_connectedComponentIn hx₀⟩
  obtain ⟨y, hyK, hymin⟩ := hK.exists_isMinOn hne (contMDiff_ambientFun hf).continuous.continuousOn
  have hyS : y ∈ slabSet (ambientFun f) a b := connectedComponentIn_subset _ _ hyK
  have hyab := (mem_slabSet_iff hab.le y).mp hyS
  refine ⟨y, hyK, ?_⟩
  by_contra hya
  have hlt : a < ambientFun f y := lt_of_le_of_ne hyab.1 (Ne.symm hya)
  obtain ⟨W, hW, hWeq⟩ := exists_open_inter_slab_eq_component hf hab hreg hx₀
  have hyW : y ∈ W := by
    have h : y ∈ W ∩ slabSet (ambientFun f) a b := hWeq ▸ hyK
    exact h.1
  apply hnmin y hyK
  have hO : W ∩ {z | a < ambientFun f z} ∈ 𝓝 y :=
    (hW.inter (isOpen_lt continuous_const (contMDiff_ambientFun hf).continuous)).mem_nhds
      ⟨hyW, hlt⟩
  filter_upwards [hO] with z hz
  by_cases hzb : ambientFun f z ≤ b
  · have hzS : z ∈ slabSet (ambientFun f) a b := (mem_slabSet_iff hab.le z).mpr ⟨hz.2.le, hzb⟩
    have hzK : z ∈ K := by
      have h : z ∈ W ∩ slabSet (ambientFun f) a b := ⟨hz.1, hzS⟩
      rw [hWeq] at h
      exact h
    exact hymin hzK
  · exact (hyab.2.trans (not_le.mp hzb).le)

theorem exists_max_level_mem_component
    (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B)
    {x₀ : Ambient B} (hx₀ : x₀ ∈ slabSet (ambientFun f) a b)
    (hnmax : ∀ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀,
      ¬ IsLocalMax (ambientFun f) y) :
    ∃ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀, ambientFun f y = b := by
  set K := connectedComponentIn (slabSet (ambientFun f) a b) x₀
  have hK : IsCompact K := isCompact_component hf hab hint x₀
  have hne : K.Nonempty := ⟨x₀, mem_connectedComponentIn hx₀⟩
  obtain ⟨y, hyK, hymax⟩ := hK.exists_isMaxOn hne (contMDiff_ambientFun hf).continuous.continuousOn
  have hyS : y ∈ slabSet (ambientFun f) a b := connectedComponentIn_subset _ _ hyK
  have hyab := (mem_slabSet_iff hab.le y).mp hyS
  refine ⟨y, hyK, ?_⟩
  by_contra hyb
  have hlt : ambientFun f y < b := lt_of_le_of_ne hyab.2 hyb
  obtain ⟨W, hW, hWeq⟩ := exists_open_inter_slab_eq_component hf hab hreg hx₀
  have hyW : y ∈ W := by
    have h : y ∈ W ∩ slabSet (ambientFun f) a b := hWeq ▸ hyK
    exact h.1
  apply hnmax y hyK
  have hO : W ∩ {z | ambientFun f z < b} ∈ 𝓝 y :=
    (hW.inter (isOpen_lt (contMDiff_ambientFun hf).continuous continuous_const)).mem_nhds
      ⟨hyW, hlt⟩
  filter_upwards [hO] with z hz
  by_cases hza : a ≤ ambientFun f z
  · have hzS : z ∈ slabSet (ambientFun f) a b := (mem_slabSet_iff hab.le z).mpr ⟨hza, hz.2.le⟩
    have hzK : z ∈ K := by
      have h : z ∈ W ∩ slabSet (ambientFun f) a b := ⟨hz.1, hzS⟩
      rw [hWeq] at h
      exact h
    exact hymax hzK
  · exact ((not_le.mp hza).le.trans hyab.1)

theorem not_isLocalMin_of_mfderiv_ne_zero
    (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) {y : Ambient B}
    (hy : mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f (ambientVal y) ≠ 0) :
    ¬ IsLocalMin (ambientFun f) y ∧ ¬ IsLocalMax (ambientFun f) y := by
  have h := mfderiv_ambientFun_ne_zero hf y hy
  refine ⟨fun hmin => h ?_, fun hmax => h ?_⟩
  · exact isCriticalPointAt_of_isLocalMin (I := 𝓘(ℝ, E2)) hmin
      BoundarylessManifold.isInteriorPoint
  · exact isCriticalPointAt_of_isLocalMax (I := 𝓘(ℝ, E2)) hmax
      BoundarylessManifold.isInteriorPoint

theorem exists_annulus_planarBase_of_regular
    (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
    (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun f) a b)
    (hnc : ∀ y ∈ connectedComponentIn (slabSet (ambientFun f) a b) x₀,
      mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f (ambientVal y) ≠ 0) :
    ∃ (Q : PlanarBase.{u} 2)
      (h : Q.surface.Carrier = slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b),
      (∀ x, pieceFun f (componentOpens hf hab hreg x₀) (cast h x).val ∈ Icc a b) ∧
      (∀ t, pieceFun f (componentOpens hf hab hreg x₀)
        (cast h (Q.collar 1 (t, halfZero))).val = a) ∧
      ∀ t, pieceFun f (componentOpens hf hab hreg x₀)
        (cast h (Q.collar 0 (t, halfZero))).val = b :=
  exists_annulus_planarBase hf hab hreg hint hx₀ hnc
    (exists_min_level_mem_component hf hab hreg hint hx₀ fun y hy =>
      (not_isLocalMin_of_mfderiv_ne_zero hf (hnc y hy)).1)
    (exists_max_level_mem_component hf hab hreg hint hx₀ fun y hy =>
      (not_isLocalMin_of_mfderiv_ne_zero hf (hnc y hy)).2)

end LevelsMet

section Recollar

variable {k : ℕ}

def recollarBase (P : PlanarBase.{u} k)
    (c : Fin k → PartialDiffeomorph circleCollarModel (SurfaceModel.model P.surface.kind)
      (Circle × EuclideanHalfSpace 1) P.surface.Carrier ∞)
    (hsrc : ∀ j, (c j).source = circleCollarSource)
    (hzero : ∀ j t, c j (t, halfZero) = P.collar j (t, halfZero))
    (hdisj : Pairwise fun i j => Disjoint (c i).target (c j).target) : PlanarBase.{u} k where
  surface := P.surface
  collar := c
  source_eq := hsrc
  boundary_zero j t := by
    rw [hzero]
    exact P.boundary_zero j t
  disjoint := hdisj
  boundary_exhausted := by
    rw [P.boundary_exhausted]
    simp only [hzero]
  embedding := P.embedding
  isSmoothEmbedding := P.isSmoothEmbedding
  range_embedding := P.range_embedding
  embedding_collar j t := by
    rw [hzero]
    exact P.embedding_collar j t

end Recollar

section Finite

theorem finite_components_of_compact {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [LocallyConnectedSpace X] : Finite (ConnectedComponents X) := by
  have hcover : (univ : Set X) ⊆ ⋃ x : X, connectedComponent x := by
    intro x hx
    exact mem_iUnion.mpr ⟨x, mem_connectedComponent⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => connectedComponent x)
    (fun x => isOpen_connectedComponent) hcover
  have hsurj : Surjective fun x : t => ConnectedComponents.mk (x : X) := by
    intro c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    have hy := ht (mem_univ y)
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    exact ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq hyx)
  exact Finite.of_surjective _ hsurj

end Finite

section HalfCollar

variable {f : B.Carrier → ℝ} {a b : ℝ}
  (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
  (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
  (x₀ : Ambient B)
  (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
    B.Carrier ∞)
  (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) (ε : ℝ)

theorem halfSpaceOneLift_val_zero (h : EuclideanHalfSpace 1) :
    DifferentialGeometry.Topology.Manifold.halfSpaceOneLift (h.val 0) = h := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  change max (h.val 0) 0 = h.val 0
  exact max_eq_left h.2

def collarClamp (q : Circle × EuclideanHalfSpace 1) : ℝ := if q.2.val 0 < 1 then q.2.val 0 else 0

theorem collarClamp_nonneg (q : Circle × EuclideanHalfSpace 1) : 0 ≤ collarClamp q := by
  unfold collarClamp
  split_ifs
  · exact q.2.2
  · exact le_rfl

theorem collarClamp_lt_one (q : Circle × EuclideanHalfSpace 1) : collarClamp q < 1 := by
  unfold collarClamp
  split_ifs with h
  · exact h
  · exact one_pos

theorem collarClamp_of_mem {q : Circle × EuclideanHalfSpace 1} (hq : q ∈ circleCollarSource) :
    collarClamp q = q.2.val 0 := by
  have hq' : q.2.val 0 < 1 := hq
  simp only [collarClamp, hq', ↓reduceIte]

def halfCollarFun
    (hin : ∀ t s, 0 ≤ s → s < 1 → ∃ y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b,
      opensVal _ y.val = c (σ t, ε * s))
    (q : Circle × EuclideanHalfSpace 1) :
    slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b :=
  Classical.choose (hin q.1 (collarClamp q) (collarClamp_nonneg q) (collarClamp_lt_one q))

theorem opensVal_halfCollarFun
    (hin : ∀ t s, 0 ≤ s → s < 1 → ∃ y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b,
      opensVal _ y.val = c (σ t, ε * s))
    (q : Circle × EuclideanHalfSpace 1) :
    opensVal _ (halfCollarFun hf hab hreg x₀ c σ ε hin q).val = c (σ q.1, ε * collarClamp q) :=
  Classical.choose_spec (hin q.1 (collarClamp q) (collarClamp_nonneg q) (collarClamp_lt_one q))

def halfCollarInv (y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) :
    Circle × EuclideanHalfSpace 1 :=
  (σ.symm (c.symm (opensVal _ y.val)).1,
    DifferentialGeometry.Topology.Manifold.halfSpaceOneLift (ε * (c.symm (opensVal _ y.val)).2))

theorem eps_mul_eps {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (s : ℝ) : ε * (ε * s) = s := by
  rcases hε with h | h <;> rw [h] <;> ring

theorem abs_eps_mul {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (s : ℝ) : |ε * s| = |s| := by
  rcases hε with h | h <;> rw [h] <;> simp

def halfCollar (hcs : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (hε : ε = 1 ∨ ε = -1)
    (hin : ∀ t s, 0 ≤ s → s < 1 → ∃ y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b,
      opensVal _ y.val = c (σ t, ε * s))
    (hside : ∀ y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b,
      opensVal _ y.val ∈ c.target → 0 ≤ ε * (c.symm (opensVal _ y.val)).2) :
    letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
    PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) ∞ :=
  letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
  have hsrc (q : Circle × EuclideanHalfSpace 1) (hq : q ∈ circleCollarSource) :
      (σ q.1, ε * q.2.val 0) ∈ c.source := by
    rw [hcs]
    have h0 : 0 ≤ q.2.val 0 := q.2.2
    have h1 : q.2.val 0 < 1 := hq
    have habs := abs_eps_mul hε (q.2.val 0)
    rw [abs_of_nonneg h0] at habs
    exact abs_lt.mp (habs.trans_lt h1)
  have hval (q : Circle × EuclideanHalfSpace 1) (hq : q ∈ circleCollarSource) :
      opensVal _ (halfCollarFun hf hab hreg x₀ c σ ε hin q).val = c (σ q.1, ε * q.2.val 0) := by
    rw [opensVal_halfCollarFun, collarClamp_of_mem hq]
  { toFun := halfCollarFun hf hab hreg x₀ c σ ε hin
    invFun := halfCollarInv hf hab hreg x₀ c σ ε
    source := circleCollarSource
    target := {y | opensVal _ y.val ∈ c.target}
    map_source' := fun q hq => by
      change opensVal _ (halfCollarFun hf hab hreg x₀ c σ ε hin q).val ∈ c.target
      rw [hval q hq]
      exact c.map_source (hsrc q hq)
    map_target' := fun y hy => by
      have h := c.map_target hy
      rw [hcs] at h
      change max (ε * (c.symm (opensVal _ y.val)).2) 0 < 1
      refine max_lt ?_ one_pos
      have habs := abs_eps_mul hε (c.symm (opensVal _ y.val)).2
      exact (le_abs_self _).trans_lt (habs ▸ abs_lt.mpr h)
    left_inv' := fun q hq => by
      have hl : c.symm (c (σ q.1, ε * q.2.val 0)) = (σ q.1, ε * q.2.val 0) :=
        c.left_inv (hsrc q hq)
      change (σ.symm (c.symm (opensVal _ (halfCollarFun hf hab hreg x₀ c σ ε hin q).val)).1,
        DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
          (ε * (c.symm (opensVal _ (halfCollarFun hf hab hreg x₀ c σ ε hin q).val)).2)) = q
      rw [hval q hq, hl]
      simp only [Diffeomorph.symm_apply_apply, eps_mul_eps hε, halfSpaceOneLift_val_zero]
    right_inv' := fun y hy => by
      have hs := hside y hy
      have hr : c (c.symm (opensVal _ y.val)) = opensVal _ y.val := c.right_inv hy
      have hmem : halfCollarInv hf hab hreg x₀ c σ ε y ∈ circleCollarSource := by
        have h := c.map_target hy
        rw [hcs] at h
        change max (ε * (c.symm (opensVal _ y.val)).2) 0 < 1
        refine max_lt ?_ one_pos
        have habs := abs_eps_mul hε (c.symm (opensVal _ y.val)).2
        exact (le_abs_self _).trans_lt (habs ▸ abs_lt.mpr h)
      apply Subtype.ext
      apply (isOpenEmbedding_opensVal _).injective
      rw [hval _ hmem]
      change c (σ (σ.symm (c.symm (opensVal _ y.val)).1),
        ε * max (ε * (c.symm (opensVal _ y.val)).2) 0) = opensVal _ y.val
      rw [max_eq_left hs, eps_mul_eps hε, Diffeomorph.apply_symm_apply]
      exact hr
    open_source := isOpen_lt
      ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
      continuous_const
    open_target := c.open_target.preimage
      ((isOpenEmbedding_opensVal _).continuous.comp continuous_subtype_val)
    contMDiffOn_toFun := by
      refine ((shiftAtlas (pieceAtlas hf hab hreg x₀)).contMDiffOn_iff_subtype_val _ _).mpr ?_
      rw [contMDiffOn_opens_ambient_iff]
      have hg : ContMDiff circleCollarModel ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun q : Circle × EuclideanHalfSpace 1 => (σ q.1, ε * q.2.val 0)) :=
        (σ.contMDiff.comp contMDiff_fst).prodMk ((contMDiff_const.mul
          DifferentialGeometry.Topology.Manifold.contMDiff_halfSpaceOneCoordinate).comp
            contMDiff_snd)
      refine (c.contMDiffOn.comp hg.contMDiffOn fun q hq => hsrc q hq).congr fun q hq => ?_
      exact hval q hq
    contMDiffOn_invFun := by
      have h1 : ContMDiff (𝓡∂ 2) (SurfaceModel.model B.kind) ∞
          (fun y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b =>
            opensVal _ y.val) :=
        (contMDiff_opensVal _).comp (shiftAtlas (pieceAtlas hf hab hreg x₀)).contMDiff_subtype_val
      have h2 : ContMDiffOn (𝓡∂ 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun y : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b =>
            c.symm (opensVal _ y.val))
          {y | opensVal (componentOpens hf hab hreg x₀) y.val ∈ c.target} :=
        c.symm.contMDiffOn.comp h1.contMDiffOn fun y hy => hy
      refine ContMDiffOn.prodMk (σ.symm.contMDiff.comp_contMDiffOn
        (contMDiff_fst.comp_contMDiffOn h2)) ?_
      refine DifferentialGeometry.Topology.Manifold.contMDiffOn_halfSpaceOneLift.comp
        ((contMDiff_const.mul contMDiff_id).comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn h2))
        fun y hy => hside y hy }

end HalfCollar

section Bicollar

variable (D : BaseMorseData B)

theorem eq_of_bicollar_eq {i : Fin (D.m + 1)}
    {c₁ c₂ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
      B.Carrier ∞}
    (hf₁ : ∀ t s, -1 < s → s < 1 → D.f (c₁ (t, s)) = D.level i + D.κ * s)
    (hf₂ : ∀ t s, -1 < s → s < 1 → D.f (c₂ (t, s)) = D.level i + D.κ * s)
    (hc₁ : ∀ t, IsMIntegralCurveOn (fun s => c₁ (t, s)) (fun x => D.κ • D.field x) (Ioo (-1) 1))
    (hc₂ : ∀ t, IsMIntegralCurveOn (fun s => c₂ (t, s)) (fun x => D.κ • D.field x) (Ioo (-1) 1))
    {t₁ t₂ : Circle} {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Ioo (-1 : ℝ) 1) (hs₂ : s₂ ∈ Ioo (-1 : ℝ) 1)
    (heq : c₁ (t₁, s₁) = c₂ (t₂, s₂)) :
    s₁ = s₂ ∧ c₁ (t₁, 0) = c₂ (t₂, 0) := by
  have hss : s₁ = s₂ := by
    have hf₁ := hf₁ t₁ s₁ hs₁.1 hs₁.2
    have hf₂ := hf₂ t₂ s₂ hs₂.1 hs₂.2
    rw [heq] at hf₁
    have hκ := D.κ_pos
    have h : D.κ * s₁ = D.κ * s₂ := by linarith
    exact mul_left_cancel₀ hκ.ne' h
  refine ⟨hss, ?_⟩
  have hℓ : 2 * D.κ < D.level i :=
    D.two_κ_lt_level.trans_le (D.level_strictMono.monotone (Fin.zero_le i))
  have hint : ∀ r ∈ Ioo (-1 : ℝ) 1, (SurfaceModel.model B.kind).IsInteriorPoint (c₁ (t₁, r)) := by
    intro r hr
    apply D.isInteriorPoint_of_pos
    rw [hf₁ t₁ r hr.1 hr.2]
    nlinarith [D.κ_pos, hr.1]
  have hv : ContMDiff (SurfaceModel.model B.kind) (SurfaceModel.model B.kind).tangent 1
      (fun x => (⟨x, D.κ • D.field x⟩ :
        TangentBundle (SurfaceModel.model B.kind) B.Carrier)) :=
    (contMDiff_const.smul_section D.field_smooth).of_le (by norm_cast)
  have heq' : c₁ (t₁, s₁) = c₂ (t₂, s₁) := by rw [heq, hss]
  have h := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff hs₁ hint hv (hc₁ t₁) (hc₂ t₂) heq'
  exact h ⟨by norm_num, by norm_num⟩

end Bicollar

section CoreCut

variable (D : BaseMorseData B)
  (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
    B.Carrier ∞) (lam : ℝ)

open Classical in
def coreCutFun (p : Circle × ℝ) : D.core.Carrier :=
  if h : D.level 0 ≤ D.f (c (p.1, lam * p.2)) then ⟨c (p.1, lam * p.2), h⟩
  else Classical.choice inferInstance

theorem coreCutFun_val {p : Circle × ℝ} (hp : D.level 0 ≤ D.f (c (p.1, lam * p.2))) :
    (coreCutFun D c lam p).val = c (p.1, lam * p.2) := by
  simp only [coreCutFun, hp, ↓reduceDIte]

def coreCut (hcs : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hpos : ∀ t s, -1 < s → s < 1 → D.level 0 < D.f (c (t, lam * s))) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ) D.core.Carrier ∞ :=
  have hsrc (p : Circle × ℝ) (hp : -1 < p.2 ∧ p.2 < 1) : (p.1, lam * p.2) ∈ c.source := by
    rw [hcs]
    have h1 : |lam * p.2| < 1 := by
      rw [abs_mul, abs_of_pos hlam]
      have hp' : |p.2| < 1 := abs_lt.mpr hp
      nlinarith [abs_nonneg p.2]
    exact abs_lt.mp h1
  have hval (p : Circle × ℝ) (hp : -1 < p.2 ∧ p.2 < 1) :
      (coreCutFun D c lam p).val = c (p.1, lam * p.2) :=
    coreCutFun_val D c lam (hpos p.1 p.2 hp.1 hp.2).le
  have hcont : ContinuousOn (fun y : D.core.Carrier => c.symm y.val)
      {y : D.core.Carrier | y.val ∈ c.target} :=
    c.symm.contMDiffOn.continuousOn.comp continuous_subtype_val.continuousOn fun y hy => hy
  { toFun := coreCutFun D c lam
    invFun := fun y => ((c.symm y.val).1, (c.symm y.val).2 / lam)
    source := {p | -1 < p.2 ∧ p.2 < 1}
    target := {y | y.val ∈ c.target ∧ |(c.symm y.val).2| < lam}
    map_source' := fun p hp => by
      have hl : c.symm (c (p.1, lam * p.2)) = (p.1, lam * p.2) := c.left_inv (hsrc p hp)
      refine ⟨?_, ?_⟩
      · rw [hval p hp]
        exact c.map_source (hsrc p hp)
      · rw [hval p hp, hl, abs_mul, abs_of_pos hlam]
        have hp' : |p.2| < 1 := abs_lt.mpr hp
        nlinarith [abs_nonneg p.2]
    map_target' := fun y hy => by
      have h : |(c.symm y.val).2 / lam| < 1 := by
        rw [abs_div, abs_of_pos hlam, div_lt_one hlam]
        exact hy.2
      exact abs_lt.mp h
    left_inv' := fun p hp => by
      have hl : c.symm (c (p.1, lam * p.2)) = (p.1, lam * p.2) := c.left_inv (hsrc p hp)
      change ((c.symm (coreCutFun D c lam p).val).1,
        (c.symm (coreCutFun D c lam p).val).2 / lam) = p
      rw [hval p hp, hl]
      ext
      · rfl
      · change lam * p.2 / lam = p.2
        field_simp
    right_inv' := fun y hy => by
      have hr : c (c.symm y.val) = y.val := c.right_inv hy.1
      have hq : -1 < (c.symm y.val).2 / lam ∧ (c.symm y.val).2 / lam < 1 := by
        have h : |(c.symm y.val).2 / lam| < 1 := by
          rw [abs_div, abs_of_pos hlam, div_lt_one hlam]
          exact hy.2
        exact abs_lt.mp h
      apply Subtype.ext
      rw [hval _ hq]
      change c ((c.symm y.val).1, lam * ((c.symm y.val).2 / lam)) = y.val
      rw [mul_div_cancel₀ _ hlam.ne']
      exact hr
    open_source := (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
    open_target := by
      have ho : IsOpen {q : Circle × ℝ | |q.2| < lam} :=
        isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
      exact hcont.isOpen_inter_preimage (c.open_target.preimage continuous_subtype_val) ho
    contMDiffOn_toFun := by
      refine (D.coreAtlas.contMDiffOn_iff_subtype_val _ _).mpr ?_
      have hg : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun p : Circle × ℝ => (p.1, lam * p.2)) :=
        contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)
      refine (c.contMDiffOn.comp hg.contMDiffOn fun p hp => hsrc p hp).congr fun p hp => ?_
      exact hval p hp
    contMDiffOn_invFun := by
      have hv : ContMDiff (𝓡∂ 2) (SurfaceModel.model B.kind) ∞
          (fun y : D.core.Carrier => y.val) :=
        (D.coreAtlas.contMDiff_iff_subtype_val (fun y : D.core.Carrier => y)).mp contMDiff_id
      have h2 : ContMDiffOn (𝓡∂ 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun y : D.core.Carrier => c.symm y.val)
          {y : D.core.Carrier | y.val ∈ c.target ∧ |(c.symm y.val).2| < lam} :=
        c.symm.contMDiffOn.comp hv.contMDiffOn fun y hy => hy.1
      exact (contMDiff_fst.comp_contMDiffOn h2).prodMk
        ((contMDiff_id.div_const lam).comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn h2)) }

end CoreCut

section Matching

variable {f : B.Carrier → ℝ} {a b : ℝ}
  (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
  (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
  (x₀ : Ambient B)
  (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
    B.Carrier ∞)

theorem contMDiff_collar_zero
    (col : letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
      PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
        (slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) ∞)
    (hcol : col.source = circleCollarSource) :
    ContMDiff (𝓡 1) (SurfaceModel.model B.kind) ∞
      (fun t => opensVal _ (col (t, halfZero)).val) := by
  let := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
  have h1 : ContMDiff (𝓡 1) circleCollarModel ∞ (fun t : Circle => (t, halfZero)) :=
    contMDiff_id.prodMk contMDiff_const
  have h2 : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ (fun t : Circle => col (t, halfZero)) :=
    col.contMDiffOn.comp_contMDiff h1 fun t => by
      rw [hcol]
      exact halfZero_mem_circleCollarSource t
  exact (contMDiff_opensVal _).comp
    ((shiftAtlas (pieceAtlas hf hab hreg x₀)).contMDiff_subtype_val.comp h2)

theorem self_mem_componentOpens : x₀ ∈ componentOpens hf hab hreg x₀ := fun h =>
  h.2 (mem_connectedComponentIn h.1)

def componentBase : componentOpens hf hab hreg x₀ := ⟨x₀, self_mem_componentOpens hf hab hreg x₀⟩

variable (hcs : c.source = {p | -1 < p.2 ∧ p.2 < 1})
  (col : letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
    PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b) ∞)
  (hcol : col.source = circleCollarSource)
  (hrange : ∀ t', ∃ t, opensVal _ (col (t, halfZero)).val = c (t', 0))
  (hrange' : ∀ t, ∃ t', opensVal _ (col (t, halfZero)).val = c (t', 0))

include hrange in
theorem opensInv_mem_of_range (t' : Circle) :
    opensInv (componentOpens hf hab hreg x₀) (componentBase hf hab hreg x₀) (c (t', 0)) ∈
      slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b := by
  obtain ⟨t, ht⟩ := hrange t'
  rw [← ht, opensInv_opensVal]
  exact (col (t, halfZero)).2

def matchPoint (t' : Circle) : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b :=
  ⟨opensInv _ (componentBase hf hab hreg x₀) (c (t', 0)),
    opensInv_mem_of_range hf hab hreg x₀ c col hrange t'⟩

theorem matchPoint_eq {t' t : Circle} (h : opensVal _ (col (t, halfZero)).val = c (t', 0)) :
    matchPoint hf hab hreg x₀ c col hrange t' = col (t, halfZero) := by
  apply Subtype.ext
  change opensInv _ (componentBase hf hab hreg x₀) (c (t', 0)) = (col (t, halfZero)).val
  rw [← h, opensInv_opensVal]

def matchDiffeo : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle :=
  letI := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
  have hsrc0 (t' : Circle) : (t', (0 : ℝ)) ∈ c.source := by
    rw [hcs]
    exact ⟨by norm_num, by norm_num⟩
  have hcolsrc (t : Circle) : (t, halfZero) ∈ col.source := by
    rw [hcol]
    exact halfZero_mem_circleCollarSource t
  { toFun := fun t => (c.symm (opensVal _ (col (t, halfZero)).val)).1
    invFun := fun t' => (col.symm (matchPoint hf hab hreg x₀ c col hrange t')).1
    left_inv := fun t => by
      obtain ⟨t'', ht''⟩ := hrange' t
      have hl : c.symm (c (t'', 0)) = (t'', 0) := c.left_inv (hsrc0 t'')
      change (col.symm (matchPoint hf hab hreg x₀ c col hrange
        (c.symm (opensVal _ (col (t, halfZero)).val)).1)).1 = t
      rw [ht'', hl]
      change (col.symm (matchPoint hf hab hreg x₀ c col hrange t'')).1 = t
      have hl2 : col.symm (col (t, halfZero)) = (t, halfZero) := col.left_inv (hcolsrc t)
      rw [matchPoint_eq hf hab hreg x₀ c col hrange ht'', hl2]
    right_inv := fun t' => by
      obtain ⟨t, ht⟩ := hrange t'
      have hl : c.symm (c (t', 0)) = (t', 0) := c.left_inv (hsrc0 t')
      change (c.symm (opensVal _ (col ((col.symm
        (matchPoint hf hab hreg x₀ c col hrange t')).1, halfZero)).val)).1 = t'
      have hl2 : col.symm (col (t, halfZero)) = (t, halfZero) := col.left_inv (hcolsrc t)
      rw [matchPoint_eq hf hab hreg x₀ c col hrange ht, hl2]
      change (c.symm (opensVal _ (col (t, halfZero)).val)).1 = t'
      rw [ht, hl]
    contMDiff_toFun := by
      have h := contMDiff_collar_zero hf hab hreg x₀ col hcol
      refine contMDiff_fst.comp (c.symm.contMDiffOn.comp_contMDiff h fun t => ?_)
      obtain ⟨t'', ht''⟩ := hrange' t
      rw [ht'']
      exact c.map_source (hsrc0 t'')
    contMDiff_invFun := by
      have hc0 : ContMDiff (𝓡 1) (SurfaceModel.model B.kind) ∞ (fun t' : Circle => c (t', 0)) :=
        c.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const) fun t' => hsrc0 t'
      have hmp : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ (matchPoint hf hab hreg x₀ c col hrange) := by
        refine ((shiftAtlas (pieceAtlas hf hab hreg x₀)).contMDiff_iff_subtype_val _).mpr ?_
        refine (contMDiffOn_opensInv _ (componentBase hf hab hreg x₀)).comp_contMDiff hc0
          fun t' => ?_
        obtain ⟨t, ht⟩ := hrange t'
        exact ⟨(col (t, halfZero)).val, ht⟩
      refine contMDiff_fst.comp (col.symm.contMDiffOn.comp_contMDiff hmp fun t' => ?_)
      obtain ⟨t, ht⟩ := hrange t'
      rw [matchPoint_eq hf hab hreg x₀ c col hrange ht]
      exact col.map_source (hcolsrc t) }

theorem matchDiffeo_spec (t : Circle) :
    c (matchDiffeo hf hab hreg x₀ c hcs col hcol hrange hrange' t, 0) =
      opensVal _ (col (t, halfZero)).val := by
  obtain ⟨t'', ht''⟩ := hrange' t
  have hl : c.symm (c (t'', 0)) = (t'', 0) :=
    c.left_inv (by rw [hcs]; exact ⟨by norm_num, by norm_num⟩)
  change c ((c.symm (opensVal _ (col (t, halfZero)).val)).1, 0) = _
  rw [ht'', hl]

end Matching

section PieceSurface

variable {f : B.Carrier → ℝ} {a b : ℝ}
  (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
  (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
  (hint : ∀ y, a ≤ f y → y ∈ interiorOpens B) {x₀ : Ambient B}
  (hx₀ : x₀ ∈ slabSet (ambientFun f) a b)

def pieceSurface : CompactSurface.{u} where
  kind := .withBoundary
  Carrier := slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b
  charts := (shiftAtlas (pieceAtlas hf hab hreg x₀)).toChartedSpace
  smooth := (shiftAtlas (pieceAtlas hf hab hreg x₀)).isManifold
  compact := compactSpace_pieceSlab hf hab hreg hint x₀
  connected := connectedSpace_pieceSlab hf hab hreg hx₀

theorem isSmoothEmbedding_comp_symm_of_kind {S : CompactSurface.{u}}
    (hS : S.kind = .withBoundary) (emb : S.Carrier → ℂ)
    (hemb : Manifold.IsSmoothEmbedding (SurfaceModel.model S.kind) 𝓘(ℝ, ℂ) ∞ emb)
    (e : S.Carrier ≃ₘ⟮SurfaceModel.model S.kind, SurfaceModel.model (pieceSurface hf hab hreg
      hint hx₀).kind⟯ (pieceSurface hf hab hreg hint hx₀).Carrier) :
    Manifold.IsSmoothEmbedding (SurfaceModel.model (pieceSurface hf hab hreg hint hx₀).kind)
      𝓘(ℝ, ℂ) ∞ (fun x => emb (e.symm x)) := by
  obtain ⟨⟨kind, Carrier, top, charts, smooth, t2, cpt, sc⟩, conn⟩ := S
  subst hS
  let inst : ChartedSpace (ModelBoundaryKind.Space .withBoundary 2)
      (pieceSurface hf hab hreg hint hx₀).Carrier := (pieceSurface hf hab hreg hint hx₀).charts
  have instM : IsManifold (ModelBoundaryKind.model .withBoundary 2) ∞
      (pieceSurface hf hab hreg hint hx₀).Carrier := (pieceSurface hf hab hreg hint hx₀).smooth
  exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp emb hemb
    e.symm

def transportBaseW {k : ℕ} (P : PlanarBase.{u} k) (hP : P.surface.kind = .withBoundary)
    (e : P.surface.Carrier ≃ₘ⟮SurfaceModel.model P.surface.kind, SurfaceModel.model
      (pieceSurface hf hab hreg hint hx₀).kind⟯ (pieceSurface hf hab hreg hint hx₀).Carrier) :
    PlanarBase.{u} k where
  surface := pieceSurface hf hab hreg hint hx₀
  collar j := (P.collar j).trans e.toPartialDiffeomorph
  source_eq j := by
    change (P.collar j).source ∩ (P.collar j) ⁻¹' univ = circleCollarSource
    rw [preimage_univ, inter_univ, P.source_eq j]
  boundary_zero j t := by
    have h := P.boundary_zero j t
    have himg := e.image_boundary (by simp)
    have hmem : e (P.collar j (t, halfZero)) ∈
        (SurfaceModel.model (pieceSurface hf hab hreg hint hx₀).kind).boundary
          (pieceSurface hf hab hreg hint hx₀).Carrier := by
      rw [← himg]
      exact mem_image_of_mem e h
    exact hmem
  disjoint i j hij := by
    have h := P.disjoint hij
    change Disjoint (univ ∩ e.symm ⁻¹' (P.collar i).target)
      (univ ∩ e.symm ⁻¹' (P.collar j).target)
    rw [univ_inter, univ_inter]
    exact h.preimage _
  boundary_exhausted := by
    have himg := e.image_boundary (by simp)
    change (SurfaceModel.model (pieceSurface hf hab hreg hint hx₀).kind).boundary
      (pieceSurface hf hab hreg hint hx₀).Carrier =
      ⋃ j, range fun t => e (P.collar j (t, halfZero))
    rw [← himg, P.boundary_exhausted, image_iUnion]
    congr 1
    ext j
    rw [← range_comp]
    rfl
  embedding x := P.embedding (e.symm x)
  isSmoothEmbedding := isSmoothEmbedding_comp_symm_of_kind hf hab hreg hint hx₀ hP P.embedding
    P.isSmoothEmbedding e
  range_embedding := by
    rw [← P.range_embedding]
    exact e.symm.surjective.range_comp P.embedding
  embedding_collar j t := by
    change P.embedding (e.symm (e (P.collar j (t, halfZero)))) = _
    rw [e.symm_apply_apply]
    exact P.embedding_collar j t

end PieceSurface

section SlabPiece

variable (D : BaseMorseData B)

abbrev slabPieceSurface (i : Fin D.m) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)) :
    CompactSurface.{u} :=
  pieceSurface D.smooth (level_castSucc_lt_succ D i) (slab_regular D i) (slab_interior D i) hx₀

structure SlabPiece (i : Fin D.m) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)) where
  k : ℕ
  hk : k ∈ ({1, 2, 3} : Finset ℕ)
  P : PlanarBase.{u} k
  hP : P.surface.kind = .withBoundary
  e : P.surface.Carrier ≃ₘ⟮SurfaceModel.model P.surface.kind,
    SurfaceModel.model (slabPieceSurface D i hx₀).kind⟯ (slabPieceSurface D i hx₀).Carrier
  lev : Fin k → Bool
  hlev : ∀ l t, D.f (opensVal _ (e (P.collar l (t, halfZero))).val) =
    if lev l then D.level i.succ else D.level i.castSucc

theorem nonempty_slabPiece_of_regular (i : Fin D.m) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ))
    (hnc : ∀ y ∈ connectedComponentIn
      (slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)) x₀,
      mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f (ambientVal y) ≠ 0) :
    Nonempty (SlabPiece D i hx₀) := by
  have hab := level_castSucc_lt_succ D i
  have hreg := slab_regular D i
  have hint := slab_interior D i
  obtain ⟨e, -, h2, h3⟩ := exists_annulus_pieceSlab_shift D.smooth hab hreg hint hx₀ hnc
    (exists_min_level_mem_component D.smooth hab hreg hint hx₀ fun y hy =>
      (not_isLocalMin_of_mfderiv_ne_zero D.smooth (hnc y hy)).1)
    (exists_max_level_mem_component D.smooth hab hreg hint hx₀ fun y hy =>
      (not_isLocalMin_of_mfderiv_ne_zero D.smooth (hnc y hy)).2)
  refine ⟨⟨2, by decide, annulusPlanarBase.{u}, rfl, e, fun l => decide (l.val = 0), ?_⟩⟩
  intro l t
  fin_cases l
  · exact h3 t
  · exact h2 t

theorem crit_value_ne_level {p : B.Carrier} (hp : p ∈ D.crit) (j : Fin (D.m + 1)) :
    D.f p ≠ D.level j := fun h =>
  mfderiv_ne_zero_of_eq_level D j h ((D.mem_crit p).mp hp)

open Classical in
theorem nonempty_slabPiece_of_extremum (i : Fin D.m) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ))
    {p : B.Carrier} (hp : p ∈ D.crit)
    (hidx : sigNeg (chartHessianAt
      (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
      (extChartAt (SurfaceModel.model B.kind) p p)) ≠ 1)
    (hpK : p ∈ connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
      (ambientVal x₀)) :
    Nonempty (SlabPiece D i hx₀) := by
  have hab := level_castSucc_lt_succ D i
  have hreg := slab_regular D i
  have hint := slab_interior D i
  have hpI : D.f p ∈ Icc (D.level i.castSucc) (D.level i.succ) :=
    connectedComponentIn_subset (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) _ hpK
  have hpi : D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ) :=
    ⟨lt_of_le_of_ne hpI.1 (crit_value_ne_level D hp _).symm,
      lt_of_le_of_ne hpI.2 (crit_value_ne_level D hp _)⟩
  obtain ⟨R, χ, hχ0, hball, himg⟩ := D.thin p hp hidx i hpi
  have hR : 0 < R := pos_radius_of_image_eq D.smooth.continuous hpi χ hχ0 hball himg
  have himg' : χ '' closedBall 0 R =
      opensVal _ '' slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀))
        (D.level i.castSucc) (D.level i.succ) := by
    rw [himg, opensVal_image_pieceSlab D.smooth hab hreg hint x₀, connectedComponentIn_eq hpK]
  let := (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace
  let E := discPieceDiffeo D.smooth hab hreg x₀ χ hR hball himg'
  let P := discPlanarBase.{u} 1
  have hbd (t : Circle) : D.f (opensVal _ (E (P.collar 0 (t, halfZero))).val) =
      D.level i.castSucc ∨ D.f (opensVal _ (E (P.collar 0 (t, halfZero))).val) =
        D.level i.succ := by
    have himgb := E.image_boundary (by simp)
    have hmem : E (P.collar 0 (t, halfZero)) ∈
        (𝓡∂ 2).boundary (slabSet (pieceFun D.f (componentOpens D.smooth hab hreg x₀))
          (D.level i.castSucc) (D.level i.succ)) := by
      rw [← himgb]
      exact mem_image_of_mem E (P.boundary_zero 0 t)
    exact (pieceSlab_boundary_iff D.smooth hab hreg x₀ _).mp hmem
  have hcont : Continuous fun t : Circle =>
      D.f (opensVal _ (E (P.collar 0 (t, halfZero))).val) := by
    have hcol : Continuous fun t : Circle => P.collar 0 (t, halfZero) := by
      refine (P.collar 0).contMDiffOn.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) fun t => ?_
      rw [P.source_eq 0]
      exact halfZero_mem_circleCollarSource t
    exact D.smooth.continuous.comp ((isOpenEmbedding_opensVal _).continuous.comp
      (continuous_subtype_val.comp (E.continuous.comp hcol)))
  have h2 := eq_or_eq_of_two_valued hcont hab hbd
  refine ⟨⟨1, by decide, P, rfl, E, Function.const (Fin 1) (decide (∀ t, D.f (opensVal _
    (E (P.collar 0 (t, halfZero))).val) = D.level i.succ)), ?_⟩⟩
  intro l t
  rw [Subsingleton.elim l 0]
  by_cases hup : ∀ t, D.f (opensVal _ (E (P.collar 0 (t, halfZero))).val) = D.level i.succ
  · simp only [hup, implies_true, decide_true]
    exact hup t
  · have hlow := h2.resolve_right hup
    simp only [hup, decide_false]
    exact hlow t

end SlabPiece

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)

theorem isCriticalPointAt_opens_iff {U : TopologicalSpace.Opens M} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : U) (hx : I.IsInteriorPoint (x : M)) :
    IsCriticalPointAt I (fun y : U => f y) x ↔ IsCriticalPointAt I f (x : M) := by
  change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y : U => f y) x) = 0 ↔
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f (x : M)) = 0
  erw [DifferentialGeometry.Manifold.mfderiv_openRestriction I hf x hx]

theorem chartHessianAt_opens_eq (U : TopologicalSpace.Opens M) (f : M → ℝ) (x : U) :
    chartHessianAt (fun y => f (((extChartAt I x).symm y : U) : M)) (extChartAt I x x) =
      chartHessianAt (fun y => f ((extChartAt I (x : M)).symm y)) (extChartAt I (x : M) x) := by
  have h : fderiv ℝ (fderiv ℝ (fun y => f ((extChartAt I (x : M)).symm y)))
      (extChartAt I (x : M) x) =
      fderiv ℝ (fderiv ℝ (fun y => f (((extChartAt I x).symm y : U) : M)))
        (extChartAt I (x : M) x) :=
    ((DifferentialGeometry.Manifold.extChartAt_subtype_val_symm_eventuallyEq I U x).fun_comp
      f).fderiv.fderiv_eq
  ext v
  change (fderiv ℝ (fderiv ℝ (fun y => f (((extChartAt I x).symm y : U) : M)))
    (extChartAt I (x : M) x)) v v = _
  rw [← h]
  rfl

theorem isNondegenerateCriticalPointAt_opens_iff {U : TopologicalSpace.Opens M} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : U) (hx : I.IsInteriorPoint (x : M)) :
    IsNondegenerateCriticalPointAt I (fun y : U => f y) x ↔
      IsNondegenerateCriticalPointAt I f (x : M) := by
  unfold IsNondegenerateCriticalPointAt
  rw [isCriticalPointAt_opens_iff I hf x hx, chartHessianAt_opens_eq I U f x]

end Transfer

section AmbientTransfer

variable {f : B.Carrier → ℝ}

theorem isCriticalPointAt_ambient_iff (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (x : Ambient B) :
    IsCriticalPointAt 𝓘(ℝ, E2) (ambientFun f) x ↔
      IsCriticalPointAt (SurfaceModel.model B.kind) f (ambientVal x) := by
  have h1 : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞
      (fun y : interiorOpens B => f y) := hf.comp contMDiff_subtype_val
  have h2 := DifferentialGeometry.Manifold.mfderiv_interiorAtlas (SurfaceModel.model B.kind) h1
    (show interiorOpens B from x)
  have h3 := isCriticalPointAt_opens_iff (SurfaceModel.model B.kind) hf
    (show interiorOpens B from x) (show interiorOpens B from x).2
  refine Iff.trans ?_ h3
  change (show E2 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) (ambientFun f) x) = 0 ↔
    (show E2 →L[ℝ] ℝ from mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ)
      (fun y : interiorOpens B => f y) x) = 0
  erw [h2]

theorem chartHessianAt_ambient_eq (x : Ambient B) :
    chartHessianAt (fun y => ambientFun f ((extChartAt 𝓘(ℝ, E2) x).symm y))
        (extChartAt 𝓘(ℝ, E2) x x) =
      chartHessianAt (fun y => f ((extChartAt (SurfaceModel.model B.kind) (ambientVal x)).symm y))
        (extChartAt (SurfaceModel.model B.kind) (ambientVal x) (ambientVal x)) :=
  chartHessianAt_opens_eq (SurfaceModel.model B.kind) (interiorOpens B) f
    (show interiorOpens B from x)

theorem isCriticalPointAt_piece_iff (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f)
    (N' : Opens (Ambient B)) (z : N') :
    IsCriticalPointAt 𝓘(ℝ, E2) (pieceFun f N') z ↔
      IsCriticalPointAt (SurfaceModel.model B.kind) f (opensVal N' z) := by
  have h := isCriticalPointAt_opens_iff 𝓘(ℝ, E2) (contMDiff_ambientFun hf) z
    BoundarylessManifold.isInteriorPoint
  exact h.trans (isCriticalPointAt_ambient_iff hf z.val)

theorem chartHessianAt_piece_eq (N' : Opens (Ambient B)) (z : N') :
    chartHessianAt (fun y => pieceFun f N' ((extChartAt 𝓘(ℝ, E2) z).symm y))
        (extChartAt 𝓘(ℝ, E2) z z) =
      chartHessianAt (fun y => f ((extChartAt (SurfaceModel.model B.kind)
        (opensVal N' z)).symm y)) (extChartAt (SurfaceModel.model B.kind) (opensVal N' z)
          (opensVal N' z)) :=
  (chartHessianAt_opens_eq 𝓘(ℝ, E2) N' (ambientFun f) z).trans (chartHessianAt_ambient_eq z.val)

theorem isNondegenerateCriticalPointAt_piece_iff
    (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (N' : Opens (Ambient B)) (z : N') :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, E2) (pieceFun f N') z ↔
      IsNondegenerateCriticalPointAt (SurfaceModel.model B.kind) f (opensVal N' z) := by
  unfold IsNondegenerateCriticalPointAt
  rw [isCriticalPointAt_piece_iff hf N' z, chartHessianAt_piece_eq N' z]

end AmbientTransfer

section PantsPiece

variable (D : BaseMorseData B)

theorem slab_index_unique {x : ℝ} {i j : Fin D.m}
    (hi : x ∈ Ioo (D.level i.castSucc) (D.level i.succ))
    (hj : x ∈ Ioo (D.level j.castSucc) (D.level j.succ)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hle : D.level i.succ ≤ D.level j.castSucc :=
      D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    linarith [hi.2, hj.1]
  · have hle : D.level j.succ ≤ D.level i.castSucc :=
      D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    linarith [hj.2, hi.1]

theorem saddle_data (i : Fin D.m) {x₀ : Ambient B} {p : B.Carrier} (hp : p ∈ D.crit)
    (hpK : p ∈ connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
      (ambientVal x₀)) :
    ∃ p' : slabOpens D i x₀, opensVal _ p' = p ∧
      pieceFun D.f (slabOpens D i x₀) p' ∈ Ioo (D.level i.castSucc) (D.level i.succ) ∧
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E2) (pieceFun D.f (slabOpens D i x₀)) p' ∧
      (∀ x, pieceFun D.f (slabOpens D i x₀) x ∈ Icc (D.level i.castSucc) (D.level i.succ) →
        IsCriticalPointAt 𝓘(ℝ, E2) (pieceFun D.f (slabOpens D i x₀)) x → x = p') := by
  have hab := level_castSucc_lt_succ D i
  have hreg := slab_regular D i
  have hint := slab_interior D i
  have hpI : D.f p ∈ Icc (D.level i.castSucc) (D.level i.succ) :=
    connectedComponentIn_subset (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) _ hpK
  have hpi : D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ) :=
    ⟨lt_of_le_of_ne hpI.1 (crit_value_ne_level D hp _).symm,
      lt_of_le_of_ne hpI.2 (crit_value_ne_level D hp _)⟩
  have hpX : p ∈ opensVal _ '' slabSet (pieceFun D.f (slabOpens D i x₀))
      (D.level i.castSucc) (D.level i.succ) := by
    rw [opensVal_image_pieceSlab D.smooth hab hreg hint x₀]
    exact hpK
  obtain ⟨w, -, hw⟩ := hpX
  refine ⟨w, hw, ?_, ?_, ?_⟩
  · change D.f (opensVal _ w) ∈ _
    rw [hw]
    exact hpi
  · rw [isNondegenerateCriticalPointAt_piece_iff D.smooth, hw]
    exact D.nondegenerate p hp
  · intro x hx hcx
    have hq : opensVal _ x ∈ D.crit :=
      (D.mem_crit _).mpr ((isCriticalPointAt_piece_iff D.smooth _ x).mp hcx)
    obtain ⟨j, hj, huniq⟩ := D.slab p hp
    have hij : j = i := slab_index_unique D hj hpi
    subst hij
    have heq := huniq _ hq hx
    apply (isOpenEmbedding_opensVal _).injective
    rw [heq, hw]

theorem nonempty_slabPiece_of_saddle (i : Fin D.m) {x₀ : Ambient B}
    (hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ))
    {p : B.Carrier} (hp : p ∈ D.crit)
    (hidx : sigNeg (chartHessianAt
      (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
      (extChartAt (SurfaceModel.model B.kind) p p)) = 1)
    (hpK : p ∈ connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
      (ambientVal x₀))
    (hdis : ¬ IsPreconnected (pieceFun D.f (slabOpens D i x₀) ⁻¹' {D.level i.castSucc}) ∨
      ¬ IsPreconnected (pieceFun D.f (slabOpens D i x₀) ⁻¹' {D.level i.succ})) :
    Nonempty (SlabPiece D i hx₀) := by
  have hab := level_castSucc_lt_succ D i
  have hreg := slab_regular D i
  have hint := slab_interior D i
  obtain ⟨p', hp', hpi', hnd', huniq'⟩ := saddle_data D i hp hpK
  have hidx' : sigNeg (chartHessianAt
      (fun y => pieceFun D.f (slabOpens D i x₀) ((extChartAt 𝓘(ℝ, E2) p').symm y))
      (extChartAt 𝓘(ℝ, E2) p' p')) = 1 := by
    rw [chartHessianAt_piece_eq, hp']
    exact hidx
  have hcpt : IsCompact (pieceFun D.f (slabOpens D i x₀) ⁻¹'
      Icc (D.level i.castSucc) (D.level i.succ)) := by
    rw [← slabSet_eq hab.le]
    exact isCompact_pieceSlab D.smooth hab hreg hint x₀
  have hconn : IsConnected (pieceFun D.f (slabOpens D i x₀) ⁻¹'
      Icc (D.level i.castSucc) (D.level i.succ)) := by
    rw [← slabSet_eq hab.le]
    exact isConnected_pieceSlab D.smooth hab hreg hx₀
  let Dsh := (pieceAtlas D.smooth hab hreg x₀).diffeomorphOfAmbient
    (shiftAtlas (pieceAtlas D.smooth hab hreg x₀))
    (Diffeomorph.refl 𝓘(ℝ, E2) (slabOpens D i x₀) ∞) (by intro z; exact Iff.rfl)
  rcases hdis with hlow | hup
  · obtain ⟨e, he⟩ := exists_planarBase_of_saddleSlab'.{u} 𝓘(ℝ, E2) finrank_euclideanSpace_fin
      (contMDiff_pieceFun D.smooth _) hab (pieceFun_regular D.smooth hreg _) hpi' hnd' hidx'
      huniq' hcpt hconn hlow
    refine ⟨⟨3, by decide, pantsPlanarBase.{u}, rfl,
      @Diffeomorph.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (pieceAtlas D.smooth hab hreg x₀).toChartedSpace _ _
        (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace _ e Dsh,
      fun l => decide (l.val = 0), fun l t => ?_⟩⟩
    have h := he l t
    by_cases hl : l.val = 0
    · simp only [hl, ↓reduceIte] at h
      simp only [hl, decide_true, ↓reduceIte]
      exact h
    · simp only [hl, ↓reduceIte] at h
      simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact h
  · obtain ⟨e, he⟩ := exists_planarBase_of_saddleSlab_upper'.{u} 𝓘(ℝ, E2)
      finrank_euclideanSpace_fin (contMDiff_pieceFun D.smooth _) hab
      (pieceFun_regular D.smooth hreg _) hpi' hnd' hidx' huniq' hcpt hconn hup
    refine ⟨⟨3, by decide, pantsPlanarBase.{u}, rfl,
      @Diffeomorph.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (pieceAtlas D.smooth hab hreg x₀).toChartedSpace _ _
        (shiftAtlas (pieceAtlas D.smooth hab hreg x₀)).toChartedSpace _ e Dsh,
      fun l => decide (l.val ≠ 0), fun l t => ?_⟩⟩
    have h := he l t
    by_cases hl : l.val = 0
    · simp only [hl, ↓reduceIte] at h
      simp only [hl, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact h
    · simp only [hl, ↓reduceIte] at h
      simp only [hl, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
      exact h

end PantsPiece

section Glue

variable (D : BaseMorseData B)

theorem exists_slab_of_level_zero_le {y : B.Carrier} (hy : D.level 0 ≤ D.f y) :
    ∃ i : Fin D.m, D.f y ∈ Icc (D.level i.castSucc) (D.level i.succ) := by
  have hlast := D.lt_level_last y
  by_contra hno
  push Not at hno
  have key : ∀ n : ℕ, (hn : n ≤ D.m) → D.level ⟨n, Nat.lt_succ_of_le hn⟩ ≤ D.f y := by
    intro n
    induction n with
    | zero => intro hn; exact hy
    | succ n ih =>
      intro hn
      have hle := ih (Nat.le_of_succ_le hn)
      by_contra hlt
      push Not at hlt
      exact hno ⟨n, hn⟩ ⟨hle, hlt.le⟩
  have h := key D.m le_rfl
  exact absurd hlast (not_lt.mpr h)

def pieceGamma (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀) (l : Fin sp.k) (t : Circle) : B.Carrier :=
  opensVal _ (sp.e (sp.P.collar l (t, halfZero))).val

theorem continuous_pieceGamma (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀) (l : Fin sp.k) : Continuous (pieceGamma D i sp l) := by
  have hcol : Continuous fun t : Circle => sp.P.collar l (t, halfZero) := by
    refine (sp.P.collar l).contMDiffOn.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) fun t => ?_
    rw [sp.P.source_eq l]
    exact halfZero_mem_circleCollarSource t
  exact (isOpenEmbedding_opensVal _).continuous.comp
    (continuous_subtype_val.comp (sp.e.continuous.comp hcol))

theorem pieceGamma_mem_target (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀) (l : Fin sp.k) (t : Circle) :
    sp.P.collar l (t, halfZero) ∈ (sp.P.collar l).target :=
  (sp.P.collar l).map_source (by rw [sp.P.source_eq l]; exact halfZero_mem_circleCollarSource t)

theorem disjoint_range_pieceGamma (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀) {l l' : Fin sp.k} (hll : l ≠ l') :
    Disjoint (range (pieceGamma D i sp l)) (range (pieceGamma D i sp l')) := by
  rw [Set.disjoint_left]
  rintro z ⟨t, rfl⟩ ⟨t', ht'⟩
  have h1 : sp.e (sp.P.collar l' (t', halfZero)) = sp.e (sp.P.collar l (t, halfZero)) :=
    Subtype.val_injective ((isOpenEmbedding_opensVal _).injective ht')
  have h2 := sp.e.injective h1
  have hd := sp.P.disjoint hll.symm
  exact Set.disjoint_left.mp hd (pieceGamma_mem_target D i sp l' t')
    (h2 ▸ pieceGamma_mem_target D i sp l t)

theorem exists_pieceGamma_of_level (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀)
    (w : slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ))
    (hw : D.f (opensVal _ w.val) = D.level i.castSucc ∨ D.f (opensVal _ w.val) = D.level i.succ) :
    ∃ l t, pieceGamma D i sp l t = opensVal _ w.val := by
  let := (shiftAtlas (pieceAtlas D.smooth (level_castSucc_lt_succ D i) (slab_regular D i)
    x₀)).toChartedSpace
  have hb : (𝓡∂ 2).IsBoundaryPoint w :=
    (pieceSlab_boundary_iff D.smooth (level_castSucc_lt_succ D i) (slab_regular D i) x₀ w).mpr hw
  have himg := sp.e.image_boundary (by simp)
  have hmem : w ∈ (SurfaceModel.model (slabPieceSurface D i hx₀).kind).boundary
      (slabPieceSurface D i hx₀).Carrier := hb
  rw [← himg, sp.P.boundary_exhausted] at hmem
  obtain ⟨z, hz, hzw⟩ := hmem
  obtain ⟨l, t, rfl⟩ := mem_iUnion.mp hz
  exact ⟨l, t, by rw [pieceGamma, hzw]⟩

theorem pieceGamma_level (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀) (l : Fin sp.k) (t : Circle) :
    D.f (pieceGamma D i sp l t) = if sp.lev l then D.level i.succ else D.level i.castSucc :=
  sp.hlev l t

theorem range_pieceGamma (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀) (l : Fin sp.k) :
    range (pieceGamma D i sp l) = connectedComponentIn
      (D.f ⁻¹' {if sp.lev l then D.level i.succ else D.level i.castSucc})
      (pieceGamma D i sp l 1) := by
  set L := if sp.lev l then D.level i.succ else D.level i.castSucc
  have hab := level_castSucc_lt_succ D i
  have hLab : L = D.level i.castSucc ∨ L = D.level i.succ := by
    by_cases h : sp.lev l <;> simp [L, h]
  have hpre : IsPreconnected (range (pieceGamma D i sp l)) :=
    isPreconnected_range (continuous_pieceGamma D i sp l)
  apply Subset.antisymm
  · refine hpre.subset_connectedComponentIn (mem_range_self 1) ?_
    rintro z ⟨t, rfl⟩
    exact pieceGamma_level D i sp l t
  · set C := connectedComponentIn (D.f ⁻¹' {L}) (pieceGamma D i sp l 1)
    have hC : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCX : C ⊆ opensVal _ '' slabSet (pieceFun D.f (slabOpens D i x₀))
        (D.level i.castSucc) (D.level i.succ) := by
      rw [opensVal_image_pieceSlab D.smooth hab (slab_regular D i) (slab_interior D i) x₀]
      have hγX : pieceGamma D i sp l 1 ∈ connectedComponentIn
          (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀) := by
        rw [← opensVal_image_pieceSlab D.smooth hab (slab_regular D i) (slab_interior D i) x₀]
        exact mem_image_of_mem _ (sp.e (sp.P.collar l (1, halfZero))).2
      rw [connectedComponentIn_eq hγX]
      refine hC.subset_connectedComponentIn (mem_connectedComponentIn ?_) ?_
      · change D.f (pieceGamma D i sp l 1) = L
        exact pieceGamma_level D i sp l 1
      · intro z hz
        have hzL' : z ∈ D.f ⁻¹' {L} := connectedComponentIn_subset (D.f ⁻¹' {L}) _ hz
        have hzL : D.f z = L := hzL'
        rcases hLab with h | h <;> rw [h] at hzL <;> rw [mem_preimage, hzL] <;>
          exact ⟨by linarith, by linarith⟩
    have hcover : C ⊆ range (pieceGamma D i sp l) ∪
        ⋃ l' ∈ ({l}ᶜ : Set (Fin sp.k)), range (pieceGamma D i sp l') := by
      intro z hz
      obtain ⟨w, hwX, hw⟩ := hCX hz
      have hzL' : z ∈ D.f ⁻¹' {L} := connectedComponentIn_subset (D.f ⁻¹' {L}) _ hz
      have hzL : D.f z = L := hzL'
      obtain ⟨l', t', hl't'⟩ := exists_pieceGamma_of_level D i sp ⟨w, hwX⟩
        (by change D.f (opensVal _ w) = _ ∨ D.f (opensVal _ w) = _; rw [hw, hzL]; exact hLab)
      by_cases hl' : l' = l
      · subst hl'
        exact Or.inl ⟨t', hl't'.trans hw⟩
      · exact Or.inr (mem_biUnion hl' ⟨t', hl't'.trans hw⟩)
    have hclosed (l' : Fin sp.k) : IsClosed (range (pieceGamma D i sp l')) :=
      (isCompact_range (continuous_pieceGamma D i sp l')).isClosed
    have hdisj : C ∩ (range (pieceGamma D i sp l) ∩
        ⋃ l' ∈ ({l}ᶜ : Set (Fin sp.k)), range (pieceGamma D i sp l')) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨-, hzA, hzV⟩ := hz
      obtain ⟨l', hl', hz'⟩ := mem_iUnion₂.mp hzV
      exact Set.disjoint_left.mp (disjoint_range_pieceGamma D i sp (Ne.symm hl')) hzA hz'
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hC _ _ (hclosed l)
      ((Set.toFinite _).isClosed_biUnion (by intro l' hl'; exact hclosed l')) hcover hdisj
      with h | h
    · exact h
    · exfalso
      have h1 : pieceGamma D i sp l 1 ∈ C := mem_connectedComponentIn (pieceGamma_level D i sp l 1)
      obtain ⟨l', hl', hz'⟩ := mem_iUnion₂.mp (h h1)
      exact Set.disjoint_left.mp (disjoint_range_pieceGamma D i sp (Ne.symm hl'))
        (mem_range_self 1) hz'

end Glue

section Shrink

variable (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
    B.Carrier ∞) (lam : ℝ)

def shrinkBicollar (hcs : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
      B.Carrier ∞ :=
  have hsrc (p : Circle × ℝ) (hp : -1 < p.2 ∧ p.2 < 1) : (p.1, lam * p.2) ∈ c.source := by
    rw [hcs]
    have h1 : |lam * p.2| < 1 := by
      rw [abs_mul, abs_of_pos hlam]
      have hp' : |p.2| < 1 := abs_lt.mpr hp
      nlinarith [abs_nonneg p.2]
    exact abs_lt.mp h1
  { toFun := fun p => c (p.1, lam * p.2)
    invFun := fun y => ((c.symm y).1, (c.symm y).2 / lam)
    source := {p | -1 < p.2 ∧ p.2 < 1}
    target := {y | y ∈ c.target ∧ |(c.symm y).2| < lam}
    map_source' := fun p hp => by
      have hl : c.symm (c (p.1, lam * p.2)) = (p.1, lam * p.2) := c.left_inv (hsrc p hp)
      refine ⟨c.map_source (hsrc p hp), ?_⟩
      rw [hl, abs_mul, abs_of_pos hlam]
      have hp' : |p.2| < 1 := abs_lt.mpr hp
      nlinarith [abs_nonneg p.2]
    map_target' := fun y hy => by
      have h : |(c.symm y).2 / lam| < 1 := by
        rw [abs_div, abs_of_pos hlam, div_lt_one hlam]
        exact hy.2
      exact abs_lt.mp h
    left_inv' := fun p hp => by
      have hl : c.symm (c (p.1, lam * p.2)) = (p.1, lam * p.2) := c.left_inv (hsrc p hp)
      change ((c.symm (c (p.1, lam * p.2))).1, (c.symm (c (p.1, lam * p.2))).2 / lam) = p
      rw [hl]
      ext
      · rfl
      · change lam * p.2 / lam = p.2
        field_simp
    right_inv' := fun y hy => by
      have hr : c (c.symm y) = y := c.right_inv hy.1
      change c ((c.symm y).1, lam * ((c.symm y).2 / lam)) = y
      rw [mul_div_cancel₀ _ hlam.ne']
      exact hr
    open_source := (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
    open_target := by
      have ho : IsOpen {q : Circle × ℝ | |q.2| < lam} :=
        isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
      exact c.symm.contMDiffOn.continuousOn.isOpen_inter_preimage c.open_target ho
    contMDiffOn_toFun := by
      have hg : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun p : Circle × ℝ => (p.1, lam * p.2)) :=
        contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)
      exact c.contMDiffOn.comp hg.contMDiffOn fun p hp => hsrc p hp
    contMDiffOn_invFun := by
      have h2 : ContMDiffOn (SurfaceModel.model B.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun y => c.symm y) {y | y ∈ c.target ∧ |(c.symm y).2| < lam} :=
        c.symm.contMDiffOn.mono fun y hy => hy.1
      exact (contMDiff_fst.comp_contMDiffOn h2).prodMk
        ((contMDiff_id.div_const lam).comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn h2)) }

theorem shrinkBicollar_apply (hcs : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (p : Circle × ℝ) :
    shrinkBicollar c lam hcs hlam hlam1 p = c (p.1, lam * p.2) := rfl

end Shrink

section Recollared

variable (D : BaseMorseData B)

theorem exists_recollared_piece (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀)
    (c : Fin sp.k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
      (Circle × ℝ) B.Carrier ∞)
    (ε : Fin sp.k → ℝ)
    (hcs : ∀ l, (c l).source = {p | -1 < p.2 ∧ p.2 < 1})
    (hε : ∀ l, ε l = 1 ∨ ε l = -1)
    (hrange : ∀ l t', ∃ t, pieceGamma D i sp l t = c l (t', 0))
    (hrange' : ∀ l t, ∃ t', pieceGamma D i sp l t = c l (t', 0))
    (hin : ∀ l t s, 0 ≤ s → s < 1 →
      ∃ y : slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ),
        opensVal _ y.val = c l (t, ε l * s))
    (hside : ∀ l (y : slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc)
      (D.level i.succ)), opensVal _ y.val ∈ (c l).target →
        0 ≤ ε l * ((c l).symm (opensVal _ y.val)).2)
    (hdisj : ∀ l l', l ≠ l' → ∀ y : B.Carrier, y ∈ (c l).target → y ∉ (c l').target) :
    ∃ (Q : PlanarBase.{u} sp.k) (ι : Q.surface.Carrier → D.core.Carrier),
      Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind)
        (SurfaceModel.model D.core.kind) ∞ ι ∧
      (∀ l, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
        (ι (Q.collar l (t, halfPoint s hs))).val = c l (σ t, ε l * s)) ∧
      (∀ x, (ι x).val ∈ connectedComponentIn
        (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)) ∧
      (∀ y ∈ connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        (ambientVal x₀), ∃ x, (ι x).val = y) ∧
      (∀ x, D.f (ι x).val = D.level i.castSucc ∨ D.f (ι x).val = D.level i.succ →
        ∃ l t, x = Q.collar l (t, halfZero)) ∧
      ∀ l t, (ι (Q.collar l (t, halfZero))).val = pieceGamma D i sp l t := by
  have hab := level_castSucc_lt_succ D i
  have hreg := slab_regular D i
  have hint := slab_interior D i
  have ha : D.level 0 ≤ D.level i.castSucc := D.level_strictMono.monotone (Fin.zero_le _)
  let Q0 := transportBaseW D.smooth hab hreg hint hx₀ sp.P sp.hP sp.e
  have hQ0 (l : Fin sp.k) (t : Circle) :
      opensVal _ (Q0.collar l (t, halfZero)).val = pieceGamma D i sp l t := rfl
  have hcolsrc (l : Fin sp.k) : (Q0.collar l).source = circleCollarSource := Q0.source_eq l
  let σ : Fin sp.k → Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle := fun l =>
    matchDiffeo D.smooth hab hreg x₀ (c l) (hcs l) (Q0.collar l) (hcolsrc l)
      (fun t' => (hrange l t').imp fun t ht => (hQ0 l t).trans ht)
      (fun t => (hrange' l t).imp fun t' ht => (hQ0 l t).trans ht)
  have hσ (l : Fin sp.k) (t : Circle) : c l (σ l t, 0) = pieceGamma D i sp l t :=
    matchDiffeo_spec D.smooth hab hreg x₀ (c l) (hcs l) (Q0.collar l) (hcolsrc l) _ _ t
  let col : Fin sp.k → _ := fun l =>
    halfCollar D.smooth hab hreg x₀ (c l) (σ l) (ε l) (hcs l) (hε l) (fun t s h0 h1 =>
      hin l (σ l t) s h0 h1) (hside l)
  have hcolval (l : Fin sp.k) (q : Circle × EuclideanHalfSpace 1) :
      opensVal _ (col l q).val = c l (σ l q.1, ε l * collarClamp q) :=
    opensVal_halfCollarFun D.smooth hab hreg x₀ (c l) (σ l) (ε l)
      (fun t s h0 h1 => hin l (σ l t) s h0 h1) q
  have hzero (l : Fin sp.k) (t : Circle) : col l (t, halfZero) = Q0.collar l (t, halfZero) := by
    apply Subtype.ext
    apply (isOpenEmbedding_opensVal _).injective
    rw [hcolval l, hQ0 l t, ← hσ l t]
    have hc : collarClamp (t, halfZero) = 0 := by
      rw [collarClamp_of_mem (halfZero_mem_circleCollarSource t)]
      rfl
    rw [hc, mul_zero]
  have hdisj' : Pairwise fun l l' => Disjoint (col l).target (col l').target := by
    intro l l' hll
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hdisj l l' hll _ hy hy'
  let Q := recollarBase Q0 col (fun l => rfl) hzero hdisj'
  let ι := pieceToCore D hab hreg x₀ ha
  refine ⟨Q, ι, isSmoothEmbedding_pieceToCore D hab hreg x₀ ha, fun l => ⟨σ l, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t s hs hs1
    change opensVal _ (col l (t, halfPoint s hs)).val = c l (σ l t, ε l * s)
    rw [hcolval l]
    have hc : collarClamp (t, halfPoint s hs) = s := by
      rw [collarClamp_of_mem (show (t, halfPoint s hs) ∈ circleCollarSource from hs1)]
      rfl
    rw [hc]
  · intro x
    rw [← opensVal_image_pieceSlab D.smooth hab hreg hint x₀]
    exact mem_image_of_mem _ x.2
  · intro y hy
    rw [← opensVal_image_pieceSlab D.smooth hab hreg hint x₀] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨⟨w, hw⟩, rfl⟩
  · intro x hx
    obtain ⟨l, t, hlt⟩ := exists_pieceGamma_of_level D i sp x hx
    refine ⟨l, t, ?_⟩
    change x = col l (t, halfZero)
    rw [hzero l t]
    apply Subtype.ext
    apply (isOpenEmbedding_opensVal _).injective
    rw [hQ0 l t]
    exact hlt.symm
  · intro l t
    change opensVal _ (col l (t, halfZero)).val = pieceGamma D i sp l t
    rw [hzero l t]
    exact hQ0 l t

end Recollared

section Glue2

variable (D : BaseMorseData B)

theorem exists_shrink_factor (hgap : D.κ < D.level 1 - D.level 0) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ D.level 0 + D.κ < D.level 1 - D.κ * lam ∧
      ∀ i : Fin D.m, 2 * (D.κ * lam) < D.level i.succ - D.level i.castSucc := by
  have hκ := D.κ_pos
  obtain ⟨g, hg, hgi⟩ : ∃ g : ℝ, 0 < g ∧
      ∀ i : Fin D.m, g ≤ D.level i.succ - D.level i.castSucc := by
    by_cases hm : Nonempty (Fin D.m)
    · obtain ⟨i₀, -, hi₀⟩ := Finset.univ.exists_min_image
        (fun i : Fin D.m => D.level i.succ - D.level i.castSucc) (Finset.univ_nonempty_iff.mpr hm)
      exact ⟨_, sub_pos.mpr (level_castSucc_lt_succ D i₀), fun i => hi₀ i (Finset.mem_univ i)⟩
    · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hm⟩
  set d := D.level 1 - D.level 0 - D.κ
  have hd : 0 < d := by simp only [d]; linarith
  refine ⟨min (1 / 2) (min (d / (2 * D.κ)) (g / (4 * D.κ))), ?_, ?_, ?_, fun i => ?_⟩
  · exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  · exact (min_le_left _ _).trans (by norm_num)
  · have h1 : min (1 / 2) (min (d / (2 * D.κ)) (g / (4 * D.κ))) ≤ d / (2 * D.κ) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have h2 : D.κ * min (1 / 2) (min (d / (2 * D.κ)) (g / (4 * D.κ))) ≤ d / 2 := by
      calc _ ≤ D.κ * (d / (2 * D.κ)) := by gcongr
        _ = d / 2 := by field_simp
    simp only [d] at h2 ⊢
    linarith
  · have h1 : min (1 / 2) (min (d / (2 * D.κ)) (g / (4 * D.κ))) ≤ g / (4 * D.κ) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h2 : D.κ * min (1 / 2) (min (d / (2 * D.κ)) (g / (4 * D.κ))) ≤ g / 4 := by
      calc _ ≤ D.κ * (g / (4 * D.κ)) := by gcongr
        _ = g / 4 := by field_simp
    linarith [hgi i]

abbrev slabS (i : Fin D.m) : Set (Ambient B) :=
  slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)

theorem ambientVal_image_slabComponent (i : Fin D.m) (x : Ambient B) :
    ambientVal '' connectedComponentIn (slabS D i) x =
      connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x) := by
  have h2 : ambientVal '' slabS D i = D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ) := by
    rw [slabS, slabSet_eq (level_castSucc_lt_succ D i).le]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨toAmbient ⟨y, slab_interior D i y hy.1⟩, hy, rfl⟩
  rw [image_connectedComponentIn_of_isEmbedding isOpenEmbedding_ambientVal.isEmbedding, h2]

theorem mk_eq_of_component_inter (i : Fin D.m) {x x' : Ambient B} (hx : x ∈ slabS D i)
    (hx' : x' ∈ slabS D i)
    (h : (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x) ∩
      connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        (ambientVal x')).Nonempty) :
    ConnectedComponents.mk (⟨x, hx⟩ : slabS D i) = ConnectedComponents.mk ⟨x', hx'⟩ := by
  obtain ⟨w, hw, hw'⟩ := h
  have heq := (connectedComponentIn_eq hw).trans (connectedComponentIn_eq hw').symm
  have hx'm : ambientVal x' ∈ connectedComponentIn
      (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x) := by
    rw [heq]
    refine mem_connectedComponentIn ?_
    exact (mem_slabSet_iff (level_castSucc_lt_succ D i).le x').mp hx'
  rw [← ambientVal_image_slabComponent] at hx'm
  obtain ⟨y, hy, hyx⟩ := hx'm
  have hyx' : y = x' := ambientVal_injective hyx
  subst hyx'
  rw [connectedComponentIn_eq_image hx] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hz' : z = ⟨y, hx'⟩ := Subtype.ext hzy
  subst hz'
  exact (ConnectedComponents.coe_eq_coe'.mpr hz).symm

def slabRep (i : Fin D.m) (c : ConnectedComponents (slabS D i)) : slabS D i := Quotient.out c

theorem mk_slabRep (i : Fin D.m) (c : ConnectedComponents (slabS D i)) :
    ConnectedComponents.mk (slabRep D i c) = c :=
  Quotient.out_eq c

theorem mem_component_slabRep (i : Fin D.m) {x : Ambient B} (hx : x ∈ slabS D i) :
    ambientVal x ∈ connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
      (ambientVal (slabRep D i (ConnectedComponents.mk ⟨x, hx⟩)).val) := by
  set r := slabRep D i (ConnectedComponents.mk ⟨x, hx⟩)
  have hr : ConnectedComponents.mk r = ConnectedComponents.mk ⟨x, hx⟩ := mk_slabRep D i _
  have hmem : (⟨x, hx⟩ : slabS D i) ∈ connectedComponent r :=
    ConnectedComponents.coe_eq_coe'.mp hr.symm
  rw [← ambientVal_image_slabComponent, connectedComponentIn_eq_image r.2]
  exact ⟨x, ⟨⟨x, hx⟩, hmem, rfl⟩, rfl⟩

theorem finite_slabComponents (i : Fin D.m) : Finite (ConnectedComponents (slabS D i)) := by
  let := (ambientSlabAtlas D.smooth (level_castSucc_lt_succ D i) (slab_regular D i)).toChartedSpace
  have : LocallyConnectedSpace (slabS D i) :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) _
  have : CompactSpace (slabS D i) := isCompact_iff_compactSpace.mp
    (isCompact_ambientSlab D.smooth (level_castSucc_lt_succ D i) (slab_interior D i))
  exact finite_components_of_compact

end Glue2

section Geo

variable {f : B.Carrier → ℝ}
  {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
    B.Carrier ∞} {L κ' : ℝ}

theorem abs_sub_lt_of_mem_target (hcs : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (hκ' : 0 < κ')
    (hcf : ∀ t s, -1 < s → s < 1 → f (c (t, s)) = L + κ' * s) {y : B.Carrier}
    (hy : y ∈ c.target) : |f y - L| < κ' := by
  have hs : c.symm y ∈ c.source := c.map_target hy
  rw [hcs] at hs
  have hr : c (c.symm y) = y := c.right_inv hy
  have h := hcf (c.symm y).1 (c.symm y).2 hs.1 hs.2
  rw [show ((c.symm y).1, (c.symm y).2) = c.symm y from rfl, hr] at h
  rw [h, add_sub_cancel_left, abs_mul, abs_of_pos hκ']
  have : |(c.symm y).2| < 1 := abs_lt.mpr hs
  nlinarith [abs_nonneg (c.symm y).2]

theorem side_of_mem_target (hcs : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (hκ' : 0 < κ')
    (hcf : ∀ t s, -1 < s → s < 1 → f (c (t, s)) = L + κ' * s) {a b ε : ℝ}
    (hL : (L = a ∧ ε = 1) ∨ (L = b ∧ ε = -1)) {y : B.Carrier} (hy : y ∈ c.target)
    (hyab : f y ∈ Icc a b) : 0 ≤ ε * (c.symm y).2 := by
  have hs : c.symm y ∈ c.source := c.map_target hy
  rw [hcs] at hs
  have hr : c (c.symm y) = y := c.right_inv hy
  have h := hcf (c.symm y).1 (c.symm y).2 hs.1 hs.2
  rw [show ((c.symm y).1, (c.symm y).2) = c.symm y from rfl, hr] at h
  rcases hL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h1 := hyab.1
    rw [h] at h1
    have : 0 ≤ κ' * (c.symm y).2 := by linarith
    nlinarith
  · have h1 := hyab.2
    rw [h] at h1
    have : κ' * (c.symm y).2 ≤ 0 := by linarith
    nlinarith

theorem half_mem_component (hcs : c.source = {p | -1 < p.2 ∧ p.2 < 1})
    (hcf : ∀ t s, -1 < s → s < 1 → f (c (t, s)) = L + κ' * s)
    {a b ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hab' : ∀ s, 0 ≤ s → s < 1 → L + κ' * (ε * s) ∈ Icc a b) {z : B.Carrier}
    (hzero : ∀ t, c (t, 0) ∈ connectedComponentIn (f ⁻¹' Icc a b) z)
    (t : Circle) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    c (t, ε * s) ∈ connectedComponentIn (f ⁻¹' Icc a b) z := by
  have habs (s' : ℝ) : |ε * s'| = |s'| := by rcases hε with h | h <;> rw [h] <;> simp
  have hsrc (s' : ℝ) (hs' : s' ∈ Icc 0 s) : (t, ε * s') ∈ c.source := by
    rw [hcs]
    have : |ε * s'| < 1 := by rw [habs, abs_of_nonneg hs'.1]; linarith [hs'.2]
    exact abs_lt.mp this
  have hpath : IsPreconnected ((fun s' => c (t, ε * s')) '' Icc 0 s) := by
    refine isPreconnected_Icc.image _ ?_
    refine c.contMDiffOn.continuousOn.comp (continuous_const.prodMk
      (continuous_const.mul continuous_id)).continuousOn fun s' hs' => hsrc s' hs'
  have hsub : (fun s' => c (t, ε * s')) '' Icc 0 s ⊆ f ⁻¹' Icc a b := by
    rintro z ⟨s', hs', rfl⟩
    have hs'' := hsrc s' hs'
    rw [hcs] at hs''
    rw [mem_preimage, hcf t (ε * s') hs''.1 hs''.2]
    exact hab' s' hs'.1 (hs'.2.trans_lt hs1)
  have h0 : c (t, ε * 0) = c (t, 0) := by rw [mul_zero]
  have hmem0 : c (t, ε * 0) ∈ (fun s' => c (t, ε * s')) '' Icc 0 s := ⟨0, ⟨le_rfl, hs0⟩, rfl⟩
  have hK := hzero t
  rw [← h0] at hK
  rw [connectedComponentIn_eq hK]
  exact hpath.subset_connectedComponentIn hmem0 hsub ⟨s, ⟨hs0, le_rfl⟩, rfl⟩

end Geo

section Assembly

variable (D : BaseMorseData B)
  (sp : ∀ (i : Fin D.m) (x₀ : Ambient B) (hx₀ : x₀ ∈ slabS D i), SlabPiece D i hx₀)

abbrev PIdx := Σ i : Fin D.m, ConnectedComponents (slabS D i)

def pRep (π : PIdx D) : slabS D π.1 := slabRep D π.1 π.2

def pSp (π : PIdx D) : SlabPiece D π.1 (pRep D π).2 := sp π.1 (pRep D π).val (pRep D π).2

def pGam (π : PIdx D) (l : Fin (pSp D sp π).k) (t : Circle) : B.Carrier :=
  pieceGamma D π.1 (pSp D sp π) l t

def pLvl (π : PIdx D) (l : Fin (pSp D sp π).k) : Fin (D.m + 1) :=
  if (pSp D sp π).lev l then π.1.succ else π.1.castSucc

def pK (π : PIdx D) : Set B.Carrier :=
  connectedComponentIn (D.f ⁻¹' Icc (D.level π.1.castSucc) (D.level π.1.succ))
    (ambientVal (pRep D π).val)

theorem pGam_level (π : PIdx D) (l : Fin (pSp D sp π).k) (t : Circle) :
    D.f (pGam D sp π l t) = D.level (pLvl D sp π l) := by
  rw [pGam, pieceGamma_level, pLvl]
  split_ifs <;> rfl

theorem range_pGam (π : PIdx D) (l : Fin (pSp D sp π).k) :
    range (pGam D sp π l) = connectedComponentIn (D.f ⁻¹' {D.level (pLvl D sp π l)})
      (pGam D sp π l 1) := by
  have h := range_pieceGamma D π.1 (pSp D sp π) l
  have hL : (if (pSp D sp π).lev l then D.level π.1.succ else D.level π.1.castSucc) =
      D.level (pLvl D sp π l) := by
    rw [pLvl]
    split_ifs <;> rfl
  rw [hL] at h
  exact h

theorem pGam_mem_pK (π : PIdx D) (l : Fin (pSp D sp π).k) (t : Circle) :
    pGam D sp π l t ∈ pK D π := by
  have h := opensVal_image_pieceSlab D.smooth (level_castSucc_lt_succ D π.1)
    (slab_regular D π.1) (slab_interior D π.1) (pRep D π).val
  rw [pK, ← h]
  exact mem_image_of_mem _ ((pSp D sp π).e ((pSp D sp π).P.collar l (t, halfZero))).2

theorem eq_of_pK_inter (i : Fin D.m) (c c' : ConnectedComponents (slabS D i))
    (h : (pK D ⟨i, c⟩ ∩ pK D ⟨i, c'⟩).Nonempty) : c = c' := by
  have h1 := mk_eq_of_component_inter D i (pRep D ⟨i, c⟩).2 (pRep D ⟨i, c'⟩).2 h
  rw [show (⟨(pRep D ⟨i, c⟩).val, (pRep D ⟨i, c⟩).2⟩ : slabS D i) = pRep D ⟨i, c⟩ from rfl,
    show (⟨(pRep D ⟨i, c'⟩).val, (pRep D ⟨i, c'⟩).2⟩ : slabS D i) = pRep D ⟨i, c'⟩ from rfl]
    at h1
  rw [pRep, pRep, mk_slabRep, mk_slabRep] at h1
  exact h1

theorem exists_pK_of_mem (i : Fin D.m) {y : B.Carrier}
    (hy : D.f y ∈ Icc (D.level i.castSucc) (D.level i.succ)) :
    ∃ c : ConnectedComponents (slabS D i), y ∈ pK D ⟨i, c⟩ := by
  have hyS : toAmbient ⟨y, slab_interior D i y hy.1⟩ ∈ slabS D i :=
    (mem_slabSet_iff (level_castSucc_lt_succ D i).le _).mpr hy
  exact ⟨ConnectedComponents.mk ⟨_, hyS⟩, mem_component_slabRep D i hyS⟩

theorem exists_pGam_of_mem (π : PIdx D) {y : B.Carrier} (hy : y ∈ pK D π)
    (hyl : D.f y = D.level π.1.castSucc ∨ D.f y = D.level π.1.succ) :
    ∃ l t, pGam D sp π l t = y := by
  have h := opensVal_image_pieceSlab D.smooth (level_castSucc_lt_succ D π.1)
    (slab_regular D π.1) (slab_interior D π.1) (pRep D π).val
  rw [pK, ← h] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact exists_pieceGamma_of_level D π.1 (pSp D sp π) ⟨w, hw⟩ hyl

end Assembly

section Assembly2

variable (D : BaseMorseData B)
  (sp : ∀ (i : Fin D.m) (x₀ : Ambient B) (hx₀ : x₀ ∈ slabS D i), SlabPiece D i hx₀)

theorem pLvl_eq_of_meet {π π' : PIdx D} {l : Fin (pSp D sp π).k} {l' : Fin (pSp D sp π').k}
    (h : (range (pGam D sp π l) ∩ range (pGam D sp π' l')).Nonempty) :
    pLvl D sp π l = pLvl D sp π' l' := by
  obtain ⟨y, ⟨t, rfl⟩, ⟨t', ht'⟩⟩ := h
  have h1 := pGam_level D sp π l t
  have h2 := pGam_level D sp π' l' t'
  rw [ht'] at h2
  exact D.level_strictMono.injective (h1.symm.trans h2)

theorem pIdx_eq_of_meet {π π' : PIdx D} {l : Fin (pSp D sp π).k} {l' : Fin (pSp D sp π').k}
    (h : (range (pGam D sp π l) ∩ range (pGam D sp π' l')).Nonempty) (hi : π.1 = π'.1) :
    π = π' := by
  obtain ⟨i, c⟩ := π
  obtain ⟨i', c'⟩ := π'
  simp only at hi
  subst hi
  obtain ⟨y, ⟨t, rfl⟩, ⟨t', ht'⟩⟩ := h
  have hc := eq_of_pK_inter D i c c' ⟨_, pGam_mem_pK D sp ⟨i, c⟩ l t,
    ht' ▸ pGam_mem_pK D sp ⟨i, c'⟩ l' t'⟩
  rw [hc]

theorem lev_eq_of_pLvl {π : PIdx D} {l : Fin (pSp D sp π).k} :
    (pSp D sp π).lev l = true ↔ pLvl D sp π l = π.1.succ := by
  rw [pLvl]
  split_ifs with h
  · exact ⟨by intro h'; rfl, by intro h'; exact h⟩
  · refine ⟨fun h' => absurd h' h, fun h' => absurd h' ?_⟩
    exact (Fin.castSucc_lt_succ).ne

theorem eq_of_meet_same_slab {n : ℕ} (eP : Fin n ≃ PIdx D) {j j' : Fin n}
    {l : Fin (pSp D sp (eP j)).k} {l' : Fin (pSp D sp (eP j')).k}
    (h : (range (pGam D sp (eP j) l) ∩ range (pGam D sp (eP j') l')).Nonempty)
    (hi : (eP j).1 = (eP j').1) :
    (⟨j, l⟩ : Σ j : Fin n, Fin (pSp D sp (eP j)).k) = ⟨j', l'⟩ := by
  have hπ := pIdx_eq_of_meet D sp h hi
  have hj : j = j' := eP.injective hπ
  subst hj
  by_contra hne
  have hll : l ≠ l' := fun h' => hne (by rw [h'])
  obtain ⟨y, hy, hy'⟩ := h
  exact Set.disjoint_left.mp (disjoint_range_pieceGamma D (eP j).1 (pSp D sp (eP j)) hll) hy hy'

def CIdx {n : ℕ} (eP : Fin n ≃ PIdx D) : Type :=
  {q : Σ j : Fin n, Fin (pSp D sp (eP j)).k //
    (pSp D sp (eP q.1)).lev q.2 = false ∧ (eP q.1).1.val ≠ 0}

theorem lev_false_of_level {π : PIdx D} {l : Fin (pSp D sp π).k} {t : Circle}
    (h : D.f (pGam D sp π l t) = D.level π.1.castSucc) : (pSp D sp π).lev l = false := by
  by_contra hl
  rw [Bool.not_eq_false] at hl
  have h1 := pGam_level D sp π l t
  rw [(lev_eq_of_pLvl D sp).mp hl, h] at h1
  exact (level_castSucc_lt_succ D π.1).ne h1

theorem lev_true_of_level {π : PIdx D} {l : Fin (pSp D sp π).k} {t : Circle}
    (h : D.f (pGam D sp π l t) = D.level π.1.succ) : (pSp D sp π).lev l = true := by
  by_contra hl
  rw [Bool.not_eq_true] at hl
  have h1 := pGam_level D sp π l t
  have hp : pLvl D sp π l = π.1.castSucc := by rw [pLvl, hl]; rfl
  rw [hp, h] at h1
  exact (level_castSucc_lt_succ D π.1).ne h1.symm

theorem exists_circle_at {n : ℕ} (eP : Fin n ≃ PIdx D) (i : Fin D.m) {y : B.Carrier}
    (hy : D.f y ∈ Icc (D.level i.castSucc) (D.level i.succ))
    (hyl : D.f y = D.level i.castSucc ∨ D.f y = D.level i.succ) :
    ∃ (j : Fin n) (l : Fin (pSp D sp (eP j)).k) (t : Circle), (eP j).1 = i ∧
      pGam D sp (eP j) l t = y := by
  obtain ⟨c, hc⟩ := exists_pK_of_mem D i hy
  obtain ⟨j, hj⟩ := eP.surjective ⟨i, c⟩
  have hyK : y ∈ pK D (eP j) := by rw [hj]; exact hc
  have hyl' : D.f y = D.level (eP j).1.castSucc ∨ D.f y = D.level (eP j).1.succ := by
    rw [hj]; exact hyl
  obtain ⟨l, t, hlt⟩ := exists_pGam_of_mem D sp (eP j) hyK hyl'
  exact ⟨j, l, t, by rw [hj], hlt⟩

theorem exists_above {n : ℕ} (eP : Fin n ≃ PIdx D) (j : Fin n) (l : Fin (pSp D sp (eP j)).k)
    (hl : (pSp D sp (eP j)).lev l = true) :
    ∃ q : CIdx D sp eP, (range (pGam D sp (eP q.1.1) q.1.2) ∩
      range (pGam D sp (eP j) l)).Nonempty := by
  set i := (eP j).1
  set y := pGam D sp (eP j) l 1
  have hy : D.f y = D.level i.succ := by
    rw [pGam_level, (lev_eq_of_pLvl D sp).mp hl]
  have hlt : i.val + 1 < D.m := by
    have h1 := D.lt_level_last y
    rw [hy] at h1
    have h2 : i.succ < Fin.last D.m := D.level_strictMono.lt_iff_lt.mp h1
    rw [Fin.lt_def, Fin.val_succ, Fin.val_last] at h2
    exact h2
  set i' : Fin D.m := ⟨i.val + 1, hlt⟩
  have hi' : i'.castSucc = i.succ := Fin.ext (by simp [i'])
  have hyI : D.f y ∈ Icc (D.level i'.castSucc) (D.level i'.succ) := by
    rw [hi', hy]
    exact ⟨le_rfl, (level_castSucc_lt_succ D i').le.trans' (by rw [hi'])⟩
  obtain ⟨j'', l'', t, hj'', hlt''⟩ := exists_circle_at D sp eP i' hyI
    (Or.inl (by rw [hi', hy]))
  have hlev : (pSp D sp (eP j'')).lev l'' = false := by
    apply lev_false_of_level D sp (t := t)
    rw [hlt'', hj'', hi', hy]
  have hne : (eP j'').1.val ≠ 0 := by
    rw [hj'']
    simp [i']
  refine ⟨⟨⟨j'', l''⟩, hlev, hne⟩, ?_⟩
  exact ⟨y, ⟨t, hlt''⟩, ⟨1, rfl⟩⟩

theorem exists_below {n : ℕ} (eP : Fin n ≃ PIdx D) (q : CIdx D sp eP) :
    ∃ r : Σ j : Fin n, Fin (pSp D sp (eP j)).k, (pSp D sp (eP r.1)).lev r.2 = true ∧
      (range (pGam D sp (eP r.1) r.2) ∩ range (pGam D sp (eP q.1.1) q.1.2)).Nonempty := by
  set i := (eP q.1.1).1
  set y := pGam D sp (eP q.1.1) q.1.2 1
  have hy : D.f y = D.level i.castSucc := by
    rw [pGam_level, pLvl, q.2.1]
    rfl
  have hi0 : i.val ≠ 0 := q.2.2
  set i₀ : Fin D.m := ⟨i.val - 1, by omega⟩
  have hi₀ : i₀.succ = i.castSucc := Fin.ext (by simp [i₀]; omega)
  have hyI : D.f y ∈ Icc (D.level i₀.castSucc) (D.level i₀.succ) := by
    rw [hi₀, hy]
    exact ⟨(level_castSucc_lt_succ D i₀).le.trans (by rw [hi₀]), le_rfl⟩
  obtain ⟨j', l', t, hj', hlt'⟩ := exists_circle_at D sp eP i₀ hyI (Or.inr (by rw [hi₀, hy]))
  have hlev : (pSp D sp (eP j')).lev l' = true := by
    apply lev_true_of_level D sp (t := t)
    rw [hlt', hj', hi₀, hy]
  refine ⟨⟨j', l'⟩, hlev, ?_⟩
  exact ⟨y, ⟨t, hlt'⟩, ⟨1, rfl⟩⟩

end Assembly2

section Hyps

variable (D : BaseMorseData B)

theorem shrink_f (U : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
    (Circle × ℝ) B.Carrier ∞) (hUs : U.source = {p | -1 < p.2 ∧ p.2 < 1}) {I : Fin (D.m + 1)}
    (hUf : ∀ t s, -1 < s → s < 1 → D.f (U (t, s)) = D.level I + D.κ * s) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (t : Circle) (s : ℝ) (hs1 : -1 < s) (hs2 : s < 1) :
    D.f (shrinkBicollar U lam hUs hlam0 hlam1 (t, s)) = D.level I + D.κ * lam * s := by
  rw [shrinkBicollar_apply]
  have h : |lam * s| < 1 := by
    rw [abs_mul, abs_of_pos hlam0]
    have : |s| < 1 := abs_lt.mpr ⟨hs1, hs2⟩
    nlinarith [abs_nonneg s]
  rw [hUf t (lam * s) (abs_lt.mp h).1 (abs_lt.mp h).2]
  ring

theorem pieceGamma_mem_image (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp' : SlabPiece D i hx₀) (l : Fin sp'.k) (t : Circle) :
    pieceGamma D i sp' l t ∈ connectedComponentIn
      (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀) := by
  rw [← opensVal_image_pieceSlab D.smooth (level_castSucc_lt_succ D i) (slab_regular D i)
    (slab_interior D i) x₀]
  exact mem_image_of_mem _ (sp'.e (sp'.P.collar l (t, halfZero))).2

theorem exists_recollared_of_data (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp' : SlabPiece D i hx₀) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamb : D.level 0 + D.κ < D.level 1 - D.κ * lam)
    (hlamg : ∀ i : Fin D.m, 2 * (D.κ * lam) < D.level i.succ - D.level i.castSucc)
    (U : Fin sp'.k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
      (Circle × ℝ) B.Carrier ∞)
    (I : Fin sp'.k → Fin (D.m + 1)) (lam' : Fin sp'.k → ℝ)
    (hlam' : ∀ l, lam' l = if sp'.lev l = false ∧ i.val = 0 then 1 else lam)
    (hUs : ∀ l, (U l).source = {p | -1 < p.2 ∧ p.2 < 1})
    (hUr : ∀ l, range (fun t => U l (t, 0)) = range (pieceGamma D i sp' l))
    (hUf : ∀ l t s, -1 < s → s < 1 → D.f (U l (t, s)) = D.level (I l) + D.κ * s)
    (hUc : ∀ l t, IsMIntegralCurveOn (fun s => U l (t, s)) (fun x => D.κ • D.field x)
      (Ioo (-1) 1))
    (hI : ∀ l, D.level (I l) = if sp'.lev l then D.level i.succ else D.level i.castSucc) :
    ∃ (Q : PlanarBase.{u} sp'.k) (ι : Q.surface.Carrier → D.core.Carrier),
      Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind)
        (SurfaceModel.model D.core.kind) ∞ ι ∧
      (∀ l, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
        (ι (Q.collar l (t, halfPoint s hs))).val =
          U l (σ t, lam' l * ((if sp'.lev l then -1 else 1) * s))) ∧
      (∀ x, (ι x).val ∈ connectedComponentIn
        (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)) ∧
      (∀ y ∈ connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        (ambientVal x₀), ∃ x, (ι x).val = y) ∧
      (∀ x, D.f (ι x).val = D.level i.castSucc ∨ D.f (ι x).val = D.level i.succ →
        ∃ l t, x = Q.collar l (t, halfZero)) ∧
      ∀ l t, (ι (Q.collar l (t, halfZero))).val = pieceGamma D i sp' l t := by
  have hκ := D.κ_pos
  have hab := level_castSucc_lt_succ D i
  have hl0 (l : Fin sp'.k) : 0 < lam' l := by rw [hlam' l]; split_ifs <;> linarith
  have hl1 (l : Fin sp'.k) : lam' l ≤ 1 := by rw [hlam' l]; split_ifs <;> linarith
  let c : Fin sp'.k → _ := fun l => shrinkBicollar (U l) (lam' l) (hUs l) (hl0 l) (hl1 l)
  let ε : Fin sp'.k → ℝ := fun l => if sp'.lev l then -1 else 1
  have hcs (l : Fin sp'.k) : (c l).source = {p | -1 < p.2 ∧ p.2 < 1} := rfl
  have hcf (l : Fin sp'.k) (t : Circle) (s : ℝ) (hs1 : -1 < s) (hs2 : s < 1) :
      D.f (c l (t, s)) = D.level (I l) + D.κ * lam' l * s :=
    shrink_f D (U l) (hUs l) (hUf l) (hl0 l) (hl1 l) t s hs1 hs2
  have hcf' (l : Fin sp'.k) : ∀ t s, -1 < s → s < 1 →
      D.f (c l (t, s)) = D.level (I l) + (D.κ * lam' l) * s := fun t s h1 h2 => hcf l t s h1 h2
  have hc0 (l : Fin sp'.k) (t : Circle) : c l (t, 0) = U l (t, 0) := by
    change U l (t, lam' l * 0) = U l (t, 0)
    rw [mul_zero]
  have hκl (l : Fin sp'.k) : 0 < D.κ * lam' l := mul_pos hκ (hl0 l)
  have hε (l : Fin sp'.k) : ε l = 1 ∨ ε l = -1 := by
    simp only [ε]; split_ifs <;> simp
  have hbot (h : i.val = 0) : D.level i.castSucc = D.level 0 ∧ D.level i.succ = D.level 1 := by
    have hm : 1 < D.m + 1 := by have := i.2; omega
    constructor
    · congr 1
      exact Fin.ext (by simp [h])
    · congr 1
      exact Fin.ext (by simp [h, Nat.mod_eq_of_lt hm])
  have hsum (l l' : Fin sp'.k) (hl : sp'.lev l = false) (hl' : sp'.lev l' = true) :
      D.κ * lam' l + D.κ * lam' l' < D.level i.succ - D.level i.castSucc := by
    have e' : lam' l' = lam := by rw [hlam' l', hl']; simp
    rw [e', hlam' l]
    split_ifs with h
    · rw [(hbot h.2).1, (hbot h.2).2, mul_one]
      linarith
    · nlinarith [hlamg i]
  have hgapl (l : Fin sp'.k) : D.κ * lam' l < D.level i.succ - D.level i.castSucc := by
    rw [hlam' l]
    split_ifs with h
    · rw [(hbot h.2).1, (hbot h.2).2, mul_one]
      nlinarith [mul_pos hκ hlam0]
    · nlinarith [hlamg i]
  have hrange (l : Fin sp'.k) (t' : Circle) : ∃ t, pieceGamma D i sp' l t = c l (t', 0) := by
    have h : U l (t', 0) ∈ range (pieceGamma D i sp' l) := hUr l ▸ mem_range_self t'
    obtain ⟨t, ht⟩ := h
    exact ⟨t, by rw [hc0, ht]⟩
  have hrange' (l : Fin sp'.k) (t : Circle) : ∃ t', pieceGamma D i sp' l t = c l (t', 0) := by
    have h : pieceGamma D i sp' l t ∈ range (fun t => U l (t, 0)) := (hUr l).symm ▸ mem_range_self t
    obtain ⟨t', ht'⟩ := h
    exact ⟨t', by rw [hc0, ← ht']⟩
  have hzeroK (l : Fin sp'.k) (t : Circle) : c l (t, 0) ∈ connectedComponentIn
      (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀) := by
    obtain ⟨t₁, ht₁⟩ := hrange l t
    rw [← ht₁]
    exact pieceGamma_mem_image D i sp' l t₁
  have hin (l : Fin sp'.k) (t : Circle) (s : ℝ) (h0 : 0 ≤ s) (h1 : s < 1) :
      ∃ y : slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ),
        opensVal _ y.val = c l (t, ε l * s) := by
    have hmem := half_mem_component (hcs l) (hcf' l) (hε l) (a := D.level i.castSucc)
      (b := D.level i.succ) (fun s' hs0 hs1 => by
        have hIl := hI l
        simp only [ε]
        split_ifs with hlev
        · simp only [hlev, ↓reduceIte] at hIl
          rw [hIl]
          constructor <;> nlinarith [hκl l, hgapl l]
        · simp only [hlev, Bool.false_eq_true, ↓reduceIte] at hIl
          rw [hIl]
          constructor <;> nlinarith [hκl l, hgapl l]) (hzeroK l) t h0 h1
    rw [← opensVal_image_pieceSlab D.smooth hab (slab_regular D i) (slab_interior D i) x₀] at hmem
    obtain ⟨w, hw, hw'⟩ := hmem
    exact ⟨⟨w, hw⟩, hw'⟩
  have hside (l : Fin sp'.k) (y : slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc)
      (D.level i.succ)) (hy : opensVal _ y.val ∈ (c l).target) :
      0 ≤ ε l * ((c l).symm (opensVal _ y.val)).2 := by
    refine side_of_mem_target (hcs l) (hκl l) (hcf' l) (a := D.level i.castSucc)
      (b := D.level i.succ) ?_ hy ((mem_slabSet_iff hab.le _).mp y.2)
    have hIl := hI l
    simp only [ε]
    split_ifs with hlev
    · simp only [hlev, ↓reduceIte] at hIl
      exact Or.inr ⟨hIl, rfl⟩
    · simp only [hlev, Bool.false_eq_true, ↓reduceIte] at hIl
      exact Or.inl ⟨hIl, rfl⟩
  have hdisj (l l' : Fin sp'.k) (hll : l ≠ l') (y : B.Carrier) (hy : y ∈ (c l).target)
      (hy' : y ∈ (c l').target) : False := by
    have h1 := abs_sub_lt_of_mem_target (hcs l) (hκl l) (hcf' l) hy
    have h2 := abs_sub_lt_of_mem_target (hcs l') (hκl l') (hcf' l') hy'
    by_cases hsame : sp'.lev l = sp'.lev l'
    · have hII : I l = I l' := D.level_strictMono.injective (by rw [hI l, hI l', hsame])
      have hlamll : lam' l = lam' l' := by rw [hlam' l, hlam' l', hsame]
      have hp := (c l).map_target hy
      have hp' := (c l').map_target hy'
      have hr : c l ((c l).symm y) = y := (c l).right_inv hy
      have hr' : c l' ((c l').symm y) = y := (c l').right_inv hy'
      rw [hcs] at hp hp'
      have hb1 : |lam' l * ((c l).symm y).2| < 1 := by
        rw [abs_mul, abs_of_pos (hl0 l)]
        have : |((c l).symm y).2| < 1 := abs_lt.mpr hp
        nlinarith [abs_nonneg ((c l).symm y).2, hl1 l]
      have hb2 : |lam' l' * ((c l').symm y).2| < 1 := by
        rw [abs_mul, abs_of_pos (hl0 l')]
        have : |((c l').symm y).2| < 1 := abs_lt.mpr hp'
        nlinarith [abs_nonneg ((c l').symm y).2, hl1 l']
      have heq : U l (((c l).symm y).1, lam' l * ((c l).symm y).2) =
          U l' (((c l').symm y).1, lam' l' * ((c l').symm y).2) := hr.trans hr'.symm
      have hUf' : ∀ t s, -1 < s → s < 1 → D.f (U l' (t, s)) = D.level (I l) + D.κ * s := by
        rw [hII]; exact hUf l'
      obtain ⟨-, h0⟩ := eq_of_bicollar_eq D (hUf l) hUf' (hUc l) (hUc l')
        (abs_lt.mp hb1) (abs_lt.mp hb2) heq
      have hm1 : U l (((c l).symm y).1, 0) ∈ range (pieceGamma D i sp' l) :=
        hUr l ▸ mem_range_self _
      have hm2 : U l (((c l).symm y).1, 0) ∈ range (pieceGamma D i sp' l') := by
        rw [h0]; exact hUr l' ▸ mem_range_self _
      exact Set.disjoint_left.mp (disjoint_range_pieceGamma D i sp' hll) hm1 hm2
    · have hIl := hI l
      have hIl' := hI l'
      have hg := hgapl l
      have hg' := hgapl l'
      rw [abs_lt] at h1 h2
      cases hlv : sp'.lev l <;> cases hlv' : sp'.lev l' <;> rw [hlv, hlv'] at hsame <;>
        simp only [hlv, hlv', Bool.false_eq_true, ↓reduceIte] at hIl hIl'
      · exact absurd rfl hsame
      · rw [hIl] at h1; rw [hIl'] at h2
        have := hsum l l' hlv hlv'
        linarith
      · rw [hIl] at h1; rw [hIl'] at h2
        have := hsum l' l hlv' hlv
        linarith
      · exact absurd rfl hsame
  exact exists_recollared_piece D i sp' c ε hcs hε hrange hrange' hin hside
    (fun l l' hll y hy hy' => hdisj l l' hll y hy hy')

end Hyps

section Assembly3

variable (D : BaseMorseData B)
  (sp : ∀ (i : Fin D.m) (x₀ : Ambient B) (hx₀ : x₀ ∈ slabS D i), SlabPiece D i hx₀)

theorem range_eq_of_meet {π π' : PIdx D} {l : Fin (pSp D sp π).k} {l' : Fin (pSp D sp π').k}
    (h : (range (pGam D sp π l) ∩ range (pGam D sp π' l')).Nonempty) :
    range (pGam D sp π l) = range (pGam D sp π' l') := by
  have hL := pLvl_eq_of_meet D sp h
  obtain ⟨y, hy, hy'⟩ := h
  rw [range_pGam] at hy ⊢
  rw [range_pGam] at hy' ⊢
  rw [hL] at hy ⊢
  rw [connectedComponentIn_eq hy, connectedComponentIn_eq hy']

theorem bottom_level {π : PIdx D} {l : Fin (pSp D sp π).k} (hl : (pSp D sp π).lev l = false)
    (h0 : π.1.val = 0) (t : Circle) : D.f (pGam D sp π l t) = D.level 0 := by
  rw [pGam_level, pLvl, hl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1
  exact Fin.ext (by simp [h0])

theorem pIdx_eq_of_pK_meet {π π' : PIdx D} (h : (pK D π ∩ pK D π').Nonempty)
    (hi : π.1 = π'.1) : π = π' := by
  obtain ⟨i, c⟩ := π
  obtain ⟨i', c'⟩ := π'
  simp only at hi
  subst hi
  rw [eq_of_pK_inter D i c c' h]

include sp in
theorem exists_planarDecomposition_of_pieces (hgap : D.κ < D.level 1 - D.level 0) :
    ∃ P : PlanarDecomposition D.core,
      ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) → ∃ (x₀ : B.Carrier) (hx₀ : D.f x₀ = D.level 0)
        (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
          (P.inclusion j ((P.piece j).collar l (t, halfPoint s hs))).val =
            Classical.choose (D.exists_levelBicollar 0 hx₀) (σ t, s) := by
  classical
  obtain ⟨lam, hlam0, hlam1, hlamb, hlamg⟩ := exists_shrink_factor D hgap
  have hκ := D.κ_pos
  have : ∀ i, Finite (ConnectedComponents (slabS D i)) := finite_slabComponents D
  let n := Nat.card (PIdx D)
  let eP : Fin n ≃ PIdx D := (Finite.equivFin (PIdx D)).symm
  choose bc hbcs hbcr hbcf hbcc using fun (π : PIdx D) (l : Fin (pSp D sp π).k) =>
    D.exists_levelBicollar (pLvl D sp π l) (pGam_level D sp π l 1)
  choose above habove using exists_above D sp eP
  choose below hbelow1 hbelow2 using exists_below D sp eP
  have hbl : ∀ (j : Fin n) (l : Fin (pSp D sp (eP j)).k),
      (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 →
        D.f (pGam D sp (eP j) l 1) = D.level 0 := fun j l h => bottom_level D sp h.1 h.2 1
  let U : (j : Fin n) → (l : Fin (pSp D sp (eP j)).k) → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (SurfaceModel.model B.kind) (Circle × ℝ) B.Carrier ∞ := fun j l =>
    if hl : (pSp D sp (eP j)).lev l = true then bc (eP (above j l hl).1.1) (above j l hl).1.2
    else if hb : (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 then
      Classical.choose (D.exists_levelBicollar 0 (hbl j l hb))
    else bc (eP j) l
  let I : (j : Fin n) → (l : Fin (pSp D sp (eP j)).k) → Fin (D.m + 1) := fun j l =>
    if hl : (pSp D sp (eP j)).lev l = true then pLvl D sp (eP (above j l hl).1.1) (above j l hl).1.2
    else if (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 then 0
    else pLvl D sp (eP j) l
  let lam' : (j : Fin n) → (l : Fin (pSp D sp (eP j)).k) → ℝ := fun j l =>
    if (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 then 1 else lam
  have hdata : ∀ (j : Fin n) (l : Fin (pSp D sp (eP j)).k),
      (U j l).source = {p | -1 < p.2 ∧ p.2 < 1} ∧
      range (fun t => U j l (t, 0)) = range (pGam D sp (eP j) l) ∧
      (∀ t s, -1 < s → s < 1 → D.f (U j l (t, s)) = D.level (I j l) + D.κ * s) ∧
      (∀ t, IsMIntegralCurveOn (fun s => U j l (t, s)) (fun x => D.κ • D.field x)
        (Ioo (-1) 1)) ∧
      D.level (I j l) = if (pSp D sp (eP j)).lev l then D.level (eP j).1.succ
        else D.level (eP j).1.castSucc := by
    intro j l
    by_cases hl : (pSp D sp (eP j)).lev l = true
    · have hU : U j l = bc (eP (above j l hl).1.1) (above j l hl).1.2 := by
        simp only [U, hl, ↓reduceDIte]
      have hI : I j l = pLvl D sp (eP (above j l hl).1.1) (above j l hl).1.2 := by
        simp only [I, hl, ↓reduceDIte]
      rw [hU, hI]
      have hmeet := habove j l hl
      refine ⟨hbcs _ _, ?_, hbcf _ _, hbcc _ _, ?_⟩
      · rw [hbcr, ← range_pGam]
        exact range_eq_of_meet D sp hmeet
      · rw [pLvl_eq_of_meet D sp hmeet, (lev_eq_of_pLvl D sp).mp hl]
        simp only [hl, ↓reduceIte]
    · have hl' : (pSp D sp (eP j)).lev l = false := by simpa using hl
      by_cases hb : (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0
      · have hU : U j l = Classical.choose (D.exists_levelBicollar 0 (hbl j l hb)) := by
          simp [U, hl', hb]
        have hI : I j l = 0 := by simp [I, hl', hb]
        rw [hU, hI]
        obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec (D.exists_levelBicollar 0 (hbl j l hb))
        refine ⟨h1, ?_, h3, h4, ?_⟩
        · rw [h2, range_pGam]
          have hL : D.level (pLvl D sp (eP j) l) = D.level 0 := by
            rw [← pGam_level D sp (eP j) l 1]; exact hbl j l hb
          rw [hL]
        · rw [hl']
          simp only [Bool.false_eq_true, ↓reduceIte]
          congr 1
          exact Fin.ext (by simp [hb.2])
      · have hb' : ¬ (eP j).1.val = 0 := fun h => hb ⟨hl', h⟩
        have hU : U j l = bc (eP j) l := by simp [U, hl', hb']
        have hI : I j l = pLvl D sp (eP j) l := by simp [I, hl', hb']
        rw [hU, hI]
        refine ⟨hbcs _ _, ?_, hbcf _ _, hbcc _ _, ?_⟩
        · rw [hbcr, ← range_pGam]
        · rw [pLvl, hl']
          simp
  choose Q ι hιe hιc hιK hιs hιb hιz using fun j : Fin n =>
    exists_recollared_of_data D (eP j).1 (pSp D sp (eP j)) hlam0 hlam1 hlamb hlamg (U j) (I j)
      (lam' j) (fun l => rfl) (fun l => (hdata j l).1) (fun l => (hdata j l).2.1)
      (fun l => (hdata j l).2.2.1) (fun l => (hdata j l).2.2.2.1) (fun l => (hdata j l).2.2.2.2)
  have : Finite (CIdx D sp eP) := by unfold CIdx; infer_instance
  let nc := Nat.card (CIdx D sp eP)
  let eC : Fin nc ≃ CIdx D sp eP := (Finite.equivFin _).symm
  have hcutlev : ∀ q : CIdx D sp eP, 1 ≤ (pLvl D sp (eP q.1.1) q.1.2).val ∧
      pLvl D sp (eP q.1.1) q.1.2 = (eP q.1.1).1.castSucc := by
    intro q
    have h : pLvl D sp (eP q.1.1) q.1.2 = (eP q.1.1).1.castSucc := by
      rw [pLvl, q.2.1]; rfl
    refine ⟨?_, h⟩
    rw [h, Fin.val_castSucc]
    exact Nat.one_le_iff_ne_zero.mpr q.2.2
  have hlev1 : ∀ q : CIdx D sp eP, D.level 1 ≤ D.level (pLvl D sp (eP q.1.1) q.1.2) := by
    intro q
    apply D.level_strictMono.monotone
    rw [Fin.le_def]
    have hm : 1 < D.m + 1 := by have := (eP q.1.1).1.2; omega
    simp only [Fin.val_one', Nat.mod_eq_of_lt hm]
    exact (hcutlev q).1
  have hpos : ∀ q : CIdx D sp eP, ∀ t s, -1 < s → s < 1 →
      D.level 0 < D.f (bc (eP q.1.1) q.1.2 (t, lam * s)) := by
    intro q t s h1 h2
    have hb : |lam * s| < 1 := by
      rw [abs_mul, abs_of_pos hlam0]
      have : |s| < 1 := abs_lt.mpr ⟨h1, h2⟩
      nlinarith [abs_nonneg s]
    rw [hbcf _ _ t _ (abs_lt.mp hb).1 (abs_lt.mp hb).2]
    have := hlev1 q
    nlinarith [mul_pos hκ hlam0]
  let cut : Fin nc → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ)
      D.core.Carrier ∞ := fun k =>
    coreCut D (bc (eP (eC k).1.1) (eC k).1.2) lam (hbcs _ _) hlam0 hlam1 (hpos (eC k))
  have hzero : ∀ (π : PIdx D) (l : Fin (pSp D sp π).k) (y : B.Carrier),
      y ∈ range (pGam D sp π l) → ∃ t, bc π l (t, 0) = y := by
    intro π l y hy
    rw [range_pGam, ← hbcr] at hy
    exact hy
  have hzero' : ∀ (π : PIdx D) (l : Fin (pSp D sp π).k) (t : Circle),
      bc π l (t, 0) ∈ range (pGam D sp π l) := by
    intro π l t
    rw [range_pGam, ← hbcr]
    exact mem_range_self t
  have hcut_eq : ∀ q q' : CIdx D sp eP,
      (range (pGam D sp (eP q.1.1) q.1.2) ∩ range (pGam D sp (eP q'.1.1) q'.1.2)).Nonempty →
        q = q' := by
    intro q q' h
    have hL := pLvl_eq_of_meet D sp h
    rw [(hcutlev q).2, (hcutlev q').2] at hL
    have hi : (eP q.1.1).1 = (eP q'.1.1).1 := Fin.castSucc_injective _ hL
    exact Subtype.ext (eq_of_meet_same_slab D sp eP h hi)
  have hlevgap : ∀ a b : Fin (D.m + 1), a < b → 2 * (D.κ * lam) < D.level b - D.level a := by
    intro a b hab
    have ha : a.val < D.m := by have := b.2; omega
    have h1 := hlamg ⟨a.val, ha⟩
    have e1 : (⟨a.val, ha⟩ : Fin D.m).castSucc = a := Fin.ext rfl
    have e2 : (⟨a.val, ha⟩ : Fin D.m).succ ≤ b := by rw [Fin.le_def]; simp; omega
    rw [e1] at h1
    have := D.level_strictMono.monotone e2
    linarith
  have hshrink : ∀ (q : CIdx D sp eP) (y : B.Carrier), y ∈ (bc (eP q.1.1) q.1.2).target →
      |((bc (eP q.1.1) q.1.2).symm y).2| < lam →
        |D.f y - D.level (pLvl D sp (eP q.1.1) q.1.2)| < D.κ * lam := by
    intro q y hy hs
    have hp := (bc (eP q.1.1) q.1.2).map_target hy
    rw [hbcs] at hp
    have hr : bc (eP q.1.1) q.1.2 ((bc (eP q.1.1) q.1.2).symm y) = y :=
      (bc (eP q.1.1) q.1.2).right_inv hy
    have h := hbcf (eP q.1.1) q.1.2 ((bc (eP q.1.1) q.1.2).symm y).1
      ((bc (eP q.1.1) q.1.2).symm y).2 hp.1 hp.2
    rw [show (((bc (eP q.1.1) q.1.2).symm y).1, ((bc (eP q.1.1) q.1.2).symm y).2) =
      (bc (eP q.1.1) q.1.2).symm y from rfl, hr] at h
    rw [h, add_sub_cancel_left, abs_mul, abs_of_pos hκ]
    exact mul_lt_mul_of_pos_left hs hκ
  let cutSide : Fin nc → Bool → Σ j : Fin n, Fin (pSp D sp (eP j)).k := fun k b =>
    if b then ⟨(eC k).1.1, (eC k).1.2⟩ else below (eC k)
  have hbotOf : ∀ (j : Fin n) (l : Fin (pSp D sp (eP j)).k),
      (∀ k b, cutSide k b ≠ ⟨j, l⟩) → (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 := by
    intro j l hns
    by_contra hnb
    by_cases hl : (pSp D sp (eP j)).lev l = true
    · apply hns (eC.symm (above j l hl)) false
      change below (eC (eC.symm (above j l hl))) = ⟨j, l⟩
      rw [Equiv.apply_symm_apply]
      have hmeet : (range (pGam D sp (eP (below (above j l hl)).1) (below (above j l hl)).2) ∩
          range (pGam D sp (eP j) l)).Nonempty := by
        rw [range_eq_of_meet D sp (hbelow2 _), range_eq_of_meet D sp (habove j l hl)]
        obtain ⟨t₀⟩ : Nonempty Circle := inferInstance
        exact ⟨_, mem_range_self t₀, mem_range_self t₀⟩
      have hL := pLvl_eq_of_meet D sp hmeet
      rw [(lev_eq_of_pLvl D sp).mp (hbelow1 _), (lev_eq_of_pLvl D sp).mp hl] at hL
      exact eq_of_meet_same_slab D sp eP hmeet (Fin.succ_injective _ hL)
    · have hl' : (pSp D sp (eP j)).lev l = false := by simpa using hl
      have h0 : (eP j).1.val ≠ 0 := fun h => hnb ⟨hl', h⟩
      apply hns (eC.symm ⟨⟨j, l⟩, hl', h0⟩) true
      exact congrArg Subtype.val (Equiv.apply_symm_apply eC ⟨⟨j, l⟩, hl', h0⟩)
  let P : PlanarDecomposition D.core :=
    { cutCount := nc
      cut := cut
      cut_source := fun k => rfl
      cut_interior := by
        intro k y hy
        have h := abs_sub_lt_of_mem_target (hbcs _ _) hκ (hbcf _ _) hy.1
        have h1 := hlev1 (eC k)
        have hne : D.f y.val ≠ D.level 0 := by
          intro h0
          rw [h0, abs_lt] at h
          nlinarith [mul_pos hκ hlam0]
        exact ((SurfaceModel.model D.core.kind).isInteriorPoint_iff_not_isBoundaryPoint y).mpr
          fun hb => hne ((D.core_isBoundaryPoint_iff y).mp hb)
      cut_disjoint := by
        intro k k' hkk
        rw [Set.disjoint_left]
        intro y hy hy'
        set q := eC k with hq
        set q' := eC k' with hq'
        by_cases hL : pLvl D sp (eP q.1.1) q.1.2 = pLvl D sp (eP q'.1.1) q'.1.2
        · have hp := (bc (eP q.1.1) q.1.2).map_target hy.1
          have hp' := (bc (eP q'.1.1) q'.1.2).map_target hy'.1
          rw [hbcs] at hp hp'
          have hr := (bc (eP q.1.1) q.1.2).right_inv hy.1
          have hr' := (bc (eP q'.1.1) q'.1.2).right_inv hy'.1
          have hf' : ∀ t s, -1 < s → s < 1 → D.f (bc (eP q'.1.1) q'.1.2 (t, s)) =
              D.level (pLvl D sp (eP q.1.1) q.1.2) + D.κ * s := by
            rw [hL]; exact hbcf _ _
          obtain ⟨-, h0⟩ := eq_of_bicollar_eq D (hbcf _ _) hf' (hbcc _ _) (hbcc _ _) hp hp'
            (hr.trans hr'.symm)
          have hmeet : (range (pGam D sp (eP q.1.1) q.1.2) ∩
              range (pGam D sp (eP q'.1.1) q'.1.2)).Nonempty :=
            ⟨_, hzero' _ _ _, by rw [h0]; exact hzero' _ _ _⟩
          exact hkk (eC.injective (hcut_eq q q' hmeet))
        · have h1 := hshrink q y.val hy.1 hy.2
          have h2 := hshrink q' y.val hy'.1 hy'.2
          rw [abs_lt] at h1 h2
          rcases lt_or_gt_of_ne hL with h | h
          · have := hlevgap _ _ h
            linarith
          · have := hlevgap _ _ h
            linarith
      pieceCount := n
      piece := fun j => ElementaryBase.planar (pSp D sp (eP j)).k (pSp D sp (eP j)).hk (Q j)
      inclusion := ι
      isSmoothEmbedding := hιe
      covers := by
        refine Set.eq_univ_of_forall fun y => ?_
        have hy0 : D.level 0 ≤ D.f y.val := y.2
        obtain ⟨i, hi⟩ := exists_slab_of_level_zero_le D hy0
        obtain ⟨c, hc⟩ := exists_pK_of_mem D i hi
        obtain ⟨j, hj⟩ := eP.surjective ⟨i, c⟩
        have hyK : y.val ∈ pK D (eP j) := by rw [hj]; exact hc
        obtain ⟨x, hx⟩ := hιs j y.val hyK
        exact mem_iUnion.mpr ⟨j, x, Subtype.ext hx⟩
      cutSide := cutSide
      cutSide_injective := by
        have hlevf : ∀ r r' : Σ j : Fin n, Fin (pSp D sp (eP j)).k, r = r' →
            (pSp D sp (eP r.1)).lev r.2 = (pSp D sp (eP r'.1)).lev r'.2 := by
          rintro r r' rfl; rfl
        have hrb : ∀ q : CIdx D sp eP, range (pGam D sp (eP (below q).1) (below q).2) =
            range (pGam D sp (eP q.1.1) q.1.2) := fun q => range_eq_of_meet D sp (hbelow2 q)
        rintro ⟨k, b⟩ ⟨k', b'⟩ h
        simp only [uncurry] at h
        cases b <;> cases b' <;> simp only [cutSide, Bool.false_eq_true, ↓reduceIte] at h
        · have hq : eC k = eC k' := by
            apply hcut_eq
            rw [← hrb, ← hrb, h]
            obtain ⟨t⟩ : Nonempty Circle := inferInstance
            exact ⟨_, mem_range_self t, mem_range_self t⟩
          rw [eC.injective hq]
        · have := hlevf _ _ h
          rw [hbelow1, (eC k').2.1] at this
          exact absurd this (by decide)
        · have := hlevf _ _ h
          rw [hbelow1, (eC k).2.1] at this
          exact absurd this (by decide)
        · have hq : eC k = eC k' := Subtype.ext h
          rw [eC.injective hq]
      cutSide_collar := by
        intro k b
        have hcutval : ∀ (t : Circle) (s : ℝ), -1 < s → s < 1 →
            (cut k (t, s)).val = bc (eP (eC k).1.1) (eC k).1.2 (t, lam * s) := fun t s h1 h2 =>
          coreCutFun_val D _ lam (hpos (eC k) t s h1 h2).le
        cases b
        · obtain ⟨σ, hσ⟩ := hιc (below (eC k)).1 (below (eC k)).2
          refine ⟨σ, fun t s hs hs1 => ?_⟩
          have hl : (pSp D sp (eP (below (eC k)).1)).lev (below (eC k)).2 = true := hbelow1 (eC k)
          have hab : above (below (eC k)).1 (below (eC k)).2 hl = eC k := by
            apply hcut_eq
            rw [range_eq_of_meet D sp (habove _ _ hl), range_eq_of_meet D sp (hbelow2 (eC k))]
            obtain ⟨t₀⟩ : Nonempty Circle := inferInstance
            exact ⟨_, mem_range_self t₀, mem_range_self t₀⟩
          have hU : U (below (eC k)).1 (below (eC k)).2 = bc (eP (eC k).1.1) (eC k).1.2 := by
            simp only [U, hl, ↓reduceDIte]
            rw [hab]
          have hlam : lam' (below (eC k)).1 (below (eC k)).2 = lam := by simp [lam', hl]
          have h := hσ t s hs hs1
          rw [hU, hlam] at h
          simp only [hl, ↓reduceIte] at h
          apply Subtype.ext
          change (ι (below (eC k)).1 ((Q (below (eC k)).1).collar (below (eC k)).2
            (t, halfPoint s hs))).val = (cut k (σ t, -s)).val
          rw [h, hcutval (σ t) (-s) (by linarith) (by linarith)]
          ring_nf
        · obtain ⟨σ, hσ⟩ := hιc (eC k).1.1 (eC k).1.2
          refine ⟨σ, fun t s hs hs1 => ?_⟩
          have hl : (pSp D sp (eP (eC k).1.1)).lev (eC k).1.2 = false := (eC k).2.1
          have hl' : ¬ (pSp D sp (eP (eC k).1.1)).lev (eC k).1.2 = true := by simp [hl]
          have hb : ¬ ((pSp D sp (eP (eC k).1.1)).lev (eC k).1.2 = false ∧
              (eP (eC k).1.1).1.val = 0) := fun h => (eC k).2.2 h.2
          have hb' : ¬ (eP (eC k).1.1).1.val = 0 := (eC k).2.2
          have hU : U (eC k).1.1 (eC k).1.2 = bc (eP (eC k).1.1) (eC k).1.2 := by
            simp [U, hl, hb']
          have hlam : lam' (eC k).1.1 (eC k).1.2 = lam := by simp only [lam', hb, ↓reduceIte]
          have h := hσ t s hs hs1
          rw [hU, hlam] at h
          simp only [hl, Bool.false_eq_true, ↓reduceIte, one_mul] at h
          apply Subtype.ext
          change (ι (eC k).1.1 ((Q (eC k).1.1).collar (eC k).1.2
            (t, halfPoint s hs))).val = (cut k (σ t, s)).val
          rw [h, hcutval (σ t) s (by linarith) hs1]
      boundary_side := by
        intro j l hns t
        have hbot := hbotOf j l hns
        refine (D.core_isBoundaryPoint_iff _).mpr ?_
        change D.f (ι j ((Q j).collar l (t, halfZero))).val = D.level 0
        rw [hιz j l t]
        exact bottom_level D sp hbot.1 hbot.2 t
      overlap := by
        have hcutzero : ∀ (k : Fin nc) (t : Circle),
            (cut k (t, 0)).val = bc (eP (eC k).1.1) (eC k).1.2 (t, 0) := by
          intro k t
          rw [show (cut k (t, 0)).val = bc (eP (eC k).1.1) (eC k).1.2 (t, lam * 0) from
            coreCutFun_val D _ lam (hpos (eC k) t 0 (by norm_num) (by norm_num)).le, mul_zero]
        have hlow : ∀ (j' : Fin n) (x' : (Q j').surface.Carrier),
            D.f (ι j' x').val = D.level (eP j').1.castSucc → (eP j').1.val ≠ 0 →
              ∃ (k : Fin nc) (t : Circle), ι j' x' = cut k (t, 0) := by
          intro j' x' hfa h0
          obtain ⟨l', t', hx'⟩ := hιb j' x' (Or.inl hfa)
          have hyγ : (ι j' x').val = pGam D sp (eP j') l' t' := by rw [hx', hιz]; rfl
          have hlev : (pSp D sp (eP j')).lev l' = false :=
            lev_false_of_level D sp (t := t') (by rw [← hyγ]; exact hfa)
          obtain ⟨t'', ht''⟩ := hzero (eP j') l' _ ⟨t', hyγ.symm⟩
          refine ⟨eC.symm ⟨⟨j', l'⟩, hlev, h0⟩, t'', Subtype.ext ?_⟩
          rw [hcutzero]
          have he := Equiv.apply_symm_apply eC ⟨⟨j', l'⟩, hlev, h0⟩
          rw [he]
          exact ht''.symm
        intro j j' x x' hjj h
        have hy' : (ι j x).val = (ι j' x').val := congrArg Subtype.val h
        have hyK : (ι j x).val ∈ pK D (eP j) := hιK j x
        have hyK' : (ι j x).val ∈ pK D (eP j') := by rw [hy']; exact hιK j' x'
        have hfy : D.f (ι j x).val ∈ Icc (D.level (eP j).1.castSucc) (D.level (eP j).1.succ) :=
          connectedComponentIn_subset (D.f ⁻¹' Icc (D.level (eP j).1.castSucc)
            (D.level (eP j).1.succ)) _ hyK
        have hfy' : D.f (ι j x).val ∈ Icc (D.level (eP j').1.castSucc)
            (D.level (eP j').1.succ) := connectedComponentIn_subset (D.f ⁻¹' Icc
              (D.level (eP j').1.castSucc) (D.level (eP j').1.succ)) _ hyK'
        by_cases hii : (eP j).1 = (eP j').1
        · exact absurd (eP.injective (pIdx_eq_of_pK_meet D ⟨_, hyK, hyK'⟩ hii)) hjj
        · rcases lt_or_gt_of_ne hii with hlt | hgt
          · have hle : D.level (eP j).1.succ ≤ D.level (eP j').1.castSucc :=
              D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
            have hfa : D.f (ι j' x').val = D.level (eP j').1.castSucc := by
              rw [← hy']; linarith [hfy.2, hfy'.1]
            have h0 : (eP j').1.val ≠ 0 := by
              have := Fin.lt_def.mp hlt; omega
            obtain ⟨k, t, hk⟩ := hlow j' x' hfa h0
            exact ⟨k, t, h.trans hk⟩
          · have hle : D.level (eP j').1.succ ≤ D.level (eP j).1.castSucc :=
              D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
            have hfa : D.f (ι j x).val = D.level (eP j).1.castSucc := by
              linarith [hfy.1, hfy'.2]
            have h0 : (eP j).1.val ≠ 0 := by
              have := Fin.lt_def.mp hgt; omega
            exact hlow j x hfa h0 }
  refine ⟨P, fun j l hns => ?_⟩
  have hb := hbotOf j l hns
  have hl' : ¬ (pSp D sp (eP j)).lev l = true := by simp [hb.1]
  refine ⟨pGam D sp (eP j) l 1, hbl j l hb, ?_⟩
  obtain ⟨σ, hσ⟩ := hιc j l
  refine ⟨σ, fun t s hs hs1 => ?_⟩
  have hU : U j l = Classical.choose (D.exists_levelBicollar 0 (hbl j l hb)) := by
    simp only [U, hl', hb, ↓reduceDIte, and_self, Bool.false_eq_true]
  have hlam : lam' j l = 1 := by simp only [lam', hb, and_self, ↓reduceIte]
  have h := hσ t s hs hs1
  rw [hU, hlam] at h
  simp only [hb.1, Bool.false_eq_true, ↓reduceIte, one_mul] at h
  exact h

end Assembly3

section Final

variable (D : BaseMorseData B)

theorem isPreconnected_pieceLevel_iff (i : Fin D.m) (x₀ : Ambient B) {L : ℝ}
    (hL : L = D.level i.castSucc ∨ L = D.level i.succ) :
    IsPreconnected (pieceFun D.f (slabOpens D i x₀) ⁻¹' {L}) ↔
      IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        (ambientVal x₀) ∩ D.f ⁻¹' {L}) := by
  have hab := level_castSucc_lt_succ D i
  have hLI : L ∈ Icc (D.level i.castSucc) (D.level i.succ) := by
    rcases hL with rfl | rfl
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  have himg : opensVal _ '' (pieceFun D.f (slabOpens D i x₀) ⁻¹' {L}) =
      connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        (ambientVal x₀) ∩ D.f ⁻¹' {L} := by
    rw [← opensVal_image_pieceSlab D.smooth hab (slab_regular D i) (slab_interior D i) x₀]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : pieceFun D.f (slabOpens D i x₀) z = L := hz
      refine ⟨⟨z, (mem_slabSet_iff hab.le z).mpr (hz' ▸ hLI), rfl⟩, hz'⟩
    · rintro ⟨⟨w, -, rfl⟩, hw⟩
      exact ⟨w, hw, rfl⟩
  rw [← himg]
  exact (isOpenEmbedding_opensVal _).isInducing.isPreconnected_image.symm

theorem nonempty_slabPiece
    (h11 : ∀ (i : Fin D.m) (p : B.Carrier), p ∈ D.crit →
      sigNeg (chartHessianAt
        (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
        (extChartAt (SurfaceModel.model B.kind) p p)) = 1 →
      D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ) →
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.castSucc}) ∨
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.succ}))
    (i : Fin D.m) (x₀ : Ambient B) (hx₀ : x₀ ∈ slabS D i) : Nonempty (SlabPiece D i hx₀) := by
  by_cases hcrit : ∃ p ∈ D.crit, p ∈ connectedComponentIn
      (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)
  · obtain ⟨p, hp, hpK⟩ := hcrit
    by_cases hidx : sigNeg (chartHessianAt
        (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
        (extChartAt (SurfaceModel.model B.kind) p p)) = 1
    · have hpI : D.f p ∈ Icc (D.level i.castSucc) (D.level i.succ) :=
        connectedComponentIn_subset (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) _ hpK
      have hpi : D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ) :=
        ⟨lt_of_le_of_ne hpI.1 (crit_value_ne_level D hp _).symm,
          lt_of_le_of_ne hpI.2 (crit_value_ne_level D hp _)⟩
      have h := h11 i p hp hidx hpi
      rw [← connectedComponentIn_eq hpK] at h
      refine nonempty_slabPiece_of_saddle D i hx₀ hp hidx hpK ?_
      rcases h with h | h
      · exact Or.inl fun h' => h ((isPreconnected_pieceLevel_iff D i x₀ (Or.inl rfl)).mp h')
      · exact Or.inr fun h' => h ((isPreconnected_pieceLevel_iff D i x₀ (Or.inr rfl)).mp h')
    · exact nonempty_slabPiece_of_extremum D i hx₀ hp hidx hpK
  · refine nonempty_slabPiece_of_regular D i hx₀ fun y hy hz => hcrit ⟨ambientVal y, ?_, ?_⟩
    · exact (D.mem_crit _).mpr hz
    · rw [← ambientVal_image_slabComponent]
      exact mem_image_of_mem _ hy

theorem exists_planarDecomposition_core_of_gap (hgap : D.κ < D.level 1 - D.level 0)
    (h11 : ∀ (i : Fin D.m) (p : B.Carrier), p ∈ D.crit →
      sigNeg (chartHessianAt
        (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
        (extChartAt (SurfaceModel.model B.kind) p p)) = 1 →
      D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ) →
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.castSucc}) ∨
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.succ})) :
    ∃ P : PlanarDecomposition D.core,
      ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) → ∃ (x₀ : B.Carrier) (hx₀ : D.f x₀ = D.level 0)
        (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
          (P.inclusion j ((P.piece j).collar l (t, halfPoint s hs))).val =
            Classical.choose (D.exists_levelBicollar 0 hx₀) (σ t, s) :=
  exists_planarDecomposition_of_pieces D
    (fun i x₀ hx₀ => Classical.choice (nonempty_slabPiece D h11 i x₀ hx₀)) hgap

end Final

section Kappa

def withKappa (D : BaseMorseData B) (κ' : ℝ) (hκ' : 0 < κ') (hκ'κ : κ' ≤ D.κ) :
    BaseMorseData B :=
  { D with
    κ := κ'
    κ_pos := hκ'
    two_κ_lt_level := by linarith [D.two_κ_lt_level]
    field_unit := fun i x hx => D.field_unit i x (by linarith) }

theorem exists_planarDecomposition_core_of_shrink (D : BaseMorseData B)
    (h11 : ∀ (i : Fin D.m) (p : B.Carrier), p ∈ D.crit →
      sigNeg (chartHessianAt
        (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
        (extChartAt (SurfaceModel.model B.kind) p p)) = 1 →
      D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ) →
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.castSucc}) ∨
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.succ})) :
    ∃ D' : BaseMorseData B, D'.f = D.f ∧ D'.crit = D.crit ∧ D'.m = D.m ∧ D'.κ ≤ D.κ ∧
      (∀ i : Fin (D'.m + 1), ∃ j : Fin (D.m + 1), D'.level i = D.level j) ∧
      ∃ P : PlanarDecomposition D'.core,
        ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) →
          ∃ (x₀ : B.Carrier) (hx₀ : D'.f x₀ = D'.level 0)
            (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
              (P.inclusion j ((P.piece j).collar l (t, halfPoint s hs))).val =
                Classical.choose (D'.exists_levelBicollar 0 hx₀) (σ t, s) := by
  have hm : 0 < D.m := by
    obtain ⟨x, hx⟩ := D.exists_level_zero_lt
    by_contra h
    have h0 : D.m = 0 := by omega
    have hlt := D.lt_level_last x
    have hl : Fin.last D.m = 0 := Fin.ext (by simp [h0])
    rw [hl] at hlt
    linarith
  have hgap0 : 0 < D.level 1 - D.level 0 := by
    have : (0 : Fin (D.m + 1)) < 1 := by
      rw [Fin.lt_def]
      simp [Nat.mod_eq_of_lt (show 1 < D.m + 1 by omega)]
    linarith [D.level_strictMono this]
  set κ' := min D.κ ((D.level 1 - D.level 0) / 2)
  have hκ' : 0 < κ' := lt_min D.κ_pos (by linarith)
  have hκ'κ : κ' ≤ D.κ := min_le_left _ _
  refine ⟨withKappa D κ' hκ' hκ'κ, rfl, rfl, rfl, hκ'κ, fun i => ⟨i, rfl⟩, ?_⟩
  refine exists_planarDecomposition_core_of_gap (withKappa D κ' hκ' hκ'κ) ?_ h11
  change κ' < D.level 1 - D.level 0
  have : κ' ≤ (D.level 1 - D.level 0) / 2 := min_le_right _ _
  linarith

end Kappa

end GC.Seifert.CoreDecomposition
