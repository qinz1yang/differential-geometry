import DifferentialGeometry.Topology.Ehresmann.SurfaceIntervalProductEFE
import DifferentialGeometry.Topology.Embedding.Graph
import DifferentialGeometry.Topology.Embedding.LinearEquiv

/-!
# Inhabitants of the surface interval product interfaces (draft 74 §5.2 D, D74-10)

Lane C14-EDP-FDCf. Compiled inhabitants of the four structures of
`Topology/Ehresmann/SurfaceIntervalProductEFE.lean`, and the kernel run on them:

* `lineSubmersion_EFE`: the identity of `ℝ` over the one-chart line atlas `lineGraphAtlas_BCF`;
* `unitArc_EFE`: `t ↦ t` on `[0, 1]`;
* `pointFibre_EFE`: the zero-dimensional point `EuclideanSpace ℝ (Fin 0)` onto the whole fibre
  `{0}` (a smooth embedding: the graph of a constant followed by a linear equivalence);
* `nonempty_pointIntervalProduct_EFE`: `exists_standard_surface_interval_product_EFE` on these
  data (a whole interval product `{pt} × [0, 1] → ℝ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Topology

local notation "F0" => EuclideanSpace ℝ (Fin 0)

/-- **Inhabitant**: the identity of the real line as a proper smooth submersion over the
one-chart line atlas. -/
def lineSubmersion_EFE : ProperSmoothSurfaceSubmersion_EFE 𝓘(ℝ) ℝ Unit (univ : Set ℝ) where
  toFun := id
  smooth := contMDiff_id
  isOpen_source := isOpen_univ
  proper := fun _ hK _ => hK
  atlas := lineGraphAtlas_BCF
  region := fun _ => univ
  isOpen_region := fun _ => isOpen_univ
  region_cover := fun _ _ => mem_iUnion.mpr ⟨(), mem_univ _⟩
  region_piece := fun _ w _ => ⟨w, mem_univ _, rfl⟩
  submersion := fun _ x _ => by
    change Surjective (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ) id x)
    rw [mfderiv_id]
    exact fun v => ⟨v, rfl⟩

/-- **Inhabitant**: the unit interval `t ↦ t` as a base arc of the line. -/
def unitArc_EFE : SmoothEmbeddedBaseArc_EFE (univ : Set ℝ) where
  toFun := id
  smooth := contDiffOn_id
  injOn := injOn_id _
  deriv_ne := fun t ht => by
    rw [derivWithin_id _ _ (uniqueDiffOn_Icc zero_lt_one t ht)]
    exact one_ne_zero
  mapsTo := fun _ _ => mem_univ _

/-- The linear equivalence `F0 × ℝ ≃ ℝ` (the first factor is a point). -/
def pointProdEquiv_EFE : (F0 × ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

theorem pointProdEquiv_zero_EFE (x : F0) : pointProdEquiv_EFE (x, 0) = 0 := by
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, ← Prod.zero_eq_mk, map_zero]

/-- **Inhabitant**: the zero-dimensional point as the standard whole fibre of the line over `0`. -/
def pointFibre_EFE : StandardWholeSurfaceFibre_EFE lineSubmersion_EFE 𝓘(ℝ, F0) F0 0 where
  emb := pointProdEquiv_EFE ∘ fun x => (id x, (fun _ : F0 => (0 : ℝ)) (id x))
  isSmoothEmbedding := (IsSmoothEmbedding.id.graph contDiff_const).continuousLinearEquiv_comp _
  range_eq := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact pointProdEquiv_zero_EFE x
    · intro hy
      refine ⟨0, ?_⟩
      change pointProdEquiv_EFE (0, 0) = y
      rw [pointProdEquiv_zero_EFE]
      exact hy.symm

/-- **The kernel on the inhabitants**: a whole interval product `{pt} × [0, 1] → ℝ` over the unit
arc, starting at the point fibre. -/
theorem nonempty_pointIntervalProduct_EFE :
    Nonempty (WholeSurfaceIntervalProduct_EFE lineSubmersion_EFE unitArc_EFE pointFibre_EFE) :=
  exists_standard_surface_interval_product_EFE _ _ _

end DifferentialGeometry.Topology.Ehresmann
