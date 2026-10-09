import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitSideDataStatement

/-!
# Mixed side data with a collar germ

Lane N2f, tier 2. The text of the elementary `SideDataGerm`
(`Seifert/MoveSplitCappedCollarAdapterData.lean`, lane X41) with the elementary presentation and
its chosen split datum replaced by a mixed stage `σ` and an explicit split datum `SD`: the maps and
every field of `MixedStage.SideData`, except that the collar formula is asked only on a germ
`s < η t`, with target width `δ_star * s`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (OnSolidBoundary)

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} (SD : σ.SplitData h)
  {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index)

structure SideDataGerm where
  η : Bool → ℝ
  η_pos : ∀ t, 0 < η t
  δ_star : ℝ
  δ_star_pos : 0 < δ_star
  port : Bool → Fin 3
  port_ne : ∀ t, port t ≠ σ.hostSide h
  port_false_ne_true : port false ≠ port true
  holonomy : Bool → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  solid : Bool → (discPlanarBase.{u} 1).surface.Carrier × Circle → N.Carrier
  smooth : ∀ t, ContMDiff ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
    (𝓡 3) ∞ (solid t)
  mfderiv_bijective : ∀ t q, Function.Bijective (mfderiv
    ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1)) (𝓡 3) (solid t) q)
  injective : ∀ t, Function.Injective (solid t)
  collar : ∀ t (p : Torus) (s : ℝ) (hs : 0 ≤ s), s < η t →
    solid t ((discPlanarBase.{u} 1).collar 0 (p.1, halfPoint s hs), p.2) =
      SplitTube.coreMap K (σ.hostMap SD (planarCollarFormula 3 (port t)
        (((holonomy t p).1 : ℂ), δ_star * s), (holonomy t p).2))
  cap_mem : ∀ t w, ∃ q, solid t q = K.cap (a, t) w
  core_mem : ∀ y : σ.toTorus.cutCarrier.Carrier, σ.InSplitRegion (j := j) (b := b) y →
    σ.toTorus.cutMap y ∈ T.core → ∃ t q, solid t q = SplitTube.coreMap K (σ.toTorus.cutMap y)
  image : ∀ t q, (∃ w, solid t q = K.cap (a, t) w) ∨ ∃ y : σ.toTorus.cutCarrier.Carrier,
    σ.InSplitRegion (j := j) (b := b) y ∧ σ.toTorus.cutMap y ∈ T.core ∧
      solid t q = SplitTube.coreMap K (σ.toTorus.cutMap y)
  boundary_of_eq : ∀ q q', solid false q = solid true q' →
    OnSolidBoundary q ∧ OnSolidBoundary q'

namespace SideDataGerm

variable {σ SD K a} (G : σ.SideDataGerm SD K a)

def bound : ℝ := G.δ_star * min 1 (min (G.η false) (G.η true))

theorem bound_pos : 0 < G.bound :=
  mul_pos G.δ_star_pos (lt_min one_pos (lt_min (G.η_pos false) (G.η_pos true)))

theorem ratio_pos {δ₂ : ℝ} (hδ₂ : 0 < δ₂) : 0 < δ₂ / G.δ_star :=
  div_pos hδ₂ G.δ_star_pos

theorem ratio_le_one {δ₂ : ℝ} (hδ₂ : δ₂ ≤ G.bound) : δ₂ / G.δ_star ≤ 1 := by
  apply (div_le_iff₀ G.δ_star_pos).mpr
  exact hδ₂.trans (by
    rw [bound, one_mul]
    simpa using mul_le_mul_of_nonneg_left
      (min_le_left 1 (min (G.η false) (G.η true))) G.δ_star_pos.le)

theorem ratio_mul_lt {δ₂ s : ℝ} (hδ₂ : 0 < δ₂) (hbound : δ₂ ≤ G.bound)
    (hs : s < 1) (t : Bool) : (δ₂ / G.δ_star) * s < G.η t := by
  have hr : δ₂ / G.δ_star ≤ min (G.η false) (G.η true) := by
    apply (div_le_iff₀ G.δ_star_pos).mpr
    exact hbound.trans (by
      rw [bound, mul_comm (min (G.η false) (G.η true)) G.δ_star]
      exact mul_le_mul_of_nonneg_left (min_le_right 1 _) G.δ_star_pos.le)
  have he : min (G.η false) (G.η true) ≤ G.η t := by
    cases t
    · exact min_le_left _ _
    · exact min_le_right _ _
  exact (mul_lt_mul_of_pos_left hs (G.ratio_pos hδ₂)).trans_le
    (by simpa using hr.trans he)

end SideDataGerm

end GC.Seifert.RelativeNormalization.MixedStage
