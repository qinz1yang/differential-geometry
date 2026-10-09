import DifferentialGeometry.Geometry.Collapse.LatePieceGeometry
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

/-!
# A closed cut component is the whole manifold (A6 CCI)

Let `D : TorusDecomposition M` be a torus decomposition of a connected closed oriented
3-manifold `M` and let `i` be a cut piece whose boundary is empty. Then the cut-piece map
`cutPieceMap D i : (D.component i).Carrier → M.Carrier`
(`Geometry/Collapse/LatePieceGeometry.lean:12`) is a diffeomorphism. Consequently every metric
on the piece is the cut metric induced by a metric on `M` with the same sectional lower bound.
This is the "slice piece → same `M`" identification of review 29 §2b (merged LFR50 design §9).

Proof. A piece with empty boundary consists of interior points of the cut carrier
(`ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val`), so on it the quotient map is the
interior diffeomorphism of the smooth assembly (`SmoothAssembly.interior_map`,
`Topology/ThreeManifold/Geometrization/SmoothTorusReconstruction.lean:37–40`). Hence the cut-piece
map is the composite of four local diffeomorphisms: the open inclusion of the piece into the
interior, `interiorDiffeomorph`, the open inclusion of `interiorImage`, and the reconstruction
diffeomorphism. It is injective, and its range is open and compact in the connected `M`, hence
everything. A bijective local diffeomorphism is a diffeomorphism
(`IsLocalDiffeomorph.diffeomorphOfBijective`, Mathlib). B's helper
`exists_diffeomorph_of_compact_injective_localDiffeomorph` has not been ported to this checkout;
it is not copied: the surjectivity step is proved here for the cut piece directly and the
diffeomorphism comes from Mathlib.

Main results.

* Tier 1: `isLocalDiffeomorph_cutPieceMap_of_closed`, `injective_cutPieceMap_of_closed`,
  `surjective_cutPieceMap_of_closed`, and `exists_diffeomorph_of_closed_cut_component`
  (the plan's statement).
* Transport of sectional lower bounds along a cross-model diffeomorphism:
  `sectionalBoundedBelow_pullbackMetricCross` (any bound `K`, any models).
* Tier 2: `exists_sectionalBoundedBelow_isInducedCutMetric_of_closed_cut_component` (the metric
  on `M` induces the given piece metric and keeps its bound `K`) and
  `exists_sectional_nonneg_of_closed_cut_component` (the plan's statement).
* Converse direction: `sectionalBoundedBelow_of_isInducedCutMetric_of_closed` — if the piece
  metric is induced by `g`, a sectional lower bound for it is a lower bound for `g` itself.
* Consumer on the existing type: `sectionalBoundedBelow_zero_of_nonnegative_cut_piece` reads the
  fields of the `nonnegative` constructor of `HyperbolicOrCollapsed`
  (`LatePieceGeometry.lean:36–40`) and concludes that the ambient metric `g` itself has
  nonnegative sectional curvature and that the piece is diffeomorphic to `M`. (Rewriting that
  constructor is lane B10, not this file.)
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-! ## Transport of sectional lower bounds along a cross-model diffeomorphism -/

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y] [IsManifold J ∞ Y] [T2Space Y]

/-- A sectional lower bound at `Φ x` pulls back to the same bound at `x`. -/
theorem sectionalBoundedBelowAt_pullbackMetricCross
    (g : SmoothRiemannianMetric J Y) (Φ : X ≃ₘ⟮I, J⟯ Y) {K : ℝ} (x : X)
    (hK : Riemannian.SectionalBoundedBelowAt g (Φ x) K) :
    Riemannian.SectionalBoundedBelowAt
      (DifferentialGeometry.Diffeomorph.pullbackMetricCross g Φ) x K := by
  intro v w
  rw [Curvature.metricRm04Standard_pullbackCross,
    DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner,
    DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner,
    DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner]
  exact hK _ _

/-- A global sectional lower bound pulls back along a cross-model diffeomorphism. -/
theorem sectionalBoundedBelow_pullbackMetricCross
    (g : SmoothRiemannianMetric J Y) (Φ : X ≃ₘ⟮I, J⟯ Y) {K : ℝ}
    (hK : Riemannian.SectionalBoundedBelow g K) :
    Riemannian.SectionalBoundedBelow
      (DifferentialGeometry.Diffeomorph.pullbackMetricCross g Φ) K :=
  fun x => sectionalBoundedBelowAt_pullbackMetricCross g Φ x (hK (Φ x))

omit [CompleteSpace F] in
/-- Pulling back along `Φ` the pull-back along `Φ.symm` returns the original metric. -/
theorem pullbackMetricCross_symm_pullbackMetricCross
    (h : SmoothRiemannianMetric I X) (Φ : X ≃ₘ⟮I, J⟯ Y) :
    DifferentialGeometry.Diffeomorph.pullbackMetricCross
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross h Φ.symm) Φ = h := by
  rw [DifferentialGeometry.Diffeomorph.pullbackMetricCross_trans, Diffeomorph.self_trans_symm,
    DifferentialGeometry.Diffeomorph.pullbackMetricCross_refl]

end Transport

/-! ## Tier 1: the cut-piece map of a closed piece is a diffeomorphism -/

section CutPiece

variable {M : ConnectedClosedOrientedManifold.{u} 3}

/-- Every point of a cut piece with empty boundary is an interior point of the cut carrier. -/
theorem mem_interior_of_closed_cut_component (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅)
    (x : D.components.piece i) : x.val ∈ D.carrier.interior := by
  have hxb : x ∉ D.carrier.model.boundary (D.components.piece i) := by
    intro hx
    have hx' : x ∈ (D.component i).model.boundary (D.component i).Carrier := hx
    rw [hclosed] at hx'
    exact hx'
  have hxi : D.carrier.model.IsInteriorPoint x := by
    rcases D.carrier.model.isInteriorPoint_or_isBoundaryPoint x with h | h
    · exact h
    · exact (hxb h).elim
  exact D.carrier.model.isInteriorPoint_iff_isInteriorPoint_val.mp hxi

/-- On a closed piece the cut-piece map factors through the interior diffeomorphism of the
smooth assembly. -/
theorem cutPieceMap_eq_interiorDiffeomorph (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅)
    (x : D.components.piece i) :
    cutPieceMap D i x =
      D.reconstruction.val
        (D.reconstructionAtlas.interiorDiffeomorph
          ⟨x.val, mem_interior_of_closed_cut_component D i hclosed x⟩).val := by
  rw [D.reconstructionAtlas.interior_map]
  rfl

/-- Tier 1, local part: the cut-piece map of a closed piece is a `C^∞` local diffeomorphism. -/
theorem isLocalDiffeomorph_cutPieceMap_of_closed (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅) :
    IsLocalDiffeomorph (D.component i).model (𝓡 3) ∞ (cutPieceMap D i) := by
  let := D.reconstructionAtlas.charts
  have hint := mem_interior_of_closed_cut_component D i hclosed
  have hι : IsLocalDiffeomorph D.carrier.model D.carrier.model ∞
      (fun x : D.components.piece i => (⟨x.val, hint x⟩ : D.carrier.interior)) := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict (V := D.carrier.interior) (f := Subtype.val) hint
      (isLocalDiffeomorph_subtype_val (I := D.carrier.model) (D.components.piece i) x)
  have hΦ := D.reconstructionAtlas.interiorDiffeomorph.isLocalDiffeomorph
  have hval : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Subtype.val : D.reconstructionAtlas.interiorImage → D.boundary.Assembled) :=
    isLocalDiffeomorph_subtype_val _
  have hr := D.reconstruction.val.isLocalDiffeomorph
  have hcomp := isLocalDiffeomorph_comp hr
    (isLocalDiffeomorph_comp hval (isLocalDiffeomorph_comp hΦ hι))
  have heq : (⇑D.reconstruction.val ∘ Subtype.val ∘ ⇑D.reconstructionAtlas.interiorDiffeomorph ∘
      fun x : D.components.piece i => (⟨x.val, hint x⟩ : D.carrier.interior)) =
        cutPieceMap D i := by
    funext x
    exact (cutPieceMap_eq_interiorDiffeomorph D i hclosed x).symm
  rw [← heq]
  exact hcomp

/-- Tier 1: the cut-piece map of a closed piece is injective (interior fibres are points). -/
theorem injective_cutPieceMap_of_closed (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅) :
    Function.Injective (cutPieceMap D i) := by
  intro x y hxy
  rw [cutPieceMap_eq_interiorDiffeomorph D i hclosed x,
    cutPieceMap_eq_interiorDiffeomorph D i hclosed y] at hxy
  have h1 := D.reconstruction.val.injective hxy
  have h2 := D.reconstructionAtlas.interiorDiffeomorph.injective (Subtype.ext h1)
  have h3 : x.val = y.val := congrArg (fun z : D.carrier.interior => z.val) h2
  exact Subtype.ext h3

/-- Tier 1: the cut-piece map of a closed piece is surjective: its range is open (local
diffeomorphism), closed (compact image in a Hausdorff space) and nonempty in the connected `M`. -/
theorem surjective_cutPieceMap_of_closed (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅) :
    Function.Surjective (cutPieceMap D i) := by
  have hf := isLocalDiffeomorph_cutPieceMap_of_closed D i hclosed
  have : ConnectedSpace (D.components.piece i) := D.components.connected i
  have hc : IsClopen (Set.range (cutPieceMap D i)) :=
    ⟨(isCompact_range hf.contMDiff.continuous).isClosed, hf.isOpen_range⟩
  rcases isClopen_iff.mp hc with he | hu
  · obtain ⟨x⟩ := (inferInstance : Nonempty (D.components.piece i))
    have hx : cutPieceMap D i x ∈ Set.range (cutPieceMap D i) := Set.mem_range_self x
    rw [he] at hx
    exact hx.elim
  · exact Set.range_eq_univ.mp hu

/-- Tier 1 (plan statement): a closed cut component is diffeomorphic to `M` by the cut-piece
map. -/
theorem exists_diffeomorph_of_closed_cut_component (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅) :
    ∃ e : Diffeomorph (D.component i).model (𝓡 3) (D.component i).Carrier M.Carrier ∞,
      ∀ x, e x = cutPieceMap D i x :=
  ⟨(isLocalDiffeomorph_cutPieceMap_of_closed D i hclosed).diffeomorphOfBijective
      ⟨injective_cutPieceMap_of_closed D i hclosed, surjective_cutPieceMap_of_closed D i hclosed⟩,
    fun _ => rfl⟩

/-! ## Tier 2: transporting the piece metric to `M` -/

/-- Tier 2, strong form: every metric `h` on a closed cut piece is the cut metric induced by a
metric `g'` on `M` (namely `h` pushed forward by the cut-piece diffeomorphism), and `g'` has every
sectional lower bound that `h` has. -/
theorem exists_sectionalBoundedBelow_isInducedCutMetric_of_closed_cut_component
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier) {K : ℝ}
    (hsec : Riemannian.SectionalBoundedBelow h K) :
    ∃ g' : SmoothRiemannianMetric (𝓡 3) M.Carrier,
      Riemannian.SectionalBoundedBelow g' K ∧ isInducedCutMetric g' D i h := by
  obtain ⟨e, he⟩ := exists_diffeomorph_of_closed_cut_component M D i hclosed
  have hfun : (⇑e : (D.component i).Carrier → M.Carrier) = cutPieceMap D i := funext he
  refine ⟨DifferentialGeometry.Diffeomorph.pullbackMetricCross h e.symm,
    sectionalBoundedBelow_pullbackMetricCross h e.symm hsec, ?_⟩
  intro x v w
  have hback := pullbackMetricCross_symm_pullbackMetricCross h e
  calc h.inner x v w
      = (DifferentialGeometry.Diffeomorph.pullbackMetricCross
          (DifferentialGeometry.Diffeomorph.pullbackMetricCross h e.symm) e).inner x v w := by
        rw [hback]
    _ = _ := by
        rw [DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner, hfun]

/-- Tier 2 (plan statement): a closed cut component with a metric of nonnegative sectional
curvature gives a metric of nonnegative sectional curvature on `M`. -/
theorem exists_sectional_nonneg_of_closed_cut_component (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hsec : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow h 0) :
    ∃ g' : SmoothRiemannianMetric (𝓡 3) M.Carrier,
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0 := by
  obtain ⟨g', hg', -⟩ :=
    exists_sectionalBoundedBelow_isInducedCutMetric_of_closed_cut_component M D i hclosed h hsec
  exact ⟨g', hg'⟩

/-- Converse direction: if the piece metric `h` of a closed cut piece is induced by `g`, then `g`
is the push-forward of `h`, so every sectional lower bound of `h` holds for `g` on all of `M`. -/
theorem sectionalBoundedBelow_of_isInducedCutMetric_of_closed
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {K : ℝ}
    (hsec : Riemannian.SectionalBoundedBelow h K) :
    Riemannian.SectionalBoundedBelow g K := by
  obtain ⟨e, he⟩ := exists_diffeomorph_of_closed_cut_component M D i hclosed
  have hfun : (⇑e : (D.component i).Carrier → M.Carrier) = cutPieceMap D i := funext he
  have hh : h = DifferentialGeometry.Diffeomorph.pullbackMetricCross g e := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner, hfun]
    exact hind x v w
  have hg : g = DifferentialGeometry.Diffeomorph.pullbackMetricCross h e.symm := by
    rw [hh]
    exact (pullbackMetricCross_symm_pullbackMetricCross g e.symm).symm
  rw [hg]
  exact sectionalBoundedBelow_pullbackMetricCross h e.symm hsec

/-! ## Consumer on the existing `HyperbolicOrCollapsed` type -/

/-- Consumer: the fields of the `nonnegative` constructor of `HyperbolicOrCollapsed`
(`LatePieceGeometry.lean:36–40`) already force the cut piece to be `M` (by the cut-piece map) and
the ambient metric `g` to have nonnegative sectional curvature on all of `M`. -/
theorem sectionalBoundedBelow_zero_of_nonnegative_cut_piece
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) (D : TorusDecomposition M) (K : ℕ)
    (A : ℝ → ℝ) (w₀ : ℝ) (i : Fin D.components.count)
    (metric : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (induced : isInducedCutMetric g D i metric)
    (closed : (D.component i).model.boundary (D.component i).Carrier = ∅)
    (curvature : Riemannian.SectionalBoundedBelow metric 0) :
    Riemannian.SectionalBoundedBelow g 0 ∧
      ∃ e : Diffeomorph (D.component i).model (𝓡 3) (D.component i).Carrier M.Carrier ∞,
        ∀ x, e x = cutPieceMap D i x := by
  -- The four fields are exactly those of this constructor.
  have _piece : HyperbolicOrCollapsed g D K A w₀ i :=
    HyperbolicOrCollapsed.nonnegative metric induced closed curvature
  exact ⟨sectionalBoundedBelow_of_isInducedCutMetric_of_closed g D i closed metric induced
    curvature, exists_diffeomorph_of_closed_cut_component M D i closed⟩

end CutPiece

end DifferentialGeometry.Geometry.Collapse
