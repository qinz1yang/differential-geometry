import DifferentialGeometry.Topology.Manifold.RegularLevel.Sublevel
import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import Mathlib.Geometry.Manifold.SmoothEmbedding

open private sublevelCoordinates sublevelCoordinates_spec sublevelChart sublevelChart_apply
  from DifferentialGeometry.Topology.Manifold.RegularLevel.Sublevel

/-!
# The inclusion of a regular sublevel is a smooth embedding

Lane LFR54-QUOT (Q1). A regular sublevel `{f ≤ a}` of a boundaryless manifold, with its native
boundary charts `RegularLevel.sublevelChartedSpace` (model `morseModelWithCornersHalfSpace m`),
includes as a smooth embedding into the ambient manifold (`isSmoothEmbedding_sublevel_val`). The
ambient model is any boundaryless `J` transported to `MorseModel (m + 1)` by a linear equivalence
`e`; the embedding is stated for `J` itself. The codomain chart at a point is the sublevel's own
ambient chart followed by `e⁻¹` and `J⁻¹`, in which the inclusion is `u ↦ e⁻¹ u`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry.Topology.Morse DifferentialGeometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel.SublevelEmbedding

variable {m : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]

/-- The inverse of a boundaryless model, as a partial diffeomorphism. -/
def modelInverse (J : ModelWithCorners ℝ E H) [J.Boundaryless] :
    PartialDiffeomorph 𝓘(ℝ, E) J E H ∞ where
  toPartialEquiv := J.toHomeomorph.symm.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    change ContMDiffOn 𝓘(ℝ, E) J ∞ J.symm univ
    simpa only [J.range_eq_univ] using J.contMDiffOn_symm (n := ∞)
  contMDiffOn_invFun := J.contMDiff.contMDiffOn

/-- **The inclusion of a regular sublevel is a smooth embedding.** -/
theorem isSmoothEmbedding_sublevel_val (e : E ≃L[ℝ] MorseModel (m + 1)) {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff (J.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv (J.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ) f x ≠ 0) :
    let _ := sublevelChartedSpace (J.transContinuousLinearEquiv e) hf hr
    IsSmoothEmbedding (morseModelWithCornersHalfSpace m) J ∞
      (Subtype.val : {y : M // f y ≤ a} → M) := by
  let I := J.transContinuousLinearEquiv e
  let _ := sublevelChartedSpace I hf hr
  let _ := sublevelIsManifold I hf hr
  refine ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1}) ?_,
    Topology.IsEmbedding.subtypeVal⟩
  intro x
  let Φ := sublevelCoordinates I hf hr x
  have hspec := sublevelCoordinates_spec I hf hr x
  let Φ' : PartialDiffeomorph J 𝓘(ℝ, MorseModel (m + 1)) M (MorseModel (m + 1)) ∞ :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := e.contMDiffOn_transContinuousLinearEquiv_left.mp Φ.contMDiffOn_toFun
      contMDiffOn_invFun :=
        e.contMDiffOn_transContinuousLinearEquiv_right.mp Φ.contMDiffOn_invFun }
  let b := (Φ'.trans e.symm.toDiffeomorph.toPartialDiffeomorph).trans (modelInverse J)
  have hb (y : M) (hy : y ∈ Φ.source) : y ∈ b.source := by
    change (y ∈ Φ.source ∧ True) ∧ True
    exact ⟨⟨hy, trivial⟩, trivial⟩
  have hbmax : b.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas J ∞ M :=
    b.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      b.contMDiffOn_toFun b.contMDiffOn_invFun
  have hchart : chartAt (MorseHalfSpace m) x = sublevelChart I hf hr x := rfl
  have hformula (y : {y : M // f y ≤ a}) (hy : (y : M) ∈ Φ.source) :
      b.toOpenPartialHomeomorph.extend J y.val =
        e.symm ((chartAt (MorseHalfSpace m) x).extend (morseModelWithCornersHalfSpace m) y) := by
    change J (J.symm (e.symm (Φ y.val))) = e.symm (morseModelWithCornersHalfSpace m
      (sublevelChart I hf hr x y))
    rw [J.right_inv (by rw [J.range_eq_univ]; trivial), morseModelWithCornersHalfSpace_apply,
      sublevelChart_apply I hf hr x hy]
  refine IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ (MorseModel (m + 1)) PUnit.{1}).trans e.symm)
    (chartAt (MorseHalfSpace m) x) b.toOpenPartialHomeomorph (mem_chart_source _ x)
    (hb x.val hspec.1) (IsManifold.chart_mem_maximalAtlas x) hbmax (fun y hy => hb y.val hy) ?_
  intro u hu
  let y := ((chartAt (MorseHalfSpace m) x).extend (morseModelWithCornersHalfSpace m)).symm u
  have hy : y ∈ (chartAt (MorseHalfSpace m) x).source := by
    simpa only [OpenPartialHomeomorph.extend_source] using
      ((chartAt (MorseHalfSpace m) x).extend (morseModelWithCornersHalfSpace m)).map_target hu
  change b.toOpenPartialHomeomorph.extend J y.val = e.symm u
  rw [hformula y hy]
  exact congrArg e.symm
    (((chartAt (MorseHalfSpace m) x).extend (morseModelWithCornersHalfSpace m)).right_inv hu)

end DifferentialGeometry.Geometry.Collapse.ZeroModel.SublevelEmbedding
