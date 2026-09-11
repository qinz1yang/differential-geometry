import DifferentialGeometry.Topology.Morse.SmoothMorseChart
import DifferentialGeometry.Topology.Morse.ModifiedFunction
import DifferentialGeometry.Topology.Morse.Attachment.ModifiedSublevel
import DifferentialGeometry.Topology.Morse.SublevelDeformation
import DifferentialGeometry.Topology.Morse.CellAdjunction

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment
open DifferentialGeometry.Topology.Morse.ManifoldCellAttachment
open DifferentialGeometry.Topology.Homotopy

namespace DifferentialGeometry.Morse

private def homotopyEquivUnderOfHomeomorph {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (j : C(A, X)) (k : C(A, Y)) (e : X ≃ₜ Y) (he : (⟨e, e.continuous_toFun⟩ : C(X, Y)).comp j = k) :
    HomotopyEquivUnder j k where
  toFun := ⟨e, e.continuous_toFun⟩
  invFun := ⟨e.symm, e.symm.continuous_toFun⟩
  map_toBase := he
  map_fromBase := by
    rw [← he]
    ext x
    exact e.left_inv (j x)
  leftInv := (ContinuousMap.HomotopyRel.refl (ContinuousMap.id X) (Set.range j)).cast
    (by ext x; exact (e.left_inv x).symm) rfl
  rightInv := (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) (Set.range k)).cast
    (by ext y; exact (e.right_inv y).symm) rfl

variable {m : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless] [IsManifold I ∞ M]

theorem one_critical_point_cell_attachment (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (k : ℕ) (hk : k ≤ m + 1)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (fun y ↦ f ((extChartAt I p).symm y))
      (extChartAt I p p)) = k)
    (a : ℝ) (ha : 0 < a)
    (hcompact : IsCompact (f ⁻¹' Icc (f p - a) (f p + a)))
    (hunique : ∀ x, f x ∈ Icc (f p - a) (f p + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ε ≤ a ∧
      ∃ φ : C(CellBoundary k, SublevelSpace f (f p - ε)),
        Nonempty (HomotopyEquivUnder
          (sublevelInclusion f (show f p - ε ≤ f p + ε by linarith))
          (ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φ)
            (continuous_adjunctionLower (i := cellBoundaryInclusion k) φ))) := by
  obtain ⟨data₀, hp, _, _, _, hχ, hχinv, hnormal, _⟩ :=
    exists_interior_morse_chart I f hf p BoundarylessManifold.isInteriorPoint k hk hnd hindex
  let R := data₀.R
  let R' := data₀.smoothRadius
  let ε := min a (min (R ^ 2) (R' ^ 2)) / 16
  let δ := Real.sqrt ε / 4
  have hmin : 0 < min a (min (R ^ 2) (R' ^ 2)) :=
    lt_min ha (lt_min (sq_pos_of_pos data₀.radius_pos) (sq_pos_of_pos data₀.smoothRadius_pos))
  have hε : 0 < ε := div_pos hmin (by norm_num)
  have hδ : 0 < δ := div_pos (Real.sqrt_pos.mpr hε) (by norm_num)
  have hεa : ε ≤ a := by
    have h := min_le_left a (min (R ^ 2) (R' ^ 2))
    dsimp [ε]
    linarith
  have hεR : ε ≤ R ^ 2 / 16 := by
    have h := (min_le_right a (min (R ^ 2) (R' ^ 2))).trans (min_le_left _ _)
    exact div_le_div_of_nonneg_right h (by norm_num)
  have hεR' : ε ≤ R' ^ 2 / 16 := by
    have h := (min_le_right a (min (R ^ 2) (R' ^ 2))).trans (min_le_right _ _)
    exact div_le_div_of_nonneg_right h (by norm_num)
  have hδsq : δ ^ 2 = ε / 16 := by
    dsimp [δ]
    rw [div_pow, Real.sq_sqrt hε.le]
    norm_num
  have hbound : 4 * ε + 9 * δ ^ 2 / 4 < R ^ 2 := by rw [hδsq]; nlinarith
  have hbound' : 4 * ε + 9 * δ ^ 2 / 4 < R' ^ 2 := by rw [hδsq]; nlinarith
  have hδε : 9 * δ ^ 2 < 4 * ε := by rw [hδsq]; linarith
  have hsqrt : Real.sqrt (2 * ε) ≤ R := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨data₀.radius_pos.le, by linarith⟩
  let data : MorseChart (m + 1) k hk (f p) I f :=
    { data₀ with ε := ε, epsilon_pos := hε, sqrt_two_epsilon_le_radius := hsqrt }
  let χ : PartialDiffeomorph 𝓘(ℝ, MorseModel (m + 1)) I (MorseModel (m + 1)) M ∞ := {
    toPartialEquiv := data₀.χ.toPartialEquiv
    open_source := data₀.χ.open_source
    open_target := data₀.χ.open_target
    contMDiffOn_toFun := hχ
    contMDiffOn_invFun := hχinv }
  let g := morseModifiedFunction hk (f p) ε δ R data.χ f
  have hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g :=
    DifferentialGeometry.Morse.contMDiff_morseModifiedFunction hk (f p) ε δ R hε hδ hbound data₀.radius_pos
      f hf χ hnormal data₀.closedBall_subset_source
  have hgle : ∀ x, g x ≤ f x :=
    morseModifiedFunction_le_f hk (f p) ε δ R hε data.χ f data₀.normalForm_on
  have hgup : sublevel g (f p + ε) = sublevel f (f p + ε) :=
    sublevel_upper_identity_morseModifiedFunction hk (f p) ε δ R hε hδ hδε data.χ f data₀.normalForm_on
  have hgcompact : IsCompact (g ⁻¹' Icc (f p - ε) (f p + ε)) :=
    isCompact_strip_morseModifiedFunction hk (f p) ε δ R a hε hδ hδε hεa data.χ f
      hf.continuous data₀.normalForm_on hg.continuous hcompact
  have hgreg : ∀ x ∈ g ⁻¹' Icc (f p - ε) (f p + ε), mfderiv I 𝓘(ℝ, ℝ) g x ≠ 0 := by
    intro x hx
    exact no_critical_point_morseModifiedFunction hk (f p) ε δ R R' a hε hδ hδε hbound
      hbound' data₀.radius_pos data₀.smoothRadius_pos hεa I f p data.χ (data₀.map_zero.trans hp)
      data₀.normalForm_on data₀.closedBall_subset_source data₀.symm_contMDiffOn data₀.contMDiffOn hunique hx
  let jg := sublevelInclusionLE hgle (f p - ε)
  let ι := sublevelInclusion f (show f p - ε ≤ f p + ε by linarith)
  let ιg := sublevelInclusion g (show f p - ε ≤ f p + ε by linarith)
  obtain ⟨er, _⟩ := exists_sublevelHomotopyEquivUnder I hg (by linarith) hgcompact hgreg jg
  let eup : SublevelSpace f (f p + ε) ≃ₜ SublevelSpace g (f p + ε) :=
    subtypeSetHomeomorph hgup.symm
  let eu := homotopyEquivUnderOfHomeomorph ι (ιg.comp jg) eup (by ext x; rfl)
  let U := data.χ '' (Set.range (fun z : ClosedCell k ↦
    (cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k)) : MorseModel (m + 1))))
  let ju := sublevelUnionInclusion (f := f) (f p - ε) U
  let elow : HomotopyEquivUnder jg ju :=
    morseModifiedLowerSublevelHomotopyEquivUnder hk (f p) ε δ R hε hδ hbound hsqrt
      data.χ f hg.continuous data₀.normalForm_on data₀.closedBall_subset_source
  have hU : U = cellImage hk (f p) data := by
    change data.χ '' Set.range _ = Set.range (data.χ ∘ _)
    exact (Set.range_comp (g := fun y : MorseModel (m + 1) ↦ data.χ y)
      (f := fun z : ClosedCell k ↦ cellMap (Real.sqrt (2 * ε))
        (z : EuclideanSpace ℝ (Fin k)))).symm
  let ecell : {x : M // x ∈ sublevel f (f p - ε) ∪ U} ≃ₜ
      CellAdjunctionSpace k (cellAttachingMap hk (f p) data) :=
    (subtypeSetHomeomorph (congrArg (sublevel f (f p - ε) ∪ ·) hU)).trans
      (cellAdjunctionHomeomorphLowerUnion data hf.continuous).symm
  let jcell : C(SublevelSpace f (f p - ε), CellAdjunctionSpace k (cellAttachingMap hk (f p) data)) :=
    ⟨adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk (f p) data),
      continuous_adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk (f p) data)⟩
  have hecell : (⟨ecell, ecell.continuous_toFun⟩ : C(_, _)).comp ju = jcell := by
    ext x
    apply (cellAdjunctionHomeomorphLowerUnion data hf.continuous).injective
    change (cellAdjunctionHomeomorphLowerUnion data hf.continuous)
      ((cellAdjunctionHomeomorphLowerUnion data hf.continuous).symm ⟨x.1, Or.inl x.2⟩) = _
    rw [Homeomorph.apply_symm_apply]
    exact (cellAdjunctionHomeomorphLowerUnion_lower data hf.continuous x).symm
  let ec := homotopyEquivUnderOfHomeomorph ju jcell ecell hecell
  exact ⟨ε, hε, hεa, cellAttachingMap hk (f p) data,
    ⟨((eu.trans er rfl).trans elow rfl).trans ec rfl⟩⟩

end DifferentialGeometry.Morse
