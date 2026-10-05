import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortTopologyXPI
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions

/-!
# FC39 external-port regression instance: the regions `M₁, M₂, M₃` and the residual faces

For the rows of the external-port instance (two cusps `rad ≥ 2`, `rad ≤ 1`, the slim torus interval
`1 ≤ rad ≤ 3/2`, the empty edge bundle, the circle region `3/2 ≤ rad ≤ 2`):

* `regionM1_XPI : M₁ = {1 ≤ rad ≤ 2}`, `relInt_M1_slim_XPI`, `regionM2_XPI : M₂ = {3/2 ≤ rad ≤ 2}`,
  `regionM3_XPI : M₃ = M₂`;
* the residual faces: exactly the internal face of the outer cusp `0` (`cusp0Face_XPI`, `rad = 2`;
  the inner cusp's internal face is shared with the slim end and is NOT residual) and the new slim
  end (`newEndFace_XPI`, `rad = 3/2`); `boundaryM2_XPI : ∂M₂ = {rad = 3/2} ∪ {rad = 2}`;
* the end kinds, end sets and the shared face (`slimEndKind_some_iff_XPI`, `endSet_XPI`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

/-! ## Unions of pieces -/

theorem slimUnion_XPI :
    extportSlim_XPI.union = {x | 1 ≤ rad_XPI x ∧ rad_XPI x ≤ 3 / 2} := by
  ext x
  simp only [SlimPiecesV2.union, mem_iUnion]
  constructor
  · rintro ⟨j, hx⟩
    change x ∈ range slimPiece_XPI.map at hx
    rw [range_slimPiece_XPI] at hx
    exact hx
  · intro hx
    refine ⟨(0 : Fin 1), ?_⟩
    change x ∈ range slimPiece_XPI.map
    rw [range_slimPiece_XPI]
    exact hx

theorem cuspUnion_XPI :
    (⋃ i, range (extportZeroDomains_XPI.piece i).map) ∪
        ⋃ b, range (extportCuspCores_XPI.piece b).map =
      {x | rad_XPI x ≤ 1 ∨ 2 ≤ rad_XPI x} := by
  ext x
  simp only [mem_union, mem_iUnion, Fin.exists_fin_two, extportCuspCores_piece_XPI,
    range_cuspPiece_zero_XPI, range_cuspPiece_one_XPI, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨i, -⟩ | h | h)
    · exact i.elim0
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-! ## The regions -/

theorem interior_cuspUnion_XPI :
    interior {x : carrierW_XPI.Carrier | rad_XPI x ≤ 1 ∨ 2 ≤ rad_XPI x} =
      {x | rad_XPI x < 1 ∨ 2 < rad_XPI x} := by
  apply Subset.antisymm
  · intro x hx
    have hx' : rad_XPI x ≤ 1 ∨ 2 ≤ rad_XPI x :=
      (interior_subset hx : x ∈ {x : carrierW_XPI.Carrier | rad_XPI x ≤ 1 ∨ 2 ≤ rad_XPI x})
    have hb := rad_bounds_XPI x
    by_contra hne
    simp only [Set.mem_ofPred_eq, not_or, not_lt] at hne
    rcases hx' with h | h
    · obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_scale_above_XPI x (by linarith)
        (isOpen_interior.mem_nhds hx) (show rad_XPI x < 2 by linarith)
      have hy : rad_XPI (scalePt_XPI x r) ≤ 1 ∨ 2 ≤ rad_XPI (scalePt_XPI x r) :=
        (interior_subset hr4 :
          scalePt_XPI x r ∈ {x : carrierW_XPI.Carrier | rad_XPI x ≤ 1 ∨ 2 ≤ rad_XPI x})
      rw [rad_scalePt_of_mem_XPI x (by linarith) hr3] at hy
      rcases hy with hy | hy <;> linarith
    · obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_scale_below_XPI x (by linarith)
        (isOpen_interior.mem_nhds hx) (show (1 : ℝ) < rad_XPI x by linarith)
      have hy : rad_XPI (scalePt_XPI x r) ≤ 1 ∨ 2 ≤ rad_XPI (scalePt_XPI x r) :=
        (interior_subset hr4 :
          scalePt_XPI x r ∈ {x : carrierW_XPI.Carrier | rad_XPI x ≤ 1 ∨ 2 ≤ rad_XPI x})
      rw [rad_scalePt_of_mem_XPI x hr3 (by linarith)] at hy
      rcases hy with hy | hy <;> linarith
  · exact interior_maximal (fun x hx => hx.imp le_of_lt le_of_lt)
      ((isOpen_lt continuous_rad_XPI continuous_const).union
        (isOpen_lt continuous_const continuous_rad_XPI))

/-- **`M₁ = {1 ≤ rad ≤ 2}`.** -/
theorem regionM1_XPI :
    regionM1 extportZeroDomains_XPI extportCuspCores_XPI =
      {x | 1 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} := by
  rw [regionM1, cuspUnion_XPI, interior_cuspUnion_XPI]
  ext x
  simp only [mem_compl_iff, Set.mem_ofPred_eq, not_or, not_lt]

/-- The relative interior of the slim piece in `M₁`: `{1 ≤ rad < 3/2}`. -/
theorem relInt_M1_slim_XPI :
    relInt (regionM1 extportZeroDomains_XPI extportCuspCores_XPI) extportSlim_XPI.union =
      {x | 1 ≤ rad_XPI x ∧ rad_XPI x < 3 / 2} := by
  rw [regionM1_XPI, slimUnion_XPI]
  apply Subset.antisymm
  · intro x hx
    have hxs := relInt_subset_XPI _ _ hx
    refine ⟨hxs.2.1, lt_of_le_of_ne hxs.2.2 fun h => ?_⟩
    refine not_mem_relInt_XPI (fun U hU => ?_) hx
    obtain ⟨r, hr1, hr2, hr3, hr4⟩ :=
      exists_scale_above_XPI x (by linarith) hU (show rad_XPI x < 2 by linarith)
    have hrad := rad_scalePt_of_mem_XPI x (r := r) (by linarith) hr3
    refine ⟨scalePt_XPI x r, hr4, ?_, ?_⟩
    · change 1 ≤ rad_XPI (scalePt_XPI x r) ∧ rad_XPI (scalePt_XPI x r) ≤ 2
      rw [hrad]
      constructor <;> linarith
    · intro hy
      have hy' : rad_XPI (scalePt_XPI x r) ≤ 3 / 2 := hy.2
      rw [hrad] at hy'
      linarith
  · intro x hx
    have hxA : x ∈ {x : carrierW_XPI.Carrier | 1 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} :=
      ⟨hx.1, by linarith [hx.2]⟩
    refine mem_relInt_of_isOpen_XPI (O := {y | rad_XPI y < 3 / 2})
      (isOpen_lt continuous_rad_XPI continuous_const) ?_ hxA hx.2
    intro y hy
    exact ⟨hy.1.1, (hy.2 : rad_XPI y < 3 / 2).le⟩

/-- **`M₂ = {3/2 ≤ rad ≤ 2}`.** -/
theorem regionM2_XPI :
    regionM2 extportSlim_XPI = {x | 3 / 2 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} := by
  rw [regionM2, relInt_M1_slim_XPI, regionM1_XPI]
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_and, not_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith, h2⟩, fun _ => h1⟩

/-- **`M₃ = M₂`** (the edge piece is empty). -/
theorem regionM3_XPI :
    regionM3 extportSlim_XPI extportEdgeBundle_XPI = {x | 3 / 2 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} := by
  rw [regionM3, extportEdge_edgePiece_XPI, relInt_empty_XPI, sdiff_empty, regionM2_XPI]

/-! ## End kinds and end sets -/

theorem slimEndKind_some_iff_XPI {e : extportSlim_XPI.End}
    {F : NeighbourFace extportZeroDomains_XPI extportCuspCores_XPI} :
    extportSlim_XPI.endKind e = some F ↔ e.1.2 = false ∧ F = slimSharedFace_XPI := by
  change slimEndKind_XPI e = some F ↔ _
  unfold slimEndKind_XPI
  cases e.1.2
  · simp only [Bool.cond_false, Option.some.injEq, true_and]
    exact eq_comm
  · simp

theorem slimEndKind_none_iff_XPI {e : extportSlim_XPI.End} :
    extportSlim_XPI.endKind e = none ↔ e.1.2 = true :=
  slimEndKind_eq_none_iff_XPI (e := e)

/-- The ambient end set of a slim end: `rad = 1` (`false`) or `rad = 3/2` (`true`). -/
theorem endSet_XPI (e : extportSlim_XPI.End) :
    extportSlim_XPI.endSet e = {x | rad_XPI x = bandEndRadius_XPI slimRadii_XPI e.1.2} :=
  slimEnd_image_XPI e.1.2

theorem bandEndRadius_slim_false_XPI : bandEndRadius_XPI slimRadii_XPI false = 1 :=
  rfl

theorem bandEndRadius_slim_true_XPI : bandEndRadius_XPI slimRadii_XPI true = 3 / 2 :=
  rfl

theorem neighbourSet_shared_XPI :
    neighbourSet slimSharedFace_XPI = {x : carrierW_XPI.Carrier | rad_XPI x = 1} := by
  change (cuspPiece_XPI 1).map '' range (bandEnd_XPI (cuspRadii_XPI 1) true) = _
  refine ((range_comp _ _).symm).trans ?_
  exact range_bandEnd_map_XPI (cuspRadii_XPI 1) true

/-! ## The residual faces -/

/-- The new slim end. -/
def slimNewEnd_XPI : extportSlim_XPI.NewEnd := ⟨⟨((0 : Fin 1), true), trivial⟩, rfl⟩

/-- **The residual face of the new slim end** (`rad = 3/2`). -/
def newEndFace_XPI : extportSlim_XPI.ResidualFace := .inr slimNewEnd_XPI

/-- **The residual face of the outer cusp `0`** (`rad = 2`, not shared with any slim end). -/
def cusp0Face_XPI : extportSlim_XPI.ResidualFace :=
  .inl ⟨.inr ⟨0, ⟨extportCuspCores_XPI.internalModelFace 0, rfl⟩⟩, fun e h => by
    rw [slimEndKind_some_iff_XPI] at h
    have h2 := congrArg (fun F : NeighbourFace extportZeroDomains_XPI extportCuspCores_XPI =>
      match F with
      | .inl _ => (2 : ℕ)
      | .inr G => G.1.val) h.2
    simp [slimSharedFace_XPI] at h2⟩

theorem residualSet_newEnd_XPI :
    extportSlim_XPI.residualSet newEndFace_XPI = {x | rad_XPI x = 3 / 2} :=
  endSet_XPI slimNewEnd_XPI.1

theorem residualSet_cusp0_XPI :
    extportSlim_XPI.residualSet cusp0Face_XPI = {x | rad_XPI x = 2} := by
  change (cuspPiece_XPI 0).map '' range (bandEnd_XPI (cuspRadii_XPI 0) true) = _
  refine ((range_comp _ _).symm).trans ?_
  exact range_bandEnd_map_XPI (cuspRadii_XPI 0) true

theorem newEnd_eq_XPI (e : extportSlim_XPI.NewEnd) : e = slimNewEnd_XPI := by
  obtain ⟨⟨⟨j, b⟩, hj⟩, he⟩ := e
  have hb : b = true := slimEndKind_none_iff_XPI.mp he
  subst hb
  obtain rfl : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  rfl

/-- **The residual faces are exactly the two faces** `cusp0Face_XPI`, `newEndFace_XPI`. -/
theorem residualFace_cases_XPI (F : extportSlim_XPI.ResidualFace) :
    F = cusp0Face_XPI ∨ F = newEndFace_XPI := by
  rcases F with ⟨F, hF⟩ | e
  · left
    rcases F with ⟨i, G⟩ | G
    · exact i.elim0
    · obtain ⟨b, G, hG⟩ := G
      subst hG
      have hb : b = 0 := by
        by_contra hb1
        have hb1' : b = 1 := by
          rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with h | h
          · exact (hb1 h).elim
          · exact h
        subst hb1'
        exact hF ⟨((0 : Fin 1), false), trivial⟩ rfl
      subst hb
      rfl
  · right
    rw [newEnd_eq_XPI e]
    rfl

theorem residualSet_cases_XPI (F : extportSlim_XPI.ResidualFace) :
    extportSlim_XPI.residualSet F = {x | rad_XPI x = 2} ∨
      extportSlim_XPI.residualSet F = {x | rad_XPI x = 3 / 2} := by
  rcases residualFace_cases_XPI F with rfl | rfl
  · exact Or.inl residualSet_cusp0_XPI
  · exact Or.inr residualSet_newEnd_XPI

/-- **`∂M₂ = {rad = 3/2} ∪ {rad = 2}`.** -/
theorem boundaryM2_XPI :
    extportSlim_XPI.boundaryM2 = {x | rad_XPI x = 3 / 2 ∨ rad_XPI x = 2} := by
  ext x
  simp only [SlimPiecesV2.boundaryM2, mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨F, hF⟩
    rcases residualSet_cases_XPI F with h | h <;> rw [h] at hF
    · exact Or.inr hF
    · exact Or.inl hF
  · rintro (h | h)
    · exact ⟨newEndFace_XPI, by rw [residualSet_newEnd_XPI]; exact h⟩
    · exact ⟨cusp0Face_XPI, by rw [residualSet_cusp0_XPI]; exact h⟩

/-- **`frontier M₂ = ∂M₂`.** -/
theorem frontier_M2_XPI :
    frontier (regionM2 extportSlim_XPI) = extportSlim_XPI.boundaryM2 := by
  rw [regionM2_XPI, boundaryM2_XPI]
  have hcl : IsClosed {x : carrierW_XPI.Carrier | 3 / 2 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} :=
    (isClosed_le continuous_const continuous_rad_XPI).inter
      (isClosed_le continuous_rad_XPI continuous_const)
  have hint : interior {x : carrierW_XPI.Carrier | 3 / 2 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} =
      {x | 3 / 2 < rad_XPI x ∧ rad_XPI x < 2} := by
    apply Subset.antisymm
    · rw [show {x : carrierW_XPI.Carrier | 3 / 2 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} =
          {x | 3 / 2 ≤ rad_XPI x} ∩ {x | rad_XPI x ≤ 2} from rfl, interior_inter]
      exact fun x hx => ⟨interior_le_rad_XPI (by norm_num) hx.1,
        interior_rad_le_XPI (by norm_num) hx.2⟩
    · exact interior_maximal (fun x hx => ⟨hx.1.le, hx.2.le⟩)
        ((isOpen_lt continuous_const continuous_rad_XPI).inter
          (isOpen_lt continuous_rad_XPI continuous_const))
  rw [hcl.frontier_eq, hint]
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_and, not_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    by_cases h : rad_XPI x = 3 / 2
    · exact Or.inl h
    · exact Or.inr (le_antisymm h2 (h3 (lt_of_le_of_ne h1 (Ne.symm h))))
  · rintro (h | h)
    · exact ⟨⟨h.ge, by linarith⟩, fun h' => by linarith⟩
    · exact ⟨⟨by linarith, h.le⟩, fun _ => h.ge⟩

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
