import DifferentialGeometry.Topology.Morse.RegularSublevel
import DifferentialGeometry.Geometry.Boundary.BoundaryManifold
import DifferentialGeometry.Topology.Morse.CriticalPoints
import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

namespace DifferentialGeometry.Topology.Morse

open scoped Manifold

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

theorem manifoldSublevel_isBoundaryPoint_iff (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ f x.1 = a := by
  classical
  let := manifoldSublevelChartedSpace I f a hf hreg
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_morseHalfSpace_range]
  change (chartAt (MorseHalfSpace m) x x : MorseModel (m + 1)) (Fin.last m) = 0 ↔
    f x.1 = a
  by_cases hx : f x.1 = a
  · have hchart : chartAt (MorseHalfSpace m) x =
        manifoldSublevelBoundaryChart I f a x hx hf hreg := by
      change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) = _
      rw [dif_pos hx]
    rw [hchart]
    exact iff_of_true (manifoldSublevelBoundaryChart_extend_last_zero I f a hf hreg x hx) hx
  · have hlt : f x.1 < a := lt_of_le_of_ne x.2 hx
    have hchart : chartAt (MorseHalfSpace m) x =
        manifoldSublevelInteriorChart I f a x hlt hf := by
      change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) = _
      rw [dif_neg hx]
    rw [hchart]
    exact iff_of_false (ne_of_gt
      (manifoldSublevelInteriorChart_extend_last_pos I f a hf x hlt)) hx

theorem manifoldSublevel_isInteriorPoint_iff (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    (morseModelWithCornersHalfSpace m).IsInteriorPoint x ↔ f x.1 < a := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
    manifoldSublevel_isBoundaryPoint_iff I f a hf hreg]
  exact ⟨lt_of_le_of_ne x.2, ne_of_lt⟩

def manifoldSublevelBoundaryHomeomorph (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    Integral.DivergenceTheorem.WithBoundary.BoundaryManifold
      (morseModelWithCornersHalfSpace m) (SublevelSpace f a) ≃ₜ LevelSetSpace f a := by
  letI := manifoldSublevelChartedSpace I f a hf hreg
  exact
    { toFun := fun x => ⟨x.1.1, (manifoldSublevel_isBoundaryPoint_iff I f a hf hreg x.1).mp x.2⟩
      invFun := fun y => ⟨⟨y.1, le_of_eq y.2⟩,
        (manifoldSublevel_isBoundaryPoint_iff I f a hf hreg _).mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

@[simp]
theorem manifoldSublevelBoundaryHomeomorph_apply_val (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    ∀ x, (manifoldSublevelBoundaryHomeomorph I f a hf hreg x).1 = x.1.1 := fun _ => rfl

@[simp]
theorem manifoldSublevelBoundaryHomeomorph_symm_apply_val (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (y : LevelSetSpace f a) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    ((manifoldSublevelBoundaryHomeomorph I f a hf hreg).symm y).1.1 = y.1 := rfl

end

noncomputable section

open scoped ContDiff

private theorem closure_lt_sublevel_eq_model
    {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
    [I.Boundaryless] [IsManifold I ∞ M]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    closure {x | f x < a} = {x | f x ≤ a} := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  let := manifoldSublevelIsManifold I f a hf hreg
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ (isClosed_le hf.continuous continuous_const)
    intro x hx
    change f x ≤ a
    exact le_of_lt hx
  · intro x hx
    let y : SublevelSpace f a := ⟨x, hx⟩
    have hd := (morseModelWithCornersHalfSpace m).dense_interior (M := SublevelSpace f a) y
    have hi : (Subtype.val : SublevelSpace f a → M) ''
        (morseModelWithCornersHalfSpace m).interior (SublevelSpace f a) = {z | f z < a} := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (manifoldSublevel_isInteriorPoint_iff I f a hf hreg w).mp hw
      · intro hz
        change f z < a at hz
        exact ⟨⟨z, hz.le⟩, (manifoldSublevel_isInteriorPoint_iff I f a hf hreg _).mpr hz, rfl⟩
    have hc := image_closure_subset_closure_image continuous_subtype_val
      (s := (morseModelWithCornersHalfSpace m).interior (SublevelSpace f a)) ⟨y, hd, rfl⟩
    rwa [hi] at hc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem closure_lt_sublevel_eq_sublevel
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    closure {x | f x < a} = {x | f x ≤ a} := by
  by_cases hE : Module.finrank ℝ E = 0
  · let : Subsingleton E := (Module.finrank_zero_iff).mp hE
    have hne (x : M) : f x ≠ a := by
      let : Subsingleton (TangentSpace I x) := by
        unfold TangentSpace
        infer_instance
      intro hx
      apply hreg x hx
      change mfderiv I 𝓘(ℝ, ℝ) f x = 0
      ext v
      have hv : v = 0 := Subsingleton.elim _ _
      rw [hv, map_zero]
      rfl
    have hset : {x : M | f x < a} = {x | f x ≤ a} := by
      ext x
      change f x < a ↔ f x ≤ a
      exact ⟨le_of_lt, fun hx => lt_of_le_of_ne hx (hne x)⟩
    rw [hset, (isClosed_le hf.continuous continuous_const).closure_eq]
  · let m := Module.finrank ℝ E - 1
    have hdim : Module.finrank ℝ E = m + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hE)).symm
    let e : E ≃L[ℝ] MorseModel (m + 1) :=
      ContinuousLinearEquiv.ofFinrankEq (hdim.trans (Module.finrank_fin_fun ℝ).symm)
    let J := I.transContinuousLinearEquiv e
    let hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
      (e.contMDiff_transContinuousLinearEquiv_left).mpr hf
    have hregJ : ∀ x : M, f x = a → ¬ IsCriticalPointAt J f x := fun x hx hc =>
      hreg x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff e x
        (hf.mdifferentiableAt (by simp))).mp hc)
    exact closure_lt_sublevel_eq_model J f a hfJ hregJ

theorem frontier_lt_sublevel_eq_levelSet
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    frontier {x | f x < a} = {x | f x = a} := by
  rw [(isOpen_lt hf.continuous continuous_const).frontier_eq,
    closure_lt_sublevel_eq_sublevel f a hf hreg]
  ext x
  change (f x ≤ a ∧ ¬ f x < a) ↔ f x = a
  exact ⟨fun hx => le_antisymm hx.1 (le_of_not_gt hx.2), fun hx => ⟨hx.le, not_lt_of_ge hx.ge⟩⟩

end

end DifferentialGeometry.Topology.Morse
