import DifferentialGeometry.Geometry.Boundary.ModelBoundary
import DifferentialGeometry.Geometry.Boundary.Orientation
import DifferentialGeometry.Tensor.BilinearForm
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary
namespace EuclideanHalfSpaceInstance

private theorem n_sub_one_add_one (n : ℕ) [NeZero n] : (n - 1) + 1 = n :=
  Nat.sub_one_add_one_eq_of_pos (Nat.pos_of_neZero n)

private def succIndex (n : ℕ) [NeZero n] : Fin (n - 1) → Fin n :=
  fun j => Fin.cast (n_sub_one_add_one n) j.succ

private theorem succIndex_ne_zero (n : ℕ) [NeZero n] (j : Fin (n - 1)) :
    succIndex n j ≠ 0 := by
  intro h
  have hval : (succIndex n j).val = (0 : Fin n).val := by rw [h]
  have hsucc : (succIndex n j).val = j.val + 1 := rfl
  rw [hsucc, Fin.val_zero] at hval
  exact Nat.succ_ne_zero _ hval

private def predIndex (n : ℕ) [NeZero n] (i : Fin n) (h : i ≠ 0) : Fin (n - 1) :=
  ⟨i.val - 1, by
    have hi : i.val < n := i.isLt
    have hipos : 0 < i.val := by
      rcases Nat.eq_zero_or_pos i.val with h0 | h0
      · exact absurd (Fin.ext (h0.trans rfl) : i = 0) h
      · exact h0
    omega⟩

private theorem succIndex_predIndex (n : ℕ) [NeZero n] (i : Fin n) (h : i ≠ 0) :
    succIndex n (predIndex n i h) = i := by
  have hipos : 0 < i.val := by
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · exact absurd (Fin.ext (h0.trans rfl) : i = 0) h
    · exact h0
  apply Fin.ext
  change (i.val - 1) + 1 = i.val
  omega

private theorem predIndex_succIndex (n : ℕ) [NeZero n] (j : Fin (n - 1)) :
    predIndex n (succIndex n j) (succIndex_ne_zero n j) = j := by
  apply Fin.ext
  change (j.val + 1) - 1 = j.val
  omega

private def consZeroFun (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  fun i =>
    if h : i = (0 : Fin n) then 0
    else x (predIndex n i h)

private def tailFun (n : ℕ) [NeZero n] (y : Fin n → ℝ) : Fin (n - 1) → ℝ :=
  fun j => y (succIndex n j)

private theorem consZeroFun_zero (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) :
    consZeroFun n x 0 = 0 := dif_pos rfl

private theorem consZeroFun_succIndex (n : ℕ) [NeZero n]
    (x : Fin (n - 1) → ℝ) (j : Fin (n - 1)) :
    consZeroFun n x (succIndex n j) = x j := by
  unfold consZeroFun
  rw [dif_neg (succIndex_ne_zero n j), predIndex_succIndex]

private theorem tailFun_consZeroFun (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) :
    tailFun n (consZeroFun n x) = x := by
  funext j
  exact consZeroFun_succIndex n x j

private theorem consZeroFun_tailFun (n : ℕ) [NeZero n] (y : Fin n → ℝ)
    (hy : y 0 = 0) :
    consZeroFun n (tailFun n y) = y := by
  funext i
  unfold consZeroFun tailFun
  by_cases h : i = (0 : Fin n)
  · rw [dif_pos h, h]; exact hy.symm
  · rw [dif_neg h, succIndex_predIndex]

private def consZeroCLM (n : ℕ) [NeZero n] :
    (Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    if h : i = (0 : Fin n) then 0
    else
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n - 1) => ℝ)
        (predIndex n i h)

private theorem consZeroCLM_apply (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) :
    consZeroCLM n x = consZeroFun n x := by
  funext i
  unfold consZeroCLM consZeroFun
  rw [ContinuousLinearMap.pi_apply]
  by_cases h : i = (0 : Fin n)
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]; rfl

private def tailCLM (n : ℕ) [NeZero n] :
    (Fin n → ℝ) →L[ℝ] (Fin (n - 1) → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (succIndex n j)

private theorem tailCLM_apply (n : ℕ) [NeZero n] (y : Fin n → ℝ) :
    tailCLM n y = tailFun n y := by
  funext j
  unfold tailCLM tailFun
  rw [ContinuousLinearMap.pi_apply]
  rfl

def inclEuclideanCLM (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    ((consZeroCLM n).comp
      (EuclideanSpace.equiv (Fin (n - 1)) ℝ).toContinuousLinearMap)

def projEuclideanCLM (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
  (EuclideanSpace.equiv (Fin (n - 1)) ℝ).symm.toContinuousLinearMap.comp
    ((tailCLM n).comp
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap)

def inclEuclidean (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin (n - 1)) → EuclideanSpace ℝ (Fin n) :=
  inclEuclideanCLM n

def projEuclidean (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
  projEuclideanCLM n

private theorem inclEuclideanCLM_apply_coord (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin (n - 1))) (i : Fin n) :
    (inclEuclideanCLM n x) i = consZeroFun n x i := by
  change (((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
          ((consZeroCLM n).comp
            (EuclideanSpace.equiv (Fin (n - 1)) ℝ).toContinuousLinearMap)) x) i
        = consZeroFun n x i
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [consZeroCLM_apply]
  rfl

theorem inclEuclideanCLM_succ_apply (n : Nat) (x : EuclideanSpace Real (Fin n)) :
    inclEuclideanCLM (n + 1) x = WithLp.toLp 2 (Fin.cons (α := fun _ => Real) 0 x) := by
  ext i
  rw [inclEuclideanCLM_apply_coord]
  refine Fin.cases ?_ (fun j => ?_) i
  · exact consZeroFun_zero (n + 1) x
  · have hj : j.succ = succIndex (n + 1) j := Fin.ext rfl
    change consZeroFun (n + 1) x j.succ = x j
    rw [hj, consZeroFun_succIndex]

private theorem projEuclideanCLM_apply_coord (n : ℕ) [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) (j : Fin (n - 1)) :
    (projEuclideanCLM n y) j = tailFun n y j := by
  change (((EuclideanSpace.equiv (Fin (n - 1)) ℝ).symm.toContinuousLinearMap.comp
          ((tailCLM n).comp
            (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap)) y) j
        = tailFun n y j
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [tailCLM_apply]
  rfl

theorem inclEuclidean_zero_coord (n : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin (n - 1))) :
    inclEuclidean n x 0 = 0 := by
  change (inclEuclideanCLM n x) (0 : Fin n) = 0
  rw [inclEuclideanCLM_apply_coord]
  exact consZeroFun_zero n _

theorem projEuclidean_inclEuclidean (n : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin (n - 1))) :
    projEuclidean n (inclEuclidean n x) = x := by
  apply (EuclideanSpace.equiv (Fin (n - 1)) ℝ).injective
  funext j
  change (projEuclideanCLM n (inclEuclideanCLM n x)) j = (x : Fin (n - 1) → ℝ) j
  rw [projEuclideanCLM_apply_coord]
  unfold tailFun
  rw [inclEuclideanCLM_apply_coord]
  exact consZeroFun_succIndex n _ _

theorem inclEuclidean_contDiff (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (inclEuclidean n) :=
  (inclEuclideanCLM n).contDiff

theorem projEuclidean_contDiff (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (projEuclidean n) :=
  (projEuclideanCLM n).contDiff

theorem inclEuclidean_continuous (n : ℕ) [NeZero n] :
    Continuous (inclEuclidean n) :=
  (inclEuclideanCLM n).continuous

theorem projEuclidean_continuous (n : ℕ) [NeZero n] :
    Continuous (projEuclidean n) :=
  (projEuclideanCLM n).continuous

theorem inclEuclidean_injective (n : ℕ) [NeZero n] :
    Function.Injective (inclEuclidean n) := by
  intro x y hxy
  have hx := projEuclidean_inclEuclidean n x
  have hy := projEuclidean_inclEuclidean n y
  rw [hxy] at hx
  exact hx.symm.trans hy

theorem range_inclEuclidean (n : ℕ) [NeZero n] :
    Set.range (inclEuclidean n) =
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  ext y
  simp only [mem_range, mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact inclEuclidean_zero_coord n x
  · intro hy
    refine ⟨projEuclidean n y, ?_⟩
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    funext i
    change (inclEuclideanCLM n (projEuclideanCLM n y)) i = (y : Fin n → ℝ) i
    rw [inclEuclideanCLM_apply_coord]
    by_cases h : i = (0 : Fin n)
    · rw [h, consZeroFun_zero]
      exact hy.symm
    · unfold consZeroFun
      rw [dif_neg h]
      rw [projEuclideanCLM_apply_coord]
      unfold tailFun
      rw [succIndex_predIndex]

theorem inclEuclidean_isClosed_range (n : ℕ) [NeZero n] :
    IsClosed (Set.range (inclEuclidean n)) := by
  rw [range_inclEuclidean]
  have heq : {y : EuclideanSpace ℝ (Fin n) | y 0 = 0}
      = (fun y : EuclideanSpace ℝ (Fin n) => y 0) ⁻¹' {0} := rfl
  rw [heq]
  refine IsClosed.preimage ?_ isClosed_singleton
  exact (PiLp.continuous_apply 2 _ 0)

theorem inclEuclidean_isInducing (n : ℕ) [NeZero n] :
    IsInducing (inclEuclidean n) := by
  refine ⟨?_⟩
  apply le_antisymm
  · exact (inclEuclidean_continuous n).le_induced
  · intro U hU
    refine ⟨(projEuclidean n)⁻¹' U,
        (projEuclidean_continuous n).isOpen_preimage U hU, ?_⟩
    ext x
    simp [projEuclidean_inclEuclidean]

def inclH (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin (n - 1)) → EuclideanHalfSpace n :=
  fun x => ⟨inclEuclidean n x, by
    rw [inclEuclidean_zero_coord]⟩

@[simp]
theorem inclH_val (n : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin (n - 1))) :
    (inclH n x).val = inclEuclidean n x := rfl

theorem inclH_continuous (n : ℕ) [NeZero n] : Continuous (inclH n) :=
  Continuous.subtype_mk (inclEuclidean_continuous n) _

theorem inclH_injective (n : ℕ) [NeZero n] : Function.Injective (inclH n) := by
  intro x y hxy
  have hval : (inclH n x).val = (inclH n y).val := by rw [hxy]
  rw [inclH_val, inclH_val] at hval
  exact inclEuclidean_injective n hval

theorem inclH_isInducing (n : ℕ) [NeZero n] : IsInducing (inclH n) := by
  have h_comp_inducing :
      IsInducing ((Subtype.val : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n))
                    ∘ inclH n) := by
    change IsInducing (inclEuclidean n)
    exact inclEuclidean_isInducing n
  exact IsInducing.of_comp (inclH_continuous n) continuous_subtype_val h_comp_inducing

theorem range_modelWithCorners_comp_inclH (n : ℕ) [NeZero n] :
    Set.range (modelWithCornersEuclideanHalfSpace n ∘ inclH n) =
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  ext y
  simp only [mem_range, Function.comp_apply, mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    change inclEuclidean n x 0 = 0
    exact inclEuclidean_zero_coord n x
  · intro hy
    have hin : y ∈ Set.range (inclEuclidean n) := by
      rw [range_inclEuclidean]; exact hy
    obtain ⟨x, hx⟩ := hin
    refine ⟨x, ?_⟩
    change (inclH n x).val = y
    rw [inclH_val]
    exact hx

theorem frontier_range_modelWithCornersEuclideanHalfSpace_eq (n : ℕ) [NeZero n] :
    frontier (Set.range (modelWithCornersEuclideanHalfSpace n)) =
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  ext y
  exact eq_comm

theorem comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm (n : ℕ) [NeZero n] :
    (modelWithCornersEuclideanHalfSpace n :
        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n))
        ∘ inclH n
        ∘ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).symm
    = inclEuclidean n := by
  funext x
  rfl

private theorem single_zero_one_apply_zero (n : ℕ) [NeZero n] :
    (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0 = 1 := by
  rw [show (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) =
        PiLp.single 2 (0 : Fin n) (1 : ℝ) from rfl]
  rw [PiLp.single_apply]
  simp

private theorem single_zero_one_notMem_hyperplane (n : ℕ) [NeZero n] :
    EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∉
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  intro hmem
  have : (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0 = 1 :=
    single_zero_one_apply_zero n
  have : (1 : ℝ) = 0 := this ▸ hmem
  exact one_ne_zero this

private theorem fderiv_inclEuclidean (n : ℕ) [NeZero n]
    (y : EuclideanSpace ℝ (Fin (n - 1))) :
    fderiv ℝ (inclEuclidean n) y = inclEuclideanCLM n := by
  change fderiv ℝ (inclEuclideanCLM n : EuclideanSpace ℝ (Fin (n - 1)) →
      EuclideanSpace ℝ (Fin n)) y = inclEuclideanCLM n
  exact (inclEuclideanCLM n).fderiv

private theorem range_inclEuclideanCLM (n : ℕ) [NeZero n] :
    Set.range (inclEuclideanCLM n) = Set.range (inclEuclidean n) := rfl

private theorem single_zero_one_transverse (n : ℕ) [NeZero n] :
    ∀ y : EuclideanSpace ℝ (Fin (n - 1)),
      EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∉
        Set.range (fderiv ℝ
          ((modelWithCornersEuclideanHalfSpace n :
              EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n))
            ∘ inclH n
            ∘ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).symm) y) := by
  intro y
  rw [comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm,
      fderiv_inclEuclidean n y, range_inclEuclideanCLM, range_inclEuclidean]
  exact single_zero_one_notMem_hyperplane n

private theorem hyperplane_basisAddHaar_zero (n : ℕ) [NeZero n] :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ((Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).addHaar :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} = 0 := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  have : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  set ker : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.proj 0 :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).toLinearMap.ker with hker_def
  have hsubm : ({y : EuclideanSpace ℝ (Fin n) | y 0 = 0} :
        Set (EuclideanSpace ℝ (Fin n))) = (ker : Set _) := by
    ext y
    simp [hker_def, LinearMap.mem_ker, EuclideanSpace.proj]
  rw [hsubm]
  refine MeasureTheory.Measure.addHaar_submodule
    (μ := (Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).addHaar) ker ?_
  intro hker_eq
  have h_in_top : EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∈
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := Submodule.mem_top
  rw [← hker_eq] at h_in_top
  have h_proj_zero : (EuclideanSpace.proj (0 : Fin n) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = 0 := by
    have := h_in_top
    simp only [hker_def, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this
    exact this
  have h_eval : (EuclideanSpace.proj (0 : Fin n) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) =
      (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0 := rfl
  rw [single_zero_one_apply_zero n] at h_eval
  exact one_ne_zero (h_proj_zero.symm.trans h_eval).symm

private theorem frontier_range_modelWithCorners_basisAddHaar_zero
    (n : ℕ) [NeZero n] :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ((Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).addHaar :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
      (frontier (Set.range (modelWithCornersEuclideanHalfSpace n))) = 0 := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  have : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  rw [frontier_range_modelWithCornersEuclideanHalfSpace_eq]
  exact hyperplane_basisAddHaar_zero n

instance instHasSmoothBoundary (n : ℕ) [NeZero n] :
    HasSmoothBoundary
      (EuclideanSpace ℝ (Fin n))
      (EuclideanHalfSpace n)
      (modelWithCornersEuclideanHalfSpace n) where
  boundaryE := EuclideanSpace ℝ (Fin (n - 1))
  boundaryENormedGroup := inferInstance
  boundaryENormedSpace := inferInstance
  boundaryEInnerProductSpace := inferInstance
  boundaryEFiniteDimensional := inferInstance
  boundaryH := EuclideanSpace ℝ (Fin (n - 1))
  boundaryHTopologicalSpace := inferInstance
  boundaryI := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))
  boundaryIBoundaryless := inferInstance
  inclH := inclH n
  inclH_continuous := inclH_continuous n
  inclH_injective := inclH_injective n
  inclH_isInducing := inclH_isInducing n
  inclH_isClosed_image := by
    rw [range_modelWithCorners_comp_inclH]
    have heq :
        {y : EuclideanSpace ℝ (Fin n) | y 0 = 0}
          = (fun y : EuclideanSpace ℝ (Fin n) => y 0) ⁻¹' {0} := rfl
    rw [heq]
    refine IsClosed.preimage ?_ isClosed_singleton
    exact PiLp.continuous_apply 2 _ 0
  projE := projEuclidean n
  projE_continuous := projEuclidean_continuous n
  projE_contDiff := projEuclidean_contDiff n
  I_inclH_boundaryI_symm_contDiff := by
    rw [comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm]
    exact inclEuclidean_contDiff n
  range_I_inclH := by
    rw [range_modelWithCorners_comp_inclH,
        frontier_range_modelWithCornersEuclideanHalfSpace_eq]
  proj_inclH_compat := by
    intro x
    change projEuclidean n (inclEuclidean n x) = x
    exact projEuclidean_inclEuclidean n x
  inwardCoordE := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  inwardCoordE_enters := by
    intro y hy
    rw [frontier_range_modelWithCornersEuclideanHalfSpace_eq] at hy
    refine ⟨1, one_pos, ?_⟩
    intro t ht
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    change 0 < (y + t • EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0
    rw [PiLp.add_apply, PiLp.smul_apply, single_zero_one_apply_zero n, hy]
    simpa using ht.1
  inwardCoordE_transverse := single_zero_one_transverse n
  range_frontier_basis_addHaar_zero := by
    intro _
    exact frontier_range_modelWithCorners_basisAddHaar_zero n
  finrank_boundaryE_succ := by
    intro _
    rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    exact Nat.sub_one_add_one_eq_of_pos (Nat.pos_of_neZero n)

example (n : ℕ) [NeZero n] :
    HasSmoothBoundary.boundaryModelE
      (modelWithCornersEuclideanHalfSpace n)
      = EuclideanSpace ℝ (Fin (n - 1)) := rfl

example (n : ℕ) [NeZero n] :
    HasSmoothBoundary.boundaryModelH
      (modelWithCornersEuclideanHalfSpace n)
      = EuclideanSpace ℝ (Fin (n - 1)) := rfl

example (n : ℕ) [NeZero n] :
    HasSmoothBoundary.boundaryModel
      (modelWithCornersEuclideanHalfSpace n)
      = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1))) := rfl

example (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (instHasSmoothBoundary n).projE := projEuclidean_contDiff n


end EuclideanHalfSpaceInstance

open Bundle Manifold

section

variable {n : Nat} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

theorem boundaryInclusionMfderiv_model_euclideanHalfSpace
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) :
    (tangentSpaceModelContinuousLinearEquiv
      (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary n).boundaryI) x).arrowCongr
        (tangentSpaceModelContinuousLinearEquiv (I := modelWithCornersEuclideanHalfSpace n) (x : M))
        (boundaryInclusionMfderiv x) = EuclideanHalfSpaceInstance.inclEuclideanCLM n := by
  rw [boundaryInclusionMfderiv_model_eq_fderiv]
  change fderiv Real (modelWithCornersEuclideanHalfSpace n ∘
      EuclideanHalfSpaceInstance.inclH n ∘ (modelWithCornersSelf Real
        (EuclideanSpace Real (Fin (n - 1)))).symm) _ = _
  rw [EuclideanHalfSpaceInstance.comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm]
  exact (EuclideanHalfSpaceInstance.inclEuclideanCLM n).fderiv

theorem boundaryInclusionMfderiv_euclideanHalfSpace_apply
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M)
    (w : TangentSpace (EuclideanHalfSpaceInstance.instHasSmoothBoundary n).boundaryI x) :
    tangentSpaceModelContinuousLinearEquiv (I := modelWithCornersEuclideanHalfSpace n) (x : M)
        (boundaryInclusionMfderiv x w) = EuclideanHalfSpaceInstance.inclEuclideanCLM n
      (tangentSpaceModelContinuousLinearEquiv
        (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary n).boundaryI) x w) := by
  have h := congrArg (fun L => L (tangentSpaceModelContinuousLinearEquiv
    (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary n).boundaryI) x w))
    (boundaryInclusionMfderiv_model_euclideanHalfSpace x)
  simpa only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_apply_apply] using h

theorem sub_head_smul_inwardCoord_mem_range_boundaryInclusionMfderiv
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n) (x : M)) :
    v - (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersEuclideanHalfSpace n) (x : M) v) 0 • inwardCoord (M := M) x ∈
      LinearMap.range (boundaryInclusionMfderiv (M := M) x).toLinearMap := by
  let e := tangentSpaceModelContinuousLinearEquiv
    (I := modelWithCornersEuclideanHalfSpace n) (x : M)
  let b := tangentSpaceModelContinuousLinearEquiv
    (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary n).boundaryI) x
  have hzero : e (v - (e v) 0 • inwardCoord (M := M) x) 0 = 0 := by
    rw [map_sub, map_smul]
    have hin : e (inwardCoord (M := M) x) = EuclideanSpace.single (0 : Fin n) (1 : Real) :=
      inwardCoord_eq x
    rw [hin]
    simp
  have hmem : e (v - (e v) 0 • inwardCoord (M := M) x) ∈
      Set.range (EuclideanHalfSpaceInstance.inclEuclidean n) := by
    rw [EuclideanHalfSpaceInstance.range_inclEuclidean]
    exact hzero
  rcases hmem with ⟨z, hz⟩
  refine ⟨b.symm z, ?_⟩
  apply e.injective
  change e (boundaryInclusionMfderiv x (b.symm z)) = _
  rw [boundaryInclusionMfderiv_euclideanHalfSpace_apply]
  change EuclideanHalfSpaceInstance.inclEuclideanCLM n (b (b.symm z)) = _
  rw [b.apply_symm_apply]
  exact hz

theorem outwardNormal_inner_euclideanHalfSpace_eq_neg_sqrt_mul_head
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n) (x : M)) :
    g.inner (x : M) (outwardNormal (M := M) g x) v =
      -Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)) *
        (tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersEuclideanHalfSpace n) (x : M) v) 0 :=
  outwardNormal_inner_eq_neg_sqrt_mul_of_sub_mem_range g x v _
    (sub_head_smul_inwardCoord_mem_range_boundaryInclusionMfderiv x v)

end

section

variable {n : Nat} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ∞ M]

private theorem inwardCoord_euclideanHalfSpace
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace (n + 1)) M) :
    inwardCoord (M := M) x = (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersEuclideanHalfSpace (n + 1)) (x : M)).symm
        (EuclideanSpace.single (0 : Fin (n + 1)) (1 : Real)) := by
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := modelWithCornersEuclideanHalfSpace (n + 1)) (x : M)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact inwardCoord_eq x

private theorem boundaryInclusionMfderiv_euclideanHalfSpace_single
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace (n + 1)) M) (i : Fin n) :
    boundaryInclusionMfderiv x
        ((tangentSpaceModelContinuousLinearEquiv
          (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary (n + 1)).boundaryI) x).symm
          (EuclideanSpace.single i 1)) =
      (tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersEuclideanHalfSpace (n + 1)) (x : M)).symm
        (EuclideanSpace.single i.succ 1) := by
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := modelWithCornersEuclideanHalfSpace (n + 1)) (x : M)).injective
  rw [boundaryInclusionMfderiv_euclideanHalfSpace_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    EuclideanHalfSpaceInstance.inclEuclideanCLM_succ_apply]
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · simp [PiLp.single_apply, Pi.single_apply]

theorem det_gram_euclideanHalfSpace_eq_normal_sq_mul_det_induced
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace (n + 1)) M)
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace (n + 1)) M) :
    (Matrix.of fun i j : Fin (n + 1) => g.inner (x : M)
      ((tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersEuclideanHalfSpace (n + 1)) (x : M)).symm (EuclideanSpace.single i 1))
      ((tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersEuclideanHalfSpace (n + 1)) (x : M)).symm (EuclideanSpace.single j 1))).det =
      g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) *
        (Matrix.of fun i j : Fin n => (inducedMetric g).inner x
          ((tangentSpaceModelContinuousLinearEquiv
            (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary (n + 1)).boundaryI) x).symm
            (EuclideanSpace.single i 1))
          ((tangentSpaceModelContinuousLinearEquiv
            (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary (n + 1)).boundaryI) x).symm
            (EuclideanSpace.single j 1))).det := by
  let b := (EuclideanSpace.basisFun (Fin n) Real).toBasis.map
    (tangentSpaceModelContinuousLinearEquiv
      (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary (n + 1)).boundaryI) x).symm.toLinearEquiv
  let c : Fin n → Real := fun i => b.repr (boundaryComponentOfInward (M := M) g x) i
  let v : Fin n → TangentSpace (modelWithCornersEuclideanHalfSpace (n + 1)) (x : M) :=
    fun i => boundaryInclusionMfderiv x (b i)
  have hsum : (∑ i, c i • v i) = inwardTangentialPart (M := M) g x := by
    rw [inwardTangentialPart_def, ← b.sum_repr (boundaryComponentOfInward (M := M) g x), map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (map_smul _ _ _).symm
  have hw : (∑ i, c i • v i) - inwardCoord (M := M) x = outwardDir (M := M) g x := by
    rw [hsum, outwardDir_def]
  have h := (g.inner (x : M)).toBilinForm.det_gram_cons_eq_mul_of_orthogonal
    (inwardCoord (M := M) x) v c (by
      intro i
      rw [hw]
      exact outwardDir_mem_normalSubspace g x (b i))
  rw [hw] at h
  have hframe : Fin.cons (α := fun _ => TangentSpace (modelWithCornersEuclideanHalfSpace (n + 1))
      (x : M)) (inwardCoord (M := M) x) v =
      fun i => (tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersEuclideanHalfSpace (n + 1)) (x : M)).symm (EuclideanSpace.single i 1) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact inwardCoord_euclideanHalfSpace x
    · simpa only [Fin.cons_succ, v, b, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply, ContinuousLinearEquiv.coe_toLinearEquiv] using
        boundaryInclusionMfderiv_euclideanHalfSpace_single x j
  rw [hframe] at h
  have hgram : (Matrix.of fun i j => (g.inner (x : M)).toBilinForm (v i) (v j)) =
      Matrix.of (fun i j : Fin n => (inducedMetric g).inner x
        ((tangentSpaceModelContinuousLinearEquiv
          (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary (n + 1)).boundaryI) x).symm
          (EuclideanSpace.single i 1))
        ((tangentSpaceModelContinuousLinearEquiv
          (I := (EuclideanHalfSpaceInstance.instHasSmoothBoundary (n + 1)).boundaryI) x).symm
          (EuclideanSpace.single j 1))) := by
    ext i j
    simpa only [Matrix.of_apply, ContinuousLinearMap.toBilinForm_apply, v, b,
      Module.Basis.map_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv] using
      (inducedMetric_inner_apply g x (b i) (b j)).symm
  rw [hgram] at h
  exact h

end

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
