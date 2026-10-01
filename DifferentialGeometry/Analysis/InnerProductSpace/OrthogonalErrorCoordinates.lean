import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis

private theorem norm_iteratedFDeriv_comp_linear_at_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E →L[ℝ] F) (f : F → G) (x : E) (j : ℕ)
    (hf : ContDiffAt ℝ j f (T x)) :
    ‖iteratedFDeriv ℝ j (f ∘ T) x‖ ≤ ‖iteratedFDeriv ℝ j f (T x)‖ * ‖T‖ ^ j := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  have hx : T x ∈ interior s := mem_interior_iff_mem_nhds.mpr hs
  have hopen : IsOpen (T ⁻¹' interior s) := isOpen_interior.preimage T.continuous
  have heq := T.iteratedFDerivWithin_comp_right (hfs.mono interior_subset)
    isOpen_interior.uniqueDiffOn hopen.uniqueDiffOn hx (i := j) le_rfl
  rw [iteratedFDerivWithin_of_isOpen j hopen hx,
    iteratedFDerivWithin_of_isOpen j isOpen_interior hx] at heq
  rw [heq]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ j f (T x)).norm_compContinuousLinearMap_le (fun _ : Fin j => T)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def orthogonalCoordinateSum (L : Submodule ℝ H) : L × Lᗮ →L[ℝ] H :=
  L.subtypeL.coprod Lᗮ.subtypeL

theorem norm_orthogonalCoordinateSum_le (L : Submodule ℝ H) :
    ‖orthogonalCoordinateSum L‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  change ‖(p.1 : H) + (p.2 : H)‖ ≤ 2 * ‖p‖
  have h1 : ‖p.1‖ ≤ ‖p‖ := le_max_left _ _
  have h2 : ‖p.2‖ ≤ ‖p‖ := le_max_right _ _
  have ht := norm_add_le (p.1 : H) (p.2 : H)
  change ‖(p.1 : H) + (p.2 : H)‖ ≤ ‖p.1‖ + ‖p.2‖ at ht
  linarith

def orthogonalSectionError (L : Submodule ℝ H) [CompleteSpace Lᗮ]
    (η : H → H) (o : H) (p : L × Lᗮ) : Lᗮ :=
  Lᗮ.orthogonalProjectionOnto (η (o + orthogonalCoordinateSum L p)) - p.2

theorem orthogonalSectionError_eq_projected_error
    (L : Submodule ℝ H) [CompleteSpace Lᗮ] (η : H → H) (o : H) (p : L × Lᗮ) :
    orthogonalSectionError L η o p = Lᗮ.orthogonalProjectionOnto
      (η (o + orthogonalCoordinateSum L p) -
        Lᗮ.starProjection ((o + orthogonalCoordinateSum L p) - o)) := by
  rw [map_sub, Submodule.orthogonalProjectionOnto_starProjection_of_le le_rfl]
  have hc : (o + orthogonalCoordinateSum L p) - o = (p.1 : H) + (p.2 : H) := by
    change (o + ((p.1 : H) + (p.2 : H))) - o = _
    abel
  rw [hc, map_add, L.orthogonalProjectionOnto_orthogonal_apply_eq_zero p.1.property,
    Lᗮ.orthogonalProjectionOnto_mem_subspace_eq_self, zero_add]
  rfl

theorem norm_iteratedFDeriv_orthogonalSectionError_le
    (L : Submodule ℝ H) [CompleteSpace Lᗮ] (η : H → H) (o : H)
    (p : L × Lᗮ) (j : ℕ)
    (hη : ContDiffAt ℝ j η (o + orthogonalCoordinateSum L p)) :
    ‖iteratedFDeriv ℝ j (orthogonalSectionError L η o) p‖ ≤
      2 ^ j * ‖iteratedFDeriv ℝ j
        (fun y => η y - Lᗮ.starProjection (y - o)) (o + orthogonalCoordinateSum L p)‖ := by
  let F : H → H := fun y => η y - Lᗮ.starProjection (y - o)
  let f : H → H := fun y => F (o + y)
  let T := orthogonalCoordinateSum L
  let P := Lᗮ.orthogonalProjectionOnto
  have hF : ContDiffAt ℝ j F (o + T p) :=
    hη.sub (Lᗮ.starProjection.contDiff.contDiffAt.comp _ (contDiffAt_id.sub contDiffAt_const))
  have hf : ContDiffAt ℝ j f (T p) :=
    hF.comp (T p) (contDiffAt_const.add contDiffAt_id)
  have hcomp : ContDiffAt ℝ j (f ∘ T) p := hf.comp p T.contDiff.contDiffAt
  have hEq : orthogonalSectionError L η o = P ∘ (f ∘ T) := by
    funext q
    exact orthogonalSectionError_eq_projected_error L η o q
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simpa only [one_mul] using Lᗮ.norm_orthogonalProjectionOnto_apply_le y
  rw [hEq]
  calc
    _ ≤ ‖P‖ * ‖iteratedFDeriv ℝ j (f ∘ T) p‖ :=
      P.norm_iteratedFDeriv_comp_left hcomp le_rfl
    _ ≤ ‖iteratedFDeriv ℝ j (f ∘ T) p‖ :=
      (mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ ‖iteratedFDeriv ℝ j f (T p)‖ * ‖T‖ ^ j :=
      norm_iteratedFDeriv_comp_linear_at_le T f p j hf
    _ ≤ ‖iteratedFDeriv ℝ j f (T p)‖ * 2 ^ j := by
      gcongr
      exact norm_orthogonalCoordinateSum_le L
    _ = _ := by
      change ‖iteratedFDeriv ℝ j (fun y => F (o + y)) (T p)‖ * 2 ^ j = _
      rw [iteratedFDeriv_comp_add_left]
      exact mul_comm _ _

theorem norm_fderiv_normal_orthogonalSectionError_le
    (L : Submodule ℝ H) [CompleteSpace Lᗮ] (η : H → H) (o : H)
    (t : L) (n : Lᗮ)
    (hη : DifferentiableAt ℝ η (o + orthogonalCoordinateSum L (t, n))) :
    ‖fderiv ℝ (fun z => orthogonalSectionError L η o (t, z)) n‖ ≤
      ‖fderiv ℝ (fun y => η y - Lᗮ.starProjection (y - o))
        (o + orthogonalCoordinateSum L (t, n))‖ := by
  let F : H → H := fun y => η y - Lᗮ.starProjection (y - o)
  let y := o + orthogonalCoordinateSum L (t, n)
  have hF : DifferentiableAt ℝ F y :=
    hη.sub (Lᗮ.starProjection.differentiableAt.comp _
      (differentiableAt_id.sub (differentiableAt_const o)))
  have hc : HasFDerivAt (fun z : Lᗮ => o + ((t : H) + (z : H))) Lᗮ.subtypeL n := by
    exact (Lᗮ.subtypeL.hasFDerivAt.const_add (t : H)).const_add o
  have hd := Lᗮ.orthogonalProjectionOnto.hasFDerivAt.comp n (hF.hasFDerivAt.comp n hc)
  have heq : (fun z => orthogonalSectionError L η o (t,z)) =
      fun z : Lᗮ => Lᗮ.orthogonalProjectionOnto (F (o + ((t : H) + (z : H)))) := by
    funext z
    exact orthogonalSectionError_eq_projected_error L η o (t,z)
  have hd' : HasFDerivAt
      (fun z : Lᗮ => Lᗮ.orthogonalProjectionOnto (F (o + ((t : H) + (z : H)))))
      (Lᗮ.orthogonalProjectionOnto.comp ((fderiv ℝ F y).comp Lᗮ.subtypeL)) n := by
    simpa only [Function.comp_def] using hd
  rw [heq, hd'.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  change ‖Lᗮ.orthogonalProjectionOnto ((fderiv ℝ F y) (z : H))‖ ≤
    ‖fderiv ℝ F y‖ * ‖z‖
  exact (Lᗮ.norm_orthogonalProjectionOnto_apply_le _).trans ((fderiv ℝ F y).le_opNorm (z : H))

end DifferentialGeometry.Analysis
