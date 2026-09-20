import DifferentialGeometry.Analysis.Elliptic.Coefficients
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Defs
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.Analysis
open Laplacian.MetricExtension
open Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem exists_smoothEllipticBilinearForm_extension
    {Ω K : Set V} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (A : V → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω)
    (hpos : ∀ x ∈ Ω, (A x).PosDef) :
    ∃ B : SmoothEllipticBilinearForm d (univ : Set V),
      (∀ x ∈ K, B.a x = A x) ∧ (∀ x, (B.a x).PosDef) ∧ B.c = 0 := by
  classical
  obtain ⟨χ, hχ, hχc, hχone, hχs, hχ01⟩ := exists_bump_compact hK hΩ hKΩ
  let F (x : V) := χ x • A x + (1 - χ x) • (1 : Matrix (Fin d) (Fin d) ℝ)
  have hF (i j : Fin d) : ContDiff ℝ ∞ (fun x => F x i j) := by
    have hh := contDiff_cutoff_smul hΩ hχ hχs (hA i j)
    have ht : ContDiff ℝ ∞ (fun x => (1 - χ x) * (1 : Matrix (Fin d) (Fin d) ℝ) i j) :=
      (contDiff_const.sub hχ).mul contDiff_const
    simpa only [F, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using hh.add ht
  have hposF (x : V) : (F x).PosDef := by
    have h0 : 0 ≤ χ x := (hχ01 (mem_range_self x)).1
    have h1 : 0 ≤ 1 - χ x := sub_nonneg.mpr (hχ01 (mem_range_self x)).2
    by_cases hx : x ∈ tsupport χ
    · rcases eq_or_lt_of_le h0 with heq | hlt
      · simp only [F, ← heq, zero_smul, sub_zero, one_smul, zero_add]
        exact Matrix.PosDef.one
      · exact ((hpos x (hχs hx)).smul hlt).add_posSemidef (Matrix.PosSemidef.one.smul h1)
    · simp only [F, image_eq_zero_of_notMem_tsupport hx, zero_smul, sub_zero, one_smul, zero_add]
      exact Matrix.PosDef.one
  obtain ⟨c, hc, hcoer⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound
    hχc F (fun i j => (hF i j).continuous.continuousOn) (fun x _ => hposF x)
  let lam := min c 1
  have hlam : 0 < lam := lt_min hc zero_lt_one
  have hcoerF (x : V) (v : V) : lam * ‖v‖ ^ 2 ≤ inner ℝ v (DeGiorgi.matMulE (F x) v) := by
    by_cases hx : x ∈ tsupport χ
    · have hh := hcoer x hx v
      change c * ‖v‖ ^ 2 ≤ _ at hh
      have ht := (mul_le_mul_of_nonneg_right (min_le_left c 1) (sq_nonneg ‖v‖)).trans hh
      simpa only [PiLp.inner_apply, DeGiorgi.matMulE, Matrix.mulVec, dotProduct,
        Pi.star_apply, star_trivial, RCLike.inner_apply, conj_trivial, mul_comm] using ht
    · have hFx : F x = 1 := by
        simp only [F, image_eq_zero_of_notMem_tsupport hx, zero_smul, sub_zero, one_smul, zero_add]
      rw [hFx]
      have he : DeGiorgi.matMulE (1 : Matrix (Fin d) (Fin d) ℝ) v = v := by
        ext i
        simp only [DeGiorgi.matMulE_apply, Matrix.one_mulVec]
      rw [he, real_inner_self_eq_norm_sq]
      exact mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _)
  let B : SmoothEllipticBilinearForm d (univ : Set V) :=
    { a := F
      c := 0
      symm := fun x i j => by
        have he := congrFun (congrFun (hposF x).isHermitian.eq j) i
        simpa only [Matrix.conjTranspose_apply, star_trivial] using he
      smooth_a := hF
      smooth_c := contDiff_const
      lam := lam
      capLam := lam
      ellipticity_pos := hlam
      ellipticity_le_upper := le_rfl
      coercive := fun x _ v => hcoerF x v }
  refine ⟨B, ?_, hposF, rfl⟩
  intro x hx
  have he := hχone.self_of_nhdsSet hx
  change χ x • A x + (1 - χ x) • (1 : Matrix (Fin d) (Fin d) ℝ) = A x
  simp only [he, Pi.one_apply, one_smul, sub_self, zero_smul, add_zero]

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem SmoothEllipticBilinearForm.posDef
    {Ω : Set V} (B : SmoothEllipticBilinearForm d Ω) {x : V} (hx : x ∈ Ω) :
    (B.a x).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    exact B.symm x j i
  · intro v hv
    have hvn : (0 : ℝ) < ‖WithLp.toLp 2 v‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (by
        intro hh
        apply hv
        ext i
        exact congrArg (fun w : V => w i) hh))
    have hh := (mul_pos B.ellipticity_pos hvn).trans_le (B.coercive x hx (WithLp.toLp 2 v))
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, DeGiorgi.matMulE_apply,
      Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, mul_comm] using hh

end DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

end

end
