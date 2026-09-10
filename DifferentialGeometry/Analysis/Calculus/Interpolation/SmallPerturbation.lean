import DifferentialGeometry.Analysis.Calculus.Inverse.VectorParameterizedInverse
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set
open scoped ContDiff Manifold NNReal

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem bijective_id_add_of_lipschitz {u : E → E} {c : ℝ≥0}
    (hu : LipschitzWith c u) (hc : c < 1) : Function.Bijective (fun x ↦ x + u x) := by
  have hT (y : E) : ContractingWith c (fun x ↦ y - u x) := by
    refine ⟨hc, LipschitzWith.of_dist_le_mul fun x z ↦ ?_⟩
    simpa only [dist_sub_left] using hu.dist_le_mul x z
  constructor
  · intro x z hxz
    apply (hT (x + u x)).fixedPoint_unique'
    · exact sub_eq_iff_eq_add.mpr rfl
    · exact sub_eq_iff_eq_add.mpr hxz
  · intro y
    refine ⟨(hT y).fixedPoint (fun x ↦ y - u x), ?_⟩
    exact (sub_eq_iff_eq_add.mp (hT y).fixedPoint_isFixedPt).symm

variable [NormedSpace ℝ E]

theorem exists_diffeomorphs_of_small_lipschitz_displacement
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {u : P × E → E} (hu : ContDiff ℝ ∞ u)
    (hsmall : ∀ p, ∃ c : ℝ≥0, c < 1 ∧ LipschitzWith c (fun x ↦ u (p, x))) :
    ∃ D : P → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : P × E ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : P × E ↦ (D q.1).symm q.2) ∧
      ∀ p x, D p x = x + u (p, x) := by
  let h : P × E → E := fun q ↦ q.2 + u q
  have hh : ContDiff ℝ ∞ h := contDiff_snd.add hu
  have hbij (p : P) : Function.Bijective (fun x ↦ h (p, x)) := by
    obtain ⟨c, hc, hlip⟩ := hsmall p
    exact bijective_id_add_of_lipschitz hlip hc
  have hvertical (p : P) (x : E) : ∃ A : E ≃L[ℝ] E,
      ∀ w, fderiv ℝ h (p, x) (0, w) = A w := by
    obtain ⟨c, hc, hlip⟩ := hsmall p
    let B := fderiv ℝ (fun z ↦ u (p, z)) x
    have hBnorm : ‖B‖₊ ≤ c := norm_fderiv_le_of_lipschitz ℝ hlip
    have hBbij : Function.Bijective (fun z ↦ z + B z) :=
      bijective_id_add_of_lipschitz (B.lipschitz.weaken hBnorm) hc
    let L := ContinuousLinearMap.id ℝ E + B
    let A : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot.mpr hBbij.1) (LinearMap.range_eq_top.mpr hBbij.2)
    refine ⟨A, ?_⟩
    intro w
    have hdu := (hu.differentiable (by simp) (p, x)).hasFDerivAt
    have hd := hasFDerivAt_snd.add hdu
    have hcderiv := (hdu.comp x ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))).fderiv
    have hBw : B w = fderiv ℝ u (p, x) (0, w) :=
      congrArg (fun T : E →L[ℝ] E ↦ T w) hcderiv
    change fderiv ℝ (Prod.snd + u) (p, x) (0, w) = A w
    rw [hd.fderiv]
    change w + fderiv ℝ u (p, x) (0, w) = w + B w
    rw [hBw]
  obtain ⟨R, hR, hleft, hright⟩ := exists_contDiffOn_vector_inverse_of_bijective
    isOpen_univ (show ContDiffOn ℝ ∞ h (univ ×ˢ univ) from hh.contDiffOn)
    (fun p _ ↦ hbij p) (fun p _ x ↦ hvertical p x)
  have hR' : ContDiff ℝ ∞ R := contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hR)
  let D (p : P) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    { toEquiv :=
        { toFun := fun x ↦ h (p, x)
          invFun := fun y ↦ R (p, y)
          left_inv := hleft p (mem_univ p)
          right_inv := hright p (mem_univ p) }
      contMDiff_toFun := (hh.comp (contDiff_const.prodMk contDiff_id)).contMDiff
      contMDiff_invFun := (hR'.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  exact ⟨D, hh, hR', fun _ _ ↦ rfl⟩

end Poincare.Analysis
