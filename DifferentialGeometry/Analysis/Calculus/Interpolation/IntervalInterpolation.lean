import DifferentialGeometry.Analysis.Calculus.Inverse.InjectiveParameterizedInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

def intervalInterpolation {P : Type*} (f : P × ℝ → ℝ) (β : P → ℝ) (q : P × ℝ) : ℝ :=
  (1 - β q.1) * q.2 + β q.1 * f q

theorem exists_diffeomorph_intervalInterpolation
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {S : Set P} (hS : IsOpen S) {f : P × ℝ → ℝ} {β : P → ℝ} {a b : ℝ}
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ univ)) (hβ : ContDiffOn ℝ ∞ β S)
    (hβrange : ∀ p ∈ S, β p ∈ Icc (0 : ℝ) 1)
    (hfpos : ∀ p ∈ S, ∀ y, 0 < deriv (fun y ↦ f (p, y)) y)
    (hfixed : ∀ p ∈ S, ∀ y, y ≤ a ∨ b ≤ y → f (p, y) = y) :
    ∃ D : P → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞,
      ContDiffOn ℝ ∞ (fun q : P × ℝ ↦ D q.1 q.2) (S ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun q : P × ℝ ↦ (D q.1).symm q.2) (S ×ˢ univ) ∧
      ∀ p ∈ S,
        (∀ y, D p y = intervalInterpolation f β (p, y)) ∧
        (∀ y, 0 < deriv (D p) y) ∧ BijOn (D p) (Icc a b) (Icc a b) ∧
        ∀ y, y ≤ a ∨ b ≤ y → D p y = y := by
  classical
  let H := intervalInterpolation f β
  have hB : ContDiffOn ℝ ∞ (fun q : P × ℝ ↦ β q.1) (S ×ˢ univ) :=
    hβ.comp contDiffOn_fst (fun _ hq ↦ hq.1)
  have hH : ContDiffOn ℝ ∞ H (S ×ˢ univ) :=
    ((contDiffOn_const.sub hB).mul contDiffOn_snd).add (hB.mul hf)
  have hfs (p : P) (hp : p ∈ S) : ContDiff ℝ ∞ (fun y ↦ f (p, y)) :=
    contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hp, mem_univ _⟩))
  have hhs (p : P) (hp : p ∈ S) : ContDiff ℝ ∞ (fun y ↦ H (p, y)) :=
    contDiffOn_univ.mp (hH.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hp, mem_univ _⟩))
  have hd (p : P) (hp : p ∈ S) (y : ℝ) :
      HasDerivAt (fun y ↦ H (p, y)) (1 - β p + β p * deriv (fun y ↦ f (p, y)) y) y := by
    convert
      ((hasDerivAt_id y).const_mul (1 - β p)).add
        (((hfs p hp).differentiable (by simp) y).hasDerivAt.const_mul (β p)) using 1 <;>
      first | rfl | simp only [mul_one]
  have hpos (p : P) (hp : p ∈ S) (y : ℝ) : 0 < deriv (fun y ↦ H (p, y)) y := by
    rw [(hd p hp y).deriv]
    have hb := hβrange p hp
    have hf' := hfpos p hp y
    rcases eq_or_lt_of_le hb.2 with he | he
    · rw [he]
      simpa using hf'
    · have hmul := mul_nonneg hb.1 hf'.le
      linarith
  have hfix (p : P) (hp : p ∈ S) (y : ℝ) (hy : y ≤ a ∨ b ≤ y) : H (p, y) = y := by
    dsimp only [H, intervalInterpolation]
    rw [hfixed p hp y hy]
    ring
  have hbij (p : P) (hp : p ∈ S) : Function.Bijective (fun y ↦ H (p, y)) := by
    refine ⟨(strictMono_of_deriv_pos (hpos p hp)).injective, ?_⟩
    apply (hhs p hp).continuous.surjective
    · apply tendsto_id.congr'
      filter_upwards [eventually_ge_atTop b] with y hy
      exact (hfix p hp y (Or.inr hy)).symm
    · apply tendsto_id.congr'
      filter_upwards [eventually_le_atBot a] with y hy
      exact (hfix p hp y (Or.inl hy)).symm
  have hvert (p : P) (hp : p ∈ S) (y : ℝ) : fderiv ℝ H (p, y) (0, 1) ≠ 0 := by
    have hdf : HasDerivAt (fun y ↦ H (p, y)) (fderiv ℝ H (p, y) (0, 1)) y :=
      ((hH.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt y
          ((hasDerivAt_const y p).prodMk (hasDerivAt_id y))
    rw [← hdf.deriv]
    exact (hpos p hp y).ne'
  obtain ⟨R, hR, hleft, hright⟩ := exists_contDiffOn_inverse_of_bijective hS hH hbij hvert
  have hrs (p : P) (hp : p ∈ S) : ContDiff ℝ ∞ (fun y ↦ R (p, y)) :=
    contDiffOn_univ.mp (hR.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hp, mem_univ _⟩))
  let D (p : P) : Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞ := if hp : p ∈ S then
    { toEquiv :=
        { toFun := fun y ↦ H (p, y)
          invFun := fun y ↦ R (p, y)
          left_inv := hleft p hp
          right_inv := hright p hp }
      contMDiff_toFun := (hhs p hp).contMDiff
      contMDiff_invFun := (hrs p hp).contMDiff }
    else Diffeomorph.refl 𝓘(ℝ) ℝ ∞
  have hD (p : P) (hp : p ∈ S) (y : ℝ) : D p y = H (p, y) := by
    simp only [D, dif_pos hp]; rfl
  have hDi (p : P) (hp : p ∈ S) (y : ℝ) : (D p).symm y = R (p, y) := by
    simp only [D, dif_pos hp]; rfl
  refine ⟨D, hH.congr (fun q hq ↦ hD q.1 hq.1 q.2),
    hR.congr (fun q hq ↦ hDi q.1 hq.1 q.2), fun p hp ↦ ?_⟩
  have he : (D p : ℝ → ℝ) = fun y ↦ H (p, y) := funext (hD p hp)
  have hmono := strictMono_of_deriv_pos (hpos p hp)
  have himage : (fun y ↦ H (p, y)) '' Icc a b = Icc a b := by
    rcases le_total a b with hab | hba
    · rw [(hhs p hp).continuous.continuousOn.image_Icc_of_monotoneOn hab (hmono.monotone.monotoneOn _),
        hfix p hp a (Or.inl le_rfl), hfix p hp b (Or.inr le_rfl)]
    · by_cases hab : a = b
      · subst b
        simp only [Icc_self, image_singleton, hfix p hp a (Or.inl le_rfl)]
      · simp only [Icc_eq_empty_of_lt (lt_of_le_of_ne hba (Ne.symm hab)), image_empty]
  refine ⟨hD p hp, fun y ↦ by rw [he]; exact hpos p hp y, ?_,
    fun y hy ↦ (hD p hp y).trans (hfix p hp y hy)⟩
  rw [he]
  refine ⟨fun y hy ↦ himage ▸ mem_image_of_mem _ hy, hmono.injective.injOn, ?_⟩
  intro y hy
  have hm : y ∈ (fun y ↦ H (p, y)) '' Icc a b := by rwa [himage]
  exact hm

end DifferentialGeometry.Analysis
