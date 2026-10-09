import DifferentialGeometry.Geometry.Curvature.Surface.DivergenceForm
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.SectionalPlane
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Periodic Gauss–Bonnet: a doubly periodic coefficient field with `K ≥ 0` is flat

SF5 kernel. For a `C²` positive symmetric coefficient field `b` on a two-dimensional space which
is periodic along a basis `(v₁, v₂)`, the chart curvature `K = coefficientSectional b y v₁ v₂` has
`K √(EG − F²) = ∂₂ P − ∂₁ Q` with doubly periodic `C¹` potentials (`DivergenceForm.lean`). Hence the
integral of `K √(EG − F²)` over a period parallelogram vanishes (fundamental theorem of calculus in
each variable and Fubini), so `K ≥ 0` forces `K ≡ 0` (zero integral of a continuous nonnegative
function on an open square, then closure and periodic reduction). No triangulation, Euler
characteristic or Gauss–Bonnet theorem is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

section Square

/-- **Periodic Stokes on the unit square.** If `A = ∂ₜ p` and `B = ∂ₛ q` are continuous,
`p (s, 1) = p (s, 0)`, `q (1, t) = q (0, t)` and `A − B ≥ 0`, then `A − B` vanishes on
`[0, 1]²`. -/
theorem sub_eq_zero_on_square_of_periodic_divergence {p q A B : ℝ × ℝ → ℝ}
    (hA : Continuous A) (hB : Continuous B)
    (hp : ∀ s t, HasDerivAt (fun t => p (s, t)) (A (s, t)) t)
    (hq : ∀ s t, HasDerivAt (fun s => q (s, t)) (B (s, t)) s)
    (hp1 : ∀ s, p (s, 1) = p (s, 0)) (hq1 : ∀ t, q (1, t) = q (0, t))
    (hnn : ∀ z, 0 ≤ A z - B z) :
    ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, A z - B z = 0 := by
  set ι : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hι
  have hint : ∀ F : ℝ × ℝ → ℝ, Continuous F → Integrable F (ι.prod ι) := by
    intro F hF
    rw [hι, Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hAs : ∀ s, Continuous fun t => A (s, t) := fun s =>
    hA.comp (continuous_const.prodMk continuous_id)
  have hBs : ∀ s, Continuous fun t => B (s, t) := fun s =>
    hB.comp (continuous_const.prodMk continuous_id)
  have hBt : ∀ t, Continuous fun s => B (s, t) := fun t =>
    hB.comp (continuous_id.prodMk continuous_const)
  have hcA : ∀ s, ∫ t, A (s, t) ∂ι = 0 := by
    intro s
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hp s t)
      ((hAs s).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le zero_le_one, hp1 s, sub_self] at h
    exact h
  have hcB : ∀ t, ∫ s, B (s, t) ∂ι = 0 := by
    intro t
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hq s t)
      ((hBt t).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le zero_le_one, hq1 t, sub_self] at h
    exact h
  have hsplit : ∀ s, ∫ t, (A (s, t) - B (s, t)) ∂ι = -∫ t, B (s, t) ∂ι := by
    intro s
    rw [integral_sub ((hAs s).integrableOn_Ioc) ((hBs s).integrableOn_Ioc), hcA s, zero_sub]
  have htot : ∫ z, (A z - B z) ∂(ι.prod ι) = 0 := by
    rw [integral_prod _ (hint (fun z => A z - B z) (hA.sub hB))]
    simp only [hsplit]
    rw [integral_neg, integral_integral_swap (f := fun s t => B (s, t)) (hint B hB)]
    simp only [hcB, integral_zero, neg_zero]
  have hae : (fun z => A z - B z) =ᵐ[ι.prod ι] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn (hint (fun z => A z - B z) (hA.sub hB))).mp htot
  rw [hι, Measure.prod_restrict, ← Measure.volume_eq_prod] at hae
  have hae' : (fun z => A z - B z) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)] 0 :=
    ae_restrict_of_ae_restrict_of_subset (prod_mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self) hae
  have heq : EqOn (fun z => A z - B z) 0 (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq hae' (isOpen_Ioo.prod isOpen_Ioo) (hA.sub hB).continuousOn
      continuousOn_const
  have hcl := heq.closure (hA.sub hB) continuous_const
  rw [closure_prod_eq, closure_Ioo zero_ne_one] at hcl
  intro z hz
  exact hcl hz

/-- A function on `ℝ²`, `1`-periodic in each variable and zero on `[0, 1]²`, is zero. -/
theorem eq_zero_of_periodic_of_eq_zero_on_square {φ : ℝ × ℝ → ℝ}
    (h1 : ∀ s t, φ (s + 1, t) = φ (s, t)) (h2 : ∀ s t, φ (s, t + 1) = φ (s, t))
    (h0 : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, φ z = 0) (z : ℝ × ℝ) : φ z = 0 := by
  obtain ⟨s, t⟩ := z
  have hs : φ (s, t) = φ (Int.fract s, t) := by
    have hper : Function.Periodic (fun s => φ (s, t)) 1 := fun s => h1 s t
    have h := (hper.int_mul ⌊s⌋) (Int.fract s)
    simp only [mul_one, Int.fract_add_floor] at h
    exact h
  have ht : φ (Int.fract s, t) = φ (Int.fract s, Int.fract t) := by
    have hper : Function.Periodic (fun t => φ (Int.fract s, t)) 1 := fun t => h2 _ t
    have h := (hper.int_mul ⌊t⌋) (Int.fract t)
    simp only [mul_one, Int.fract_add_floor] at h
    exact h
  rw [hs, ht]
  exact h0 _ ⟨⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩,
    ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩⟩

end Square

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem fderiv_add_period' (f : E → ℝ) {w : E} (hf : ∀ y, f (y + w) = f y) (y : E) :
    fderiv ℝ f (y + w) = fderiv ℝ f y := by
  have h : (fun z => f (z + w)) = f := funext hf
  rw [← fderiv_comp_add_right, h]

private theorem hasDerivAt_affine_line (y w : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => y + t • w) w t := by
  simpa using ((hasDerivAt_id t).smul_const w).const_add y

private theorem gram_eq_zero_of_not_linearIndependent {B : E →L[ℝ] E →L[ℝ] ℝ}
    {u v : E} (h : ¬LinearIndependent ℝ ![u, v]) : B u u * B v v - (B u v) ^ 2 = 0 := by
  by_cases hu : u = 0
  · subst hu
    simp
  · obtain ⟨a, ha⟩ : ∃ a : ℝ, a • u = v := by
      simpa only [LinearIndependent.pair_iff' hu, not_forall, not_not] using h
    subst ha
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    ring

variable [FiniteDimensional ℝ E]

/-- **SF5 kernel (periodic Gauss–Bonnet).** A `C²` positive symmetric coefficient field on a
two-dimensional space, periodic along a basis `(v₁, v₂)`, whose chart curvature on the pair
`(v₁, v₂)` is nonnegative, has vanishing chart curvature on every pair. -/
theorem coefficientSectional_eq_zero_of_periodic_of_nonneg (hE : Module.finrank ℝ E = 2)
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂])
    (hper₁ : ∀ y, b (y + v₁) = b y) (hper₂ : ∀ y, b (y + v₂) = b y)
    (hK : ∀ y, 0 ≤ coefficientSectional b y v₁ v₂) :
    ∀ y u v, coefficientSectional b y u v = 0 := by
  have hPc := contDiff_surfaceConnectionP hb hsymm hpos hli
  have hQc := contDiff_surfaceConnectionQ hb hsymm hpos hli
  set P := surfaceConnectionP b v₁ v₂ with hPdef
  set Q := surfaceConnectionQ b v₁ v₂ with hQdef
  let L : ℝ × ℝ → E := fun z => z.1 • v₁ + z.2 • v₂
  have hL : Continuous L := (continuous_fst.smul continuous_const).add
    (continuous_snd.smul continuous_const)
  let A : ℝ × ℝ → ℝ := fun z => fderiv ℝ P (L z) v₂
  let B : ℝ × ℝ → ℝ := fun z => fderiv ℝ Q (L z) v₁
  have hA : Continuous A := ((hPc.continuous_fderiv (by norm_num)).comp hL).clm_apply continuous_const
  have hB : Continuous B := ((hQc.continuous_fderiv (by norm_num)).comp hL).clm_apply continuous_const
  have hp : ∀ s t, HasDerivAt (fun t => P (L (s, t))) (A (s, t)) t := by
    intro s t
    have hd : HasFDerivAt P (fderiv ℝ P (s • v₁ + t • v₂)) (s • v₁ + t • v₂) :=
      (hPc.differentiable (by norm_num) _).hasFDerivAt
    exact hd.comp_hasDerivAt t (hasDerivAt_affine_line (s • v₁) v₂ t)
  have hq : ∀ s t, HasDerivAt (fun s => Q (L (s, t))) (B (s, t)) s := by
    intro s t
    have hd : HasFDerivAt Q (fderiv ℝ Q (s • v₁ + t • v₂)) (t • v₂ + s • v₁) := by
      rw [add_comm (t • v₂)]
      exact (hQc.differentiable (by norm_num) _).hasFDerivAt
    have h := hd.comp_hasDerivAt s (hasDerivAt_affine_line (t • v₂) v₁ s)
    convert h using 1
    funext s
    simp only [Function.comp, L]
    rw [add_comm]
  have hp1 : ∀ s, P (L (s, 1)) = P (L (s, 0)) := by
    intro s
    simp only [L, one_smul, zero_smul, add_zero]
    exact surfaceConnectionP_add_period hper₂ v₁ v₂ (s • v₁)
  have hq1 : ∀ t, Q (L (1, t)) = Q (L (0, t)) := by
    intro t
    simp only [L, one_smul, zero_smul, zero_add]
    rw [add_comm]
    exact surfaceConnectionQ_add_period hper₁ v₁ v₂ (t • v₂)
  have hid : ∀ y, coefficientSectional b y v₁ v₂ * Real.sqrt (surfaceGramDet b v₁ v₂ y) =
      fderiv ℝ P y v₂ - fderiv ℝ Q y v₁ :=
    coefficientSectional_mul_sqrt_eq_fderiv_sub hE hb hsymm hpos hli
  have hnn : ∀ z, 0 ≤ A z - B z := fun z => by
    rw [← hid]
    exact mul_nonneg (hK _) (Real.sqrt_nonneg _)
  have hsq := sub_eq_zero_on_square_of_periodic_divergence (p := fun z => P (L z))
    (q := fun z => Q (L z)) hA hB hp hq hp1 hq1 hnn
  have hPp₁ := fderiv_add_period' P (surfaceConnectionP_add_period hper₁ v₁ v₂)
  have hPp₂ := fderiv_add_period' P (surfaceConnectionP_add_period hper₂ v₁ v₂)
  have hQp₁ := fderiv_add_period' Q (surfaceConnectionQ_add_period hper₁ v₁ v₂)
  have hQp₂ := fderiv_add_period' Q (surfaceConnectionQ_add_period hper₂ v₁ v₂)
  have hL1 : ∀ s t, L (s + 1, t) = L (s, t) + v₁ := fun s t => by
    simp only [L, add_smul, one_smul]
    abel
  have hL2 : ∀ s t, L (s, t + 1) = L (s, t) + v₂ := fun s t => by
    simp only [L, add_smul, one_smul]
    abel
  have hzero : ∀ z, A z - B z = 0 := eq_zero_of_periodic_of_eq_zero_on_square
    (φ := fun z => A z - B z)
    (fun s t => by simp only [A, B, hL1, hPp₁, hQp₁])
    (fun s t => by simp only [A, B, hL2, hPp₂, hQp₂]) hsq
  have h0 : ∀ y, coefficientSectional b y v₁ v₂ = 0 := by
    intro y
    obtain ⟨s, t, rfl⟩ := exists_smul_add_smul_eq_of_finrank_eq_two hE hli y
    have hW := Real.sqrt_pos.mpr (surfaceGramDet_pos hsymm hpos hli (s • v₁ + t • v₂))
    have h := hid (s • v₁ + t • v₂)
    have hz := hzero (s, t)
    simp only [A, B, L] at hz
    rw [hz] at h
    exact (mul_eq_zero.mp h).resolve_right hW.ne'
  intro y u v
  by_cases huv : LinearIndependent ℝ ![u, v]
  · have htop : ∀ {x₁ x₂ : E}, LinearIndependent ℝ ![x₁, x₂] →
        Submodule.span ℝ ({x₁, x₂} : Set E) = ⊤ := fun h => by
      rw [← Matrix.range_cons_cons_empty]
      exact h.span_eq_top_of_card_eq_finrank' (by simp [hE])
    rw [coefficientSectional_eq_of_span_eq hb.contDiffAt (Eventually.of_forall hsymm)
      ((b y).isCoercive_of_posDef (hpos y)) huv ((htop huv).trans (htop hli).symm)]
    exact h0 y
  · rw [coefficientSectional_def, gram_eq_zero_of_not_linearIndependent huv, div_zero]

end Kernel

end DifferentialGeometry.Analysis
