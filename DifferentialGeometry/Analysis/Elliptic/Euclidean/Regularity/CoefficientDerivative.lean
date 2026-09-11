import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.ProductDifferenceBounds
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.FiniteSum
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.WeakDivergence

noncomputable section

open MeasureTheory Set Filter
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped ENNReal

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

def coefficientDerivativeField (p : ℝ≥0∞) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (u : E → ℝ) (Omega : Set E) (l : Fin d) : E → E :=
  fun x => WithLp.toLp 2 fun i => ∑ j : Fin d,
    (fderiv ℝ (fun y => a y i j) x) (EuclideanSpace.single l 1) *
      chosenWeakPartialOrZero p j u Omega x

def coefficientDerivativeSource (p : ℝ≥0∞) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (u : E → ℝ) (Omega : Set E) (l : Fin d) : E → ℝ :=
  fun x => ∑ i : Fin d, ∑ j : Fin d, (
    (fderiv ℝ (fun y => (fderiv ℝ (fun z => a z i j) y)
      (EuclideanSpace.single l 1)) x) (EuclideanSpace.single i 1) *
        chosenWeakPartialOrZero p j u Omega x +
      (fderiv ℝ (fun y => a y i j) x) (EuclideanSpace.single l 1) *
        chosenWeakPartialOrZero p i (chosenWeakPartialOrZero p j u Omega) Omega x)

theorem locallyIntegrable_coefficientDerivativeField_apply
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E}
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x => a x i j))
    {u : E → ℝ} (hu : MemW1p p u Omega) (l i : Fin d) :
    LocallyIntegrable (fun x => coefficientDerivativeField p a u Omega l x i)
      (volume.restrict Omega) :=
  locallyIntegrable_finsetSum Finset.univ (fun j _ =>
    ((chosenWeakPartialOrZero_memLp_of_mem hu j).locallyIntegrable hp).continuous_mul
      (((ha i j).continuous_fderiv one_ne_zero).clm_apply continuous_const))

theorem locallyIntegrable_coefficientDerivativeSource
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E}
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ 2 (fun x => a x i j))
    {u : E → ℝ} (hu : MemWkp 2 p u Omega) (l : Fin d) :
    LocallyIntegrable (coefficientDerivativeSource p a u Omega l) (volume.restrict Omega) := by
  apply locallyIntegrable_finsetSum Finset.univ
  intro i _
  apply locallyIntegrable_finsetSum Finset.univ
  intro j _
  have hw : MemW1p p (chosenWeakPartialOrZero p j u Omega) Omega :=
    MemWkp.one_iff_memW1p.mp (hu.chosenWeakPartial_mem j)
  have hda : ContDiff ℝ 1
      (fun x => (fderiv ℝ (fun y => a y i j) x) (EuclideanSpace.single l 1)) :=
    ((ha i j).fderiv_right (by norm_num)).clm_apply contDiff_const
  exact (((chosenWeakPartialOrZero_memLp_of_mem hu.memW1p j).locallyIntegrable hp).continuous_mul
    ((hda.continuous_fderiv one_ne_zero).clm_apply continuous_const)).add
    (((chosenWeakPartialOrZero_memLp_of_mem hw i).locallyIntegrable hp).continuous_mul
      hda.continuous)

private theorem memLp_continuous_mul
    {Omega : Set E} (hOmega : MeasurableSet Omega)
    (hcompact : IsCompact (closure Omega))
    {p : ℝ≥0∞} {a f : E → ℝ} (ha : Continuous a)
    (hf : MemLp f p (volume.restrict Omega)) :
    MemLp (fun x => a x * f x) p (volume.restrict Omega) := by
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn ha.continuousOn
  apply hf.mul' (p := ⊤) (r := p)
  refine memLp_top_of_bound ha.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hOmega] with x hx
  exact hC x (subset_closure hx)

theorem memLp_coefficientDerivativeField
    {Omega : Set E} (hOmega : MeasurableSet Omega)
    (hcompact : IsCompact (closure Omega))
    {p : ℝ≥0∞} {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j))
    {u : E → ℝ} (hu : MemW1p p u Omega) (l : Fin d) :
    MemLp (coefficientDerivativeField p a u Omega l) p (volume.restrict Omega) := by
  refine MemLp.of_eval_piLp ?_
  intro i
  simpa only [coefficientDerivativeField, PiLp.toLp_apply] using
    memLp_finsetSum Finset.univ (fun j _ =>
      memLp_continuous_mul hOmega hcompact (contDiff_partial_eta (ha i j) l).continuous
        (chosenWeakPartialOrZero_memLp_of_mem hu j))

theorem memLp_coefficientDerivativeSource
    {Omega : Set E} (hOmega : MeasurableSet Omega)
    (hcompact : IsCompact (closure Omega))
    {p : ℝ≥0∞} {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j))
    {u : E → ℝ} (hu : MemWkp 2 p u Omega) (l : Fin d) :
    MemLp (coefficientDerivativeSource p a u Omega l) p (volume.restrict Omega) := by
  apply memLp_finsetSum Finset.univ
  intro i _
  apply memLp_finsetSum Finset.univ
  intro j _
  have hdu : MemW1p p (chosenWeakPartialOrZero p j u Omega) Omega :=
    (MemWkp.one_iff_memW1p).mp (hu.chosenWeakPartial_mem j)
  exact (memLp_continuous_mul hOmega hcompact
    (contDiff_partial_eta (contDiff_partial_eta (ha i j) l) i).continuous
    (chosenWeakPartialOrZero_memLp_of_mem hu.memW1p j)).add
    (memLp_continuous_mul hOmega hcompact (contDiff_partial_eta (ha i j) l).continuous
      (chosenWeakPartialOrZero_memLp_of_mem hdu i))

private theorem memWkp_smooth_mul
    (m : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E} (hOmega : IsOpen Omega)
    (hcompact : IsCompact (closure Omega))
    {a f : E → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hf : MemWkp m p f Omega) :
    MemWkp m p (fun x => a x * f x) Omega := by
  obtain ⟨C, _, hC⟩ :=
    DifferentialGeometry.Analysis.Calculus.exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
      isOpen_univ ha.contDiffOn hcompact (subset_univ _) m
  exact MemWkp.smul_smooth_bounded m hp hOmega ha
    (fun j hj x hx => by
      simpa only [iteratedFDerivWithin_univ] using hC x (subset_closure hx) j hj) hf

theorem memWkp_coefficientDerivativeSource
    (m : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E} (hOmega : IsOpen Omega)
    (hcompact : IsCompact (closure Omega))
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j))
    {u : E → ℝ} (hu : MemWkp (m + 2) p u Omega) (l : Fin d) :
    MemWkp m p (coefficientDerivativeSource p a u Omega l) Omega := by
  apply MemWkp.finset_sum hp hOmega Finset.univ
  intro i _
  apply MemWkp.finset_sum hp hOmega Finset.univ
  intro j _
  exact MemWkp.add hp hOmega
    (memWkp_smooth_mul m hp hOmega hcompact
      (contDiff_partial_eta (contDiff_partial_eta (ha i j) l) i)
      ((hu.chosenWeakPartial_mem j).le_of_le (Nat.le_succ m)))
    (memWkp_smooth_mul m hp hOmega hcompact (contDiff_partial_eta (ha i j) l)
      ((hu.chosenWeakPartial_mem j).chosenWeakPartial_mem i))

theorem hasWeakDiv_coefficientDerivativeField
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E} (hOmega : IsOpen Omega)
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j))
    {u : E → ℝ} (hu : MemWkp 2 p u Omega) (l : Fin d) :
    HasWeakDiv (coefficientDerivativeSource p a u Omega l)
      (coefficientDerivativeField p a u Omega l) Omega := by
  let c : Fin d → Fin d → E → ℝ :=
    fun i j x => (fderiv ℝ (fun y => a y i j) x) (EuclideanSpace.single l 1)
  let w : Fin d → E → ℝ := fun j => chosenWeakPartialOrZero p j u Omega
  let v : Fin d → Fin d → E → ℝ :=
    fun i j => chosenWeakPartialOrZero p i (w j) Omega
  let g : Fin d → Fin d → E → ℝ := fun i j x =>
    (fderiv ℝ (c i j) x) (EuclideanSpace.single i 1) * w j x + c i j x * v i j x
  have hc : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (c i j) :=
    fun i j => contDiff_partial_eta (ha i j) l
  have hw : ∀ j, MemW1p p (w j) Omega := fun j =>
    MemWkp.one_iff_memW1p.mp (hu.chosenWeakPartial_mem j)
  have hwloc : ∀ j, LocallyIntegrable (w j) (volume.restrict Omega) :=
    fun j => (hw j).1.locallyIntegrable hp
  have hvloc : ∀ i j, LocallyIntegrable (v i j) (volume.restrict Omega) :=
    fun i j => (chosenWeakPartialOrZero_memLp_of_mem (hw j) i).locallyIntegrable hp
  have hfloc : ∀ i j, LocallyIntegrable (fun x => c i j x * w j x)
      (volume.restrict Omega) :=
    fun i j => (hwloc j).continuous_mul (hc i j).continuous
  have hgloc : ∀ i j, LocallyIntegrable (g i j) (volume.restrict Omega) := fun i j =>
    ((hwloc j).continuous_mul (contDiff_partial_eta (hc i j) i).continuous).add
      ((hvloc i j).continuous_mul (hc i j).continuous)
  have hparts : ∀ i j, HasWeakPartialDeriv i (g i j)
      (fun x => c i j x * w j x) Omega := by
    intro i j
    have hprod := (chosenWeakPartialOrZero_isWeakPartial_of_mem (hw j) i).mul_smooth
      hOmega (hc i j) (hwloc j) (hvloc i j)
    simpa only [g, v, add_comm] using hprod
  have hsum := hasWeakDiv_sum_of_hasWeakPartialDeriv
    (F := coefficientDerivativeField p a u Omega l)
    (G := fun i x => ∑ j, g i j x)
    (locallyIntegrable_coefficientDerivativeField_apply hp
      (fun i j => (ha i j).of_le (by norm_cast)) hu.memW1p l)
    (fun i => locallyIntegrable_finsetSum Finset.univ (fun j _ => hgloc i j))
    (fun i => by
      simpa only [coefficientDerivativeField, PiLp.toLp_apply, c, w] using
        HasWeakPartialDeriv.finset_sum Finset.univ (fun j _ => hfloc i j)
          (fun j _ => hgloc i j) (fun j _ => hparts i j))
  simpa only [coefficientDerivativeSource, c, w, v, g] using! hsum

end DeGiorgi
