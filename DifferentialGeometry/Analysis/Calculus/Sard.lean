import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.HausdorffDimension
import DifferentialGeometry.Analysis.Integration.Measure.HausdorffDimension
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.Module.LinearMap.DivisionRing

section

open Set MeasureTheory
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem dense_regular_values_endomorphism {f : E → E} (hf : Differentiable ℝ f) :
    Dense {y : E | ∀ x, f x = y → Function.Bijective (fderiv ℝ f x)} := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let s : Set E := {x | (fderiv ℝ f x).det = 0}
  have hnull : Measure.addHaar (f '' s) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero Measure.addHaar
      (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx)
  have hdense : Dense ((f '' s)ᶜ) := Measure.dense_of_ae (μ := Measure.addHaar) (by
    rw [ae_iff]
    have hset : {a | ¬a ∉ f '' s} = f '' s := by
      ext z
      simp only [Set.mem_ofPred_eq, not_not]
    rw [hset]
    exact hnull)
  apply hdense.mono
  intro y hy x hxy
  have hdet : (fderiv ℝ f x).det ≠ 0 := by
    intro hx
    exact hy ⟨x, hx, hxy⟩
  have hker : (fderiv ℝ f x).ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hinj : Function.Injective (fderiv ℝ f x) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem Differentiable.dense_regular_values_of_finrank_eq {f : E → F}
    (hf : Differentiable ℝ f) (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    Dense {y : F | ∀ x, f x = y → Function.Bijective (fderiv ℝ f x)} := by
  let e : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  have h := dense_regular_values_endomorphism (e.differentiable.comp hf)
  have hpre := h.preimage e.toHomeomorph.isOpenMap
  apply hpre.mono
  intro y hy x hxy
  have hbij := hy x (congrArg e hxy)
  have heq : fderiv ℝ (e ∘ f) x = e.toContinuousLinearMap.comp (fderiv ℝ f x) := by
    rw [fderiv_comp x e.differentiableAt (hf x), e.fderiv]
  rw [heq] at hbij
  constructor
  · intro v w hvw
    apply hbij.1
    exact congrArg e hvw
  · intro v
    obtain ⟨w, hw⟩ := hbij.2 (e v)
    exact ⟨w, e.injective hw⟩

theorem ContDiffOn.addHaar_image_eq_zero_of_finrank_lt [SecondCountableTopology E]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [Measure.IsAddHaarMeasure μ]
    {f : E → F} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F) :
    μ (f '' s) = 0 := by
  have hloc : dimH (f '' s) ≤ dimH s := by
    refine dimH_image_le_of_locally_lipschitzOn fun x hx => ?_
    obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
    refine ⟨K, t ∩ s, ?_, hK.mono inter_subset_left⟩
    exact Filter.mem_inf_iff.mpr ⟨t, ht, s, Filter.mem_principal.mpr subset_rfl, rfl⟩
  have hlt : dimH (f '' s) < Module.finrank ℝ F := by
    calc dimH (f '' s) ≤ dimH s := hloc
      _ ≤ (Module.finrank ℝ E : ℝ≥0∞) :=
        (dimH_mono (subset_univ s)).trans_eq (Real.dimH_univ_eq_finrank E)
      _ < (Module.finrank ℝ F : ℝ≥0∞) := by exact_mod_cast hdim
  exact DifferentialGeometry.MeasureTheory.addHaar_eq_zero_of_dimH_lt μ hlt

theorem volume_le_of_subset_slab {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hV : V ≠ ⊤)
    (c : EuclideanSpace ℝ (Fin n)) {A B : ℝ} (ha : 0 ≤ A)
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (h1 : ∀ y ∈ T, ‖y - c‖ ≤ A)
    (h2 : ∀ y ∈ T, ∃ v ∈ V, ∃ w, ‖w‖ ≤ B ∧ y - c = v + w) :
    volume T ≤ ENNReal.ofReal ((2*A)^(n-1) * (2*B)) := by
  classical
  have hperp : Vᗮ ≠ ⊥ := by
    intro hbot
    have h2 : Module.finrank ℝ ↥(Vᗮ) = 0 := by rw [hbot]; simp
    have h3 := Submodule.finrank_add_finrank_orthogonal V
    rw [h2, Nat.add_zero] at h3
    exact hV (Submodule.eq_top_of_finrank_eq h3)
  obtain ⟨u, huV, hunorm⟩ : ∃ u ∈ Vᗮ, ‖u‖ = 1 := by
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hperp
    refine ⟨‖u‖⁻¹ • u, Submodule.smul_mem _ _ hu, ?_⟩
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u),
      inv_mul_cancel₀ (ne_of_gt hpos)]
  have horth : Orthonormal ℝ ((↑) : ({u} : Set (EuclideanSpace ℝ (Fin n))) →
      EuclideanSpace ℝ (Fin n)) := by
    rw [orthonormal_iff_ite]
    intro i j
    obtain rfl : i = j := Subsingleton.elim i j
    have hi : (i : EuclideanSpace ℝ (Fin n)) = u := Set.mem_singleton_iff.mp i.2
    rw [if_pos rfl, hi, real_inner_self_eq_norm_sq, hunorm]
    norm_num
  obtain ⟨ι, b, hsub, hb⟩ := horth.exists_orthonormalBasis_extension
  have humem : u ∈ ι := by simpa using hsub (mem_singleton u)
  set i0 : ↥ι := ⟨u, humem⟩ with hi0
  have hb0 : b i0 = u := by
    have h := congrFun hb i0
    simpa [i0] using h
  have hcard : Fintype.card ↥ι = n := by
    rw [Fintype.card_coe]
    have h1 := Module.finrank_eq_card_finset_basis b.toBasis
    rw [finrank_euclideanSpace_fin] at h1
    exact h1.symm
  set fsz : ↥ι → ℝ := fun i => if i = i0 then B else A with hfsz
  have hfsz_i0 : fsz i0 = B := by simp [hfsz]
  have hfsz_ne : ∀ i, i ≠ i0 → fsz i = A := by intro i hi; simp [hfsz, hi]
  set Box0 : Set (EuclideanSpace ℝ ↥ι) :=
    {z | ∀ i, z.ofLp i ∈ Icc (-(fsz i)) (fsz i)} with hBox0
  set Box : Set (EuclideanSpace ℝ ↥ι) :=
    {z | ∀ i, (z - b.repr c).ofLp i ∈ Icc (-(fsz i)) (fsz i)} with hBox
  have hsubT : T ⊆ b.repr.symm '' Box := by
    intro y hy
    refine ⟨b.repr y, ?_, ?_⟩
    · intro i
      rw [mem_Icc]
      by_cases hi : i = i0
      · subst hi
        rw [hfsz_i0]
        obtain ⟨v, hvV, w, hw, hyw⟩ := h2 y hy
        have hcoord : (b.repr y - b.repr c).ofLp i0
            = (b.repr v).ofLp i0 + (b.repr w).ofLp i0 := by
          rw [← map_sub, hyw, map_add, WithLp.ofLp_add, Pi.add_apply]
        have hv0 : (b.repr v).ofLp i0 = 0 := by
          rw [OrthonormalBasis.repr_apply_apply, hb0, real_inner_comm]
          exact (Submodule.mem_orthogonal V u).mp huV v hvV
        have hbound : |(b.repr w).ofLp i0| ≤ B := by
          calc |(b.repr w).ofLp i0| = |inner ℝ u w| := by
                rw [OrthonormalBasis.repr_apply_apply, hb0]
            _ ≤ ‖u‖ * ‖w‖ := abs_real_inner_le_norm u w
            _ = ‖w‖ := by rw [hunorm, one_mul]
            _ ≤ B := hw
        rw [hcoord, hv0, zero_add]
        exact abs_le.mp hbound
      · rw [hfsz_ne i hi]
        have hnorm : ‖b.repr y - b.repr c‖ = ‖y - c‖ := by
          rw [← map_sub, b.repr.norm_map]
        have hle : ‖(b.repr y - b.repr c).ofLp i‖ ≤ ‖b.repr y - b.repr c‖ :=
          PiLp.norm_apply_le _ i
        rw [Real.norm_eq_abs] at hle
        exact abs_le.mp (le_trans hle (le_trans (le_of_eq hnorm) (h1 y hy)))
    · simp
  have hBox_meas : MeasurableSet Box := by
    have hset : Box = ⋂ i, {z : EuclideanSpace ℝ ↥ι |
        (z - b.repr c).ofLp i ∈ Icc (-(fsz i)) (fsz i)} := by
      ext z; simp [hBox]
    rw [hset]
    exact MeasurableSet.iInter fun i => isClosed_Icc.measurableSet.preimage (by fun_prop)
  have hBox_eq : b.repr.symm '' Box = b.repr ⁻¹' Box := by
    ext z; constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hz; exact ⟨b.repr z, hz, by simp⟩
  have hmeas1 : volume (b.repr.symm '' Box) = volume Box := by
    rw [hBox_eq, ← Measure.map_apply b.repr.continuous.measurable hBox_meas,
      b.repr.measurePreserving.map_eq]
  have htrans : volume Box = volume Box0 := by
    have hset : Box = (fun z : EuclideanSpace ℝ ↥ι => z + (-(b.repr c))) ⁻¹' Box0 := by
      ext z; simp [hBox, hBox0, sub_eq_add_neg]
    rw [hset]
    exact measure_preimage_add_right volume (-(b.repr c)) Box0
  have hsplitS : Box0 = WithLp.ofLp ⁻¹'
      (Set.pi univ (fun i : ↥ι => Icc (-(fsz i)) (fsz i))) := by
    ext z; constructor
    · intro h i; simpa using h i
    · intro h i; simpa using h i
  have hmeas2 : volume Box0 = volume (Set.pi univ
      (fun i : ↥ι => Icc (-(fsz i)) (fsz i))) := by
    rw [hsplitS, ← Measure.map_apply (by fun_prop) (MeasurableSet.pi countable_univ
      (fun i _ => measurableSet_Icc)), (PiLp.volume_preserving_ofLp ↥ι).map_eq]
  have hprodeq : volume (Set.pi univ (fun i : ↥ι => Icc (-(fsz i)) (fsz i)))
      = ∏ i : ↥ι, volume (Icc (-(fsz i)) (fsz i)) := by
    have hvol : (volume : Measure (↥ι → ℝ)) = Measure.pi (fun _ => volume) := rfl
    rw [hvol]
    exact Measure.pi_pi _ _
  have hiv : ∀ i : ↥ι, volume (Icc (-(fsz i)) (fsz i)) = ENNReal.ofReal (2 * fsz i) := by
    intro i
    rw [Real.volume_Icc]
    congr 1
    ring
  have hrest : ∏ i ∈ (Finset.univ : Finset ↥ι).erase i0, ENNReal.ofReal (2 * fsz i)
      = ENNReal.ofReal (2 * A) ^ (n - 1) := by
    have h1 : ∏ i ∈ (Finset.univ : Finset ↥ι).erase i0, ENNReal.ofReal (2 * fsz i)
        = ∏ _i ∈ (Finset.univ : Finset ↥ι).erase i0, ENNReal.ofReal (2 * A) :=
      Finset.prod_congr rfl fun i hi => by rw [hfsz_ne i (Finset.mem_erase.mp hi).1]
    rw [h1, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i0),
      Finset.card_univ, hcard]
  calc volume T ≤ volume (b.repr.symm '' Box) := measure_mono hsubT
    _ = volume Box := hmeas1
    _ = volume Box0 := htrans
    _ = volume (Set.pi univ (fun i : ↥ι => Icc (-(fsz i)) (fsz i))) := hmeas2
    _ = ∏ i : ↥ι, volume (Icc (-(fsz i)) (fsz i)) := hprodeq
    _ = ∏ i : ↥ι, ENNReal.ofReal (2 * fsz i) := Finset.prod_congr rfl fun i _ => hiv i
    _ = ENNReal.ofReal ((2*A)^(n-1) * (2*B)) := by
      rw [← Finset.prod_erase_mul (Finset.univ : Finset ↥ι) _ (Finset.mem_univ i0), hfsz_i0,
        hrest, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
        mul_comm]

end

noncomputable section
universe u

open Set MeasureTheory Filter
open scoped ContDiff Topology NNReal ENNReal
namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contDiffOn_iteratedFDeriv {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) :
    ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k f) U := by
  intro x hx
  exact ((hf.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right
    (m := ∞) (by exact_mod_cast (le_top : (⊤ : ℕ∞) + k ≤ ⊤))).contDiffWithinAt

private theorem jet_evaluation_derivative {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U)
    {k : ℕ} (v : Fin (k + 1) → E) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ k f y (Fin.tail v)) x (v 0) =
      iteratedFDeriv ℝ (k + 1) f x v := by
  exact ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
    (m := k) (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).iteratedFDeriv_succ_apply_left'.symm

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
private theorem measure_prod_eq_zero_of_sections {S : Set (ℝ × F)}
    [MeasurableSpace F] (hS : MeasurableSet S)
    (ν : Measure F) (hs : ∀ t : ℝ, ν (Prod.mk t ⁻¹' S) = 0) :
    ((volume : Measure ℝ).prod ν) S = 0 := by
  exact Measure.measure_prod_null_of_ae_null hS (Filter.Eventually.of_forall hs)

private theorem holder_image_null [FiniteDimensional ℝ E] {m n : ℕ} (hn : 0 < n)
    (hm : Module.finrank ℝ E = m)
    {f : E → EuclideanSpace ℝ (Fin n)}
    {s : Set E} {C : ℝ≥0}
    (hf : HolderOnWith C (m + 1) f s) : volume (f '' s) = 0 := by
  apply DifferentialGeometry.MeasureTheory.addHaar_eq_zero_of_dimH_lt volume
  rw [finrank_euclideanSpace_fin]
  have hdim : dimH s ≤ (m : ℝ≥0∞) := by
    exact (dimH_mono (subset_univ s)).trans_eq
      (by simp [Real.dimH_univ_eq_finrank, hm])
  have hratio : (m : ℝ≥0∞) / (m + 1) < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp))]
    simpa using (show (m : ℝ≥0∞) < m + 1 by exact_mod_cast Nat.lt_succ_self m)
  have hlt : dimH (f '' s) < 1 := by
    have hh := hf.dimH_image_le (by positivity)
    simp only [ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one] at hh
    exact hh.trans_lt ((ENNReal.div_le_div_right hdim _).trans_lt hratio)
  exact hlt.trans_le (by exact_mod_cast hn)


private theorem jet_evaluation_smooth {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) (v : Fin k → E) :
    ContDiffOn ℝ ∞ (fun x => iteratedFDeriv ℝ k f x v) U := by
  exact (contDiffOn_iteratedFDeriv hU hf k).continuousLinearMap_comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) F v)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem holderOnWith_of_norm_sub_le_pow {f : E → F} {s : Set E} {C : ℝ≥0} {k : ℕ}
    (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ k) :
    HolderOnWith C k f s := by
  intro x hx y hy
  simpa only [edist_dist, dist_eq_norm, NNReal.coe_natCast, ENNReal.rpow_natCast,
    ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_pow (norm_nonneg _)] using ENNReal.ofReal_le_ofReal (h x hx y hy)

private theorem isOpen_surjective [FiniteDimensional ℝ F] :
    IsOpen {L : E →L[ℝ] F | Function.Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L hL
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  let R' : F →L[ℝ] E := R.toContinuousLinearMap
  have hLR : L.comp R' = ContinuousLinearMap.id ℝ F := by
    ext x
    exact congrArg (fun A : F →ₗ[ℝ] F => A x) hR
  have hnh : Set.range (fun A : F ≃L[ℝ] F => (A : F →L[ℝ] F)) ∈ 𝓝 (L.comp R') := by
    rw [hLR]
    exact (ContinuousLinearEquiv.refl ℝ F).nhds
  have hc : Continuous (fun S : E →L[ℝ] F => S.comp R') :=
    continuous_id.clm_comp continuous_const
  apply Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hnh)
  rintro S ⟨A, hA⟩
  change (A : F →L[ℝ] F) = S.comp R' at hA
  have hs : Function.Surjective (S.comp R') := by
    rw [← hA]
    exact A.surjective
  exact Function.Surjective.of_comp hs

private theorem exists_scalar_jet_detector {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) {k : ℕ}
    (hnext : iteratedFDeriv ℝ (k + 1) f x ≠ 0) :
    ∃ h : E → ℝ, ContDiffOn ℝ ∞ h U ∧
      (∀ y : E, iteratedFDeriv ℝ k f y = 0 → h y = 0) ∧ fderiv ℝ h x ≠ 0 := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hnext
  have hv' : iteratedFDeriv ℝ (k + 1) f x v ≠ 0 := by simpa using hv
  obtain ⟨ℓ, _, hℓ⟩ := exists_dual_vector ℝ
    (iteratedFDeriv ℝ (k + 1) f x v) (norm_ne_zero_iff.mpr hv')
  let q : E → F := fun y => iteratedFDeriv ℝ k f y (Fin.tail v)
  have hq : ContDiffOn ℝ ∞ q U := jet_evaluation_smooth hU hf k (Fin.tail v)
  refine ⟨ℓ ∘ q, hq.continuousLinearMap_comp ℓ, ?_, ?_⟩
  · intro y hy
    simp [q, hy]
  · intro hzero
    have hqd := (hq.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hder := (ℓ.hasFDerivAt.comp x hqd.hasFDerivAt).fderiv
    have hz := congrArg (fun A : E →L[ℝ] ℝ => A (v 0)) hzero
    rw [hder] at hz
    change ℓ (fderiv ℝ q x (v 0)) = 0 at hz
    have hjet : fderiv ℝ q x (v 0) = iteratedFDeriv ℝ (k + 1) f x v :=
      jet_evaluation_derivative hU hf hx v
    rw [hjet, hℓ] at hz
    exact (norm_ne_zero_iff.mpr hv') hz

variable [CompleteSpace F]

private theorem flat_taylor_bound {f : E → F} {x y : E} {k : ℕ} {B : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (k + 1) f (x + t • y))
    (hz : ∀ i : ℕ, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (k + 1) f (x + t • y)‖ ≤ B) :
    ‖f (x + y) - f x‖ ≤ (k.factorial : ℝ)⁻¹ * B * ‖y‖ ^ (k + 1) := by
  have hsum : (∑ i ∈ Finset.range (k + 1), (i.factorial : ℝ)⁻¹ •
      iteratedFDeriv ℝ i f x (fun _ => y)) = f x := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hi0
      simp [hz i (Nat.one_le_iff_ne_zero.mpr hi0)
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    · simp
  have heq := map_add_eq_sum_add_integral_iteratedFDeriv hf
  rw [hsum] at heq
  have hint : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ k •
      iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ => y)‖ ≤ B * ‖y‖ ^ (k + 1) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := B * ‖y‖ ^ (k + 1)) (f := fun t => (1 - t) ^ k •
        iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ => y))
    have hb' : ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖(1 - t) ^ k • iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ => y)‖
          ≤ B * ‖y‖ ^ (k + 1) := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
      have hp : 0 ≤ 1 - t := sub_nonneg.mpr ht'.2
      have hp1 : (1 - t) ^ k ≤ 1 := pow_le_one₀ hp (sub_le_self _ ht'.1)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hp _)]
      calc
        (1 - t) ^ k * ‖iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ => y)‖
          ≤ 1 * ‖iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ => y)‖ :=
            mul_le_mul_of_nonneg_right hp1 (norm_nonneg _)
        _ ≤ B * ‖y‖ ^ (k + 1) := by
          simp only [one_mul]
          calc
            ‖iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ => y)‖
              ≤ ‖iteratedFDeriv ℝ (k + 1) f (x + t • y)‖ * ‖y‖ ^ (k + 1) := by
                simpa using (iteratedFDeriv ℝ (k + 1) f (x + t • y)).le_opNorm (fun _ => y)
            _ ≤ B * ‖y‖ ^ (k + 1) :=
              mul_le_mul_of_nonneg_right (hb t ht') (pow_nonneg (norm_nonneg _) _)
    apply le_trans (hi (by simpa only [uIoc_of_le zero_le_one] using hb'))
    simp
  rw [heq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact (mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq
    (mul_assoc _ _ _).symm


private theorem exists_holderOnWith_on_flat_set {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hK : IsCompact K) (hc : Convex ℝ K) (hKU : K ⊆ U) (k : ℕ) :
    ∃ C : ℝ≥0, HolderOnWith C (k + 1) f
      {x | x ∈ K ∧ ∀ i : ℕ, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0} := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((contDiffOn_iteratedFDeriv hU hf (k + 1)).continuousOn.mono hKU)
  let C : ℝ≥0 := ⟨(k.factorial : ℝ)⁻¹ * max B 0, by positivity⟩
  refine ⟨C, ?_⟩
  rw [show (k : ℝ≥0) + 1 = ((k + 1 : ℕ) : ℝ≥0) by simp]
  apply holderOnWith_of_norm_sub_le_pow
  intro x hx y hy
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (k + 1) f (x + t • (y - x))‖ ≤ max B 0 := by
    intro t ht
    exact (hB _ (hc.add_smul_sub_mem hx.1 hy.1 ht)).trans (le_max_left _ _)
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (k + 1) f (x + t • (y - x)) := by
    intro t ht
    exact (hf.contDiffAt (hU.mem_nhds (hKU (hc.add_smul_sub_mem hx.1 hy.1 ht)))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (k + 1))
  have h := flat_taylor_bound hd hx.2 hb
  change ‖f x - f y‖ ≤ ((k.factorial : ℝ)⁻¹ * max B 0) * ‖x - y‖ ^ (k + 1)
  simpa only [add_sub_cancel, norm_sub_rev] using h

private theorem image_null_of_locally_null {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace Y]
    (μ : Measure Y) {f : X → Y} {s : Set X}
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, μ (f '' t) = 0) : μ (f '' s) = 0 := by
  choose! t ht hzero using h
  obtain ⟨a, has, hac, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin ht
  apply measure_mono_null (image_mono hcover)
  simp only [image_iUnion]
  exact (measure_biUnion_null_iff hac).mpr fun x hx => hzero x (has hx)

private theorem volume_image_flat_set_eq_zero [FiniteDimensional ℝ E] {n : ℕ} (hn : 0 < n)
    {f : E → EuclideanSpace ℝ (Fin n)}
    {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ∀ i : ℕ, 1 ≤ i → i ≤ Module.finrank ℝ E →
      iteratedFDeriv ℝ i f x = 0}) = 0 := by
  apply image_null_of_locally_null volume
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx.1)
  let K := Metric.closedBall x (r / 2)
  have hKU : K ⊆ U := (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrU
  obtain ⟨C, hC⟩ := exists_holderOnWith_on_flat_set hU hf
    (isCompact_closedBall x (r / 2)) (convex_closedBall x (r / 2)) hKU (Module.finrank ℝ E)
  refine ⟨K ∩ {y | y ∈ U ∧ ∀ i : ℕ, 1 ≤ i → i ≤ Module.finrank ℝ E →
      iteratedFDeriv ℝ i f y = 0}, ?_, ?_⟩
  · exact inter_mem (mem_nhdsWithin_of_mem_nhds
      (Metric.closedBall_mem_nhds x (half_pos hr))) self_mem_nhdsWithin
  · exact holder_image_null hn rfl (hC.mono fun y hy => ⟨hy.1, hy.2.2⟩)


omit [CompleteSpace F] in
private theorem critical_image_isSigmaCompact [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    IsSigmaCompact (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hd : Continuous (fun x : U => fderiv ℝ f x) :=
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).domRestrict
  have hc : IsClosed {x : U | ¬ Function.Surjective (fderiv ℝ f x)} :=
    (isOpen_surjective (E := E) (F := F)).isClosed_compl.preimage hd
  have hs : IsSigmaCompact {x : U | ¬ Function.Surjective (fderiv ℝ f x)} :=
    isSigmaCompact_univ.of_isClosed_subset hc (subset_univ _)
  have hi := hs.image_of_continuousOn hf.continuousOn.domRestrict.continuousOn
  have heq : (fun x : U => f x) '' {x : U | ¬ Function.Surjective (fderiv ℝ f x)} =
      f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)} := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, ⟨x.property, hx⟩, hxy⟩
    · rintro ⟨x, ⟨hxU, hx⟩, hxy⟩
      exact ⟨⟨x, hxU⟩, hx, hxy⟩
  change IsSigmaCompact ((fun x : U => f x) ''
    {x : U | ¬ Function.Surjective (fderiv ℝ f x)}) at hi
  rwa [heq] at hi

private theorem measurableSet_of_isSigmaCompact {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    {S : Set X} (hS : IsSigmaCompact S) : MeasurableSet S := by
  obtain ⟨K, hK, hKS⟩ := hS
  rw [← hKS]
  exact MeasurableSet.iUnion fun i => (hK i).measurableSet


private def splitEuclidean (d : ℕ) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin d) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => ℝ)).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).symm.trans
      ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm))

private theorem volume_preserving_splitEuclidean (d : ℕ) :
    MeasurePreserving (splitEuclidean d) := by
  have hmid : MeasurePreserving (Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).symm := by
    convert volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 using 1
    funext x
    apply Prod.ext rfl
    funext i
    change x i.succ = x ((0 : Fin (d + 1)).succAbove i)
    simp
  have hlast := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin d))
  exact hlast.comp (hmid.comp (PiLp.volume_preserving_ofLp (Fin (d + 1))))

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

variable {E X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem surjective_fderiv_comp_symm_iff (e : OpenPartialHomeomorph E X)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f e.source)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {y : X} (hy : y ∈ e.target) :
    Function.Surjective (fderiv ℝ (f ∘ e.symm) y) ↔
      Function.Surjective (fderiv ℝ f (e.symm y)) := by
  have hx := e.map_target hy
  have hd := (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hi := (hei.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hfd := (hf.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hleft : (e.symm ∘ e) =ᶠ[𝓝 (e.symm y)] id := by
    filter_upwards [e.open_source.mem_nhds hx] with x hx using e.left_inv hx
  have hi' : HasFDerivAt e.symm (fderiv ℝ e.symm y) (e (e.symm y)) := by
    simpa only [e.right_inv hy] using hi.hasFDerivAt
  have hinv : (fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y)) =
      ContinuousLinearMap.id ℝ E := by
    have hchain : HasFDerivAt (e.symm ∘ e)
        ((fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y))) (e.symm y) := by
      simpa only [e.right_inv hy] using hi'.comp (e.symm y) hd.hasFDerivAt
    exact hchain.unique ((hasFDerivAt_id _).congr_of_eventuallyEq hleft)
  have hsurj : Function.Surjective (fderiv ℝ e.symm y) := by
    intro x
    refine ⟨fderiv ℝ e (e.symm y) x, ?_⟩
    exact congrArg (fun L : E →L[ℝ] E => L x) hinv
  rw [fderiv_comp y hfd hi]
  change Function.Surjective ((fderiv ℝ f (e.symm y)) ∘ (fderiv ℝ e.symm y)) ↔ _
  exact ⟨Function.Surjective.of_comp, fun h => h.comp hsurj⟩

private theorem surjective_fderiv_slice_iff {G : ℝ × E → ℝ × F} {W : Set (ℝ × E)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hfst : ∀ p ∈ W, (G p).1 = p.1) {p : ℝ × E} (hp : p ∈ W) :
    Function.Surjective (fderiv ℝ G p) ↔
      Function.Surjective (fderiv ℝ (fun z : E => (G (p.1, z)).2) p.2) := by
  have hd := (hG.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)
  have heq : (fun q => (G q).1) =ᶠ[𝓝 p] Prod.fst := by
    filter_upwards [hW.mem_nhds hp] with q hq using hfst q hq
  have hfirst : (ContinuousLinearMap.fst ℝ ℝ F).comp (fderiv ℝ G p) =
      ContinuousLinearMap.fst ℝ ℝ E :=
    hd.hasFDerivAt.fst.unique (hasFDerivAt_fst.congr_of_eventuallyEq heq)
  have hi : HasFDerivAt (fun z : E => (p.1, z)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hB : fderiv ℝ (fun z : E => (G (p.1, z)).2) p.2 =
      ((ContinuousLinearMap.snd ℝ ℝ F).comp (fderiv ℝ G p)).comp
        (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hd' : HasFDerivAt (fun q => (G q).2)
        ((ContinuousLinearMap.snd ℝ ℝ F).comp (fderiv ℝ G p)) (p.1,p.2) :=
      hd.hasFDerivAt.snd
    exact (hd'.comp p.2 hi).fderiv
  have hfst' (v : ℝ × E) : (fderiv ℝ G p v).1 = v.1 :=
    congrArg (fun L : (ℝ × E) →L[ℝ] ℝ => L v) hfirst
  constructor
  · intro h y
    obtain ⟨⟨t,z⟩, hz⟩ := h (0,y)
    have ht : t = 0 := (hfst' (t,z)).symm.trans (congrArg Prod.fst hz)
    refine ⟨z, ?_⟩
    rw [hB]
    change (fderiv ℝ G p (0,z)).2 = y
    simpa only [ht] using congrArg Prod.snd hz
  · intro h ⟨t,y⟩
    obtain ⟨z,hz⟩ := h (y - (fderiv ℝ G p (t,0)).2)
    refine ⟨(t,z), Prod.ext (hfst' _) ?_⟩
    rw [hB] at hz
    change (fderiv ℝ G p (0,z)).2 = _ at hz
    have hv : (t,z) = (t,0) + (0,z) := by simp
    rw [hv, map_add]
    change (fderiv ℝ G p (t,0)).2 + (fderiv ℝ G p (0,z)).2 = y
    rw [hz, add_sub_cancel]

private theorem critical_image_slice_eq {G : ℝ × E → ℝ × F} {W : Set (ℝ × E)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hfst : ∀ p ∈ W, (G p).1 = p.1) (t : ℝ) :
    {y : F | (t,y) ∈ G '' {p | p ∈ W ∧ ¬ Function.Surjective (fderiv ℝ G p)}} =
      (fun z : E => (G (t,z)).2) ''
        {z | (t,z) ∈ W ∧ ¬ Function.Surjective (fderiv ℝ (fun w => (G (t,w)).2) z)} := by
  ext y
  constructor
  · rintro ⟨⟨s,z⟩, ⟨hp,hc⟩, heq⟩
    have hst : s = t := (hfst (s,z) hp).symm.trans (congrArg Prod.fst heq)
    subst s
    exact ⟨z, ⟨hp, fun h => hc ((surjective_fderiv_slice_iff hW hG hfst hp).mpr h)⟩,
      congrArg Prod.snd heq⟩
  · rintro ⟨z,⟨hp,hc⟩,rfl⟩
    exact ⟨(t,z), ⟨hp, fun h => hc ((surjective_fderiv_slice_iff hW hG hfst hp).mp h)⟩,
      Prod.ext (hfst (t,z) hp) rfl⟩

private theorem image_hypersurface_subset_critical_image [Nontrivial F]
    {f : E → F} (e : OpenPartialHomeomorph E (ℝ × X)) {A : Set E}
    (hf : ContDiffOn ℝ ∞ f e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hzero : ∀ x ∈ A ∩ e.source, (e x).1 = 0 ∧ fderiv ℝ f x = 0) :
    f '' (A ∩ e.source) ⊆ (fun z : X => f (e.symm (0,z))) ''
      {z | (0,z) ∈ e.target ∧ ¬ Function.Surjective
        (fderiv ℝ (fun w : X => f (e.symm (0,w))) z)} := by
  rintro y ⟨x,hx,rfl⟩
  let z := (e x).2
  have heq : e x = (0,z) := Prod.ext (hzero x hx).1 rfl
  have hz : (0,z) ∈ e.target := heq ▸ e.map_source hx.2
  have hinv : e.symm (0,z) = x := by rw [← heq, e.left_inv hx.2]
  have hfd : DifferentiableAt ℝ f (e.symm (0,z)) := by
    rw [hinv]
    exact (hf.contDiffAt (e.open_source.mem_nhds hx.2)).differentiableAt (by simp)
  have hid := (hei.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hi : DifferentiableAt ℝ (fun w : X => e.symm (0,w)) z :=
    hid.comp z (((hasFDerivAt_const (0 : ℝ) z).prodMk (hasFDerivAt_id z)).differentiableAt)
  have hd : fderiv ℝ (fun w : X => f (e.symm (0,w))) z = 0 := by
    simpa only [Function.comp_def, hinv, (hzero x hx).2, ContinuousLinearMap.zero_comp] using
      (hfd.hasFDerivAt.comp z hi.hasFDerivAt).fderiv
  refine ⟨z, ⟨hz, ?_⟩, congrArg f hinv⟩
  rw [hd]
  intro hsurj
  obtain ⟨v,hv⟩ := exists_ne (0 : F)
  obtain ⟨w,hw⟩ := hsurj v
  exact hv (by simpa using hw.symm)

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem surjective_scalar_of_ne_zero {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    Function.Surjective L := by
  apply LinearMap.surjective_iff_ne_zero.mpr
  intro h
  apply hL
  ext x
  exact congrArg (fun L : E →ₗ[ℝ] ℝ => L x) h

private theorem finrank_ker_lt_of_ne_zero [FiniteDimensional ℝ E]
    {L : E →L[ℝ] ℝ} (hL : L ≠ 0) : Module.finrank ℝ L.ker < Module.finrank ℝ E := by
  have h := L.toLinearMap.finrank_range_add_finrank_ker
  have hr : L.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr (surjective_scalar_of_ne_zero hL)
  rw [hr, finrank_top, Module.finrank_self] at h
  omega

private theorem exists_target_coordinates {q : ℕ}
    {L : E →L[ℝ] EuclideanSpace ℝ (Fin (q + 1))} (hL : L ≠ 0) :
    ∃ T : EuclideanSpace ℝ (Fin (q + 1)) ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin q),
      MeasurePreserving T ∧ (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin q))).comp
        ((T : EuclideanSpace ℝ (Fin (q + 1)) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin q)).comp L) ≠ 0 := by
  classical
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hL
  have hw' : L w ≠ 0 := by simpa using hw
  obtain ⟨i,hi⟩ : ∃ i : Fin (q + 1), L w i ≠ 0 := by
    by_contra! h
    exact hw' (by ext i; exact h i)
  let P := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin (q + 1)) i)
  let T := P.toContinuousLinearEquiv.trans (splitEuclidean q)
  refine ⟨T, (volume_preserving_splitEuclidean q).comp P.measurePreserving, ?_⟩
  intro hz
  have heq := congrArg (fun A : E →L[ℝ] ℝ => A w) hz
  have hfirst : (T (L w)).1 = L w i := by
    change L w ((Equiv.swap (0 : Fin (q + 1)) i).symm 0) = L w i
    simp
  exact hi (hfirst.symm.trans heq)

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

private theorem surjective_fderiv_equiv_comp_iff
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : F ≃L[ℝ] X) {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) :
    Function.Surjective (fderiv ℝ (T ∘ f) x) ↔ Function.Surjective (fderiv ℝ f x) := by
  rw [fderiv_comp x T.differentiableAt hf, T.fderiv]
  change Function.Surjective (T ∘ fderiv ℝ f x) ↔ _
  constructor
  · intro h y
    obtain ⟨z,hz⟩ := h (T y)
    exact ⟨z,T.injective hz⟩
  · exact fun h => T.surjective.comp h

private theorem volume_image_stratum_eq_zero
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : 0 < n) {f : E → EuclideanSpace ℝ (Fin n)} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (j : ℕ)
    (ih : ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
      Module.finrank ℝ X < Module.finrank ℝ E →
      ∀ (g : X → EuclideanSpace ℝ (Fin n)) (V : Set X), IsOpen V → ContDiffOn ℝ ∞ g V →
        volume (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ iteratedFDeriv ℝ j f x = 0 ∧
      iteratedFDeriv ℝ (j + 1) f x ≠ 0}) = 0 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply image_null_of_locally_null volume
  intro x hx
  obtain ⟨h, hh, hzero, hL⟩ := exists_scalar_jet_detector hU hf hx.1 hx.2.2.2
  let L := fderiv ℝ h x
  obtain ⟨e,hxe,heU,he,hei,hefirst⟩ :=
    exists_contDiff_submersion_chart_of_hasFDerivAt (by simp) hh hU hx.1
      ((hh.contDiffAt (hU.mem_nhds hx.1)).differentiableAt (by simp)).hasFDerivAt
      (surjective_scalar_of_ne_zero hL) L.ker_closedComplemented_of_finiteDimensional_range
  let V : Set L.ker := {z | (0,z) ∈ e.target}
  have hV : IsOpen V := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have hins : ContDiffOn ℝ ∞ (fun z : L.ker => ((0 : ℝ), z)) V :=
    (ContinuousLinearMap.inr ℝ ℝ L.ker).contDiff.contDiffOn
  have hg : ContDiffOn ℝ ∞ (fun z : L.ker => f (e.symm (0,z))) V :=
    (hf.mono heU).comp (hei.comp hins fun _ hz => hz) (fun z hz => e.map_target hz)
  have hz := ih L.ker (finrank_ker_lt_of_ne_zero hL) _ V hV hg
  refine ⟨{y | y ∈ U ∧ fderiv ℝ f y = 0 ∧ iteratedFDeriv ℝ j f y = 0 ∧
      iteratedFDeriv ℝ (j + 1) f y ≠ 0} ∩ e.source,
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hxe)), ?_⟩
  apply measure_mono_null (image_hypersurface_subset_critical_image e (hf.mono heU) hei ?_) hz
  intro y hy
  exact ⟨(hefirst y).trans (hzero y hy.1.2.2.1), hy.1.2.1⟩

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

private theorem volume_image_nonzero_derivative_critical_eq_zero
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {q : ℕ} {f : E → EuclideanSpace ℝ (Fin (q + 1))} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (ih : ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
      Module.finrank ℝ X < Module.finrank ℝ E →
      ∀ (g : X → EuclideanSpace ℝ (Fin q)) (V : Set X), IsOpen V → ContDiffOn ℝ ∞ g V →
        volume (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x) ∧
      fderiv ℝ f x ≠ 0}) = 0 := by
  apply image_null_of_locally_null volume
  intro a ha
  obtain ⟨T,hT,hTnz⟩ := exists_target_coordinates ha.2.2
  let h : E → ℝ := fun x => (T (f x)).1
  have hh : ContDiffOn ℝ ∞ h U := (hf.continuousLinearMap_comp T.toContinuousLinearMap).fst
  have hfa := (hf.contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by simp)
  have hd : fderiv ℝ h a = (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin q))).comp
      (T.toContinuousLinearMap.comp (fderiv ℝ f a)) :=
    ((T.hasFDerivAt.comp a hfa.hasFDerivAt).fst).fderiv
  have hL : fderiv ℝ h a ≠ 0 := hd ▸ hTnz
  let L := fderiv ℝ h a
  obtain ⟨e,hae,heU,he,hei,hefirst⟩ :=
    exists_contDiff_submersion_chart_of_hasFDerivAt (by simp) hh hU ha.1
      ((hh.contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by simp)).hasFDerivAt
      (surjective_scalar_of_ne_zero hL) L.ker_closedComplemented_of_finiteDimensional_range
  let G : ℝ × L.ker → ℝ × EuclideanSpace ℝ (Fin q) := (T ∘ f) ∘ e.symm
  have hTf : ContDiffOn ℝ ∞ (T ∘ f) e.source :=
    (hf.mono heU).continuousLinearMap_comp T.toContinuousLinearMap
  have hG : ContDiffOn ℝ ∞ G e.target := hTf.comp hei (fun _ hz => e.map_target hz)
  have hfst : ∀ p ∈ e.target, (G p).1 = p.1 := by
    intro p hp
    change h (e.symm p) = p.1
    rw [← hefirst, e.right_inv hp]
  let S := G '' {p | p ∈ e.target ∧ ¬ Function.Surjective (fderiv ℝ G p)}
  have hS : MeasurableSet S := measurableSet_of_isSigmaCompact
    (critical_image_isSigmaCompact e.open_target hG)
  have hnull : volume S = 0 := by
    apply measure_prod_eq_zero_of_sections hS volume
    intro t
    change volume {y | (t,y) ∈ G '' {p | p ∈ e.target ∧
      ¬ Function.Surjective (fderiv ℝ G p)}} = 0
    rw [critical_image_slice_eq e.open_target hG hfst t]
    have hV : IsOpen {z : L.ker | (t,z) ∈ e.target} :=
      e.open_target.preimage (continuous_const.prodMk continuous_id)
    have hins : ContDiffOn ℝ ∞ (fun z : L.ker => (t,z)) {z | (t,z) ∈ e.target} :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    exact ih L.ker (finrank_ker_lt_of_ne_zero hL) _ _ hV
      (hG.snd.comp hins (fun _ hz => hz))
  refine ⟨{x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x) ∧ fderiv ℝ f x ≠ 0} ∩ e.source,
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hae)), ?_⟩
  apply measure_mono_null (t := T ⁻¹' S) ?_ (hT.preimage_null hnull)
  rintro y ⟨x,hx,rfl⟩
  refine ⟨e x, ⟨e.map_source hx.2, ?_⟩, ?_⟩
  · intro hs
    have hs' := (surjective_fderiv_comp_symm_iff e hTf he hei (e.map_source hx.2)).mp hs
    rw [e.left_inv hx.2] at hs'
    exact hx.1.2.1 ((surjective_fderiv_equiv_comp_iff T
      ((hf.contDiffAt (hU.mem_nhds hx.1.1)).differentiableAt (by simp))).mp hs')
  · change T (f (e.symm (e x))) = T (f x)
    rw [e.left_inv hx.2]

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

private theorem sard_euclidean (m : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      Module.finrank ℝ E = m →
      ∀ (n : ℕ) (f : E → EuclideanSpace ℝ (Fin n)) (U : Set E),
        IsOpen U → ContDiffOn ℝ ∞ f U →
          volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro E _ _ _ hm n f U hU hf
    cases n with
    | zero =>
      have hc : {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)} = (∅ : Set E) := by
        ext x
        constructor
        · intro hx
          exact (hx.2 (fun y => ⟨0, Subsingleton.elim _ _⟩)).elim
        · exact fun hx => False.elim hx
      rw [hc, image_empty, measure_empty]
    | succ q =>
      let P : Set E := {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x) ∧ fderiv ℝ f x ≠ 0}
      let Z : Set E := {x | x ∈ U ∧ ∀ i : ℕ, 1 ≤ i → i ≤ Module.finrank ℝ E →
        iteratedFDeriv ℝ i f x = 0}
      let A (j : ℕ) : Set E := {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧
        iteratedFDeriv ℝ j f x = 0 ∧ iteratedFDeriv ℝ (j + 1) f x ≠ 0}
      have hP : volume (f '' P) = 0 :=
        volume_image_nonzero_derivative_critical_eq_zero hU hf
          (fun X _ _ _ hX g V hV hg =>
            ih (Module.finrank ℝ X) (by simpa only [hm] using hX) X rfl q g V hV hg)
      have hZ : volume (f '' Z) = 0 := volume_image_flat_set_eq_zero (Nat.succ_pos q) hU hf
      have hA (j : ℕ) : volume (f '' A j) = 0 :=
        volume_image_stratum_eq_zero (Nat.succ_pos q) hU hf j
          (fun X _ _ _ hX g V hV hg =>
            ih (Module.finrank ℝ X) (by simpa only [hm] using hX) X rfl (q+1) g V hV hg)
      have hnull : volume (f '' ((P ∪ Z) ∪ ⋃ j : ℕ, A j)) = 0 := by
        rw [image_union, image_union, image_iUnion]
        exact measure_union_null (measure_union_null hP hZ) (measure_iUnion_null hA)
      apply measure_mono_null (image_mono ?_) hnull
      intro x hx
      by_cases hd : fderiv ℝ f x = 0
      · by_cases hu : x ∈ ⋃ j : ℕ, A j
        · exact Or.inr hu
        · apply Or.inl ∘ Or.inr
          refine ⟨hx.1, ?_⟩
          have hjets : ∀ j : ℕ, iteratedFDeriv ℝ (j + 1) f x = 0 := by
            intro j
            induction j with
            | zero =>
              change iteratedFDeriv ℝ 1 f x = 0
              apply norm_eq_zero.mp
              rw [norm_iteratedFDeriv_one, hd, norm_zero]
            | succ j hj =>
              by_contra hnext
              exact hu (mem_iUnion.mpr ⟨j+1, hx.1, hd, hj, hnext⟩)
          intro i hi _
          cases i with
          | zero => omega
          | succ j => exact hjets j
      · exact Or.inl (Or.inl ⟨hx.1, hx.2, hd⟩)

end DifferentialGeometry.Analysis

theorem ContDiffOn.sard
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {f : E → F} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  let T : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin])
  let : (Measure.map T μ).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  let G := T ∘ f
  have hG : ContDiffOn ℝ ∞ G U := hf.continuousLinearMap_comp T.toContinuousLinearMap
  have hnull := DifferentialGeometry.Analysis.sard_euclidean (Module.finrank ℝ E)
    E rfl (Module.finrank ℝ F) G U hU hG
  have hmapped := (Measure.absolutelyContinuous_isAddHaarMeasure (Measure.map T μ) volume) hnull
  have hTmeas : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  rw [hTmeas.map_apply] at hmapped
  apply measure_mono_null ?_ hmapped
  rintro y ⟨x,⟨hx,hc⟩,rfl⟩
  refine ⟨x,⟨hx,?_⟩,rfl⟩
  intro hs
  exact hc ((DifferentialGeometry.Analysis.surjective_fderiv_equiv_comp_iff T
    ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))).mp hs)
