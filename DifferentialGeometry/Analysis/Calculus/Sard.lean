import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.HausdorffDimension
import DifferentialGeometry.Analysis.Integration.Measure.HausdorffDimension

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
