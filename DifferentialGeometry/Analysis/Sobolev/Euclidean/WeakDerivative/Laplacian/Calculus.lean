import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence.Local
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Laplacian
import DifferentialGeometry.Analysis.Sobolev.Tools.DiffQuotLocal
import DifferentialGeometry.Analysis.Integration.Lp.Cutoff
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.DirectionalJets
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_laplacian_mul_cutoff_eq_of_hasWeakDiv
    {Ω : Set E} (hΩ : IsOpen Ω) {u f η : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hdiv : DeGiorgi.HasWeakDiv f hu.weakGrad Ω)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, Laplacian.laplacian φ x * (η x * u x)) =
      ∫ x, φ x * (η x * f x + 2 * (∑ j,
        fderiv ℝ η x (EuclideanSpace.single j 1) * hu.weakGrad x j) +
          Laplacian.laplacian η x * u x) := by
  let D (j : Fin d) (x : E) := fderiv ℝ η x (EuclideanSpace.single j 1)
  let DD (j : Fin d) (x : E) := fderiv ℝ (D j) x (EuclideanSpace.single j 1)
  have hD (j : Fin d) : ContDiff ℝ ∞ (D j) :=
    (hη.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc (j : Fin d) : HasCompactSupport (D j) := hηc.fderiv_apply ℝ _
  have hDs (j : Fin d) : tsupport (D j) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ _).trans hηs
  have hDD (j : Fin d) : Continuous (DD j) :=
    ((hD j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hDDc (j : Fin d) : HasCompactSupport (DD j) := (hDc j).fderiv_apply ℝ _
  have hDDs (j : Fin d) : tsupport (DD j) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ _).trans (hDs j)
  have hmul {a b : E → ℝ} (hb : MemLp b 2 (volume.restrict Ω))
      (ha : Continuous a) (hac : HasCompactSupport a) (has : tsupport a ⊆ Ω) :
      MemLp (fun x => a x * b x) 2 (volume.restrict univ) := by
    simpa only [Measure.restrict_univ, smul_eq_mul] using
      hb.continuous_smul_of_tsupport_subset hΩ.measurableSet ha hac has
  let P (x : E) : E := η x • hu.weakGrad x
  let Q (x : E) : E := WithLp.toLp 2 fun j => D j x * u x
  let A (x : E) := η x * f x + ∑ j, D j x * hu.weakGrad x j
  let B (x : E) := ∑ j, (D j x * hu.weakGrad x j + DD j x * u x)
  let H (x : E) : E := WithLp.toLp 2 fun j => D j x * hu.weakGrad x j + DD j x * u x
  have hP (j : Fin d) : MemLp (fun x => P x j) 2 (volume.restrict univ) :=
    hmul (hu.weakGrad_component_memLp j) hη.continuous hηc hηs
  have hQ (j : Fin d) : MemLp (fun x => Q x j) 2 (volume.restrict univ) :=
    hmul hu.memLp (hD j).continuous (hDc j) (hDs j)
  have hH (j : Fin d) : MemLp (fun x => H x j) 2 (volume.restrict univ) :=
    (hmul (hu.weakGrad_component_memLp j) (hD j).continuous (hDc j) (hDs j)).add
      (hmul hu.memLp (hDD j) (hDDc j) (hDDs j))
  have hA : MemLp A 2 (volume.restrict univ) :=
    (hmul hf hη.continuous hηc hηs).add
      (memLp_finsetSum _ fun j _ =>
        hmul (hu.weakGrad_component_memLp j) (hD j).continuous (hDc j) (hDs j))
  have hB : MemLp B 2 (volume.restrict univ) := memLp_finsetSum _ fun j _ => hH j
  have hdivP : DeGiorgi.HasWeakDiv A P univ :=
    hdiv.mul_cutoff_univ (fun j => (hu.weakGrad_component_memLp j).locallyIntegrable (by norm_num))
      (hf.locallyIntegrable (by norm_num)) hη hηc hηs
  have hparts (j : Fin d) : DeGiorgi.HasWeakPartialDeriv j (fun x => H x j) (fun x => Q x j) univ :=
    hasWeakPartialDeriv_mul_cutoff_univ hΩ hu.memLp (hu.weakGrad_component_memLp j) j
      (hu.isWeakGrad j) (hD j) (hDc j) (hDs j)
  have hdivQ : DeGiorgi.HasWeakDiv B Q univ :=
    DeGiorgi.hasWeakDiv_of_hasWeakPartialDeriv
      (fun j => (hQ j).locallyIntegrable (by norm_num))
      (fun j => (hH j).locallyIntegrable (by norm_num)) hparts
  have hdivPQ := hdivP.add hdivQ
    (fun j => (hP j).locallyIntegrable (by norm_num))
    (fun j => (hQ j).locallyIntegrable (by norm_num))
    (hA.locallyIntegrable (by norm_num)) (hB.locallyIntegrable (by norm_num))
  have hgrad : DeGiorgi.HasWeakGrad (P + Q) (fun x => η x * u x) univ := by
    intro j
    exact hasWeakPartialDeriv_mul_cutoff_univ hΩ hu.memLp (hu.weakGrad_component_memLp j) j
      (hu.isWeakGrad j) hη hηc hηs
  have hmain := integral_mul_laplacian_eq_of_hasWeakDiv
    ((hmul hu.memLp hη.continuous hηc hηs).locallyIntegrable (by norm_num))
    (fun j => ((hP j).add (hQ j)).locallyIntegrable (by norm_num)) hgrad hdivPQ
    (show DeGiorgi.IsSmoothTestOn univ φ from ⟨hφ, hφc, subset_univ _⟩)
  simp only [Measure.restrict_univ] at hmain
  have hrhs (x : E) : (A + B) x = η x * f x + 2 * (∑ j, D j x * hu.weakGrad x j) +
      Laplacian.laplacian η x * u x := by
    rw [laplacian_eq_sum_euclidean_fderiv (hη.contDiffAt.of_le (by norm_cast)), Finset.sum_mul]
    simp only [Pi.add_apply, A, B, Finset.sum_add_distrib, DD, D]
    ring
  calc
    _ = ∫ x, (η x * u x) * Laplacian.laplacian φ x :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    _ = ∫ x, (A + B) x * φ x := hmain
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
      change (A + B) x * φ x = _
      rw [hrhs x]
      ring)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem hasWeakDiv_partial_of_contDiffOn
    {Ω : Set V} (hΩ : IsOpen Ω) {u f : V → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hdiv : DeGiorgi.HasWeakDiv f (DeGiorgi.smoothGradField u) Ω) (l : Fin d) :
    DeGiorgi.HasWeakDiv (fun x => fderiv ℝ f x (EuclideanSpace.single l 1))
      (DeGiorgi.smoothGradField (fun x => fderiv ℝ u x (EuclideanSpace.single l 1))) Ω := by
  let D (j : Fin d) (x : V) := fderiv ℝ u x (EuclideanSpace.single j 1)
  have hD (j : Fin d) : ContDiffOn ℝ 1 (D j) Ω :=
    (hu.fderiv_of_isOpen (m := 1) hΩ (by norm_num)).clm_apply contDiffOn_const
  let G (x : V) : V := WithLp.toLp 2 fun j => fderiv ℝ (D j) x (EuclideanSpace.single l 1)
  have hparts (j : Fin d) : DeGiorgi.HasWeakPartialDeriv l (fun x => G x j)
      (fun x => DeGiorgi.smoothGradField u x j) Ω :=
    hasWeakPartialDeriv_of_contDiffOn hΩ (hD j) l
  have hF (j : Fin d) : LocallyIntegrableOn (fun x => DeGiorgi.smoothGradField u x j) Ω volume :=
    (hD j).continuousOn.locallyIntegrableOn hΩ.measurableSet
  have hG (j : Fin d) : LocallyIntegrableOn (fun x => G x j) Ω volume := by
    have hc := ((hD j).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
      (continuousOn_const (c := EuclideanSpace.single l 1))
    exact hc.locallyIntegrableOn hΩ.measurableSet
  have hh := hdiv.comm_of_locallyIntegrableOn (hasWeakPartialDeriv_of_contDiffOn hΩ hf l)
    hparts hF hG
  apply hh.congr_ae EventuallyEq.rfl
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  ext j
  change fderiv ℝ (D j) x (EuclideanSpace.single l 1) =
    fderiv ℝ (D l) x (EuclideanSpace.single j 1)
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  simp only [D, fderiv_clm_apply hdu (differentiableAt_const _), fderiv_const_apply,
    add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hu.contDiffAt (hΩ.mem_nhds hx)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField])
    (EuclideanSpace.single l 1) (EuclideanSpace.single j 1)

theorem hasWeakDiv_iteratedFDeriv_apply_of_contDiffOn
    {Ω : Set V} (hΩ : IsOpen Ω) {u f : V → ℝ} {N : ℕ}
    (hu : ContDiffOn ℝ (N + 1 : ℕ) u Ω) (hf : ContDiffOn ℝ N f Ω)
    (hdiv : DeGiorgi.HasWeakDiv f (DeGiorgi.smoothGradField u) Ω)
    (v : Fin N → Fin d) :
    DeGiorgi.HasWeakDiv (fun x => iteratedFDeriv ℝ N f x
      (fun i => EuclideanSpace.single (v i) 1))
      (DeGiorgi.smoothGradField (fun x => iteratedFDeriv ℝ N u x
        (fun i => EuclideanSpace.single (v i) 1))) Ω := by
  induction N generalizing u f with
  | zero => simpa only [iteratedFDeriv_zero_apply] using hdiv
  | succ N ih =>
      let Du (x : V) := fderiv ℝ u x (EuclideanSpace.single (v 0) 1)
      let Df (x : V) := fderiv ℝ f x (EuclideanSpace.single (v 0) 1)
      have hu2 : ContDiffOn ℝ 2 u Ω := hu.of_le (by exact_mod_cast (by omega : 2 ≤ N + 1 + 1))
      have hf1 : ContDiffOn ℝ 1 f Ω := hf.of_le (by exact_mod_cast (by omega : 1 ≤ N + 1))
      have hDu : ContDiffOn ℝ (N + 1 : ℕ) Du Ω :=
        (hu.fderiv_of_isOpen (m := (N + 1 : ℕ)) hΩ (by norm_cast)).clm_apply contDiffOn_const
      have hDf : ContDiffOn ℝ N Df Ω :=
        (hf.fderiv_of_isOpen (m := (N : ℕ)) hΩ (by norm_cast)).clm_apply contDiffOn_const
      have hdivD : DeGiorgi.HasWeakDiv Df (DeGiorgi.smoothGradField Du) Ω :=
        hasWeakDiv_partial_of_contDiffOn hΩ hu2 hf1 hdiv (v 0)
      have hInd := ih hDu hDf hdivD (Fin.tail v)
      have hequ : EqOn (fun x => iteratedFDeriv ℝ N Du x
          (fun i => EuclideanSpace.single (Fin.tail v i) 1))
          (fun x => iteratedFDeriv ℝ (N + 1) u x
            (fun i => EuclideanSpace.single (v i) 1)) Ω := by
        intro x hx
        have huc : ContDiffAt ℝ (N + 1) u x :=
          (hu.contDiffAt (hΩ.mem_nhds hx)).of_le (by norm_cast; omega)
        dsimp only [Du]
        rw [← huc.fderiv_iteratedFDeriv_apply (EuclideanSpace.single (v 0) 1)]
        exact (iteratedFDeriv_succ_apply_left (fun i => EuclideanSpace.single (v i) 1)).symm
      have heqf : EqOn (fun x => iteratedFDeriv ℝ N Df x
          (fun i => EuclideanSpace.single (Fin.tail v i) 1))
          (fun x => iteratedFDeriv ℝ (N + 1) f x
            (fun i => EuclideanSpace.single (v i) 1)) Ω := by
        intro x hx
        dsimp only [Df]
        rw [← (hf.contDiffAt (hΩ.mem_nhds hx)).fderiv_iteratedFDeriv_apply
          (EuclideanSpace.single (v 0) 1)]
        exact (iteratedFDeriv_succ_apply_left (fun i => EuclideanSpace.single (v i) 1)).symm
      apply hInd.congr_ae
      · exact (ae_restrict_mem hΩ.measurableSet).mono fun x hx => heqf hx
      · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
        have hgerm : (fun x => iteratedFDeriv ℝ N Du x
            (fun i => EuclideanSpace.single (Fin.tail v i) 1)) =ᶠ[𝓝 x]
            (fun x => iteratedFDeriv ℝ (N + 1) u x
              (fun i => EuclideanSpace.single (v i) 1)) := by
          filter_upwards [hΩ.mem_nhds hx] with y hy
          exact hequ hy
        ext j
        exact congrArg (fun L : V →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) hgerm.fderiv_eq

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
