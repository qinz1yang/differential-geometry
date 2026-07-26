import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpBoundK

/-!
# Exact tensor compatibility for chartwise `W^{2,p}` limits

The estimates in `ChartWkpBound.lean` use the globally smooth coefficient

`chartKernelCutoff α * chartKernelCutoff β * transitionCoeff β α`.

For reconstruction one must also prove that the two extra cutoff factors do
not change the partition-of-unity components.  This file records that exact
identity.  The target cutoff is absorbed by the target POU weight; the source
cutoff is absorbed either by the source POU weight of an actual section or by
the pointwise support theorem for `secCompRep`.

The two final statements are the exact identities used by completeness:

* `secCompDecomp` decomposes an arbitrary genuine tensor section into the
  finite sum of transported source-chart components;
* `secPullLimitEq` computes a target component of one reconstructed weak
  source-chart limit as the finite sum of its transported scalar limits.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- A target POU weight absorbs its chart-kernel cutoff pointwise. -/
theorem pouCutoffMul (α : M) (x : M) (v : ℝ) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
          M → ℝ) x * v) := by
  classical
  by_cases hρ : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hρ, zero_mul, zero_mul]
  · have hx_supp : x ∈ tsupport
        (fun y : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
      subset_tsupport _ hρ
    have hχ : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
        M → ℝ) x = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) α hx_supp
    rw [hχ, one_mul]

/-- Reading a POU-weighted component at the Euclidean coordinate of a source
point recovers the manifold-side POU component. -/
theorem secComp_coord
    (r s : ℕ) (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    secChartComp (I := I) (M := M) r s S α P.1 P.2
        (toEuclidean (E := E) (extChartAt I α x)) =
      secCompPou (I := I) (M := M) r s S α P.1 P.2 x := by
  rw [secComp_apply_mem (I := I) (M := M) r s S α P.1 P.2
    (toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) α hx)]
  rw [symm_toEuclidean_symm_toEuclidean_extChartAt
    (I := I) (M := M) α hx]

/-- The POU-weighted raw transition formula for an arbitrary genuine tensor
section.  This is the smooth-section lemma from the spectral construction with
the unnecessary smoothness hypothesis removed. -/
theorem pouRawTrans
    (r s : ℕ) (S : RSTensorSection I M r s) (β α : M)
    (P : TensorCompIdx (E := E) r s) {x : M}
    (hxα : x ∈ (chartAt H α).source) :
    ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        secCompRaw (I := I) (M := M) r s S α P.1 P.2 x =
      ∑ Q : TensorCompIdx (E := E) r s,
        ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
            M → ℝ) x *
          transitionCoeff (E := E) (I := I) (M := M) r s β α P Q x *
            secCompPou (I := I) (M := M) r s S β Q.1 Q.2 x := by
  classical
  by_cases hβ : ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hβ, zero_mul]
    refine (Finset.sum_eq_zero (fun Q _ => ?_)).symm
    unfold secCompPou
    rw [hβ]
    ring
  · have hx_supp : x ∈ tsupport
        (fun y : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
      subset_tsupport _ hβ
    have hxβ : x ∈ (chartAt H β).source :=
      chartAtlasPOU_isSubordinate I M β hx_supp
    have hχβ : ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
        M → ℝ) x = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) β hx_supp
    have hdecomp := secCompRaw_trans (E := E) (I := I) (M := M)
      r s S β α P ⟨hxβ, hxα⟩
    rw [hdecomp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    unfold secCompPou
    rw [hχβ]
    ring

/-- A pointwise-supported weak source component absorbs both cutoff factors of
the global transition coefficient after multiplication by the target POU
weight. -/
theorem repCoeffEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P Q : TensorCompIdx (E := E) r s) {v : EuclN → ℝ}
    (hv : tsupport v ⊆ chartImagePOUTsupport (I := I) (M := M) β)
    {x : M} (hxβ : x ∈ (chartAt H β).source) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (transitionCoeff (E := E) (I := I) (M := M) r s β α P Q x *
          v (toEuclidean (E := E) (extChartAt I β x))) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (transportCoeffManifold (I := I) (M := M) g r s β α P Q x *
          v (toEuclidean (E := E) (extChartAt I β x))) := by
  classical
  by_cases hρα : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hρα, zero_mul, zero_mul]
  by_cases hvx : v (toEuclidean (E := E) (extChartAt I β x)) = 0
  · rw [hvx, mul_zero, mul_zero]
  have hxα_supp : x ∈ tsupport
      (fun z : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) :=
    subset_tsupport _ hρα
  have hχα : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
      M → ℝ) x = 1 :=
    chartKernelCutoff_eqOn_one (I := I) (M := M) α hxα_supp
  have hy_supp := hv (subset_tsupport _ hvx)
  unfold chartImagePOUTsupport at hy_supp
  obtain ⟨z, hz, hzy⟩ := hy_supp
  obtain ⟨w, hw_supp, hwz⟩ := hz
  have hwβ : w ∈ (chartAt H β).source :=
    chartAtlasPOU_isSubordinate I M β hw_supp
  have hw_ext : w ∈ (extChartAt I β).source := by
    rw [extChartAt_source]
    exact hwβ
  have hx_ext : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source]
    exact hxβ
  have hcoord :
      toEuclidean (E := E) (extChartAt I β w) =
        toEuclidean (E := E) (extChartAt I β x) := by
    rw [hwz, hzy]
  have hext : extChartAt I β w = extChartAt I β x :=
    (toEuclidean (E := E)).injective hcoord
  have hwx : w = x := (extChartAt I β).injOn hw_ext hx_ext hext
  have hχβ : ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
      M → ℝ) x = 1 := by
    rw [← hwx]
    exact chartKernelCutoff_eqOn_one (I := I) (M := M) β hw_supp
  rw [transportCoeffManifold_apply, hχα, hχβ]
  ring

/-- One reconstructed weak source-chart model has exactly the transported
component formula in every target chart, modulo the chart-target measure. -/
theorem secPullLimitEq
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (β α : M) (P : TensorCompIdx (E := E) r s) :
    secChartComp (I := I) (M := M) r s
        (secModelPull (I := I) (M := M) r s β
          (secModelLimit (I := I) (M := M) g r s k hp hp_top u h_cauchy β))
        α P.1 P.2 =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => ∑ Q : TensorCompIdx (E := E) r s,
        secTransTerm (I := I) (M := M) g r s β α P Q
          (secCompRep (I := I) (M := M) g r s k hp hp_top u
            h_cauchy β Q.1 Q.2) y) := by
  classical
  have hmem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)),
      y ∈ chartTargetEuclid (I := I) (M := M) α :=
    ae_restrict_mem (chartTargetEuclid_measurableSet (I := I) (M := M) α)
  filter_upwards [hmem] with y hy
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hxα : x ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [secComp_apply_mem (I := I) (M := M) r s _ α P.1 P.2 hy]
  unfold secCompPou
  by_cases hxβ : x ∈ (chartAt H β).source
  · rw [secPull_raw_trans (E := E) (I := I) (M := M) r s β α
      (secModelLimit (I := I) (M := M) g r s k hp hp_top u h_cauchy β)
      P ⟨hxβ, hxα⟩, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro Q _
    rw [secModelLimit_proj (I := I) (M := M) g r s k hp hp_top u
      h_cauchy β (toEuclidean (E := E) (extChartAt I β x)) Q.1 Q.2]
    unfold secTransTerm chartPushed
    rw [chartPullback_apply_of_mem (I := I) (M := M) β _ hxβ,
      transCoeffE_apply (I := I) (M := M) g r s β α P Q hxβ]
    exact repCoeffEq (I := I) (M := M) g r s β α P Q
      (secCompRep_support (I := I) (M := M) g r s k hp hp_top u
        h_cauchy β Q.1 Q.2) hxβ
  · have hpull : secModelPull (I := I) (M := M) r s β
        (secModelLimit (I := I) (M := M) g r s k hp hp_top u h_cauchy β) x = 0 := by
      unfold secModelPull
      rw [dif_neg hxβ]
    unfold secCompRaw secTriv
    rw [hpull, map_zero, map_zero, mul_zero]
    refine (Finset.sum_eq_zero (fun Q _ => ?_)).symm
    unfold secTransTerm chartPushed
    rw [chartPullback_apply_of_notMem (I := I) (M := M) β _ hxβ, mul_zero]

/-- Every component of an arbitrary genuine tensor section is the finite sum
of the transported POU components from the canonical active chart set. -/
theorem secCompDecomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    secChartComp (I := I) (M := M) r s S α P.1 P.2 =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Q : TensorCompIdx (E := E) r s,
          secTransTerm (I := I) (M := M) g r s β α P Q
            (secChartComp (I := I) (M := M) r s S β Q.1 Q.2) y) := by
  classical
  have hmem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)),
      y ∈ chartTargetEuclid (I := I) (M := M) α :=
    ae_restrict_mem (chartTargetEuclid_measurableSet (I := I) (M := M) α)
  filter_upwards [hmem] with y hy
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hxα : x ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [secComp_apply_mem (I := I) (M := M) r s S α P.1 P.2 hy]
  unfold secCompPou
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  calc
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        secCompRaw (I := I) (M := M) r s S α P.1 P.2 x =
      (∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) *
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          secCompRaw (I := I) (M := M) r s S α P.1 P.2 x) := by
      rw [hsum, one_mul]
    _ = ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          (((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            secCompRaw (I := I) (M := M) r s S α P.1 P.2 x) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun β _ => by ring)
    _ = ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Q : TensorCompIdx (E := E) r s,
          secTransTerm (I := I) (M := M) g r s β α P Q
            (secChartComp (I := I) (M := M) r s S β Q.1 Q.2) y := by
      refine Finset.sum_congr rfl ?_
      intro β _
      by_cases hxβ : x ∈ (chartAt H β).source
      · rw [pouRawTrans (E := E) (I := I) (M := M) r s S β α P hxα,
          Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro Q _
        unfold secTransTerm chartPushed
        rw [chartPullback_apply_of_mem (I := I) (M := M) β _ hxβ,
          transCoeffE_apply (I := I) (M := M) g r s β α P Q hxβ,
          secComp_coord (I := I) (M := M) r s S β Q hxβ,
          transportCoeffManifold_apply]
        have hcut := pouCutoffMul (I := I) (M := M) α x
          (((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
              M → ℝ) x *
            transitionCoeff (E := E) (I := I) (M := M) r s β α P Q x *
              secCompPou (I := I) (M := M) r s S β Q.1 Q.2 x)
        calc
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
              (((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
                  M → ℝ) x *
                transitionCoeff (E := E) (I := I) (M := M) r s β α P Q x *
                  secCompPou (I := I) (M := M) r s S β Q.1 Q.2 x) =
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
              (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
                  M → ℝ) x *
                (((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
                    M → ℝ) x *
                  transitionCoeff (E := E) (I := I) (M := M) r s β α P Q x *
                    secCompPou (I := I) (M := M) r s S β Q.1 Q.2 x)) := hcut
          _ = ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
              ((((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
                    M → ℝ) x *
                  ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
                    M → ℝ) x *
                  transitionCoeff (E := E) (I := I) (M := M) r s β α P Q x) *
                secCompPou (I := I) (M := M) r s S β Q.1 Q.2 x) := by ring
      · have hρβ : ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := by
          by_contra hne
          exact hxβ (chartAtlasPOU_isSubordinate I M β (subset_tsupport _ hne))
        rw [hρβ, zero_mul, mul_zero]
        refine (Finset.sum_eq_zero (fun Q _ => ?_)).symm
        unfold secTransTerm chartPushed
        rw [chartPullback_apply_of_notMem (I := I) (M := M) β _ hxβ, mul_zero]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
