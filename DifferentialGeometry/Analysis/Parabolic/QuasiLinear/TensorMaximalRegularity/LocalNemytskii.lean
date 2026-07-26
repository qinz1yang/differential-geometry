import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ForcingFixedPoint
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzExistence

/-!
# Nemytskii operators on an almost-everywhere state set

Maximal regularity controls a critical quasilinear solution in a lower
Sobolev norm uniformly in time, while retaining only an `L²` bound in the top
Sobolev norm.  Thus a geometric nonlinearity may be defined and Lipschitz only
on a closed lower-norm state set, even though its arguments are top-norm
fields.  This file packages the measure-theoretic construction needed in that
situation without extending the nonlinearity outside its genuine state set.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {T : ℝ}

/-- Lift a time field to a state-set subtype, using the zero state off the
set.  The exceptional branch is irrelevant whenever the field lies in the
state set almost everywhere. -/
def aeSetLift {S : Set X} (hzero : (0 : X) ∈ S) (f : timeL2 X T) : ℝ → S :=
  by
    classical
    exact fun t => if ht : f t ∈ S then ⟨f t, ht⟩ else ⟨0, hzero⟩

/-- The subtype lift has the original field as its coercion almost
everywhere. -/
theorem aeSetLift_coe_ae {S : Set X} (hzero : (0 : X) ∈ S)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    (fun t => ((aeSetLift hzero f t : S) : X)) =ᵐ[timeMeasure T] fun t => f t := by
  filter_upwards [hf] with t ht
  simp only [aeSetLift, dif_pos ht]

/-- The subtype lift is almost-everywhere strongly measurable. -/
theorem aeSetLift_aesm {S : Set X} (hzero : (0 : X) ∈ S)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    AEStronglyMeasurable (aeSetLift hzero f) (timeMeasure T) := by
  apply (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).mp
  exact (Lp.aestronglyMeasurable f).congr
    (aeSetLift_coe_ae hzero f hf).symm

omit [InnerProductSpace ℝ Y] [CompleteSpace Y] in
/-- A Lipschitz map on a state-set subtype sends every top-norm time field
which remains in that state set almost everywhere to an `L²` field. -/
theorem memLp_on {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    MemLp (fun t => N (aeSetLift hzero f t)) 2 (timeMeasure T) := by
  let z : S := ⟨0, hzero⟩
  have hlift := aeSetLift_aesm hzero f hf
  have hshiftMeas : AEStronglyMeasurable
      (fun t => N (aeSetLift hzero f t) - N z) (timeMeasure T) :=
    (hN.continuous.comp_aestronglyMeasurable hlift).sub
      aestronglyMeasurable_const
  have hshift : MemLp (fun t => N (aeSetLift hzero f t) - N z) 2
      (timeMeasure T) := by
    refine (Lp.memLp f).of_le_mul (c := (L : ℝ)) hshiftMeas ?_
    filter_upwards [hf] with t ht
    have hdist := hN.dist_le_mul (aeSetLift hzero f t) z
    rw [dist_eq_norm] at hdist
    simpa only [aeSetLift, dif_pos ht, z, Subtype.dist_eq, dist_zero_right] using hdist
  have hconst : MemLp (fun _ : ℝ => N z) 2 (timeMeasure T) :=
    memLp_const (N z)
  have hsum := hshift.add hconst
  have hfun : (fun t => N (aeSetLift hzero f t)) =
      fun t => (N (aeSetLift hzero f t) - N z) + N z := by
    funext t
    abel
  rw [hfun]
  exact hsum

/-- The pointwise Nemytskii field associated to a Lipschitz nonlinearity on
an almost-everywhere state set. -/
def nemytskiiOn {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    timeL2 Y T :=
  (memLp_on hzero hN f hf).toLp (fun t => N (aeSetLift hzero f t))

/-- `nemytskiiOn` is represented by the partial nonlinearity evaluated on
the canonical subtype lift. -/
theorem nemytskiiOn_coeFn {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    nemytskiiOn hzero hN f hf =ᵐ[timeMeasure T]
      fun t => N (aeSetLift hzero f t) :=
  (memLp_on hzero hN f hf).coeFn_toLp

/-- The Nemytskii field of the zero time field is the constant state-set
value `N 0`, hence has the sharp finite-slab `L²` bound. -/
theorem nemytskiiOn_zero_le {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hf : ∀ᵐ t ∂(timeMeasure T), ((0 : timeL2 X T) t) ∈ S) :
    ‖nemytskiiOn hzero hN (0 : timeL2 X T) hf‖ ≤
      Real.sqrt T * ‖N ⟨0, hzero⟩‖ := by
  refine timeL2_norm_le_of_ae_bound _ (norm_nonneg _) ?_
  have hcoe := nemytskiiOn_coeFn hzero hN (0 : timeL2 X T) hf
  have hzeroFn := Lp.coeFn_zero (E := X) (p := 2) (μ := timeMeasure T)
  filter_upwards [hcoe, hzeroFn, hf] with t ht htz hmem
  rw [ht]
  simp only [aeSetLift, dif_pos hmem]
  have hval : ((0 : timeL2 X T) t) = (0 : X) := by
    simpa only [Pi.zero_apply] using htz
  have hsub : (⟨(0 : timeL2 X T) t, hmem⟩ : S) = ⟨0, hzero⟩ :=
    Subtype.ext hval
  rw [hsub]

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
