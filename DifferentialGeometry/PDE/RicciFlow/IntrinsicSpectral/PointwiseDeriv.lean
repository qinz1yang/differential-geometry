import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Bridge from a maximally-regular `L²`-time-derivative to a pointwise
right-derivative on `[0, T)`.**

The signature now carries genuine maximal-regularity data: an element
`u : timeH1 X T` (the carrier of `MaxRegSolutionSpace`) together with a
continuous representative `g : ℝ → X` of its `L²`-time-derivative
(`hrep : u.deriv =ᵐ[timeMeasure T] g`). Under these hypotheses the
represented function `u.toFun` has pointwise right derivative `g t` at every
`t ∈ Set.Ico 0 T`, taken within the half-line `Set.Ici 0` (the D.3-corrected
boundary-aware form replacing the earlier `HasDerivAt`).

The link between the data `u` and the derivative `g t` is exactly
`TimeH1.hasDerivWithinAt_toFun_of_continuousOn`, which gives the
`Icc 0 T`-relative form; the conclusion `HasDerivWithinAt _ _ (Set.Ici 0) t`
follows because `Icc 0 T` and `Ici 0` agree on a neighborhood of any
`t ∈ Ico 0 T` (use `t < T` to find an open interval `Ioo (t − ε) T` on which
both sets coincide with `Ici 0 ∩ Iio T`).

**Missing prerequisite for the substantive proof:** the elementary local
neighborhood-equality lemma

  for `t ∈ Set.Ico (0 : ℝ) T`, `Icc 0 T ∩ Ioo (t − 1) T = Ici 0 ∩ Ioo (t − 1) T`,

together with `HasDerivWithinAt.congr_set` /
`HasDerivWithinAt.mono_of_mem_nhdsWithin` to transport the `Icc 0 T`-relative
derivative across the set change. The body is left as `sorry` pending the
formalisation of this neighborhood-equality + transport, which depends on
fixing the exact Mathlib API name for the set-change congruence
(`nhdsWithin_eq_nhdsWithin'` vs `nhdsWithin_inter_of_mem'`). -/
theorem maxreg_l2deriv_to_pointwise_hasderivwithinat
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {T : ℝ} (u : timeH1 X T) {g : ℝ → X}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) T))
    (hrep : u.deriv =ᵐ[timeMeasure T] g) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt u.toFun (g t) (Set.Ici (0 : ℝ)) t := by
  intro t ht
  have ht_icc : t ∈ Set.Icc (0 : ℝ) T :=
    ⟨ht.1, le_of_lt ht.2⟩
  have hderivIcc : HasDerivWithinAt u.toFun (g t) (Set.Icc (0 : ℝ) T) t :=
    u.hasDerivWithinAt_toFun_of_continuousOn hg hrep ht_icc
  have hIic : Set.Iic T ∈ nhds t := Iic_mem_nhds ht.2
  have hmem : Set.Icc (0 : ℝ) T ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
    have : Set.Ici (0 : ℝ) ∩ Set.Iic T ∈ nhdsWithin t (Set.Ici (0 : ℝ)) :=
      inter_mem_nhdsWithin _ hIic
    simpa [Set.Ici_inter_Iic] using this
  exact hderivIcc.mono_of_mem_nhdsWithin hmem

theorem hasDerivAt_clm_apply_from_h1_time
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : ℝ → X →L[ℝ] Y) (L' : ℝ → X →L[ℝ] Y) (u : ℝ → X) (u' : ℝ → X)
    (t : ℝ) (_x : X)
    (hL : HasDerivAt L (L' t) t) (hu : HasDerivAt u (u' t) t) :
    HasDerivAt (fun s : ℝ => L s (u s)) (L' t (u t) + L t (u' t)) t :=
  hL.clm_apply hu

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
