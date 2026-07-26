import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Volume
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.ScalarWeak
import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Family
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Conjugate heat equation along Ricci flow

This file begins the analytic producer chain used by Perelman's entropy proof.
Its first endpoint is conservation of the total mass of a smooth solution of
the conjugate heat equation under the moving Riemannian volume measure.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.Evolution.Volume
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-! ## Reversing the terminal-value equation -/

/-- The realized metric family obtained by reading `G` backwards from time
`T`.  Forward time `s` for this family corresponds to original time `T - s`. -/
def reverseFamily
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (T : Real) :
    DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real where
  metric := fun s => G.metric (T - s)
  connection := fun s => G.connection (T - s)
  metricCompatible := fun s => G.metricCompatible (T - s)

@[simp] theorem reverse_metric
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (T s : Real) :
    (reverseFamily G T).metric s = G.metric (T - s) := by
  rfl

/-- Translate a reversed heat-potential solution by a positive-time offset.

The new reverse time `r` reads the old solution at `r - a`; simultaneously
moving the terminal anchor from `T` to `T + a` leaves the underlying original
metric time unchanged. -/
theorem heat_pot_add
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (V u : Real → M → Real) (T a : Real)
    (h : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D
      (reverseFamily G T) V u) :
    DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (D.timeShift (-a)) (reverseFamily G (T + a))
      (fun r x => V (r - a) x) (fun r x => u (r - a) x) := by
  refine
    { jointSmooth := ?_
      jointCont := ?_
      sliceSmooth := ?_
      equation := ?_ }
  · have hmap :
        ContMDiff ((modelWithCornersSelf Real Real).prod I)
          ((modelWithCornersSelf Real Real).prod I) ∞
          (fun p : Real × M => (p.1 - a, p.2)) :=
      (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
    have hmaps :
        Set.MapsTo (fun p : Real × M => (p.1 - a, p.2))
          ((D.timeShift (-a)).regular ×ˢ (Set.univ : Set M))
          (D.regular ×ˢ (Set.univ : Set M)) := by
      intro p hp
      exact ⟨by simpa [sub_eq_add_neg] using hp.1, hp.2⟩
    simpa only [Function.comp_apply] using
      h.jointSmooth.comp hmap.contMDiffOn hmaps
  · have hmap : Continuous (fun p : Real × M => (p.1 - a, p.2)) :=
      (continuous_fst.sub continuous_const).prodMk continuous_snd
    have hmaps :
        Set.MapsTo (fun p : Real × M => (p.1 - a, p.2))
          ((D.timeShift (-a)).carrier ×ˢ (Set.univ : Set M))
          (D.carrier ×ˢ (Set.univ : Set M)) := by
      intro p hp
      exact ⟨by simpa [sub_eq_add_neg] using hp.1, hp.2⟩
    simpa only [Function.comp_apply] using
      h.jointCont.comp hmap.continuousOn hmaps
  · intro r hr
    exact h.sliceSmooth (r - a) (by simpa [sub_eq_add_neg] using hr)
  · intro r hr x
    have hr' : r - a ∈ D.regular := by
      simpa [sub_eq_add_neg] using hr
    have heq := h.equation (r - a) hr' x
    have hshift : HasDerivAt (fun s : Real => s - a) 1 r := by
      simpa using (hasDerivAt_id (x := r)).sub_const a
    have hcomp := heq.comp r hshift
    have htime : T - (r - a) = T + a - r := by ring
    have hcomp' :
        HasDerivAt (fun s : Real => u (s - a) x)
          (DifferentialGeometry.Integral.Connection.laplacianAt
              (I := I) (reverseFamily G T) (r - a) (u (r - a)) x +
            V (r - a) x * u (r - a) x) r := by
      simpa only [Function.comp_apply, mul_one] using hcomp
    convert hcomp' using 1
    all_goals
      simp only [reverseFamily,
        DifferentialGeometry.Integral.Connection.laplacianAt, htime]

/-- Read a spacetime scalar field backwards from terminal time `T`. -/
def reverseHeat (T : Real) (u : Real → M → Real) : Real → M → Real :=
  fun s x => u (T - s) x

@[simp] theorem reverse_heat_apply
    (T : Real) (u : Real → M → Real) (s : Real) (x : M) :
    reverseHeat T u s x = u (T - s) x := by
  rfl

/-- Time reversal changes the sign of the pointwise time derivative. -/
theorem reverse_deriv
    (T : Real) (u : Real → M → Real) (s : Real) (x : M)
    (hu : DifferentiableAt Real (fun t : Real => u t x) (T - s)) :
    deriv (fun r : Real => reverseHeat T u r x) s =
      -deriv (fun t : Real => u t x) (T - s) := by
  have hsub : HasDerivAt (fun r : Real => T - r) (-1) s := by
    simpa using
      (hasDerivAt_const (x := s) (c := T)).sub (hasDerivAt_id (x := s))
  have hcomp := hu.hasDerivAt.comp s hsub
  simpa [reverseHeat] using hcomp.deriv

/-- A backward conjugate-heat equation becomes a forward heat equation with
reaction coefficient `-scalar` after reversing time. -/
theorem conj_heat_forward
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) (T s : Real) (x : M)
    (hu : DifferentiableAt Real (fun t : Real => u t x) (T - s))
    (hconj : deriv (fun t : Real => u t x) (T - s) =
      -DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) G (T - s) (u (T - s)) x +
        scalar (T - s) x * u (T - s) x) :
    deriv (fun r : Real => reverseHeat T u r x) s =
      DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) (reverseFamily G T) s (reverseHeat T u s) x -
        scalar (T - s) x * reverseHeat T u s x := by
  rw [reverse_deriv T u s x hu, hconj]
  change
    -(-DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) G (T - s) (u (T - s)) x +
        scalar (T - s) x * u (T - s) x) =
      DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) G (T - s) (u (T - s)) x -
        scalar (T - s) x * u (T - s) x
  ring

/-- A forward solution for the reversed metric family pulls back to a backward
conjugate-heat solution for the original family. -/
theorem conj_heat_backward
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (scalar v : Real → M → Real) (T t : Real) (x : M)
    (hv : DifferentiableAt Real (fun s : Real => v s x) (T - t))
    (hforward : deriv (fun s : Real => v s x) (T - t) =
      DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) (reverseFamily G T) (T - t) (v (T - t)) x -
        scalar t x * v (T - t) x) :
    deriv (fun s : Real => reverseHeat T v s x) t =
      -DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) G t (reverseHeat T v t) x +
        scalar t x * reverseHeat T v t x := by
  rw [reverse_deriv T v t x hv, hforward]
  change
    -(DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) G (T - (T - t)) (v (T - t)) x -
        scalar t x * v (T - t) x) =
      -DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) G t (v (T - t)) x + scalar t x * v (T - t) x
  rw [show T - (T - t) = t by ring]
  ring

/-- Reversing a field twice around the same terminal time recovers it. -/
@[simp] theorem reverse_heat_reverse
    (T : Real) (u : Real → M → Real) :
    reverseHeat T (reverseHeat T u) = u := by
  funext s x
  change u (T - (T - s)) x = u s x
  rw [show T - (T - s) = s by ring]

/-- The interval-local conjugate-heat predicate, expressed as the genuine
forward heat-potential problem after reversing from terminal time `T`. -/
def IsConjHeatOn
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) (T : Real) : Prop :=
  DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D (reverseFamily G T)
    (fun s x => -scalar (T - s) x) (reverseHeat T u)

/-- A forward heat-potential solution for the reversed metric gives the
corresponding interval-local conjugate-heat solution. -/
theorem conj_heat_of_pot
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (scalar v : Real → M → Real) (T : Real)
    (h : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D
      (reverseFamily G T) (fun s x => -scalar (T - s) x) v) :
    IsConjHeatOn D G scalar (reverseHeat T v) T := by
  simpa only [IsConjHeatOn, reverse_heat_reverse] using h

/-- The heat-potential equation on the reversed family yields the original
backward conjugate-heat equation at each reflected regular time. -/
theorem heat_pot_to_conj
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (scalar v : Real → M → Real) (T t : Real)
    (h : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D
      (reverseFamily G T) (fun s x => -scalar (T - s) x) v)
    (ht : T - t ∈ D.regular) (x : M) :
    HasDerivAt (fun s : Real => reverseHeat T v s x)
      (-DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) G t (reverseHeat T v t) x +
        scalar t x * reverseHeat T v t x) t := by
  have hsub : HasDerivAt (fun s : Real => T - s) (-1) t := by
    simpa using
      (hasDerivAt_const (x := t) (c := T)).sub (hasDerivAt_id (x := t))
  have hcomp := (h.equation (T - t) ht x).comp t hsub
  convert hcomp using 1
  change
    -DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) G t (v (T - t)) x + scalar t x * v (T - t) x =
      (DifferentialGeometry.Integral.Connection.laplacianAt
          (I := I) G (T - (T - t)) (v (T - t)) x +
        -scalar (T - (T - t)) x * v (T - t) x) * -1
  rw [show T - (T - t) = t by ring]
  ring

/-- A smooth solution of the conjugate heat equation has stationary total mass
under the moving Riemannian volume of a Ricci-flow metric family.

The metric input is expressed by its trace evolution, while `hconj` is the
actual pointwise equation `∂ₜu = -Δu + Ru`.  This is the normalization
producer needed before coupling Perelman's `W` functional to conjugate heat. -/
theorem conj_heat_mass_deriv
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) {t : Real}
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t)
    (huReg : FunctionRegularAt u t)
    (huSmooth : ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (htrace : ∀ x : M, traceTimeDerivMetricAt (I := I) G t x =
      (-2 : Real) * scalar t x)
    (hconj : ∀ x : M,
      deriv (fun s : Real => u s x) t =
        -Δ_g (I := I) (G.metric t) huSmooth x + scalar t x * u t x) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      0 t := by
  have hvariation :=
    volume_variation_ricciFlow_at (I := I) (M := M) G scalar hg huReg htrace
  have hgreen :=
    integral_smul_laplacian_sub_eq_zero_family
      (I := I) (M := M) (fun s : Real => G.metric s)
      (f := fun _ : M => (1 : Real)) (h := u t)
      contMDiff_const huSmooth t
  have hlap :
      ∫ x, Δ_g (I := I) (G.metric t) huSmooth x
        ∂(volumeMeasureFamily (I := I) (M := M) G t) = 0 := by
    simpa only [one_mul, Δ_g_const, mul_zero, sub_zero] using hgreen
  have hmass :
      (∫ x, (deriv (fun s : Real => u s x) t - scalar t x * u t x)
        ∂(volumeMeasureFamily (I := I) (M := M) G t)) = 0 := by
    calc
      (∫ x, (deriv (fun s : Real => u s x) t - scalar t x * u t x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t)) =
          ∫ x, -Δ_g (I := I) (G.metric t) huSmooth x
            ∂(volumeMeasureFamily (I := I) (M := M) G t) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hconj x]
        ring
      _ = 0 := by rw [integral_neg, hlap, neg_zero]
  exact hvariation.congr_deriv hmass

/-- Total mass of a smooth conjugate-heat solution is constant on a closed
time interval.  This is the interval form of `conj_heat_mass_deriv`. -/
theorem conj_heat_mass_eq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) {a b : Real} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) a)
    (huReg : FunctionRegularAt u a)
    (huSmooth : ∀ t ∈ Set.Icc a b,
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (htrace : ∀ t ∈ Set.Icc a b, ∀ x : M,
      traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x)
    (hconj : ∀ (t : Real) (ht : t ∈ Set.Icc a b) (x : M),
      deriv (fun s : Real => u s x) t =
        -Δ_g (I := I) (G.metric t) (huSmooth t ht) x +
          scalar t x * u t x) :
    (∫ x, u b x ∂(volumeMeasureFamily (I := I) (M := M) G b)) =
      ∫ x, u a x ∂(volumeMeasureFamily (I := I) (M := M) G a) := by
  let mass : Real → Real := fun t =>
    ∫ x, u t x ∂(volumeMeasureFamily (I := I) (M := M) G t)
  have huRegAt : ∀ t : Real, FunctionRegularAt u t := fun _ =>
    { hasDerivAt_time := huReg.hasDerivAt_time
      continuous_joint := huReg.continuous_joint
      continuous_deriv_joint := huReg.continuous_deriv_joint }
  have hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt mass 0 t := by
    intro t ht
    simpa only [mass] using
      conj_heat_mass_deriv (I := I) (M := M) G scalar u (t := t)
        (hg.at_any t) (huRegAt t) (huSmooth t ht) (htrace t ht)
        (hconj t ht)
  have hdiff : DifferentiableOn Real mass (Set.Icc a b) := by
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hconst : ∀ t ∈ Set.Icc a b, mass t = mass a :=
    constant_of_has_deriv_right_zero hdiff.continuousOn (fun t ht =>
      (hderiv t ⟨ht.1, le_of_lt ht.2⟩).hasDerivWithinAt)
  simpa only [mass] using hconst b (Set.right_mem_Icc.mpr hab)

/-- Unit terminal mass propagates to every earlier time of a smooth
conjugate-heat solution. -/
theorem conj_heat_mass_one
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) {a b : Real}
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) a)
    (huReg : FunctionRegularAt u a)
    (huSmooth : ∀ t ∈ Set.Icc a b,
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (htrace : ∀ t ∈ Set.Icc a b, ∀ x : M,
      traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x)
    (hconj : ∀ (t : Real) (ht : t ∈ Set.Icc a b) (x : M),
      deriv (fun s : Real => u s x) t =
        -Δ_g (I := I) (G.metric t) (huSmooth t ht) x +
          scalar t x * u t x)
    (hmass : (∫ x, u b x ∂(volumeMeasureFamily (I := I) (M := M) G b)) = 1) :
    ∀ t ∈ Set.Icc a b,
      (∫ x, u t x ∂(volumeMeasureFamily (I := I) (M := M) G t)) = 1 := by
  intro t ht
  have huRegAt : FunctionRegularAt u t :=
    { hasDerivAt_time := huReg.hasDerivAt_time
      continuous_joint := huReg.continuous_joint
      continuous_deriv_joint := huReg.continuous_deriv_joint }
  have hmass_eq :=
    conj_heat_mass_eq (I := I) (M := M) G scalar u ht.2
      (hg.at_any t) huRegAt
      (fun s hs => huSmooth s ⟨ht.1.trans hs.1, hs.2⟩)
      (fun s hs x => htrace s ⟨ht.1.trans hs.1, hs.2⟩ x)
      (fun s hs x => by
        simpa using hconj s ⟨ht.1.trans hs.1, hs.2⟩ x)
  calc
    (∫ x, u t x ∂(volumeMeasureFamily (I := I) (M := M) G t)) =
        ∫ x, u b x ∂(volumeMeasureFamily (I := I) (M := M) G b) := hmass_eq.symm
    _ = 1 := hmass

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
