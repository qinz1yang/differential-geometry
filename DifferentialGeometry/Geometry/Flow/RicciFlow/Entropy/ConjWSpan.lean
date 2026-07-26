import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinOn
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.WVariation

set_option autoImplicit false

/-!
# Exact-interval W comparison for Galerkin limits

The existing endpoint-continuity theorem supplies the right limit at reverse
time zero.  Exact heat-potential reconstruction then supplies antitonicity on
the whole positive interior, so no second lifespan is selected.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Bundle Filter MeasureTheory Set Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open scoped Manifold ContDiff Topology

universe u uE uH

variable {M : Type u}
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Every strictly interior reverse-time value of an exact Galerkin heat
potential has W value at most its prescribed value at reverse time zero. -/
theorem gallim_w_lt
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [BoundarylessManifold I M] [CompactSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hpot : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 tau hτ.le)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      (fun s x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
      (fun s x =>
        scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i r => ulim r i) s x))
    (hreg : ∀ s ∈ Set.Icc (0 : Real) tau,
      (T : Real) - s ∈ D.regular)
    {a : Real} (ha : 0 < a)
    (hpos : ∀ q ∈ Set.Icc (0 : Real) tau, ∀ x : M,
      0 < scalarSpecSum (I := I) (M := M)
        (S.family.metric (T : Real)) (fun i s => ulim s i) q x) :
    ∀ q ∈ Set.Ico (0 : Real) tau,
      (let n := Module.finrank Real E
       let G := reverseFamily (I := I) (M := M)
         (flowG (I := I) S) (T : Real)
       let u : Real → M → Real := fun s x =>
         scalarSpecSum (I := I) (M := M)
           (S.family.metric (T : Real)) (fun i r => ulim r i) s x
       let f : Real → M → Real := fun s =>
         perelmanPotential n (a + s) (u s)
       let R : Real → M → Real := fun s x => S.scalar ((T : Real) - s) x
       let Q : Real → M → Real := fun s x =>
         (G.metric s).inner x
           (gradientFun (I := I) (G.metric s) (f s) x)
           (gradientFun (I := I) (G.metric s) (f s) x)
       wFunctional (volumeMeasureFamily (I := I) (M := M) G q)
         n (a + q) (R q) (Q q) (f q)) ≤
      (let n := Module.finrank Real E
       let G := reverseFamily (I := I) (M := M)
         (flowG (I := I) S) (T : Real)
       let u : Real → M → Real := fun s x =>
         scalarSpecSum (I := I) (M := M)
           (S.family.metric (T : Real)) (fun i r => ulim r i) s x
       let f : Real → M → Real := fun s =>
         perelmanPotential n (a + s) (u s)
       let R : Real → M → Real := fun s x => S.scalar ((T : Real) - s) x
       let Q : Real → M → Real := fun s x =>
         (G.metric s).inner x
           (gradientFun (I := I) (G.metric s) (f s) x)
           (gradientFun (I := I) (G.metric s) (f s) x)
       wFunctional (volumeMeasureFamily (I := I) (M := M) G 0)
         n a (R 0) (Q 0) (f 0)) := by
  classical
  let n := Module.finrank Real E
  let G := reverseFamily (I := I) (M := M)
    (flowG (I := I) S) (T : Real)
  let u : Real → M → Real := fun s x =>
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
      (fun i r => ulim r i) s x
  let f : Real → M → Real := fun s => perelmanPotential n (a + s) (u s)
  let R : Real → M → Real := fun s x => S.scalar ((T : Real) - s) x
  let Q : Real → M → Real := fun s x =>
    (G.metric s).inner x
      (gradientFun (I := I) (G.metric s) (f s) x)
      (gradientFun (I := I) (G.metric s) (f s) x)
  let W : Real → Real := fun s =>
    wFunctional (volumeMeasureFamily (I := I) (M := M) G s)
      n (a + s) (R s) (Q s) (f s)
  obtain ⟨tauC, htauC, _htauC_tau, hcontC⟩ :=
    gallim_w_cont (I := I) (M := M) hS hDim hτ hlim ha hpos
  have hW0 : Tendsto W (𝓝[>] (0 : Real)) (𝓝 (W 0)) := by
    have hcont0 := hcontC 0 ⟨le_rfl, htauC.le⟩
    simpa only [W, n, G, u, f, R, Q] using
      hcont0.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT htauC)
  let Dr := RealTimeInterval.closed 0 tau hτ.le
  let uShift : Real → M → Real := fun r x => u (r - a) x
  have hheatShift :
      DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
        (Dr.timeShift (-a))
        (reverseFamily (I := I) (M := M) (flowG (I := I) S)
          ((T : Real) + a))
        (fun r x =>
          (conjCoeff (I := I) (M := M) S
            ((T : Real) + a - r) : M → Real) x)
        uShift := by
    have hraw := heat_pot_add (I := I) (M := M) Dr
      (flowG (I := I) S)
      (fun r x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - r) : M → Real) x)
      u (T : Real) a hpot
    have hcoeff :
        (fun r x =>
          (conjCoeff (I := I) (M := M) S
            ((T : Real) - (r - a)) : M → Real) x) =
        fun r x =>
          (conjCoeff (I := I) (M := M) S
            ((T : Real) + a - r) : M → Real) x := by
      funext r x
      congr 2
      ring
    rw [hcoeff] at hraw
    simpa only [uShift] using hraw
  have hposShift : ∀ r : Real,
      r ∈ (Dr.timeShift (-a)).regular ∩ Set.Ioi (0 : Real) →
      ∀ x : M, 0 < uShift r x := by
    intro r hr x
    have hrOld : r - a ∈ Set.Ioo (0 : Real) tau := by
      simpa only [Dr, RealTimeInterval.timeShift_regular, Set.mem_setOf_eq,
        RealTimeInterval.closed, sub_eq_add_neg] using hr.1
    exact hpos (r - a) ⟨hrOld.1.le, hrOld.2.le⟩ x
  let GShift := reverseFamily (I := I) (M := M)
    (flowG (I := I) S) ((T : Real) + a)
  let fShift : Real → M → Real := fun r =>
    perelmanPotential n r (uShift r)
  let RShift : Real → M → Real := fun r x =>
    S.scalar ((T : Real) + a - r) x
  let QShift : Real → M → Real := fun r x =>
    (GShift.metric r).inner x
      (gradientFun (I := I) (GShift.metric r) (fShift r) x)
      (gradientFun (I := I) (GShift.metric r) (fShift r) x)
  let WShift : Real → Real :=
    wFunctionalAlong
      (volumeMeasureFamily (I := I) (M := M) GShift)
      n (fun r : Real => r) RShift QShift fShift
  have hWShift (q : Real) : WShift (a + q) = W q := by
    have hmetric : GShift.metric (a + q) = G.metric q := by
      change S.family.metric ((T : Real) + a - (a + q)) =
        S.family.metric ((T : Real) - q)
      rw [show (T : Real) + a - (a + q) = (T : Real) - q by ring]
    have huq : uShift (a + q) = u q := by
      funext x
      simp only [uShift, add_sub_cancel_left]
    have hfq : fShift (a + q) = f q := by
      dsimp only [fShift, f]
      rw [huq]
    have hRq : RShift (a + q) = R q := by
      funext x
      change S.scalar ((T : Real) + a - (a + q)) x =
        S.scalar ((T : Real) - q) x
      rw [show (T : Real) + a - (a + q) = (T : Real) - q by ring]
    have hQq : QShift (a + q) = Q q := by
      funext x
      dsimp only [QShift, Q]
      rw [hmetric, hfq]
    have hmu :
        volumeMeasureFamily (I := I) (M := M) GShift (a + q) =
          volumeMeasureFamily (I := I) (M := M) G q := by
      change riemannianVolumeMeasure (I := I) (M := M)
          (GShift.metric (a + q)) =
        riemannianVolumeMeasure (I := I) (M := M) (G.metric q)
      rw [hmetric]
    dsimp only [WShift, wFunctionalAlong]
    rw [hmu, hRq, hQq, hfq]
  have hanti : AntitoneOn W (Set.Ioo (0 : Real) tau) := by
    intro r hr s hs hrs
    have hDr : Set.Icc (a + r) (a + s) ⊆ (Dr.timeShift (-a)).regular := by
      intro z hz
      change z - a ∈ Set.Ioo (0 : Real) tau
      constructor
      · rw [sub_pos]
        exact (lt_add_of_pos_right a hr.1).trans_le hz.1
      · linarith [hz.2, hs.2]
    have hD : ∀ z ∈ Set.Icc (a + r) (a + s),
        (T : Real) + a - z ∈ D.regular := by
      intro z hz
      have hz' : z - a ∈ Set.Icc (0 : Real) tau := by
        constructor <;> linarith [hr.1, hs.2, hz.1, hz.2]
      rw [show (T : Real) + a - z = (T : Real) - (z - a) by ring]
      exact hreg (z - a) hz'
    have hmono : AntitoneOn WShift (Set.Icc (a + r) (a + s)) := by
      simpa only [WShift, GShift, fShift, RShift, QShift] using
        w_rev_antitone (I := I) S hS ((T : Real) + a)
          uShift hheatShift hposShift (add_pos ha hr.1) hDr hD
    have hleft : a + r ∈ Set.Icc (a + r) (a + s) :=
      ⟨le_rfl, add_le_add_right hrs a⟩
    have hright : a + s ∈ Set.Icc (a + r) (a + s) :=
      ⟨add_le_add_right hrs a, le_rfl⟩
    have hle := hmono hleft hright (add_le_add_right hrs a)
    rw [hWShift s, hWShift r] at hle
    exact hle
  intro q hq
  suffices hle : W q ≤ W 0 by
    simpa only [W, n, G, u, f, R, Q, add_zero] using hle
  by_cases hq0 : q = 0
  · subst q
    exact le_rfl
  · have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hq0)
    have hqoo : q ∈ Set.Ioo (0 : Real) tau := ⟨hqpos, hq.2⟩
    apply ge_of_tendsto hW0
    filter_upwards [Ioc_mem_nhdsGT hqpos] with r hr
    exact hanti ⟨hr.1, hr.2.trans_lt hq.2⟩ hqoo hr.2

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
