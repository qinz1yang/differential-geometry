import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinSpan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjWSpan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.WLower

set_option autoImplicit false

/-!
# Uniform W lower bounds on positive regular slabs

This file iterates the exact-interior Galerkin W comparison with one compact-
slab lifespan.  The induction accepts arbitrary smooth positive unit densities,
so it applies both to cutoff data and to every evolved intermediate slice.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Bundle Filter MeasureTheory Set Tensor0SBundle
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

/-- Perelman's W functional at one Ricci-flow time, written in the positive
density normal form used by conjugate heat propagation. -/
noncomputable def flowW
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t theta : Real) (v : M → Real) : Real :=
  let g := S.family.metric t
  let f := perelmanPotential (Module.finrank Real E) theta v
  wFunctional (riemannianVolumeMeasure (I := I) (M := M) g)
    (Module.finrank Real E) theta (S.scalar t)
    (fun x => g.inner x
      (gradientFun (I := I) g f x)
      (gradientFun (I := I) g f x)) f

/-- One fixed positive base slice supplies a W lower constant uniformly over
all compact regular slabs with that left endpoint and scale budget. -/
theorem w_span_uniform
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [BoundarylessManifold I M] [CompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3)
    {a₀ a tauMax : Real} (ha₀a : a₀ < a) :
    ∃ L : Real, ∀ {b : Real}, a ≤ b →
      Set.Icc a₀ b ⊆ D.regular →
      ∀ t ∈ Set.Icc a b,
        ∀ {theta : Real}, 0 < theta → theta + (t - a) < tauMax →
        ∀ {v : M → Real}, ContMDiff I 𝓘(Real) ∞ v →
          (∀ x : M, 0 < v x) →
          (∫ x, v x ∂(riemannianVolumeMeasure (I := I) (M := M)
            (S.family.metric t))) = 1 →
          L ≤ flowW (I := I) (M := M) S t theta v := by
  classical
  obtain ⟨L, hL⟩ := w_density_lower (I := I) (M := M)
    (S.family.metric a) hDim tauMax
  refine ⟨L, ?_⟩
  intro b hab hreg
  obtain ⟨rho₀, hrho₀, _hrho₀_one, hspan⟩ :=
    gallim_span (I := I) (M := M) S hS hreg
  let r : Real := min rho₀ (a - a₀)
  have hr : 0 < r := lt_min hrho₀ (sub_pos.mpr ha₀a)
  have hr_rho : r ≤ rho₀ := min_le_left _ _
  have hr_gap : r ≤ a - a₀ := min_le_right _ _
  let delta : Real := r / 2
  have hdelta : 0 < delta := by
    simpa only [delta] using half_pos hr
  have hdelta_r : delta < r := by
    simpa only [delta] using half_lt_self hr
  let Good : Real → Prop := fun t =>
    ∀ theta : Real, 0 < theta → theta + (t - a) < tauMax →
      ∀ v : M → Real, ContMDiff I 𝓘(Real) ∞ v →
        (∀ x : M, 0 < v x) →
        (∫ x, v x ∂(riemannianVolumeMeasure (I := I) (M := M)
          (S.family.metric t))) = 1 →
        L ≤ flowW (I := I) (M := M) S t theta v
  have hbase : Good a := by
    dsimp only [Good]
    intro theta htheta hbudget v hv hpos hmass
    have hthetaMax : theta ∈ Set.Ioc (0 : Real) tauMax := by
      constructor
      · exact htheta
      · linarith
    have hbound := hL hthetaMax hv hpos hmass
    simpa only [flowW, hDim, SolutionOn.scalar, SolutionFamily.scalar] using hbound
  have hstep (s t : Real) (hs : s ∈ Set.Icc a b)
      (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
      (hgap : t - s ≤ delta) (hgood : Good s) : Good t := by
    dsimp only [Good] at hgood ⊢
    intro theta htheta hbudget v hv hpos hmass
    by_cases hstEq : s = t
    · subst t
      exact hgood theta htheta hbudget v hv hpos hmass
    have hqpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst hstEq)
    let T : D.RegularTime :=
      ⟨t, hreg ⟨ha₀a.le.trans ht.1, ht.2⟩⟩
    have hT : (T : Real) ∈ Set.Icc a₀ b :=
      ⟨ha₀a.le.trans ht.1, ht.2⟩
    have hleft : a₀ ≤ (T : Real) - r := by
      change a₀ ≤ t - r
      linarith [ht.1, hr_gap]
    let zeta : C^∞⟮I, M; Real⟯ := ⟨v, hv⟩
    let u₀ : SmoothCcTensor (S.family.metric (T : Real)) 0 0 :=
      scalarCc (I := I) (M := M) (S.family.metric (T : Real)) zeta
    have hu₀ :
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u₀.toSection = v := by
      simpa only [u₀, zeta] using
        scalar0_scalarCc (I := I) (M := M)
          (S.family.metric (T : Real)) zeta
    obtain ⟨V, phi, ulim, hlim, hpot⟩ :=
      hspan T hT r hr hr_rho hleft u₀
    let u : Real → M → Real := fun q x =>
      scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
        (fun i z => ulim z i) q x
    have hinit : ∀ x : M,
        0 < TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          u₀.toSection x := by
      intro x
      rw [hu₀]
      exact hpos x
    have hposPath : ∀ q ∈ Set.Icc (0 : Real) r, ∀ x : M, 0 < u q x := by
      simpa only [u] using
        gallim_pos_on (I := I) (M := M) S hS hreg T hT hr hleft
          hlim hpot hinit
    have href : ∀ q ∈ Set.Icc (0 : Real) r,
        (T : Real) - q ∈ D.regular := by
      intro q hq
      apply hreg
      constructor <;> linarith [hq.1, hq.2, hT.1, hT.2, hleft]
    have hmassPath := heatpot_mass_on (I := I) (M := M)
      S hS T hr hpot href
    let q : Real := t - s
    have hqIcc : q ∈ Set.Icc (0 : Real) r := by
      constructor
      · exact hqpos.le
      · exact hgap.trans hdelta_r.le
    have hqIco : q ∈ Set.Ico (0 : Real) r :=
      ⟨hqpos.le, hgap.trans_lt hdelta_r⟩
    have htq : (T : Real) - q = s := by
      dsimp only [T, q]
      ring
    have hu0eq : u 0 = v := by
      dsimp only [u]
      rw [galLim_initial (I := I) (M := M) hlim]
      exact hu₀
    have hmass0 :
        (∫ x, u 0 x ∂(volumeMeasureFamily (I := I) (M := M)
          (reverseFamily (I := I) (M := M)
            (flowG (I := I) S) (T : Real)) 0)) = 1 := by
      rw [hu0eq]
      simpa only [volumeMeasureFamily, metricFamilyForMeasure,
        riemannianMeasureFamily, reverseFamily, flowG, sub_zero] using hmass
    have hmassq :
        (∫ x, u q x ∂(riemannianVolumeMeasure (I := I) (M := M)
          (S.family.metric s))) = 1 := by
      have hm := (hmassPath q hqIcc).trans hmass0
      simpa only [volumeMeasureFamily, metricFamilyForMeasure,
        riemannianMeasureFamily, reverseFamily, flowG, htq] using hm
    have hsmoothq : ContMDiff I 𝓘(Real) ∞ (u q) := by
      exact hpot.sliceSmooth q hqIcc
    have hposq : ∀ x : M, 0 < u q x := hposPath q hqIcc
    have hthetaq : 0 < theta + q := add_pos_of_pos_of_nonneg htheta hqIco.1
    have hbudgetq : theta + q + (s - a) < tauMax := by
      have hqeq : q = t - s := rfl
      rw [hqeq]
      linarith
    have hlower : L ≤ flowW (I := I) (M := M) S s (theta + q) (u q) :=
      hgood (theta + q) hthetaq hbudgetq (u q) hsmoothq hposq hmassq
    have hW := gallim_w_lt (I := I) (M := M)
      hS hDim hr hlim hpot href htheta hposPath q hqIco
    have hWflow :
        flowW (I := I) (M := M) S s (theta + q) (u q) ≤
          flowW (I := I) (M := M) S t theta v := by
      simpa [flowW, u, hu0eq, htq, hDim, volumeMeasureFamily,
        metricFamilyForMeasure, riemannianMeasureFamily, reverseFamily,
        flowG] using hW
    exact hlower.trans hWflow
  have hgrid : ∀ n : Nat, ∀ t ∈ Set.Icc a b,
      t ≤ a + (n : Real) * delta → Good t := by
    intro n
    induction n with
    | zero =>
        intro t ht hta
        have hta' : t = a := by
          norm_num at hta
          exact le_antisymm hta ht.1
        subst t
        exact hbase
    | succ n ih =>
        intro t ht htn
        let s : Real := max a (t - delta)
        have hsA : a ≤ s := le_max_left _ _
        have hst : s ≤ t := by
          apply max_le ht.1
          linarith [hdelta.le]
        have hsB : s ≤ b := hst.trans ht.2
        have hsn : s ≤ a + (n : Real) * delta := by
          apply max_le
          · have hn0 : 0 ≤ (n : Real) * delta :=
              mul_nonneg (Nat.cast_nonneg n) hdelta.le
            linarith
          · norm_num [Nat.cast_succ] at htn ⊢
            linarith
        have hgap : t - s ≤ delta := by
          have hsLower : t - delta ≤ s := le_max_right _ _
          linarith
        exact hstep s t ⟨hsA, hsB⟩ ht hst hgap (ih s ⟨hsA, hsB⟩ hsn)
  obtain ⟨N : Nat, hN⟩ := exists_nat_gt ((b - a) / delta)
  have hcover : b ≤ a + (N : Real) * delta := by
    have hmul : b - a < (N : Real) * delta :=
      (div_lt_iff₀ hdelta).mp hN
    linarith
  intro t ht theta htheta hbudget v hv hpos hmass
  have hgood := hgrid N t ht (ht.2.trans hcover)
  exact hgood theta htheta hbudget v hv hpos hmass

/-- On one compact positive regular slab, a single constant bounds W below for
every smooth positive unit density whose scale stays below a fixed budget. -/
theorem w_span
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [BoundarylessManifold I M] [CompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3)
    {a₀ a b tauMax : Real} (ha₀a : a₀ < a) (hab : a ≤ b)
    (hreg : Set.Icc a₀ b ⊆ D.regular) :
    ∃ L : Real, ∀ t ∈ Set.Icc a b,
      ∀ {theta : Real}, 0 < theta → theta + (t - a) < tauMax →
      ∀ {v : M → Real}, ContMDiff I 𝓘(Real) ∞ v →
        (∀ x : M, 0 < v x) →
        (∫ x, v x ∂(riemannianVolumeMeasure (I := I) (M := M)
          (S.family.metric t))) = 1 →
        L ≤ flowW (I := I) (M := M) S t theta v := by
  obtain ⟨L, hL⟩ := w_span_uniform (I := I) (M := M)
    (tauMax := tauMax) S hS hDim ha₀a
  exact ⟨L, hL (b := b) hab hreg⟩

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
