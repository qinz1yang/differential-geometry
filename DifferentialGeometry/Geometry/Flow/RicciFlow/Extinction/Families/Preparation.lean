import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ClassWidth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Geodesic.Chart.Regularity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

structure FlatteningProfile where
  psi : ℝ → ℝ
  smooth : ContDiff ℝ ∞ psi
  nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ psi x
  positive : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < psi x
  integral_one : (∫ x in (0 : ℝ)..1, psi x) = 1
  flat_zero : ∀ m : ℕ, iteratedDeriv m psi 0 = 0
  flat_one : ∀ m : ℕ, iteratedDeriv m psi 1 = 0
  symmetric : ∀ x ∈ Icc (0 : ℝ) 1, psi (1 - x) = psi x
  monotone_first_half : MonotoneOn psi (Icc (0 : ℝ) (1 / 2))


def FlatteningProfile.beta (P : FlatteningProfile) (x : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..x, P.psi w

private theorem zero_jets_left {f : ℝ → ℝ} {x : ℝ} (hf : ContDiff ℝ ∞ f)
    (hz : EqOn f (fun _ => 0) (Iio x)) (m : ℕ) : iteratedDeriv m f x = 0 := by
  have heq : EqOn (iteratedDeriv m f) (fun _ => 0) (Iio x) := by
    intro y hy
    simpa only [iteratedDeriv_fun_const_zero] using (hz.iteratedDeriv_of_isOpen isOpen_Iio m) hy
  exact heq.closure (ContDiff.continuous_iteratedDeriv' m (contDiff_infty.mp hf m)) continuous_const
    (by simp only [closure_Iio, mem_Iic, le_refl])

private theorem zero_jets_right {f : ℝ → ℝ} {x : ℝ} (hf : ContDiff ℝ ∞ f)
    (hz : EqOn f (fun _ => 0) (Ioi x)) (m : ℕ) : iteratedDeriv m f x = 0 := by
  have heq : EqOn (iteratedDeriv m f) (fun _ => 0) (Ioi x) := by
    intro y hy
    simpa only [iteratedDeriv_fun_const_zero] using (hz.iteratedDeriv_of_isOpen isOpen_Ioi m) hy
  exact heq.closure (ContDiff.continuous_iteratedDeriv' m (contDiff_infty.mp hf m)) continuous_const
    (by simp only [closure_Ioi, mem_Ici, le_refl])


theorem flatteningProfile_exists : Nonempty FlatteningProfile := by
  let raw : ℝ → ℝ := fun x => expNegInvGlue (x * (1 - x))
  have hraw : ContDiff ℝ ∞ raw :=
    expNegInvGlue.contDiff.comp (contDiff_id.mul (contDiff_const.sub contDiff_id))
  have hrawpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < raw x :=
    expNegInvGlue.pos_of_pos (mul_pos hx.1 (sub_pos.mpr hx.2))
  let Z : ℝ := ∫ x in (0 : ℝ)..1, raw x
  have hZ : 0 < Z := intervalIntegral.integral_pos (by norm_num)
    hraw.continuous.continuousOn (fun x _ => expNegInvGlue.nonneg _)
    ⟨1 / 2, by norm_num, hrawpos _ (by norm_num)⟩
  let psi : ℝ → ℝ := fun x => raw x / Z
  have hpsi : ContDiff ℝ ∞ psi := hraw.div_const Z
  refine ⟨{
    psi := psi
    smooth := hpsi
    nonneg := ?_
    positive := ?_
    integral_one := ?_
    flat_zero := ?_
    flat_one := ?_
    symmetric := ?_
    monotone_first_half := ?_ }⟩
  · intro x _hx
    exact div_nonneg (expNegInvGlue.nonneg _) hZ.le
  · intro x hx
    exact div_pos (hrawpos x hx) hZ
  · change (∫ x in (0 : ℝ)..1, raw x / Z) = 1
    rw [intervalIntegral.integral_div]
    exact div_self hZ.ne'
  · intro m
    apply zero_jets_left hpsi ?_ m
    intro x hx
    change x < 0 at hx
    have hz : raw x = 0 := expNegInvGlue.zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (show x ≤ 0 from le_of_lt hx) (by linarith))
    simp only [psi, hz, zero_div]
  · intro m
    apply zero_jets_right hpsi ?_ m
    intro x hx
    change 1 < x at hx
    have hz : raw x = 0 := expNegInvGlue.zero_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x by linarith [hx]) (by linarith [hx]))
    simp only [psi, hz, zero_div]
  · intro x _hx
    change expNegInvGlue ((1 - x) * (1 - (1 - x))) / Z =
      expNegInvGlue (x * (1 - x)) / Z
    congr 2
    ring
  · intro x hx y hy hxy
    apply div_le_div_of_nonneg_right _ hZ.le
    apply expNegInvGlue.monotone
    have hprod := mul_nonneg (sub_nonneg.mpr hxy)
      (show 0 ≤ 1 - x - y by linarith [hy.2])
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

def IsShortSegment (g : SmoothRiemannianMetric I Q) (p q : Q) (c : ℝ → Q) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c (Ioo (-1 : ℝ) 2) ∧
    IsGeodesicOn (I := I) g c (Ioo (-1 : ℝ) 2) ∧
    c 0 = p ∧ c 1 = q ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      riemannianEDistOf g (c s) (c t) =
        ENNReal.ofReal |s - t| * riemannianEDistOf g p q

def shortSegment (g : SmoothRiemannianMetric I Q) (p q : Q) : ℝ → Q := by
  classical
  exact if h : ∃ c : ℝ → Q, IsShortSegment g p q c then Classical.choose h else fun _ => p


def polygonVertex (γ : Surgery.Topology.Circle → Q) (N : ℕ) (i : ℤ) : Q :=
  γ (((i : ℝ) / N : ℝ) : Surgery.Topology.Circle)

def flatPolygon (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    (N : ℕ) (γ : Surgery.Topology.Circle → Q) : Surgery.Topology.Circle → Q :=
  AddCircle.liftIco (1 : ℝ) 0 (fun x : ℝ =>
    let i : ℤ := ⌊(N : ℝ) * x⌋
    shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (P.beta ((N : ℝ) * x - i)))

def initialRamp (γ : Surgery.Topology.Circle → Q) : ProductCurve Q where
  map x _ := (γ x, x)
  y x _ := x
  degree := 1
  lift_eq _ _ := rfl
  increment _ _ := by simp

variable [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
include hT2 hCompact hConnected hBoundary

theorem shortSegment_neighborhood (g : SmoothRiemannianMetric I Q) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ p q, riemannianEDistOf g p q < ENNReal.ofReal radius →
        IsShortSegment g p q (shortSegment g p q) ∧
        ∀ c : ℝ → Q, IsShortSegment g p q c →
          EqOn c (shortSegment g p q) (Ioo (-1 : ℝ) 2)) ∧
      ContMDiffOn ((I.prod I).prod 𝓘(ℝ, ℝ)) I ∞
        (fun z : (Q × Q) × ℝ => shortSegment g z.1.1 z.1.2 z.2)
        ({pq : Q × Q | riemannianEDistOf g pq.1 pq.2 < ENNReal.ofReal radius} ×ˢ
          Ioo (-1 : ℝ) 2) ∧
      ∀ p t, t ∈ Icc (0 : ℝ) 1 → shortSegment g p p t = p := by
  sorry

theorem rfs_flat_polygon_bounds (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ (N : ℕ), 2 ≤ N → ∀ γ : RegularLoop I Q,
        (∀ i : Fin N, riemannianEDistOf g (polygonVertex γ N i.val)
          (polygonVertex γ N (i.val + 1)) < ENNReal.ofReal radius) →
        ∃ c : RegularLoop I Q,
          (∀ z, c z = flatPolygon g P N γ z) ∧
          ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift c.toContinuousLoop) ∧
          (∀ (i : ℤ) (m : ℕ), 0 < m →
            iteratedDeriv m (e.map ∘ loopLift c.toContinuousLoop) ((i : ℝ) / N) = 0) ∧
          loopLength g c.toContinuousLoop =
            ∑ i : Fin N, (riemannianEDistOf g (polygonVertex γ N i.val)
              (polygonVertex γ N (i.val + 1))).toReal ∧
          loopLength g c.toContinuousLoop ≤ loopLength g γ.toContinuousLoop ∧
          ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
            (initialRamp c).SmoothOn (I := I) univ ∧
            (initialRamp c).IsRampOn (fun _ => g) lambda univ ∧
            (initialRamp c).length (fun _ => g) lambda 0 ≤ loopLength g γ.toContinuousLoop + 1 ∧
            (initialRamp c).totalCurvature (fun _ => g) lambda 0 ≤ (N : ℝ) * Real.pi) ∧
      (∀ (K : Type*) [TopologicalSpace K] (N : ℕ), 2 ≤ N →
        ∀ v : K → Surgery.Topology.Circle → Q,
          (∀ i : Fin N, Continuous (fun k => polygonVertex (v k) N i.val)) →
          (∀ k (i : Fin N), riemannianEDistOf g (polygonVertex (v k) N i.val)
            (polygonVertex (v k) N (i.val + 1)) < ENNReal.ofReal radius) →
          ∀ m : ℕ, Continuous (fun p : K × ℝ =>
            iteratedDeriv m (fun x : ℝ =>
              e.map (flatPolygon g P N (v p.1) (x : Surgery.Topology.Circle))) p.2)) := by
  sorry

theorem rfs_prepared_family (g : SmoothRiemannianMetric I Q) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (eta : ℝ) (heta : 0 < eta) :
    ∃ P : FlatteningProfile, ∃ N : ℕ, 2 ≤ N ∧
      ∃ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        (∀ p z, (prepared p).1 z = flatPolygon g P N (Γ p).1 z) ∧
        HasContinuousSmoothLoopJets e prepared ∧
        ContinuousMap.Homotopic prepared Γ ∧
        (∀ p, |regularLeastArea g (prepared p) - regularLeastArea g (Γ p)| < eta) ∧
        let L₀ := 1 + sSup (Set.range (fun p => loopLength g (Γ p).1.toContinuousLoop))
        let Theta₀ := (N : ℝ) * Real.pi
        let Ainit := familyMaximum g Γ + eta
        0 ≤ L₀ ∧ 0 ≤ Theta₀ ∧ 0 ≤ Ainit ∧
          ∀ p (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
            (initialRamp (prepared p).1).SmoothOn (I := I) univ ∧
            (initialRamp (prepared p).1).IsRampOn (fun _ => g) lambda univ ∧
            (initialRamp (prepared p).1).length (fun _ => g) lambda 0 ≤ L₀ ∧
            (initialRamp (prepared p).1).totalCurvature (fun _ => g) lambda 0 ≤ Theta₀ ∧
            regularLeastArea g (prepared p) ≤ Ainit := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
