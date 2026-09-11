import DifferentialGeometry.Geometry.Comparison.Toponogov.EscapingRadialArms
import DifferentialGeometry.Geometry.Comparison.Toponogov.AsymptoticOppositeArms

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [ConnectedSpace M]

theorem exists_escaping_opposite_intrinsic_arms
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (hescape : Tendsto (fun i => (riemannianEDist I p (x i)).toReal) atTop atTop)
    (hscaled : Tendsto (fun i => lam i * (riemannianEDist I p (x i)).toReal)
      atTop atTop) :
    let D : ℕ → ℝ := fun i => (riemannianEDist I p (x i)).toReal
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ (wMinus wPlus : ∀ n, TangentSpace I (x (phi n))),
        (∀ n, g.inner (x (phi n)) (wMinus n) (wMinus n) = 1 ∧
          g.inner (x (phi n)) (wPlus n) (wPlus n) = 1) ∧
        (∀ n, intrinsicGeodesic (I := I) g hEnorm (x (phi n)) (wMinus n)
          (D (phi n)) = p) ∧
        (∀ n, intrinsicGeodesic (I := I) g hEnorm (x (phi n)) (wPlus n)
          (riemannianEDist I (x (phi n)) (x (phi (n + 1)))).toReal = x (phi (n + 1))) ∧
        (∀ n, 1 ≤ D (phi n) ∧ D (phi n) ≤
          (riemannianEDist I (x (phi n)) (x (phi (n + 1)))).toReal) ∧
        Tendsto (fun n => lam (phi n) * D (phi n)) atTop atTop ∧
        Tendsto (fun n => lam (phi n) *
          (riemannianEDist I (x (phi n)) (x (phi (n + 1)))).toReal) atTop atTop ∧
        ∀ r : ℝ, 0 < r → Tendsto (fun n => lam (phi n) * (riemannianEDist I
          (intrinsicGeodesic (I := I) g hEnorm (x (phi n)) (wMinus n) (r / lam (phi n)))
          (intrinsicGeodesic (I := I) g hEnorm (x (phi n)) (wPlus n)
            (r / lam (phi n)))).toReal) atTop (𝓝 (2 * r)) := by
  dsimp only
  let D : ℕ → ℝ := fun i => (riemannianEDist I p (x i)).toReal
  obtain ⟨phi, hphi, u, v, hu, hvunit, hvconv, hvend, hpositive, hgrowth,
    _, hratio, hselectedScaled, _⟩ :=
    exists_convergent_fast_radial_arms (I := I) g hEnorm p x lam hescape hscaled
  let q : ℕ → M := fun n => x (phi n)
  let a : ℕ → ℝ := fun n => D (phi n)
  let c : ℕ → ℝ := fun n => (riemannianEDist I (q n) (q (n + 1))).toReal
  let scale : ℕ → ℝ := fun n => lam (phi n)
  have ha (n : ℕ) : 0 < a n := by
    change 0 < (riemannianEDist I p (x (phi n))).toReal
    linarith [hpositive n]
  have hscale (n : ℕ) : 0 < scale n := hlam (phi n)
  have hdouble (n : ℕ) : 2 * a n ≤ a (n + 1) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc
      2 * a n ≤ ((n : ℝ) + 2) * a n :=
        mul_le_mul_of_nonneg_right (by linarith) (ha n).le
      _ ≤ a (n + 1) := hgrowth n
  have htri (y z w : M) : (riemannianEDist I y w).toReal ≤
      (riemannianEDist I y z).toReal + (riemannianEDist I z w).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨riemannianEDist_ne_top (I := I) y z,
        riemannianEDist_ne_top (I := I) z w⟩)
      (riemannianEDist_triangle (I := I) (x := y) (y := z) (z := w))
    simpa only [ENNReal.toReal_add (riemannianEDist_ne_top (I := I) y z)
      (riemannianEDist_ne_top (I := I) z w)] using h
  have hconnector (n : ℕ) : a n ≤ c n := by
    have h := htri p (q n) (q (n + 1))
    change a (n + 1) ≤ a n + c n at h
    linarith [hdouble n]
  have hc (n : ℕ) : 0 < c n := (ha n).trans_le (hconnector n)
  have hbackDistance (n : ℕ) : (riemannianEDist I (q n) p).toReal = a n := by
    rw [riemannianEDist_comm]
  have hexMinus : ∀ n, ∃ w : TangentSpace I (q n), g.inner (q n) w w = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm (q n) w (a n) = p := by
    intro n
    have hdistpos : 0 < (riemannianEDist I (q n) p).toReal := by
      rw [hbackDistance]
      exact ha n
    obtain ⟨w, hw, hend⟩ := exists_unit_intrinsic_vector_of_pos_distance (I := I)
      g hEnorm (q n) p hdistpos
    refine ⟨w, hw, ?_⟩
    simpa only [hbackDistance] using hend
  have hexPlus : ∀ n, ∃ w : TangentSpace I (q n), g.inner (q n) w w = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm (q n) w (c n) = q (n + 1) := by
    intro n
    exact exists_unit_intrinsic_vector_of_pos_distance (I := I)
      g hEnorm (q n) (q (n + 1)) (hc n)
  choose wMinus hwMinus hwMinusEnd using hexMinus
  choose wPlus hwPlus hwPlusEnd using hexPlus
  have hminMinus (n : ℕ) : (riemannianEDist I (q n)
      (intrinsicGeodesic (I := I) g hEnorm (q n) (wMinus n) (a n))).toReal = a n := by
    rw [hwMinusEnd, hbackDistance]
  have hminPlus (n : ℕ) : (riemannianEDist I (q n)
      (intrinsicGeodesic (I := I) g hEnorm (q n) (wPlus n) (c n))).toReal = c n := by
    rw [hwPlusEnd]
  have hradialMin (n : ℕ) : (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (v n) (a n))).toReal = a n := by
    rw [hvend]
  have hvnext : Tendsto (fun n => v (n + 1)) atTop (𝓝 u) :=
    hvconv.comp (tendsto_add_atTop_nat 1)
  have hfar : Tendsto (fun n => comparisonAngle (a n) (c n) (a (n + 1)))
      atTop (𝓝 Real.pi) := by
    have h := tendsto_far_comparisonAngle_pi_of_convergent_initial_vectors (I := I)
      g hEnorm hsec p u v (fun n => v (n + 1)) a (fun n => a (n + 1))
      hu hvunit (fun n => hvunit (n + 1)) hvconv hvnext ha hdouble
      hradialMin (fun n => hradialMin (n + 1)) hratio
    have hend (n : ℕ) : intrinsicGeodesic (I := I) g hEnorm p (v n) (a n) = q n :=
      hvend n
    simpa only [hend, c] using h
  have hmovingAngle : Tendsto (fun n => comparisonAngle (a n) (c n)
      (riemannianEDist I
        (intrinsicGeodesic (I := I) g hEnorm (q n) (wMinus n) (a n))
        (intrinsicGeodesic (I := I) g hEnorm (q n) (wPlus n) (c n))).toReal)
      atTop (𝓝 Real.pi) := by
    simpa only [hwMinusEnd, hwPlusEnd] using hfar
  have hscaledA : Tendsto (fun n => scale n * a n) atTop atTop := hselectedScaled
  have hscaledC : Tendsto (fun n => scale n * c n) atTop atTop := by
    apply tendsto_atTop_mono _ hscaledA
    intro n
    exact mul_le_mul_of_nonneg_left (hconnector n) (hscale n).le
  refine ⟨phi, hphi, wMinus, wPlus, ?_, hwMinusEnd, hwPlusEnd, ?_, hscaledA, hscaledC, ?_⟩
  · intro n
    exact ⟨hwMinus n, hwPlus n⟩
  · intro n
    exact ⟨hpositive n, hconnector n⟩
  · intro r hr
    exact tendsto_rescaled_intrinsic_opposite_arms (I := I) g hEnorm hsec q wMinus wPlus
      a c scale ha hc hscale hwMinus hwPlus hminMinus hminPlus hscaledA hscaledC hmovingAngle hr

end DifferentialGeometry.Geometry.Comparison.Toponogov
