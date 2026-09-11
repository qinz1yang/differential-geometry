import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteShortening
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonTriangleLimit

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_fast_positive_subsequence {D : ℕ → ℝ} (hD : Tendsto D atTop atTop) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ (∀ n, 1 ≤ D (phi n)) ∧
      ∀ n : ℕ, ((n : ℝ) + 2) * D (phi n) ≤ D (phi (n + 1)) := by
  have hex (n k : ℕ) : ∃ j : ℕ, k < j ∧ 1 ≤ D j ∧
      ((n : ℝ) + 2) * D k ≤ D j := by
    have hevent : ∀ᶠ j in atTop, k < j ∧ 1 ≤ D j ∧
        ((n : ℝ) + 2) * D k ≤ D j := by
      filter_upwards [eventually_gt_atTop k, hD (eventually_ge_atTop 1),
        hD (eventually_ge_atTop (((n : ℝ) + 2) * D k))] with j hj hOne hGrow
      exact ⟨hj, hOne, hGrow⟩
    exact hevent.exists
  choose next hnext using hex
  have hfirst : ∀ᶠ n in atTop, (1 : ℝ) ≤ D n := hD (eventually_ge_atTop 1)
  obtain ⟨k0, hk0⟩ := hfirst.exists
  let phi : ℕ → ℕ := fun n => Nat.rec k0 (fun m k => next m k) n
  have hstep (n : ℕ) : phi (n + 1) = next n (phi n) := rfl
  have hmono : StrictMono phi := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hstep]
    exact (hnext n (phi n)).1
  have hpos : ∀ n, 1 ≤ D (phi n) := by
    intro n
    cases n with
    | zero => exact hk0
    | succ n =>
      rw [hstep]
      exact (hnext n (phi n)).2.1
  refine ⟨phi, hmono, hpos, ?_⟩
  intro n
  rw [hstep]
  exact (hnext n (phi n)).2.2

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

theorem tendsto_far_comparisonAngle_pi_of_convergent_initial_vectors
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (u : TangentSpace I p) (w v : ℕ → TangentSpace I p) (a b : ℕ → ℝ)
    (hunit : g.inner p u u = 1)
    (hwunit : ∀ i, g.inner p (w i) (w i) = 1)
    (hvunit : ∀ i, g.inner p (v i) (v i) = 1)
    (hwconv : Tendsto w atTop (𝓝 u)) (hvconv : Tendsto v atTop (𝓝 u))
    (ha : ∀ i, 0 < a i) (hseparated : ∀ i, 2 * a i ≤ b i)
    (hminA : ∀ i, (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (w i) (a i))).toReal = a i)
    (hminB : ∀ i, (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (v i) (b i))).toReal = b i)
    (hratio : Tendsto (fun i => a i / b i) atTop (𝓝 0)) :
    Tendsto (fun i => comparisonAngle (a i)
      (riemannianEDist I
        (intrinsicGeodesic (I := I) g hEnorm p (w i) (a i))
        (intrinsicGeodesic (I := I) g hEnorm p (v i) (b i))).toReal
      (b i)) atTop (𝓝 Real.pi) := by
  let alpha : ℕ → M := fun i => intrinsicGeodesic (I := I) g hEnorm p (w i) (a i)
  let beta : ℕ → M := fun i => intrinsicGeodesic (I := I) g hEnorm p (v i) (b i)
  let c : ℕ → ℝ := fun i => (riemannianEDist I (alpha i) (beta i)).toReal
  have hradA (i : ℕ) : (riemannianEDist I p (alpha i)).toReal = a i := hminA i
  have hradB (i : ℕ) : (riemannianEDist I p (beta i)).toReal = b i := hminB i
  have hb (i : ℕ) : 0 < b i := by linarith [ha i, hseparated i]
  have htri (x y z : M) : (riemannianEDist I x z).toReal ≤
      (riemannianEDist I x y).toReal + (riemannianEDist I y z).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨riemannianEDist_ne_top (I := I) x y,
        riemannianEDist_ne_top (I := I) y z⟩)
      (riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z))
    simpa only [ENNReal.toReal_add (riemannianEDist_ne_top (I := I) x y)
      (riemannianEDist_ne_top (I := I) y z)] using h
  have hlower (i : ℕ) : |a i - b i| ≤ c i := by
    have h1 := htri p (alpha i) (beta i)
    have h2 := htri p (beta i) (alpha i)
    rw [hradA, hradB] at h1 h2
    rw [riemannianEDist_comm (I := I) (x := beta i) (y := alpha i)] at h2
    change b i ≤ a i + c i at h1
    change a i ≤ b i + c i at h2
    apply abs_le.mpr
    constructor <;> linarith
  have hupper (i : ℕ) : c i ≤ a i + b i := by
    have h := htri (alpha i) p (beta i)
    rw [riemannianEDist_comm (I := I) (x := alpha i) (y := p), hradA, hradB] at h
    exact h
  have hc (i : ℕ) : 0 < c i := by
    have hba : b i - a i ≤ c i := by
      have h := neg_le_abs (a i - b i)
      linarith [hlower i]
    linarith [ha i, hseparated i]
  have hinnerContinuous : Continuous
      (fun z : TangentSpace I p × TangentSpace I p => g.inner p z.1 z.2) :=
    ((g.inner p).continuous.comp continuous_fst).clm_apply continuous_snd
  have hinner : Tendsto (fun i => g.inner p (w i) (v i)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, hunit] using
      (hinnerContinuous.tendsto (u, u)).comp (hwconv.prodMk_nhds hvconv)
  have hactual : Tendsto (fun i => Real.arccos (g.inner p (w i) (v i)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.arccos_one] using
      Real.continuous_arccos.continuousAt.tendsto.comp hinner
  have hbase : Tendsto (fun i => comparisonAngle (a i) (b i) (c i)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hactual
    · intro i
      exact (comparisonAngle_mem_Icc (a i) (b i) (c i)).1
    · intro i
      have h := complete_triangle_angle (I := I) g hEnorm hsec p (w i) (v i)
        (a i) (b i) (ha i) (hb i) (hwunit i) (hvunit i) (hminA i) (hminB i)
      rw [hminA i, hminB i] at h
      exact h
  exact tendsto_comparisonAngle_pi_of_tendsto_zero ha hb hc hlower hupper hratio hbase

end DifferentialGeometry.Geometry.Comparison.Toponogov
