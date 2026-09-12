import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.LeastArea
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuousOn_intervalIntegral_of_continuousOn_rectangle {f : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ContinuousOn (fun t : ℝ => ∫ x in (0 : ℝ)..1, f x t) (Icc a b) := by
  have hproj : Continuous (fun p : ℝ × ℝ =>
      ((max 0 (min p.2 1), max a (min p.1 b)) : ℝ × ℝ)) := by fun_prop
  have hmaps : ∀ p : ℝ × ℝ,
      ((max 0 (min p.2 1), max a (min p.1 b)) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b := by
    rintro ⟨u, v⟩
    exact ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩,
      ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩⟩
  have hcont : Continuous
      (Function.uncurry fun s u => f (max 0 (min u 1)) (max a (min s b))) :=
    h.comp_continuous hproj hmaps
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun s u => f (max 0 (min u 1)) (max a (min s b))) hcont 0 1
  refine hc.continuousOn.congr fun t ht => intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  have hx1 : max 0 (min x 1) = x := by rw [min_eq_left hx.2, max_eq_right hx.1]
  have ht1 : max a (min t b) = t := by rw [min_eq_left ht.2, max_eq_right ht.1]
  simp only [hx1, ht1]

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem unitTangent_inner_self (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    (g t).inner (c.lift x t) (c.unitTangent g x t) (c.unitTangent g x t) = 1 := by
  have hs := c.speed_pos g hi x t ht
  have hsquare : c.speed g x t ^ 2 = (g t).inner (c.lift x t) (c.X x t) (c.X x t) :=
    Real.sq_sqrt ((g t).pos (c.lift x t) (c.X x t) (hi x t ht)).le
  simp only [unitTangent, map_smul, smul_apply, smul_eq_mul]
  rw [← hsquare]
  field_simp [ne_of_gt hs]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem normal_component_add_tangent (g : SmoothRiemannianMetric I M) (p : M)
    (V T : TangentSpace I p) (alpha : ℝ) (hT : g.inner p T T = 1) :
    (V + alpha • T) - g.inner p (V + alpha • T) T • T =
      V - g.inner p V T • T := by
  have hinner : g.inner p (V + alpha • T) T = g.inner p V T + alpha := by
    simp [map_add, map_smul, hT]
  rw [hinner, add_smul]
  abel

def normalVelocityError (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) : c.Field (I := I) := fun x t =>
  let W := c.velocity (I := I) J x t - c.curvatureVector g x t
  W - (g t).inner (c.lift x t) W (c.unitTangent g x t) • c.unitTangent g x t

def areaError (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) : ℝ → ℝ :=
  c.integral g (fun x t => Real.sqrt (c.normSq g (c.normalVelocityError g J) x t))

omit [CompleteSpace E] in
theorem areaError_nonneg (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (t : ℝ) : 0 ≤ c.areaError g J t := by
  apply intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  exact mul_nonneg (Real.sqrt_nonneg _) (c.speed_nonneg g x t)

omit [CompleteSpace E] in
theorem normalVelocityError_eq_zero (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.IsSolutionOn g J) (x t : ℝ) (ht : t ∈ J) :
    c.normalVelocityError g J x t = 0 := by
  simp [normalVelocityError, hc.equation x t ht]

omit [CompleteSpace E] in
theorem areaError_eq_zero (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.IsSolutionOn g J) (t : ℝ) (ht : t ∈ J) :
    c.areaError g J t = 0 := by
  simp [areaError, integral, normSq, c.normalVelocityError_eq_zero g hc _ t ht]

end CurveMap


def curveOfLoopFamily (γ : ℝ → ContinuousFreeLoop M) : CurveMap M := fun z t => γ t z

def loopFamilyLeastArea (g : ℝ → SmoothRiemannianMetric I M)
    (γ : ℝ → ContinuousFreeLoop M) (t : ℝ) : ℝ :=
  sInf (Width.competitorAreas (g t) (γ t))

variable [hBoundary : I.Boundaryless] [hT2 : T2Space M]
    [hCompact : CompactSpace M] [hNonempty : Nonempty M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty in
theorem loopFamilyLeastArea_eq (g : ℝ → SmoothRiemannianMetric I M)
    (γ : ℝ → ContinuousFreeLoop M) (t : ℝ) (hctr : IsContractibleLoop (γ t))
    (hlip : Width.IsLipschitzLoop (g t) (γ t)) :
    loopFamilyLeastArea g γ t = Width.leastArea (g t) (γ t) hctr hlip := rfl


def regularLoopSlice (γ : ℝ → ContinuousFreeLoop M) {J : Set ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    Width.RegularLoop I M where
  toContinuousLoop := γ t
  contMDiff_lift := ((curveOfLoopFamily γ).smooth_slice hγ ht).of_le (by simp)

omit [CompleteSpace E] hNonempty in
theorem loopFamilyLeastArea_nonneg (g : ℝ → SmoothRiemannianMetric I M)
    (γ : ℝ → ContinuousFreeLoop M) {J : Set ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) J)
    (hctr : ∀ t ∈ J, IsContractibleLoop (γ t)) (t : ℝ) (ht : t ∈ J) :
    0 ≤ loopFamilyLeastArea g γ t :=
  Width.leastArea_nonneg (g t) (γ t) (hctr t ht)
    ((regularLoopSlice γ hγ t ht).isLipschitz (g t))

variable [SigmaCompactSpace M]
variable {D : RealTimeInterval} {a b : ℝ}

include hBoundary hT2 hCompact hNonempty


def scalarMinimum (G : SolutionFamily (I := I) (M := M)) (t : ℝ) : ℝ :=
  sInf (Set.range (G.scalar t))


def areaIntegratingFactor (G : SolutionFamily (I := I) (M := M)) (s v : ℝ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * ∫ w in s..v, scalarMinimum G w)

theorem rfs_csf_boundary_isotopy (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  sorry

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_area_error (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc a b))
    (hi : c.ImmersedOn (I := I) (Icc a b))
    (hintegrand : ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt (c.normSq B.family.metric
          (c.normalVelocityError B.family.metric (Icc a b)) p.1 p.2) *
        c.speed B.family.metric p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ContinuousOn (c.areaError B.family.metric (Icc a b)) (Icc a b) ∧
      ∀ α : ℝ → ℝ → ℝ, c.IsGeometricSolutionOn B.family.metric (Icc a b) α →
        ∀ t ∈ Icc a b, c.areaError B.family.metric (Icc a b) t = 0 := by
  let _ := hc
  let _ := hi
  refine ⟨continuousOn_intervalIntegral_of_continuousOn_rectangle B.lt.le ?_, ?_⟩
  · simpa only [CurveMap.areaError, CurveMap.integral] using hintegrand
  · intro α hg t ht
    have hW : ∀ x, c.normalVelocityError B.family.metric (Icc a b) x t = 0 := by
      intro x
      have hT := c.unitTangent_inner_self B.family.metric hg.immersed x t ht
      have h0 : c.velocity (I := I) (Icc a b) x t - c.curvatureVector B.family.metric x t =
          α x t • c.unitTangent B.family.metric x t := by
        rw [hg.equation x t ht]
        abel
      simp only [CurveMap.normalVelocityError, h0, map_smul, smul_apply, smul_eq_mul, hT,
        mul_one, sub_self]
    simp [CurveMap.areaError, CurveMap.integral, CurveMap.normSq, hW]

theorem rfs_csf_embedded_area (B : RicciBackground (I := I) (M := M) D a b)
    (hdim : Module.finrank ℝ E = 3) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) :
    ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by
  sorry

omit hBoundary hT2 hCompact hNonempty in
theorem rfs_csf_area_comparison_ode (A rho F : ℝ → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hA : ContinuousOn A (Icc s t)) (hrho : ContinuousOn rho (Icc s t))
    (hF : ContinuousOn F (Icc s t)) (exceptional : Finset ℝ)
    (hDini : ∀ v ∈ Ico s t, v ∉ exceptional → ∀ ε > 0, ∃ δ > 0,
      ∀ h ∈ Ioo (0 : ℝ) δ, v + h ≤ t →
        (A (v + h) - A v) / h ≤ -rho v * A v + F v + ε) :
    Real.exp (∫ w in s..t, rho w) * A t ≤ A s +
      ∫ v in s..t, Real.exp (∫ w in s..v, rho w) * F v := by
  sorry

theorem rfs_csf_generic_curves (B : RicciBackground (I := I) (M := M) D a b)
    (hdim : Module.finrank ℝ E = 3) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b)) :
    ∃ approximants : ℕ → ℝ → ContinuousFreeLoop M,
      (∀ j, (curveOfLoopFamily (approximants j)).SmoothOn (I := I) (Icc a b) ∧
        (curveOfLoopFamily (approximants j)).ImmersedOn (I := I) (Icc a b) ∧
        ∃ exceptional : Finset ℝ, ∀ t ∈ Icc a b,
          t ∉ exceptional → Topology.IsEmbedding (approximants j t)) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ m : ℕ, m ≤ 2 →
        ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
          ‖iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (approximants j q.2 (q.1 : Surgery.Topology.Circle)))
              (univ ×ˢ Icc a b) p -
            iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
              (univ ×ˢ Icc a b) p‖ < ε) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ Icc a b,
        |(curveOfLoopFamily (approximants j)).areaError B.family.metric (Icc a b) t -
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t| < ε) ∧
      ((∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        (∀ j t, t ∈ Icc a b → IsContractibleLoop (approximants j t)) ∧
        ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ Icc a b,
          |loopFamilyLeastArea B.family.metric (approximants j) t -
            loopFamilyLeastArea B.family.metric γ t| < ε) := by
  sorry

theorem rfs_csf_immersed_area (B : RicciBackground (I := I) (M := M) D a b)
    (hdim : Module.finrank ℝ E = 3) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t)) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
        areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
          loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, areaIntegratingFactor B.family s v *
              (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
      (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
        (loopFamilyLeastArea B.family.metric γ (t + h) -
            loopFamilyLeastArea B.family.metric γ t) / h ≤
          -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
