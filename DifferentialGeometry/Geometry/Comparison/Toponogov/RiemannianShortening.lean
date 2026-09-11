/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Comparison.Toponogov.RiemannianDistance
import DifferentialGeometry.Geometry.Comparison.Toponogov.SquaredDistanceDefectConvexity

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ENNReal Manifold ContDiff Topology

namespace DifferentialGeometry.Toponogov

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

def squaredRiemannianPairDefect (g : SmoothRiemannianMetric I M)
    (alpha beta : ℝ → M) (s t : ℝ) : ℝ :=
  s ^ 2 + t ^ 2 -
    riemannianDistance (I := I) g (alpha s) (beta t) ^ 2

omit [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem riemannianEDistOf_ne_top_of_distance_pos
    (g : SmoothRiemannianMetric I M) {x y : M}
    (hpos : 0 < riemannianDistance (I := I) g x y) :
    riemannianEDistOf (I := I) g x y ≠ (⊤ : ℝ≥0∞) := by
  intro htop
  unfold riemannianDistance at hpos
  rw [htop] at hpos
  simp at hpos

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem cos_riemannianComparisonAngle_of_radial
    (g : SmoothRiemannianMetric I M) {o : M} {alpha beta : ℝ → M}
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (halpha : riemannianDistance (I := I) g o (alpha s) = s)
    (hbeta : riemannianDistance (I := I) g o (beta t) = t)
    (c : RealizedMinimizingConnector (I := I) g (alpha s) (beta t)) :
    Real.cos (riemannianComparisonAngle (I := I) g (alpha s) o (beta t)) =
      squaredRiemannianPairDefect (I := I) g alpha beta s t / (2 * s * t) := by
  have hox : riemannianEDistOf (I := I) g o (alpha s) ≠ (⊤ : ℝ≥0∞) :=
    riemannianEDistOf_ne_top_of_distance_pos g (halpha.symm ▸ hs)
  have hoy : riemannianEDistOf (I := I) g o (beta t) ≠ (⊤ : ℝ≥0∞) :=
    riemannianEDistOf_ne_top_of_distance_pos g (hbeta.symm ▸ ht)
  have hside := riemannianComparisonAngle_sideInequalities
    (I := I) g (alpha s) o (beta t) hox hoy c.edist_ne_top
  have hside' : |s - t| ≤ riemannianDistance (I := I) g (alpha s) (beta t) ∧
      riemannianDistance (I := I) g (alpha s) (beta t) ≤ s + t := by
    simpa only [halpha, hbeta] using hside
  rw [riemannianComparisonAngle, halpha, hbeta,
    cos_comparisonAngle hs ht hside'.1 hside'.2, comparisonCosine]
  rfl

omit [T2Space (TangentBundle I M)] in
private theorem squaredRiemannianPairDefect_convexOn_fst
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {alpha beta : ℝ → M} {A B t : ℝ}
    (halpha : UnitSpeedGeodesicOn (I := I) g alpha (Icc 0 A))
    (ht : t ∈ Icc (0 : ℝ) B)
    (hconnectors : ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
      Nonempty (RealizedMinimizingConnector (I := I) g (alpha s) (beta t))) :
    ConvexOn ℝ (Icc (0 : ℝ) A)
      (fun s ↦ squaredRiemannianPairDefect (I := I) g alpha beta s t) := by
  have hbase : ConvexOn ℝ (Icc (0 : ℝ) A)
      (squaredRiemannianDistanceDefect (I := I) g (beta t) alpha) := by
    apply squaredDistanceDefect_convexOn_of_realizedConnectors
      (I := I) g hsec (beta t) alpha (Icc 0 A) (convex_Icc 0 A) halpha
    intro s hs
    obtain ⟨c⟩ := hconnectors s hs t ht
    exact ⟨c.reverse⟩
  apply (hbase.add_const (t ^ 2)).congr
  intro s _
  simp only [Pi.add_apply, squaredRiemannianDistanceDefect,
    squaredRiemannianPairDefect]
  rw [riemannianDistance_comm (I := I) g (beta t) (alpha s)]
  ring

omit [T2Space (TangentBundle I M)] in
private theorem squaredRiemannianPairDefect_convexOn_snd
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {alpha beta : ℝ → M} {A B s : ℝ}
    (hbeta : UnitSpeedGeodesicOn (I := I) g beta (Icc 0 B))
    (hs : s ∈ Icc (0 : ℝ) A)
    (hconnectors : ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
      Nonempty (RealizedMinimizingConnector (I := I) g (alpha s) (beta t))) :
    ConvexOn ℝ (Icc (0 : ℝ) B)
      (fun t ↦ squaredRiemannianPairDefect (I := I) g alpha beta s t) := by
  have hbase : ConvexOn ℝ (Icc (0 : ℝ) B)
      (squaredRiemannianDistanceDefect (I := I) g (alpha s) beta) :=
    squaredDistanceDefect_convexOn_of_realizedConnectors
      (I := I) g hsec (alpha s) beta (Icc 0 B) (convex_Icc 0 B) hbeta
        (hconnectors s hs)
  apply (hbase.add_const (s ^ 2)).congr
  intro t _
  simp only [Pi.add_apply, squaredRiemannianDistanceDefect,
    squaredRiemannianPairDefect]
  ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem riemannianComparisonAngle_antitone_fst_of_convex_defect
    (g : SmoothRiemannianMetric I M) {o : M} {alpha beta : ℝ → M}
    {A B s₁ s₂ t : ℝ} (hA : 0 < A)
    (halpha_zero : alpha 0 = o)
    (halpha_radial : ∀ s ∈ Icc (0 : ℝ) A,
      riemannianDistance (I := I) g o (alpha s) = s)
    (hbeta_radial : ∀ t ∈ Icc (0 : ℝ) B,
      riemannianDistance (I := I) g o (beta t) = t)
    (hconvex : ∀ t ∈ Icc (0 : ℝ) B,
      ConvexOn ℝ (Icc (0 : ℝ) A)
        (fun s ↦ squaredRiemannianPairDefect (I := I) g alpha beta s t))
    (hconnectors : ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
      Nonempty (RealizedMinimizingConnector (I := I) g (alpha s) (beta t)))
    (hs₁ : 0 < s₁) (hs₁s₂ : s₁ ≤ s₂) (hs₂A : s₂ ≤ A)
    (ht : 0 < t) (htB : t ≤ B) :
    riemannianComparisonAngle (I := I) g (alpha s₂) o (beta t) ≤
      riemannianComparisonAngle (I := I) g (alpha s₁) o (beta t) := by
  have hs₂ : 0 < s₂ := hs₁.trans_le hs₁s₂
  have hs₁A : s₁ ≤ A := hs₁s₂.trans hs₂A
  have htmem : t ∈ Icc (0 : ℝ) B := ⟨ht.le, htB⟩
  have hbeta_t := hbeta_radial t htmem
  have hzero : squaredRiemannianPairDefect (I := I) g alpha beta 0 t = 0 := by
    simp [squaredRiemannianPairDefect, halpha_zero, hbeta_t]
  have hquotient :
      squaredRiemannianPairDefect (I := I) g alpha beta s₁ t / s₁ ≤
        squaredRiemannianPairDefect (I := I) g alpha beta s₂ t / s₂ :=
    convex_div_mono_of_zero hA (hconvex t htmem) hzero
      hs₁ hs₁s₂ hs₂A
  have hscaled :
      squaredRiemannianPairDefect (I := I) g alpha beta s₁ t / (2 * s₁ * t) ≤
        squaredRiemannianPairDefect (I := I) g alpha beta s₂ t / (2 * s₂ * t) := by
    calc
      squaredRiemannianPairDefect (I := I) g alpha beta s₁ t / (2 * s₁ * t) =
          (squaredRiemannianPairDefect (I := I) g alpha beta s₁ t / s₁) /
            (2 * t) := by ring
      _ ≤ (squaredRiemannianPairDefect (I := I) g alpha beta s₂ t / s₂) /
            (2 * t) := div_le_div_of_nonneg_right hquotient (by positivity)
      _ = squaredRiemannianPairDefect (I := I) g alpha beta s₂ t /
            (2 * s₂ * t) := by ring
  obtain ⟨c₁⟩ := hconnectors s₁ ⟨hs₁.le, hs₁A⟩ t htmem
  obtain ⟨c₂⟩ := hconnectors s₂ ⟨hs₂.le, hs₂A⟩ t htmem
  have hcos :
      Real.cos (riemannianComparisonAngle (I := I) g (alpha s₁) o (beta t)) ≤
        Real.cos (riemannianComparisonAngle (I := I) g (alpha s₂) o (beta t)) := by
    rw [cos_riemannianComparisonAngle_of_radial g hs₁ ht
        (halpha_radial s₁ ⟨hs₁.le, hs₁A⟩) hbeta_t c₁,
      cos_riemannianComparisonAngle_of_radial g hs₂ ht
        (halpha_radial s₂ ⟨hs₂.le, hs₂A⟩) hbeta_t c₂]
    exact hscaled
  have htheta₁ := comparisonAngle_mem_Icc
    (riemannianDistance (I := I) g o (alpha s₁))
    (riemannianDistance (I := I) g o (beta t))
    (riemannianDistance (I := I) g (alpha s₁) (beta t))
  have htheta₂ := comparisonAngle_mem_Icc
    (riemannianDistance (I := I) g o (alpha s₂))
    (riemannianDistance (I := I) g o (beta t))
    (riemannianDistance (I := I) g (alpha s₂) (beta t))
  unfold riemannianComparisonAngle
  rw [← Real.arccos_cos htheta₂.1 htheta₂.2,
    ← Real.arccos_cos htheta₁.1 htheta₁.2]
  exact Real.arccos_le_arccos hcos

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem riemannianComparisonAngle_antitone_snd_of_convex_defect
    (g : SmoothRiemannianMetric I M) {o : M} {alpha beta : ℝ → M}
    {A B s t₁ t₂ : ℝ} (hB : 0 < B)
    (hbeta_zero : beta 0 = o)
    (halpha_radial : ∀ s ∈ Icc (0 : ℝ) A,
      riemannianDistance (I := I) g o (alpha s) = s)
    (hbeta_radial : ∀ t ∈ Icc (0 : ℝ) B,
      riemannianDistance (I := I) g o (beta t) = t)
    (hconvex : ∀ s ∈ Icc (0 : ℝ) A,
      ConvexOn ℝ (Icc (0 : ℝ) B)
        (fun t ↦ squaredRiemannianPairDefect (I := I) g alpha beta s t))
    (hconnectors : ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
      Nonempty (RealizedMinimizingConnector (I := I) g (alpha s) (beta t)))
    (hs : 0 < s) (hsA : s ≤ A)
    (ht₁ : 0 < t₁) (ht₁t₂ : t₁ ≤ t₂) (ht₂B : t₂ ≤ B) :
    riemannianComparisonAngle (I := I) g (alpha s) o (beta t₂) ≤
      riemannianComparisonAngle (I := I) g (alpha s) o (beta t₁) := by
  have ht₂ : 0 < t₂ := ht₁.trans_le ht₁t₂
  have ht₁B : t₁ ≤ B := ht₁t₂.trans ht₂B
  have hsmem : s ∈ Icc (0 : ℝ) A := ⟨hs.le, hsA⟩
  have halpha_s := halpha_radial s hsmem
  have hzero : squaredRiemannianPairDefect (I := I) g alpha beta s 0 = 0 := by
    simp [squaredRiemannianPairDefect, hbeta_zero, halpha_s,
      riemannianDistance_comm (I := I) g (alpha s) o]
  have hquotient :
      squaredRiemannianPairDefect (I := I) g alpha beta s t₁ / t₁ ≤
        squaredRiemannianPairDefect (I := I) g alpha beta s t₂ / t₂ :=
    convex_div_mono_of_zero hB (hconvex s hsmem) hzero
      ht₁ ht₁t₂ ht₂B
  have hscaled :
      squaredRiemannianPairDefect (I := I) g alpha beta s t₁ / (2 * s * t₁) ≤
        squaredRiemannianPairDefect (I := I) g alpha beta s t₂ / (2 * s * t₂) := by
    calc
      squaredRiemannianPairDefect (I := I) g alpha beta s t₁ / (2 * s * t₁) =
          (squaredRiemannianPairDefect (I := I) g alpha beta s t₁ / t₁) /
            (2 * s) := by ring
      _ ≤ (squaredRiemannianPairDefect (I := I) g alpha beta s t₂ / t₂) /
            (2 * s) := div_le_div_of_nonneg_right hquotient (by positivity)
      _ = squaredRiemannianPairDefect (I := I) g alpha beta s t₂ /
            (2 * s * t₂) := by ring
  obtain ⟨c₁⟩ := hconnectors s hsmem t₁ ⟨ht₁.le, ht₁B⟩
  obtain ⟨c₂⟩ := hconnectors s hsmem t₂ ⟨ht₂.le, ht₂B⟩
  have hcos :
      Real.cos (riemannianComparisonAngle (I := I) g (alpha s) o (beta t₁)) ≤
        Real.cos (riemannianComparisonAngle (I := I) g (alpha s) o (beta t₂)) := by
    rw [cos_riemannianComparisonAngle_of_radial g hs ht₁ halpha_s
        (hbeta_radial t₁ ⟨ht₁.le, ht₁B⟩) c₁,
      cos_riemannianComparisonAngle_of_radial g hs ht₂ halpha_s
        (hbeta_radial t₂ ⟨ht₂.le, ht₂B⟩) c₂]
    exact hscaled
  have htheta₁ := comparisonAngle_mem_Icc
    (riemannianDistance (I := I) g o (alpha s))
    (riemannianDistance (I := I) g o (beta t₁))
    (riemannianDistance (I := I) g (alpha s) (beta t₁))
  have htheta₂ := comparisonAngle_mem_Icc
    (riemannianDistance (I := I) g o (alpha s))
    (riemannianDistance (I := I) g o (beta t₂))
    (riemannianDistance (I := I) g (alpha s) (beta t₂))
  unfold riemannianComparisonAngle
  rw [← Real.arccos_cos htheta₂.1 htheta₂.2,
    ← Real.arccos_cos htheta₁.1 htheta₁.2]
  exact Real.arccos_le_arccos hcos

omit [T2Space (TangentBundle I M)] in
theorem riemannianComparisonAngle_antitoneOn_fst_of_realizedConnectors
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {o : M} {alpha beta : ℝ → M} {A B : ℝ}
    (hA : 0 < A)
    (halpha : UnitSpeedGeodesicOn (I := I) g alpha (Icc 0 A))
    (halpha_zero : alpha 0 = o)
    (halpha_radial : ∀ s ∈ Icc (0 : ℝ) A,
      riemannianDistance (I := I) g o (alpha s) = s)
    (hbeta_radial : ∀ t ∈ Icc (0 : ℝ) B,
      riemannianDistance (I := I) g o (beta t) = t)
    (hconnectors : ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
      Nonempty (RealizedMinimizingConnector (I := I) g (alpha s) (beta t)))
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) B) :
    AntitoneOn
      (fun s ↦ riemannianComparisonAngle (I := I) g (alpha s) o (beta t))
      (Ioc (0 : ℝ) A) := by
  have hconvex : ∀ u ∈ Icc (0 : ℝ) B,
      ConvexOn ℝ (Icc (0 : ℝ) A)
        (fun s ↦ squaredRiemannianPairDefect (I := I) g alpha beta s u) := by
    intro u hu
    exact squaredRiemannianPairDefect_convexOn_fst g hsec halpha hu hconnectors
  intro s₁ hs₁ s₂ hs₂ hs₁s₂
  exact riemannianComparisonAngle_antitone_fst_of_convex_defect
    g hA halpha_zero halpha_radial hbeta_radial hconvex hconnectors
      hs₁.1 hs₁s₂ hs₂.2 ht.1 ht.2

omit [T2Space (TangentBundle I M)] in
theorem riemannianComparisonAngle_antitoneOn_snd_of_realizedConnectors
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {o : M} {alpha beta : ℝ → M} {A B : ℝ}
    (hB : 0 < B)
    (hbeta : UnitSpeedGeodesicOn (I := I) g beta (Icc 0 B))
    (hbeta_zero : beta 0 = o)
    (halpha_radial : ∀ s ∈ Icc (0 : ℝ) A,
      riemannianDistance (I := I) g o (alpha s) = s)
    (hbeta_radial : ∀ t ∈ Icc (0 : ℝ) B,
      riemannianDistance (I := I) g o (beta t) = t)
    (hconnectors : ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
      Nonempty (RealizedMinimizingConnector (I := I) g (alpha s) (beta t)))
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) A) :
    AntitoneOn
      (fun t ↦ riemannianComparisonAngle (I := I) g (alpha s) o (beta t))
      (Ioc (0 : ℝ) B) := by
  have hconvex : ∀ u ∈ Icc (0 : ℝ) A,
      ConvexOn ℝ (Icc (0 : ℝ) B)
        (fun t ↦ squaredRiemannianPairDefect (I := I) g alpha beta u t) := by
    intro u hu
    exact squaredRiemannianPairDefect_convexOn_snd g hsec hbeta hu hconnectors
  intro t₁ ht₁ t₂ ht₂ ht₁t₂
  exact riemannianComparisonAngle_antitone_snd_of_convex_defect
    g hB hbeta_zero halpha_radial hbeta_radial hconvex hconnectors
      hs.1 hs.2 ht₁.1 ht₁t₂ ht₂.2

omit [T2Space (TangentBundle I M)] in
theorem riemannianComparisonAngle_shortening_of_realizedConnectors
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {o : M} {alpha beta : ℝ → M} {A B s₁ s₂ t₁ t₂ : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (halpha : UnitSpeedGeodesicOn (I := I) g alpha (Icc 0 A))
    (hbeta : UnitSpeedGeodesicOn (I := I) g beta (Icc 0 B))
    (halpha_zero : alpha 0 = o) (hbeta_zero : beta 0 = o)
    (halpha_radial : ∀ s ∈ Icc (0 : ℝ) A,
      riemannianDistance (I := I) g o (alpha s) = s)
    (hbeta_radial : ∀ t ∈ Icc (0 : ℝ) B,
      riemannianDistance (I := I) g o (beta t) = t)
    (hconnectors : ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
      Nonempty (RealizedMinimizingConnector (I := I) g (alpha s) (beta t)))
    (hs₁ : 0 < s₁) (hs₁s₂ : s₁ ≤ s₂) (hs₂A : s₂ ≤ A)
    (ht₁ : 0 < t₁) (ht₁t₂ : t₁ ≤ t₂) (ht₂B : t₂ ≤ B) :
    riemannianComparisonAngle (I := I) g (alpha s₂) o (beta t₂) ≤
      riemannianComparisonAngle (I := I) g (alpha s₁) o (beta t₁) := by
  have hfirst := riemannianComparisonAngle_antitoneOn_fst_of_realizedConnectors
    (I := I) g hsec hA halpha halpha_zero halpha_radial hbeta_radial
      hconnectors ⟨ht₁, ht₁t₂.trans ht₂B⟩
  have hsecond := riemannianComparisonAngle_antitoneOn_snd_of_realizedConnectors
    (I := I) g hsec hB hbeta hbeta_zero halpha_radial hbeta_radial
      hconnectors ⟨hs₁.trans_le hs₁s₂, hs₂A⟩
  exact (hsecond ⟨ht₁, ht₁t₂.trans ht₂B⟩
      ⟨ht₁.trans_le ht₁t₂, ht₂B⟩ ht₁t₂).trans
    (hfirst ⟨hs₁, hs₁s₂.trans hs₂A⟩
      ⟨hs₁.trans_le hs₁s₂, hs₂A⟩ hs₁s₂)

theorem riemannianComparisonAngle_shortening_of_complete
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {o : M} {alpha beta : ℝ → M} {A B s₁ s₂ t₁ t₂ : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (halpha : UnitSpeedGeodesicOn (I := I) g alpha (Icc 0 A))
    (hbeta : UnitSpeedGeodesicOn (I := I) g beta (Icc 0 B))
    (halpha_zero : alpha 0 = o) (hbeta_zero : beta 0 = o)
    (halpha_radial : ∀ s ∈ Icc (0 : ℝ) A,
      riemannianDistance (I := I) g o (alpha s) = s)
    (hbeta_radial : ∀ t ∈ Icc (0 : ℝ) B,
      riemannianDistance (I := I) g o (beta t) = t)
    (hs₁ : 0 < s₁) (hs₁s₂ : s₁ ≤ s₂) (hs₂A : s₂ ≤ A)
    (ht₁ : 0 < t₁) (ht₁t₂ : t₁ ≤ t₂) (ht₂B : t₂ ≤ B) :
    riemannianComparisonAngle (I := I) g (alpha s₂) o (beta t₂) ≤
      riemannianComparisonAngle (I := I) g (alpha s₁) o (beta t₁) := by
  apply riemannianComparisonAngle_shortening_of_realizedConnectors
    (I := I) g hsec hA hB halpha hbeta halpha_zero hbeta_zero
      halpha_radial hbeta_radial
  · intro s _ t _
    exact nonempty_realizedMinimizingConnector_of_complete
      (I := I) g hcomplete (alpha s) (beta t)
  · exact hs₁
  · exact hs₁s₂
  · exact hs₂A
  · exact ht₁
  · exact ht₁t₂
  · exact ht₂B

end DifferentialGeometry.Toponogov
