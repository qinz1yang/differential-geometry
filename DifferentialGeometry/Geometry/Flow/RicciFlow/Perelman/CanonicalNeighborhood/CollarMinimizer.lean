import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCurveMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AmbientCollarShortening
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs

set_option autoImplicit false
noncomputable section
open Bundle Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [T2Space (TangentBundle I3 M)] [SigmaCompactSpace M]

theorem exists_fixed_collar_minimizer_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 M)
      (F : PartialDiffeomorph IC I3 Cylinder M ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 →
      0 ≤ eps → eps ≤ 1 / 2 → 0 ∈ times → U ⊆ F.source →
      univ ×ˢ Icc (-H₀) H₀ ⊆ U → ∀ p q : Sphere 2,
      ∃ gamma : ℝ → M, gamma 0 = F (p, 0) ∧ gamma 1 = F (q, 0) ∧
        ContMDiff 𝓘(ℝ, ℝ) I3 ∞ gamma ∧
        (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ F '' (univ ×ˢ Icc (-H₀) H₀)) ∧
        metricPathELength (g 0) gamma 0 1 = riemannianEDistOf (g 0) (F (p, 0)) (F (q, 0)) := by
  obtain ⟨H₀, hH₀, htrap⟩ := exists_fixed_ambient_collar_trapping_constants (M := M)
  refine ⟨H₀, hH₀, ?_⟩
  intro C h g F U times order eps cmp hmetric heps hepsHalf hzero hsource hslab p q
  have hcpt : IsCompact (F '' (univ ×ˢ Icc (-H₀) H₀)) :=
    ((isCompact_univ : IsCompact (univ : Set (Sphere 2))).prod isCompact_Icc).image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono (hslab.trans hsource))
  obtain ⟨D, _hD, hshortcuts⟩ := exists_uniform_transverse_shortcuts (M := M)
  have hlevel : ∀ y : Sphere 2, (y, (0 : ℝ)) ∈ U := by
    intro y
    apply hslab
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  obtain ⟨beta, hbeta0, hbeta1, hbeta, _hbetaS, hlength⟩ :=
    hshortcuts C h g F U times order eps 0 cmp hmetric heps (by linarith)
      hzero hsource hlevel p q
  have hdist := edistOf_le_metricPathELength (g 0) (by norm_num : (0 : ℝ) ≤ 1) hbeta
  rw [hbeta0, hbeta1] at hdist
  have hfinite : riemannianEDistOf (g 0) (F (p, 0)) (F (q, 0)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdist.trans hlength)
  apply exists_smooth_minimizer_of_compact_trapping (g 0) hcpt
    (delta := 1 / 2) (by norm_num) hfinite
  intro gamma hsmooth hstart hend hnear
  apply htrap C h g F U times order eps cmp hmetric heps hepsHalf hzero hsource hslab
    p q gamma hsmooth hstart hend
  simpa only [hstart, hend] using hnear

omit [T2Space M] [T2Space (TangentBundle I3 M)] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricPathELength_scaleMetric (g : SmoothRiemannianMetric I3 M)
    {Q : ℝ} (hQ : 0 < Q) (gamma : ℝ → M) (a b : ℝ) :
    metricPathELength (scaleMetric Q hQ g) gamma a b =
      ENNReal.ofReal (Real.sqrt Q) * metricPathELength g gamma a b := by
  rw [metricPathELength_eq, metricPathELength_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s _hs => ?_
  rw [scaleMetric_inner, Real.sqrt_mul hQ.le, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [T2Space (TangentBundle I3 W)] [SigmaCompactSpace W]

theorem exists_finiteHorn_collar_minimizer_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∃ i, ∀ x ∈ H.subend i,
      ∃ (F : PartialDiffeomorph IC I3 Cylinder W ∞) (p : Sphere 2),
        F (p, 0) = x ∧ IsCompact (F '' (univ ×ˢ Icc (-H₀) H₀)) ∧
        ∀ q r : Sphere 2, ∃ gamma : ℝ → W,
          gamma 0 = F (q, 0) ∧ gamma 1 = F (r, 0) ∧
          ContMDiff 𝓘(ℝ, ℝ) I3 ∞ gamma ∧
          (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ F '' (univ ×ˢ Icc (-H₀) H₀)) ∧
          metricPathELength g gamma 0 1 = riemannianEDistOf g (F (q, 0)) (F (r, 0)) := by
  obtain ⟨H₀, hH₀, hminimize⟩ := exists_fixed_collar_minimizer_depth (M := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth
  obtain ⟨i, htail⟩ := H.cylindrical_tail
  refine ⟨i, ?_⟩
  intro x hx
  obtain ⟨C, F, p, hcenter, _hsection, hsource, hQ, ⟨cmp⟩⟩ := htail x hx
  have hsubset : (univ ×ˢ Icc (-H₀) H₀ : Set Cylinder) ⊆
      univ ×ˢ Icc (-H.collar_depth) H.collar_depth := by
    intro z hz
    exact ⟨hz.1, ⟨(neg_le_neg hdepth).trans hz.2.1, hz.2.2.trans hdepth⟩⟩
  have hcpt : IsCompact (F '' (univ ×ˢ Icc (-H₀) H₀)) :=
    ((isCompact_univ : IsCompact (univ : Set (Sphere 2))).prod isCompact_Icc).image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono (hsubset.trans hsource))
  refine ⟨F, p, hcenter, hcpt, ?_⟩
  intro q r
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hlength⟩ :=
    hminimize C (fun _ => C.metric 0)
      (fun _ => scaleMetric (metricScalarAt g x) hQ g) F
      (univ ×ˢ Icc (-H.collar_depth) H.collar_depth) {0}
      (⌈H.neck_precision⁻¹⌉₊) H.neck_precision cmp rfl H.neck_precision_pos.le
      (by linarith [H.neck_precision_small]) (by simp) hsource hsubset q r
  refine ⟨gamma, hstart, hend, hsmooth, hmem, ?_⟩
  rw [metricPathELength_scaleMetric, edistOf_scale] at hlength
  exact (ENNReal.mul_right_inj
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hQ)) ENNReal.ofReal_ne_top).mp hlength

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
