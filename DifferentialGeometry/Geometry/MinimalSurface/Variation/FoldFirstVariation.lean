import DifferentialGeometry.Geometry.Measure.Area.DiskPatchFirstVariation
import DifferentialGeometry.Geometry.Measure.Area.IsotopyFirstVariation
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskDivergence

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

private theorem sourceSectionCovariantDerivative_ambient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U z)
    (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E p (Y p))) (v : ℂ) :
    sourceSectionCovariantDerivative g U (fun q => Y (U q)) z v =
      (leviCivitaConnectionOfMetric g) Y (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) := by
  let line : ℝ → ℂ := fun t => z + t • v
  have hl : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t => U (line t)) 0 :=
    (show ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U (line 0) by simpa [line] using hU).comp 0
      (hl.contMDiff.contMDiffAt.of_le (by simp))
  have hX : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun p => TotalSpace.mk' E p (Y p)) (U (line 0)) :=
    hY.mdifferentiable (by simp) (U (line 0))
  have hvel : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => U (line t)) 0 (1 : ℝ) : E) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v :=
    source_mfderiv_line (I := 𝓘(ℝ, E)) (r := U)
      (hU.mdifferentiableAt (by simp)) v
  have hchain :
      (covDerivAlong (I := 𝓘(ℝ, E)) g (fun t => U (line t))
        (fun t => Y (U (line t))) 0 : E) =
      (leviCivitaConnectionOfMetric g) Y (U (line 0))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => U (line t)) 0 (1 : ℝ)) :=
    covDerivAlong_eq_leviCivita_of_eventuallyEq (I := 𝓘(ℝ, E))
      (X := Y) (V := fun t => Y (U (line t)))
      g (fun t => U (line t)) 0 hγ hX (Eventually.of_forall (fun _ => rfl))
  change (covDerivAlong (I := 𝓘(ℝ, E)) g (fun t => U (line t))
    (fun t => Y (U (line t))) 0 : E) = _
  rw [hchain, hvel]
  let A : M → E →L[ℝ] E := fun p => (leviCivitaConnectionOfMetric g) Y p
  change A (U (line 0)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) =
    A (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v)
  have hline0 : line 0 = z := by simp only [line, zero_smul, add_zero]
  rw [hline0]

private theorem fold_gram_density_eq_ambient_divergence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΦzero : ∀ x, Φ 0 x = x)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    (hvelocity : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = Y x)
    {U : ℂ → M} {S H : Set ℂ} (hS : IsOpen S)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U S)
    {z : ℂ} (hz : z ∈ S) (hH : H ∈ 𝓝 z)
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    diskMapGramMetricVariationDensity
        (fun t => Diffeomorph.pullbackMetric g (Φ t)) 0 U z =
      ambientDivergenceWithin g U H Y z := by
  have hΦ₀ : Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) M ∞ := by
    ext x
    exact hΦzero x
  rw [diskMapGramMetricVariationDensity_pullback_eq_tangentTrace
    g Φ hΦ hΦ₀ Y hvelocity hS hU hz hi]
  have hw (v : ℂ) : partialWithin (E := E) U H z v = diskMapPartial U z v := by
    exact congrArg (fun L : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (U z) => L v)
      (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) (f := U) hH)
  have hzU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U z :=
    ((hU z hz).contMDiffAt (hS.mem_nhds hz)).of_le (by simp)
  simp only [ambientDivergenceWithin, gramWithin, densityWithin,
    ambientPartialWithin, hw, sourceSectionCovariantDerivative_ambient g hzU Y hY,
    riemannianAreaDensity, diskMapPartial]

/-- The actual area derivative of a folded disk patch is the sum of its two
ambient divergence integrals. The lower sheet is the literal reflected
restriction of the same disk. Smoothness is required only on the open halves,
so no differentiability across the fold is assumed. -/
theorem hasDerivAt_riemannianArea_isotopy_of_fold
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΦzero : ∀ x, Φ 0 x = x)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    (hvelocity : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = Y x)
    (p r : ℝ)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ conj)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hi : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hir : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) z)) :
    let U := diskExtension u
    let S := Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}
    let H := closedHalfDisk p r
    IntegrableOn (ambientDivergenceWithin g U H Y) S ∧
      IntegrableOn (ambientDivergenceWithin g (U ∘ conj) H Y) S ∧
      HasDerivAt (fun t => riemannianArea g ((Φ t) ∘ U)
        (Metric.closedBall (p : ℂ) r))
        ((∫ z in S, ambientDivergenceWithin g U H Y z) +
          ∫ z in S, ambientDivergenceWithin g (U ∘ conj) H Y z) 0 := by
  dsimp only
  let S := Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}
  let H := closedHalfDisk p r
  have hS : IsOpen S := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hSH : S ⊆ H := fun z hz =>
    ⟨(show 0 < z.im from hz.2).le, Metric.ball_subset_closedBall hz.1⟩
  have heq (F : ℂ → M)
      (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F S)
      (hiF : ∀ z ∈ S, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z)) :
      EqOn (diskMapGramMetricVariationDensity
        (fun t => Diffeomorph.pullbackMetric g (Φ t)) 0 F)
        (ambientDivergenceWithin g F H Y) S := by
    intro z hz
    exact fold_gram_density_eq_ambient_divergence g Φ hΦ hΦzero Y hY hvelocity
      hS hF hz (mem_of_superset (hS.mem_nhds hz) hSH) (hiF z hz)
  have heqU := heq (diskExtension u) hU hi
  have heqUr := heq (diskExtension u ∘ conj) hUr hir
  obtain ⟨hQU, hQUr, hd⟩ := hasDerivAt_riemannianArea_isotopy_of_halfDisk_immersion
    g u huLip Φ hΦ hΦzero p r (hU.of_le (by simp)) (hUr.of_le (by simp)) hi hir
  refine ⟨hQU.congr_fun heqU hS.measurableSet,
    hQUr.congr_fun heqUr hS.measurableSet, ?_⟩
  have hIU := setIntegral_congr_fun (μ := volume) hS.measurableSet heqU
  have hIUr := setIntegral_congr_fun (μ := volume) hS.measurableSet heqUr
  rw [hIU, hIUr] at hd
  exact hd

end DifferentialGeometry.Geometry
