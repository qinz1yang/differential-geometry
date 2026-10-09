import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.PerelmanV
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.HamiltonJacobi
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PerelmanBracket

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Entropy
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem gradientRicciSoliton_and_hamiltonNormalized_of_hamilton_jacobi
    [I.Boundaryless] [T2Space M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (u : ℝ → M → ℝ)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (flowG S) T) (fun r x => -S.scalar (T - r) x) u)
    (hpos : ∀ r, r ∈ Dr.regular ∩ Set.Ioi (0 : ℝ) → ∀ x, 0 < u r x)
    {t : ℝ} (ht : t ∈ Dr.regular) (htpos : 0 < t)
    (hTt : T - t ∈ D.regular)
    (hHJ : ∀ r, r ∈ Dr.regular → 0 < r → ∀ x : M,
      2 * deriv (fun q => perelmanPotential (Module.finrank ℝ E) q (u q) x) r +
        ((reverseFamily (flowG S) T).metric r).inner x
          (gradientFun (I := I) ((reverseFamily (flowG S) T).metric r)
            (perelmanPotential (Module.finrank ℝ E) r (u r)) x)
          (gradientFun (I := I) ((reverseFamily (flowG S) T).metric r)
            (perelmanPotential (Module.finrank ℝ E) r (u r)) x) -
        S.scalar (T - r) x + perelmanPotential (Module.finrank ℝ E) r (u r) x / r = 0) :
    let G := reverseFamily (flowG S) T
    let f := perelmanPotential (Module.finrank ℝ E) t (u t)
    let hf := potential_slice Dr G (fun r x => -S.scalar (T - r) x) u
      (Module.finrank ℝ E) hu ht htpos (hpos t ⟨ht, htpos⟩)
    gradientRicciSoliton (I := I) (G.metric t) ⟨f, hf⟩ (1 / t) ∧
      hamiltonNormalized (I := I) (G.metric t) ⟨f, hf⟩ (1 / t) := by
  let G := reverseFamily (flowG S) T
  let f := perelmanPotential (Module.finrank ℝ E) t (u t)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    potential_slice Dr G (fun r x => -S.scalar (T - r) x) u
      (Module.finrank ℝ E) hu ht htpos (hpos t ⟨ht, htpos⟩)
  have hVzero : ∀ r, r ∈ Dr.regular → 0 < r → ∀ y : M,
      perelmanV G (fun q z => S.scalar (T - q) z) u r y = 0 := by
    intro r hr hrpos y
    have hb := perelman_bracket_eq_zero_of_hamilton_jacobi
      Dr G (fun q z => S.scalar (T - q) z) u hu hr hrpos
      (hpos r ⟨hr, hrpos⟩) y (hHJ r hr hrpos y)
    dsimp only [perelmanV, gradientAt]
    rw [hb, zero_mul]
  have hVevent : ∀ y : M,
      (fun r => perelmanV G (fun q z => S.scalar (T - q) z) u r y) =ᶠ[𝓝 t]
        (fun _ => 0) := by
    intro y
    filter_upwards [Dr.regular_isOpen.mem_nhds ht, eventually_gt_nhds htpos] with r hr hrpos
    exact hVzero r hr hrpos y
  have hnorm_at (y : M) : normSq0S (G.metric t) y 2
      (metricRicciAt (G.metric t) y +
        hessianSec (metricCov (G.metric t)) (metricCov_smooth (G.metric t)) f hf y -
        (1 / (2 * t)) • metricTensor0S (G.metric t) y) = 0 := by
    have he := (perelman_v_evolution S hS T u hu hpos ht htpos hTt y).deriv
    change deriv (fun r => perelmanV G (fun q z => S.scalar (T - q) z) u r y) t =
      laplacianAt G t (perelmanV G (fun q z => S.scalar (T - q) z) u t) y -
      S.scalar (T - t) y * perelmanV G (fun q z => S.scalar (T - q) z) u t y -
      2 * t * normSq0S (G.metric t) y 2
        (metricRicciAt (G.metric t) y +
          hessianSec (metricCov (G.metric t)) (metricCov_smooth (G.metric t)) f hf y -
          (1 / (2 * t)) • metricTensor0S (G.metric t) y) * u t y at he
    have hd : deriv (fun r => perelmanV G (fun q z => S.scalar (T - q) z) u r y) t = 0 := by
      simpa only [deriv_const] using (hVevent y).deriv_eq
    have hvfield : (perelmanV G (fun q z => S.scalar (T - q) z) u t) = fun _ : M => 0 := by
      funext z
      exact hVzero t ht htpos z
    rw [hd, hvfield] at he
    simp only [laplacianAt, laplacian_const, mul_zero, sub_zero, zero_sub] at he
    have hu0 := hpos t ⟨ht, htpos⟩ y
    have hcoeff : 2 * t * u t y ≠ 0 := ne_of_gt (by positivity)
    have hz : (2 * t * u t y) * normSq0S (G.metric t) y 2
        (metricRicciAt (G.metric t) y +
          hessianSec (metricCov (G.metric t)) (metricCov_smooth (G.metric t)) f hf y -
          (1 / (2 * t)) • metricTensor0S (G.metric t) y) = 0 := by nlinarith
    exact (mul_eq_zero.mp hz).resolve_left hcoeff
  have hsol : gradientRicciSoliton (I := I) (G.metric t) ⟨f, hf⟩ (1 / t) :=
    (DifferentialGeometry.Geometry.gradientRicciSoliton_iff_normSq0S_eq_zero
      (I := I) (G.metric t) ⟨f, hf⟩ (1 / t)).mpr (by
      intro y
      change normSq0S (G.metric t) y 2
        (metricRicciAt (G.metric t) y +
          hessianSec (metricCov (G.metric t)) (metricCov_smooth (G.metric t)) f hf y -
          ((1 / t) / 2) • metricTensor0S (G.metric t) y) = 0
      rw [div_div, mul_comm t 2]
      exact hnorm_at y)
  have hbracket : ∀ y : M,
      t * (2 * ΔG (I := I) (G.metric t) ⟨f, hf⟩ y - normGradSqFun (I := I) (G.metric t) f y +
        metricScalarAt (I := I) (G.metric t) y) + f y - (Module.finrank ℝ E : ℝ) = 0 := by
    intro y
    have hb := perelman_bracket_eq_zero_of_hamilton_jacobi
      Dr G (fun q z => S.scalar (T - q) z) u hu ht htpos
      (hpos t ⟨ht, htpos⟩) y (hHJ t ht htpos y)
    have hlap : laplacianAt G t f y = ΔG (I := I) (G.metric t) ⟨f, hf⟩ y :=
      laplacian_levi_eq (G.metric t) hf y
    change t * (2 * laplacianAt G t f y -
      (G.metric t).inner y (gradientFun (I := I) (G.metric t) f y)
        (gradientFun (I := I) (G.metric t) f y) +
        metricScalarAt (G.metric t) y) + f y - (Module.finrank ℝ E : ℝ) = 0 at hb
    simpa only [hlap, normGradSqFun_def, gradient_eq_gradFun] using hb
  have hham := (DifferentialGeometry.Geometry.gradientRicciSoliton_hamiltonNormalized_iff_perelman_bracket_eq_zero
    (I := I) (g := G.metric t) (f := ⟨f, hf⟩) htpos.ne' hsol).mpr hbracket
  exact ⟨hsol, hham⟩

theorem gradientRicciSoliton_and_hamiltonNormalized_of_conjugate_density_and_hamilton_jacobi
    [I.Boundaryless] [T2Space M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (f : ℝ → M → ℝ)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (flowG S) T) (fun r x => -S.scalar (T - r) x)
      (fun r => perelmanDensity (Module.finrank ℝ E) r (f r)))
    {t : ℝ} (ht : t ∈ Dr.regular) (htpos : 0 < t)
    (hTt : T - t ∈ D.regular)
    (hHJ : ∀ r, r ∈ Dr.regular → 0 < r → ∀ x : M,
      2 * deriv (fun q => f q x) r +
        ((reverseFamily (flowG S) T).metric r).inner x
          (gradientFun (I := I) ((reverseFamily (flowG S) T).metric r) (f r) x)
          (gradientFun (I := I) ((reverseFamily (flowG S) T).metric r) (f r) x) -
        S.scalar (T - r) x + f r x / r = 0) :
    ∃ hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f t),
      gradientRicciSoliton (I := I) ((reverseFamily (flowG S) T).metric t)
        ⟨f t, hf⟩ (1 / t) ∧
      hamiltonNormalized (I := I) ((reverseFamily (flowG S) T).metric t)
        ⟨f t, hf⟩ (1 / t) := by
  let u := fun r => perelmanDensity (Module.finrank ℝ E) r (f r)
  have hpos : ∀ r, r ∈ Dr.regular ∩ Set.Ioi (0 : ℝ) → ∀ x, 0 < u r x := by
    intro r hr x
    exact mul_pos (prefactor_pos (Module.finrank ℝ E) hr.2) (Real.exp_pos _)
  have hHJ' : ∀ r, r ∈ Dr.regular → 0 < r → ∀ x : M,
      2 * deriv (fun q => perelmanPotential (Module.finrank ℝ E) q (u q) x) r +
        ((reverseFamily (flowG S) T).metric r).inner x
          (gradientFun (I := I) ((reverseFamily (flowG S) T).metric r)
            (perelmanPotential (Module.finrank ℝ E) r (u r)) x)
          (gradientFun (I := I) ((reverseFamily (flowG S) T).metric r)
            (perelmanPotential (Module.finrank ℝ E) r (u r)) x) -
        S.scalar (T - r) x + perelmanPotential (Module.finrank ℝ E) r (u r) x / r = 0 := by
    intro r hr hrpos x
    have he : (fun q => perelmanPotential (Module.finrank ℝ E) q (u q) x) =ᶠ[𝓝 r]
        (fun q => f q x) := by
      filter_upwards [eventually_gt_nhds hrpos] with q hq
      exact congrFun (potential_density (Module.finrank ℝ E) hq (f q)) x
    have hd := he.deriv_eq
    simpa only [hd, u, potential_density (Module.finrank ℝ E) hrpos] using hHJ r hr hrpos x
  have h := gradientRicciSoliton_and_hamiltonNormalized_of_hamilton_jacobi
    S hS T u hu hpos ht htpos hTt hHJ'
  have he : perelmanPotential (Module.finrank ℝ E) t (u t) = f t :=
    potential_density (Module.finrank ℝ E) htpos (f t)
  have hf := potential_slice Dr (reverseFamily (flowG S) T)
    (fun r x => -S.scalar (T - r) x) u (Module.finrank ℝ E) hu ht htpos (hpos t ⟨ht, htpos⟩)
  have hf' : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f t) := he ▸ hf
  refine ⟨hf', ?_⟩
  have hb : (⟨perelmanPotential (Module.finrank ℝ E) t (u t), hf⟩ :
      ContMDiffMap I 𝓘(ℝ, ℝ) M ℝ ∞) = ⟨f t, hf'⟩ := by
    ext x
    exact congrFun he x
  change gradientRicciSoliton (I := I) ((reverseFamily (flowG S) T).metric t)
      ⟨perelmanPotential (Module.finrank ℝ E) t (u t), hf⟩ (1 / t) ∧
    hamiltonNormalized (I := I) ((reverseFamily (flowG S) T).metric t)
      ⟨perelmanPotential (Module.finrank ℝ E) t (u t), hf⟩ (1 / t) at h
  rw [hb] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Entropy
