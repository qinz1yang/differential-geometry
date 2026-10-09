import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5PotentialLaplacian
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5PotentialCalculus
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Analysis.Elliptic.Poisson
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.ArbitraryTest
import DifferentialGeometry.Analysis.Elliptic.Regularity.Bochner.Polarised

/-!
# The potential family of a surface Ricci flow

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (i) (potential gauge, design D18,
errata "route change for (i)"). With `T* = A₀ / C₀` and `r = 1 / (T* - t)`:
* `surfaceFlow_poissonRHS_integral_eq_zero`: `∫ (R - r) dμ_{g(t)} = 0` on `[0, T)`;
* `surfaceFlow_exists_ode_potential`: for `t₀ = T / 2`, `F₀` the mean-zero solution of
  `Δ F₀ = R(t₀) - r(t₀)` and `E(t) = (T* - t₀) / (T* - t)`, the function
  `F = E (F₀ + ∫_{t₀}^t E⁻¹ R)` is jointly smooth on `(0, T) × M` with `∂ₜ F = R + r F`. The
  defect `P = Δ F - (R - r)` satisfies `∂ₜ P = (R + r) P` (`surfaceFlow_ΔG_hasDerivAt`,
  `surfaceScalar_hasDerivAt`, `r' = r²`) and `P(t₀) = 0`, so `Δ F = R - r` on `(0, T)`;
* `surfaceFlow_exists_potential_family`: design D18 (i). Subtract the moving mean
  `m = A⁻¹ ∫ F dμ_{g(t)}`, which is smooth by `surfaceFlow_contDiffOn_integral`, and take
  `a = r m - m'`; at `t = 0` use the static solution.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open MeasureTheory Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  {T : ℝ} {hT : 0 < T}

private local instance potentialFamilyMeasurable : MeasurableSpace M := borel M
private local instance potentialFamilyBorel : BorelSpace M := ⟨rfl⟩
private local instance potentialFamilyComplete : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance potentialFamilyOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
theorem ΔG_add_const_mul (g : SmoothRiemannianMetric I M) (u v : C^∞⟮I, M; ℝ⟯) (c : ℝ)
    (huv : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => u y + c * v y)) (x : M) :
    ΔG g ⟨fun y => u y + c * v y, huv⟩ x = ΔG g u x + c * ΔG g v x := by
  let w : C^∞⟮I, M; ℝ⟯ := ⟨(fun _ => c) * (v : M → ℝ), contMDiff_const.mul v.contMDiff⟩
  have h1 : (⟨fun y => u y + c * v y, huv⟩ : C^∞⟮I, M; ℝ⟯) = u + w := by
    ext y
    rfl
  have hgc : gradFun g (fun _ : M => c) x = 0 := gradFun_const g c x
  have hΔc : ΔG g ⟨fun _ : M => c, contMDiff_const⟩ x = 0 := Δ_g_const g c x
  have h2 : ΔG g w x = c * ΔG g v x := by
    have h := Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral.Δ_g_smul_eq g
      (φ := fun _ : M => c) contMDiff_const v.contMDiff x
    rw [hgc, hΔc] at h
    simp only [map_zero, zero_apply, mul_zero, add_zero] at h
    exact h
  rw [h1, Δ_g_add, h2]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
theorem ΔG_sub_const_eq (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; ℝ⟯) (c : ℝ)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => u y - c)) (x : M) :
    ΔG g ⟨fun y => u y - c, hu⟩ x = ΔG g u x := by
  have h := Analysis.Laplacian.BochnerPolarised.Δ_g_sub g (f := u) (h := fun _ : M => c)
    u.contMDiff contMDiff_const hu x
  have hc : ΔG g ⟨fun _ : M => c, contMDiff_const⟩ x = 0 := Δ_g_const g c x
  rw [h, hc, sub_zero]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem surfaceFlow_extinction_sub_pos (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    0 < flowExtinctionTime S - t := by
  exact sub_pos.mpr (surfaceFlow_lt_extinctionTime hT S hS hdim hscal ht)

omit [NeZero (Module.finrank ℝ E)] in
theorem surfaceFlow_poissonRHS_integral_eq_zero (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    (∫ x, (S.scalar t x - 1 / (flowExtinctionTime S - t))
      ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 := by
  let μ := riemannianVolumeMeasure I M (S.family.metric t)
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) _
  have hint : Integrable (S.scalar t) μ :=
    (scalarSmoothOfSolution S t).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC := totalScalarCurvature_pos (S.family.metric 0) hscal
  have hpos := surfaceFlow_extinction_sub_pos hdim S hS hscal ht
  rw [integral_sub hint (integrable_const _), integral_const, smul_eq_mul]
  have hR : (∫ x, S.scalar t x ∂μ) = totalScalarCurvature (S.family.metric t) := rfl
  have hA : μ.real univ = surfaceArea (S.family.metric t) := rfl
  change (∫ x, S.scalar t x ∂μ) - μ.real univ * _ = 0
  rw [hR, hA, surfaceFlow_totalScalarCurvature_eq_initial hT S hS hdim ht,
    surfaceFlow_area_eq_initial_sub hT S hS hdim ht]
  unfold flowExtinctionTime at hpos ⊢
  set A₀ := surfaceArea (S.family.metric 0)
  set C := totalScalarCurvature (S.family.metric 0)
  have hA' : A₀ - C * t = C * (A₀ / C - t) := by
    field_simp
  rw [hA', mul_assoc, mul_one_div_cancel hpos.ne', mul_one, sub_self]

theorem surfaceFlow_exists_static_potential (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    ∃ u : C^∞⟮I, M; ℝ⟯, (∫ x, u x ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 ∧
      ∀ x, ΔG (S.family.metric t) u x = S.scalar t x - 1 / (flowExtinctionTime S - t) := by
  let q : C^∞⟮I, M; ℝ⟯ := ⟨fun x => S.scalar t x - 1 / (flowExtinctionTime S - t),
    (scalarSmoothOfSolution S t).sub contMDiff_const⟩
  obtain ⟨u, hu, -⟩ := existsUnique_meanZero_smooth_poisson (S.family.metric t) q
    (surfaceFlow_poissonRHS_integral_eq_zero hdim S hS hscal ht)
  exact ⟨u, hu.1, hu.2⟩

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem surfaceFlow_poisson_defect_hasDerivAt (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (u : ℝ → C^∞⟮I, M; ℝ⟯)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => u q.1 q.2) (Ioo 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hpos : 0 < flowExtinctionTime S - t)
    (hd : ∀ y, HasDerivAt (fun s => u s y)
      (S.scalar t y + 1 / (flowExtinctionTime S - t) * u t y) t) (x : M) :
    HasDerivAt (fun s => ΔG (S.family.metric s) (u s) x -
        (S.scalar s x - 1 / (flowExtinctionTime S - s)))
      ((S.scalar t x + 1 / (flowExtinctionTime S - t)) *
        (ΔG (S.family.metric t) (u t) x - (S.scalar t x - 1 / (flowExtinctionTime S - t)))) t := by
  set Tst := flowExtinctionTime S
  let R : C^∞⟮I, M; ℝ⟯ := ⟨S.scalar t, scalarSmoothOfSolution S t⟩
  have hut : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => R y + 1 / (Tst - t) * u t y) :=
    R.contMDiff.add (contMDiff_const.mul (u t).contMDiff)
  let ut : C^∞⟮I, M; ℝ⟯ := ⟨fun y => R y + 1 / (Tst - t) * u t y, hut⟩
  have hΔ := surfaceFlow_ΔG_hasDerivAt hdim S hS u hu ut ht hd x
  have hΔut : ΔG (S.family.metric t) ut x =
      ΔG (S.family.metric t) R x + 1 / (Tst - t) * ΔG (S.family.metric t) (u t) x :=
    ΔG_add_const_mul (S.family.metric t) R (u t) (1 / (Tst - t)) hut x
  have hRd := surfaceScalar_hasDerivAt S hS hdim (D := RealTimeInterval.closedOpen 0 T hT)
    (t := t) ht x
  have hne : Tst - t ≠ 0 := hpos.ne'
  have hrd : HasDerivAt (fun s => 1 / (Tst - s)) (1 / (Tst - t) ^ 2) t := by
    have h1 : HasDerivAt (fun s => Tst - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub Tst
    have h2 := (h1.inv hne).congr_deriv (show -(-1) / (Tst - t) ^ 2 = 1 / (Tst - t) ^ 2 by ring)
    simpa only [one_div, Pi.inv_def] using h2
  refine (hΔ.sub (hRd.sub hrd)).congr_deriv ?_
  have e1 : ΔG (S.family.metric t) ⟨S.scalar t, scalarSmoothOfSolution S t⟩ x =
      ΔG (S.family.metric t) R x := rfl
  have e3 : 1 / (Tst - t) ^ 2 = (1 / (Tst - t)) ^ 2 := by rw [one_div_pow]
  rw [hΔut, e1, e3]
  ring

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem surfaceFlow_poisson_of_ode (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hTst : T ≤ flowExtinctionTime S) (u : ℝ → C^∞⟮I, M; ℝ⟯)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => u q.1 q.2) (Ioo 0 T ×ˢ univ))
    (hd : ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun s => u s y)
      (S.scalar t y + 1 / (flowExtinctionTime S - t) * u t y) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T)
    (h₀ : ∀ x, ΔG (S.family.metric t₀) (u t₀) x =
      S.scalar t₀ x - 1 / (flowExtinctionTime S - t₀)) :
    ∀ t ∈ Ioo 0 T, ∀ x, ΔG (S.family.metric t) (u t) x =
      S.scalar t x - 1 / (flowExtinctionTime S - t) := by
  intro t ht x
  have hpos : ∀ s ∈ Ioo 0 T, 0 < flowExtinctionTime S - s := fun s hs =>
    sub_pos.mpr (hs.2.trans_le hTst)
  have hj : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => S.scalar p.1 p.2)
      (Ioo 0 T ×ˢ univ) := scalar_joint S hS
  have hRc : ContinuousOn (fun s => S.scalar s x) (Ioo 0 T) := by
    have hc := hj.continuousOn.comp
      (Continuous.continuousOn (f := fun s : ℝ => (s, x)) (continuous_id.prodMk continuous_const))
      (fun s hs => ⟨hs, mem_univ x⟩)
    exact hc
  have hrc : ContinuousOn (fun s => 1 / (flowExtinctionTime S - s)) (Ioo 0 T) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id) (fun s hs => (hpos s hs).ne')
  have hP0 : ΔG (S.family.metric t₀) (u t₀) x -
      (S.scalar t₀ x - 1 / (flowExtinctionTime S - t₀)) = 0 := by
    rw [h₀ x, sub_self]
  have hz := eqOn_zero_of_hasDerivAt_mul (P := fun s => ΔG (S.family.metric s) (u s) x -
      (S.scalar s x - 1 / (flowExtinctionTime S - s)))
    (k := fun s => S.scalar s x + 1 / (flowExtinctionTime S - s)) ht₀ (hRc.add hrc)
    (fun s hs => surfaceFlow_poisson_defect_hasDerivAt hdim S hS u hu hs (hpos s hs) (hd s hs) x)
    hP0 t ht
  exact sub_eq_zero.mp hz

def surfaceFlowOdePotential
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (F₀ : C^∞⟮I, M; ℝ⟯) (t₀ t : ℝ) (x : M) : ℝ :=
  (flowExtinctionTime S - t₀) / (flowExtinctionTime S - t) *
    (F₀ x + ∫ s in t₀..t,
      S.scalar s x * ((flowExtinctionTime S - s) / (flowExtinctionTime S - t₀)))

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem surfaceFlowOdePotential_contMDiffOn
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hTst : T ≤ flowExtinctionTime S) (F₀ : C^∞⟮I, M; ℝ⟯) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => surfaceFlowOdePotential S F₀ t₀ q.1 q.2) (Ioo 0 T ×ˢ univ) := by
  set Tst := flowExtinctionTime S
  have hj : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => S.scalar p.1 p.2)
      (Ioo 0 T ×ˢ univ) := scalar_joint S hS
  have hw : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (Tst - p.1) / (Tst - t₀)) :=
    ((contDiff_const.sub contDiff_id).div_const (Tst - t₀)).contMDiff.comp contMDiff_fst
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => S.scalar p.1 p.2 * ((Tst - p.1) / (Tst - t₀))) (Ioo 0 T ×ˢ univ) :=
    hj.mul hw.contMDiffOn
  have hI := contMDiffOn_intervalIntegral_time ht₀
    (fun s x => S.scalar s x * ((Tst - s) / (Tst - t₀))) hG
  have hEc : ContDiffOn ℝ ∞ (fun t : ℝ => (Tst - t₀) / (Tst - t)) (Ioo 0 T) :=
    contDiffOn_const.div (contDiffOn_const.sub contDiffOn_id)
      (fun t ht => (sub_pos.mpr (ht.2.trans_le hTst)).ne')
  have hE : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (Tst - t₀) / (Tst - p.1)) (Ioo 0 T ×ˢ univ) :=
    hEc.contMDiffOn.comp contMDiff_fst.contMDiffOn (fun p hp => hp.1)
  have hF₀ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => F₀ p.2) :=
    F₀.contMDiff.comp contMDiff_snd
  exact hE.mul (hF₀.contMDiffOn.add hI)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem surfaceFlowOdePotential_hasDerivAt
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hTst : T ≤ flowExtinctionTime S) (F₀ : C^∞⟮I, M; ℝ⟯) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : M) :
    HasDerivAt (fun s => surfaceFlowOdePotential S F₀ t₀ s x)
      (S.scalar t x + 1 / (flowExtinctionTime S - t) * surfaceFlowOdePotential S F₀ t₀ t x) t := by
  set Tst := flowExtinctionTime S
  have hne : Tst - t ≠ 0 := (sub_pos.mpr (ht.2.trans_le hTst)).ne'
  have hne₀ : Tst - t₀ ≠ 0 := (sub_pos.mpr (ht₀.2.trans_le hTst)).ne'
  have hj : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => S.scalar p.1 p.2)
      (Ioo 0 T ×ˢ univ) := scalar_joint S hS
  have hRc : ContinuousOn (fun s => S.scalar s x) (Ioo 0 T) := by
    have hc := hj.continuousOn.comp
      (Continuous.continuousOn (f := fun s : ℝ => (s, x)) (continuous_id.prodMk continuous_const))
      (fun s hs => ⟨hs, mem_univ x⟩)
    exact hc
  have hGc : ContinuousOn (fun s => S.scalar s x * ((Tst - s) / (Tst - t₀))) (Ioo 0 T) :=
    hRc.mul ((continuousOn_const.sub continuousOn_id).div_const _)
  have hsub : uIcc t₀ t ⊆ Ioo 0 T := ordConnected_Ioo.uIcc_subset ht₀ ht
  have hId : HasDerivAt (fun s => ∫ τ in t₀..s, S.scalar τ x * ((Tst - τ) / (Tst - t₀)))
      (S.scalar t x * ((Tst - t) / (Tst - t₀))) t :=
    intervalIntegral.integral_hasDerivAt_right ((hGc.mono hsub).intervalIntegrable)
      (hGc.stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hGc.continuousAt (isOpen_Ioo.mem_nhds ht))
  have hEd : HasDerivAt (fun s => (Tst - t₀) / (Tst - s)) ((Tst - t₀) / (Tst - t) ^ 2) t := by
    have h1 : HasDerivAt (fun s => Tst - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub Tst
    have h2 := ((h1.inv hne).const_mul (Tst - t₀)).congr_deriv
      (show (Tst - t₀) * (-(-1) / (Tst - t) ^ 2) = (Tst - t₀) / (Tst - t) ^ 2 by ring)
    simpa only [div_eq_mul_inv, Pi.inv_def] using h2
  have h := hEd.mul ((hasDerivAt_const t (F₀ x)).add hId)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, zero_add]
  have hP : surfaceFlowOdePotential S F₀ t₀ t x = (Tst - t₀) / (Tst - t) *
      (F₀ x + ∫ τ in t₀..t, S.scalar τ x * ((Tst - τ) / (Tst - t₀))) := rfl
  rw [hP]
  generalize (∫ τ in t₀..t, S.scalar τ x * ((Tst - τ) / (Tst - t₀))) = J
  field_simp
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem surfaceFlowOdePotential_self
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hTst : T ≤ flowExtinctionTime S) (F₀ : C^∞⟮I, M; ℝ⟯) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) (x : M) :
    surfaceFlowOdePotential S F₀ t₀ t₀ x = F₀ x := by
  have hne₀ : flowExtinctionTime S - t₀ ≠ 0 := (sub_pos.mpr (ht₀.2.trans_le hTst)).ne'
  simp only [surfaceFlowOdePotential, intervalIntegral.integral_same, add_zero, div_self hne₀,
    one_mul]

theorem surfaceFlow_exists_ode_potential (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) :
    ∃ F : ℝ → C^∞⟮I, M; ℝ⟯,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => F q.1 q.2) (Ioo 0 T ×ˢ univ) ∧
      (∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => F s x)
        (S.scalar t x + 1 / (flowExtinctionTime S - t) * F t x) t) ∧
      ∀ t ∈ Ioo 0 T, ∀ x, ΔG (S.family.metric t) (F t) x =
        S.scalar t x - 1 / (flowExtinctionTime S - t) := by
  have hTst : T ≤ flowExtinctionTime S := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  have ht₀ : T / 2 ∈ Ioo 0 T := ⟨by linarith, by linarith⟩
  obtain ⟨F₀, -, hF₀⟩ := surfaceFlow_exists_static_potential hdim S hS hscal ⟨ht₀.1.le, ht₀.2⟩
  have hΦ := surfaceFlowOdePotential_contMDiffOn S hS hTst F₀ ht₀
  have hslice : ∀ t ∈ Ioo 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (surfaceFlowOdePotential S F₀ (T / 2) t) := by
    intro t ht x
    have hat := hΦ.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (show (t, x) ∈ Ioo 0 T ×ˢ univ from ⟨ht, mem_univ x⟩))
    exact hat.comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  let F : ℝ → C^∞⟮I, M; ℝ⟯ := fun t =>
    if h : t ∈ Ioo 0 T then ⟨surfaceFlowOdePotential S F₀ (T / 2) t, hslice t h⟩ else F₀
  have hF : ∀ t ∈ Ioo 0 T, ∀ x, F t x = surfaceFlowOdePotential S F₀ (T / 2) t x := by
    intro t ht x
    simp only [F, ht, ↓reduceDIte]
    rfl
  have hFj : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => F q.1 q.2)
      (Ioo 0 T ×ˢ univ) := hΦ.congr (fun q hq => hF q.1 hq.1 q.2)
  have hFd : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => F s x)
      (S.scalar t x + 1 / (flowExtinctionTime S - t) * F t x) t := by
    intro t ht x
    have h := surfaceFlowOdePotential_hasDerivAt S hS hTst F₀ ht₀ ht x
    rw [← hF t ht x] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hF s hs x
  have hFF : F (T / 2) = F₀ := by
    ext x
    rw [hF _ ht₀ x, surfaceFlowOdePotential_self S hTst F₀ ht₀ x]
  have h₀ : ∀ x, ΔG (S.family.metric (T / 2)) (F (T / 2)) x =
      S.scalar (T / 2) x - 1 / (flowExtinctionTime S - T / 2) := by
    intro x
    rw [hFF]
    exact hF₀ x
  exact ⟨F, hFj, hFd, surfaceFlow_poisson_of_ode hdim S hS hTst F hFj hFd ht₀ h₀⟩

theorem surfaceFlow_exists_potential_family (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) :
    ∃ f : ℝ → C^∞⟮I, M; ℝ⟯,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2)
        (Ioo 0 T ×ˢ univ) ∧
      (∀ t ∈ Ico 0 T, (∫ x, f t x ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 ∧
        ∀ x, ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t)) ∧
      ∃ a : ℝ → ℝ, ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => f s x)
        (S.scalar t x + f t x / (flowExtinctionTime S - t) + a t) t := by
  obtain ⟨F, hFj, hFd, hFΔ⟩ := surfaceFlow_exists_ode_potential hdim S hS hscal
  obtain ⟨u₀, hu₀m, hu₀Δ⟩ :=
    surfaceFlow_exists_static_potential hdim S hS hscal (t := 0) ⟨le_rfl, hT⟩
  let num : ℝ → ℝ := fun t => ∫ x, F t x ∂riemannianVolumeMeasure I M (S.family.metric t)
  let den : ℝ → ℝ := fun t => ∫ _x, (1 : ℝ) ∂riemannianVolumeMeasure I M (S.family.metric t)
  let m : ℝ → ℝ := fun t => num t / den t
  have hnum : ContDiffOn ℝ ∞ num (Ioo 0 T) :=
    surfaceFlow_contDiffOn_integral S hS (fun t x => F t x) hFj
  have hden : ContDiffOn ℝ ∞ den (Ioo 0 T) :=
    surfaceFlow_contDiffOn_integral S hS (fun _ _ => 1) contMDiffOn_const
  have hden_eq : ∀ t, den t = (riemannianVolumeMeasure I M (S.family.metric t)).real univ := by
    intro t
    simp only [den, integral_const, smul_eq_mul, mul_one]
  have hden_pos : ∀ t, 0 < den t := fun t => by
    rw [hden_eq]
    exact surfaceArea_pos (I := I) (M := M) (S.family.metric t)
  have hm : ContDiffOn ℝ ∞ m (Ioo 0 T) := hnum.div hden (fun t _ => (hden_pos t).ne')
  let f : ℝ → C^∞⟮I, M; ℝ⟯ := fun t =>
    if t ∈ Ioo 0 T then ⟨fun x => F t x - m t, (F t).contMDiff.sub contMDiff_const⟩ else u₀
  have hf : ∀ t ∈ Ioo 0 T, f t = ⟨fun x => F t x - m t, (F t).contMDiff.sub contMDiff_const⟩ :=
    fun t ht => ite_eq_left ht
  have hf0 : f 0 = u₀ := by
    have h0 : (0 : ℝ) ∉ Ioo 0 T := fun h => lt_irrefl 0 h.1
    simp only [f, h0, ↓reduceIte]
  have hfx : ∀ t ∈ Ioo 0 T, ∀ x, f t x = F t x - m t := fun t ht x => by
    rw [hf t ht]
    rfl
  refine ⟨f, ?_, ?_, ?_⟩
  · refine (hFj.sub (hm.contMDiffOn.comp contMDiff_fst.contMDiffOn (fun p hp => hp.1))).congr ?_
    intro q hq
    exact hfx q.1 hq.1 q.2
  · intro t ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · rw [← h0, hf0]
      exact ⟨hu₀m, hu₀Δ⟩
    have ht' : t ∈ Ioo 0 T := ⟨hpos, ht.2⟩
    rw [hf t ht']
    refine ⟨?_, fun x => (ΔG_sub_const_eq _ (F t) (m t) _ x).trans (hFΔ t ht' x)⟩
    let μ := riemannianVolumeMeasure I M (S.family.metric t)
    let _ : IsFiniteMeasure μ :=
      riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) _
    have hint : Integrable (fun x => F t x) μ :=
      (F t).contMDiff.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    change (∫ x, (F t x - m t) ∂μ) = 0
    rw [integral_sub hint (integrable_const _), integral_const, smul_eq_mul, ← hden_eq t]
    change num t - den t * (num t / den t) = 0
    rw [mul_comm, div_mul_cancel₀ (num t) (hden_pos t).ne', sub_self]
  · refine ⟨fun t => 1 / (flowExtinctionTime S - t) * m t - deriv m t, ?_⟩
    intro t ht x
    have hmd : HasDerivAt m (deriv m t) t :=
      ((hm.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
    have h := (hFd t ht x).sub hmd
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hfx s hs x
    · rw [hfx t ht x]
      ring

end GC.Geometry

end
