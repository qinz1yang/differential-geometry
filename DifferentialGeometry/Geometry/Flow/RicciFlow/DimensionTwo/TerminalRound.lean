import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Backward.SurfaceHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceMetricEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

noncomputable section
open Set
open DifferentialGeometry.Analysis.Parabolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

theorem surface_scalar_eq_profile_of_terminal_constant
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2) {a b σ : ℝ} (hab : a < b) (hσ : 0 ≤ σ)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hterminal : ∀ x, S.scalar b x = σ) :
    ∀ t ∈ Icc a b, ∀ x, S.scalar t x = σ / (1 + σ * (b - t)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let U := S.timeRestrict (RealTimeInterval.closed a b hab.le)
  have hU : IsSolutionOn U := isSolutionOn_timeRestrict hS hcar hreg
  let r := fun t : ℝ => σ / (1 + σ * (b - t))
  have hden (t : ℝ) (ht : t ≤ b) : 0 < 1 + σ * (b - t) := by
    have hh : 0 ≤ σ * (b - t) := mul_nonneg hσ (sub_nonneg.mpr ht)
    linarith
  have hrderiv (t : ℝ) (ht : t ≤ b) : HasDerivAt r ((r t)^2) t := by
    have hd := (((hasDerivAt_const t b).sub (hasDerivAt_id t)).const_mul σ).const_add 1
    have h := (hasDerivAt_const t σ).div hd (hden t ht).ne'
    have hv : (0 * (1 + σ * (b - t)) - σ * (σ * (0 - 1))) / (1 + σ * (b - t)) ^ 2 = (r t) ^ 2 := by
      dsimp only [r]
      rw [div_pow]
      ring
    exact h.congr_deriv hv
  have hrcont : ContinuousOn r (Icc a b) :=
    continuousOn_const.div (continuousOn_const.add
      (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))) (fun t ht => (hden t ht.2).ne')
  have hrjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => r p.1) (Ioo a b ×ˢ univ) := by
    dsimp only [r]
    have hd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => 1 + σ * (b - p.1)) (Ioo a b ×ˢ univ) :=
      contMDiffOn_const.add (contMDiffOn_const.mul (contMDiffOn_const.sub contMDiffOn_fst))
    exact ContMDiffOn.div₀ contMDiffOn_const hd (fun p hp => (hden p.1 hp.1.2.le).ne')
  let u := fun t x => U.scalar t x - r t
  let V := fun t x => U.scalar t x + r t
  have hu : IsHeatPotOn (RealTimeInterval.closed a b hab.le) (flowG U) V u := by
    refine ⟨(scalar_joint U hU).sub hrjoint,?_,?_,?_⟩
    · exact hU.scalarCont.sub (hrcont.comp continuousOn_fst (fun _ hp => hp.1))
    · intro t ht
      exact (scalarSmoothOfSolution U t).sub contMDiff_const
    · intro t ht x
      have hd := (Perelman.KappaSolutions.surfaceScalar_hasDerivAt U hU hdim ht x).sub
        (hrderiv t ht.2.le)
      have hlap : laplacianAt (flowG U) t (u t) x =
          ΔG (U.family.metric t) ⟨U.scalar t, scalarSmoothOfSolution U t⟩ x := by
        change laplacian (LeviCivita (U.family.metric t)) (U.family.metric t)
          (fun y => U.scalar t y - r t) x = _
        rw [laplacian_sub_const (LeviCivita (U.family.metric t)) (U.family.metric t)
          (r t) ((scalarSmoothOfSolution U t).mdifferentiable (by simp)) x]
        exact laplacian_levi_eq (U.family.metric t) (scalarSmoothOfSolution U t) x
      apply hd.congr_deriv
      rw [hlap]
      dsimp only [V,u]
      ring
  have hVcont : ContinuousOn (fun p : ℝ × M => V p.1 p.2) (Icc a b ×ˢ univ) :=
    hU.scalarCont.add (hrcont.comp continuousOn_fst (fun _ hp => hp.1))
  have hz := heat_potential_eq_zero_of_terminal_eq_zero_on_surface U hU hdim hu hab
    Subset.rfl Subset.rfl hVcont
    (fun t _ => (scalarSmoothOfSolution U t).add contMDiff_const)
    (fun x => by simp only [u,r,show U.scalar b x = S.scalar b x from rfl,hterminal,sub_self,mul_zero,add_zero,div_one])
  intro t ht x
  exact sub_eq_zero.mp (hz t ht x)

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

theorem surface_metric_eq_scale_of_terminal_scalar_constant
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2) {a b σ : ℝ} (hab : a < b) (hσ : 0 ≤ σ)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hterminal : ∀ x, S.scalar b x = σ) :
    ∀ t ∈ Icc a b, ∀ x (v w : TangentSpace I x),
      (S.family.metric t).inner x v w =
        (1 + σ * (b - t)) * (S.family.metric b).inner x v w := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hR := surface_scalar_eq_profile_of_terminal_constant S hS hdim hab hσ hcar hreg hterminal
  intro t ht x v w
  let f := fun t => (S.family.metric t).inner x v w
  let den := fun t : ℝ => 1 + σ * (b - t)
  have hden (s : ℝ) (hs : s ≤ b) : 0 < den s := by
    dsimp only [den]
    have h := mul_nonneg hσ (sub_nonneg.mpr hs)
    linarith
  let ratio := fun s => f s / den s
  have hcont : ContinuousOn ratio (Icc a b) :=
    (hS.smoothMetric.coeff_cont x v w |>.mono hcar).div
      (continuous_const.add (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
      (fun s hs => (hden s hs.2).ne')
  have hderiv (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt ratio 0 s := by
    have hd := Perelman.KappaSolutions.surfaceMetric_hasDerivAt S hS hdim (hreg hs) x v w
    rw [hR s (Ioo_subset_Icc_self hs) x] at hd
    have hden' := (((hasDerivAt_const s b).sub (hasDerivAt_id s)).const_mul σ).const_add 1
    have hquot := hd.fun_div hden' (hden s hs.2.le).ne'
    apply hquot.congr_deriv
    simp only [Pi.sub_apply,id_eq]
    have hn : 1 + σ * (b - s) ≠ 0 := (hden s hs.2.le).ne'
    field_simp [hn]
    ring
  have hmono : MonotoneOn ratio (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont
    (fun s hs => (hderiv s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hderiv s (by simpa only [interior_Icc] using hs)).deriv])
  have hanti : AntitoneOn ratio (Icc a b) := antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont
    (fun s hs => (hderiv s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hderiv s (by simpa only [interior_Icc] using hs)).deriv])
  have heq : ratio t = ratio b := le_antisymm
    (hmono ht ⟨hab.le,le_rfl⟩ ht.2) (hanti ht ⟨hab.le,le_rfl⟩ ht.2)
  dsimp only [ratio,den] at heq
  simp only [sub_self,mul_zero,add_zero,div_one] at heq
  exact (div_eq_iff (hden t ht.2).ne').mp heq |>.trans (mul_comm _ _)

end DifferentialGeometry.PDE.RicciFlow
