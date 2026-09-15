import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Variation.Flow
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import DifferentialGeometry.Geometry.Operator.Laplacian.TimeDerivative
import DifferentialGeometry.Geometry.Operator.LaplacianRegularity
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

noncomputable section
open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem reverseMetric_pair_contMDiffAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (T t : ℝ) (ht : T - t ∈ D.regular)
    (Y Z : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (S.base.metric (T - p.1)).inner p.2 (Y p.2) (Z p.2)) (t, x) := by
  have hp := hS.smoothMetric.pairSmoothAt (x := x) (D.regular_isOpen.mem_nhds ht) ![Y, Z]
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (T - p.1, p.2)) (t, x) :=
    (contMDiffAt_const.sub contMDiffAt_fst).prodMk contMDiffAt_snd
  exact hp.comp (t, x) hmap

end DifferentialGeometry.PDE.RicciFlow.Entropy

end

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open Bundle Filter Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem revLaplacianPotential_time
    [I.Boundaryless] [T2Space M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (u : ℝ → M → ℝ)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (flowG S) T) (fun r x => -S.scalar (T - r) x) u)
    (hpos : ∀ r, r ∈ Dr.regular ∩ Set.Ioi (0 : ℝ) → ∀ x, 0 < u r x)
    {t : ℝ} (ht : t ∈ Dr.regular) (htpos : 0 < t)
    (hTt : T - t ∈ D.regular) (x : M) :
    let G := reverseFamily (flowG S) T
    let f := fun r => perelmanPotential (Module.finrank ℝ E) r (u r)
    let hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f t) :=
      potential_slice Dr G (fun r x => -S.scalar (T - r) x) u
        (Module.finrank ℝ E) hu ht htpos (hpos t ⟨ht, htpos⟩)
    let ft := fun y => laplacianAt G t (f t) y -
      (G.metric t).inner y (gradientAt G t (f t) y) (gradientAt G t (f t) y) +
      S.scalar (T - t) y - (Module.finrank ℝ E : ℝ) / (2 * t)
    HasDerivAt (fun r => laplacianAt G r (f r) x)
      (laplacianAt G t ft x -
        2 * inner0S (G.metric t) x 2 (metricRicciAt (G.metric t) x)
          (hessianSec (metricCov (G.metric t)) (metricCov_smooth (G.metric t))
            (f t) hf x)) t := by
  classical
  dsimp only
  let G := reverseFamily (flowG S) T
  let f : ℝ → M → ℝ := fun r => perelmanPotential (Module.finrank ℝ E) r (u r)
  let U : Set ℝ := Dr.regular ∩ Ioi (0 : ℝ)
  have hU : IsOpen U := Dr.regular_isOpen.inter isOpen_Ioi
  have htU : t ∈ U := ⟨ht, htpos⟩
  have hfs (r : ℝ) (hr : r ∈ U) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f r) :=
    potential_slice Dr G (fun r x => -S.scalar (T - r) x) u
      (Module.finrank ℝ E) hu hr.1 hr.2 (hpos r hr)
  let ft : M → ℝ := fun y => laplacianAt G t (f t) y -
    (G.metric t).inner y (gradientAt G t (f t) y) (gradientAt G t (f t) y) +
    S.scalar (T - t) y - (Module.finrank ℝ E : ℝ) / (2 * t)
  have hft : ContMDiff I 𝓘(ℝ, ℝ) ∞ ft := by
    have hl : ContMDiff I 𝓘(ℝ, ℝ) ∞ (laplacianAt G t (f t)) :=
      contMDiff_laplacian_leviCivita (G.metric t) (hfs t htU)
    have hq : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => (G.metric t).inner y
        (gradientAt G t (f t) y) (gradientAt G t (f t) y)) := by
      exact normGradSqFun_contMDiff (G.metric t) (hfs t htU)
    have hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (S.scalar (T - t)) :=
      metricScalar_smooth (G.metric t)
    exact ((hl.sub hq).add hR).sub contMDiff_const
  have hf : ∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (t, y) := by
    intro y
    exact (potential_joint Dr G (fun r x => -S.scalar (T - r) x) u
      (Module.finrank ℝ E) hu hpos).contMDiffAt
      ((hU.prod isOpen_univ).mem_nhds ⟨htU, mem_univ y⟩)
  have hd (y : M) : HasDerivAt (fun r => f r y) (ft y) t := by
    have h := potential_pde Dr G (fun r x => -S.scalar (T - r) x) u
      (Module.finrank ℝ E) hu ht htpos (hpos t htU) y
    simpa only [ft, f, gradientAt, sub_neg_eq_add] using h
  let F : ℝ → M → ℝ := fun r => if r ∈ U then f r else fun _ => 0
  have hFeq : F =ᶠ[𝓝 t] f := by
    filter_upwards [hU.mem_nhds htU] with r hr
    simp only [F, if_pos hr]
  have hFs (r : ℝ) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (F r) := by
    by_cases hr : r ∈ U
    · simpa only [F, if_pos hr] using hfs r hr
    · simp only [F, if_neg hr]
      exact contMDiff_const
  have hFj (y : M) : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => F p.1 p.2) (t, y) := by
    apply (hf y).congr_of_eventuallyEq
    filter_upwards [(continuousAt_fst : ContinuousAt (fun p : ℝ × M => p.1) (t, y)).eventually hFeq]
      with p hp
    exact congrFun hp p.2
  have hFd (y : M) : HasDerivAt (fun r => F r y) (ft y) t :=
    (hd y).congr_of_eventuallyEq (hFeq.mono fun r hr => congrFun hr y)
  have hg (y : M) (v w : TangentSpace I y) :
      HasDerivAt (fun r => (G.metric r).inner y v w)
        (2 * metricRicci (G.metric t) y (vec2 v w)) t := by
    have hsub : HasDerivAt (fun r : ℝ => T - r) (-1) t := by
      have h := (hasDerivAt_const (x := t) (c := T)).sub (hasDerivAt_id (x := t))
      have hfun : (fun _ : ℝ => T) - id = fun r : ℝ => T - r := by
        funext r
        rfl
      rw [hfun] at h
      simpa only [zero_sub] using h
    have h := (metricDerivAt S hS ⟨T - t, hTt⟩ y v w).comp t hsub
    have he : ((-2 : ℝ) * S.ricciAt (T - t) y (vec2 v w)) * (-1) =
        2 * metricRicci (G.metric t) y (vec2 v w) := by
      change ((-2 : ℝ) * S.ricciAt (T - t) y (vec2 v w)) * (-1) =
        2 * S.ricciAt (T - t) y (vec2 v w)
      ring
    exact h.congr_deriv he
  have hgs (Y Z : ContMDiffSection I E ∞ (TangentSpace I)) (y : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (G.metric p.1).inner p.2 (Y p.2) (Z p.2)) (t, y) :=
    (reverseMetric_pair_contMDiffAt S hS T t hTt Y Z y).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hmain := laplacian_leviCivita_hasDerivAt_of_ricci_deriv
    G.metric 2 t hg hgs F hFs ft hft hFj hFd x
  have heq : (fun r => laplacianAt G r (f r) x) =ᶠ[𝓝 t]
      (fun r => laplacian (LeviCivita (G.metric r)) (G.metric r) (F r) x) := by
    filter_upwards [hFeq] with r hr
    rw [hr]
    rfl
  have hres := hmain.congr_of_eventuallyEq heq
  have hsimp := hres
  simp only [F, if_pos htU, metricRicci_apply] at hsimp
  have hh : hessianSec (LeviCivita (G.metric t))
      (leviCivita_contMDiffCovariantDerivativeLocally (G.metric t)) (f t) (hfs t htU) x =
      hessianSec (metricCov (G.metric t)) (metricCov_smooth (G.metric t))
        (f t) (hfs t htU) x := rfl
  rw [hh] at hsimp
  exact hsimp

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
