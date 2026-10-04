import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5GaugeFlow
import DifferentialGeometry.Geometry.Operator.Laplacian.TimeDerivative
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar

/-!
# The time derivative of the Laplacian along a surface Ricci flow

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (i) (potential gauge, design D18,
errata "route change for (i)").

Along a Ricci flow `∂ₜ g = -2 Ric = -R g` of surfaces, for a function family `u` jointly smooth on
`(0, T) × M` with time derivative `uₜ` at `t`:
* `surfaceFlow_ΔG_hasDerivAt`: `∂ₜ (Δ_{g(t)} u) = Δ_{g(t)} uₜ + R Δ_{g(t)} u`, from
  `laplacian_leviCivita_hasDerivAt_of_ricci_deriv` (`c = -2`), `Ric = (R / 2) g` and the trace
  form of the Laplacian.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow
open Bundle Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
  {T : ℝ} {hT : 0 < T}

theorem laplacian_eq_metricTracePair (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; ℝ⟯)
    (x : M) :
    ΔG g u x = metricTracePair0SAt g
      (hessianSec (LeviCivita g) (leviCivita_contMDiffCovariantDerivativeLocally g) u
        u.contMDiff x) := by
  let _ : SigmaCompactSpace M := inferInstance
  have h1 : laplacian (LeviCivita g) g u x = metricTracePair0SAt g
      (hessianSec (LeviCivita g) (leviCivita_contMDiffCovariantDerivativeLocally g) u
        u.contMDiff x) :=
    (scalarLap_smooth (LeviCivita g) (leviCivita_contMDiffCovariantDerivativeLocally g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible g) u u.contMDiff).eq_trace
  exact (laplacian_levi_eq g u.contMDiff x).symm.trans h1

theorem inner_metricRicci_hessianSec_of_finrank_eq_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; ℝ⟯) (x : M) :
    inner0S g x 2 (metricRicci g x)
        (hessianSec (LeviCivita g) (leviCivita_contMDiffCovariantDerivativeLocally g) u
          u.contMDiff x) =
      metricScalarAt g x / 2 * ΔG g u x := by
  rw [metricRicci_apply, metricRicciAt_eq_half_metricScalarAt_smul_metric_of_finrank_eq_two g hdim,
    inner0S_smul_left, laplacian_eq_metricTracePair]
  rfl

theorem surfaceFlow_ΔG_hasDerivAt (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (u : ℝ → C^∞⟮I, M; ℝ⟯)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => u q.1 q.2) (Ioo 0 T ×ˢ univ))
    (ut : C^∞⟮I, M; ℝ⟯) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hd : ∀ y, HasDerivAt (fun s => u s y) (ut y) t) (x : M) :
    HasDerivAt (fun s => ΔG (S.family.metric s) (u s) x)
      (ΔG (S.family.metric t) ut x + S.scalar t x * ΔG (S.family.metric t) (u t) x) t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : SigmaCompactSpace M := inferInstance
  have hreg : t ∈ (RealTimeInterval.closedOpen 0 T hT).regular := ht
  have hregN : (RealTimeInterval.closedOpen 0 T hT).regular ∈ 𝓝 t :=
    (RealTimeInterval.closedOpen 0 T hT).regular_isOpen.mem_nhds hreg
  have hg : ∀ y (a b : TangentSpace I y), HasDerivAt (fun r => (S.family.metric r).inner y a b)
      ((-2 : ℝ) * metricRicci (S.family.metric t) y (vec2 a b)) t := fun y a b =>
    metricDerivAt S hS ⟨t, hreg⟩ y a b
  have hgs : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ y,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (S.family.metric p.1).inner p.2 (Y p.2) (Z p.2)) (t, y) := by
    intro Y Z y
    exact (hS.smoothMetric.pairSmoothAt (x := y) hregN ![Y, Z]).of_le (by decide)
  have huj : ∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (t, y) := fun y =>
    hu.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)
  have h := laplacian_leviCivita_hasDerivAt_of_ricci_deriv S.family.metric (-2) t hg hgs
    (fun s y => u s y) (fun r => (u r).contMDiff) ut ut.contMDiff huj hd x
  have heq : ∀ r, laplacian (LeviCivita (S.family.metric r)) (S.family.metric r)
      (fun y => u r y) x = ΔG (S.family.metric r) (u r) x := fun r =>
    laplacian_levi_eq (S.family.metric r) (u r).contMDiff x
  simp only [heq] at h
  rw [inner_metricRicci_hessianSec_of_finrank_eq_two hdim] at h
  refine h.congr_deriv ?_
  change _ - _ * (metricScalarAt (S.family.metric t) x / 2 * _) = _
  have hR : metricScalarAt (S.family.metric t) x = S.scalar t x := rfl
  have hl : laplacian (LeviCivita (S.family.metric t)) (S.family.metric t) ut x =
      ΔG (S.family.metric t) ut x := laplacian_levi_eq (S.family.metric t) ut.contMDiff x
  rw [hR, hl]
  ring

end GC.Geometry

end
