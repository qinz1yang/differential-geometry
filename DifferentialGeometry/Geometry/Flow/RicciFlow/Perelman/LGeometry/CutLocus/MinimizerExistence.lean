import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MinimizerDomain

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

theorem exists_lMinVec_ray
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x) :
    ∃ W : TangentSpace I x,
      (W, tau) ∈ lMinDomain S T x ∧
        lExp S T x W tau = lExp S T x Z tau := by
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _htau0, hbDom⟩
  let b : Real := Real.sqrt tau
  obtain ⟨rho, hrho, hrho_id, _hrho_deriv, hrho_range⟩ :=
    exists_lRegDomain_smoothClamp S T x Z (Real.sqrt_pos.2 htau) hbDom
  let z : E := Z
  let alpha : Real → M := fun s ↦ lRegCurve S T x Z (rho s)
  have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      (fun s : Real ↦ (z, rho s)) :=
    contMDiff_const.prodMk hrhoM
  have halphaInf : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn (modelWithCornersSelf Real Real) I ∞
      (fun s ↦ lRegCurve S T x Z (rho s)) univ
    exact (lRegCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change rho s ∈ lRegDomain S T x Z
        exact hrho_range s)
  have halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha :=
    halphaInf.of_le (by norm_num)
  have hrho0 : rho 0 = 0 := by
    simpa only [id_eq] using hrho_id ⟨le_rfl, (Real.sqrt_pos.2 htau).le⟩
  have hrhob : rho b = b := by
    simpa only [id_eq] using hrho_id ⟨(Real.sqrt_pos.2 htau).le, le_rfl⟩
  have halpha0 : alpha 0 = x := by
    simp only [alpha, hrho0, lRegCurve_zero]
  have halphab : alpha b = lExp S T x Z tau := by
    simp only [alpha, hrhob, lExp, b]
  have hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lExpPosDom_reg S T x Z hdom (by simpa only [b] using hs)
  have hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - tau) T := by
    intro s hs
    have hsSq : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
          (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).2
            (by simpa only [b] using hs.2)
        _ = tau := Real.sq_sqrt htau.le
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have htime : Icc (T - tau) T ⊆ D.carrier := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hleTau : T - r ≤ tau := by linarith [hr.1]
    have hsqrtMem : Real.sqrt (T - r) ∈ Icc (0 : Real) b :=
      ⟨Real.sqrt_nonneg _, by
        simpa only [b] using Real.sqrt_le_sqrt hleTau⟩
    have hregR := lExpPosDom_reg S T x Z hdom hsqrtMem
    have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    exact D.regular_subset (by simpa only [heq] using hregR)
  obtain ⟨W, hW, hend⟩ :=
    exists_lMinVec (I := I) S hS T (T - tau) T tau htau htime
      (by simpa only [b] using hback) x (lExp S T x Z tau) alpha halpha
      halpha0 (by simpa only [b] using halphab)
      (by simpa only [b] using hreg)
  exact ⟨W, hW, hend⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
