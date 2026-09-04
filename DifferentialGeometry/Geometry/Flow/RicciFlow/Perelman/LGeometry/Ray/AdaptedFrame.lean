import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.Existence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedCurve_adaptedFrame
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {b : Real}
    (hb : 0 < b) (hbdom : b ∈ lRegularizedDomain S T x Z) :
    ∃ (P : Fin (Module.finrank Real E) →
          ∀ s, TangentSpace I (lRegularizedCurve S T x Z s))
        (Ω : Set Real),
      IsOpen Ω ∧ Set.Icc (0 : Real) b ⊆ Ω ∧
      (∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (lRegularizedCurve S T x Z s) (P i s) : TangentBundle I M)) Ω) ∧
      (∀ i, IsLAdapted S T (lRegularizedCurve S T x Z) (P i) Ω) ∧
      ∀ i j,
        (S.base.metric (T - b ^ 2)).inner (lRegularizedCurve S T x Z b)
            (P i b) (P j b) = if i = j then 1 else 0 := by
  classical
  obtain ⟨rho, a, d, ha, hbd, hrho, hrho_id, _hrho_deriv, hrho_dom⟩ :=
    exists_lRegularizedDomain_smoothGerm S T x Z hb hbdom
  let alpha : Real → M := fun s ↦ lRegularizedCurve S T x Z (rho s)
  have hrho_m : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      ((fun s : Real ↦ ((Z : E), rho s)) : Real → E × Real) :=
    contMDiff_const.prodMk hrho_m
  have halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha := by
    rw [← contMDiffOn_univ]
    exact (lRegularizedCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change rho s ∈ lRegularizedDomain S T x Z
        exact hrho_dom s)
  have hreg : ∀ s ∈ Set.Ioo a d, T - s ^ 2 ∈ D.regular := by
    intro s hs
    have hsIcc : s ∈ Set.Icc a d := ⟨hs.1.le, hs.2.le⟩
    have hsreg := lRegularizedDomain_regularity S T x Z (hrho_dom s)
    simpa only [hrho_id hsIcc, id_eq] using hsreg
  let q := S.base.metric (T - b ^ 2)
  obtain ⟨basis, hbasis⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) q (alpha b)
  have hex (i : Fin (Module.finrank Real E)) :=
    exists_lAdaptedField S hS T alpha halpha ha hb hbd hreg (basis i)
  choose R Ωi hΩi hseg_i hsub_i hRsm hRb hRode using hex
  let Ω : Set Real := ⋂ i, Ωi i
  have hΩ : IsOpen Ω := isOpen_iInter_of_finite hΩi
  have hseg : Set.Icc (0 : Real) b ⊆ Ω := by
    intro s hs
    simp only [Ω, Set.mem_iInter]
    intro i
    exact hseg_i i hs
  have hΩsub (s : Real) (hs : s ∈ Ω) : s ∈ Set.Ioo a d := by
    exact hsub_i 0 ((Set.mem_iInter.mp hs) 0)
  let gamma : Real → M := lRegularizedCurve S T x Z
  let P : Fin (Module.finrank Real E) → ∀ s, TangentSpace I (gamma s) :=
    fun i s ↦ (R i s : E)
  have hbase (s : Real) (hs : s ∈ Ω) : alpha s = gamma s := by
    have hsIcc : s ∈ Set.Icc a d :=
      ⟨(hΩsub s hs).1.le, (hΩsub s hs).2.le⟩
    dsimp only [alpha, gamma]
    rw [hrho_id hsIcc]
    rfl
  have hcurve (s : Real) (hs : s ∈ Ω) : alpha =ᶠ[nhds s] gamma := by
    filter_upwards [hΩ.mem_nhds hs] with r hr
    exact hbase r hr
  have hPsm : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (P i s) : TangentBundle I M)) Ω := by
    intro i
    have hraw := (hRsm i).mono (fun _ hs ↦ (Set.mem_iInter.mp hs) i)
    refine hraw.congr ?_
    intro s hs
    change TotalSpace.mk' E (gamma s) (P i s) =
      TotalSpace.mk' E (alpha s) (R i s)
    rw [hbase s hs]
  have hPode : ∀ i, IsLAdapted S T gamma (P i) Ω := by
    intro i s hs
    have hfield : ∀ᶠ r in nhds s, (R i r : E) = (P i r : E) := by
      filter_upwards
      intro r
      rfl
    have hcov :=
      DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
        (I := I) (S.base.metric (T - s ^ 2)) (R i) (P i)
        (hcurve s hs) hfield
    have hraw := hRode i s ((Set.mem_iInter.mp hs) i)
    change (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
      gamma (P i) s : E) =
        (-2 * s) • (ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (gamma s) (P i s) : E)
    rw [← hcov]
    rw [← hbase s hs]
    simpa only [P] using congrArg
      (fun v : TangentSpace I (alpha s) ↦ (v : E)) hraw
  refine ⟨P, Ω, hΩ, hseg, ?_, hPode, ?_⟩
  · simpa only [gamma] using hPsm
  · intro i j
    have hbmem : b ∈ Ω := hseg ⟨hb.le, le_rfl⟩
    change q.inner (gamma b) (P i b) (P j b) = if i = j then 1 else 0
    rw [← hbase b hbmem]
    change q.inner (alpha b) (R i b) (R j b) = if i = j then 1 else 0
    rw [hRb i, hRb j]
    exact hbasis i j

end DifferentialGeometry.PDE.RicciFlow.Perelman
