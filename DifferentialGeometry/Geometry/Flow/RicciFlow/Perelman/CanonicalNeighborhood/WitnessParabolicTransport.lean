import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelTheorem

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] {D : RealTimeInterval}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] in
theorem rescaledMetric_paraSolution
    (S : SolutionOn (I := I) (M := M) D) (tau A : ℝ) (hA : 0 < A)
    (htau : tau ∈ D.carrier) (s Q : ℝ) (hQ : 0 < Q) :
    rescaledMetric (I := I) (parabolicSolution S tau A hA htau) s (A⁻¹ * Q)
        (mul_pos (inv_pos.mpr hA) hQ) =
      rescaledMetric (I := I) S (parabolicTime tau A s) Q hQ := by
  funext u
  have htime : parabolicTime tau A (parabolicTime s (A⁻¹ * Q) u) =
      parabolicTime (parabolicTime tau A s) Q u := by
    dsimp only [parabolicTime]
    field_simp [hA.ne', hQ.ne']
    ring
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  simp only [rescaledMetric, parabolicSolution_metric, scaleMetric_inner, htime]
  field_simp [hA.ne']

private theorem parabolicTime_modelWindow_start (tau A s eps Q : ℝ)
    (hA : 0 < A) (heps : 0 < eps) (hQ : 0 < Q) :
    parabolicTime tau A (s - (eps * (A⁻¹ * Q))⁻¹) =
      parabolicTime tau A s - (eps * Q)⁻¹ := by
  dsimp only [parabolicTime]
  field_simp [hA.ne', heps.ne', hQ.ne']
  ring

def KappaModelWitness.parabolic
    {S : SolutionOn (I := I) (M := M) D} {eps kappa : ℝ} {x : M}
    (tau A : ℝ) (hA : 0 < A) (htau : tau ∈ D.carrier) (s : ℝ)
    (W : KappaModelWitness (I := I) eps kappa S x (parabolicTime tau A s)) :
    KappaModelWitness (I := I) eps kappa (parabolicSolution S tau A hA htau) x s := by
  have hscalar : 0 < (parabolicSolution S tau A hA htau).scalar s x := by
    rw [parabolicSolution_scalar]
    exact mul_pos (inv_pos.mpr hA) W.scalar_pos
  refine
    { eps_pos := W.eps_pos
      eps_lt_one := W.eps_lt_one
      time_mem := W.time_mem
      scalar_pos := hscalar
      window_mem := ?_
      model := W.model
      model_ancient := W.model_ancient
      model_scalar_base := W.model_scalar_base
      embedding := W.embedding
      comparison := ?_ }
  · intro u hu
    apply W.window_mem
    have hmono : Monotone (parabolicTime tau A) := fun a b hab =>
      add_le_add_right (div_le_div_of_nonneg_right hab hA.le) tau
    have hstart := parabolicTime_modelWindow_start tau A s eps
      (S.scalar (parabolicTime tau A s) x) hA W.eps_pos W.scalar_pos
    rw [parabolicSolution_scalar] at hu
    exact ⟨hstart ▸ hmono hu.1, hmono hu.2⟩
  · let : TopologicalSpace W.model.M := W.model.topology
    let : ChartedSpace H W.model.M := W.model.charted
    let : IsManifold I ∞ W.model.M := W.model.smooth
    let : IsManifold I 1 W.model.M :=
      IsManifold.of_le (I := I) (M := W.model.M) (n := ∞) (by decide)
    let : SigmaCompactSpace W.model.M := W.model.sigmaCompact
    let : T2Space W.model.M := W.model.t2
    have hmetric : rescaledMetric (I := I) (parabolicSolution S tau A hA htau) s
        ((parabolicSolution S tau A hA htau).scalar s x) hscalar =
        rescaledMetric (I := I) S (parabolicTime tau A s)
          (S.scalar (parabolicTime tau A s) x) W.scalar_pos := by
      calc
        _ = rescaledMetric (I := I) (parabolicSolution S tau A hA htau) s
            (A⁻¹ * S.scalar (parabolicTime tau A s) x)
            (mul_pos (inv_pos.mpr hA) W.scalar_pos) := by
          congr 1
          exact congrFun (congrFun (parabolicSolution_scalar S tau A hA htau) s) x
        _ = _ := rescaledMetric_paraSolution S tau A hA htau s
          (S.scalar (parabolicTime tau A s) x) W.scalar_pos
    rw [hmetric]
    exact W.comparison

def KappaModelWitness.ofParabolic
    {S : SolutionOn (I := I) (M := M) D} {eps kappa : ℝ} {x : M}
    (tau A : ℝ) (hA : 0 < A) (htau : tau ∈ D.carrier) (s : ℝ)
    (W : KappaModelWitness (I := I) eps kappa (parabolicSolution S tau A hA htau) x s) :
    KappaModelWitness (I := I) eps kappa S x (parabolicTime tau A s) := by
  have hscalar : 0 < S.scalar (parabolicTime tau A s) x := by
    have h := W.scalar_pos
    rw [parabolicSolution_scalar] at h
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hA)).mp h
  refine
    { eps_pos := W.eps_pos
      eps_lt_one := W.eps_lt_one
      time_mem := W.time_mem
      scalar_pos := hscalar
      window_mem := ?_
      model := W.model
      model_ancient := W.model_ancient
      model_scalar_base := W.model_scalar_base
      embedding := W.embedding
      comparison := ?_ }
  · intro u hu
    have hmono : Monotone (parabolicBackward tau A) := fun a b hab =>
      mul_le_mul_of_nonneg_left (sub_le_sub_right hab tau) hA.le
    have hstart := parabolicTime_modelWindow_start tau A s eps
      (S.scalar (parabolicTime tau A s) x) hA W.eps_pos hscalar
    have hleft : parabolicBackward tau A
        (parabolicTime tau A s - (eps * S.scalar (parabolicTime tau A s) x)⁻¹) =
        s - (eps * (A⁻¹ * S.scalar (parabolicTime tau A s) x))⁻¹ := by
      rw [← hstart, parabolicBackward_time hA.ne']
    have hright : parabolicBackward tau A (parabolicTime tau A s) = s := parabolicBackward_time hA.ne'
    have hmem : parabolicBackward tau A u ∈ Set.Icc
        (s - (eps * (parabolicSolution S tau A hA htau).scalar s x)⁻¹) s := by
      rw [parabolicSolution_scalar]
      exact ⟨hleft ▸ hmono hu.1, hright ▸ hmono hu.2⟩
    have hsource := W.window_mem hmem
    change parabolicTime tau A (parabolicBackward tau A u) ∈ D.carrier at hsource
    simpa only [parabolicTime_back hA.ne'] using hsource
  · let : TopologicalSpace W.model.M := W.model.topology
    let : ChartedSpace H W.model.M := W.model.charted
    let : IsManifold I ∞ W.model.M := W.model.smooth
    let : IsManifold I 1 W.model.M :=
      IsManifold.of_le (I := I) (M := W.model.M) (n := ∞) (by decide)
    let : SigmaCompactSpace W.model.M := W.model.sigmaCompact
    let : T2Space W.model.M := W.model.t2
    have hmetric : rescaledMetric (I := I) (parabolicSolution S tau A hA htau) s
        ((parabolicSolution S tau A hA htau).scalar s x) W.scalar_pos =
        rescaledMetric (I := I) S (parabolicTime tau A s)
          (S.scalar (parabolicTime tau A s) x) hscalar := by
      calc
        _ = rescaledMetric (I := I) (parabolicSolution S tau A hA htau) s
            (A⁻¹ * S.scalar (parabolicTime tau A s) x)
            (mul_pos (inv_pos.mpr hA) hscalar) := by
          congr 1
          exact congrFun (congrFun (parabolicSolution_scalar S tau A hA htau) s) x
        _ = _ := rescaledMetric_paraSolution S tau A hA htau s
          (S.scalar (parabolicTime tau A s) x) hscalar
    rw [← hmetric]
    exact W.comparison

theorem isGoodPoint_paraSolution_iff
    (S : SolutionOn (I := I) (M := M) D) (tau A : ℝ) (hA : 0 < A)
    (htau : tau ∈ D.carrier) (s : ℝ) (x : M) (eps kappa : ℝ) :
    IsGoodPoint.{u, uE, uH} (I := I) eps kappa (parabolicSolution S tau A hA htau) x s ↔
      IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x (parabolicTime tau A s) :=
  ⟨fun ⟨W⟩ => ⟨W.ofParabolic tau A hA htau s⟩,
    fun ⟨W⟩ => ⟨W.parabolic tau A hA htau s⟩⟩

theorem isOrientedGoodPoint_paraSolution_iff
    (orient : OrientationDatum I) (S : SolutionOn (I := I) (M := M) D)
    (tau A : ℝ) (hA : 0 < A) (htau : tau ∈ D.carrier)
    (s : ℝ) (x : M) (eps kappa : ℝ) :
    IsOrientedGoodPoint (I := I) orient eps kappa (parabolicSolution S tau A hA htau) x s ↔
      IsOrientedGoodPoint (I := I) orient eps kappa S x (parabolicTime tau A s) :=
  ⟨fun ⟨W, hW⟩ => ⟨W.ofParabolic tau A hA htau s, hW⟩,
    fun ⟨W, hW⟩ => ⟨W.parabolic tau A hA htau s, hW⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
