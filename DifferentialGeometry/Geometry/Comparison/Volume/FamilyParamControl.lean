import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation
import DifferentialGeometry.Geometry.Coordinates.TangentPartialDiffeomorph
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Topology.FiberBundleT2

set_option autoImplicit false

/-!
# Parametrized control for a short metric-family slab

This file gives fixed normal-coordinate control for a smooth metric family near
the closed initial endpoint.  The result is deliberately local in the chosen
exponential parametrization: compactness supplies a uniform density lower
bound and a uniform coordinate-speed upper bound on one fixed model ball.
-/

noncomputable section

open Bundle Manifold Matrix Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

universe u uE uH

variable {M : Type u}
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
/-- Joint continuity of the parametrized density of a fixed partial
diffeomorphism against a continuous metric family. -/
private theorem paramDensity_cont
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {K : Set Real} (hK : K ⊆ D.carrier)
    (Ψ : PartialDiffeomorph 𝓘(Real, E) I E M 1)
    {B : Set E} (hB : B ⊆ Ψ.source) :
    Continuous (fun q : {t : Real // t ∈ K} × B =>
      paramDensity (I := I) (G.metric q.1.1) Ψ q.2.1) := by
  classical
  let P := {t : Real // t ∈ K} × B
  let b : P → M := fun q => Ψ q.2.1
  have hb : Continuous b :=
    Ψ.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_snd)
      (fun q => hB q.2.2)
  have hslot : ∀ i : Fin (Module.finrank Real E),
      Continuous (fun q : P =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q)
          (mfderiv 𝓘(Real, E) I Ψ q.2.1 ((chartModelBasis E) i))) := by
    intro i
    let lift : P → TangentBundle 𝓘(Real, E) E :=
      fun q => ⟨q.2.1, (chartModelBasis E) i⟩
    have hlift : Continuous lift :=
      (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.continuous.comp
        ((continuous_subtype_val.comp continuous_snd).prodMk continuous_const)
    simpa [b, lift] using
      (PartialDiffeomorph.mfderiv_cont Ψ (by norm_num) lift hlift
        (fun q => hB q.2.2))
  have hentry : ∀ i j : Fin (Module.finrank Real E),
      Continuous (fun q : P =>
        paramGramMatrix (I := I) (G.metric q.1.1) Ψ q.2.1 i j) := by
    intro i j
    let v : Fin 2 → (q : P) → TangentSpace I (b q) :=
      fun k q => mfderiv 𝓘(Real, E) I Ψ q.2.1
        ((chartModelBasis E) (if k = 0 then i else j))
    have hv : ∀ k : Fin 2, Continuous (fun q : P =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v k q)) := by
      intro k
      exact hslot (if k = 0 then i else j)
    have heval :=
      (metricTensor_cont_restrict_of_metricFamilySmoothOn
        (I := I) (M := M) G hG hK).eval_continuous
        (P := P) (τ := fun q => q.1.1) (b := b)
        (continuous_subtype_val.comp continuous_fst)
        (fun q => q.1.2) hb hv
    refine heval.congr (fun q => ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [b, v, paramGramMatrix_apply]
  have hmatrix : Continuous (fun q : P =>
      paramGramMatrix (I := I) (G.metric q.1.1) Ψ q.2.1) := by
    apply continuous_matrix
    exact hentry
  exact Real.continuous_sqrt.comp
    ((continuous_id.matrix_det).comp hmatrix)

/-- A fixed initial exponential parametrization has uniform density below and
uniform coordinate speed above on a fixed model ball for all sufficiently
short carrier times. -/
theorem exists_param_ctrl
    [T2Space M]
    {omega : Real} (h0omega : 0 < omega)
    (G : RealizedMetricFamilyOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0omega))
    (hG : MetricFamilySmoothOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0omega) G)
    (a : M) :
    let Ψ := NormalCoordinates.expMapDiffeo (I := I) (G.metric 0) a
    ∃ tau R c L : Real,
      0 < tau ∧ tau < omega ∧ 0 < R ∧ 0 < c ∧ 1 ≤ L ∧
      Metric.closedBall (0 : E) (2 * R) ⊆ Ψ.source ∧
      ∀ (t : RealTimeInterval.FlowTime
          (RealTimeInterval.closedOpen 0 omega h0omega)),
        (t : Real) ≤ tau →
        ∀ w ∈ Metric.closedBall (0 : E) (2 * R),
          c ≤ paramDensity (I := I) (G.metric (t : Real)) Ψ w ∧
          ∀ v : E,
            Real.sqrt
              ((G.metric (t : Real)).inner (Ψ w)
                (mfderiv 𝓘(Real, E) I Ψ w v)
                (mfderiv 𝓘(Real, E) I Ψ w v)) ≤ L * ‖v‖ := by
  classical
  dsimp only
  let Ψ := NormalCoordinates.expMapDiffeo (I := I) (G.metric 0) a
  let tau : Real := omega / 2
  let R : Real := expMapC2Radius (I := I) (G.metric 0) a / 4
  let K : Set Real := Set.Icc 0 tau
  let B : Set E := Metric.closedBall (0 : E) (2 * R)
  have htau_pos : 0 < tau := by dsimp [tau]; linarith
  have htau_lt : tau < omega := by dsimp [tau]; linarith
  have hR_pos : 0 < R := by
    dsimp [R]
    exact div_pos (expMapC2Radius_pos (I := I) (G.metric 0) a) (by norm_num)
  have hK : K ⊆
      (RealTimeInterval.closedOpen 0 omega h0omega).carrier := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 htau_lt⟩
  have hB : B ⊆ Ψ.source := by
    intro w hw
    apply mem_expMapDiffeo_source_of_norm_lt_radius
      (I := I) (G.metric 0) a
    have hw_le : ‖w‖ ≤ 2 * R := by
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hw
    have h2R_lt : 2 * R < expMapC2Radius (I := I) (G.metric 0) a := by
      dsimp [R]
      nlinarith [expMapC2Radius_pos (I := I) (G.metric 0) a]
    exact lt_of_le_of_lt hw_le h2R_lt
  let T := {t : Real // t ∈ K}
  let P := T × B
  let dens : P → Real := fun q =>
    paramDensity (I := I) (G.metric q.1.1) Ψ q.2.1
  have hdens : Continuous dens :=
    paramDensity_cont (I := I) G hG hK Ψ hB
  letI : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace B :=
    isCompact_iff_compactSpace.mp (by
      simpa [B] using isCompact_closedBall (0 : E) (2 * R))
  have hPne : (Set.univ : Set P).Nonempty := by
    let q : P :=
      (⟨0, by simp [K, htau_pos.le]⟩,
        ⟨0, by simp [B, hR_pos.le]⟩)
    exact ⟨q, Set.mem_univ q⟩
  obtain ⟨qmin, _hqmin, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set P)).exists_isMinOn
      hPne hdens.continuousOn
  let c : Real := dens qmin
  have hc_pos : 0 < c := by
    dsimp [c, dens]
    exact paramDensity_pos (I := I) (G.metric qmin.1.1) Ψ
      (hB qmin.2.2)
  let U : Set E := Metric.closedBall (0 : E) 1
  let Q := P × U
  let speed : Q → Real := fun q =>
    Real.sqrt
      ((G.metric q.1.1.1).inner (Ψ q.1.2.1)
        (mfderiv 𝓘(Real, E) I Ψ q.1.2.1 q.2.1)
        (mfderiv 𝓘(Real, E) I Ψ q.1.2.1 q.2.1))
  have htangent : Continuous (fun q : Q =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (Ψ q.1.2.1)
        (mfderiv 𝓘(Real, E) I Ψ q.1.2.1 q.2.1)) := by
    let lift : Q → TangentBundle 𝓘(Real, E) E :=
      fun q => ⟨q.1.2.1, q.2.1⟩
    have hlift : Continuous lift :=
      (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.continuous.comp
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd))
    simpa [lift] using
      (PartialDiffeomorph.mfderiv_cont Ψ (by norm_num) lift hlift
        (fun q => hB q.1.2.2))
  have hspeed : Continuous speed := by
    have hquad :=
      metricTimeBundleQuad_cont_of_metricFamilySmoothOn
        (I := I) (M := M) G hG hK
    have hpull : Continuous (fun q : Q =>
        (q.1.1,
          TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (Ψ q.1.2.1)
            (mfderiv 𝓘(Real, E) I Ψ q.1.2.1 q.2.1))) :=
      (continuous_fst.comp continuous_fst).prodMk htangent
    exact Real.continuous_sqrt.comp (hquad.comp hpull)
  letI : CompactSpace U :=
    isCompact_iff_compactSpace.mp (by
      simpa [U] using isCompact_closedBall (0 : E) 1)
  have hQne : (Set.univ : Set Q).Nonempty := by
    obtain ⟨p0, _⟩ := hPne
    let q : Q := (p0, ⟨0, by simp [U]⟩)
    exact ⟨q, Set.mem_univ q⟩
  obtain ⟨qmax, _hqmax, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Q)).exists_isMaxOn
      hQne hspeed.continuousOn
  let L : Real := max 1 (speed qmax)
  have hL_one : 1 ≤ L := le_max_left _ _
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_one
  refine ⟨tau, R, c, L, htau_pos, htau_lt, hR_pos, hc_pos, hL_one, hB, ?_⟩
  intro t ht w hw
  have htK : (t : Real) ∈ K := ⟨t.2.1, ht⟩
  let p : P := (⟨(t : Real), htK⟩, ⟨w, hw⟩)
  have hc_le : c ≤ paramDensity (I := I) (G.metric (t : Real)) Ψ w := by
    have hp := (isMinOn_iff.mp hmin) p (Set.mem_univ p)
    simpa [c, dens, p] using hp
  refine ⟨hc_le, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    have hd0 :
        mfderiv 𝓘(Real, E) I Ψ w (0 : E) =
          (0 : TangentSpace I (Ψ w)) := by
      exact map_zero _
    rw [hd0]
    simp
  · have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u : E := ‖v‖⁻¹ • v
    have hu_norm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (ne_of_gt hvnorm_pos)
    have hu_mem : u ∈ U := by
      simp [U, Metric.mem_closedBall, dist_zero_right, hu_norm]
    let q : Q := (p, ⟨u, hu_mem⟩)
    have hspeed_le : speed q ≤ L := by
      exact le_trans ((isMaxOn_iff.mp hmax) q (Set.mem_univ q))
        (le_max_right _ _)
    have hv_from_u : ‖v‖ • u = v := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvnorm_pos), one_smul]
    have hscale :
        (G.metric (t : Real)).inner (Ψ w)
            (mfderiv 𝓘(Real, E) I Ψ w v)
            (mfderiv 𝓘(Real, E) I Ψ w v) =
          ‖v‖ ^ 2 *
            (G.metric (t : Real)).inner (Ψ w)
              (mfderiv 𝓘(Real, E) I Ψ w u)
              (mfderiv 𝓘(Real, E) I Ψ w u) := by
      conv_lhs => rw [← hv_from_u]
      have hdscale :
          mfderiv 𝓘(Real, E) I Ψ w (‖v‖ • u) =
            ‖v‖ • mfderiv 𝓘(Real, E) I Ψ w u := by
        exact map_smul _ _ _
      rw [hdscale, metric_smul2]
      ring
    rw [hscale, Real.sqrt_mul (sq_nonneg ‖v‖), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg v)]
    have hspeed_le' :
        Real.sqrt
            ((G.metric (t : Real)).inner (Ψ w)
              (mfderiv 𝓘(Real, E) I Ψ w u)
              (mfderiv 𝓘(Real, E) I Ψ w u)) ≤ L := by
      simpa [speed, q, p] using hspeed_le
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hspeed_le' (norm_nonneg v))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
