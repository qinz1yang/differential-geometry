import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointDistanceCoreBinding
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirectionsApplications
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.RadialFunctionAtScaleApplications

/-!
# The LC55 disc core at every sufficiently large scale

The threshold is selected once from the actual compact normal core, the point-direction margin
and the supplied asymptotic cone approximations. Each larger scale produces its own smoothed
point-distance function. The existing compact-support isotopy then identifies its full core
with the radius sublevel of the same bundle, including the actual closed unit-disc map.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Morse GC.MetricGeometry
open DifferentialGeometry.Geometry.Topology DifferentialGeometry.Geometry.Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [instE : NormedAddCommGroup E] [instER : NormedSpace ℝ E]
  [instEF : FiniteDimensional ℝ E] [instEZ : NeZero (Module.finrank ℝ E)]
  {H : Type*} [instH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [instIB : I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [instMC : ChartedSpace H M]
  [instMM : IsManifold I ∞ M] [instMS : SigmaCompactSpace M]
  [instRB : RiemannianBundle (fun x : M => TangentSpace I x)]
  [instRM : IsRiemannianManifold I M] [instComplete : CompleteSpace M]
  [instCR : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  {EB F : Type*} [instEB : NormedAddCommGroup EB] [instEBR : NormedSpace ℝ EB]
  [instEBF : FiniteDimensional ℝ EB]
  [instF : NormedAddCommGroup F] [instFR : NormedSpace ℝ F]
  [instFF : FiniteDimensional ℝ F]
  {HB : Type*} [instHB : TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [instIBB : IB.Boundaryless]
  {B : Type*} [instB : TopologicalSpace B] [instBC : ChartedSpace HB B]
  [instBM : IsManifold IB ∞ B] [instBCompact : CompactSpace B]
  {Vb : B → Type*} [instTotal : TopologicalSpace (TotalSpace F Vb)]
  [instFibNorm : ∀ b, NormedAddCommGroup (Vb b)]
  [instFibInner : ∀ b, InnerProductSpace ℝ (Vb b)]
  [instFib : FiberBundle F Vb] [instVec : VectorBundle ℝ F Vb]
  [instSmooth : ContMDiffVectorBundle ∞ F Vb IB]
  [instSmoothInner : IsContMDiffRiemannianBundle IB ∞ F Vb]

theorem exists_point_distance_discCore_at_every_scale
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x, SectionalBoundedBelowAt g x 0)
    (p : M) {C : Type*} [instC : MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox M C (m.rescale R⁻¹ (inv_pos.mpr hR)) instC p o τ))
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hVB : ∀ x, g.inner x (V x) (V x) ≤ 4) {A : ℝ}
    (hVdir : ∀ x, A ≤ dist p x →
      ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p x, g.inner x (V x) w ≤ -(1 / 4))
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F Vb) M ∞)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hdu : ∀ x, ℓ < ‖(e.symm x).2‖ →
      mvfderiv (I := I) (fun y => ‖(e.symm y).2‖) x (V x) = 1)
    {k : ℕ} (hd : Module.finrank ℝ (EB × F) = k + 1) :
    ∃ Rstar : ℝ, 0 < Rstar ∧ ∀ R : ℝ, Rstar ≤ R → ∀ hR : 0 < R,
      let _instScaledMetric := m.rescale R⁻¹ (inv_pos.mpr hR)
      let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      ∃ ζ : M → ℝ, (∀ x, |ζ x - dist p x| < 1 / 80) ∧
        LipschitzWith (Real.toNNReal (1 / 64)) (fun x => ζ x - dist p x) ∧
        (∃ W : Set M, IsOpen W ∧
          (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → x ∈ W) ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ W) ∧
        IsCompact {x | ζ x ≤ 1} ∧
        Metric.closedBall p (1 / 2) ⊆ interior {x | ζ x ≤ 1} ∧
        {x | ζ x ≤ 1} ⊆ Metric.ball p 2 ∧
        frontier {x | ζ x ≤ 1} ⊆ {x | 79 / 80 < dist p x ∧ dist p x < 81 / 80} ∧
        (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
          gR.inner x (R • V x) (R • V x) ≤ 4) ∧
        (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
          7 / 32 ≤ mvfderiv (I := I) ζ x (R • V x)) ∧
        ∃ T : ℝ, ∃ hT : 0 < T,
          ∃ e' : Diffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F Vb) M ∞,
            {x | ζ x ≤ 1} = {x | ‖(e'.symm x).2‖ ≤ T} ∧
            let _instUnit := normClosedDiscBundleChartedSpace (IB := IB) (V := Vb) hd 1 one_pos
            let _instCore := discCoreChartedSpace e' hd T hT
            ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace k)
                (morseModelWithCornersHalfSpace k)
                {z : TotalSpace F Vb // ‖z.2‖ ≤ 1} {x : M // ‖(e'.symm x).2‖ ≤ T} ∞,
              ∀ z, (Ψ z).val = e' ⟨z.val.proj, T • z.val.2⟩
 := by
  let u : M → ℝ := fun x => ‖(e.symm x).2‖
  let Tzero : ℝ := ℓ + 1
  have hTzero : 0 < Tzero := by dsimp [Tzero]; linarith
  obtain ⟨Bzero, hBzero⟩ := (isCompact_discCore e Tzero).isBounded.subset_ball p
  let τ : ℝ := radialSmoothingConeError ((1 / 64) / 4) / 2
  have htau : 0 < τ := by
    dsimp [τ]
    exact half_pos (radialSmoothingConeError_pos (by norm_num))
  have htau1 : τ < 1 := by
    have hbound : radialSmoothingConeError ((1 / 64 : ℝ) / 4) ≤ 1 / 600 := min_le_left _ _
    dsimp [τ]
    linarith
  obtain ⟨Rcone, hRcone⟩ := hcone τ htau htau1
  let Rstar : ℝ := max (max Rcone 1) (max (4 / 3 * A + 1) (2 * Bzero + 1))
  have hRstar : 0 < Rstar :=
    lt_of_lt_of_le one_pos ((le_max_right Rcone 1).trans (le_max_left _ _))
  refine ⟨Rstar, hRstar, fun R hRR hR => ?_⟩
  have hRconeR : Rcone ≤ R :=
    (le_max_left Rcone 1).trans ((le_max_left _ _).trans hRR)
  have hRA : 4 / 3 * A + 1 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hRR)
  have hRB : 2 * Bzero + 1 ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hRR)
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
  have hsecR : ∀ y ∈ Metric.ball p (400 * R),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * R⁻¹ ^ 2)) := by
    intro y _hy
    exact (hsec y).mono (by nlinarith [sq_nonneg R⁻¹])
  obtain ⟨ζ, hclose, hlip, W, hW, hcollar, hζ⟩ :=
    exists_point_distance_core_function_at_scale g hmetric hR (hRcone R hR hRconeR).some
      Hc hsecR (by
        dsimp [τ]
        exact half_lt_self (radialSmoothingConeError_pos (by norm_num)))
  have hpair (x : M) (hx : A ≤ dist p x) :=
    radialScaled_field_pairing_le g hEnorm hR p x (V x) (hVdir x hx)
  have hBzero' (x : M) (hx : u x ≤ Tzero) : dist x p < Bzero := by
    exact Metric.mem_ball.mp (hBzero hx)
  let _instScaledMetric := m.rescale R⁻¹ hRi
  let _instScaledBundle := radialScaledBundle g R⁻¹ hRi
  let _instScaledContinuous : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) := radialScaledContinuous g R⁻¹ hRi
  let _instScaledRiemannian : IsRiemannianManifold I M :=
    radialScaledManifold (m := m) g hmetric R⁻¹ hRi
  let _instScaledComplete : CompleteSpace M :=
    (m.rescale_completeSpace_iff R⁻¹ hRi).mpr instComplete
  let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) g
  have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
  have hbound : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
      gR.inner x (R • V x) (R • V x) ≤ 4 := by
    intro x _hlow _hupp
    change R⁻¹ ^ 2 * g.inner x (R • V x) (R • V x) ≤ 4
    simp only [map_smul, smul_apply, smul_eq_mul]
    have heq : R⁻¹ ^ 2 * (R * (R * g.inner x (V x) (V x))) = g.inner x (V x) (V x) := by
      field_simp
    rw [heq]
    exact hVB x
  have hdir : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
      ∀ w ∈ inwardMinimizingDirections (I := I) gR hnR p x,
        gR.inner x (R • V x) w ≤ -(1 / 4) := by
    intro x hlow _hupp
    have hlow' : 3 / 4 < R⁻¹ * @dist M m.toDist p x := hlow
    have hphysical : A ≤ @dist M m.toDist p x := by
      have hd : 3 / 4 * R < @dist M m.toDist p x := by
        have hh := mul_lt_mul_of_pos_left hlow' hR
        rwa [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, mul_comm] at hh
      linarith
    exact hpair x hphysical
  have hsmall : {x | u x ≤ Tzero} ⊆ Metric.ball p (1 / 2) := by
    intro x hx
    have hb := hBzero' x hx
    change R⁻¹ * @dist M m.toDist x p < 1 / 2
    have hd : @dist M m.toDist x p < R / 2 := by linarith
    calc R⁻¹ * @dist M m.toDist x p < R⁻¹ * (R / 2) :=
      mul_lt_mul_of_pos_left hd hRi
      _ = 1 / 2 := by field_simp
  have hu : Continuous u := continuous_discCoreRadius_of_isContMDiffRiemannianBundle e
  have hpositive : ∀ x, Tzero ≤ u x → 0 < mvfderiv (I := I) u x (R • V x) := by
    intro x hx
    rw [map_smul, hdu x (by dsimp [Tzero, u] at hx; linarith), smul_eq_mul, mul_one]
    exact hR
  obtain ⟨hcompact, hin, hout, hfront, hmargin, Tupper, hTupper, hiso⟩ :=
    point_distance_core_isotopy_discCore (IB := IB) (Vb := Vb) gR hnR p
      (ε := Real.toNNReal (1 / 64)) (by norm_num) hclose hlip hW hcollar hζ
      (fun x => R • V x) hbound hdir e (c := 1) one_pos (u := u) (fun x => by simp [u])
      hTzero hsmall (isOpen_lt continuous_const hu)
      (fun x hx => hTzero.trans_le hx) (R • V).contMDiff.contMDiffOn hpositive
  let T : ℝ := (Tzero + Tupper) / 2
  have hTinterval : T ∈ Ioo Tzero Tupper := by dsimp [T]; constructor <;> linarith
  have hT : 0 < T := hTzero.trans hTinterval.1
  obtain ⟨Hs, -, -, -, -, -, e', -, hcore⟩ := hiso T hTinterval
  have hcore' : {x | ζ x ≤ 1} = {x | ‖(e'.symm x).2‖ ≤ T} := by
    simpa only [div_one] using hcore
  refine ⟨ζ, hclose, hlip, ⟨W, hW, hcollar, hζ⟩, hcompact, hin, hout, hfront,
    hbound, hmargin, T, hT, e', hcore', ?_⟩
  let _instUnit := normClosedDiscBundleChartedSpace (IB := IB) (V := Vb) hd 1 one_pos
  let _instCore := discCoreChartedSpace e' hd T hT
  exact ⟨unitDiscCoreDiffeomorph e' hd T hT, unitDiscCoreDiffeomorph_apply e' hd T hT⟩

variable [instMConnected : ConnectedSpace M] [instTangentT2 : T2Space (TangentBundle I M)]

theorem exists_normalFlow_point_distance_discCore_at_every_scale
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x, SectionalBoundedBelowAt g x 0) (p : M)
    {C : Type*} [instC : MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ Rzero : ℝ,
      ∀ R : ℝ, ∀ hR : 0 < R, Rzero ≤ R →
        Nonempty (@KleinerLottApprox M C (m.rescale R⁻¹ (inv_pos.mpr hR)) instC p o τ))
    {S : Set M} (hconv : IsTotallyConvex g S)
    (hB : relBoundary I S = ∅) (hScomp : IsCompact S)
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯) (ϕ : Flow ℝ M) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hIntegral : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    (hVB : ∀ x, g.inner x (V x) (V x) ≤ 4) {A : ℝ}
    (hVdir : ∀ x, A ≤ dist p x →
      ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p x, g.inner x (V x) w ≤ -(1 / 4)) :
    let hSlice := isEmbeddedSlice_of_relBoundary_eq_empty
      hEnorm hconv hB
    let _instSlice := embeddedSliceChartedSpace hSlice
    let _instSliceManifold := embeddedSlice_isManifold hSlice
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _instNormalTopology := a.totalSpaceTopology
    let _instNormalFibre := a.toFiberBundle
    let _instNormalVector := a.toVectorBundle
    let _instNormalSmooth := normalBundle_isContMDiff
      g hEnorm hconv hB
    let _instNormalRiemannian :=
      normalBundle_isContMDiffRiemannianBundle
        g hEnorm hconv hB
    ∀ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
        (normalBundleFiber g S) ≃ₘ⟮
          (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
      (∀ z, e z = normalFlowMap (I := I) g hEnorm S ϕ ℓ z) →
    ∃ Rstar : ℝ, 0 < Rstar ∧ ∀ R : ℝ, Rstar ≤ R → ∀ hR : 0 < R,
      let _instScaledMetric := m.rescale R⁻¹ (inv_pos.mpr hR)
      let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      ∃ ζ : M → ℝ, (∀ x, |ζ x - dist p x| < 1 / 80) ∧
        LipschitzWith (Real.toNNReal (1 / 64)) (fun x => ζ x - dist p x) ∧
        (∃ W : Set M, IsOpen W ∧
          (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → x ∈ W) ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ W) ∧
        IsCompact {x | ζ x ≤ 1} ∧
        Metric.closedBall p (1 / 2) ⊆ interior {x | ζ x ≤ 1} ∧
        {x | ζ x ≤ 1} ⊆ Metric.ball p 2 ∧
        frontier {x | ζ x ≤ 1} ⊆ {x | 79 / 80 < dist p x ∧ dist p x < 81 / 80} ∧
        (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
          gR.inner x (R • V x) (R • V x) ≤ 4) ∧
        (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
          7 / 32 ≤ mvfderiv (I := I) ζ x (R • V x)) ∧
        ∃ T : ℝ, ∃ hT : 0 < T,
          ∃ e' : Diffeomorph
              ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
                𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)) I
              (TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
                (normalBundleFiber g S)) M ∞,
            {x | ζ x ≤ 1} = {x | ‖(e'.symm x).2‖ ≤ T} ∧
            let _instUnit := normClosedDiscBundleChartedSpace
              (IB := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)) (V := normalBundleFiber g S)
              (normalBundle_totalSpace_finrank (I := I) S) 1 one_pos
            let _instCore :=
              discCoreChartedSpace e' (normalBundle_totalSpace_finrank (I := I) S) T hT
            ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace (Module.finrank ℝ E - 1))
                (morseModelWithCornersHalfSpace (Module.finrank ℝ E - 1))
                {z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
                  (normalBundleFiber g S) // ‖z.2‖ ≤ 1}
                {x : M // ‖(e'.symm x).2‖ ≤ T} ∞,
              ∀ z, (Ψ z).val = e' ⟨z.val.proj, T • z.val.2⟩ := by
  intro hSlice instSlice instSliceManifold a instNormalTopology instNormalFibre
    instNormalVector instNormalSmooth instNormalRiemannian e he
  let _instSoulCompact : CompactSpace S := isCompact_iff_compactSpace.mp hScomp
  obtain ⟨-, -, -, hdu⟩ :=
    normalFlow_radius_core_data g hEnorm hconv hB hScomp V ϕ hℓ hIntegral e he
  exact exists_point_distance_discCore_at_every_scale g hEnorm hsec p Hc hcone V hVB hVdir
    e hℓ hdu (normalBundle_totalSpace_finrank (I := I) S)

theorem exists_lc55_normal_disc_core [instMNoncompact : NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x, SectionalBoundedBelowAt g x 0) (p : M)
    {C : Type*} [instC : MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ Rzero : ℝ,
      ∀ R : ℝ, ∀ hR : 0 < R, Rzero ≤ R →
        Nonempty (@KleinerLottApprox M C (m.rescale R⁻¹ (inv_pos.mpr hR)) instC p o τ)) :
    ∃ S : Set M, ∃ hconv : IsTotallyConvex g S, ∃ hB : relBoundary I S = ∅,
      S.Nonempty ∧ IsCompact S ∧
      ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯, ∃ ϕ : Flow ℝ M,
        ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ A : ℝ, 0 < A ∧
          (∀ q, IsMIntegralCurve (fun t => ϕ t q) V) ∧
          (∀ x, g.inner x (V x) (V x) ≤ 4) ∧
          (∀ x, A ≤ dist p x →
            ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p x,
              g.inner x (V x) w ≤ -(1 / 4)) ∧
    let hSlice := isEmbeddedSlice_of_relBoundary_eq_empty
      hEnorm hconv hB
    let _instSlice := embeddedSliceChartedSpace hSlice
    let _instSliceManifold := embeddedSlice_isManifold hSlice
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _instNormalTopology := a.totalSpaceTopology
    let _instNormalFibre := a.toFiberBundle
    let _instNormalVector := a.toVectorBundle
    let _instNormalSmooth := normalBundle_isContMDiff
      g hEnorm hconv hB
    let _instNormalRiemannian :=
      normalBundle_isContMDiffRiemannianBundle
        g hEnorm hconv hB
    ∃ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
        (normalBundleFiber g S) ≃ₘ⟮
          (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
      (∀ z, e z = normalFlowMap (I := I) g hEnorm S ϕ ℓ z) ∧
    ∃ Rstar : ℝ, 0 < Rstar ∧ ∀ R : ℝ, Rstar ≤ R → ∀ hR : 0 < R,
      let _instScaledMetric := m.rescale R⁻¹ (inv_pos.mpr hR)
      let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      ∃ ζ : M → ℝ, (∀ x, |ζ x - dist p x| < 1 / 80) ∧
        LipschitzWith (Real.toNNReal (1 / 64)) (fun x => ζ x - dist p x) ∧
        (∃ W : Set M, IsOpen W ∧
          (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → x ∈ W) ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ W) ∧
        IsCompact {x | ζ x ≤ 1} ∧
        Metric.closedBall p (1 / 2) ⊆ interior {x | ζ x ≤ 1} ∧
        {x | ζ x ≤ 1} ⊆ Metric.ball p 2 ∧
        frontier {x | ζ x ≤ 1} ⊆ {x | 79 / 80 < dist p x ∧ dist p x < 81 / 80} ∧
        (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
          gR.inner x (R • V x) (R • V x) ≤ 4) ∧
        (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
          7 / 32 ≤ mvfderiv (I := I) ζ x (R • V x)) ∧
        ∃ T : ℝ, ∃ hT : 0 < T,
          ∃ e' : Diffeomorph
              ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
                𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)) I
              (TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
                (normalBundleFiber g S)) M ∞,
            {x | ζ x ≤ 1} = {x | ‖(e'.symm x).2‖ ≤ T} ∧
            let _instUnit := normClosedDiscBundleChartedSpace
              (IB := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)) (V := normalBundleFiber g S)
              (normalBundle_totalSpace_finrank (I := I) S) 1 one_pos
            let _instCore :=
              discCoreChartedSpace e' (normalBundle_totalSpace_finrank (I := I) S) T hT
            ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace (Module.finrank ℝ E - 1))
                (morseModelWithCornersHalfSpace (Module.finrank ℝ E - 1))
                {z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
                  (normalBundleFiber g S) // ‖z.2‖ ≤ 1}
                {x : M // ‖(e'.symm x).2‖ ≤ T} ∞,
              ∀ z, (Ψ z).val = e' ⟨z.val.proj, T • z.val.2⟩ := by
  obtain ⟨S, hconv, hB, hSne, hScomp, V, ϕ, ℓ, hℓ, A, hA, hVB, -, hIntegral, hVdir,
      u, -, -, -, -, -, -, hnormal⟩ :=
    exists_point_outward_normalFlow_radius g hEnorm
      (fun x => (sectionalBoundedBelowAt_zero_iff g x).mp (hsec x)) p
  refine ⟨S, hconv, hB, hSne, hScomp, V, ϕ, ℓ, hℓ, A, hA, hIntegral, hVB, hVdir, ?_⟩
  intro hSlice instSlice instSliceManifold a instNormalTopology instNormalFibre
    instNormalVector instNormalSmooth instNormalRiemannian
  obtain ⟨e, he, -, -⟩ := hnormal
  exact ⟨e, he, exists_normalFlow_point_distance_discCore_at_every_scale g hEnorm hsec p Hc
    hcone hconv hB hScomp V ϕ hℓ.le hIntegral hVB hVdir e he⟩

end DifferentialGeometry.Geometry.Collapse
