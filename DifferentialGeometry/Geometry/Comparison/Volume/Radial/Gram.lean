import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram
import DifferentialGeometry.Geometry.Comparison.Volume.HyperbolicModel
import DifferentialGeometry.Geometry.Comparison.Volume.Radial.Gronwall
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Set Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

section Radial

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

omit [T2Space M]
  [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma radialJacobi_li
    {ι : Type*} {v : ι → E}
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {t : ℝ}
    (hv : LinearIndependent ℝ v) (ht : t ≠ 0)
    (htx_source : t • x ∈ (expMapDiffeo (I := I) g p).source)
    (htx_rad : ‖t • x‖ < expMapC2Radius (I := I) g p) :
    LinearIndependent ℝ fun i ↦
      radialJacobiField (I := I) g p x (v i) t := by
  let L := mfderiv 𝓘(ℝ, E) I
    (fun b : E ↦ (expMap (I := I) g p
      (show TangentSpace I p from b) : M)) (t • x)
  have hlocal := PartialDiffeomorph.isLocalDiffeomorphAt
    (I := 𝓘(ℝ, E)) (J := I) (n := 1) (expMapDiffeo (I := I) g p) htx_source
  have hLinj : Function.Injective L := by
    dsimp only [L]
    rw [← expDiffeo_mfderiv (I := I) g p htx_source]
    exact (hlocal.mfderivToContinuousLinearEquiv (by norm_num)).injective
  exact linearIndependent_radialJacobiField (I := I) g p x hv ht
    (mem_expDomain_of_norm_lt_radius (I := I) g p htx_rad) hLinj

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem radial_wronsk_zero
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w z : E,
      ‖x‖ < r → ‖w‖ < r → ‖z‖ < r →
      ∀ {b : ℝ}, 0 < b → b < 1 → ∀ t ∈ Icc (0 : ℝ) b,
        jacobiWronskian g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w)
          (radialJacobiField (I := I) g p x z) t = 0 := by
  obtain ⟨rd, hrd, hdiff⟩ := exists_radialJacobi_diff (I := I) g p
  obtain ⟨rj, hrj, hJacobian⟩ := exists_jacobi_Ioo (I := I) g p
  obtain ⟨r0, hr0, hJacobian0⟩ := exists_radialJacobi_zero_radius (I := I) g hEnorm p
  let re : ℝ := expMapC2Radius (I := I) g p
  let r : ℝ := min rd (min rj (min r0 re))
  have hre : 0 < re := expMapC2Radius_pos (I := I) g p
  have hr : 0 < r := by
    dsimp [r, re]
    exact lt_min hrd (lt_min hrj (lt_min hr0 hre))
  refine ⟨r, hr, ?_⟩
  intro x w z hx hw hz b hb hblt t ht
  have hr_rd : r ≤ rd := min_le_left _ _
  have hr_rj : r ≤ rj := (min_le_right _ _).trans (min_le_left _ _)
  have hr_r0 : r ≤ r0 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr_re : r ≤ re :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hxrd : ‖x‖ < rd := hx.trans_le hr_rd
  have hxj : ‖x‖ < rj := hx.trans_le hr_rj
  have hx0 : ‖x‖ < r0 := hx.trans_le hr_r0
  have hxe : ‖x‖ < expMapC2Radius (I := I) g p := by
    simpa only [re] using hx.trans_le hr_re
  have hwrd : ‖w‖ < rd := hw.trans_le hr_rd
  have hzrd : ‖z‖ < rd := hz.trans_le hr_rd
  have hwj : ‖w‖ < rj := hw.trans_le hr_rj
  have hzj : ‖z‖ < rj := hz.trans_le hr_rj
  have hw0 : ‖w‖ < r0 := hw.trans_le hr_r0
  have hz0 : ‖z‖ < r0 := hz.trans_le hr_r0
  have hb1 : b ≤ 1 := hblt.le
  obtain ⟨hJdiff, hDJdiff⟩ := hdiff x w hxrd hwrd hb1
  obtain ⟨hKdiff, hDKdiff⟩ := hdiff x z hxrd hzrd hb1
  have hJ0 := hJacobian0 x w hx0 hw0
  have hK0 := hJacobian0 x z hx0 hz0
  have hcurve :
      (fun v : ℝ => Geodesic.maximalGeodesic (I := I) g p
        (show TangentSpace I p from v • x) 1) = radialCurve (I := I) g p x := by
    funext v
    rfl
  have hJacobianJ : ∀ s ∈ Icc (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) s := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      rw [← hcurve]
      exact hJ0
    · exact hJacobian x w hxj hwj (b := (1 : ℝ)) le_rfl s
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2.trans_lt hblt⟩
  have hJacobianK : ∀ s ∈ Icc (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x z) s := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      rw [← hcurve]
      exact hK0
    · exact hJacobian x z hxj hzj (b := (1 : ℝ)) le_rfl s
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2.trans_lt hblt⟩
  exact wronskian_zero_on (I := I) (by norm_num) g
    (radialCurve (I := I) g p x)
    (radialJacobiField (I := I) g p x w)
    (radialJacobiField (I := I) g p x z)
    (radialCurve_contMDiffAt_Icc (I := I) g p x hb1 hxe)
    hJdiff hKdiff hDJdiff hDKdiff hJacobianJ hJacobianK
    (radialJacobi_zero (I := I) g p x w)
    (radialJacobi_zero (I := I) g p x z) t ht

end Radial

section PolarDensity

variable [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def basisGram
    {V κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (f : κ → V) : Matrix κ κ ℝ :=
  Matrix.of fun i j => β (f i) (f j)

private lemma gram_basis_change
    {U V κ : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype κ]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (L : U →L[ℝ] V)
    (e B : Module.Basis κ ℝ U) :
    basisGram β (fun i => L (B i)) =
      (e.toMatrix B).transpose * basisGram β (fun i => L (e i)) * e.toMatrix B := by
  classical
  ext i j
  change β (L (B i)) (L (B j)) = _
  rw [show B i = ∑ k, (e.repr (B i)) k • e k from (e.sum_repr (B i)).symm]
  rw [show B j = ∑ l, (e.repr (B j)) l • e l from (e.sum_repr (B j)).symm]
  simp only [basisGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Module.Basis.toMatrix_apply, map_sum, map_smul,
    sum_apply, smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring_nf

private lemma gram_det_change
    {U V κ : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype κ] [DecidableEq κ]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (L : U →L[ℝ] V)
    (e B : Module.Basis κ ℝ U) :
    (basisGram β (fun i => L (B i))).det =
      (e.det B) ^ 2 * (basisGram β (fun i => L (e i))).det := by
  rw [gram_basis_change β L e B, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Module.Basis.det_apply]
  ring

noncomputable def basisIndexEquiv
    (B : Module.Basis (Option ι) ℝ E) :
    Option ι ≃ Fin (Module.finrank ℝ E) :=
  Fintype.equivOfCardEq (by
    simpa using (Module.finrank_eq_card_basis B).symm)

noncomputable def modelBasisFor
    (B : Module.Basis (Option ι) ℝ E) : Module.Basis (Option ι) ℝ E :=
  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).reindex (basisIndexEquiv B).symm

private noncomputable def endpointGram
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {κ : Type*} (v : κ → E) : Matrix κ κ ℝ :=
  Matrix.of fun i j =>
    g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x (v i) 1)
      (radialJacobiField (I := I) g p x (v j) 1)

omit [T2Space M]
  [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma endpoint_det_basis
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    (endpointGram (I := I) g p x B).det =
      ((modelBasisFor B).det B) ^ 2 *
        (radialJacobiGram (I := I) g p x).det := by
  let q : M := expMap (I := I) g p (show TangentSpace I p from x)
  let L : E →L[ℝ] TangentSpace I q := mfderiv 𝓘(ℝ, E) I
    (fun z : E => (expMap (I := I) g p
      (show TangentSpace I p from z) : M)) x
  have hB : endpointGram (I := I) g p x B =
      basisGram (g.inner q) (fun i => L (B i)) := by
    ext i j
    simp only [endpointGram, basisGram, Matrix.of_apply]
    rw [radialJacobi_one (I := I) g p x (B i) hxrad,
      radialJacobi_one (I := I) g p x (B j) hxrad]
    rfl
  have hmodel : endpointGram (I := I) g p x (modelBasisFor B) =
      Matrix.reindex (basisIndexEquiv B).symm (basisIndexEquiv B).symm
        (radialJacobiGram (I := I) g p x) := by
    ext i j
    simp only [endpointGram, Matrix.of_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, radialJacobiGram_apply, modelBasisFor,
      Module.Basis.reindex_apply, Equiv.symm_symm]
  have hmodelDet : (endpointGram (I := I) g p x (modelBasisFor B)).det =
      (radialJacobiGram (I := I) g p x).det := by
    rw [hmodel, Matrix.det_reindex_self]
  have hmodelGram :
      basisGram (g.inner q) (fun i => L ((modelBasisFor B) i)) =
        endpointGram (I := I) g p x (modelBasisFor B) := by
    ext i j
    simp only [basisGram, endpointGram, Matrix.of_apply]
    rw [radialJacobi_one (I := I) g p x ((modelBasisFor B) i) hxrad,
      radialJacobi_one (I := I) g p x ((modelBasisFor B) j) hxrad]
    rfl
  rw [hB]
  rw [gram_det_change (g.inner q) L (modelBasisFor B) B]
  rw [hmodelGram, hmodelDet]

private noncomputable def transverseEndGram
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) (r : ℝ)
    (B : Module.Basis (Option ι) ℝ E) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (radialCurve (I := I) g p u r)
      (radialJacobiField (I := I) g p (r • u) (B (some i)) 1)
      (radialJacobiField (I := I) g p (r • u) (B (some j)) 1)

private lemma bilin_smul_left
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (a : ℝ) (x y : V) :
    β (a • x) y = a * β x y := by
  have h := congrArg (fun A : V →L[ℝ] ℝ => A y) (β.map_smul a x)
  simpa only [smul_apply, smul_eq_mul] using h

private lemma bilin_smul_both
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (a : ℝ) (x y : V) :
    β (a • x) (a • y) = a ^ 2 * β x y := by
  rw [bilin_smul_left, (β x).map_smul]
  simp only [smul_eq_mul, pow_two]
  ring

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)] in
open Filter in
open scoped Matrix in
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis) in
theorem tendsto_curveDensity_radialJacobiField_div_abs_pow
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (v : ι → E)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    Tendsto
      (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t /
        |t| ^ Fintype.card ι)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  classical
  let C : Matrix (Fin (Module.finrank ℝ E)) ι ℝ :=
    fun k i => (chartModelBasis E).repr (v i) k
  let A : ℝ → Matrix ι ι ℝ :=
    fun t => Cᵀ * normalGramMatrix (I := I) g p (t • u) * C
  have hv (i : ι) :
      v i = ∑ k, C k i • (chartModelBasis E) k := by
    dsimp only [C]
    exact ((chartModelBasis E).sum_repr (v i)).symm
  have hG0 (k l : Fin (Module.finrank ℝ E)) :
      normalGramMatrix (I := I) g p (0 : E) k l =
        g.inner p ((chartModelBasis E) k) ((chartModelBasis E) l) := by
    rw [normalGram_apply, expMapDiffeo_zero]
    change
      g.inner p
          (mfderiv 𝓘(ℝ, E) I (normalChartAt (I := I) g p).symm (0 : E)
            ((chartModelBasis E) k))
          (mfderiv 𝓘(ℝ, E) I (normalChartAt (I := I) g p).symm (0 : E)
            ((chartModelBasis E) l)) =
        g.inner p ((chartModelBasis E) k) ((chartModelBasis E) l)
    exact normalChartAt_metric_pullback_at_origin (I := I) g p
      ((chartModelBasis E) k) ((chartModelBasis E) l)
  have hC0 :
      Cᵀ * normalGramMatrix (I := I) g p (0 : E) * C =
        (1 : Matrix ι ι ℝ) := by
    have hbase0 :
        curveGram (I := I) g (fun _ : ℝ => p)
            (fun k (_ : ℝ) => (show TangentSpace I p from (chartModelBasis E) k)) 0 =
          normalGramMatrix (I := I) g p (0 : E) := by
      ext k l
      simpa only [curveGram, Matrix.of_apply] using (hG0 k l).symm
    have hrect0 :=
      curveGram_rect (I := I) g (fun _ : ℝ => p)
        (fun k (_ : ℝ) => (show TangentSpace I p from (chartModelBasis E) k))
        (fun i (_ : ℝ) => (show TangentSpace I p from v i)) 0 C hv
    rw [← hbase0, ← hrect0]
    ext i j
    simpa only [curveGram, Matrix.of_apply, Matrix.one_apply] using hON i j
  have hA0 : A 0 = (1 : Matrix ι ι ℝ) := by
    simpa only [A, zero_smul] using hC0
  have htx : Tendsto (fun t : ℝ => t • u) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : E)) := by
    have hcont : Continuous fun t : ℝ => t • u :=
      continuous_id.smul continuous_const
    have hzero : Tendsto (fun t : ℝ => t • u) (𝓝 (0 : ℝ)) (𝓝 (0 : E)) := by
      simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto
    exact hzero.mono_left inf_le_left
  have hnormal :
      Tendsto
        (fun t : ℝ => normalGramMatrix (I := I) g p (t • u))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (normalGramMatrix (I := I) g p (0 : E))) :=
    (normalGram_contAt (I := I) g p).tendsto.comp htx
  have hA : Tendsto A (𝓝[≠] (0 : ℝ)) (𝓝 (1 : Matrix ι ι ℝ)) := by
    rw [← hA0]
    have hmul : ContinuousAt
        (fun G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ =>
          Cᵀ * G * C)
        (normalGramMatrix (I := I) g p (0 : E)) := by
      have hleft : Continuous
          (fun G : Matrix (Fin (Module.finrank ℝ E))
              (Fin (Module.finrank ℝ E)) ℝ => Cᵀ * G) :=
        continuous_const.matrix_mul continuous_id
      have hright : Continuous
          (fun _ : Matrix (Fin (Module.finrank ℝ E))
              (Fin (Module.finrank ℝ E)) ℝ => C) :=
        continuous_const
      exact (hleft.matrix_mul hright).continuousAt
    simpa only [A, Function.comp_def, zero_smul] using hmul.tendsto.comp hnormal
  have hsrc : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      t • u ∈ (expMapDiffeo (I := I) g p).source :=
    htx.eventually ((expMapDiffeo (I := I) g p).open_source.mem_nhds
      (zero_mem_expMapDiffeo_source (I := I) g p))
  have hrad : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ‖(t • u : E)‖ < expMapC2Radius (I := I) g p := by
    have hball := htx.eventually
      (Metric.ball_mem_nhds (0 : E) (expMapC2Radius_pos (I := I) g p))
    filter_upwards [hball] with t ht
    simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hgram : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      curveGram (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t =
        (t ^ 2) • A t := by
    filter_upwards [hsrc, hrad] with t hsrct hradt
    have hrecomb (i : ι) :
        radialJacobiField (I := I) g p (t • u) (v i) 1 =
          ∑ k, C k i • radialJacobiField (I := I) g p (t • u)
            ((chartModelBasis E) k) 1 := by
      calc
        radialJacobiField (I := I) g p (t • u) (v i) 1 =
            radialJacobiField (I := I) g p (t • u)
              (∑ k, C k i • (chartModelBasis E) k) 1 := by rw [hv i]
        _ = _ := radialJacobi_sum (I := I) g p (t • u)
          (chartModelBasis E) (fun k => C k i) hradt
    have hbase :
        curveGram (I := I) g (radialCurve (I := I) g p u)
            (fun k t => radialJacobiField (I := I) g p (t • u)
              ((chartModelBasis E) k) 1) t =
          normalGramMatrix (I := I) g p (t • u) := by
      rw [normalGram_radialMat (I := I) g p hsrct hradt]
      rfl
    have hrect :
        curveGram (I := I) g (radialCurve (I := I) g p u)
            (fun i t => radialJacobiField (I := I) g p (t • u) (v i) 1) t =
          A t := by
      rw [curveGram_rect (I := I) g (radialCurve (I := I) g p u)
        (fun k t => radialJacobiField (I := I) g p (t • u)
          ((chartModelBasis E) k) 1)
        (fun i t => radialJacobiField (I := I) g p (t • u) (v i) 1)
        t C hrecomb, hbase]
    calc
      curveGram (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t =
          (t ^ 2) •
            curveGram (I := I) g (radialCurve (I := I) g p u)
              (fun i t => radialJacobiField (I := I) g p (t • u) (v i) 1) t := by
        ext i j
        simp only [curveGram, Matrix.of_apply, Matrix.smul_apply]
        have hi :
            radialJacobiField (I := I) g p u (v i) t =
              t • radialJacobiField (I := I) g p (t • u) (v i) 1 := by
          exact (radialJacobi_scale (I := I) g p u (v i) t).trans
            (radialJacobi_one_smul (I := I) g p (t • u) (v i) t hradt)
        have hj :
            radialJacobiField (I := I) g p u (v j) t =
              t • radialJacobiField (I := I) g p (t • u) (v j) 1 := by
          exact (radialJacobi_scale (I := I) g p u (v j) t).trans
            (radialJacobi_one_smul (I := I) g p (t • u) (v j) t hradt)
        rw [hi, hj]
        exact bilin_smul_both
          (g.inner (radialCurve (I := I) g p u t)) t
          (radialJacobiField (I := I) g p (t • u) (v i) 1)
          (radialJacobiField (I := I) g p (t • u) (v j) 1)
      _ = (t ^ 2) • A t := congrArg ((t ^ 2) • ·) hrect
  have hdet : Tendsto (fun t => (A t).det) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, id_eq, Matrix.det_one] using
      (continuous_id.matrix_det.continuousAt.tendsto.comp hA)
  have hsqrt : Tendsto (fun t => Real.sqrt (A t).det) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hdet)
  refine hsqrt.congr' ?_
  filter_upwards [hgram, self_mem_nhdsWithin] with t hgramt ht
  have ht0 : t ≠ 0 := ht
  have htpow : 0 < |t| ^ Fintype.card ι := pow_pos (abs_pos.mpr ht0) _
  simp only [curveDensity]
  rw [hgramt, Matrix.det_smul]
  have hpow : (t ^ 2) ^ Fintype.card ι = (t ^ Fintype.card ι) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow, Real.sqrt_mul (sq_nonneg (t ^ Fintype.card ι)),
    Real.sqrt_sq_eq_abs, abs_pow, mul_div_cancel_left₀ _ htpow.ne']

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)] in
open Filter in
theorem tendsto_curveDensity_radialJacobiField_div_pow
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) (v : ι → E)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    Tendsto (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i => radialJacobiField (I := I) g p u (v i)) t / t ^ Fintype.card ι)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  apply ((tendsto_curveDensity_radialJacobiField_div_abs_pow (I := I) g p u v hON).mono_left
    (nhdsGT_le_nhdsNE 0)).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [abs_of_pos (show 0 < t from ht)]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)] in
open Filter in
theorem tendsto_curveDensity_radialJacobiField_div_hyperbolicDensity
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (v : ι → E) (q : ℝ)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    Tendsto (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i => radialJacobiField (I := I) g p u (v i)) t /
          hyperbolicDensity q (Fintype.card ι) t)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hcd := tendsto_curveDensity_radialJacobiField_div_pow (I := I) g p u v hON
  have hmd := (tendsto_hyperbolicDensity_div_pow q (Fintype.card ι)).mono_left
    (nhdsGT_le_nhdsNE 0)
  have hcombine := hcd.div hmd one_ne_zero
  rw [div_one] at hcombine
  refine hcombine.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_div_div_cancel_right₀ (pow_ne_zero _ (show 0 < t from ht).ne') _ _

omit [T2Space M]
  [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma endpoint_det_split
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hBu : B none = u) (hperp : ∀ i, g.inner p u (B (some i)) = 0)
    {r : ℝ} (hr : 0 < r)
    (hrad : ‖r • u‖ < expMapC2Radius (I := I) g p) :
    (endpointGram (I := I) g p (r • u) B).det =
      g.inner p u u * (transverseEndGram (I := I) g p u r B).det := by
  let q : M := expMap (I := I) g p (show TangentSpace I p from r • u)
  let L := mfderiv 𝓘(ℝ, E) I
    (fun z : E => (expMap (I := I) g p
      (show TangentSpace I p from z) : M)) (r • u)
  have hfield : ∀ o : Option ι,
      radialJacobiField (I := I) g p (r • u) (B o) 1 = L (B o) := by
    intro o
    simpa only [L, tangentSpaceModelContinuousLinearEquiv_symm_apply] using
      radialJacobi_one (I := I) g p (r • u) (B o) hrad
  have hgauss := gauss_lemma_pullback (I := I) g p hrad
  have hLru : L (r • u) = r • L u := L.map_smul r u
  have hdiagRaw : g.inner q (L (r • u)) (L (r • u)) =
      g.inner p (r • u) (r • u) := by
    simpa only [q, L] using hgauss.1
  have hdiagScaled : r ^ 2 * g.inner q (L u) (L u) =
      r ^ 2 * g.inner p u u := by
    rw [hLru] at hdiagRaw
    rw [bilin_smul_both] at hdiagRaw
    have hbaseScale : g.inner p (r • u) (r • u) =
        r ^ 2 * g.inner p u u :=
      bilin_smul_both (g.inner p) r u u
    rw [hbaseScale] at hdiagRaw
    exact hdiagRaw
  have hdiag : g.inner q (L u) (L u) = g.inner p u u := by
    nlinarith [sq_pos_of_pos hr]
  have hcross : ∀ i, g.inner q (L u) (L (B (some i))) = 0 := by
    intro i
    have horth : g.inner p (r • u) (B (some i)) = 0 := by
      calc
        g.inner p (r • u) (B (some i)) =
            r * g.inner p u (B (some i)) :=
          bilin_smul_left (g.inner p) r u (B (some i))
        _ = 0 := by rw [hperp i, mul_zero]
    have hs := hgauss.2 horth
    have hsRaw : g.inner q (L (r • u)) (L (B (some i))) = 0 := by
      simpa only [q, L] using hs
    have hs' : r * g.inner q (L u) (L (B (some i))) = 0 := by
      rw [hLru] at hsRaw
      rw [bilin_smul_left] at hsRaw
      exact hsRaw
    exact (mul_eq_zero.mp hs').resolve_left hr.ne'
  let e : Option ι ≃ ι ⊕ PUnit.{1} :=
    Equiv.optionEquivSumPUnit.{0} ι
  let D : Matrix PUnit.{1} PUnit.{1} ℝ :=
    Matrix.of fun _ _ => g.inner p u u
  have hblock :
      Matrix.reindex e e (endpointGram (I := I) g p (r • u) B) =
        Matrix.fromBlocks (transverseEndGram (I := I) g p u r B)
          0 0 D := by
    ext a b
    rcases a with i | a
    · rcases b with j | b
      · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          endpointGram, Matrix.of_apply, Matrix.fromBlocks_apply₁₁,
          transverseEndGram, radialCurve]
        rfl
      · cases b
        simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inl,
          Equiv.optionEquivSumPUnit_symm_inr, endpointGram, Matrix.of_apply,
          Matrix.fromBlocks_apply₁₂, hfield, hBu]
        rw [g.symm]
        exact hcross i
    · cases a
      rcases b with j | b
      · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inr,
          Equiv.optionEquivSumPUnit_symm_inl, endpointGram, Matrix.of_apply,
          Matrix.fromBlocks_apply₂₁, hfield, hBu]
        exact hcross j
      · cases b
        simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inr, endpointGram, Matrix.of_apply,
          Matrix.fromBlocks_apply₂₂, D, hfield, hBu]
        exact hdiag
  have hreindexDet :
      (Matrix.reindex e e (endpointGram (I := I) g p (r • u) B)).det =
        (endpointGram (I := I) g p (r • u) B).det :=
    Matrix.det_reindex_self e _
  have hDdet : D.det = g.inner p u u := by
    rw [Matrix.det_unique]
    rfl
  have hdet : (endpointGram (I := I) g p (r • u) B).det =
      (transverseEndGram (I := I) g p u r B).det * D.det := by
    rw [← hreindexDet, hblock, Matrix.det_fromBlocks_zero₂₁]
  rw [hDdet] at hdet
  simpa only [mul_comm] using hdet

omit [Fintype ι] [DecidableEq ι] in
omit [T2Space M]
  [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma curveGram_end
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E) {r : ℝ}
    (hrad : ‖r • u‖ < expMapC2Radius (I := I) g p) :
    curveGram (I := I) g (radialCurve (I := I) g p u)
        (fun i => radialJacobiField (I := I) g p u (B (some i))) r =
      (r ^ 2) • transverseEndGram (I := I) g p u r B := by
  ext i j
  have hi : radialJacobiField (I := I) g p u (B (some i)) r =
      r • radialJacobiField (I := I) g p (r • u) (B (some i)) 1 := by
    rw [radialJacobi_scale (I := I) g p u (B (some i)) r]
    convert radialJacobi_one_smul
      (I := I) g p (r • u) (B (some i)) r hrad using 1
    all_goals rfl
  have hj : radialJacobiField (I := I) g p u (B (some j)) r =
      r • radialJacobiField (I := I) g p (r • u) (B (some j)) 1 := by
    rw [radialJacobi_scale (I := I) g p u (B (some j)) r]
    convert radialJacobi_one_smul
      (I := I) g p (r • u) (B (some j)) r hrad using 1
    all_goals rfl
  simp only [curveGram, Matrix.of_apply, Matrix.smul_apply, transverseEndGram]
  rw [hi, hj]
  convert bilin_smul_both
      (g.inner (radialCurve (I := I) g p u r)) r
      (radialJacobiField (I := I) g p (r • u) (B (some i)) 1)
      (radialJacobiField (I := I) g p (r • u) (B (some j)) 1) using 1
  all_goals rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma curveGram_det_scale
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E) {r : ℝ}
    (hrad : ‖r • u‖ < expMapC2Radius (I := I) g p) :
    (curveGram (I := I) g (radialCurve (I := I) g p u)
      (fun i => radialJacobiField (I := I) g p u (B (some i))) r).det =
        r ^ (2 * Fintype.card ι) *
          (transverseEndGram (I := I) g p u r B).det := by
  rw [curveGram_end (I := I) g p u B hrad, Matrix.det_smul]
  rw [← pow_mul]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private lemma model_det_ne
    (B : Module.Basis (Option ι) ℝ E) :
    (modelBasisFor B).det B ≠ 0 :=
  ((modelBasisFor B).isUnit_det B).ne_zero

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma density_det_eq
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hBu : B none = u) (hperp : ∀ i, g.inner p u (B (some i)) = 0)
    {r : ℝ} (hr : 0 < r)
    (hrad : ‖r • u‖ < expMapC2Radius (I := I) g p) :
    r ^ (2 * Fintype.card ι) * ((modelBasisFor B).det B) ^ 2 *
        (radialJacobiGram (I := I) g p (r • u)).det =
      g.inner p u u *
        (curveGram (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (B (some i))) r).det := by
  have hbasis := endpoint_det_basis (I := I) g p (r • u) B hrad
  have hsplit := endpoint_det_split (I := I) g p u B hBu hperp hr hrad
  have hcurve := curveGram_det_scale (I := I) g p u B hrad
  calc
    r ^ (2 * Fintype.card ι) * ((modelBasisFor B).det B) ^ 2 *
          (radialJacobiGram (I := I) g p (r • u)).det =
        r ^ (2 * Fintype.card ι) *
          (endpointGram (I := I) g p (r • u) B).det := by
      rw [hbasis]
      ring
    _ = r ^ (2 * Fintype.card ι) *
          (g.inner p u u * (transverseEndGram (I := I) g p u r B).det) := by
      rw [hsplit]
    _ = g.inner p u u *
          (r ^ (2 * Fintype.card ι) *
            (transverseEndGram (I := I) g p u r B).det) := by ring
    _ = g.inner p u u *
        (curveGram (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (B (some i))) r).det := by
      rw [hcurve]

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem normalDensity_curve
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hBu : B none = u)
    (hperp : ∀ i : ι, g.inner p u (B (some i)) = 0)
    {b : ℝ}
    (hsrc : MapsTo (fun r : ℝ => r • u) (Ioo (0 : ℝ) b)
      (expMapDiffeo (I := I) g p).source)
    (hrad : ∀ r ∈ Ioo (0 : ℝ) b,
      ‖r • u‖ < expMapC2Radius (I := I) g p) :
    ∃ c : ℝ, 0 < c ∧
      c = Real.sqrt (g.inner p u u) / |(modelBasisFor B).det B| ∧
      ∀ r ∈ Ioo (0 : ℝ) b,
        r ^ Fintype.card ι * normalChartDensity (I := I) g p (r • u) =
          c * curveDensity (I := I) g (radialCurve (I := I) g p u)
            (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r := by
  let a : ℝ := |(modelBasisFor B).det B|
  let s : ℝ := Real.sqrt (g.inner p u u)
  have hu : u ≠ 0 := by
    rw [← hBu]
    exact B.ne_zero none
  have hguu : 0 < g.inner p u u := g.pos p u hu
  have ha : 0 < a := by
    simpa only [a, abs_pos] using model_det_ne (B := B)
  have hs : 0 < s := Real.sqrt_pos.2 hguu
  refine ⟨s / a, div_pos hs ha, rfl, ?_⟩
  intro r hrIoo
  have hr : 0 < r := hrIoo.1
  have hxsrc : r • u ∈ (expMapDiffeo (I := I) g p).source := hsrc hrIoo
  have hxrad : ‖r • u‖ < expMapC2Radius (I := I) g p := hrad r hrIoo
  have htransLI : LinearIndependent ℝ fun i : ι => B (some i) :=
    B.linearIndependent.comp (fun i : ι => some i) (Option.some_injective ι)
  have hcurveLI : LinearIndependent ℝ fun i : ι =>
      radialJacobiField (I := I) g p u (B (some i)) r :=
    radialJacobi_li (I := I) g p u htransLI hr.ne' hxsrc hxrad
  have hcurvePos : 0 <
      (curveGram (I := I) g (radialCurve (I := I) g p u)
        (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r).det :=
    curveGram_det_pos (I := I) g (radialCurve (I := I) g p u)
      (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r hcurveLI
  have hnormalPos : 0 < (normalGramMatrix (I := I) g p (r • u)).det := by
    simpa only [normalGramMatrix] using
      paramGramMatrix_det_pos (I := I) g (expMapDiffeo (I := I) g p) hxsrc
  have hradialPos : 0 < (radialJacobiGram (I := I) g p (r • u)).det := by
    rw [← normalGram_radialMat (I := I) g p hxsrc hxrad]
    exact hnormalPos
  have hdet := density_det_eq (I := I) g p u B hBu hperp hr hxrad
  have hrpowSq : (r ^ Fintype.card ι) ^ 2 =
      r ^ (2 * Fintype.card ι) := by
    rw [← pow_mul]
    congr 1
    omega
  have haSq : a ^ 2 = ((modelBasisFor B).det B) ^ 2 := by
    simp only [a, sq_abs]
  have hsquares :
      (r ^ Fintype.card ι * a *
          Real.sqrt (radialJacobiGram (I := I) g p (r • u)).det) ^ 2 =
        (s * curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r) ^ 2 := by
    calc
      (r ^ Fintype.card ι * a *
          Real.sqrt (radialJacobiGram (I := I) g p (r • u)).det) ^ 2 =
          r ^ (2 * Fintype.card ι) * ((modelBasisFor B).det B) ^ 2 *
            (radialJacobiGram (I := I) g p (r • u)).det := by
        rw [mul_pow, mul_pow, hrpowSq, haSq, Real.sq_sqrt hradialPos.le]
      _ = g.inner p u u *
          (curveGram (I := I) g (radialCurve (I := I) g p u)
            (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r).det :=
        hdet
      _ = (s * curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r) ^ 2 := by
        simp only [s, curveDensity]
        rw [mul_pow, Real.sq_sqrt hguu.le, Real.sq_sqrt hcurvePos.le]
  have hleftNonneg : 0 ≤ r ^ Fintype.card ι * a *
      Real.sqrt (radialJacobiGram (I := I) g p (r • u)).det :=
    mul_nonneg (mul_nonneg (pow_nonneg hr.le _) ha.le) (Real.sqrt_nonneg _)
  have hrightNonneg : 0 ≤ s *
      curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r :=
    mul_nonneg hs.le (Real.sqrt_nonneg _)
  have hroot : r ^ Fintype.card ι * a *
        Real.sqrt (radialJacobiGram (I := I) g p (r • u)).det =
      s * curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r :=
    (sq_eq_sq₀ hleftNonneg hrightNonneg).1 hsquares
  rw [normalDensity_radial (I := I) g p hxsrc hxrad]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff ha.ne').2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hroot

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem normalChartDensity_zero_of_perpOrthonormal
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hBu : B none = u)
    (hperp : ∀ i, g.inner p u (B (some i)) = 0)
    (hON : ∀ i j, g.inner p (B (some i)) (B (some j)) = if i = j then 1 else 0) :
    normalChartDensity (I := I) g p 0 =
      Real.sqrt (g.inner p u u) / |(modelBasisFor B).det B| := by
  classical
  have hguu_nonneg : 0 ≤ g.inner p u u := by
    rcases eq_or_ne u 0 with hu | hu
    · rw [hu]
      change 0 ≤ g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)
      have hz : (g.inner p) (0 : TangentSpace I p) = 0 := map_zero (g.inner p)
      rw [hz]
      rfl
    · exact (g.pos p u hu).le
  have ha_ne : (modelBasisFor B).det B ≠ 0 := model_det_ne (B := B)
  have hmfd0 : mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) (0 : E) =
      ContinuousLinearMap.id ℝ E := by
    have h_eventually : expMapDiffeo (I := I) g p =ᶠ[nhds (0 : E)]
        (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) := by
      refine Filter.eventuallyEq_of_mem
        ((expMapDiffeo (I := I) g p).open_source.mem_nhds
          (zero_mem_expMapDiffeo_source (I := I) g p)) ?_
      intro v hv
      exact expMapDiffeo_apply_eq (I := I) g p hv
    rw [h_eventually.mfderiv_eq]
    exact mfderiv_expMap_at_zero (I := I) g p
  have hparam0 :
      paramGramMatrix (I := I) g (expMapDiffeo (I := I) g p) 0 =
        Matrix.reindex (basisIndexEquiv B) (basisIndexEquiv B)
          (basisGram (g.inner p) (modelBasisFor B)) := by
    ext i j
    simp only [paramGramMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      basisGram, Matrix.of_apply]
    rw [hmfd0, expMapDiffeo_zero]
    rw [show modelBasisFor B ((basisIndexEquiv B).symm i) = DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i by
      dsimp [modelBasisFor]
      rw [Module.Basis.reindex_apply]
      simp]
    rw [show modelBasisFor B ((basisIndexEquiv B).symm j) = DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j by
      dsimp [modelBasisFor]
      rw [Module.Basis.reindex_apply]
      simp]
    rfl
  have hdet0 :
      (paramGramMatrix (I := I) g (expMapDiffeo (I := I) g p) 0).det =
        (basisGram (g.inner p) (modelBasisFor B)).det := by
    rw [hparam0, Matrix.det_reindex_self]
  have hGramB : (basisGram (g.inner p) B).det = g.inner p u u := by
    let e : Option ι ≃ ι ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit.{0} ι
    let D : Matrix PUnit.{1} PUnit.{1} ℝ := Matrix.of fun _ _ => g.inner p u u
    have hblock :
        Matrix.reindex e e (basisGram (g.inner p) B) =
          Matrix.fromBlocks (1 : Matrix ι ι ℝ) 0 0 D := by
      ext a b
      rcases a with i | a
      · rcases b with j | b
        · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
            basisGram, Matrix.of_apply, Matrix.fromBlocks_apply₁₁]
          exact hON i j
        · cases b
          simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
            Equiv.optionEquivSumPUnit_symm_inl, Equiv.optionEquivSumPUnit_symm_inr,
            basisGram, Matrix.of_apply, Matrix.fromBlocks_apply₁₂, hBu, D]
          rw [g.symm p (B (some i)) u]
          exact hperp i
      · cases a
        rcases b with j | b
        · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
            Equiv.optionEquivSumPUnit_symm_inr, Equiv.optionEquivSumPUnit_symm_inl,
            basisGram, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, hBu]
          exact hperp j
        · cases b
          rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂]
          change g.inner p (B none) (B none) = D PUnit.unit PUnit.unit
          rw [hBu]
          rfl
    have hreindexDet : (Matrix.reindex e e (basisGram (g.inner p) B)).det =
        (basisGram (g.inner p) B).det := Matrix.det_reindex_self e _
    have hDdet : D.det = g.inner p u u := by
      rw [Matrix.det_unique]
      rfl
    rw [← hreindexDet, hblock, Matrix.det_fromBlocks_zero₂₁]
    simp
    rfl
  have hdetrel : (basisGram (g.inner p) B).det =
      ((modelBasisFor B).det B) ^ 2 * (basisGram (g.inner p) (modelBasisFor B)).det := by
    have h := gram_det_change (β := g.inner p) (L := ContinuousLinearMap.id ℝ E)
      (e := modelBasisFor B) (B := B)
    have hleft : basisGram (g.inner p) (fun i => (ContinuousLinearMap.id ℝ E) (B i)) =
        basisGram (g.inner p) B := by
      ext i j
      rfl
    have hright : basisGram (g.inner p)
        (fun i => (ContinuousLinearMap.id ℝ E) ((modelBasisFor B) i)) =
        basisGram (g.inner p) (modelBasisFor B) := by
      ext i j
      rfl
    exact (congrArg Matrix.det hleft).symm.trans
      (h.trans (congrArg (fun A => ((modelBasisFor B).det B) ^ 2 * A.det) hright))
  have hXeq : (basisGram (g.inner p) (modelBasisFor B)).det =
      g.inner p u u / ((modelBasisFor B).det B) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 ha_ne)]
    rw [mul_comm]
    exact ((hGramB.symm).trans hdetrel).symm
  have hXnonneg : 0 ≤ (basisGram (g.inner p) (modelBasisFor B)).det := by
    rw [hXeq]
    exact div_nonneg hguu_nonneg (sq_nonneg _)
  have hmain :
      Real.sqrt (g.inner p u u) / |(modelBasisFor B).det B| =
        Real.sqrt ((basisGram (g.inner p) (modelBasisFor B)).det) := by
    have hsq :
        (Real.sqrt (g.inner p u u) / |(modelBasisFor B).det B|) ^ 2 =
          (Real.sqrt ((basisGram (g.inner p) (modelBasisFor B)).det)) ^ 2 := by
      calc
        (Real.sqrt (g.inner p u u) / |(modelBasisFor B).det B|) ^ 2 =
            g.inner p u u / ((modelBasisFor B).det B) ^ 2 := by
              rw [div_pow, Real.sq_sqrt hguu_nonneg, sq_abs]
        _ = (basisGram (g.inner p) (modelBasisFor B)).det := hXeq.symm
        _ = (Real.sqrt ((basisGram (g.inner p) (modelBasisFor B)).det)) ^ 2 :=
          (Real.sq_sqrt hXnonneg).symm
    exact (sq_eq_sq₀ (div_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (Real.sqrt_nonneg _)).1 hsq
  rw [normalChartDensity_apply, paramDensity_apply, hdet0]
  exact hmain.symm

end PolarDensity

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
