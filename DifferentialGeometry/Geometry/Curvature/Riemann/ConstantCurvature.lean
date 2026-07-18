import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.EinsteinMetric
import DifferentialGeometry.Geometry.Curvature.CoordRm04Bridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff RealInnerProductSpace
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure (chartModelBasis)
open DifferentialGeometry.Integral.DivergenceTheorem (chartRiemannTensor chartGramOnE chartGramOnE_def)

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private lemma basis_inner_chartGram_center
    (g : SmoothRiemannianMetric I M) (x : M) (a b : Fin (Module.finrank ℝ E)) :
    g.inner x (chartModelBasis E a) (chartModelBasis E b)
      = chartGramOnE (I := I) g x a b (extChartAt I x x) := by
  rw [← chartBasisVecFiber_self (I := I) x a, ← chartBasisVecFiber_self (I := I) x b,
      ← DifferentialGeometry.Integral.Measure.chartGramMatrix_apply g x x a b, chartGramOnE_def,
      (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)]

private lemma g_inner_center
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g.inner x v w
      = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr v a * (chartModelBasis E).repr w b *
            chartGramOnE (I := I) g x a b (extChartAt I x x) := by
  classical
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hxsrc : x ∈ (extChartAt I x).source := mem_extChartAt_source (I := I) x
  rw [g_inner_eq_chart_sum (I := I) g x hx hxsrc v w]
  simp only [trivToE_self_apply (I := I) x v, trivToE_self_apply (I := I) x w]

private lemma reprR (g : SmoothRiemannianMetric I M) (x : M) (X Y : TangentSpace I x)
    (b : Fin (Module.finrank ℝ E)) :
    (chartModelBasis E).repr (chartRiemannCLM (I := I) g x X Y Y) b
      = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr Y i * (chartModelBasis E).repr X j *
              (chartModelBasis E).repr Y k *
              chartRiemannTensor (I := I) g x i j k b (extChartAt I x x) := by
  classical
  rw [chartRiemannCLM_apply g x X Y Y]
  simp only [map_sum, LinearEquiv.map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
    (fun j _ => Finset.sum_congr rfl (fun k _ => ?_)))
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl, mul_one]
  · intro l _ hl; rw [if_neg hl, mul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h

private lemma metricRm04Std_eq_sectionalNumerator
    (g : SmoothRiemannianMetric I M) (x : M) (X Y : TangentSpace I x) :
    metricRm04StdAt (I := I) g x X Y Y X
      = sectionalCurvatureNumerator (I := I) g x X Y := by
  classical
  rw [metricRm04StdAt_eq_chartRiemannCLM g x X Y Y X,
      g_inner_center g x X (chartRiemannCLM (I := I) g x X Y Y)]
  simp only [reprR g x X Y]
  rw [sectionalCurvatureNumerator_def]
  simp only [chartRiemannLower_def, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => ?_)))))
  ring

private lemma exists_gOrthonormalBasis_first
    (g : SmoothRiemannianMetric I M) (x : M) {m : ℕ}
    (hm : Module.finrank ℝ E = m + 1)
    (T : TangentSpace I x) (hT : g.inner x T T = 1) :
    ∃ basis : Module.Basis (Fin (m + 1)) ℝ (TangentSpace I x),
      (∀ a b, g.inner x (basis a) (basis b) = if a = b then 1 else 0) ∧ basis 0 = T := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  have hfr : Module.finrank ℝ (TangentSpace I x) = Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_fin]
    exact (show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl).trans hm
  have hTnorm : ‖T‖ = 1 := by
    have hsq : ‖T‖ * ‖T‖ = 1 := by
      rw [← real_inner_self_eq_norm_mul_norm, hinner_eq]; exact hT
    nlinarith [norm_nonneg T]
  have hsingle : Orthonormal ℝ (({0} : Set (Fin (m + 1))).restrict (fun _ => T)) := by
    haveI : Subsingleton ↥({0} : Set (Fin (m + 1))) :=
      ⟨fun a b => Subtype.ext
        ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)⟩
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl]
    simp only [Set.restrict_apply]
    rw [real_inner_self_eq_norm_mul_norm, hTnorm, mul_one]
  obtain ⟨bu, hbu⟩ := hsingle.exists_orthonormalBasis_extension_of_card_eq hfr
  have hbu0 : bu 0 = T := hbu 0 (by simp)
  refine ⟨bu.toBasis, ?_, ?_⟩
  · intro a b
    rw [OrthonormalBasis.coe_toBasis, ← hinner_eq]
    have ho := bu.orthonormal
    rw [orthonormal_iff_ite] at ho
    exact ho a b
  · rw [OrthonormalBasis.coe_toBasis]; exact hbu0

private lemma ricci_symm
    (g : SmoothRiemannianMetric I M) (x : M) (U V : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) U V)
      = metricRicciAt (I := I) g x (vec2 (I := I) V U) := by
  classical
  have key :
      metricRicci (I := I) (M := M) g x
          (fun q : Fin 2 => if q = 0 then U else V) =
        metricRicci (I := I) (M := M) g x
          (fun q : Fin 2 => if q = 0 then V else U) := by
    let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis
      (I := I) x
    let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) E →
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) E → ℝ :=
      fun i j =>
        DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
          (I := I) g x i j (extChartAt I x x)
    have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv := by
      simpa [basis, gInv] using
        (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
          (I := I) g x)
    have hcomp :
        ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) E,
          metricRicci (I := I) (M := M) g x
              (fun q : Fin 2 => if q = 0 then basis i else basis j) =
            metricRicci (I := I) (M := M) g x
              (fun q : Fin 2 => if q = 0 then basis j else basis i) := by
      intro i j
      simpa [basis, metricRicci_apply,
        DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply] using
        (metricRicciSymm (I := I) (M := M) g basis gInv hinv i j)
    exact
      DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
        (I := I) basis (metricRicci (I := I) (M := M) g x) hcomp U V
  rw [metricRicci_apply] at key
  exact key

private lemma ricci_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (a b c : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) (a + b) c)
      = metricRicciAt (I := I) g x (vec2 (I := I) a c)
        + metricRicciAt (I := I) g x (vec2 (I := I) b c) := by
  classical
  have h := Tensor0SBundle.Tensor0SSpace.map_update_add
    (metricRicciAt (I := I) (M := M) g x) (vec2 (I := I) a c) 0 a b
  have e0 : Function.update (vec2 (I := I) a c) 0 (a + b) = vec2 (I := I) (a + b) c := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e1 : Function.update (vec2 (I := I) a c) 0 a = vec2 (I := I) a c := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e2 : Function.update (vec2 (I := I) a c) 0 b = vec2 (I := I) b c := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  rw [e0, e1, e2] at h
  exact h

private lemma ricci_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (a b c : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) a (b + c))
      = metricRicciAt (I := I) g x (vec2 (I := I) a b)
        + metricRicciAt (I := I) g x (vec2 (I := I) a c) := by
  classical
  have h := Tensor0SBundle.Tensor0SSpace.map_update_add
    (metricRicciAt (I := I) (M := M) g x) (vec2 (I := I) a b) 1 b c
  have e0 : Function.update (vec2 (I := I) a b) 1 (b + c) = vec2 (I := I) a (b + c) := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e1 : Function.update (vec2 (I := I) a b) 1 b = vec2 (I := I) a b := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e2 : Function.update (vec2 (I := I) a b) 1 c = vec2 (I := I) a c := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  rw [e0, e1, e2] at h
  exact h

private lemma ricci_diag_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (T : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) (c • T) (c • T))
      = c ^ 2 * metricRicciAt (I := I) g x (vec2 (I := I) T T) := by
  classical
  have h := Tensor0SBundle.Tensor0SSpace.map_smul_univ
    (metricRicciAt (I := I) (M := M) g x) (fun _ : Fin 2 => c)
    (vec2 (I := I) T T)
  have e : (fun i : Fin 2 => c • (vec2 (I := I) T T) i)
      = vec2 (I := I) (c • T) (c • T) := by
    funext q; fin_cases q <;> simp [vec2]
  rw [e] at h
  rw [h, Fin.prod_univ_two, smul_eq_mul, sq]

private lemma ricci_zero
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) g x
        (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
  have h := ricci_diag_smul (I := I) g x 0 (0 : TangentSpace I x)
  simpa using h

private lemma ricci_diag_unit
    (g : SmoothRiemannianMetric I M) (K : ℝ)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      sectionalCurvatureDenominator (I := I) g p v w ≠ 0 →
        sectionalCurvature (I := I) g p v w = K)
    (x : M) (T : TangentSpace I x) (hT : g.inner x T T = 1) :
    metricRicciAt (I := I) g x (vec2 (I := I) T T)
      = K * ((Module.finrank ℝ E : ℝ) - 1) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank ℝ E = m + 1 :=
    ⟨Module.finrank ℝ E - 1, by
      have : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
      omega⟩
  obtain ⟨basis, hON, h0⟩ := exists_gOrthonormalBasis_first (I := I) g x hm T hT
  have hframe := metricRicci_velocity_eq_sum_rm04_frame (I := I) g basis hON
    h0 (fun i => rfl)
  rw [metricRicci_apply] at hframe
  have hterm : ∀ i : Fin m,
      metricRm04StdAt (I := I) g x (basis i.succ) T T (basis i.succ) = K := by
    intro i
    have hEE : g.inner x (basis i.succ) (basis i.succ) = 1 := by
      have := hON i.succ i.succ; simpa using this
    have hET : g.inner x (basis i.succ) T = 0 := by
      have h := hON i.succ 0
      rw [h0] at h
      rw [if_neg (Fin.succ_ne_zero i)] at h
      exact h
    have hDenom : sectionalCurvatureDenominator (I := I) g x (basis i.succ) T = 1 := by
      rw [sectionalCurvatureDenominator_def, hEE, hT, hET]; ring
    have hsecK : sectionalCurvature (I := I) g x (basis i.succ) T = K :=
      hsec x (basis i.succ) T (by rw [hDenom]; exact one_ne_zero)
    have hNum : sectionalCurvatureNumerator (I := I) g x (basis i.succ) T = K := by
      rw [sectionalCurvature_def, hDenom, div_one] at hsecK
      exact hsecK
    rw [metricRm04Std_eq_sectionalNumerator, hNum]
  have hsum : (∑ i : Fin m,
      metricRm04StdAt (I := I) g x (basis i.succ) T T (basis i.succ))
      = K * ((Module.finrank ℝ E : ℝ) - 1) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm]
    push_cast; ring
  calc metricRicciAt (I := I) g x (vec2 (I := I) T T)
      = ∑ i : Fin m,
          metricRm04StdAt (I := I) g x (basis i.succ) T T (basis i.succ) := hframe
    _ = K * ((Module.finrank ℝ E : ℝ) - 1) := hsum

private lemma ricci_diag_all
    (g : SmoothRiemannianMetric I M) (K : ℝ)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      sectionalCurvatureDenominator (I := I) g p v w ≠ 0 →
        sectionalCurvature (I := I) g p v w = K)
    (x : M) (u : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) u u)
      = K * ((Module.finrank ℝ E : ℝ) - 1) * g.inner x u u := by
  classical
  by_cases hu : u = 0
  · subst hu
    rw [ricci_zero]
    simp
  · have hpos : 0 < g.inner x u u := g.pos x u hu
    set c := Real.sqrt (g.inner x u u) with hc
    have hcpos : 0 < c := Real.sqrt_pos.mpr hpos
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have hc2 : c ^ 2 = g.inner x u u := Real.sq_sqrt hpos.le
    set T := c⁻¹ • u with hTdef
    have hTunit : g.inner x T T = 1 := by
      have h1 : g.inner x T T = c⁻¹ * (c⁻¹ * g.inner x u u) := by
        rw [hTdef, map_smul (g.inner x) c⁻¹ u, ContinuousLinearMap.smul_apply,
            smul_eq_mul, map_smul (g.inner x u) c⁻¹ u, smul_eq_mul]
      rw [h1, ← hc2, sq]; field_simp
    have hdu := ricci_diag_unit (I := I) g K hsec x T hTunit
    have huT : u = c • T := by
      rw [hTdef, smul_smul, mul_inv_cancel₀ hcne, one_smul]
    have hLHS : metricRicciAt (I := I) g x (vec2 (I := I) u u)
        = c ^ 2 * (K * ((Module.finrank ℝ E : ℝ) - 1)) := by
      rw [huT, ricci_diag_smul, hdu]
    rw [hLHS, ← hc2]; ring

theorem einstein_of_constant_sectionalCurvature
    (g : SmoothRiemannianMetric I M) (K : Real)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      sectionalCurvatureDenominator (I := I) g p v w ≠ 0 →
        sectionalCurvature (I := I) g p v w = K) :
    DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g
      (K * ((Module.finrank Real E : Real) - 1)) := by
  intro x v w
  have dvw := ricci_diag_all (I := I) g K hsec x (v + w)
  have dv := ricci_diag_all (I := I) g K hsec x v
  have dw := ricci_diag_all (I := I) g K hsec x w
  have hExpand : metricRicciAt (I := I) g x (vec2 (I := I) (v + w) (v + w))
      = metricRicciAt (I := I) g x (vec2 (I := I) v v)
        + metricRicciAt (I := I) g x (vec2 (I := I) v w)
        + metricRicciAt (I := I) g x (vec2 (I := I) w v)
        + metricRicciAt (I := I) g x (vec2 (I := I) w w) := by
    rw [ricci_add_left, ricci_add_right, ricci_add_right]; ring
  have hsym := ricci_symm (I := I) g x w v
  have hG : g.inner x (v + w) (v + w)
      = g.inner x v v + g.inner x v w + g.inner x w v + g.inner x w w := by
    rw [map_add (g.inner x) v w, ContinuousLinearMap.add_apply,
        map_add (g.inner x v) v w, map_add (g.inner x w) v w]; ring
  have hgsym : g.inner x w v = g.inner x v w := g.symm x w v
  linear_combination (1 / 2) * dvw - (1 / 2) * hExpand
    + (K * ((Module.finrank Real E : Real) - 1) / 2) * hG
    - (1 / 2) * dv - (1 / 2) * dw - (1 / 2) * hsym
    + (K * ((Module.finrank Real E : Real) - 1) / 2) * hgsym

end Riemannian
end Geometry
end DifferentialGeometry
