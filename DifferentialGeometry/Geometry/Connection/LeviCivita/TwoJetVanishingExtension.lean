import DifferentialGeometry.Geometry.Connection.LeviCivita.LinearExtensionTangent
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Geometry.Operator.HessianTrace
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleNabla

/-!
# A controlled smooth tangent extension with vanishing covariant `2`-jet at the basepoint

For a smooth Riemannian metric `g` on a closed manifold, a base point `x₀ : M`, and a fibre
vector `v : TangentSpace I x₀`, this file isolates the **covariant-`2`-jet-vanishing** smooth
tangent extension `W : Π b, TangentSpace I b` of `v`: a smooth section with

* `W x₀ = v` (it extends `v`);
* `∇_u W (x₀) = 0` for every direction `u` — the covariant `1`-jet vanishes; and
* `∇_Y(∇_Y W)(x₀) = 0` for every smooth field `Y` — the iterated covariant `2`-jet vanishes.

Such an extension is the geometric device that turns the genuine per-direction third-order
cancellation residue of `MovingFrameRemainderFrameSumBridge`/`SecondOrderCommutationResidueFiberBound`
into a *pure curvature* contraction reading only `v`: in the second-order leading-slot commutation
residue `secondOrderResidue g s S x i w` the four covariant-derivative-of-`w` summands —
`R(B, ∇_B w) V`, `∇_{[B, w]}(∇_B V)` (through `∇_B w`), `∇_B(∇_{∇_B w} V)`, and the iterated
`∇_B(∇_B w)`-direction term — all read the covariant `1`- or `2`-jet of `w` at `x`, which the
vanishing-`2`-jet extension kills, leaving only the order-`≤ 2` curvature contractions of `V` against
the `(∇R)` and `R` classes.

The construction is the **chart-coordinate quadratic correction** of the coordinate-constant linear
extension `linearExtensionTangent x₀ v` (`LinearExtensionTangent`): the linear extension already has a
vanishing chart-derivative near `x₀`, so its covariant `1`-jet at `x₀` is the pure metric Christoffel
correction (`covApply_linearExtensionTangent_basepoint_eq`) and its covariant `2`-jet is the chart
`∂Γ + Γ·Γ` contraction (`covApply_covApply_linearExtensionTangent_basepoint_eq`); subtracting the
degree-`1` and degree-`2` chart polynomials reproducing those corrections cancels the covariant
`1`- and `2`-jets without disturbing the basepoint value.

## Main results

* `covApply_covApply_linearExtensionTangent_basepoint_eq` — the basepoint chart formula for the
  iterated covariant derivative `∇_v(∇_v(linearExtensionTangent x₀ w))(x₀)` in terms of the chart
  Christoffel derivative `∂Γ` (`fderiv` of `chartChristoffel`), the quadratic `Γ·Γ` contraction, and
  the coordinate `tangentCoord x₀ w`. (Posited chart sub-node.)
* `exists_twoJetVanishing_tangentExtension` — the existence of a smooth covariant-`2`-jet-vanishing
  tangent extension of `v`. (Posited geometric construction.)
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Where the bump is eventually `1` near `b` (and `b` lies in the trivialization base set),
the chart-trivialised representation of `linearExtensionTangent x₀ w` is eventually equal to the
constant model coordinate `tangentCoord x₀ w` near `b`. This is the base-set/bump-`1`
localisation behind the vanishing chart derivative of the coordinate-constant field. -/
private lemma chartE_section_repr_linExt_eventuallyEq_const_at
    (x₀ : M) (w : TangentSpace I x₀) {b : M}
    (hb1 : (linExtBump (I := I) x₀ : M → ℝ) =ᶠ[𝓝 b] (fun _ => (1 : ℝ)))
    (hbbase : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 b) :
    chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w)
      =ᶠ[𝓝 b] (fun _ : M => tangentCoord (I := I) x₀ w) := by
  classical
  filter_upwards [hb1, hbbase] with c hc1 hcbase
  have hWc : linearExtensionTangent (I := I) x₀ w c =
      coordExtensionTangent (I := I) x₀ w c := by
    rw [linearExtensionTangent_apply, hc1, one_smul]
  rw [chartE_section_repr_eq_trivToE, hWc, ← chartE_section_repr_eq_trivToE]
  exact chartE_section_repr_coordExtensionTangent_eq (I := I) x₀ w hcbase

/-- **First Christoffel layer (pointwise) for the linear extension.** At a good-set point `b`
of the chart at `x₀` where the bump is eventually `1` near `b`, the covariant-derivative value
`(LeviCivita g) (linExt x₀ w) b (linExt x₀ v b)` equals
`trivFromE x₀ b (christoffelCorrection g x₀ b (tangentCoord x₀ w) (linExt x₀ v b))`. The chart
derivative of the coordinate-constant representation vanishes, leaving only the metric
Christoffel correction. -/
private lemma LeviCivita_covApply_linExt_firstLayer_pointwise
    (g : SmoothRiemannianMetric I M) (x₀ : M) (w v : TangentSpace I x₀)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) x₀)
    (hb1 : (linExtBump (I := I) x₀ : M → ℝ) =ᶠ[𝓝 b] (fun _ => (1 : ℝ))) :
    (LeviCivita (I := I) g).toFun (linearExtensionTangent (I := I) x₀ w) b
        (linearExtensionTangent (I := I) x₀ v b) =
      trivFromE (I := I) x₀ b
        (christoffelCorrection (I := I) g x₀ b (tangentCoord (I := I) x₀ w)
          (linearExtensionTangent (I := I) x₀ v b)) := by
  classical
  have hbbase : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 b :=
    (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) hb)
  have hconst := chartE_section_repr_linExt_eventuallyEq_const_at (I := I) x₀ w hb1 hbbase
  have hWat : MDiffAt (T% (linearExtensionTangent (I := I) x₀ w)) b :=
    (linearExtensionTangent_smooth (I := I) x₀ w).mdifferentiableAt (by norm_num)
  rw [LeviCivita_chart_apply (I := I) g x₀ hb hWat
    (linearExtensionTangent (I := I) x₀ v b)]
  rw [chartLeviCivita_apply (I := I) g x₀ (linearExtensionTangent (I := I) x₀ w) hb
    (linearExtensionTangent (I := I) x₀ v b)]
  have hfd0 :
      fderiv ℝ (chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w)
          ∘ (extChartAt I x₀).symm) (extChartAt I x₀ b) = 0 := by
    have hb_src : b ∈ (extChartAt I x₀).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
    have hev :
        (chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w)
            ∘ (extChartAt I x₀).symm)
          =ᶠ[𝓝 (extChartAt I x₀ b)] (fun _ : E => tangentCoord (I := I) x₀ w) := by
      have hsymm_cont : ContinuousAt (extChartAt I x₀).symm (extChartAt I x₀ b) := by
        have hb_tgt : extChartAt I x₀ b ∈ (extChartAt I x₀).target :=
          (extChartAt I x₀).map_source hb_src
        exact (continuousOn_extChartAt_symm x₀).continuousAt
          ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hb_tgt)
      have hsymm_pt : (extChartAt I x₀).symm (extChartAt I x₀ b) = b :=
        (extChartAt I x₀).left_inv hb_src
      have hmem :
          {c : M | chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w) c
            = tangentCoord (I := I) x₀ w} ∈ 𝓝 ((extChartAt I x₀).symm (extChartAt I x₀ b)) := by
        rw [hsymm_pt]; exact hconst
      filter_upwards [hsymm_cont.preimage_mem_nhds hmem] with y hy using hy
    rw [hev.fderiv_eq, fderiv_const_apply]
  rw [hfd0, ContinuousLinearMap.zero_apply, zero_add]
  have hreprb : chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w) b =
      tangentCoord (I := I) x₀ w := hconst.self_of_nhds
  rw [hreprb]

/-- **First Christoffel layer (neighbourhood) for the linear extension.** The chart-trivialised
representation of the intermediate section
`S := covApply (LeviCivita g) (linExt x₀ v) (linExt x₀ w)`, pulled through `(extChartAt I x₀).symm`,
is eventually equal near `φ x₀` to the chart-Christoffel contraction
`y ↦ ∑_{i,j,m} Vᵢ Wⱼ Γᵐᵢⱼ(y) • eₘ` of the constant coordinates `V := tangentCoord x₀ v`,
`W := tangentCoord x₀ w`. -/
private lemma chartE_section_repr_covApply_linExt_eventuallyEq
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : TangentSpace I x₀) :
    (chartE_section_repr (I := I) x₀
        (Connection.covApply (LeviCivita (I := I) g)
          (linearExtensionTangent (I := I) x₀ v) (linearExtensionTangent (I := I) x₀ w))
        ∘ (extChartAt I x₀).symm)
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
        (fun y : E =>
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) i *
                  ((chartModelBasis E).repr (tangentCoord (I := I) x₀ w)) j *
                  chartChristoffel (I := I) g x₀ i j m y) •
                (chartModelBasis E) m) := by
  classical
  have hbump1 : {b : M | (linExtBump (I := I) x₀ : M → ℝ) b = 1} ∈ 𝓝 x₀ :=
    (linExtBump (I := I) x₀).eventuallyEq_one
  obtain ⟨W₀, hW₀_sub, hW₀_open, hx₀W₀⟩ := mem_nhds_iff.mp hbump1
  have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) x₀) :=
    chartLeviCivitaGoodSet_isOpen (I := I) x₀
  set Vset : Set E :=
    (extChartAt I x₀).target ∩
      (extChartAt I x₀).symm ⁻¹' (chartLeviCivitaGoodSet (I := I) x₀ ∩ W₀) with hVset_def
  have hcont_symm : ContinuousOn (extChartAt I x₀).symm (extChartAt I x₀).target :=
    continuousOn_extChartAt_symm x₀
  have hVset_open : IsOpen Vset :=
    hcont_symm.isOpen_inter_preimage (isOpen_extChartAt_target (I := I) x₀)
      (hgood_open.inter hW₀_open)
  have hx₀_good : x₀ ∈ chartLeviCivitaGoodSet (I := I) x₀ :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀)
  have hx₀src_ext : x₀ ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x₀
  have hx₀tgt : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hx₀src_ext
  have hφx₀V : extChartAt I x₀ x₀ ∈ Vset := by
    refine ⟨hx₀tgt, ?_⟩
    rw [Set.mem_preimage, (extChartAt I x₀).left_inv hx₀src_ext]
    exact ⟨hx₀_good, hx₀W₀⟩
  filter_upwards [hVset_open.mem_nhds hφx₀V] with y hy
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  rw [Set.mem_preimage] at hy_pre
  obtain ⟨hy_good, hy_W₀⟩ := hy_pre
  set b : M := (extChartAt I x₀).symm y with hb_def
  have hbbase : b ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hy_good
  have hb1 : (linExtBump (I := I) x₀ : M → ℝ) =ᶠ[𝓝 b] (fun _ => (1 : ℝ)) := by
    filter_upwards [hW₀_open.mem_nhds hy_W₀] with c hc using hW₀_sub hc
  simp only [Function.comp_apply, chartE_section_repr_eq_trivToE, Connection.covApply_apply]
  rw [show (LeviCivita (I := I) g).toFun (linearExtensionTangent (I := I) x₀ w) b
        (linearExtensionTangent (I := I) x₀ v b) =
      trivFromE (I := I) x₀ b
        (christoffelCorrection (I := I) g x₀ b (tangentCoord (I := I) x₀ w)
          (linearExtensionTangent (I := I) x₀ v b)) from
    LeviCivita_covApply_linExt_firstLayer_pointwise (I := I) g x₀ w v hy_good hb1]
  rw [trivToE_trivFromE (I := I) x₀ hbbase]
  rw [christoffelCorrection_apply (I := I) g x₀ b (tangentCoord (I := I) x₀ w)
    (linearExtensionTangent (I := I) x₀ v b)]
  have hreprVb :
      (chartModelBasis E).repr
          (trivToE (I := I) x₀ b (linearExtensionTangent (I := I) x₀ v b)) =
        (chartModelBasis E).repr (tangentCoord (I := I) x₀ v) := by
    have hVb : chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ v) b =
        tangentCoord (I := I) x₀ v :=
      (chartE_section_repr_linExt_eventuallyEq_const_at (I := I) x₀ v hb1
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hbbase)).self_of_nhds
    rw [chartE_section_repr_eq_trivToE] at hVb
    rw [hVb]
  have hφb : extChartAt I x₀ b = y := by
    rw [hb_def, (extChartAt I x₀).right_inv hy_tgt]
  rw [hreprVb, hφb]

/-- Each chart Christoffel symbol is differentiable at the chart image `φ x₀` (it is `C^∞` on the
interior of the chart target, which contains `φ x₀`). -/
private lemma chartChristoffel_differentiableAt_basepoint
    (g : SmoothRiemannianMetric I M) (x₀ : M) (i j m : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
      (extChartAt I x₀ x₀) := by
  classical
  have hx₀src_ext : x₀ ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x₀
  have hx₀tgt : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hx₀src_ext
  have hx₀int : extChartAt I x₀ x₀ ∈ interior ((extChartAt I x₀).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x₀ hx₀tgt
  have hcd : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g x₀ i j m)
      (interior (extChartAt I x₀).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g x₀ i j m
  exact (hcd.differentiableOn (by norm_num)).differentiableAt
    (isOpen_interior.mem_nhds hx₀int)

/-- The Fréchet derivative, at `φ x₀` in a direction `d : E`, of the coordinate-Christoffel
contraction `y ↦ ∑_{i,j,m} Vᵢ Wⱼ Γᵐᵢⱼ(y) • eₘ` expands as
`∑_{i,j,m} Vᵢ Wⱼ (∂_d Γᵐᵢⱼ)(φ x₀) • eₘ`. -/
private lemma fderiv_christoffelVWSum_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (V W : E) (d : E) :
    fderiv ℝ
        (fun y : E =>
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                  chartChristoffel (I := I) g x₀ i j m y) • (chartModelBasis E) m)
        (extChartAt I x₀ x₀) d =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
              (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                (extChartAt I x₀ x₀)) d) • (chartModelBasis E) m := by
  classical
  have hdiff_inner : ∀ i j m : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y : E =>
        (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
            chartChristoffel (I := I) g x₀ i j m y) • (chartModelBasis E) m)
        (extChartAt I x₀ x₀) := by
    intro i j m
    exact (((chartChristoffel_differentiableAt_basepoint (I := I) g x₀ i j m).const_mul
      (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j)).smul_const
      ((chartModelBasis E) m))
  rw [fderiv_fun_sum (fun i _ => DifferentiableAt.fun_sum
    (fun j _ => DifferentiableAt.fun_sum (fun m _ => hdiff_inner i j m)))]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fderiv_fun_sum (fun j _ => DifferentiableAt.fun_sum (fun m _ => hdiff_inner i j m))]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [fderiv_fun_sum (fun m _ => hdiff_inner i j m)]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [fderiv_smul_const (((chartChristoffel_differentiableAt_basepoint (I := I) g x₀ i j m).const_mul
    (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j)))
    ((chartModelBasis E) m)]
  rw [ContinuousLinearMap.smulRight_apply]
  rw [fderiv_const_mul (chartChristoffel_differentiableAt_basepoint (I := I) g x₀ i j m)
    (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j)]
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc]

/-- Collect a `3`-fold-indexed family of scalar-multiples of a basis vector indexed by the
innermost variable, factoring the basis vector out of the inner two sums. -/
private lemma sum3_collect_basis_inner
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      ∑ z : Fin (Module.finrank ℝ E), (F a b z) • (chartModelBasis E) z) =
      ∑ z : Fin (Module.finrank ℝ E),
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F a b z) •
          (chartModelBasis E) z := by
  classical
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ z : Fin (Module.finrank ℝ E), (F a b z) • (chartModelBasis E) z) =
      ∑ z : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E), (F a b z) • (chartModelBasis E) z from by
    simp_rw [← Finset.sum_product']
    refine Finset.sum_nbij' (fun x => (x.2.2, x.1, x.2.1)) (fun x => (x.2.1, x.2.2, x.1))
      (fun x _ => Finset.mem_univ _) (fun x _ => Finset.mem_univ _)
      (fun x _ => by ext <;> simp) (fun x _ => by ext <;> simp) (fun x _ => rfl)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_smul]

/-- Collect a `5`-fold-indexed family of scalar-multiples of a basis vector indexed by the
innermost variable, factoring the basis vector out of the inner four sums. -/
private lemma sum5_collect_basis_inner
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        ∑ z : Fin (Module.finrank ℝ E), (F a b c d z) • (chartModelBasis E) z) =
      ∑ z : Fin (Module.finrank ℝ E),
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            F a b c d z) • (chartModelBasis E) z := by
  classical

  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ∑ z : Fin (Module.finrank ℝ E), (F a b c d z) • (chartModelBasis E) z) =
      ∑ z : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E), (F a b c d z) • (chartModelBasis E) z from by
    simp_rw [← Finset.sum_product']
    refine Finset.sum_nbij' (fun x => (x.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1))
      (fun x => (x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.1))
      (fun x _ => Finset.mem_univ _) (fun x _ => Finset.mem_univ _)
      (fun x _ => by ext <;> simp) (fun x _ => by ext <;> simp) (fun x _ => rfl)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_smul]

/-- Reindex a `4`-fold scalar sum from `(p,q,i,j)`-order to `(i,j,p,q)`-order. -/
private lemma sum4_scalar_swap_pairs
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ) :
    (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E), F p q i j) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E), F p q i j := by
  classical
  simp_rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1))
    (fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)) (fun x _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_univ _) (fun x _ => by ext <;> simp) (fun x _ => by ext <;> simp)
    (fun x _ => rfl)

/-- The `q`-coordinate in `chartModelBasis E` of the coordinate-Christoffel value
`∑_{i,j,m} Vᵢ Wⱼ Γᵐᵢⱼ(y) • eₘ` is `∑_{i,j} Vᵢ Wⱼ Γᵍᵢⱼ(y)`. -/
private lemma chartModelBasis_repr_christoffelVWSum
    (g : SmoothRiemannianMetric I M) (x₀ : M) (V W : E) (y : E)
    (q : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                chartChristoffel (I := I) g x₀ i j m y) • (chartModelBasis E) m)) q =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
          chartChristoffel (I := I) g x₀ i j q y := by
  classical
  rw [map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_sum]
  simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single q
    (fun m _ hm => by rw [Module.Basis.repr_self_apply, if_neg hm, mul_zero])
    (fun hq => absurd (Finset.mem_univ q) hq)]
  rw [Module.Basis.repr_self_apply, if_pos rfl, mul_one]

/-- **The basepoint chart formula for the iterated covariant derivative of the linear extension
(`∂Γ`-sub-node, posited).** For the coordinate-constant linear extension `linearExtensionTangent x₀ w`
(`LinearExtensionTangent`), the iterated tangent covariant derivative
`∇_v(∇_v(linearExtensionTangent x₀ w))(x₀)` along a fixed direction `v` collapses, at the basepoint, to
the chart-coordinate second-order contraction of the model coordinate `tangentCoord x₀ w` against the
chart Christoffel derivative `∂Γ` (the `fderiv` of `chartChristoffel`) and the quadratic `Γ·Γ` term:
```
∇_v(∇_v W)(x₀) = trivFromE x₀ x₀ ( ∑ᵢⱼₖₗ (vᵏ vⁱ wʲ) · (∂ₖ Γᵐᵢⱼ)(φ x₀) · eₘ
                                     + ∑ᵢⱼₖₗₘ (vⁱ vᵏ wʲ) · Γᵐₖₗ(φ x₀) · Γˡᵢⱼ(φ x₀) · eₘ ),
```
with `W := linearExtensionTangent x₀ w`, `v`-coordinates and `w := tangentCoord x₀ w` taken in the
`chartModelBasis`, and `Γ = chartChristoffel g x₀`. The bump and the (vanishing near `x₀`) chart
derivative of the coordinate-constant field contribute nothing; only the once-differentiated and the
quadratic Christoffel corrections survive. This is the genuine missing chart formula, the second-order
companion of the `1`-jet basepoint reduction `covApply_linearExtensionTangent_basepoint_eq`.

**Posited** (body `sorry`): the chart computation of the iterated covariant derivative of the
coordinate-constant field — a second-order chart-coordinate expansion. Consumers transitively depend on
its `sorryAx`. -/
theorem covApply_covApply_linearExtensionTangent_basepoint_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) (w : TangentSpace I x₀)
    (v : TangentSpace I x₀) :
    (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ v)
          (linearExtensionTangent (I := I) x₀ w)) x₀
        (linearExtensionTangent (I := I) x₀ v x₀) =
      trivFromE (I := I) x₀ x₀
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) k *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) i *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ w)) j) •
              ((fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) ((chartModelBasis E) k) • (chartModelBasis E) m)) +
      trivFromE (I := I) x₀ x₀
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) i *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) k *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ w)) j *
                chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
                chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀)) •
              (chartModelBasis E) m) := by
  classical
  set V : E := tangentCoord (I := I) x₀ v with hV_def
  set W : E := tangentCoord (I := I) x₀ w with hW_def
  set S : Π b : M, TangentSpace I b :=
    Connection.covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ v)
      (linearExtensionTangent (I := I) x₀ w) with hS_def
  have hLv1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (linearExtensionTangent (I := I) x₀ w)) := by
    have h : ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    rw [h]; exact linearExtensionTangent_smooth (I := I) x₀ w
  have hS_at : MDiffAt (T% S) x₀ :=
    Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g)
      (linearExtensionTangent_smooth (I := I) x₀ v) hLv1
  have hx₀_good : x₀ ∈ chartLeviCivitaGoodSet (I := I) x₀ :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀)
  have hx₀src_ext : x₀ ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x₀
  have hev := chartE_section_repr_covApply_linExt_eventuallyEq (I := I) g x₀ v w
  have hLv_x₀ : linearExtensionTangent (I := I) x₀ v x₀ = v :=
    linearExtensionTangent_eq (I := I) x₀ v
  rw [hLv_x₀]
  rw [LeviCivita_chart_apply (I := I) g x₀ hx₀_good hS_at v]
  rw [chartLeviCivita_apply (I := I) g x₀ S hx₀_good v]
  rw [trivToE_self_apply (I := I) x₀ v]

  rw [hev.fderiv_eq, fderiv_christoffelVWSum_apply (I := I) g x₀ V W v]
  have hSx₀_repr :
      chartE_section_repr (I := I) x₀ S x₀ =
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
              (chartModelBasis E) m := by
    have h0 := hev.self_of_nhds
    simp only [Function.comp_apply] at h0
    rw [(extChartAt I x₀).left_inv hx₀src_ext] at h0
    exact h0
  rw [hSx₀_repr]
  rw [christoffelCorrection_apply (I := I) g x₀ x₀
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
            chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
          (chartModelBasis E) m) v]
  rw [trivToE_self_apply (I := I) x₀ v]
  rw [map_add]

  have hv_basis : (v : E) =
      ∑ k : Fin (Module.finrank ℝ E), ((chartModelBasis E).repr V) k • (chartModelBasis E) k := by
    have : (V : E) = v := by rw [hV_def]; exact trivToE_self_apply (I := I) x₀ v
    rw [← this]
    exact ((chartModelBasis E).sum_repr V).symm
  congr 1
  · -- ∂Γ term: expand the direction-`v` fderiv into the basis sum and reorder `(m,k) → (k,m)`.
    have hLHS1 :
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) v) • (chartModelBasis E) m) =
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr V) k * ((chartModelBasis E).repr V) i *
                  ((chartModelBasis E).repr W) j) •
                ((fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                    (extChartAt I x₀ x₀)) ((chartModelBasis E) k) • (chartModelBasis E) m) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      have hfd : ∀ m : Fin (Module.finrank ℝ E),
          (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
              (extChartAt I x₀ x₀)) v =
            ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr V) k *
                (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) ((chartModelBasis E) k) := by
        intro m
        conv_lhs => rw [hv_basis]
        rw [map_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_smul, smul_eq_mul]
      rw [show (∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) v) • (chartModelBasis E) m) =
          ∑ m : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                (((chartModelBasis E).repr V) k *
                  (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                    (extChartAt I x₀ x₀)) ((chartModelBasis E) k))) • (chartModelBasis E) m from by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hfd m, Finset.mul_sum, Finset.sum_smul]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m _ => ?_))
      rw [smul_smul]
      congr 1
      ring
    rw [hLHS1]
  · -- Γ·Γ term: collect both sides by the output basis index and match the scalar coefficients.
    refine congrArg (trivFromE (I := I) x₀ x₀) ?_
    have hVeqv : (V : E) = v := by rw [hV_def]; exact trivToE_self_apply (I := I) x₀ v

    rw [sum3_collect_basis_inner (fun p q r =>
      ((chartModelBasis E).repr v) p *
        ((chartModelBasis E).repr
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                  chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
                (chartModelBasis E) m)) q *
        chartChristoffel (I := I) g x₀ p q r (extChartAt I x₀ x₀))]

    rw [sum5_collect_basis_inner (fun i j k l m =>
      ((chartModelBasis E).repr V) i * ((chartModelBasis E).repr V) k *
        ((chartModelBasis E).repr W) j *
        chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
        chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀))]

    refine Finset.sum_congr rfl (fun z _ => ?_)
    refine congrArg (fun t : ℝ => t • (chartModelBasis E) z) ?_

    have hLHScoeff :
        (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) p *
            ((chartModelBasis E).repr
              (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                ∑ m : Fin (Module.finrank ℝ E),
                  (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                      chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
                    (chartModelBasis E) m)) q *
            chartChristoffel (I := I) g x₀ p q z (extChartAt I x₀ x₀)) =
          ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr V) p * ((chartModelBasis E).repr V) i *
                ((chartModelBasis E).repr W) j *
                chartChristoffel (I := I) g x₀ i j q (extChartAt I x₀ x₀) *
                chartChristoffel (I := I) g x₀ p q z (extChartAt I x₀ x₀) := by
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      rw [chartModelBasis_repr_christoffelVWSum (I := I) g x₀ V W (extChartAt I x₀ x₀) q, ← hVeqv]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    rw [hLHScoeff]

    rw [sum4_scalar_swap_pairs (fun p q i j =>
      ((chartModelBasis E).repr V) p * ((chartModelBasis E).repr V) i *
        ((chartModelBasis E).repr W) j *
        chartChristoffel (I := I) g x₀ i j q (extChartAt I x₀ x₀) *
        chartChristoffel (I := I) g x₀ p q z (extChartAt I x₀ x₀))]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
    ring

/-- The **polynomial chart-coordinate tangent extension** attached to `(x₀, P)`: at `b` it
re-injects the model-space value `P (extChartAt I x₀ b − extChartAt I x₀ x₀)` of a chart-coordinate
map `P : E → E` (read in the *centred* chart coordinate `extChartAt I x₀ b − extChartAt I x₀ x₀`)
into the fibre `T_b M` through the tangent trivialization centred at `x₀`, then cuts off by the
centred bump `linExtBump x₀`.

For the constant map `P = fun _ => c` this is (on the bump-`1` set) the chart-parallel/coordinate
extension `coordExtensionTangent`; the point of the polynomial version is that a non-constant `P`
has a non-vanishing chart derivative, which the chart Levi-Civita formula reads off as the
covariant `1`-jet (`fderiv P` at the centre) and the iterated covariant `2`-jet (`fderiv² P` at the
centre), allowing the metric Christoffel `1`-jet correction and the `∂Γ + Γ·Γ` `2`-jet correction of
`linearExtensionTangent x₀ v` to be cancelled by a degree-`≤ 2` polynomial `P`. -/
def polyCoordExtensionTangent (x₀ : M) (P : E → E) :
    Π b : M, TangentSpace I b :=
  fun b => (linExtBump (I := I) x₀ : M → ℝ) b •
    trivFromE (I := I) x₀ b (P (extChartAt I x₀ b - extChartAt I x₀ x₀))

@[simp] lemma polyCoordExtensionTangent_apply (x₀ : M) (P : E → E) (b : M) :
    polyCoordExtensionTangent (I := I) x₀ P b =
      (linExtBump (I := I) x₀ : M → ℝ) b •
        trivFromE (I := I) x₀ b (P (extChartAt I x₀ b - extChartAt I x₀ x₀)) := rfl

/-- At the basepoint, the polynomial chart-coordinate extension evaluates to
`P 0` re-injected through the (identity) basepoint trivialization, i.e. literally `P 0`. -/
lemma polyCoordExtensionTangent_basepoint (x₀ : M) (P : E → E) :
    polyCoordExtensionTangent (I := I) x₀ P x₀ = P 0 := by
  classical
  rw [polyCoordExtensionTangent_apply, linExtBump_eq_one, one_smul, sub_self,
    trivFromE_self_apply]

/-- The **chart-trivialised representation** of the polynomial chart-coordinate extension, pulled
back through `(extChartAt I x₀).symm`, is eventually equal near `extChartAt I x₀ x₀` to the centred
polynomial `y ↦ P (y − extChartAt I x₀ x₀)`: near `x₀` the bump is `1` and the trivialization
round-trip `trivToE ∘ trivFromE = id` collapses the re-injection. -/
lemma chartE_section_repr_polyCoordExtensionTangent_eventuallyEq
    (x₀ : M) (P : E → E) :
    (chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P))
        ∘ (extChartAt I x₀).symm
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
        (fun y : E => P (y - extChartAt I x₀ x₀)) := by
  classical
  set φ := extChartAt I x₀ with hφ_def
  have hbump1 : {b : M | (linExtBump (I := I) x₀ : M → ℝ) b = 1} ∈ 𝓝 x₀ :=
    (linExtBump (I := I) x₀).eventuallyEq_one
  have hbase : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ := by
    rw [show (trivializationAt E (TangentSpace I) x₀).baseSet = (chartAt H x₀).source from rfl]
    exact (chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)
  have hmem : {b : M | chartE_section_repr (I := I) x₀
        (polyCoordExtensionTangent (I := I) x₀ P) b = P (φ b - φ x₀)} ∈ 𝓝 x₀ := by
    filter_upwards [hbump1, hbase] with b hb1 hbbase
    have hWb : polyCoordExtensionTangent (I := I) x₀ P b =
        trivFromE (I := I) x₀ b (P (φ b - φ x₀)) := by
      rw [polyCoordExtensionTangent_apply, hb1, one_smul]
    show chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) b = P (φ b - φ x₀)
    rw [chartE_section_repr_eq_trivToE, hWb]
    exact trivToE_trivFromE (I := I) x₀ hbbase _
  have hsymm_cont : ContinuousAt φ.symm (φ x₀) := continuousAt_extChartAt_symm x₀
  have hsymm_pt : φ.symm (φ x₀) = x₀ := extChartAt_to_inv x₀
  have hpre : φ.symm ⁻¹' {b : M | chartE_section_repr (I := I) x₀
        (polyCoordExtensionTangent (I := I) x₀ P) b = P (φ b - φ x₀)} ∈ 𝓝 (φ x₀) := by
    apply hsymm_cont.preimage_mem_nhds
    rw [hsymm_pt]; exact hmem
  have htgt : φ.target ∈ 𝓝 (φ x₀) := by
    have hx₀src : x₀ ∈ φ.source := by
      rw [hφ_def, extChartAt_source]; exact mem_chart_source H x₀
    have hx₀int : φ x₀ ∈ interior (φ.target : Set E) :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) x₀ (φ.map_source hx₀src)
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hx₀int) interior_subset
  filter_upwards [hpre, htgt] with y hy hy_tgt
  have hy' : chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) (φ.symm y)
      = P (φ (φ.symm y) - φ x₀) := hy
  show chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) (φ.symm y)
      = P (y - φ x₀)
  rw [hy', φ.right_inv hy_tgt]

/-- On the trivialization base set at `x₀`, the chart-trivialised representation of the polynomial
chart-coordinate extension equals the centred polynomial value `P (extChartAt I x₀ b − extChartAt I x₀ x₀)`
times the bump. -/
lemma chartE_section_repr_polyCoordExtensionTangent_eq
    (x₀ : M) (P : E → E) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) b =
      (linExtBump (I := I) x₀ : M → ℝ) b •
        P (extChartAt I x₀ b - extChartAt I x₀ x₀) := by
  classical
  rw [chartE_section_repr_eq_trivToE, polyCoordExtensionTangent_apply, map_smul]
  rw [trivToE_trivFromE (I := I) x₀ hb]

/-- **Smoothness of the polynomial chart-coordinate extension.** For a `C^∞` chart-coordinate map
`P : E → E`, the section `polyCoordExtensionTangent x₀ P` is a `C^∞` tangent-bundle section: it is
the bump-cut-off of the field `b ↦ trivFromE x₀ b (P (φ b − φ x₀))`, which is smooth on the
trivialization base set (composite of the smooth chart `φ`, the smooth `P`, and the smooth inverse
trivialization), exactly as for the constant-coordinate `linearExtensionTangent`. -/
theorem polyCoordExtensionTangent_smooth (x₀ : M) {P : E → E}
    (hP : ContDiff ℝ ∞ P) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (polyCoordExtensionTangent (I := I) x₀ P)) := by
  classical
  set u : Set M := (chartAt H x₀).source with hu_def
  set ψ : M → ℝ := (linExtBump (I := I) x₀ : M → ℝ) with hψ_def
  have hψ_smooth : ContMDiffOn I 𝓘(ℝ) ∞ ψ u :=
    (linExtBump (I := I) x₀).contMDiff.contMDiffOn
  have hu_open : IsOpen u := (chartAt H x₀).open_source
  have hψ_tsupport : tsupport ψ ⊆ u :=
    (linExtBump (I := I) x₀).tsupport_subset_chartAt_source

  set F : Π b : M, TangentSpace I b :=
    fun b => trivFromE (I := I) x₀ b (P (extChartAt I x₀ b - extChartAt I x₀ x₀)) with hF_def
  have hbaseEq : u = (trivializationAt E (TangentSpace I) x₀).baseSet := rfl

  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I x₀) (chartAt H x₀).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := x₀)
  have hPval : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => P (extChartAt I x₀ b - extChartAt I x₀ x₀)) u := by
    have hP_cm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ P := hP.contMDiff
    have hsub : ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun b : M => extChartAt I x₀ b - extChartAt I x₀ x₀) u :=
      hφ_cm.sub contMDiffOn_const
    exact hP_cm.comp_contMDiffOn hsub
  have hF_smooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% F) u := by
    rw [hbaseEq]
    have hiff :=
      ((trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
        (IB := I) (n := ∞) (s := fun b => F b)
    refine hiff.mpr ?_
    rw [← hbaseEq]
    refine hPval.congr ?_
    intro b hb
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hbaseEq]; exact hb
    change (trivializationAt E (TangentSpace I) x₀ ⟨b, F b⟩).2 =
      P (extChartAt I x₀ b - extChartAt I x₀ x₀)
    have happ :
        (trivializationAt E (TangentSpace I) x₀
          ⟨b, (trivializationAt E (TangentSpace I) x₀).symm b
            (P (extChartAt I x₀ b - extChartAt I x₀ x₀))⟩).2
          = P (extChartAt I x₀ b - extChartAt I x₀ x₀) := by
      have h := (trivializationAt E (TangentSpace I) x₀).apply_mk_symm hb_base
        (P (extChartAt I x₀ b - extChartAt I x₀ x₀))
      simpa using congrArg Prod.snd h
    simpa [hF_def, trivFromE, Trivialization.symmL_apply] using happ
  have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
    (V := TangentSpace I) hψ_smooth hu_open hψ_tsupport hF_smooth
  have h_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        (polyCoordExtensionTangent (I := I) x₀ P b)) =
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        ((ψ • fun b' : M => F b') b)) := by
    funext b
    change TotalSpace.mk' E b (polyCoordExtensionTangent (I := I) x₀ P b) =
      TotalSpace.mk' E b ((ψ b) • F b)
    rw [polyCoordExtensionTangent_apply]
  rw [h_eq]
  exact h

/-- **The basepoint covariant `1`-jet of the polynomial chart-coordinate extension.** For a `C^∞`
chart map `P`, the covariant derivative of `polyCoordExtensionTangent x₀ P` along `u`, evaluated at
`x₀`, is the basepoint chart formula: the Fréchet derivative at the chart centre of the centred
polynomial `y ↦ P (y − φ x₀)` (read as a model-space linear map), plus the metric Christoffel
correction reading the basepoint value `P 0`. -/
theorem covApply_polyCoordExtensionTangent_basepoint_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) {P : E → E} (hP : ContDiff ℝ ∞ P)
    (u : TangentSpace I x₀) :
    (LeviCivita (I := I) g).toFun (polyCoordExtensionTangent (I := I) x₀ P) x₀ u =
      trivFromE (I := I) x₀ x₀
        (fderiv ℝ (fun y : E => P (y - extChartAt I x₀ x₀)) (extChartAt I x₀ x₀) u +
          christoffelCorrection (I := I) g x₀ x₀ (P 0) u) := by
  classical
  have hself : x₀ ∈ chartLeviCivitaGoodSet (I := I) x₀ :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀)
  have hMDiff : MDiffAt (T% (polyCoordExtensionTangent (I := I) x₀ P)) x₀ :=
    (polyCoordExtensionTangent_smooth (I := I) x₀ hP).mdifferentiableAt (by norm_num)
  rw [LeviCivita_chart_apply (I := I) g x₀ hself hMDiff u]
  rw [chartLeviCivita_apply (I := I) g x₀ (polyCoordExtensionTangent (I := I) x₀ P) hself u]

  have hfd :
      fderiv ℝ (chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P)
          ∘ (extChartAt I x₀).symm) (extChartAt I x₀ x₀) =
        fderiv ℝ (fun y : E => P (y - extChartAt I x₀ x₀)) (extChartAt I x₀ x₀) :=
    (chartE_section_repr_polyCoordExtensionTangent_eventuallyEq (I := I) x₀ P).fderiv_eq
  rw [hfd, trivToE_self_apply (I := I) x₀ u]

  have hrepr0 :
      chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) x₀ = P 0 := by
    rw [chartE_section_repr_eq_trivToE, polyCoordExtensionTangent_basepoint,
      trivToE_self_apply]
  rw [hrepr0]

/-- **First chart layer (pointwise) for the polynomial chart-coordinate extension.** At a good-set
point `b` of the chart at `x₀` where the bump is eventually `1` near `b`, the covariant-derivative
value `(LeviCivita g) (polyCoordExtensionTangent x₀ P) b (linExt x₀ u b)` equals
`trivFromE x₀ b (fderiv P (φ b − c) (tangentCoord x₀ u) + christoffelCorrection g x₀ b (P (φ b − c)) (linExt x₀ u b))`,
with `c := extChartAt I x₀ x₀`. (Unlike the constant-coordinate `linExt`, the chart derivative does
not vanish: it is `fderiv P` at the centred chart point, read on the constant model coordinate
`tangentCoord x₀ u` of the constant reading vector.) -/
private lemma LeviCivita_covApply_polyCoordExt_firstLayer_pointwise
    (g : SmoothRiemannianMetric I M) (x₀ : M) {P : E → E} (hP : ContDiff ℝ ∞ P)
    (u : TangentSpace I x₀)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) x₀)
    (hb1 : (linExtBump (I := I) x₀ : M → ℝ) =ᶠ[𝓝 b] (fun _ => (1 : ℝ))) :
    (LeviCivita (I := I) g).toFun (polyCoordExtensionTangent (I := I) x₀ P) b
        (linearExtensionTangent (I := I) x₀ u b) =
      trivFromE (I := I) x₀ b
        (fderiv ℝ P (extChartAt I x₀ b - extChartAt I x₀ x₀) (tangentCoord (I := I) x₀ u) +
          christoffelCorrection (I := I) g x₀ b
            (P (extChartAt I x₀ b - extChartAt I x₀ x₀))
            (linearExtensionTangent (I := I) x₀ u b)) := by
  classical
  set φ := extChartAt I x₀ with hφ_def
  set c := extChartAt I x₀ x₀ with hc_def
  have hbbase : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 b :=
    (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) hb)
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hb_src : b ∈ φ.source := chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hCat : MDiffAt (T% (polyCoordExtensionTangent (I := I) x₀ P)) b :=
    (polyCoordExtensionTangent_smooth (I := I) x₀ hP).mdifferentiableAt (by norm_num)
  rw [LeviCivita_chart_apply (I := I) g x₀ hb hCat (linearExtensionTangent (I := I) x₀ u b)]
  rw [chartLeviCivita_apply (I := I) g x₀ (polyCoordExtensionTangent (I := I) x₀ P) hb
    (linearExtensionTangent (I := I) x₀ u b)]

  have hev :
      (chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) ∘ φ.symm)
        =ᶠ[𝓝 (φ b)] (fun y : E => P (y - c)) := by
    have hsymm_cont : ContinuousAt φ.symm (φ b) := continuousAt_extChartAt_symm' hb_src
    have hsymm_pt : φ.symm (φ b) = b := φ.left_inv hb_src
    have hmem : {c' : M | chartE_section_repr (I := I) x₀
          (polyCoordExtensionTangent (I := I) x₀ P) c' = P (φ c' - c)} ∈ 𝓝 b := by
      filter_upwards [hb1, hbbase] with d hd1 hdbase
      have hWd : polyCoordExtensionTangent (I := I) x₀ P d =
          trivFromE (I := I) x₀ d (P (φ d - c)) := by
        rw [polyCoordExtensionTangent_apply, hd1, one_smul]
      show chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) d = P (φ d - c)
      rw [chartE_section_repr_eq_trivToE, hWd]
      exact trivToE_trivFromE (I := I) x₀ hdbase _
    have htgt : φ.target ∈ 𝓝 (φ b) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds
        (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb)) interior_subset
    filter_upwards [hsymm_cont.preimage_mem_nhds (by rw [hsymm_pt]; exact hmem), htgt]
      with y hy hy_tgt
    have hy' : chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) (φ.symm y)
        = P (φ (φ.symm y) - c) := hy
    show (chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) ∘ φ.symm) y
        = P (y - c)
    simp only [Function.comp_apply]
    rw [hy', φ.right_inv hy_tgt]

  have hfd :
      fderiv ℝ (chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) ∘ φ.symm)
        (φ b) = fderiv ℝ P (φ b - c) := by
    rw [hev.fderiv_eq]
    have hshift : HasFDerivAt (fun y : E => y - c) (ContinuousLinearMap.id ℝ E) (φ b) :=
      (hasFDerivAt_id (φ b)).sub_const c
    have hPd : HasFDerivAt P (fderiv ℝ P (φ b - c)) (φ b - c) :=
      (hP.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt (fun y : E => P (y - c))
        ((fderiv ℝ P (φ b - c)).comp (ContinuousLinearMap.id ℝ E)) (φ b) :=
      hPd.comp (φ b) hshift
    rw [hcomp.fderiv, ContinuousLinearMap.comp_id]
  rw [hfd]

  have hread : trivToE (I := I) x₀ b (linearExtensionTangent (I := I) x₀ u b) =
      tangentCoord (I := I) x₀ u := by
    have hub : linearExtensionTangent (I := I) x₀ u b = coordExtensionTangent (I := I) x₀ u b := by
      rw [linearExtensionTangent_apply, hb1.self_of_nhds, one_smul]
    rw [hub]
    have := chartE_section_repr_coordExtensionTangent_eq (I := I) x₀ u hb_base
    rwa [chartE_section_repr_eq_trivToE] at this
  rw [hread]

  have hreprb : chartE_section_repr (I := I) x₀ (polyCoordExtensionTangent (I := I) x₀ P) b =
      P (φ b - c) := by
    have hWb : polyCoordExtensionTangent (I := I) x₀ P b =
        trivFromE (I := I) x₀ b (P (φ b - c)) := by
      rw [polyCoordExtensionTangent_apply, hb1.self_of_nhds, one_smul]
    rw [chartE_section_repr_eq_trivToE, hWb]
    exact trivToE_trivFromE (I := I) x₀ hb_base _
  rw [hreprb]

/-- **Inner-section chart representation for the polynomial extension.** The chart-trivialised
representation of the intermediate section `S := covApply (LeviCivita g) (linExt x₀ u) C`,
`C := polyCoordExtensionTangent x₀ P`, pulled through `(extChartAt I x₀).symm`, is eventually equal
near `φ x₀` to `y ↦ fderiv P (y − c) U + ∑_{i,j,m} Uᵢ (P (y−c))ⱼ Γᵐᵢⱼ(y) eₘ`, with `U := tangentCoord x₀ u`,
`c := φ x₀`, `Γ = chartChristoffel g x₀`. (The non-vanishing `fderiv P` term is the new feature versus
the constant-coordinate `linExt`.) -/
private lemma chartE_section_repr_covApply_polyCoordExt_eventuallyEq
    (g : SmoothRiemannianMetric I M) (x₀ : M) {P : E → E} (hP : ContDiff ℝ ∞ P)
    (u : TangentSpace I x₀) :
    (chartE_section_repr (I := I) x₀
        (Connection.covApply (LeviCivita (I := I) g)
          (linearExtensionTangent (I := I) x₀ u)
          (polyCoordExtensionTangent (I := I) x₀ P)) ∘ (extChartAt I x₀).symm)
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
        (fun y : E =>
          fderiv ℝ P (y - extChartAt I x₀ x₀) (tangentCoord (I := I) x₀ u) +
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) i *
                  ((chartModelBasis E).repr (P (y - extChartAt I x₀ x₀))) j *
                  chartChristoffel (I := I) g x₀ i j m y) •
                (chartModelBasis E) m) := by
  classical
  set φ := extChartAt I x₀ with hφ_def
  set c := extChartAt I x₀ x₀ with hc_def
  have hbump1 : {b : M | (linExtBump (I := I) x₀ : M → ℝ) b = 1} ∈ 𝓝 x₀ :=
    (linExtBump (I := I) x₀).eventuallyEq_one
  obtain ⟨W₀, hW₀_sub, hW₀_open, hx₀W₀⟩ := mem_nhds_iff.mp hbump1
  have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) x₀) :=
    chartLeviCivitaGoodSet_isOpen (I := I) x₀
  set Vset : Set E :=
    φ.target ∩ φ.symm ⁻¹' (chartLeviCivitaGoodSet (I := I) x₀ ∩ W₀) with hVset_def
  have hcont_symm : ContinuousOn φ.symm φ.target := continuousOn_extChartAt_symm x₀
  have hVset_open : IsOpen Vset :=
    hcont_symm.isOpen_inter_preimage (isOpen_extChartAt_target (I := I) x₀)
      (hgood_open.inter hW₀_open)
  have hx₀_good : x₀ ∈ chartLeviCivitaGoodSet (I := I) x₀ :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀)
  have hx₀src_ext : x₀ ∈ φ.source := by
    rw [hφ_def, extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x₀
  have hx₀tgt : φ x₀ ∈ φ.target := φ.map_source hx₀src_ext
  have hφx₀V : φ x₀ ∈ Vset := by
    refine ⟨hx₀tgt, ?_⟩
    rw [Set.mem_preimage, φ.left_inv hx₀src_ext]
    exact ⟨hx₀_good, hx₀W₀⟩
  filter_upwards [hVset_open.mem_nhds hφx₀V] with y hy
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  rw [Set.mem_preimage] at hy_pre
  obtain ⟨hy_good, hy_W₀⟩ := hy_pre
  set b : M := φ.symm y with hb_def
  have hb1 : (linExtBump (I := I) x₀ : M → ℝ) =ᶠ[𝓝 b] (fun _ => (1 : ℝ)) := by
    filter_upwards [hW₀_open.mem_nhds hy_W₀] with d hd using hW₀_sub hd
  have hφb : φ b = y := by rw [hb_def, φ.right_inv hy_tgt]
  simp only [Function.comp_apply, chartE_section_repr_eq_trivToE, Connection.covApply_apply]
  rw [show (LeviCivita (I := I) g).toFun (polyCoordExtensionTangent (I := I) x₀ P) b
        (linearExtensionTangent (I := I) x₀ u b) =
      trivFromE (I := I) x₀ b
        (fderiv ℝ P (φ b - c) (tangentCoord (I := I) x₀ u) +
          christoffelCorrection (I := I) g x₀ b (P (φ b - c))
            (linearExtensionTangent (I := I) x₀ u b)) from
    LeviCivita_covApply_polyCoordExt_firstLayer_pointwise (I := I) g x₀ hP u hy_good hb1]
  have hbbase : b ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hy_good
  rw [trivToE_trivFromE (I := I) x₀ hbbase]
  rw [christoffelCorrection_apply (I := I) g x₀ b (P (φ b - c))
    (linearExtensionTangent (I := I) x₀ u b)]

  have hreadrepr :
      trivToE (I := I) x₀ b (linearExtensionTangent (I := I) x₀ u b) =
        tangentCoord (I := I) x₀ u := by
    have hub : linearExtensionTangent (I := I) x₀ u b = coordExtensionTangent (I := I) x₀ u b := by
      rw [linearExtensionTangent_apply, hb1.self_of_nhds, one_smul]
    rw [hub]
    have := chartE_section_repr_coordExtensionTangent_eq (I := I) x₀ u hbbase
    rwa [chartE_section_repr_eq_trivToE] at this
  rw [hreadrepr, hφb]

/-- The explicit `E → E` inner-section chart-representation function `Φ` of
`covApply (LeviCivita g) (linExt x₀ u) (polyCoordExtensionTangent x₀ P)`: `Φ(y) := fderiv P (y − c) U
+ ∑_{i,j,m} Uᵢ (P (y−c))ⱼ Γᵐᵢⱼ(y) eₘ`, with `U := tangentCoord x₀ u`, `c := φ x₀`. -/
private def innerReprPoly (g : SmoothRiemannianMetric I M) (x₀ : M) (P : E → E)
    (u : TangentSpace I x₀) : E → E :=
  fun y : E =>
    fderiv ℝ P (y - extChartAt I x₀ x₀) (tangentCoord (I := I) x₀ u) +
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) i *
            ((chartModelBasis E).repr (P (y - extChartAt I x₀ x₀))) j *
            chartChristoffel (I := I) g x₀ i j m y) •
          (chartModelBasis E) m

/-- **The iterated covariant chart `2`-jet of the polynomial extension, reduced to a Fréchet
derivative.** For a `C^∞` chart map `P`, the iterated covariant derivative
`∇_{linExt u}(∇_{linExt u}(polyCoordExtensionTangent x₀ P))(x₀)` applied to `u` equals
`trivFromE x₀ x₀ (fderiv (innerReprPoly …) (φ x₀) u + christoffelCorrection g x₀ x₀ (innerReprPoly … (φ x₀)) u)`:
the outer chart Levi-Civita formula at `x₀` reading the inner-section chart representation. -/
private lemma covApply_covApply_polyCoordExt_basepoint_reduce
    (g : SmoothRiemannianMetric I M) (x₀ : M) {P : E → E} (hP : ContDiff ℝ ∞ P)
    (u : TangentSpace I x₀) :
    (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u)
          (polyCoordExtensionTangent (I := I) x₀ P)) x₀ u =
      trivFromE (I := I) x₀ x₀
        (fderiv ℝ (innerReprPoly (I := I) g x₀ P u) (extChartAt I x₀ x₀) u +
          christoffelCorrection (I := I) g x₀ x₀
            (innerReprPoly (I := I) g x₀ P u (extChartAt I x₀ x₀)) u) := by
  classical
  set φ := extChartAt I x₀ with hφ_def
  set c := extChartAt I x₀ x₀ with hc_def
  set S : Π b : M, TangentSpace I b :=
    Connection.covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u)
      (polyCoordExtensionTangent (I := I) x₀ P) with hS_def

  have hC1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (polyCoordExtensionTangent (I := I) x₀ P)) := by
    have h : ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    rw [h]; exact polyCoordExtensionTangent_smooth (I := I) x₀ hP
  have hS_at : MDiffAt (T% S) x₀ :=
    Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g)
      (linearExtensionTangent_smooth (I := I) x₀ u) hC1
  have hx₀_good : x₀ ∈ chartLeviCivitaGoodSet (I := I) x₀ :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀)
  have hx₀src_ext : x₀ ∈ φ.source := by
    rw [hφ_def, extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x₀
  have hev := chartE_section_repr_covApply_polyCoordExt_eventuallyEq (I := I) g x₀ hP u
  rw [LeviCivita_chart_apply (I := I) g x₀ hx₀_good hS_at u]
  rw [chartLeviCivita_apply (I := I) g x₀ S hx₀_good u]
  rw [trivToE_self_apply (I := I) x₀ u]

  have hev' : (chartE_section_repr (I := I) x₀ S ∘ φ.symm)
      =ᶠ[𝓝 c] innerReprPoly (I := I) g x₀ P u := hev
  have hfd_eq : fderiv ℝ (chartE_section_repr (I := I) x₀ S ∘ φ.symm) c =
      fderiv ℝ (innerReprPoly (I := I) g x₀ P u) c := hev'.fderiv_eq
  rw [hfd_eq]

  have hSx₀_repr : chartE_section_repr (I := I) x₀ S x₀ = innerReprPoly (I := I) g x₀ P u c := by
    have h0 := hev'.self_of_nhds
    simp only [Function.comp_apply] at h0
    rw [φ.left_inv hx₀src_ext] at h0
    exact h0
  rw [hSx₀_repr]

/-- The degree-`≤ 2` **jet-cancelling chart polynomial** attached to `(g, x₀, v)` with a chosen
symmetric quadratic coefficient `Qbil`: its degree-`1` part is the negated metric Christoffel
`1`-jet correction `−christoffelCorrection g x₀ x₀ (tangentCoord x₀ v)` (the linear coefficient that
cancels the covariant `1`-jet of `linearExtensionTangent x₀ v`), and its degree-`2` part is
`½ Qbil h h` (the quadratic coefficient chosen to cancel the covariant `2`-jet). -/
private def jetCancelPoly (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀)
    (Qbil : E →L[ℝ] E →L[ℝ] E) : E → E :=
  fun h => -(christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) h) +
    (1 / 2 : ℝ) • Qbil h h

private lemma jetCancelPoly_zero (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀)
    (Qbil : E →L[ℝ] E →L[ℝ] E) :
    jetCancelPoly (I := I) g x₀ v Qbil 0 = 0 := by
  simp [jetCancelPoly]

/-- `HasFDerivAt` of the centred quadratic `y ↦ ½ Qbil (y−c) (y−c)` at the centre `z = c`: the
derivative is the zero map (the quadratic term vanishes to second order at the centre). -/
private lemma hasFDerivAt_centredQuad_at_centre
    (Qbil : E →L[ℝ] E →L[ℝ] E) (c : E) :
    HasFDerivAt (fun y : E => (1 / 2 : ℝ) • Qbil (y - c) (y - c)) (0 : E →L[ℝ] E) c := by
  have hc : HasFDerivAt (fun y : E => Qbil (y - c)) (Qbil.comp (ContinuousLinearMap.id ℝ E)) c := by
    have hshift : HasFDerivAt (fun y : E => y - c) (ContinuousLinearMap.id ℝ E) c :=
      (hasFDerivAt_id c).sub_const c
    exact (Qbil.hasFDerivAt).comp c hshift
  have hu : HasFDerivAt (fun y : E => y - c) (ContinuousLinearMap.id ℝ E) c :=
    (hasFDerivAt_id c).sub_const c
  have happ := hc.clm_apply hu

  have hzero : (Qbil (c - c)).comp (ContinuousLinearMap.id ℝ E) +
      (Qbil.comp (ContinuousLinearMap.id ℝ E)).flip (c - c) = (0 : E →L[ℝ] E) := by
    rw [sub_self]; ext w; simp
  rw [hzero] at happ
  have := happ.const_smul (1 / 2 : ℝ)
  rw [smul_zero] at this
  exact this

private lemma jetCancelPoly_contDiff (g : SmoothRiemannianMetric I M) (x₀ : M)
    (v : TangentSpace I x₀) (Qbil : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ∞ (jetCancelPoly (I := I) g x₀ v Qbil) := by
  unfold jetCancelPoly
  have h1 : ContDiff ℝ ∞ (fun h : E =>
      -(christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) h)) :=
    ((christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) :
      E →L[ℝ] E).contDiff).neg
  have h2 : ContDiff ℝ ∞ (fun h : E => (1 / 2 : ℝ) • Qbil h h) := by
    have hb : ContDiff ℝ ∞ (fun h : E => (Qbil h) h) :=
      (Qbil.contDiff.clm_apply contDiff_id)
    exact hb.const_smul _
  exact h1.add h2

/-- The Fréchet derivative at the origin of the centred `jetCancelPoly` is its linear part: the
quadratic `½ Qbil h h` contributes nothing to the first derivative at `0`. -/
private lemma fderiv_jetCancelPoly_centred
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀)
    (Qbil : E →L[ℝ] E →L[ℝ] E) (u : E) :
    fderiv ℝ (fun y : E => jetCancelPoly (I := I) g x₀ v Qbil (y - extChartAt I x₀ x₀))
        (extChartAt I x₀ x₀) u =
      -(christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) u) := by
  classical
  set c := extChartAt I x₀ x₀ with hc
  set L : E →L[ℝ] E := christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) with hL

  have hlinFD : HasFDerivAt (fun y : E => -(L (y - c))) (-L) c := by
    have h0 : HasFDerivAt (fun y : E => L (y - c)) L c := by
      have hshift : HasFDerivAt (fun y : E => y - c) (ContinuousLinearMap.id ℝ E) c :=
        (hasFDerivAt_id c).sub_const c
      have hcomp : HasFDerivAt (fun y : E => L (y - c)) (L.comp (ContinuousLinearMap.id ℝ E)) c :=
        (L.hasFDerivAt).comp c hshift
      rwa [ContinuousLinearMap.comp_id] at hcomp
    exact h0.neg

  have hquadFD : HasFDerivAt (fun y : E => (1 / 2 : ℝ) • Qbil (y - c) (y - c)) 0 c :=
    hasFDerivAt_centredQuad_at_centre Qbil c

  have hsum : HasFDerivAt (fun y : E => jetCancelPoly (I := I) g x₀ v Qbil (y - c)) (-L) c := by
    have hadd := hlinFD.add hquadFD
    rw [add_zero] at hadd
    refine hadd.congr_of_eventuallyEq ?_
    filter_upwards with y
    show jetCancelPoly (I := I) g x₀ v Qbil (y - c) =
      -(L (y - c)) + (1 / 2 : ℝ) • Qbil (y - c) (y - c)
    rw [hL]; rfl
  rw [hsum.fderiv]
  rw [ContinuousLinearMap.neg_apply, hL]
  rfl

/-- The basepoint coordinate `tangentCoord x₀ u = u` (the basepoint trivialization is the
identity on `E`). -/
private lemma tangentCoord_self (x₀ : M) (u : TangentSpace I x₀) :
    tangentCoord (I := I) x₀ u = u := trivToE_self_apply (I := I) x₀ u

/-- **Bundled continuous-bilinear form of the basepoint Christoffel correction.** A continuous
bilinear map `E →L[ℝ] (TangentSpace I x₀ →L[ℝ] E)` with
`christoffelCorrectionBilin g x₀ Y v = christoffelCorrection g x₀ x₀ Y v`. -/
private def christoffelCorrectionBilin (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E →L[ℝ] (TangentSpace I x₀ →L[ℝ] E) :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    ∑ k : Fin (Module.finrank ℝ E),
      (((chartModelBasis E).coord j).toContinuousLinearMap).smulRight
        ((((chartModelBasis E).coord i).toContinuousLinearMap.comp
            (trivToE (I := I) x₀ x₀)).smulRight
          (chartChristoffel (I := I) g x₀ i j k (extChartAt I x₀ x₀) • (chartModelBasis E) k))

private lemma christoffelCorrectionBilin_apply (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Y : E) (v : TangentSpace I x₀) :
    christoffelCorrectionBilin (I := I) g x₀ Y v =
      christoffelCorrection (I := I) g x₀ x₀ Y v := by
  classical
  rw [christoffelCorrection_apply]
  unfold christoffelCorrectionBilin
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smul_smul, smul_smul]
  congr 1
  show ((chartModelBasis E).coord j) Y * ((chartModelBasis E).coord i) (trivToE (I := I) x₀ x₀ v) *
      chartChristoffel (I := I) g x₀ i j k (extChartAt I x₀ x₀) =
    ((chartModelBasis E).coord i) (trivToE (I := I) x₀ x₀ v) * ((chartModelBasis E).coord j) Y *
      chartChristoffel (I := I) g x₀ i j k (extChartAt I x₀ x₀)
  ring

/-- **Bundled continuous-bilinear `∂Γ` form** (with coefficient `V`): the continuous bilinear map
whose diagonal at `u` reproduces the `∂Γ`-summand of the linear-extension `2`-jet, with the two
coordinate-constant `u`-slots split into the bilinear arguments `(a, b)` (the chart-Christoffel
`fderiv` direction `eₖ` reading `a`, the lower index `i` reading `b`). -/
private def psiDGamma (g : SmoothRiemannianMetric I M) (x₀ : M) (V : E) :
    E →L[ℝ] E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
      (((chartModelBasis E).coord k).toContinuousLinearMap).smulRight
        ((((chartModelBasis E).coord i).toContinuousLinearMap).smulRight
          (((chartModelBasis E).repr V) j •
            trivFromE (I := I) x₀ x₀
              ((fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) ((chartModelBasis E) k) • (chartModelBasis E) m)))

private lemma psiDGamma_apply (g : SmoothRiemannianMetric I M) (x₀ : M) (V : E) (a b : E) :
    psiDGamma (I := I) g x₀ V a b =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr a) k * ((chartModelBasis E).repr b) i *
              ((chartModelBasis E).repr V) j) •
            trivFromE (I := I) x₀ x₀
              ((fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) ((chartModelBasis E) k) • (chartModelBasis E) m) := by
  classical
  unfold psiDGamma
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  conv_rhs =>
    rw [show ((chartModelBasis E).repr a) k * ((chartModelBasis E).repr b) i *
          ((chartModelBasis E).repr V) j =
        ((chartModelBasis E).repr a) k *
          (((chartModelBasis E).repr b) i * ((chartModelBasis E).repr V) j) from by ring,
      mul_smul, mul_smul]
  rfl

/-- **Bundled continuous-bilinear `Γ·Γ` form** (with coefficient `V`): the continuous bilinear map
whose diagonal at `u` reproduces the quadratic `Γ·Γ`-summand of the linear-extension `2`-jet, with
the two coordinate-constant `u`-slots split into the bilinear arguments `(a, b)`. -/
private def psiGG (g : SmoothRiemannianMetric I M) (x₀ : M) (V : E) :
    E →L[ℝ] E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).coord i).toContinuousLinearMap).smulRight
          ((((chartModelBasis E).coord k).toContinuousLinearMap).smulRight
            ((((chartModelBasis E).repr V) j *
                chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
                chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀)) •
              trivFromE (I := I) x₀ x₀ ((chartModelBasis E) m)))

private lemma psiGG_apply (g : SmoothRiemannianMetric I M) (x₀ : M) (V : E) (a b : E) :
    psiGG (I := I) g x₀ V a b =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr a) i * ((chartModelBasis E).repr b) k *
                ((chartModelBasis E).repr V) j *
                chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
                chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀)) •
              trivFromE (I := I) x₀ x₀ ((chartModelBasis E) m) := by
  classical
  unfold psiGG
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  conv_rhs =>
    rw [show ((chartModelBasis E).repr a) i * ((chartModelBasis E).repr b) k *
          ((chartModelBasis E).repr V) j *
          chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
          chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀) =
        ((chartModelBasis E).repr a) i *
          (((chartModelBasis E).repr b) k *
            (((chartModelBasis E).repr V) j *
              chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
              chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀))) from by ring,
      mul_smul, mul_smul]
  rfl

/-- The Fréchet derivative of `jetCancelPoly g x₀ v Qbil` at a general point `z`, applied to `w`:
`fderiv P z w = −christoffelCorrection g x₀ x₀ (tangentCoord x₀ v) w + ½ (Qbil z w + Qbil w z)`. -/
private lemma fderiv_jetCancelPoly_apply (g : SmoothRiemannianMetric I M) (x₀ : M)
    (v : TangentSpace I x₀) (Qbil : E →L[ℝ] E →L[ℝ] E) (z w : E) :
    fderiv ℝ (jetCancelPoly (I := I) g x₀ v Qbil) z w =
      -(christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) w) +
        (1 / 2 : ℝ) • (Qbil z w + Qbil w z) := by
  classical
  set L : E →L[ℝ] E := christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) with hL
  have hlin : HasFDerivAt (fun y : E => -(L y)) (-L) z := (L.hasFDerivAt).neg
  have hid : HasFDerivAt (fun y : E => y) (ContinuousLinearMap.id ℝ E) z := hasFDerivAt_id z
  have hc : HasFDerivAt (fun y : E => Qbil y) (Qbil.comp (ContinuousLinearMap.id ℝ E)) z :=
    (Qbil.hasFDerivAt).comp z hid
  have hquad : HasFDerivAt (fun y : E => (1 / 2 : ℝ) • Qbil y y)
      ((1 / 2 : ℝ) • ((Qbil z).comp (ContinuousLinearMap.id ℝ E) +
        (Qbil.comp (ContinuousLinearMap.id ℝ E)).flip z)) z :=
    (hc.clm_apply hid).const_smul (1 / 2 : ℝ)
  have hsum : HasFDerivAt (jetCancelPoly (I := I) g x₀ v Qbil)
      (-L + (1 / 2 : ℝ) • ((Qbil z).comp (ContinuousLinearMap.id ℝ E) +
        (Qbil.comp (ContinuousLinearMap.id ℝ E)).flip z)) z := by
    refine (hlin.add hquad).congr_of_eventuallyEq ?_
    filter_upwards with y
    show jetCancelPoly (I := I) g x₀ v Qbil y = -(L y) + (1 / 2 : ℝ) • Qbil y y
    rw [hL]; rfl
  rw [hsum.fderiv]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, hL]
  congr 1

/-- The basepoint Fréchet derivative of `jetCancelPoly g x₀ v Qbil` is its linear part:
`fderiv P 0 w = −christoffelCorrection g x₀ x₀ (tangentCoord x₀ v) w`. -/
private lemma fderiv_jetCancelPoly_zero_apply (g : SmoothRiemannianMetric I M) (x₀ : M)
    (v : TangentSpace I x₀) (Qbil : E →L[ℝ] E →L[ℝ] E) (w : E) :
    fderiv ℝ (jetCancelPoly (I := I) g x₀ v Qbil) 0 w =
      -(christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) w) := by
  rw [fderiv_jetCancelPoly_apply]; simp

/-- The derivative at the chart centre, in direction `u`, of the inner-section "`fderiv P`" head
`y ↦ fderiv P (y − c) U` for `P = jetCancelPoly g x₀ v Qbil`: `½ (Qbil u U + Qbil U u)` (the
constant `−christoffelCorrection` head drops, the quadratic head's derivative is the symmetrised
`Qbil`). -/
private lemma fderiv_jetCancel_Aterm (g : SmoothRiemannianMetric I M) (x₀ : M)
    (v : TangentSpace I x₀) (Qbil : E →L[ℝ] E →L[ℝ] E) (U u : E) :
    fderiv ℝ (fun y : E => fderiv ℝ (jetCancelPoly (I := I) g x₀ v Qbil)
        (y - extChartAt I x₀ x₀) U) (extChartAt I x₀ x₀) u =
      (1 / 2 : ℝ) • (Qbil u U + Qbil U u) := by
  classical
  set c := extChartAt I x₀ x₀ with hc
  have hfun : (fun y : E => fderiv ℝ (jetCancelPoly (I := I) g x₀ v Qbil) (y - c) U) =
      (fun y : E => -(christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) U) +
        (1 / 2 : ℝ) • (Qbil (y - c) U + Qbil U (y - c))) := by
    funext y; rw [fderiv_jetCancelPoly_apply]
  rw [hfun]
  have hA1 : HasFDerivAt (fun y : E => Qbil (y - c) U) (Qbil.flip U) c := by
    have hgen : ∀ z : E, HasFDerivAt (fun y : E => Qbil (y - c) U)
        ((Qbil.flip U).comp (ContinuousLinearMap.id ℝ E)) z := by
      intro z
      have hshiftz : HasFDerivAt (fun y : E => y - c) (ContinuousLinearMap.id ℝ E) z :=
        (hasFDerivAt_id z).sub_const c
      have hq : HasFDerivAt (fun w : E => Qbil w U) (Qbil.flip U) (z - c) := by
        refine ((Qbil.flip U).hasFDerivAt (x := z - c)).congr_of_eventuallyEq ?_
        filter_upwards with w; rw [ContinuousLinearMap.flip_apply]
      exact hq.comp z hshiftz
    have h := hgen c; rwa [ContinuousLinearMap.comp_id] at h
  have hA2 : HasFDerivAt (fun y : E => Qbil U (y - c)) (Qbil U) c := by
    have hgen : ∀ z : E, HasFDerivAt (fun y : E => Qbil U (y - c))
        ((Qbil U).comp (ContinuousLinearMap.id ℝ E)) z := by
      intro z
      have hshiftz : HasFDerivAt (fun y : E => y - c) (ContinuousLinearMap.id ℝ E) z :=
        (hasFDerivAt_id z).sub_const c
      exact ((Qbil U).hasFDerivAt).comp z hshiftz
    have h := hgen c; rwa [ContinuousLinearMap.comp_id] at h
  have hAfull : HasFDerivAt
      (fun y : E => -(christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) U) +
        (1 / 2 : ℝ) • (Qbil (y - c) U + Qbil U (y - c)))
      ((1 / 2 : ℝ) • (Qbil.flip U + Qbil U)) c := by
    have hconst : HasFDerivAt
        (fun _ : E => -(christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) U))
        (0 : E →L[ℝ] E) c := hasFDerivAt_const _ c
    have := hconst.add ((hA1.add hA2).const_smul (1 / 2 : ℝ))
    rwa [zero_add] at this
  rw [hAfull.fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply]

/-- `chartChristoffel` is differentiable at the chart basepoint (it is `C^∞` on the interior of
the chart target). -/
private lemma chartChristoffel_differentiableAt_basepoint'
    (g : SmoothRiemannianMetric I M) (x₀ : M) (i j m : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
      (extChartAt I x₀ x₀) :=
  chartChristoffel_differentiableAt_basepoint (I := I) g x₀ i j m

/-- A single `(i,j,m)`-summand of the inner-section Christoffel sum is differentiable at the
chart basepoint. -/
private lemma diffAt_jetCancel_Bsummand (g : SmoothRiemannianMetric I M) (x₀ : M)
    {P : E → E} (hP : ContDiff ℝ ∞ P) (U : E) (i j m : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (fun y : E =>
        (((chartModelBasis E).repr U) i *
            (((chartModelBasis E).repr (P (y - extChartAt I x₀ x₀))) j) *
            chartChristoffel (I := I) g x₀ i j m y) • (chartModelBasis E) m)
        (extChartAt I x₀ x₀) := by
  classical
  set c := extChartAt I x₀ x₀ with hc
  have hPshift : Differentiable ℝ (fun y : E => P (y - c)) :=
    (hP.differentiable (by norm_num)).comp ((differentiable_id).sub_const c)
  have hcoordj : DifferentiableAt ℝ (fun y : E => ((chartModelBasis E).repr (P (y - c))) j) c :=
    (((chartModelBasis E).coord j).toContinuousLinearMap.differentiable.comp
      hPshift).differentiableAt
  have hγ : DifferentiableAt ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y) c :=
    chartChristoffel_differentiableAt_basepoint (I := I) g x₀ i j m
  exact (((hcoordj.const_mul _).mul hγ)).smul_const ((chartModelBasis E) m)

/-- The Fréchet derivative at the chart basepoint, in direction `u`, of a single `(i,j,m)`-summand
`y ↦ (Uᵢ (P (y−c))ⱼ Γᵐᵢⱼ(y)) eₘ` of the inner-section Christoffel sum, for `P` with `P 0 = 0`:
the `∂Γ`-head drops (it reads `(P 0)ⱼ = 0`), leaving `Uᵢ (fderiv P 0 u)ⱼ Γᵐᵢⱼ(c) eₘ`. -/
private lemma fderiv_jetCancel_Bsummand (g : SmoothRiemannianMetric I M) (x₀ : M)
    {P : E → E} (hP : ContDiff ℝ ∞ P) (hP0 : P 0 = 0) (U u : E)
    (i j m : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun y : E =>
        (((chartModelBasis E).repr U) i *
            (((chartModelBasis E).repr (P (y - extChartAt I x₀ x₀))) j) *
            chartChristoffel (I := I) g x₀ i j m y) • (chartModelBasis E) m)
        (extChartAt I x₀ x₀) u =
      (((chartModelBasis E).repr U) i *
          (((chartModelBasis E).repr (fderiv ℝ P 0 u)) j) *
          chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) • (chartModelBasis E) m := by
  classical
  set c := extChartAt I x₀ x₀ with hc
  set cst := ((chartModelBasis E).repr U) i with hcst
  set γ := fun y : E => chartChristoffel (I := I) g x₀ i j m y with hγ
  have hγdiff : DifferentiableAt ℝ γ c :=
    chartChristoffel_differentiableAt_basepoint (I := I) g x₀ i j m
  set e := (chartModelBasis E) m with he
  have hcomp : HasFDerivAt (fun y : E => P (y - c)) (fderiv ℝ P 0) c := by
    have hcompgen : ∀ z : E, HasFDerivAt (fun y : E => P (y - c)) (fderiv ℝ P (z - c)) z := by
      intro z
      have hshiftz : HasFDerivAt (fun y : E => y - c) (ContinuousLinearMap.id ℝ E) z :=
        (hasFDerivAt_id z).sub_const c
      have hPdz : HasFDerivAt P (fderiv ℝ P (z - c)) (z - c) :=
        (hP.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have hcz : HasFDerivAt (fun y : E => P (y - c))
          ((fderiv ℝ P (z - c)).comp (ContinuousLinearMap.id ℝ E)) z := hPdz.comp z hshiftz
      rwa [ContinuousLinearMap.comp_id] at hcz
    have h := hcompgen c; rwa [sub_self] at h
  have hcoordj : HasFDerivAt (fun y : E => ((chartModelBasis E).repr (P (y - c))) j)
      ((((chartModelBasis E).coord j).toContinuousLinearMap).comp (fderiv ℝ P 0)) c :=
    ((((chartModelBasis E).coord j).toContinuousLinearMap).hasFDerivAt).comp c hcomp
  have hγ' : HasFDerivAt γ (fderiv ℝ γ c) c := hγdiff.hasFDerivAt
  have h1 : HasFDerivAt (fun y : E => cst * (((chartModelBasis E).repr (P (y - c))) j))
      ((cst : ℝ) • ((((chartModelBasis E).coord j).toContinuousLinearMap).comp (fderiv ℝ P 0))) c :=
    hcoordj.const_mul cst
  have hs := (h1.mul hγ').smul_const e
  have hFD : fderiv ℝ (fun y : E =>
        (cst * (((chartModelBasis E).repr (P (y - c))) j) * γ y) • e) c =
      ((fun y => cst * (((chartModelBasis E).repr (P (y - c))) j)) c • fderiv ℝ γ c +
        γ c • ((cst : ℝ) • ((((chartModelBasis E).coord j).toContinuousLinearMap).comp
          (fderiv ℝ P 0)))).smulRight e := hs.fderiv
  rw [hFD, ContinuousLinearMap.smulRight_apply]
  have hP0c : ((chartModelBasis E).repr (P (c - c))) j = 0 := by rw [sub_self, hP0]; simp
  have hcoordeq : (((chartModelBasis E).coord j).toContinuousLinearMap) (fderiv ℝ P 0 u) =
      ((chartModelBasis E).repr (fderiv ℝ P 0 u)) j := rfl
  have hcoeff :
      (((fun y => cst * (((chartModelBasis E).repr (P (y - c))) j)) c • fderiv ℝ γ c +
        γ c • ((cst : ℝ) • ((((chartModelBasis E).coord j).toContinuousLinearMap).comp
          (fderiv ℝ P 0)))) u) =
        cst * (((chartModelBasis E).repr (fderiv ℝ P 0 u)) j) * γ c := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, hcoordeq, hP0c, smul_eq_mul]
    ring
  rw [hcoeff]

/-- The centre value of the inner-section chart representation `innerReprPoly` for `P` with
`P 0 = 0`: the Christoffel sum reads `(P 0)ⱼ = 0` and drops, leaving the `fderiv P` head
`fderiv P 0 (tangentCoord x₀ u)`. -/
private lemma innerReprPoly_centre (g : SmoothRiemannianMetric I M) (x₀ : M)
    {P : E → E} (hP0 : P 0 = 0) (u : TangentSpace I x₀) :
    innerReprPoly (I := I) g x₀ P u (extChartAt I x₀ x₀) =
      fderiv ℝ P 0 (tangentCoord (I := I) x₀ u) := by
  classical
  unfold innerReprPoly
  rw [sub_self, hP0]
  have hzero : ∀ i j m : Fin (Module.finrank ℝ E),
      (((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) i *
          ((chartModelBasis E).repr (0 : E)) j *
          chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
        (chartModelBasis E) m = 0 := by
    intro i j m; rw [map_zero]; simp
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun m _ => hzero i j m)))]
  simp

/-- The full Fréchet derivative at the chart basepoint, in direction `u`, of the inner-section
chart representation `innerReprPoly g x₀ P u` for `P = jetCancelPoly g x₀ v Qbil`: the `A`-head
(symmetrised `Qbil`) plus the `B`-head (the `∂(P)`-once-differentiated Christoffel sum). -/
private lemma fderiv_innerReprPoly_jetCancel (g : SmoothRiemannianMetric I M) (x₀ : M)
    (v : TangentSpace I x₀) (Qbil : E →L[ℝ] E →L[ℝ] E) (u : TangentSpace I x₀) :
    fderiv ℝ (innerReprPoly (I := I) g x₀ (jetCancelPoly (I := I) g x₀ v Qbil) u)
        (extChartAt I x₀ x₀) u =
      (1 / 2 : ℝ) • (Qbil u (tangentCoord (I := I) x₀ u) + Qbil (tangentCoord (I := I) x₀ u) u) +
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) i *
                (((chartModelBasis E).repr
                  (fderiv ℝ (jetCancelPoly (I := I) g x₀ v Qbil) 0 u)) j) *
                chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
              (chartModelBasis E) m := by
  classical
  set c := extChartAt I x₀ x₀ with hc
  set U := tangentCoord (I := I) x₀ u with hU
  set P := jetCancelPoly (I := I) g x₀ v Qbil with hP
  have hPcd : ContDiff ℝ ∞ P := jetCancelPoly_contDiff (I := I) g x₀ v Qbil
  have hP0 : P 0 = 0 := jetCancelPoly_zero (I := I) g x₀ v Qbil
  set Afun : E → E := fun y : E => fderiv ℝ P (y - c) U with hAfun
  set Bfun : E → E := fun y : E =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr U) i * ((chartModelBasis E).repr (P (y - c))) j *
            chartChristoffel (I := I) g x₀ i j m y) • (chartModelBasis E) m with hBfun
  have hsplit : innerReprPoly (I := I) g x₀ P u = fun y => Afun y + Bfun y := by funext y; rfl
  rw [hsplit]
  have hAdiff : DifferentiableAt ℝ Afun c := by
    rw [hAfun]
    have hfun : (fun y : E => fderiv ℝ P (y - c) U) =
        (fun y : E => -(christoffelCorrection (I := I) g x₀ x₀ (tangentCoord (I := I) x₀ v) U) +
          (1 / 2 : ℝ) • (Qbil (y - c) U + Qbil U (y - c))) := by
      funext y; rw [hP, fderiv_jetCancelPoly_apply]
    rw [hfun]
    have hd1 : Differentiable ℝ (fun y : E => Qbil (y - c) U) :=
      (Qbil.flip U).differentiable.comp ((differentiable_id).sub_const c)
    have hd2 : Differentiable ℝ (fun y : E => Qbil U (y - c)) :=
      (Qbil U).differentiable.comp ((differentiable_id).sub_const c)
    exact (differentiableAt_const _).add (((hd1.add hd2).differentiableAt).const_smul (1 / 2 : ℝ))
  have hBdiff : DifferentiableAt ℝ Bfun c := by
    rw [hBfun]
    exact DifferentiableAt.fun_sum (fun i _ => DifferentiableAt.fun_sum (fun j _ =>
      DifferentiableAt.fun_sum (fun m _ => diffAt_jetCancel_Bsummand (I := I) g x₀ hPcd U i j m)))
  rw [fderiv_fun_add hAdiff hBdiff, ContinuousLinearMap.add_apply]
  congr 1
  · rw [hAfun, hP]
    exact fderiv_jetCancel_Aterm (I := I) g x₀ v Qbil U u
  · rw [hBfun]
    rw [fderiv_fun_sum (fun i _ => DifferentiableAt.fun_sum
      (fun j _ => DifferentiableAt.fun_sum
        (fun m _ => diffAt_jetCancel_Bsummand (I := I) g x₀ hPcd U i j m)))]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fderiv_fun_sum (fun j _ => DifferentiableAt.fun_sum
      (fun m _ => diffAt_jetCancel_Bsummand (I := I) g x₀ hPcd U i j m))]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [fderiv_fun_sum (fun m _ => diffAt_jetCancel_Bsummand (I := I) g x₀ hPcd U i j m)]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    exact fderiv_jetCancel_Bsummand (I := I) g x₀ hPcd hP0 U u i j m

/-- The diagonal of `psiDGamma g x₀ V` at `u` is the `∂Γ`-summand of the linear-extension `2`-jet
read with `tangentCoord x₀ u` in both coordinate slots (with `trivFromE x₀ x₀` distributed in). -/
private lemma psiDGamma_diag (g : SmoothRiemannianMetric I M) (x₀ : M) (V : E)
    (u : TangentSpace I x₀) :
    psiDGamma (I := I) g x₀ V u u =
      trivFromE (I := I) x₀ x₀
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) k *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) i *
                ((chartModelBasis E).repr V) j) •
              ((fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) ((chartModelBasis E) k) • (chartModelBasis E) m)) := by
  classical
  rw [psiDGamma_apply, tangentCoord_self]
  simp only [map_sum, ContinuousLinearMap.map_smul]

/-- The diagonal of `psiGG g x₀ V` at `u` is the `Γ·Γ`-summand of the linear-extension `2`-jet
read with `tangentCoord x₀ u` in both coordinate slots (with `trivFromE x₀ x₀` distributed in). -/
private lemma psiGG_diag (g : SmoothRiemannianMetric I M) (x₀ : M) (V : E)
    (u : TangentSpace I x₀) :
    psiGG (I := I) g x₀ V u u =
      trivFromE (I := I) x₀ x₀
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) i *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) k *
                ((chartModelBasis E).repr V) j *
                chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
                chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀)) •
              (chartModelBasis E) m) := by
  classical
  rw [psiGG_apply, tangentCoord_self]
  simp only [map_sum, ContinuousLinearMap.map_smul]

/-- **Existence of the cancelling quadratic coefficient (iterated chart `2`-jet content).** There is
a continuous bilinear quadratic coefficient `Qbil : E →L[ℝ] E →L[ℝ] E` such that the degree-`≤ 2`
chart-polynomial correction `polyCoordExtensionTangent x₀ (jetCancelPoly g x₀ v Qbil)` has iterated
covariant `2`-jet at `x₀`, read along each coordinate-constant reading direction
`linearExtensionTangent x₀ u`, equal to the negative of that of `linearExtensionTangent x₀ v`.

This is the genuine new chart-coordinate content of the construction. The full reduction is:
`covApply_covApply_polyCoordExt_basepoint_reduce` rewrites the `2`-jet of
`polyCoordExtensionTangent x₀ P` (any `C^∞` `P`) as
`trivFromE x₀ x₀ (fderiv (innerReprPoly … P u) (φ x₀) u + christoffelCorrection g x₀ x₀ (innerReprPoly … P u (φ x₀)) u)`.
Evaluating the inner-section chart representation `innerReprPoly` at and near `φ x₀`, for `P` with
`P 0 = 0`, gives the closed form
`trivFromE x₀ x₀ ( (fderiv (fderiv ℝ P) 0 u) (tangentCoord x₀ u) + 2 • christoffelCorrection g x₀ x₀ (fderiv P 0 (tangentCoord x₀ u)) u )`
(the chart-second-derivative `fderiv² P 0` term, plus twice the `Γ·(fderiv P 0)` term — one from the
inner Fréchet derivative, one from the outer Christoffel correction; the `∂Γ` term drops because
`P 0 = 0`). For `P = jetCancelPoly g x₀ v Qbil` the linear part fixes `fderiv P 0 = −christoffelCorrection g x₀ x₀ (tangentCoord x₀ v)`
and the quadratic part gives `(fderiv (fderiv ℝ P) 0 u) (tangentCoord x₀ u) = Qbil u u` (using
`tangentCoord x₀ u = u`). The right-hand side is the explicit `∂Γ + Γ·Γ` quadratic form from
`covApply_covApply_linearExtensionTangent_basepoint_eq`. Choosing `Qbil` to be the
(finite-coordinate, hence continuous bilinear) quadratic form `u ↦ trivToE x₀ x₀ (−RHS u) − 2 • christoffelCorrection g x₀ x₀ (fderiv P 0 u) u`
closes the cancellation. -/
private lemma exists_jetCancelQuadraticCoeff
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀) :
    ∃ Qbil : E →L[ℝ] E →L[ℝ] E,
      ∀ u : TangentSpace I x₀,
        (LeviCivita (I := I) g).toFun
            (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u)
              (polyCoordExtensionTangent (I := I) x₀ (jetCancelPoly (I := I) g x₀ v Qbil))) x₀ u =
          -((LeviCivita (I := I) g).toFun
            (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u)
              (linearExtensionTangent (I := I) x₀ v)) x₀ u) := by
  classical
  set V : E := tangentCoord (I := I) x₀ v with hV

  set Φ₁ : E →L[ℝ] E →L[ℝ] E :=
    (christoffelCorrectionBilin (I := I) g x₀).comp
      (-(christoffelCorrection (I := I) g x₀ x₀ V)) with hΦ₁
  refine ⟨-(psiDGamma (I := I) g x₀ V) - psiGG (I := I) g x₀ V - (2 : ℝ) • Φ₁, fun u => ?_⟩
  set Qbil : E →L[ℝ] E →L[ℝ] E :=
    -(psiDGamma (I := I) g x₀ V) - psiGG (I := I) g x₀ V - (2 : ℝ) • Φ₁ with hQbil
  set P : E → E := jetCancelPoly (I := I) g x₀ v Qbil with hP
  set c := extChartAt I x₀ x₀ with hc

  have hU : tangentCoord (I := I) x₀ u = u := tangentCoord_self (I := I) x₀ u

  have hfP0 : fderiv ℝ P 0 u = -(christoffelCorrection (I := I) g x₀ x₀ V u) := by
    rw [hP]; exact fderiv_jetCancelPoly_zero_apply (I := I) g x₀ v Qbil u

  rw [covApply_covApply_polyCoordExt_basepoint_reduce (I := I) g x₀
    (jetCancelPoly_contDiff (I := I) g x₀ v Qbil) u]
  rw [show jetCancelPoly (I := I) g x₀ v Qbil = P from rfl]
  rw [innerReprPoly_centre (I := I) g x₀ (jetCancelPoly_zero (I := I) g x₀ v Qbil) u]
  rw [show fderiv ℝ (innerReprPoly (I := I) g x₀ P u) c u =
        (1 / 2 : ℝ) • (Qbil u (tangentCoord (I := I) x₀ u) + Qbil (tangentCoord (I := I) x₀ u) u) +
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) i *
                  (((chartModelBasis E).repr (fderiv ℝ P 0 u)) j) *
                  chartChristoffel (I := I) g x₀ i j m c) • (chartModelBasis E) m from
      fderiv_innerReprPoly_jetCancel (I := I) g x₀ v Qbil u]

  rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr (tangentCoord (I := I) x₀ u)) i *
              (((chartModelBasis E).repr (fderiv ℝ P 0 u)) j) *
              chartChristoffel (I := I) g x₀ i j m c) • (chartModelBasis E) m) =
      christoffelCorrection (I := I) g x₀ x₀ (fderiv ℝ P 0 u) u from by
    rw [christoffelCorrection_apply]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun m _ => ?_)))
    rw [show trivToE (I := I) x₀ x₀ u = u from trivToE_self_apply (I := I) x₀ u, hU]]
  rw [hU]

  set Cterm : E := christoffelCorrection (I := I) g x₀ x₀ (fderiv ℝ P 0 u) u with hCterm
  rw [show (1 / 2 : ℝ) • (Qbil u u + Qbil u u) = Qbil u u from by
    rw [← two_smul ℝ (Qbil u u), smul_smul]; norm_num]
  rw [show Qbil u u + Cterm + Cterm = Qbil u u + (2 : ℝ) • Cterm from by
    rw [add_assoc, ← two_smul ℝ Cterm]]

  rw [map_add, map_smul,
    show trivFromE (I := I) x₀ x₀ (Qbil u u) = Qbil u u from
      trivFromE_self_apply (I := I) x₀ (Qbil u u),
    show trivFromE (I := I) x₀ x₀ Cterm = Cterm from trivFromE_self_apply (I := I) x₀ Cterm]

  rw [show (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u)
          (linearExtensionTangent (I := I) x₀ v)) x₀ u =
      (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u)
          (linearExtensionTangent (I := I) x₀ v)) x₀ (linearExtensionTangent (I := I) x₀ u x₀) from by
    rw [linearExtensionTangent_eq (I := I) x₀ u]]
  rw [covApply_covApply_linearExtensionTangent_basepoint_eq (I := I) g x₀ v u]
  rw [← hV]

  rw [hQbil]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply]
  rw [psiDGamma_diag (I := I) g x₀ V u, psiGG_diag (I := I) g x₀ V u]
  rw [show Φ₁ u u = Cterm from by
    rw [hCterm, hfP0, hΦ₁]
    change christoffelCorrectionBilin (I := I) g x₀
        ((-(christoffelCorrection (I := I) g x₀ x₀ V)) u) u =
      christoffelCorrection (I := I) g x₀ x₀ (-(christoffelCorrection (I := I) g x₀ x₀ V u)) u
    rw [christoffelCorrectionBilin_apply, ContinuousLinearMap.neg_apply]]

  module

/-- **The jet-cancelling chart-polynomial correction.** For a smooth Riemannian metric `g` on a
closed manifold, a base point `x₀`, and a fibre vector `v : TangentSpace I x₀`, there is a smooth
tangent-bundle section `C : Π b, TangentSpace I b` that

* vanishes at the basepoint: `C x₀ = 0`;
* has covariant `1`-jet at `x₀` equal to the *negative* of the covariant `1`-jet of
  `linearExtensionTangent x₀ v`: `∇_u C(x₀) = − ∇_u(linExt x₀ v)(x₀)` for every direction `u`; and
* has iterated covariant `2`-jet at `x₀`, read along every coordinate-constant linear-extension
  direction `linearExtensionTangent x₀ u`, equal to the *negative* of that of `linExt x₀ v`:
  `∇_{linExt u}(∇_{linExt u} C)(x₀)(u) = − ∇_{linExt u}(∇_{linExt u}(linExt x₀ v))(x₀)(u)`.

`C := polyCoordExtensionTangent x₀ (jetCancelPoly g x₀ v Qbil)` is the explicit degree-`≤ 2`
chart-coordinate field: its degree-`1` part `−christoffelCorrection g x₀ x₀ (tangentCoord x₀ v)`
cancels the covariant `1`-jet (the chart derivative at the centre being that linear coefficient, by
`covApply_polyCoordExtensionTangent_basepoint_eq` and `covApply_linearExtensionTangent_basepoint_eq`),
and its degree-`2` quadratic coefficient `Qbil` is chosen (by `exists_jetCancelQuadraticCoeff`, whose
iterated covariant chart `2`-jet content reduces through
`covApply_covApply_polyCoordExt_basepoint_reduce` together with the basepoint `2`-jet of the linear
extension `covApply_covApply_linearExtensionTangent_basepoint_eq`) to cancel the covariant `2`-jet. -/
theorem exists_linExtJetCancellingCorrection
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀) :
    ∃ C : Π b : M, TangentSpace I b,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% C) ∧
      C x₀ = 0 ∧
      (∀ u : TangentSpace I x₀, (LeviCivita (I := I) g).toFun C x₀ u =
        -((LeviCivita (I := I) g).toFun (linearExtensionTangent (I := I) x₀ v) x₀ u)) ∧
      (∀ u : TangentSpace I x₀,
        (LeviCivita (I := I) g).toFun
            (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u) C) x₀ u =
          -((LeviCivita (I := I) g).toFun
            (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u)
              (linearExtensionTangent (I := I) x₀ v)) x₀ u)) := by
  classical

  obtain ⟨Qbil, hQbil⟩ := exists_jetCancelQuadraticCoeff (I := I) g x₀ v
  set P : E → E := jetCancelPoly (I := I) g x₀ v Qbil with hP_def
  have hP_cd : ContDiff ℝ ∞ P := jetCancelPoly_contDiff (I := I) g x₀ v Qbil
  refine ⟨polyCoordExtensionTangent (I := I) x₀ P, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    exact polyCoordExtensionTangent_smooth (I := I) x₀ hP_cd
  · -- basepoint value `C x₀ = P 0 = 0`
    rw [polyCoordExtensionTangent_basepoint, hP_def, jetCancelPoly_zero]
  · -- covariant `1`-jet cancellation
    intro u
    rw [covApply_polyCoordExtensionTangent_basepoint_eq (I := I) g x₀ hP_cd u]
    rw [hP_def, jetCancelPoly_zero, fderiv_jetCancelPoly_centred (I := I) g x₀ v Qbil u]

    have hcc0 : christoffelCorrection (I := I) g x₀ x₀ (0 : E) u = 0 := by
      rw [christoffelCorrection_apply]
      simp
    rw [hcc0, add_zero]

    rw [covApply_linearExtensionTangent_basepoint_eq (I := I) g x₀ v u]
    rw [map_neg]
  · -- covariant `2`-jet cancellation (the chosen `Qbil` clause)
    intro u
    exact hQbil u

/-- **The covariant-`1`-jet-vanishing tangent extension whose iterated covariant derivative also
vanishes along every coordinate-constant (linear-extension) reading direction (linear-extension
`2`-jet-vanishing construction).** This is the genuine chart-polynomial correction of
`linearExtensionTangent x₀ v`: the degree-`1` chart polynomial cancelling the metric Christoffel
`1`-jet correction (`covApply_linearExtensionTangent_basepoint_eq`) and the degree-`2` chart polynomial
cancelling the `∂Γ + Γ·Γ` `2`-jet correction (`covApply_covApply_linearExtensionTangent_basepoint_eq`,
the second-order chart formula proved above), both cut off by the same bump.

It produces a smooth tangent-bundle section `W` with `W x₀ = v`, vanishing covariant `1`-jet
`∇_u W(x₀) = 0`, and — read along the coordinate-constant linear extensions `linearExtensionTangent x₀ u`
of every direction `u` — vanishing iterated covariant `2`-jet
`∇_{linExt u}(∇_{linExt u} W)(x₀) = 0`. (The general-field `2`-jet vanishing is then obtained from this
linear-extension form by the value-locality reduction
`covApply_covApply_eq_linExt_of_covApply_zero`.)

This is the genuine quadratic chart-polynomial construction: the `C₁`-linear and `C₂`-quadratic chart
corrections solving the (linear) `1`- and `2`-jet cancellation equations supplied by the two basepoint
chart formulas. It is a NEW genuine-content sub-node of `exists_twoJetVanishing_tangentExtension`, not a
rephrasing of it (its `2`-jet clause is restricted to linear-extension reading directions, where the
chart `2`-jet formula applies directly).

**Proof (glue, TRANSIT over the jet-cancelling correction child).** Take the jet-cancelling
chart-polynomial correction `C := exists_linExtJetCancellingCorrection g x₀ v` (vanishing at `x₀`, with
covariant `1`- and linear-extension-`2`-jets the negatives of those of `linExt x₀ v`), and set
`W := linExt x₀ v + C`. The basepoint value is `v + 0 = v`; the covariant `1`-jet is, by additivity of
the Levi-Civita connection, `∇_u(linExt v)(x₀) + ∇_u C(x₀) = 0`; and the iterated covariant `2`-jet along
each linear-extension direction is, by additivity of the inner gradient and the outer covariant
derivative, `∇_{linExt u}(∇_{linExt u}(linExt v))(x₀)(u) + ∇_{linExt u}(∇_{linExt u} C)(x₀)(u) = 0`.
Transits the correction child's `sorryAx`. -/
theorem exists_linExtTwoJetVanishing_tangentExtension
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀) :
    ∃ W : Π b : M, TangentSpace I b,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) ∧
      W x₀ = v ∧
      (∀ u : TangentSpace I x₀, (LeviCivita (I := I) g).toFun W x₀ u = 0) ∧
      (∀ u : TangentSpace I x₀,
        (LeviCivita (I := I) g).toFun
            (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u) W) x₀ u = 0) := by
  classical

  obtain ⟨C, hC_sm, hC_x, hC_grad, hC_hess⟩ :=
    exists_linExtJetCancellingCorrection (I := I) g x₀ v

  refine ⟨fun b => linearExtensionTangent (I := I) x₀ v b + C b, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    exact (linearExtensionTangent_smooth (I := I) x₀ v).add_section hC_sm
  · -- basepoint value: `linExt v x₀ + C x₀ = v + 0 = v`
    change linearExtensionTangent (I := I) x₀ v x₀ + C x₀ = v
    rw [linearExtensionTangent_eq (I := I) x₀ v, hC_x, add_zero]
  · -- vanishing covariant `1`-jet
    intro u
    have hLv : MDiffAt (T% (linearExtensionTangent (I := I) x₀ v)) x₀ :=
      (linearExtensionTangent_smooth (I := I) x₀ v).mdifferentiableAt (by norm_num)
    have hCd : MDiffAt (T% C) x₀ := hC_sm.mdifferentiableAt (by norm_num)
    have hadd := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.add hLv hCd
      (Set.mem_univ x₀)
    rw [LeviCivita_toFun] at hadd ⊢
    rw [show (fun b => linearExtensionTangent (I := I) x₀ v b + C b) =
        linearExtensionTangent (I := I) x₀ v + C from rfl, hadd]
    rw [ContinuousLinearMap.add_apply]
    rw [show leviCivitaStitched (I := I) g (linearExtensionTangent (I := I) x₀ v) x₀ u =
        (LeviCivita (I := I) g).toFun (linearExtensionTangent (I := I) x₀ v) x₀ u from rfl]
    rw [show leviCivitaStitched (I := I) g C x₀ u =
        (LeviCivita (I := I) g).toFun C x₀ u from rfl]
    rw [hC_grad u, add_neg_cancel]
  · intro u

    have hsplit : covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u)
          (fun b => linearExtensionTangent (I := I) x₀ v b + C b) =
        covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u)
            (linearExtensionTangent (I := I) x₀ v) +
          covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u) C := by
      funext b
      have hLvb : MDiffAt (T% (linearExtensionTangent (I := I) x₀ v)) b :=
        (linearExtensionTangent_smooth (I := I) x₀ v).mdifferentiableAt (by norm_num)
      have hCb : MDiffAt (T% C) b := hC_sm.mdifferentiableAt (by norm_num)
      have hbgood : b ∈ chartLeviCivitaGoodSet (I := I) b :=
        self_mem_chartLeviCivitaGoodSet (I := I) (α := b)
      simp only [Connection.covApply_apply, Pi.add_apply]
      rw [show (fun b => linearExtensionTangent (I := I) x₀ v b + C b) =
          linearExtensionTangent (I := I) x₀ v + C from rfl]
      rw [LeviCivita_toFun,
        leviCivitaStitched_add_on_goodSet (I := I) g b hLvb hCb hbgood]
      rfl
    rw [hsplit]

    have hLu1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
        (T% (linearExtensionTangent (I := I) x₀ v)) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
      exact linearExtensionTangent_smooth (I := I) x₀ v
    have hC1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% C) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
      exact hC_sm
    have hBLv : MDiffAt (T% (covApply (LeviCivita (I := I) g)
        (linearExtensionTangent (I := I) x₀ u) (linearExtensionTangent (I := I) x₀ v))) x₀ :=
      Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g)
        (linearExtensionTangent_smooth (I := I) x₀ u) hLu1
    have hBC : MDiffAt (T% (covApply (LeviCivita (I := I) g)
        (linearExtensionTangent (I := I) x₀ u) C)) x₀ :=
      Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g)
        (linearExtensionTangent_smooth (I := I) x₀ u) hC1
    have hadd := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.add hBLv hBC
      (Set.mem_univ x₀)
    rw [LeviCivita_toFun] at hadd ⊢
    rw [hadd, ContinuousLinearMap.add_apply]
    rw [show leviCivitaStitched (I := I) g (covApply (LeviCivita (I := I) g)
          (linearExtensionTangent (I := I) x₀ u) (linearExtensionTangent (I := I) x₀ v)) x₀ u =
        (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g)
          (linearExtensionTangent (I := I) x₀ u) (linearExtensionTangent (I := I) x₀ v)) x₀ u
        from rfl]
    rw [show leviCivitaStitched (I := I) g (covApply (LeviCivita (I := I) g)
          (linearExtensionTangent (I := I) x₀ u) C) x₀ u =
        (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g)
          (linearExtensionTangent (I := I) x₀ u) C) x₀ u from rfl]
    rw [hC_hess u, add_neg_cancel]

/-- **Value-locality of the iterated covariant derivative at a `1`-jet-vanishing section.** If the
covariant `1`-jet of `W` vanishes at `x₀` (the `(1,1)`-tensor `∇W(x₀) = 0`), then the iterated
covariant derivative `∇_Y(∇_Y W)(x₀)` depends on the smooth reading field `Y` only through its value
`Y x₀`: it equals the same expression read along the coordinate-constant linear extension
`linearExtensionTangent x₀ (Y x₀)` of that value.

This is the covariant evaluation-Leibniz / value-locality identity:
`∇_u(∇_Y W) = (∇_u ∇W)(Y) + ∇W(∇_u Y)`; at `x₀`, `∇W(x₀) = 0` kills the second (`∇_u Y`-dependent) term,
and the difference of the two readings (along `Y` and along `linExt (Y x₀)`) is `∇W(x₀)` applied to a
field vanishing at `x₀` — zero from both sides. It is a NEW genuine reusable tensor-calculus sub-node
(the tangent-bundle instance of the operator-field evaluation Leibniz
`OperatorFieldCovariantCalculus.tensorCovDerivAt_appCc_eq`), not a rephrasing of
`exists_twoJetVanishing_tangentExtension`.

The proof uses the generic Hom-bundle evaluation-Leibniz `homBundleCovariantDerivativeGen_apply`
(with the tangent Levi-Civita as both source and target connection, and the smooth operator-field
`τ b := ∇W b`): for the difference reading field `D := Y − linExt(Y x₀)` (which vanishes at `x₀`),
`∇_v(∇_D W)(x₀) = (∇_v τ)(D x₀) + τ(x₀)(∇_v D) = (∇_v τ)(0) + (∇W x₀)(∇_v D) = 0`, so the `Y`- and
`linExt(Y x₀)`-readings of the iterated covariant derivative agree. -/
theorem covApply_covApply_eq_linExt_of_covApply_zero
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {W : Π b : M, TangentSpace I b} (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hgrad : ∀ u : TangentSpace I x₀, (LeviCivita (I := I) g).toFun W x₀ u = 0)
    {Y : Π b : M, TangentSpace I b} (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y W) x₀ (Y x₀) =
      (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ (Y x₀)) W) x₀
        (Y x₀) := by
  classical
  set Z : Π b : M, TangentSpace I b := linearExtensionTangent (I := I) x₀ (Y x₀) with hZ_def
  have hZ_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z) :=
    linearExtensionTangent_smooth (I := I) x₀ (Y x₀)
  have hZ_x : Z x₀ = Y x₀ := linearExtensionTangent_eq (I := I) x₀ (Y x₀)

  set D : Π b : M, TangentSpace I b := fun b => Y b - Z b with hD_def
  have hD_x : D x₀ = 0 := by rw [hD_def]; simp [hZ_x]
  have hD_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% D) := by
    have := hY.sub_section hZ_sm
    simpa [hD_def, Pi.sub_apply] using this

  have hsplit : covApply (LeviCivita (I := I) g) Y W =
      covApply (LeviCivita (I := I) g) Z W + covApply (LeviCivita (I := I) g) D W := by
    funext b
    simp only [Connection.covApply_apply, Pi.add_apply, hD_def]
    rw [map_sub]
    abel

  have hW1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% W) := by
    have h : ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    rw [h]; exact hW
  have hBZ : MDiffAt (T% (covApply (LeviCivita (I := I) g) Z W)) x₀ :=
    Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hZ_sm hW1
  have hBD : MDiffAt (T% (covApply (LeviCivita (I := I) g) D W)) x₀ :=
    Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hD_sm hW1

  have hadd := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.add hBZ hBD (Set.mem_univ x₀)
  rw [hsplit]
  rw [LeviCivita_toFun] at hadd ⊢
  rw [hadd]
  rw [ContinuousLinearMap.add_apply]

  have hDvanish : leviCivitaStitched (I := I) g (covApply (LeviCivita (I := I) g) D W) x₀ (Y x₀) = 0 := by

    have hτ_sm : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) x
          ((LeviCivita (I := I) g).toFun W x)) := by
      rw [← contMDiffOn_univ]
      refine LeviCivita_section_contMDiffOn_univ (I := I) g ?_
      rw [ENat.coe_top_add_one]
      exact hW.contMDiffOn
    set τ : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x⟯ :=
      ⟨fun x => (LeviCivita (I := I) g).toFun W x, hτ_sm⟩ with hτ_def
    set Dsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨D, hD_sm⟩ with hDsec_def
    have hleib := HomConnectionGen.homBundleCovariantDerivativeGen_apply
      (I := I) (M := M) (E_U := E) (U := (TangentSpace I : M → Type _)) (F := E)
      (V := (TangentSpace I : M → Type _)) (LeviCivita (I := I) g) (LeviCivita (I := I) g)
      τ Dsec x₀ (Y x₀)

    rw [show (Dsec : Π b : M, TangentSpace I b) x₀ = 0 from hD_x] at hleib
    rw [ContinuousLinearMap.map_zero] at hleib

    have hτD : (fun y => (τ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) y
          ((Dsec : Π b : M, TangentSpace I b) y)) =
        covApply (LeviCivita (I := I) g) D W := by
      funext y; rfl
    rw [hτD] at hleib

    have hτterm : (τ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) x₀
          ((LeviCivita (I := I) g) (Dsec : Π b : M, TangentSpace I b) x₀ (Y x₀)) = 0 :=
      hgrad _
    rw [hτterm, sub_zero] at hleib
    exact hleib.symm
  rw [hDvanish, add_zero]

/-- **The covariant-`2`-jet-vanishing smooth tangent extension.** For a smooth Riemannian metric `g` on a
closed manifold, a base point `x₀`, and a fibre vector `v : TangentSpace I x₀`, there is a smooth
tangent-bundle section `W : Π b, TangentSpace I b` that

* extends `v`: `W x₀ = v`;
* has vanishing covariant `1`-jet at `x₀`: `∇_u W(x₀) = (LeviCivita g).toFun W x₀ u = 0` for every
  direction `u`; and
* has vanishing iterated covariant `2`-jet at `x₀`: for every smooth field `Y`,
  `∇_Y(∇_Y W)(x₀) = (LeviCivita g).toFun (covApply (LeviCivita g) Y W) x₀ (Y x₀) = 0`.

This is the composition glue of the genuine linear-extension `2`-jet-vanishing construction
`exists_linExtTwoJetVanishing_tangentExtension` (which supplies `W`, its basepoint value, its vanishing
covariant `1`-jet, and the vanishing iterated `2`-jet along every coordinate-constant reading direction)
with the value-locality reduction `covApply_covApply_eq_linExt_of_covApply_zero` (which turns the
general-field `2`-jet into the coordinate-constant one, using `∇W(x₀) = 0`). Transits the two children's
`sorryAx`. -/
theorem exists_twoJetVanishing_tangentExtension
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀) :
    ∃ W : Π b : M, TangentSpace I b,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) ∧
      W x₀ = v ∧
      (∀ u : TangentSpace I x₀, (LeviCivita (I := I) g).toFun W x₀ u = 0) ∧
      (∀ Y : Π b : M, TangentSpace I b, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) →
        (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y W) x₀ (Y x₀) = 0) := by
  obtain ⟨W, hW_sm, hW_x, hW_grad, hW_linHess⟩ :=
    exists_linExtTwoJetVanishing_tangentExtension (I := I) g x₀ v
  refine ⟨W, hW_sm, hW_x, hW_grad, fun Y hY => ?_⟩
  rw [covApply_covApply_eq_linExt_of_covApply_zero (I := I) g x₀ hW_sm hW_grad hY]
  exact hW_linHess (Y x₀)

end Connection
end Integral
end DifferentialGeometry

end
