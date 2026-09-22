import DifferentialGeometry.Geometry.Metric.RicciSoliton.ChartHessianBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineCoefficientConvergence
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.DifferentiatedBasisIdentityOffCenter
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecificLimits.Basic


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

section Bilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open scoped BigOperators

private theorem bilinear_basis_reconstruction_eval
    {ι : Type*} [Fintype ι] (B : Module.Basis ι ℝ E)
    (M : ι → ι → ℝ) (i j : ι) :
    (∑ p : ι,
      (B.coord p).toContinuousLinearMap.smulRight
        (∑ q : ι, M p q • (B.coord q).toContinuousLinearMap))
      (B i) (B j) = M i j := by
  classical
  simp [sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    Module.Basis.coord_apply, B.repr_self, Finsupp.single_apply,
    mul_ite]

private theorem bilinear_basis_reconstruction
    {ι : Type*} [Fintype ι] (B : Module.Basis ι ℝ E)
    (L : E →L[ℝ] E →L[ℝ] ℝ) :
    L = ∑ i : ι,
      (B.coord i).toContinuousLinearMap.smulRight
        (∑ j : ι, L (B i) (B j) • (B.coord j).toContinuousLinearMap) := by
  apply ContinuousLinearMap.coe_injective
  apply B.ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply B.ext
  intro j
  exact (bilinear_basis_reconstruction_eval B
    (fun p q => L (B p) (B q)) i j).symm


end Bilinear

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

local notation "θ" => (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1))

theorem HalfLineMetricConvergenceData.poleEndpoint_chart_hessian_of_gradient_convergence
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular)
    (ell : P.M × ℝ → ℝ)
    (hsmooth : ∀ n : ℕ, ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, θ n)))
    (hsol : ∀ n : ℕ, gradientRicciSoliton (co.gInf (1 - θ n))
      (⟨fun x => ell (x, θ n), hsmooth n⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / θ n))
    (α : P.M) {K W : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I α).target) (hW : IsOpen W) (hWK : W ⊆ K)
    (hgradient : TendstoUniformlyOn
      (fun n => fderiv ℝ (fun y : E => ell ((extChartAt I α).symm y, θ n)))
      (fderiv ℝ (fun y : E => ell ((extChartAt I α).symm y, 1))) atTop W) :
    ∀ y ∈ W,
      DifferentiableAt ℝ (fderiv ℝ (fun z : E => ell ((extChartAt I α).symm z, 1))) y ∧
      ∀ i j : Fin (Module.finrank ℝ E),
        fderiv ℝ (fderiv ℝ (fun z : E => ell ((extChartAt I α).symm z, 1))) y
          (chartModelBasis E i) (chartModelBasis E j) =
        (1 / 2 : ℝ) * chartGramOnE (co.gInf 0) α i j y -
          chartRicciTensor (co.gInf 0) α i j y +
          ∑ k : Fin (Module.finrank ℝ E), chartChristoffel (co.gInf 0) α i j k y *
            fderiv ℝ (fun z : E => ell ((extChartAt I α).symm z, 1)) y
              (chartModelBasis E k) := by
  classical
  let _ : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let B := chartModelBasis E
  let β : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ :=
    fun i => (B.coord i).toContinuousLinearMap
  let fn : ℕ → E → ℝ := fun n y => ell ((extChartAt I α).symm y, θ n)
  let f₁ : E → ℝ := fun y => ell ((extChartAt I α).symm y, 1)
  let Vn := fun n y (ijk : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E)) =>
    (chartGramOnE (co.gInf (1 - θ n)) α ijk.1 ijk.2.1 y,
      chartRicciTensor (co.gInf (1 - θ n)) α ijk.1 ijk.2.1 y,
      chartChristoffel (co.gInf (1 - θ n)) α ijk.1 ijk.2.1 ijk.2.2 y)
  let V₀ := fun y (ijk : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E)) =>
    (chartGramOnE (co.gInf 0) α ijk.1 ijk.2.1 y,
      chartRicciTensor (co.gInf 0) α ijk.1 ijk.2.1 y,
      chartChristoffel (co.gInf 0) α ijk.1 ijk.2.1 ijk.2.2 y)
  let Qn := fun n z i j => (1 / θ n / 2) * (Vn n z (i, j, 0)).1 -
    (Vn n z (i, j, 0)).2.1 + ∑ k, (Vn n z (i, j, k)).2.2 *
      fderiv ℝ (fn n) z (B k)
  let Q₀ := fun z i j => (1 / 2 : ℝ) * (V₀ z (i, j, 0)).1 -
    (V₀ z (i, j, 0)).2.1 + ∑ k, (V₀ z (i, j, k)).2.2 * fderiv ℝ f₁ z (B k)
  let Dn := fun n z => ∑ i, (β i).smulRight (∑ j, Qn n z i j • β j)
  let D₀ := fun z => ∑ i, (β i).smulRight (∑ j, Q₀ z i j • β j)
  have hθpos (n : ℕ) : 1 < θ n := by
    change 1 < 1 + 1 / ((n : ℝ) + 1)
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hθband (n : ℕ) : 1 - θ n ∈ Icc (-1 : ℝ) 0 := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hdiv : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr hn
    constructor
    · change -1 ≤ 1 - (1 + 1 / ((n : ℝ) + 1))
      linarith
    · exact (sub_neg.mpr (hθpos n)).le
  have hθlim : Tendsto θ atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htime : Tendsto (fun n => 1 - θ n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hθlim
  have hVconv : TendstoUniformlyOn Vn V₀ atTop W :=
    (co.tendstoUniformlyOn_chart_coefficients_at_zero Phi hcarrier hregular α hK hKt
      (by norm_num : (-1 : ℝ) < 0) (fun n => 1 - θ n) hθband htime).mono hWK
  have hfn (n : ℕ) (z : E) (hz : z ∈ W) : ContDiffAt ℝ ∞ (fn n) z :=
    (scalarOnE_contDiffOn (I := I) α (hsmooth n)).contDiffAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds (hKt (hWK hz)))
  have hDcont : ContinuousOn (fderiv ℝ f₁) W := by
    apply hgradient.continuousOn
    exact (Eventually.of_forall fun n z hz =>
      ((hfn n z hz).fderiv_right (m := 1) (by decide)).continuousAt.continuousWithinAt).frequently
  have hVcont : ContinuousOn V₀ W := by
    apply continuousOn_pi.mpr
    intro ijk
    have hsubset : W ⊆ interior (extChartAt I α).target := by
      rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
      exact hWK.trans hKt
    exact ((chartGramOnE_contDiffOn (co.gInf 0) α ijk.1 ijk.2.1).continuousOn.mono
      (hWK.trans hKt)).prodMk
      (((chartRicciTensor_contDiffOn_interior (co.gInf 0) α ijk.1 ijk.2.1).continuousOn.mono
        hsubset).prodMk
        ((chartChristoffel_contDiffOn_interior (co.gInf 0) α
          ijk.1 ijk.2.1 ijk.2.2).continuousOn.mono
          hsubset))
  have hD2eq (n : ℕ) (z : E) (hz : z ∈ W) :
      fderiv ℝ (fderiv ℝ (fn n)) z = Dn n z := by
    have hzt : z ∈ (extChartAt I α).target := hKt (hWK hz)
    let x := (extChartAt I α).symm z
    have hx : x ∈ (chartAt H α).source := by
      simpa only [extChartAt_source] using (extChartAt I α).map_target hzt
    have hxy : extChartAt I α x = z := (extChartAt I α).right_inv hzt
    have hgood : x ∈ chartLeviCivitaGoodSet (I := I) α := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
      exact (extChartAt I α).map_target hzt
    have hcomponent (i j : Fin (Module.finrank ℝ E)) :
        fderiv ℝ (fderiv ℝ (fn n)) z (B i) (B j) = Qn n z i j := by
      let ev : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (B j)
      have hfd : DifferentiableAt ℝ (fderiv ℝ (fn n)) z :=
        ((hfn n z hz).fderiv_right (m := 1) (by decide)).differentiableAt_one
      have heval : chartIteratedPartialDeriv (I := I) α (fun x => ell (x, θ n)) i j z =
          fderiv ℝ (fderiv ℝ (fn n)) z (B i) (B j) := by
        change fderiv ℝ (ev ∘ fderiv ℝ (fn n)) z (B i) = _
        rw [fderiv_comp z ev.differentiableAt hfd, ev.fderiv]
        rfl
      have hh := gradientRicciSoliton_chartIteratedPartialDeriv (hsol n) α hx i j
      rw [hxy, ricciTensor_chartBasisVec_alpha_eq (co.gInf (1 - θ n)) α i j hgood,
        hxy] at hh
      rw [← heval]
      exact hh
    calc
      fderiv ℝ (fderiv ℝ (fn n)) z = ∑ i, (β i).smulRight (∑ j,
          fderiv ℝ (fderiv ℝ (fn n)) z (B i) (B j) • β j) :=
        bilinear_basis_reconstruction B (fderiv ℝ (fderiv ℝ (fn n)) z)
      _ = Dn n z := by
        simp only [Dn, hcomponent]
  intro y hy
  have hDprod : Tendsto (fun ny : ℕ × E => fderiv ℝ (fn ny.1) ny.2)
      (atTop ×ˢ 𝓝 y) (𝓝 (fderiv ℝ f₁ y)) := by
    have hbase : Tendsto (fun ny : ℕ × E => fderiv ℝ f₁ ny.2)
        (atTop ×ˢ 𝓝[W] y) (𝓝 (fderiv ℝ f₁ y)) :=
      (hDcont y hy).tendsto.comp tendsto_snd
    simpa only [hW.nhdsWithin_eq hy] using hbase.congr_uniformity
      (tendstoLocallyUniformlyOn_iff_forall_tendsto.mp
        hgradient.tendstoLocallyUniformlyOn y hy)
  have hVprod : Tendsto (fun ny : ℕ × E => Vn ny.1 ny.2)
      (atTop ×ˢ 𝓝 y) (𝓝 (V₀ y)) := by
    have hbase : Tendsto (fun ny : ℕ × E => V₀ ny.2)
        (atTop ×ˢ 𝓝[W] y) (𝓝 (V₀ y)) :=
      (hVcont y hy).tendsto.comp tendsto_snd
    simpa only [hW.nhdsWithin_eq hy] using hbase.congr_uniformity
      (tendstoLocallyUniformlyOn_iff_forall_tendsto.mp
        hVconv.tendstoLocallyUniformlyOn y hy)
  have hσ : Tendsto (fun n => 1 / θ n / 2) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.div_apply, div_one] using
      ((tendsto_const_nhds (x := (1 : ℝ))).div hθlim (by norm_num : (1 : ℝ) ≠ 0)).div_const 2
  have hQ (i j : Fin (Module.finrank ℝ E)) :
      Tendsto (fun ny : ℕ × E => Qn ny.1 ny.2 i j)
        (atTop ×ˢ 𝓝 y) (𝓝 (Q₀ y i j)) := by
    exact (((hσ.comp tendsto_fst).mul ((continuous_fst.tendsto (V₀ y (i, j, 0))).comp
      (tendsto_pi_nhds.mp hVprod (i, j, 0)))).sub
      (((continuous_fst.comp continuous_snd).tendsto (V₀ y (i, j, 0))).comp
      (tendsto_pi_nhds.mp hVprod (i, j, 0)))).add
      (tendsto_finsetSum Finset.univ fun k _ =>
        ((continuous_snd.comp continuous_snd).tendsto (V₀ y (i, j, k)) |>.comp
          (tendsto_pi_nhds.mp hVprod (i, j, k))).mul
          (((ContinuousLinearMap.apply ℝ ℝ (B k)).continuous.tendsto
            (fderiv ℝ f₁ y)).comp hDprod))
  have hDnprod : Tendsto (fun ny : ℕ × E => Dn ny.1 ny.2)
      (atTop ×ˢ 𝓝 y) (𝓝 (D₀ y)) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    exact ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ) (β i)).continuous.tendsto
      (∑ j, Q₀ y i j • β j)).comp
      (tendsto_finsetSum Finset.univ fun j _ => (hQ i j).smul tendsto_const_nhds)
  have hactual : Tendsto
      (fun ny : ℕ × E => fderiv ℝ (fderiv ℝ (fn ny.1)) ny.2)
      (atTop ×ˢ 𝓝 y) (𝓝 (D₀ y)) := by
    apply hDnprod.congr'
    filter_upwards [tendsto_snd.eventually (hW.mem_nhds hy)] with ny hny
    exact (hD2eq ny.1 ny.2 hny).symm
  have hlimit : HasFDerivAt (fderiv ℝ f₁) (D₀ y) y := by
    apply hasFDerivAt_of_tendstoUniformlyOnFilter
      (f := fun n => fderiv ℝ (fn n))
      (f' := fun n z => fderiv ℝ (fderiv ℝ (fn n)) z)
      (g := fderiv ℝ f₁) (g' := fun _ => D₀ y)
      (tendsto_prod_filter_iff.mp hactual)
    · filter_upwards [tendsto_snd.eventually (hW.mem_nhds hy)] with ny hny
      exact (((hfn ny.1 ny.2 hny).fderiv_right (m := 1)
        (by decide)).differentiableAt_one).hasFDerivAt
    · exact eventually_of_mem (hW.mem_nhds hy) fun z hz => hgradient.tendsto_at hz
  refine ⟨hlimit.differentiableAt, ?_⟩
  intro i j
  rw [hlimit.fderiv]
  exact bilinear_basis_reconstruction_eval B (Q₀ y) i j

end DifferentialGeometry.CheegerGromovCompactness
