import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ChartCurvatureRegularity
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpace

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set Filter
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.Tensor.Coordinates (extChartAt_source_eq_chartAt_source
  trivializationAt_baseSet_eq_chartAt_source)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D D₁ D₂ : RealTimeInterval}

theorem lPhaseField_contDiffOn_of_jointContMDiffOn (S : SolutionOn (I := I) (M := M) D)
    {J : Set ℝ}
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set M)))
    (T : ℝ) (x0 : M) :
    ContDiffOn ℝ ∞ (Function.uncurry (lPhaseField S T x0))
      {p : ℝ × (E × E) | T - p.1 ^ 2 ∈ J ∧ p.2.1 ∈ interior (extChartAt I x0).target} := by
  classical
  intro q hq
  let Ω : Set (ℝ × (E × E)) :=
    {p | T - p.1 ^ 2 ∈ J ∧ p.2.1 ∈ interior (extChartAt I x0).target}
  let V : Set (ℝ × E) := J ×ˢ interior (extChartAt I x0).target
  let base : ℝ × (E × E) → ℝ × E := fun p => (T - p.1 ^ 2, p.2.1)
  have hG := S.chartGramFamilySmoothWithinOn_of_jointContMDiffOn hmetric x0
  have hbase : ContDiffWithinAt ℝ ∞ base Ω q :=
    ((contDiff_const.sub (contDiff_fst.pow 2)).prodMk contDiff_snd.fst).contDiffWithinAt
  have hmaps : MapsTo base Ω V := fun p hp => ⟨hp.1, hp.2⟩
  have hbq : base q ∈ V := hmaps hq
  have hcomp : ∀ F : ℝ × E → ℝ, ContDiffWithinAt ℝ ∞ F V (base q) →
      ContDiffWithinAt ℝ ∞ (fun p => F (base p)) Ω q := fun F h => h.comp q hbase hmaps
  let christ : ℝ × (E × E) → E := fun p =>
    ∑ k : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) (S.base.metric (T - p.1 ^ 2)) x0 i j k p.2.1 *
            chartCoord (E := E) i p.2.2 * chartCoord (E := E) j p.2.2) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k
  let gradC : ℝ × (E × E) → E := fun p =>
    ∑ i : Fin (Module.finrank ℝ E),
      (∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (S.base.metric (T - p.1 ^ 2)) x0 i j p.2.1 *
          (let x := (extChartAt I x0).symm p.2.1
           mvfderiv (I := I) (S.scalar (T - p.1 ^ 2)) x
             (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x))) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i
  let ricC : ℝ × (E × E) → E := fun p =>
    ∑ i : Fin (Module.finrank ℝ E),
      (∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (S.base.metric (T - p.1 ^ 2)) x0 i j p.2.1 *
          ∑ k : Fin (Module.finrank ℝ E),
            chartCoord (E := E) k p.2.2 *
              (let x := (extChartAt I x0).symm p.2.1
               S.ricciAt (T - p.1 ^ 2) x
                 (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
                   (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x)))) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i
  let rhs : ℝ × (E × E) → E × E := fun p =>
    (p.2.2, -christ p + ((2 * p.1 ^ 2) • gradC p - (4 * p.1) • ricC p))
  have hinv (i j : Fin (Module.finrank ℝ E)) : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × (E × E) =>
        chartInvGramOnE (I := I) (S.base.metric (T - p.1 ^ 2)) x0 i j p.2.1) Ω q :=
    hcomp (fun r => chartInvGramOnE (I := I) (S.base.metric r.1) x0 i j r.2)
      (chartInvGramOnE_contDiffWithinAt S.base.metric x0 hG i j hbq.1 hbq.2)
  have hchrist (i j k : Fin (Module.finrank ℝ E)) : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × (E × E) =>
        chartChristoffel (I := I) (S.base.metric (T - p.1 ^ 2)) x0 i j k p.2.1) Ω q :=
    hcomp (fun r => chartChristoffel (I := I) (S.base.metric r.1) x0 i j k r.2)
      (chartChristoffel_contDiffWithinAt S.base.metric x0 hG i j k hbq.1 hbq.2)
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      ContDiffWithinAt ℝ ∞ (fun p : ℝ × (E × E) => chartCoord (E := E) i p.2.2) Ω q := by
    simpa only [chartCoordCLM_apply, Function.comp_def] using
      ((chartCoordCLM (E := E) i).contDiff.comp
        (contDiff_snd.snd : ContDiff ℝ ∞ (fun p : ℝ × (E × E) => p.2.2))).contDiffWithinAt
  have hscalar (j : Fin (Module.finrank ℝ E)) : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × (E × E) =>
        let x := (extChartAt I x0).symm p.2.1
        mvfderiv (I := I) (S.scalar (T - p.1 ^ 2)) x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x)) Ω q :=
    hcomp _ ((S.chartScalarDeriv_contDiffOn_of_jointContMDiffOn hmetric x0 j) (base q) hbq)
  have hric (k j : Fin (Module.finrank ℝ E)) : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × (E × E) =>
        let x := (extChartAt I x0).symm p.2.1
        S.ricciAt (T - p.1 ^ 2) x
          (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x))) Ω q :=
    hcomp _ ((S.chartRicci_contDiffOn_of_jointContMDiffOn hmetric x0 k j) (base q) hbq)
  have hchristC : ContDiffWithinAt ℝ ∞ christ Ω q := by
    refine ContDiffWithinAt.sum fun k _ => ?_
    exact (ContDiffWithinAt.sum fun i _ => ContDiffWithinAt.sum fun j _ =>
      ((hchrist i j k).mul (hcoord i)).mul (hcoord j)).smul contDiffWithinAt_const
  have hgradC : ContDiffWithinAt ℝ ∞ gradC Ω q := by
    refine ContDiffWithinAt.sum fun i _ => ?_
    exact (ContDiffWithinAt.sum fun j _ => (hinv i j).mul (hscalar j)).smul
      contDiffWithinAt_const
  have hricC : ContDiffWithinAt ℝ ∞ ricC Ω q := by
    refine ContDiffWithinAt.sum fun i _ => ?_
    exact (ContDiffWithinAt.sum fun j _ => (hinv i j).mul
      (ContDiffWithinAt.sum fun k _ => (hcoord k).mul (hric k j))).smul contDiffWithinAt_const
  have hrhs : ContDiffWithinAt ℝ ∞ rhs Ω q := by
    have hs : ContDiffWithinAt ℝ ∞ (fun p : ℝ × (E × E) => p.1) Ω q := contDiffWithinAt_fst
    have hforce : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × (E × E) => (2 * p.1 ^ 2) • gradC p - (4 * p.1) • ricC p) Ω q :=
      (((contDiffWithinAt_const (c := (2 : ℝ))).mul (hs.pow 2)).smul hgradC).sub
        (((contDiffWithinAt_const (c := (4 : ℝ))).mul hs).smul hricC)
    exact contDiffWithinAt_snd.snd.prodMk (hchristC.neg.add hforce)
  have heq : ∀ p ∈ Ω, Function.uncurry (lPhaseField S T x0) p = rhs p := by
    intro p hp
    let t := T - p.1 ^ 2
    let x := (extChartAt I x0).symm p.2.1
    let g := S.family.metric t
    let A := trivFromE (I := I) x0 x p.2.2
    have hxtarget : p.2.1 ∈ (extChartAt I x0).target := interior_subset hp.2
    have hxsrc : x ∈ (chartAt H x0).source := by
      have hxext : x ∈ (extChartAt I x0).source :=
        (extChartAt I x0).map_target hxtarget
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hxext
    have hxbase : x ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
      rwa [trivializationAt_baseSet_eq_chartAt_source]
    have hchrist_eq :
        chartChristoffelContraction (I := I) g x0 p.2.2 p.2.2 p.2.1 =
          christ p := by
      rfl
    have hgrad_eq :
        trivToE (I := I) x0 x
            (gradientFun (I := I) g (S.scalar t) x) = gradC p := by
      let cv : ∀ y : M, TangentSpace I y →ₗ[Real] Real := fun y =>
        (mfderiv I 𝓘(Real, Real) (S.scalar t) y).toLinearMap
      have hsharp := trivToE_metricSharp (I := I) g x0 cv hxbase
      change trivToE (I := I) x0 x (metricSharp (I := I) g x (cv x)) = _
      rw [hsharp]
      simp only [gradC, cv, t, g, x, chartInvGramOnE_def,
        DifferentialGeometry.mvfderiv_real_eq_mfderiv]
      refine Finset.sum_congr rfl ?_
      intro i _
      congr 1
    have hric_comp (j : Fin (Module.finrank Real E)) :
        ricciTensor (I := I) g x A
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x) =
          ∑ k : Fin (Module.finrank Real E),
            chartCoord (E := E) k p.2.2 *
              S.ricciAt t x
                (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
                    (I := I) x0 j x)) := by
      have hA : A = ∑ k : Fin (Module.finrank Real E),
          chartCoord (E := E) k p.2.2 •
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x := by
        have hcoordA : trivToE (I := I) x0 x A = p.2.2 := by
          exact trivToE_trivFromE (I := I) x0 hxbase p.2.2
        have hrec := chartBasisVecFiber_recompose (I := I) x0 hxbase A
        rw [hcoordA] at hrec
        simpa only [chartCoord_def] using hrec
      rw [hA, map_sum, sum_apply]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [map_smul, smul_apply, smul_eq_mul]
      congr 1
      exact (metricRicciAt_apply_eq_ricciTensor (I := I) g x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x)).symm
    have hric_eq :
        trivToE (I := I) x0 x
            (metricSharp (I := I) g x
              ((ricciTensor (I := I) g x A).toLinearMap)) = ricC p := by
      let cv : ∀ y : M, TangentSpace I y →ₗ[Real] Real := fun y =>
        (ricciTensor (I := I) g y
          (trivFromE (I := I) x0 y p.2.2)).toLinearMap
      have hsharp := trivToE_metricSharp (I := I) g x0 cv hxbase
      change trivToE (I := I) x0 x (metricSharp (I := I) g x (cv x)) = _
      rw [hsharp]
      simp only [ricC, cv, t, g, x, chartInvGramOnE_def]
      refine Finset.sum_congr rfl ?_
      intro i _
      congr 1
      refine Finset.sum_congr rfl ?_
      intro j _
      change chartInvGramMatrix (I := I) g x0 x i j *
          ricciTensor (I := I) g x A
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x) =
        chartInvGramMatrix (I := I) g x0 x i j *
          ∑ k : Fin (Module.finrank Real E),
            chartCoord (E := E) k p.2.2 *
              S.ricciAt t x
                (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x))
      rw [hric_comp j]
    have haccel_eq :
        trivToE (I := I) x0 x (lRegularizedAccel S T p.1 x A) =
          (2 * p.1 ^ 2) • gradC p - (4 * p.1) • ricC p := by
      change trivToE (I := I) x0 x
        ((2 * p.1 ^ 2) • gradientFun (I := I) g (S.scalar t) x -
          (4 * p.1) • metricSharp (I := I) g x
            ((ricciTensor (I := I) g x A).toLinearMap)) = _
      rw [map_sub, map_smul, map_smul, hgrad_eq, hric_eq]
    change lPhaseField S T x0 p.1 p.2 = rhs p
    simp only [lPhaseField, rhs]
    apply Prod.ext
    · rfl
    change
      -chartChristoffelContraction (I := I)
          (S.base.metric (T - p.1 ^ 2)) x0 p.2.2 p.2.2 p.2.1 +
          trivToE (I := I) x0 x (lRegularizedAccel S T p.1 x A) =
        -christ p + ((2 * p.1 ^ 2) • gradC p - (4 * p.1) • ricC p)
    rw [show chartChristoffelContraction (I := I)
        (S.base.metric (T - p.1 ^ 2)) x0 p.2.2 p.2.2 p.2.1 = christ p by
          simpa only [SolutionOn.family_metric, t, g] using hchrist_eq]
    rw [haccel_eq]
  exact hrhs.congr heq (heq q hq)

theorem lPhaseField_contDiffAt_of_jointContMDiffOn (S : SolutionOn (I := I) (M := M) D)
    {J : Set ℝ} (hJ : IsOpen J)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set M)))
    (T : ℝ) (x0 : M) {s : ℝ} {z : E × E} (ht : T - s ^ 2 ∈ J)
    (hz : z.1 ∈ interior (extChartAt I x0).target) :
    ContDiffAt ℝ ∞ (Function.uncurry (lPhaseField S T x0)) (s, z) := by
  have hopen : IsOpen {p : ℝ × (E × E) |
      T - p.1 ^ 2 ∈ J ∧ p.2.1 ∈ interior (extChartAt I x0).target} :=
    (hJ.preimage (continuous_const.sub (continuous_fst.pow 2))).inter
      (isOpen_interior.preimage continuous_snd.fst)
  exact (lPhaseField_contDiffOn_of_jointContMDiffOn S hmetric T x0).contDiffAt
    (hopen.mem_nhds ⟨ht, hz⟩)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lPhaseField_congr {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} {T s : ℝ}
    (h : S₁.base.metric (T - s ^ 2) = S₂.base.metric (T - s ^ 2)) (x0 : M) :
    lPhaseField S₁ T x0 s = lPhaseField S₂ T x0 s := by
  have hscalar : S₁.base.scalar (T - s ^ 2) = S₂.base.scalar (T - s ^ 2) := by
    unfold SolutionFamily.scalar
    rw [h]
  have hacc : lRegularizedAccel S₁ T s = lRegularizedAccel S₂ T s := by
    funext x A
    simp only [lRegularizedAccel, SolutionOn.scalar, h, hscalar]
  funext z
  simp only [lPhaseField, h, hacc]

theorem exists_lPhaseFlow_of_start (S : SolutionOn (I := I) (M := M) D) {a c : ℝ} (hac : a < c)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a c ×ˢ (univ : Set M)))
    {T s0 : ℝ} (hs0 : 0 < s0) (hstart : T - s0 ^ 2 = a) (x0 : M) (z0 : E × E)
    (hz0 : z0.1 ∈ interior (extChartAt I x0).target) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set (ℝ × (E × E)), IsOpen W ∧ (s0, z0) ∈ W ∧
      W ⊆ Ioo (s0 - ε) (s0 + ε) ×ˢ univ ∧
      ∃ Ψ : (ℝ × (E × E)) × ℝ → E × E,
        (∀ p ∈ W, Ψ (p, p.1) = p.2) ∧
        ContDiffOn ℝ ∞ Ψ (W ×ˢ Ioo (s0 - ε) (s0 + ε)) ∧
        ∀ p ∈ W, ∀ s ∈ Ioc (s0 - ε) s0,
          HasDerivAt (fun r => Ψ (p, r)) (lPhaseField S T x0 s (Ψ (p, s))) s ∧
            T - s ^ 2 ∈ Ico a c ∧ (Ψ (p, s)).1 ∈ interior (extChartAt I x0).target := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Ω : Set (ℝ × (E × E)) :=
    {p | T - p.1 ^ 2 ∈ Ico a c ∧ p.2.1 ∈ interior (extChartAt I x0).target}
  have hF : ContDiffOn ℝ ∞ (Function.uncurry (lPhaseField S T x0)) Ω :=
    lPhaseField_contDiffOn_of_jointContMDiffOn S hmetric T x0
  let refl : ℝ × (E × E) → ℝ × (E × E) := fun q => (-q.1, q.2)
  have hrefl : ContDiff ℝ ∞ refl := contDiff_fst.neg.prodMk contDiff_snd
  let f : ℝ × (E × E) → E × E := Function.uncurry (lPhaseField S T x0) ∘ refl
  let U : Set (ℝ × (E × E)) :=
    {q | q.1 < 0 ∧ T - q.1 ^ 2 < c ∧ q.2.1 ∈ interior (extChartAt I x0).target}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt (continuous_const.sub (continuous_fst.pow 2)) continuous_const).inter
        (isOpen_interior.preimage continuous_snd.fst))
  have hU0 : ((-s0, z0) : ℝ × (E × E)) ∈ U :=
    ⟨by linarith, by rw [neg_sq, hstart]; exact hac, hz0⟩
  have hf : ContDiffOn ℝ ∞ f ((Ici (-s0) ×ˢ univ) ∩ U) := by
    refine hF.comp hrefl.contDiffOn ?_
    rintro q ⟨⟨hq1, -⟩, hqneg, hqc, hqz⟩
    have hq1' : -s0 ≤ q.1 := hq1
    have hsq : q.1 ^ 2 ≤ s0 ^ 2 := by nlinarith
    refine ⟨⟨?_, ?_⟩, hqz⟩
    · change a ≤ T - (-q.1) ^ 2
      rw [neg_sq]
      linarith
    · change T - (-q.1) ^ 2 < c
      rw [neg_sq]
      exact hqc
  obtain ⟨G, hG, hGf⟩ := ContDiffOn.exists_contDiff_extension_Ici_prod_nhdsWithin hf hUopen hU0
  let vf : ℝ × (E × E) → ℝ × (E × E) := fun p => ((1 : ℝ), G (refl p))
  have hvf : ContDiff ℝ ∞ vf := contDiff_const.prodMk (hG.comp hrefl)
  let p0 : ℝ × (E × E) := (s0, z0)
  let P : ℝ × (E × E) → Prop := fun p =>
    (p.1 ≤ s0 → G (refl p) = lPhaseField S T x0 p.1 p.2) ∧ 0 < p.1 ∧ T - p.1 ^ 2 < c ∧
      p.2.1 ∈ interior (extChartAt I x0).target
  have hP : ∀ᶠ p in 𝓝 p0, P p := by
    have hext : ∀ᶠ q in 𝓝 ((-s0, z0) : ℝ × (E × E)),
        q ∈ Ici (-s0) ×ˢ (univ : Set (E × E)) → G q = f q :=
      eventually_nhdsWithin_iff.mp hGf
    have hext' : ∀ᶠ p in 𝓝 p0,
        refl p ∈ Ici (-s0) ×ˢ (univ : Set (E × E)) → G (refl p) = f (refl p) :=
      (hrefl.continuous.tendsto p0).eventually hext
    have hpos : ∀ᶠ p in 𝓝 p0, 0 < p.1 :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds (show (0 : ℝ) < p0.1 from hs0)
    have hc0 : T - p0.1 ^ 2 < c := by
      change T - s0 ^ 2 < c
      rw [hstart]
      exact hac
    have hlt : ∀ᶠ p in 𝓝 p0, T - p.1 ^ 2 < c :=
      (isOpen_lt (continuous_const.sub (continuous_fst.pow 2)) continuous_const).mem_nhds hc0
    have hint : ∀ᶠ p in 𝓝 p0, p.2.1 ∈ interior (extChartAt I x0).target :=
      (isOpen_interior.preimage continuous_snd.fst).mem_nhds hz0
    filter_upwards [hext', hpos, hlt, hint] with p hpe hpp hpl hpi
    refine ⟨fun hle => ?_, hpp, hpl, hpi⟩
    have hmem : refl p ∈ Ici (-s0) ×ˢ (univ : Set (E × E)) :=
      ⟨show -s0 ≤ -p.1 by linarith, mem_univ _⟩
    rw [hpe hmem]
    change lPhaseField S T x0 (-(-p.1)) p.2 = lPhaseField S T x0 p.1 p.2
    rw [neg_neg]
  obtain ⟨ε₀, hε₀, hlocal⟩ := exists_flow_on isOpen_univ hvf.contDiffOn isCompact_singleton
    (subset_univ _)
  obtain ⟨W₀, hW₀, hp0W₀, Ψ₀, hΨ₀0, hΨ₀sm, hΨ₀d, -⟩ := hlocal p0 (mem_singleton p0)
  have hbox : IsOpen (W₀ ×ˢ Ioo (-ε₀) ε₀) := hW₀.prod isOpen_Ioo
  have hcont : ContinuousAt Ψ₀ (p0, 0) :=
    hΨ₀sm.continuousOn.continuousAt
      (hbox.mem_nhds ⟨hp0W₀, ⟨by linarith, by linarith⟩⟩)
  have hPΨ : ∀ᶠ x in 𝓝 (p0, (0 : ℝ)), P (Ψ₀ x) := by
    have h := hΨ₀0 p0 hp0W₀
    exact hcont.eventually (by rw [h]; exact hP)
  rw [nhds_prod_eq] at hPΨ
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.mp hPΨ
  obtain ⟨t, htsub, htopen, hp0t⟩ := mem_nhds_iff.mp hpa
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp hpb
  let ε : ℝ := min ε₀ δ / 2
  have hε : 0 < ε := by positivity
  have hεε₀ : 2 * ε ≤ ε₀ := by
    have := min_le_left ε₀ δ
    simp only [ε]
    linarith
  have hεδ : 2 * ε ≤ δ := by
    have := min_le_right ε₀ δ
    simp only [ε]
    linarith
  have htime : ∀ q ∈ W₀, ∀ r ∈ Ioo (-ε₀) ε₀, (Ψ₀ (q, r)).1 = q.1 + r := by
    intro q hq
    have hzero : (0 : ℝ) ∈ Ioo (-ε₀) ε₀ := ⟨by linarith, hε₀⟩
    let phi : ℝ → ℝ := fun r => (Ψ₀ (q, r)).1 - q.1
    have hphi : ∀ r ∈ Ioo (-ε₀) ε₀, HasDerivAt phi 1 r := by
      intro r hr
      have hfst := hasFDerivAt_fst.comp_hasDerivAt r (hΨ₀d q hq r hr)
      simpa [phi, vf, Function.comp_def] using hfst.sub_const q.1
    have hphi0 : phi 0 = 0 := by
      simp only [phi, hΨ₀0 q hq, sub_self]
    intro r hr
    have h := DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
      phi hzero hphi hphi0 r hr
    simp only [phi] at h
    linarith
  let W : Set (ℝ × (E × E)) := (t ∩ W₀) ∩ Ioo (s0 - ε) (s0 + ε) ×ˢ univ
  have hWsub : W ⊆ Ioo (s0 - ε) (s0 + ε) ×ˢ univ := fun _ hp => hp.2
  have hrel : ∀ p ∈ W, ∀ s ∈ Ioo (s0 - ε) (s0 + ε), s - p.1 ∈ Ioo (-ε₀) ε₀ ∧
      dist (s - p.1) 0 < δ := by
    intro p hp s hs
    have h1 := hp.2.1
    have hlt : |s - p.1| < 2 * ε := by
      rw [abs_lt]
      constructor <;> linarith [h1.1, h1.2, hs.1, hs.2]
    refine ⟨⟨by linarith [neg_abs_le (s - p.1)], by linarith [le_abs_self (s - p.1)]⟩, ?_⟩
    rw [Real.dist_eq, sub_zero]
    linarith
  refine ⟨ε, hε, W, (htopen.inter hW₀).inter (isOpen_Ioo.prod isOpen_univ),
    ⟨⟨hp0t, hp0W₀⟩, ⟨by linarith, by linarith⟩, mem_univ _⟩, hWsub,
    fun q => (Ψ₀ (q.1, q.2 - q.1.1)).2, ?_, ?_, ?_⟩
  · intro p hp
    simp only [sub_self, hΨ₀0 p hp.1.2]
  · have hlift : ContDiff ℝ ∞ (fun q : (ℝ × (E × E)) × ℝ => (q.1, q.2 - q.1.1)) :=
      contDiff_fst.prodMk (contDiff_snd.sub contDiff_fst.fst)
    have hmaps : MapsTo (fun q : (ℝ × (E × E)) × ℝ => (q.1, q.2 - q.1.1))
        (W ×ˢ Ioo (s0 - ε) (s0 + ε)) (W₀ ×ˢ Ioo (-ε₀) ε₀) :=
      fun q hq => ⟨hq.1.1.2, (hrel q.1 hq.1 q.2 hq.2).1⟩
    exact (hΨ₀sm.comp hlift.contDiffOn hmaps).snd
  · intro p hp s hs
    have hs' : s ∈ Ioo (s0 - ε) (s0 + ε) := ⟨hs.1, by linarith [hs.2]⟩
    obtain ⟨hr, hrδ⟩ := hrel p hp s hs'
    have hPs : P (Ψ₀ (p, s - p.1)) := hab (htsub hp.1.1) (hδb hrδ)
    have hts : (Ψ₀ (p, s - p.1)).1 = s := by
      rw [htime p hp.1.2 _ hr]
      ring
    obtain ⟨hPeq, hPpos, hPlt, hPint⟩ := hPs
    rw [hts] at hPeq hPpos hPlt
    refine ⟨?_, ⟨?_, hPlt⟩, hPint⟩
    · have hd := (hΨ₀d p hp.1.2 _ hr).comp_sub_const s p.1
      have hsnd := hasFDerivAt_snd.comp_hasDerivAt s hd
      have hval : (vf (Ψ₀ (p, s - p.1))).2 = lPhaseField S T x0 s (Ψ₀ (p, s - p.1)).2 := by
        change G (refl (Ψ₀ (p, s - p.1))) = _
        rw [hPeq hs.2]
      simpa [Function.comp_def, hval] using hsnd
    · have hsq : s ^ 2 ≤ s0 ^ 2 := by nlinarith [hs.2]
      linarith

theorem exists_lPhaseAt_of_start (S : SolutionOn (I := I) (M := M) D) {a c : ℝ} (hac : a < c)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a c ×ˢ (univ : Set M)))
    {T s0 : ℝ} (hs0 : 0 < s0) (hstart : T - s0 ^ 2 = a) (x0 : M) (z0 : E × E)
    (hz0 : z0.1 ∈ interior (extChartAt I x0).target) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set (E × E), IsOpen U ∧ z0 ∈ U ∧
      ∃ Φ : (E × E) × ℝ → E × E,
        (∀ z ∈ U, Φ (z, s0) = z) ∧
        ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (s0 - ε) (s0 + ε)) ∧
        ∀ z ∈ U, ∀ s ∈ Ioc (s0 - ε) s0,
          HasDerivAt (fun r => Φ (z, r)) (lPhaseField S T x0 s (Φ (z, s))) s ∧
            T - s ^ 2 ∈ Ico a c ∧ (Φ (z, s)).1 ∈ interior (extChartAt I x0).target := by
  obtain ⟨ε, hε, W, hW, hp0, -, Ψ, hΨ0, hΨsm, hΨd⟩ :=
    exists_lPhaseFlow_of_start S hac hmetric hs0 hstart x0 z0 hz0
  let U : Set (E × E) := (fun z => (s0, z)) ⁻¹' W
  have hlift : ContDiff ℝ ∞ (fun q : (E × E) × ℝ => (((s0, q.1) : ℝ × (E × E)), q.2)) :=
    (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
  refine ⟨ε, hε, U, hW.preimage (continuous_const.prodMk continuous_id), hp0,
    fun q => Ψ ((s0, q.1), q.2), fun z hz => hΨ0 (s0, z) hz, ?_,
    fun z hz s hs => hΨd (s0, z) hz s hs⟩
  exact hΨsm.comp hlift.contDiffOn (fun q hq => ⟨hq.1, hq.2⟩)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem isLRegularizedCurveOn_transfer {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} {T : ℝ} {alpha : ℝ → M} {J : Set ℝ} {x : M}
    {Z : TangentSpace I x} (h : IsLRegularizedCurveOn S₁ T alpha J x Z)
    (hreg : ∀ s ∈ J, T - s ^ 2 ∈ D₂.regular)
    (hmetric : ∀ s ∈ J, S₁.base.metric (T - s ^ 2) = S₂.base.metric (T - s ^ 2)) :
    IsLRegularizedCurveOn S₂ T alpha J x Z := by
  refine ⟨h.1, h.2.1, fun s hs => ?_⟩
  obtain ⟨-, hdiff, hrep, hacc⟩ := h.2.2 s hs
  have hscalar : S₁.base.scalar (T - s ^ 2) = S₂.base.scalar (T - s ^ 2) := by
    unfold SolutionFamily.scalar
    rw [hmetric s hs]
  have hA : lRegularizedAccel S₁ T s = lRegularizedAccel S₂ T s := by
    funext y A
    simp only [lRegularizedAccel, SolutionOn.scalar, hmetric s hs, hscalar]
  refine ⟨hreg s hs, hdiff, hrep, ?_⟩
  rw [← hmetric s hs, ← hA]
  exact hacc

theorem lRegularizedDomain_subset_of_metric_eq {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} {T : ℝ} (hreg : D₁.regular ⊆ D₂.regular)
    (hmetric : ∀ t ∈ D₁.regular, S₁.base.metric t = S₂.base.metric t)
    (x : M) (Z : TangentSpace I x) :
    lRegularizedDomain S₁ T x Z ⊆ lRegularizedDomain S₂ T x Z := by
  rintro s ⟨alpha, J, hJ, hJc, h0, hs, halpha⟩
  exact ⟨alpha, J, hJ, hJc, h0, hs, isLRegularizedCurveOn_transfer halpha
    (fun r hr => hreg (halpha.2.2 r hr).1)
    (fun r hr => hmetric _ (halpha.2.2 r hr).1)⟩

theorem lRegularizedCurve_eqOn_of_metric_eq {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} (hS₁ : IsSolutionOn S₁) {T : ℝ}
    (hreg : D₁.regular ⊆ D₂.regular)
    (hmetric : ∀ t ∈ D₁.regular, S₁.base.metric t = S₂.base.metric t)
    (x : M) (Z : TangentSpace I x) :
    EqOn (lRegularizedCurve S₁ T x Z) (lRegularizedCurve S₂ T x Z)
      (lRegularizedDomain S₁ T x Z) := by
  intro s hs
  have hs₂ : s ∈ lRegularizedDomain S₂ T x Z :=
    lRegularizedDomain_subset_of_metric_eq hreg hmetric x Z hs
  obtain ⟨J₁, hJ₁, hJ₁c, h0J₁, hsJ₁, halpha⟩ := lRegularizedChosen_spec S₁ T x Z hs
  obtain ⟨J₂, hJ₂, hJ₂c, h0J₂, hsJ₂, hbeta⟩ := lRegularizedChosen_spec S₂ T x Z hs₂
  have hKc : IsPreconnected (J₁ ∩ J₂) := by
    rw [isPreconnected_iff_ordConnected] at hJ₁c hJ₂c ⊢
    exact hJ₁c.inter hJ₂c
  have hbeta₁ : IsLRegularizedCurveOn S₁ T (lRegularizedChosen S₂ T x Z hs₂) (J₁ ∩ J₂) x Z :=
    isLRegularizedCurveOn_transfer
      ⟨hbeta.1, hbeta.2.1, fun r hr => hbeta.2.2 r hr.2⟩
      (fun r hr => (halpha.2.2 r hr.1).1)
      (fun r hr => (hmetric _ (halpha.2.2 r hr.1).1).symm)
  rw [lRegularizedCurve_of_mem hs, lRegularizedCurve_of_mem hs₂]
  exact lRegularizedCurve_eqOn_of_initial_data S₁ hS₁ T hJ₁ hJ₁c h0J₁ (hJ₁.inter hJ₂) hKc
    ⟨h0J₁, h0J₂⟩ halpha hbeta₁ ⟨hsJ₁, hsJ₁, hsJ₂⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
