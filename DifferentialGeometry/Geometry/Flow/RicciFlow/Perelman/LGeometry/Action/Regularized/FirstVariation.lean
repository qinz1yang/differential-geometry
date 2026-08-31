import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Regularized

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem hasDerivAt_lRegLagrangian
    (S : SolutionOn (I := I) (M := M) D) (T s : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    HasDerivAt (fun u : Real ↦ lRegLagrangian S T (f u) s)
      ((S.base.metric (T - s ^ 2)).inner (f 0 s)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (f 0) (fun r : Real ↦
              lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
          (lVelocity (I := I) (f 0) s) +
        2 * s ^ 2 *
          (S.base.metric (T - s ^ 2)).inner (f 0 s)
            (gradientFun (I := I) (S.base.metric (T - s ^ 2))
              (S.scalar (T - s ^ 2)) (f 0 s))
            (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) 0 := by
  let g := S.base.metric (T - s ^ 2)
  have hspeed := speedSq_hasDerivAt (I := I) g f s hf
  rw [commute_ds_dt_intrinsic (I := I) g f hf s] at hspeed
  have hspeed' : HasDerivAt (fun u : Real ↦ speedSq (I := I) g f u s)
      (2 * g.inner (f 0 s)
        (covDerivAlong (I := I) g (f 0)
          (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
        (lVelocity (I := I) (f 0) s)) 0 := by
    simpa only [lVelocity] using hspeed
  have hslice : MDifferentiableAt 𝓘(Real, Real) I
      (fun u : Real ↦ f u s) 0 := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
        (fun u : Real ↦ (u, s)) :=
      contMDiff_id.prodMk contMDiff_const
    exact ((hf : ContMDiff _ _ (8 : Nat) _).comp hincl).contMDiffAt.mdifferentiableAt
      (by norm_num)
  have hscalar := lScalar_var_deriv S (T - s ^ 2 + s) s f hslice
  have hscalar' : HasDerivAt
      (fun u : Real ↦ S.scalar (T - s ^ 2) (f u s))
      ((S.base.metric (T - s ^ 2)).inner (f 0 s)
        (gradientFun (I := I) (S.base.metric (T - s ^ 2))
          (S.scalar (T - s ^ 2)) (f 0 s))
        (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) 0 := by
    convert hscalar using 1 <;> ring_nf
  have hout := (hspeed'.const_mul (1 / 2 : Real)).add
    (hscalar'.const_mul (2 * s ^ 2))
  have hfun : (fun u : Real ↦ lRegLagrangian S T (f u) s) =
      (fun y ↦ (1 / 2 : Real) * speedSq (I := I) g f y s) +
        (fun y ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (f y s)) := by
    funext u
    rfl
  rw [← hfun] at hout
  refine hout.congr_deriv ?_
  with_unfolding_all
    ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegScalar_contDiffOn_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦ S.scalar (T - p.2 ^ 2) (f p.1 p.2))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : Nat) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ (T - q.2 ^ 2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hfAt
  have hscalar₀ : ContMDiffAt
      (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M ↦ S.scalar q.1 q.2)
      (T - p.2 ^ 2, f p.1 p.2) :=
    (scalar_joint (I := I) S hS).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds hp) Filter.univ_mem)
  have hscalarMD : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ S.scalar (T - q.2 ^ 2) (f q.1 q.2)) p :=
    (hscalar₀.of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)).comp p harg
  have hscalar : ContDiffAt Real 2
      (fun q : Real × Real ↦ S.scalar (T - q.2 ^ 2) (f q.1 q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalarMD
  exact hscalar.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegSpeed_contDiffOn_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦
        (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
          (lVelocity (I := I) (f p.1) p.2)
          (lVelocity (I := I) (f p.1) p.2))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : Nat) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ (T - q.2 ^ 2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hfAt
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T - p.2 ^ 2) (x := f p.1 p.2)
    (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y ↦ TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f q.1 q.2) ((S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2))) p := by
    have hcomp := (hmetric₀.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).comp p harg
    rw [SolutionOn.family_metric] at hcomp
    with_unfolding_all exact hcomp
  have hvel : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2) : TangentBundle I M)) p := by
    simpa only [lVelocity] using
      ((velocity_totalSpace_contMDiff (I := I) (M := M) f hf) p).of_le
        (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M ↦ TangentSpace I y)
    (E₂ := fun y : M ↦ TangentSpace I y)
    (E₃ := fun _ : M ↦ Real) hmetric hvel hvel
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    with_unfolding_all exact htotal.2
  have hcd : ContDiffAt Real 2
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegPair_contDiffOn_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦
        (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
          (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
          (lVelocity (I := I) (f p.1) p.2))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  have hswap : IsSmoothVariation (I := I)
      (fun a b : Real ↦ f b a) := by
    exact (hf : ContMDiff _ _ (8 : Nat) _).comp
      (contMDiff_snd.prodMk contMDiff_fst)
  have hYall : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (7 : Nat)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real ↦ f u q.2) q.1) :
            TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff
      (I := I) (M := M) (fun a b : Real ↦ f b a) hswap
    have hcomp := hbase.comp
      (contMDiff_snd.prodMk contMDiff_fst :
        ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real))
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (7 : Nat)
          (fun q : Real × Real ↦ (q.2, q.1)))
    with_unfolding_all exact hcomp
  have hXall := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : Nat) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ (T - q.2 ^ 2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hfAt
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T - p.2 ^ 2) (x := f p.1 p.2)
    (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y ↦ TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f q.1 q.2) ((S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2))) p := by
    have hcomp := (hmetric₀.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).comp p harg
    rw [SolutionOn.family_metric] at hcomp
    with_unfolding_all exact hcomp
  have hY : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real ↦ f u q.2) q.1) :
            TangentBundle I M)) p :=
    hYall.contMDiffAt.of_le (by norm_num)
  have hX : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2) : TangentBundle I M)) p := by
    simpa only [lVelocity] using hXall.contMDiffAt.of_le (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M ↦ TangentSpace I y)
    (E₂ := fun y : M ↦ TangentSpace I y)
    (E₃ := fun _ : M ↦ Real) hmetric hY hX
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real ↦ f u q.2) q.1)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    with_unfolding_all exact htotal.2
  have hcd : ContDiffAt Real 2
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real ↦ f u q.2) q.1)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegLagrangian_contDiffOn_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦ lRegLagrangian S T (f p.1) p.2)
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  have hscalar := lRegScalar_contDiffOn_two (I := I) S hS T f hf
  have hspeed := lRegSpeed_contDiffOn_two (I := I) S hS T f hf
  simpa only [lRegLagrangian] using
    (contDiffOn_const.mul hspeed).add
      ((contDiffOn_const.mul (contDiffOn_snd.pow 2)).mul hscalar)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem hasDerivAt_lRegAction
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular) :
    HasDerivAt (fun u : Real ↦ lRegAction S T (f u) a b)
      (∫ s in a..b,
        (S.base.metric (T - s ^ 2)).inner (f 0 s)
            (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
              (f 0) (fun r : Real ↦
                lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
            (lVelocity (I := I) (f 0) s) +
          2 * s ^ 2 *
            (S.base.metric (T - s ^ 2)).inner (f 0 s)
              (gradientFun (I := I) (S.base.metric (T - s ^ 2))
                (S.scalar (T - s ^ 2)) (f 0 s))
              (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) 0 := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let lag : Real → Real → Real := fun u s ↦ lRegLagrangian S T (f u) s
  let dLag : Real → Real → Real := fun u s ↦
    fderiv Real (fun p : Real × Real ↦ lRegLagrangian S T (f p.1) p.2)
      (u, s) (1, 0)
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hlag2 : ContDiffOn Real 2
      (fun p : Real × Real ↦ lRegLagrangian S T (f p.1) p.2) U := by
    simpa only [U] using lRegLagrangian_contDiffOn_two (I := I) S hS T f hf
  have hlag1 : ContDiffOn Real 1
      (fun p : Real × Real ↦ lRegLagrangian S T (f p.1) p.2) U :=
    hlag2.of_le (by norm_num)
  have hlagJoint : ContinuousOn
      (fun p : Real × Real ↦ lRegLagrangian S T (f p.1) p.2) U :=
    hlag2.continuousOn
  have hfd : ContinuousOn
      (fderiv Real (fun p : Real × Real ↦ lRegLagrangian S T (f p.1) p.2)) U :=
    hlag1.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hdJoint : ContinuousOn (fun p : Real × Real ↦ dLag p.1 p.2) U := by
    simpa only [dLag] using hfd.clm_apply continuousOn_const
  have hlagCont (u : Real) : ContinuousOn (lag u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ (u, s)) (Set.uIcc a b) :=
      continuousOn_const.prodMk continuousOn_id
    apply hlagJoint.comp hmap
    intro s hs
    exact ht s hs
  have hdCont (u : Real) : ContinuousOn (dLag u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ (u, s)) (Set.uIcc a b) :=
      continuousOn_const.prodMk continuousOn_id
    apply hdJoint.comp hmap
    intro s hs
    exact ht s hs
  have hlagDiff : DifferentiableOn Real
      (fun p : Real × Real ↦ lRegLagrangian S T (f p.1) p.2) U :=
    hlag1.differentiableOn (by norm_num)
  have hslice (u s : Real) (hs : s ∈ Set.uIcc a b) :
      HasDerivAt (fun z : Real ↦ lag z s) (dLag u s) u := by
    have hpU : (u, s) ∈ U := ht s hs
    have hat := (hlagDiff (u, s) hpU).differentiableAt
      (hUopen.mem_nhds hpU)
    simpa only [lag, dLag] using Aux2.hasDerivAt_slice_fst
      (fun z r : Real ↦ lRegLagrangian S T (f z) r) u s hat
  let K : Set (Real × Real) := Set.Icc (-1 : Real) 1 ×ˢ Set.uIcc a b
  have hKcompact : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod isCompact_uIcc
  have hKsub : K ⊆ U := by
    intro p hp
    exact ht p.2 hp.2
  obtain ⟨C, hC⟩ :=
    hKcompact.bddAbove_image (hdJoint.mono hKsub).norm
  let C₀ : Real := max C 0
  have hC₀ : ∀ p ∈ K, ‖dLag p.1 p.2‖ ≤ C₀ := by
    intro p hp
    exact (hC ⟨p, hp, rfl⟩).trans (le_max_left C 0)
  have hnhds : Set.Icc (-1 : Real) 1 ∈ 𝓝 (0 : Real) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hmeas : ∀ᶠ u in 𝓝 (0 : Real),
      AEStronglyMeasurable (lag u)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall fun u ↦
      (hlagCont u).aestronglyMeasurable_of_subset_isCompact
        isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hint : IntervalIntegrable (lag 0) MeasureTheory.volume a b :=
    (hlagCont 0).intervalIntegrable
  have hdmeas : AEStronglyMeasurable (dLag 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hdCont 0).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hbound : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        ‖dLag u s‖ ≤ (fun _ : Real ↦ C₀) s :=
    Filter.Eventually.of_forall fun s hs u hu ↦
      hC₀ (u, s) ⟨hu, Set.uIoc_subset_uIcc hs⟩
  have hboundInt : IntervalIntegrable (fun _ : Real ↦ C₀)
      MeasureTheory.volume a b := continuousOn_const.intervalIntegrable
  have hdiff : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        HasDerivAt (fun z : Real ↦ lag z s) (dLag u s) u :=
    Filter.Eventually.of_forall fun s hs u _ ↦
      hslice u s (Set.uIoc_subset_uIcc hs)
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := lag) (F' := dLag) (x₀ := (0 : Real))
      (s := Set.Icc (-1 : Real) 1) (a := a) (b := b)
      (bound := fun _ : Real ↦ C₀) hnhds hmeas hint hdmeas
      hbound hboundInt hdiff
  let raw : Real → Real := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (f 0 s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (f 0) (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
        (lVelocity (I := I) (f 0) s) +
      2 * s ^ 2 *
        (S.base.metric (T - s ^ 2)).inner (f 0 s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (f 0 s))
          (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  have heq : Set.EqOn (dLag 0) raw (Set.uIcc a b) := by
    intro s hs
    exact (hslice 0 s hs).unique (by
      simpa only [lag, raw] using hasDerivAt_lRegLagrangian (I := I) S T s f hf)
  have heqInt : (∫ s in a..b, dLag 0 s) = ∫ s in a..b, raw s :=
    intervalIntegral.integral_congr heq
  rw [heqInt] at hparam
  simpa only [lRegAction, lag, raw] using hparam.2

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegEulerPair_variation_contDiffOn_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 1
      (fun p : Real × Real ↦
        lRegEulerPair S T (f p.1) p.2
          (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let pair : Real × Real → Real := fun p ↦
    (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
      (lVelocity (I := I) (f p.1) p.2)
  let lag : Real × Real → Real := fun p ↦ lRegLagrangian S T (f p.1) p.2
  let dPair : Real × Real → Real := fun p ↦
    fderiv Real pair p (0, 1)
  let dLag : Real × Real → Real := fun p ↦
    fderiv Real lag p (1, 0)
  let raw : Real × Real → Real := fun p ↦ dPair p - dLag p
  let euler : Real × Real → Real := fun p ↦
    lRegEulerPair S T (f p.1) p.2
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hpair2 : ContDiffOn Real 2 pair U := by
    simpa only [pair, U] using lRegPair_contDiffOn_two (I := I) S hS T f hf
  have hlag2 : ContDiffOn Real 2 lag U := by
    simpa only [lag, U] using lRegLagrangian_contDiffOn_two (I := I) S hS T f hf
  have hdPair : ContDiffOn Real 1 dPair U := by
    have hfd : ContDiffOn Real 1 (fderiv Real pair) U :=
      hpair2.fderiv_of_isOpen hUopen (by norm_num)
    simpa only [dPair] using hfd.clm_apply contDiffOn_const
  have hdLag : ContDiffOn Real 1 dLag U := by
    have hfd : ContDiffOn Real 1 (fderiv Real lag) U :=
      hlag2.fderiv_of_isOpen hUopen (by norm_num)
    simpa only [dLag] using hfd.clm_apply contDiffOn_const
  have hraw : ContDiffOn Real 1 raw U := by
    simpa only [raw] using hdPair.sub hdLag
  have hpairDiff : DifferentiableOn Real pair U :=
    hpair2.differentiableOn (by norm_num)
  have hlagDiff : DifferentiableOn Real lag U :=
    hlag2.differentiableOn (by norm_num)
  have heq : Set.EqOn euler raw U := by
    intro p hp
    let fp : Real → Real → M := fun a s ↦ f (p.1 + a) s
    have hfp : IsSmoothVariation (I := I) fp := by
      exact (hf : ContMDiff _ _ (8 : Nat) _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hfp0 : fp 0 = f p.1 := by
      funext s
      simp only [fp, add_zero]
    have hYshift (s : Real) :
        lVelocity (I := I) (fun a : Real ↦ fp a s) 0 =
          lVelocity (I := I) (fun a : Real ↦ f a s) p.1 := by
      simpa only [fp, lVelocity, varFst] using
        varFst_shift (I := I) f hf p.1 s
    have hYfun :
        (fun s : Real ↦ lVelocity (I := I) (fun a : Real ↦ fp a s) 0) =
          fun s : Real ↦
            lVelocity (I := I) (fun a : Real ↦ f a s) p.1 :=
      funext hYshift
    have hpairAt : DifferentiableAt Real pair p :=
      (hpairDiff p hp).differentiableAt (hUopen.mem_nhds hp)
    have hlagAt : DifferentiableAt Real lag p :=
      (hlagDiff p hp).differentiableAt (hUopen.mem_nhds hp)
    have hpairSlice : HasDerivAt
        (fun s : Real ↦ pair (p.1, s)) (dPair p) p.2 := by
      simpa only [dPair] using Aux2.hasDerivAt_slice_snd
        (fun u s : Real ↦ pair (u, s)) p.1 p.2 hpairAt
    have hlagSlice : HasDerivAt
        (fun u : Real ↦ lag (u, p.2)) (dLag p) p.1 := by
      simpa only [dLag] using Aux2.hasDerivAt_slice_fst
        (fun u s : Real ↦ lag (u, s)) p.1 p.2 hlagAt
    have hlagShift : HasDerivAt
        (fun u : Real ↦ lag (p.1 + u, p.2)) (dLag p) 0 :=
      HasDerivAt.comp_const_add p.1 0 (by
        simpa only [add_zero] using hlagSlice)
    have hlagGeom := hasDerivAt_lRegLagrangian (I := I) S T p.2 fp hfp
    rw [hfp0, hYfun, hYshift p.2] at hlagGeom
    have hdLagEq := hlagShift.unique (by
      simpa only [lag, fp] using hlagGeom)
    have hcentral : MDifferentiableAt 𝓘(Real, Real) I (fp 0) p.2 := by
      have hline : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
          (fun s : Real ↦ ((0 : Real), s)) :=
        contMDiff_const.prodMk contMDiff_id
      have hcomp := (hfp : ContMDiff _ _ (8 : Nat) _).comp hline
      exact hcomp.contMDiffAt.mdifferentiableAt (by norm_num)
    have hYdiff : DifferentiableAt Real
        (chartRepAt (I := I) (fp 0)
          (fun s : Real ↦
            lVelocity (I := I) (fun a : Real ↦ fp a s) 0) p.2) p.2 := by
      with_unfolding_all exact
        (variationField_chartRep_differentiableAt (I := I) fp hfp p.2)
    have hAdiff : DifferentiableAt Real
        (chartRepAt (I := I) (fp 0)
          (fun s : Real ↦ lVelocity (I := I) (fp 0) s) p.2) p.2 := by
      with_unfolding_all exact
        (velocityField_chartRep_differentiableAt (I := I) fp hfp p.2)
    have hpairGeom := lRegInner_deriv (I := I) S hS T (fp 0)
      (fun s : Real ↦ lVelocity (I := I) (fun a : Real ↦ fp a s) 0)
      (fun s : Real ↦ lVelocity (I := I) (fp 0) s) p.2 hp
      hcentral hYdiff hAdiff
    rw [hfp0, hYfun, hYshift p.2] at hpairGeom
    have hpairFun :
        (fun r : Real ↦
          (S.base.metric (T - r ^ 2)).inner (f p.1 r)
            (lVelocity (I := I) (fun a : Real ↦ fp a r) 0)
            (lVelocity (I := I) (f p.1) r)) =
          fun r : Real ↦ pair (p.1, r) := by
      funext r
      rw [hYshift r]
    rw [hpairFun] at hpairGeom
    have hdPairEq : dPair p =
        ((S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
              (covDerivAlong (I := I) (S.base.metric (T - p.2 ^ 2))
                (f p.1) (fun r : Real ↦
                  lVelocity (I := I) (fun u : Real ↦ f u r) p.1) p.2)
              (lVelocity (I := I) (f p.1) p.2) +
            (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
              (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
              (covDerivAlong (I := I) (S.base.metric (T - p.2 ^ 2))
                (f p.1) (fun r : Real ↦
                  lVelocity (I := I) (f p.1) r) p.2)) +
          4 * p.2 * S.ricciAt (T - p.2 ^ 2) (f p.1 p.2)
            (vec2
              (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
              (lVelocity (I := I) (f p.1) p.2)) := by
      exact hpairSlice.unique hpairGeom
    dsimp only [euler, raw]
    rw [hdPairEq, hdLagEq]
    simp only [lRegEulerPair]
    rw [((S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)).map_sub]
    rw [lRegAccel_inner]
    ring
  have hout : ContDiffOn Real 1 euler U :=
    hraw.congr (fun p hp ↦ heq hp)
  simpa only [euler, U] using hout

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegAction_first_variation
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular) :
    HasDerivAt (fun u : Real ↦ lRegAction S T (f u) a b)
      ((S.base.metric (T - b ^ 2)).inner (f 0 b)
            (lVelocity (I := I) (fun u : Real ↦ f u b) 0)
            (lVelocity (I := I) (f 0) b) -
        (S.base.metric (T - a ^ 2)).inner (f 0 a)
            (lVelocity (I := I) (fun u : Real ↦ f u a) 0)
            (lVelocity (I := I) (f 0) a) -
        ∫ s in a..b,
          lRegEulerPair S T (f 0) s
            (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) 0 := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let pair : Real × Real → Real := fun p ↦
    (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
      (lVelocity (I := I) (f p.1) p.2)
  let dPair : Real → Real := fun s ↦
    fderiv Real pair (0, s) (0, 1)
  let B : Real → Real := fun s ↦ pair (0, s)
  let raw : Real → Real := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (f 0 s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (f 0) (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
        (lVelocity (I := I) (f 0) s) +
      2 * s ^ 2 *
        (S.base.metric (T - s ^ 2)).inner (f 0 s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (f 0 s))
          (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  let Eul : Real → Real := fun s ↦
    lRegEulerPair S T (f 0) s
      (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hpair2 : ContDiffOn Real 2 pair U := by
    simpa only [pair, U] using lRegPair_contDiffOn_two (I := I) S hS T f hf
  have hpairDiff : DifferentiableOn Real pair U :=
    hpair2.differentiableOn (by norm_num)
  have hpair1 : ContDiffOn Real 1 pair U :=
    hpair2.of_le (by norm_num)
  have hfd : ContinuousOn (fderiv Real pair) U :=
    hpair1.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hdJoint : ContinuousOn
      (fun p : Real × Real ↦ fderiv Real pair p (0, 1)) U :=
    hfd.clm_apply continuousOn_const
  have hdCont : ContinuousOn dPair (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ ((0 : Real), s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdJoint.comp hmap
    intro s hs
    exact ht s hs
  have hBslice : ∀ s ∈ Set.uIcc a b, HasDerivAt B (dPair s) s := by
    intro s hs
    have hp : ((0 : Real), s) ∈ U := ht s hs
    have hat : DifferentiableAt Real pair (0, s) :=
      (hpairDiff (0, s) hp).differentiableAt (hUopen.mem_nhds hp)
    simpa only [B, dPair] using Aux2.hasDerivAt_slice_snd
      (fun u r : Real ↦ pair (u, r)) 0 s hat
  have hdBint : IntervalIntegrable (deriv B)
      MeasureTheory.volume a b := by
    exact hdCont.intervalIntegrable.congr (fun s hs ↦
      (hBslice s (Set.uIoc_subset_uIcc hs)).deriv.symm)
  have hEulJoint : ContinuousOn
      (fun p : Real × Real ↦
        lRegEulerPair S T (f p.1) p.2
          (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)) U := by
    simpa only [U] using (lRegEulerPair_variation_contDiffOn_one (I := I) S hS T f hf).continuousOn
  have hEulCont : ContinuousOn Eul (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ ((0 : Real), s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hEulJoint.comp hmap
    intro s hs
    exact ht s hs
  have hEulInt : IntervalIntegrable Eul MeasureTheory.volume a b :=
    hEulCont.intervalIntegrable
  have hBgeom : ∀ s ∈ Set.uIcc a b,
      HasDerivAt B (raw s + Eul s) s := by
    intro s hs
    have hcentral : MDifferentiableAt 𝓘(Real, Real) I (f 0) s := by
      have hline : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
          (fun r : Real ↦ ((0 : Real), r)) :=
        contMDiff_const.prodMk contMDiff_id
      have hcomp := (hf : ContMDiff _ _ (8 : Nat) _).comp hline
      exact hcomp.contMDiffAt.mdifferentiableAt (by norm_num)
    have hYdiff : DifferentiableAt Real
        (chartRepAt (I := I) (f 0)
          (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0) s) s := by
      with_unfolding_all exact
        (variationField_chartRep_differentiableAt (I := I) f hf s)
    have hAdiff : DifferentiableAt Real
        (chartRepAt (I := I) (f 0)
          (fun r : Real ↦ lVelocity (I := I) (f 0) r) s) s := by
      with_unfolding_all exact
        (velocityField_chartRep_differentiableAt (I := I) f hf s)
    have hinner := lRegInner_deriv (I := I) S hS T (f 0)
      (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0)
      (fun r : Real ↦ lVelocity (I := I) (f 0) r) s (ht s hs)
      hcentral hYdiff hAdiff
    convert hinner using 1
    simp only [raw, Eul, lRegEulerPair]
    rw [((S.base.metric (T - s ^ 2)).inner (f 0 s)
      (lVelocity (I := I) (fun u : Real ↦ f u s) 0)).map_sub]
    rw [lRegAccel_inner]
    ring
  have hftc := intervalIntegral.integral_deriv_eq_sub
    (fun s hs ↦ (hBslice s hs).differentiableAt) hdBint
  have hrawEq : (∫ s in a..b, raw s) =
      B b - B a - ∫ s in a..b, Eul s := by
    calc
      (∫ s in a..b, raw s) =
          ∫ s in a..b, (deriv B s - Eul s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            have hderiv := (hBgeom s hs).deriv
            linarith
      _ = (∫ s in a..b, deriv B s) - ∫ s in a..b, Eul s :=
        intervalIntegral.integral_sub hdBint hEulInt
      _ = B b - B a - ∫ s in a..b, Eul s := by rw [hftc]
  have hact : HasDerivAt (fun u : Real ↦ lRegAction S T (f u) a b)
      (∫ s in a..b, raw s) 0 := by
    simpa only [raw] using hasDerivAt_lRegAction (I := I) S hS T f hf a b ht
  apply hact.congr_deriv
  simpa only [B, pair, Eul] using hrawEq

end DifferentialGeometry.PDE.RicciFlow.Perelman
