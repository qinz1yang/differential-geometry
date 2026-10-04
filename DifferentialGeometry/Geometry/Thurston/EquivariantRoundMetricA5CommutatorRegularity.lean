import DifferentialGeometry.Geometry.Metric.Family.CovariantDerivativeBounds
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionRegularity
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5CommutatorIdentity

/-!
# Joint smoothness of the iterated covariant derivatives of the traceless Hessian

Chapter 7, surface lemma U1, route (a), step a5.2 (iii), item C2 (lane U1C2; design D18,
`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`).

For a smooth metric family `g t` and a family `A t` of covariant tensor fields whose components
in every coordinate frame are jointly smooth, every `∇^k_{g(t)} A(t)` has jointly smooth
coordinate components (`iterCov_family_components_contMDiffOn`, the time-dependent version of
the tree's private `tensor_iterCov_components_contMDiffOn`), hence a jointly smooth squared norm
(`iterCov_family_normSq_contMDiffOn`) and jointly smooth values on smooth vector fields
(`family_apply_sections_contMDiffOn`, by expanding the fields in the coordinate frame).

The traceless Hessian `M(t) = ∇²f(t) - ½ Δf(t) g(t)` of a jointly smooth `f` has jointly smooth
coordinate components (`tracelessHess_frameComp_contMDiffOn`): `∇²f = ∇(∇ f)` is an iterated
covariant derivative of the scalar field `f(t)`, `Δf` is jointly smooth by P8b's
`laplacian_family_contMDiffOn`, and the metric components are the flat chart model components.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor
open Bundle Set Filter Topology
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local notation "TF " k => Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
  (n := (∞ : WithTop ℕ∞)) k

theorem iterCov_family_components_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {r : ℕ} (A : ℝ → TF r) (x₀ : M)
    (hbase : ∀ n : Fin r → CoordinateIdx (𝕜 := ℝ) E,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => frameComp0S (A p.1) (coordinateFrameAt (I := I) x₀) p.2 n)
        (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀))
    (k : ℕ) (n : Fin (r + k) → CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => iterCov (g p.1) r (A p.1) k p.2
        (frameTuple (coordinateFrameAt (I := I) x₀) p.2 n))
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  have hsub : chartLeviCivitaGoodSet (I := I) x₀ ⊆ coordinateFrameSet (I := I) x₀ :=
    fun _ hx => chartLeviCivitaGoodSet_mem_baseSet hx
  have hc := iterCovComp_joint_contMDiffOn J (chartLeviCivitaGoodSet (I := I) x₀)
    (chartLeviCivitaGoodSet_isOpen (I := I) x₀) (coordinateFrameAt (I := I) x₀)
    (fun i => ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn i).mono hsub)
    (fun t x => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (g t))
      (coordinateFrameAt (I := I) x₀) (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x)
    (fun t => frameComp0S (A t) (coordinateFrameAt (I := I) x₀))
    (fun i j l => connectionComponents_contMDiffOn g J hgram hJ x₀ i j l)
    hbase k n
  apply hc.congr
  intro p hp
  exact (iterCovComp_eq_iterCov (g p.1) (A p.1) (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) (coordinateFrameSet_open (I := I) x₀)
    k (hsub hp.2) n).symm

omit [T2Space M] in
theorem family_normSq_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {s : ℕ} (B : ℝ → TF s)
    (hB : ∀ (x₀ : M) (n : Fin s → CoordinateIdx (𝕜 := ℝ) E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => B p.1 p.2 (frameTuple (coordinateFrameAt (I := I) x₀) p.2 n))
        (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (g p.1) p.2 s (B p.1 p.2)) (J ×ˢ (univ : Set M)) := by
  classical
  intro p hp
  let u := chartLeviCivitaGoodSet (I := I) p.2
  let frame := coordinateFrameAt (I := I) p.2
  let inv := fun q : ℝ × M => fun i j : CoordinateIdx (𝕜 := ℝ) E =>
    inverseMetricFlatModelInChartComponent (g q.1) p.2 i j (extChartAt I p.2 q.2)
  let comp := fun q : ℝ × M => fun n : Fin s → CoordinateIdx (𝕜 := ℝ) E =>
    B q.1 q.2 (frameTuple frame q.2 n)
  have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => ∑ ns : Fin s → CoordinateIdx (𝕜 := ℝ) E,
        ∑ ms : Fin s → CoordinateIdx (𝕜 := ℝ) E,
          (∏ i : Fin s, inv q (ns i) (ms i)) * comp q ns * comp q ms) (J ×ˢ u) := by
    intro q hq
    refine ContMDiffWithinAt.sum fun ns _ => ContMDiffWithinAt.sum fun ms _ => ?_
    exact ((ContMDiffWithinAt.prod fun i _ =>
      inverseComponents_contMDiffOn g J hgram p.2 (ns i) (ms i) q hq).mul
        (hB p.2 ns q hq)).mul (hB p.2 ms q hq)
  have hn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => normSq0S (g q.1) q.2 s (B q.1 q.2)) (J ×ˢ u) := by
    apply hs.congr
    intro q hq
    have hx := chartLeviCivitaGoodSet_mem_baseSet hq.2
    rw [normSq0S_eq_coord (g q.1) q.2 s (coordinateFrameAtBasis (I := I) p.2 hx)
      (inv q) (gInvBasisAt (g q.1) p.2 hx)]
    have hb (slots : Fin s → CoordinateIdx (𝕜 := ℝ) E) :
        (fun j => coordinateFrameAtBasis (I := I) p.2 hx (slots j)) =
          frameTuple frame q.2 slots := by
      funext j
      exact coordinateFrameAt_basis_apply (I := I) p.2 hx (slots j)
    simp only [coordInner0S, tensor0SComponent_apply, hb]
    rfl
  have hx : p.2 ∈ u := self_mem_chartLeviCivitaGoodSet (I := I) p.2
  apply (hn p ⟨hp.1, hx⟩).mono_of_mem_nhdsWithin
  have hu : {q : ℝ × M | q.2 ∈ u} ∈ 𝓝 p :=
    ((chartLeviCivitaGoodSet_isOpen (I := I) p.2).preimage continuous_snd).mem_nhds hx
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hu] with q hq hqu
  exact ⟨hq.1, hqu⟩

omit [T2Space M] in
theorem family_apply_sections_contMDiffOn {J : Set ℝ} {s : ℕ} (B : ℝ → TF s)
    (hB : ∀ (x₀ : M) (n : Fin s → CoordinateIdx (𝕜 := ℝ) E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => B p.1 p.2 (frameTuple (coordinateFrameAt (I := I) x₀) p.2 n))
        (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => B p.1 p.2 (fun i => V i p.2)) (J ×ˢ (univ : Set M)) := by
  classical
  intro p hp
  let u := chartLeviCivitaGoodSet (I := I) p.2
  let e := trivializationAt E (TangentSpace I : M → Type _) p.2
  let b := Module.finBasis ℝ E
  let c : Fin s → CoordinateIdx (𝕜 := ℝ) E → M → ℝ := fun i j y =>
    e.localFrameCoeff I b j y (V i y)
  have hsub : u ⊆ e.baseSet := fun _ hy => chartLeviCivitaGoodSet_mem_baseSet hy
  have hc : ∀ i j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (c i j) u := fun i j =>
    contMDiffOn_localFrameCoeff (I := I) (e := e) b (chartLeviCivitaGoodSet_isOpen (I := I) p.2)
      hsub ((V i).contMDiff.contMDiffOn) j
  have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => ∑ n : Fin s → CoordinateIdx (𝕜 := ℝ) E,
        (∏ i, c i (n i) q.2) * B q.1 q.2 (frameTuple (coordinateFrameAt (I := I) p.2) q.2 n))
      (J ×ˢ u) := by
    intro q hq
    refine ContMDiffWithinAt.sum fun n _ => ?_
    refine (ContMDiffWithinAt.prod fun i _ => ?_).mul (hB p.2 n q hq)
    exact (hc i (n i) q.2 hq.2).comp q contMDiffWithinAt_snd (fun r hr => hr.2)
  have hn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => B q.1 q.2 (fun i => V i q.2)) (J ×ˢ u) := by
    apply hs.congr
    intro q hq
    have hy : q.2 ∈ e.baseSet := hsub hq.2
    have hexp : (fun i => V i q.2) =
        fun i => ∑ j, c i j q.2 • coordinateFrameAt (I := I) p.2 j q.2 :=
      funext fun i => Bundle.Trivialization.eq_sum_localFrameCoeff_smul (I := I) (e := e)
        (b := b) (s := fun y => V i y) hy
    rw [hexp]
    have key := ContinuousMultilinearMap.map_sum
      (B q.1 q.2 : ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I q.2) ℝ)
      (fun i j => c i j q.2 • coordinateFrameAt (I := I) p.2 j q.2)
    refine key.trans (Finset.sum_congr rfl fun n _ => ?_)
    have key2 := ContinuousMultilinearMap.map_smul_univ
      (B q.1 q.2 : ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I q.2) ℝ)
      (fun i => c i (n i) q.2) (fun i => coordinateFrameAt (I := I) p.2 (n i) q.2)
    exact key2.trans (smul_eq_mul _ _)
  have hx : p.2 ∈ u := self_mem_chartLeviCivitaGoodSet (I := I) p.2
  apply (hn p ⟨hp.1, hx⟩).mono_of_mem_nhdsWithin
  have hu : {q : ℝ × M | q.2 ∈ u} ∈ 𝓝 p :=
    ((chartLeviCivitaGoodSet_isOpen (I := I) p.2).preimage continuous_snd).mem_nhds hx
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hu] with q hq hqu
  exact ⟨hq.1, hqu⟩

omit [I.Boundaryless] in
theorem duSec_eq_covStep_fromScalarField (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    duSec f hf = covStep g 0 (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) f hf) := by
  refine DFunLike.ext _ _ fun x => tensor0SSpace_ext 1 x fun v => ?_
  have hv : v = ![v 0] := by funext i; fin_cases i; rfl
  rw [covStep_fromScalarField_apply, hv, duSec_apply_vec]
  rfl

theorem tracelessHessAt_frameTuple [NeZero (Module.finrank ℝ E)] (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (x₀ x : M) (n : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    tracelessHessAt g f x (frameTuple (coordinateFrameAt (I := I) x₀) x n) =
      iterCov g 0 (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) f f.contMDiff) 2 x
          (frameTuple (coordinateFrameAt (I := I) x₀) x n) -
        ΔG g f x / 2 * g.inner x (coordinateFrameAt (I := I) x₀ (n 0) x)
          (coordinateFrameAt (I := I) x₀ (n 1) x) := by
  have hv : frameTuple (coordinateFrameAt (I := I) x₀) x n =
      vec2 (coordinateFrameAt (I := I) x₀ (n 0) x) (coordinateFrameAt (I := I) x₀ (n 1) x) := by
    funext i; fin_cases i <;> rfl
  have hv' : frameTuple (coordinateFrameAt (I := I) x₀) x n =
      ![coordinateFrameAt (I := I) x₀ (n 0) x, coordinateFrameAt (I := I) x₀ (n 1) x] := by
    funext i; fin_cases i <;> rfl
  rw [hv, tracelessHessAt_vec2, ← hv, hv']
  congr 1
  change _ = covStep g 1 (covStep g 0 (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) f
    f.contMDiff)) x _
  rw [← duSec_eq_covStep_fromScalarField, covStep_duSec_apply_vec]

section Flow

variable {T : ℝ} {hT : 0 < T}

omit [I.Boundaryless] in
theorem surfaceFlow_chartGram_contMDiffOn
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartGramMatrix (S.family.metric p.1) x₀ p.2 i j)
      (Ioo 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hmetric := MetricFamilySmoothOn.metricCLMSection_contMDiffOn
    (D := RealTimeInterval.closedOpen 0 T hT) hS.smoothMetric (J := Ioo 0 T) subset_rfl
  exact chartGramMatrix_joint_contMDiffOn (fun t => S.family.metric t) (Ioo 0 T) hmetric x₀ i j

theorem tracelessHess_frameComp_contMDiffOn [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    (Mf : ℝ → TF 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    (x₀ : M) (n : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => frameComp0S (Mf p.1) (coordinateFrameAt (I := I) x₀) p.2 n)
      (Ioo 0 T ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  have hgram := surfaceFlow_chartGram_contMDiffOn S hS
  have hJ : UniqueDiffOn ℝ (Ioo 0 T) := isOpen_Ioo.uniqueDiffOn
  have hsub : Ioo 0 T ×ˢ chartLeviCivitaGoodSet (I := I) x₀ ⊆ Ioo 0 T ×ˢ univ :=
    prod_mono subset_rfl (subset_univ _)
  have hH := iterCov_family_components_contMDiffOn (fun t => S.family.metric t) (Ioo 0 T) hJ
    hgram (fun t => Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) (f t) (f t).contMDiff) x₀
    (fun m => (hf.mono hsub).congr fun p _ => by
      simp only [frameComp0S_apply, Tensor0SField.fromScalarField_apply]) 2 n
  have hL := laplacian_family_contMDiffOn hS.smoothMetric isOpen_Ioo subset_rfl
    (u := fun s y => f s y) hf
  have hG := coordinate_model_contMDiffOn (I := I) (Ioo 0 T) x₀
    (fun q : ℝ × E => metricFlatModelInChartComponent (S.family.metric q.1) x₀ (n 0) (n 1) q.2)
    (((metricFlatModel_contDiffOn (fun t => S.family.metric t) (Ioo 0 T) hgram x₀).clm_apply
      contDiffOn_const).clm_apply contDiffOn_const)
  refine (hH.sub (((hL.mono hsub).div_const 2).mul hG)).congr fun p hp => ?_
  have hx : p.2 ∈ coordinateFrameSet (I := I) x₀ := chartLeviCivitaGoodSet_mem_baseSet hp.2
  simp only [frameComp0S_apply]
  have hlap : laplacian (LeviCivita (S.family.metric p.1)) (S.family.metric p.1)
      (fun y => f p.1 y) p.2 = ΔG (S.family.metric p.1) (f p.1) p.2 :=
    laplacian_levi_eq (S.family.metric p.1) (f p.1).contMDiff p.2
  rw [show (fun q => coordinateFrameAt (I := I) x₀ (n q) p.2) =
      frameTuple (coordinateFrameAt (I := I) x₀) p.2 n from rfl, hM p.1 hp.1,
    tracelessHessAt_frameTuple, Pi.mul_apply, hlap,
    metricFlatModelInChart_component_of_mem (S.family.metric p.1) x₀ hx]

theorem tracelessHess_iterCov_components_contMDiffOn [NeZero (Module.finrank ℝ E)]
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    (Mf : ℝ → TF 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    (q : ℕ) (x₀ : M) (n : Fin (2 + q) → CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => iterCov (S.family.metric p.1) 2 (Mf p.1) q p.2
        (frameTuple (coordinateFrameAt (I := I) x₀) p.2 n))
      (Ioo 0 T ×ˢ chartLeviCivitaGoodSet (I := I) x₀) :=
  iterCov_family_components_contMDiffOn (fun t => S.family.metric t) (Ioo 0 T)
    isOpen_Ioo.uniqueDiffOn (surfaceFlow_chartGram_contMDiffOn S hS) Mf x₀
    (tracelessHess_frameComp_contMDiffOn S hS f hf Mf hM x₀) q n

theorem tracelessHess_iterCov_normSq_contMDiffOn [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    (Mf : ℝ → TF 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x) (q : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (S.family.metric p.1) p.2 (2 + q)
        (iterCov (S.family.metric p.1) 2 (Mf p.1) q p.2)) (Ioo 0 T ×ˢ univ) :=
  family_normSq_contMDiffOn (fun t => S.family.metric t) (Ioo 0 T)
    (surfaceFlow_chartGram_contMDiffOn S hS) (fun t => iterCov (S.family.metric t) 2 (Mf t) q)
    (tracelessHess_iterCov_components_contMDiffOn S hS f hf Mf hM q)

theorem tracelessHess_iterCov_apply_contMDiffOn [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    (Mf : ℝ → TF 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x) (q : ℕ)
    (V : Fin (2 + q) → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => iterCov (S.family.metric p.1) 2 (Mf p.1) q p.2 (fun i => V i p.2))
      (Ioo 0 T ×ˢ univ) :=
  family_apply_sections_contMDiffOn (fun t => iterCov (S.family.metric t) 2 (Mf t) q)
    (tracelessHess_iterCov_components_contMDiffOn S hS f hf Mf hM q) V

end Flow

end GC.Geometry
