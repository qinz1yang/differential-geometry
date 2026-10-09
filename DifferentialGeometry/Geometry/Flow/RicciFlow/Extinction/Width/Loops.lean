import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import DifferentialGeometry.Geometry.Metric.SourceTangent
import DifferentialGeometry.Topology.LoopSpace.PeriodicDescent
import DifferentialGeometry.Topology.LoopSpace.Regular
import DifferentialGeometry.Topology.Homotopy.Map
import DifferentialGeometry.Analysis.Calculus.Derivative.AffineCurveFamilies
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families
import DifferentialGeometry.Topology.LoopSpace.SmoothingSuperposition
import DifferentialGeometry.Topology.LoopSpace.Lipschitz
import DifferentialGeometry.Analysis.FiniteDimensional.CompactNeighborhood
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz

noncomputable section

universe uK

open Bundle Manifold Set MeasureTheory Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (Q : Type*) [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]


structure RegularLoop where
  toContinuousLoop : ContinuousFreeLoop Q
  contMDiff_lift : ContMDiff 𝓘(ℝ, ℝ) I 1
    (fun t : ℝ => toContinuousLoop (t : Surgery.Topology.Circle))

variable {I Q}

instance : CoeFun (RegularLoop I Q) (fun _ => Surgery.Topology.Circle → Q) :=
  ⟨fun γ => γ.toContinuousLoop⟩


def loopLift (γ : ContinuousFreeLoop Q) (t : ℝ) : Q := γ (t : Surgery.Topology.Circle)


def loopVelocity (γ : ContinuousFreeLoop Q) (t : ℝ) : TangentSpace I (loopLift γ t) :=
  mfderiv 𝓘(ℝ, ℝ) I (loopLift γ) t (1 : ℝ)


def RegularLoop.firstJet (γ : RegularLoop I Q) (t : Icc (0 : ℝ) 1) :
    TangentBundle I Q :=
  ⟨loopLift γ.toContinuousLoop t, loopVelocity (I := I) γ.toContinuousLoop t⟩

theorem RegularLoop.continuous_firstJet (γ : RegularLoop I Q) :
    Continuous γ.firstJet := by
  exact (γ.contMDiff_lift.continuous_tangentMap le_rfl).comp
    ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_subtype_val.prodMk continuous_const))


def RegularLoop.firstJetMap (γ : RegularLoop I Q) :
    C(Icc (0 : ℝ) 1, TangentBundle I Q) :=
  ⟨γ.firstJet, γ.continuous_firstJet⟩


instance regularLoopTopologicalSpace : TopologicalSpace (RegularLoop I Q) :=
  TopologicalSpace.induced
    (fun γ : RegularLoop I Q => (γ.toContinuousLoop, γ.firstJetMap)) inferInstance

theorem RegularLoop.continuous_value_jet :
    Continuous (fun γ : RegularLoop I Q => (γ.toContinuousLoop, γ.firstJetMap)) :=
  continuous_induced_dom


def regularLoopInclusion : C(RegularLoop I Q, ContinuousFreeLoop Q) :=
  ⟨RegularLoop.toContinuousLoop, continuous_fst.comp RegularLoop.continuous_value_jet⟩


abbrev ContractibleRegularLoop :=
  {γ : RegularLoop I Q // IsContractibleLoop γ.toContinuousLoop}


def contractibleRegularLoopInclusion :
    C(ContractibleRegularLoop (I := I) (Q := Q), ContractibleContinuousLoop Q) :=
  ⟨fun γ => ⟨γ.1.toContinuousLoop, γ.2⟩,
    (regularLoopInclusion.continuous.comp continuous_subtype_val).subtype_mk _⟩


abbrev RegularFamily (K : Type*) [TopologicalSpace K] :=
  C(K, ContractibleRegularLoop (I := I) (Q := Q))


abbrev RegularRepresentative (ξ : FreeContractibleSphereClass Q) :=
  {Γ : RegularFamily (I := I) (Q := Q) (Sphere 2) //
    FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ) = ξ}


def constantRegularLoop (q : Q) : RegularLoop I Q :=
  ⟨constantLoops q, contMDiff_const⟩


def constantContractibleRegularLoop (q : Q) :
    ContractibleRegularLoop (I := I) (Q := Q) :=
  ⟨constantRegularLoop q, isContractibleLoop_constant q⟩


def regularGenLoopInclusion (q : Q)
    (u : GenLoop (Fin 2) (ContractibleRegularLoop (I := I) (Q := Q))
      (constantContractibleRegularLoop q)) :
    GenLoop (Fin 2) (ContractibleContinuousLoop Q)
      (contractibleRegularLoopInclusion (constantContractibleRegularLoop (I := I) q)) :=
  ⟨contractibleRegularLoopInclusion.comp u.1,
    fun p hp => congrArg contractibleRegularLoopInclusion (u.2 p hp)⟩


structure SmoothLoopEmbedding (N : ℕ) where
  map : Q → EuclideanSpace ℝ (Fin N)
  smooth : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ map
  isClosedEmbedding : IsClosedEmbedding map
  injective_mfderiv : ∀ q, Function.Injective
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) map q)

structure SmoothTubularRetraction {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N) where
  neighborhood : Set (EuclideanSpace ℝ (Fin N))
  isOpen_neighborhood : IsOpen neighborhood
  range_subset : Set.range e.map ⊆ neighborhood
  retract : EuclideanSpace ℝ (Fin N) → Q
  smoothOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ retract neighborhood
  leftInverse : Function.LeftInverse retract e.map


def embeddingFirstJet {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (γ : RegularLoop I Q) :
    C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) where
  toFun t := (e.map (loopLift γ.toContinuousLoop t),
    deriv (e.map ∘ loopLift γ.toContinuousLoop) t)
  continuous_toFun := by
    have h : ContDiff ℝ 1 (e.map ∘ loopLift γ.toContinuousLoop) :=
      ((e.smooth.of_le (by simp)).comp γ.contMDiff_lift).contDiff
    exact (h.continuous.comp continuous_subtype_val).prodMk
      (h.continuous_deriv_one.comp continuous_subtype_val)

theorem continuous_embeddingFirstJet {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) :
    Continuous (embeddingFirstJet (I := I) (Q := Q) e) := by
  have hT : Continuous
      (fun z : TangentBundle I Q =>
        (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin N)))
          (tangentMap I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map z)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin N))).continuous.comp
      (e.smooth.continuous_tangentMap (by simp))
  let T : C(TangentBundle I Q,
      EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) :=
    ⟨fun z => (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin N)))
        (tangentMap I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map z), hT⟩
  have hjet : Continuous (fun γ : RegularLoop I Q => T.comp γ.firstJetMap) :=
    (ContinuousMap.continuous_postcomp T).comp
      (continuous_snd.comp RegularLoop.continuous_value_jet)
  refine hjet.congr fun γ => ?_
  apply ContinuousMap.ext
  intro t
  have hcr := tangentMap_comp_at (I := 𝓘(ℝ, ℝ)) (I' := I)
    (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin N)))
    (⟨(t : ℝ), (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)
    (e.smooth.mdifferentiable (by simp) (loopLift γ.toContinuousLoop (t : ℝ)))
    (γ.contMDiff_lift.mdifferentiable one_ne_zero (t : ℝ))
  have h2 : (tangentMap I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map (γ.firstJet t)).2 =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
        (e.map ∘ loopLift γ.toContinuousLoop) (t : ℝ) (1 : ℝ) :=
    congrArg (fun w : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
        (EuclideanSpace ℝ (Fin N)) => w.2) hcr.symm
  simp only [ContinuousMap.comp_apply, T, embeddingFirstJet, RegularLoop.firstJetMap,
    ContinuousMap.coe_mk]
  refine Prod.ext ?_ ?_
  · rfl
  · have hsnd : ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin N)))
        (tangentMap I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map (γ.firstJet t))).2 =
        (tangentMap I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map (γ.firstJet t)).2 := rfl
    simp only [hsnd, h2, mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv (𝕜 := ℝ)
      (f := e.map ∘ loopLift γ.toContinuousLoop) (x := (t : ℝ))

theorem continuous_value_jet_of_embeddingFirstJet_of_retraction {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) (R : SmoothTubularRetraction e) :
    Continuous[TopologicalSpace.induced (embeddingFirstJet (I := I) (Q := Q) e) inferInstance,
      inferInstance] (fun γ : RegularLoop I Q => (γ.toContinuousLoop, γ.firstJetMap)) := by
  classical
  obtain ⟨U, hU, hrange, r, hr, hleft⟩ := R
  let : TopologicalSpace (RegularLoop I Q) :=
    TopologicalSpace.induced (embeddingFirstJet (I := I) (Q := Q) e) inferInstance
  have hjet : Continuous (fun γ : RegularLoop I Q =>
      embeddingFirstJet (I := I) (Q := Q) e γ) :=
    continuous_induced_dom
  have hS : Continuous (fun p : RegularLoop I Q × Icc (0 : ℝ) 1 =>
      embeddingFirstJet (I := I) (Q := Q) e p.1 p.2) :=
    continuous_eval.comp ((hjet.comp continuous_fst).prodMk continuous_snd)
  have hval : Continuous (fun p : RegularLoop I Q × Icc (0 : ℝ) 1 =>
      r ((embeddingFirstJet (I := I) (Q := Q) e p.1 p.2).1)) :=
    hr.continuousOn.comp_continuous (continuous_fst.comp hS)
      (fun _ => hrange (mem_range_self _))
  have hW : Continuous (fun p : RegularLoop I Q × ℝ =>
      p.1.toContinuousLoop (p.2 : Surgery.Topology.Circle)) := by
    refine DifferentialGeometry.Topology.continuous_of_continuousOn_Icc_of_add_one ?_ ?_
    · have hρ : Continuous (fun p :
          (univ ×ˢ Icc (0 : ℝ) 1 : Set (RegularLoop I Q × ℝ)) =>
          ((p.1.1, (⟨p.1.2, (Set.mem_prod.mp p.2).2⟩ : Icc (0 : ℝ) 1)) :
            RegularLoop I Q × Icc (0 : ℝ) 1)) :=
        (continuous_subtype_val.fst).prodMk
          ((continuous_subtype_val.snd).subtype_mk fun p => (Set.mem_prod.mp p.2).2)
      have hdom : Continuous (fun p :
          (univ ×ˢ Icc (0 : ℝ) 1 : Set (RegularLoop I Q × ℝ)) =>
          r ((embeddingFirstJet (I := I) (Q := Q) e p.1.1
            ⟨p.1.2, (Set.mem_prod.mp p.2).2⟩).1)) :=
        (hval.comp hρ).congr fun _ => rfl
      refine continuousOn_iff_continuous_domRestrict.mpr (hdom.congr fun p => ?_)
      exact hleft (loopLift p.1.1.toContinuousLoop (p.1.2 : ℝ))
    · intro k t
      exact congrArg (fun x => k.toContinuousLoop x) (AddCircle.coe_add_period (1 : ℝ) t)
  have hV : Continuous (fun p : RegularLoop I Q × Surgery.Topology.Circle =>
      p.1.toContinuousLoop p.2) := by
    have hcoe : IsOpenQuotientMap (fun s : ℝ => (s : Surgery.Topology.Circle)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    refine (IsOpenQuotientMap.id.prodMap hcoe).continuous_comp_iff.mp ?_
    exact hW
  have hvalue : Continuous (fun γ : RegularLoop I Q => γ.toContinuousLoop) := by
    rw [DifferentialGeometry.Topology.FreeLoop.continuous_family_iff]
    exact hV
  have hfirstJet : Continuous (fun γ : RegularLoop I Q => γ.firstJetMap) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hJ : Continuous (fun p : RegularLoop I Q × Icc (0 : ℝ) 1 =>
        TotalSpace.mk' E (r ((embeddingFirstJet (I := I) (Q := Q) e p.1 p.2).1))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I r
            ((embeddingFirstJet (I := I) (Q := Q) e p.1 p.2).1)
            ((embeddingFirstJet (I := I) (Q := Q) e p.1 p.2).2))) :=
      (DifferentialGeometry.Geometry.continuousOn_source_tangentMap hU
        (hr.of_le (by exact_mod_cast le_top))).comp_continuous hS
        (fun _ => ⟨hrange (mem_range_self _), trivial⟩)
    refine hJ.congr fun p => ?_
    obtain ⟨γ, t⟩ := p
    have hcomp : loopLift γ.toContinuousLoop =
        r ∘ (e.map ∘ loopLift γ.toContinuousLoop) := by
      funext s
      exact (hleft (loopLift γ.toContinuousLoop s)).symm
    have hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I r
        (e.map (loopLift γ.toContinuousLoop (t : ℝ))) :=
      ((hr (e.map (loopLift γ.toContinuousLoop (t : ℝ)))
        (hrange (mem_range_self _))).contMDiffAt
          (hU.mem_nhds (hrange (mem_range_self _)))).mdifferentiableAt (by simp)
    have hv : DifferentiableAt ℝ (e.map ∘ loopLift γ.toContinuousLoop) (t : ℝ) :=
      (((e.smooth.of_le (by simp)).comp γ.contMDiff_lift).contDiff.differentiable
        one_ne_zero (t : ℝ))
    have htv := DifferentialGeometry.Geometry.tangent_velocity_comp
      (r := r) (v := e.map ∘ loopLift γ.toContinuousLoop) (t := (t : ℝ)) hmd hv
    rw [← hcomp] at htv
    have hjet_eq : tangentMap 𝓘(ℝ, ℝ) I (loopLift γ.toContinuousLoop)
        (⟨(t : ℝ), (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) = γ.firstJet t := rfl
    rw [hjet_eq] at htv
    simp only [Function.uncurry_apply_pair, embeddingFirstJet,
      RegularLoop.firstJetMap, ContinuousMap.coe_mk]
    exact htv.symm
  exact hvalue.prodMk hfirstJet

theorem regularLoop_topology_eq_embedding_of_retraction {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) (R : SmoothTubularRetraction e) :
    regularLoopTopologicalSpace (I := I) (Q := Q) =
      TopologicalSpace.induced (embeddingFirstJet e) inferInstance :=
  le_antisymm
    (continuous_iff_le_induced.mp (continuous_embeddingFirstJet (I := I) (Q := Q) e))
    (continuous_iff_le_induced.mp
      (continuous_value_jet_of_embeddingFirstJet_of_retraction (I := I) (Q := Q) e R))

theorem regularLoop_topology_eq_embedding {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace Q] [Nonempty Q] :
    regularLoopTopologicalSpace (I := I) (Q := Q) =
      TopologicalSpace.induced (embeddingFirstJet e) inferInstance := by
  obtain ⟨r, U, hU, hrange, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      (e := e.map) e.smooth e.isClosedEmbedding.isEmbedding e.injective_mfderiv
  exact regularLoop_topology_eq_embedding_of_retraction e ⟨U, hU, hrange, r, hr, hleft⟩

def HasContinuousSmoothLoopJets {K : Type*} [TopologicalSpace K] {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (Γ : RegularFamily (I := I) (Q := Q) K) : Prop :=
  (∀ k, ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift (Γ k).1.toContinuousLoop)) ∧
  ∀ r : ℕ, Continuous (fun p : K × ℝ =>
    iteratedDeriv r (e.map ∘ loopLift (Γ p.1).1.toContinuousLoop) p.2)


def HasContinuousSmoothJets {K : Type*} [TopologicalSpace K] {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) (Γ : C(K, RegularLoop I Q)) : Prop :=
  (∀ k, ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift (Γ k).toContinuousLoop)) ∧
  ∀ r : ℕ, Continuous (fun p : K × ℝ =>
    iteratedDeriv r (e.map ∘ loopLift (Γ p.1).toContinuousLoop) p.2)


def IsLipschitzLoop (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q) : Prop :=
  ∃ L : ℝ≥0, ∀ x y : Surgery.Topology.Circle,
    riemannianEDistOf g (γ x) (γ y) ≤ (L : ℝ≥0∞) * edist x y


def loopLength (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1,
    Real.sqrt (g.inner (loopLift γ t)
      (loopVelocity (I := I) γ t) (loopVelocity (I := I) γ t))

theorem loopLength_nonneg (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q) :
    0 ≤ loopLength g γ := by
  exact integral_nonneg fun _ => Real.sqrt_nonneg _


theorem continuous_tangentMetricSpeed (g : SmoothRiemannianMetric I Q) :
    Continuous (fun v : TangentBundle I Q => Real.sqrt (g.inner v.proj v.2 v.2)) := by
  exact (DifferentialGeometry.metricQuad_cont g).sqrt


theorem RegularLoop.integrable_speed (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) :
    IntegrableOn (fun t : ℝ => Real.sqrt (g.inner (loopLift γ.toContinuousLoop t)
      (loopVelocity (I := I) γ.toContinuousLoop t)
      (loopVelocity (I := I) γ.toContinuousLoop t))) (Icc (0 : ℝ) 1) := by
  have hc := (continuous_tangentMetricSpeed g).comp γ.continuous_firstJet
  have hc' : ContinuousOn (fun t : ℝ =>
      Real.sqrt (g.inner (loopLift γ.toContinuousLoop t)
        (loopVelocity (I := I) γ.toContinuousLoop t)
        (loopVelocity (I := I) γ.toContinuousLoop t))) (Icc (0 : ℝ) 1) :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  exact hc'.integrableOn_Icc


theorem regularFamily_continuous_firstJet {K : Type*} [TopologicalSpace K]
    (Γ : RegularFamily (I := I) (Q := Q) K) :
    Continuous (fun p : K × Icc (0 : ℝ) 1 => (Γ p.1).1.firstJet p.2) := by
  have hk : Continuous (fun k => (Γ k).1.firstJetMap) :=
    (continuous_snd.comp RegularLoop.continuous_value_jet).comp
      (continuous_subtype_val.comp Γ.continuous)
  exact continuous_eval.comp ((hk.comp continuous_fst).prodMk continuous_snd)

theorem regularFamily_uniform_speed {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g : SmoothRiemannianMetric I Q) (Γ : RegularFamily (I := I) (Q := Q) K) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ k (t : Icc (0 : ℝ) 1),
      Real.sqrt (g.inner (loopLift (Γ k).1.toContinuousLoop t)
        (loopVelocity (I := I) (Γ k).1.toContinuousLoop t)
        (loopVelocity (I := I) (Γ k).1.toContinuousLoop t)) ≤ V := by
  have hs := (continuous_tangentMetricSpeed g).comp (regularFamily_continuous_firstJet Γ)
  obtain ⟨V, hV⟩ := (isCompact_range hs).bddAbove
  refine ⟨max 0 V, le_max_left _ _, fun k t => ?_⟩
  exact (hV ⟨(k, t), rfl⟩).trans (le_max_right _ _)

theorem isLipschitzLoop_constant (g : SmoothRiemannianMetric I Q) (q : Q) :
    IsLipschitzLoop g (constantLoops q) := by
  refine ⟨0, fun x y => ?_⟩
  change riemannianEDistOf g q q ≤ _
  rw [riemannianEDistOf_self]
  exact bot_le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDistOf_comm (g : SmoothRiemannianMetric I Q) (x y : Q) :
    riemannianEDistOf g x y = riemannianEDistOf g y x := by
  let : RiemannianBundle (TangentSpace I : Q → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDistOf_le_speed_bound (g : SmoothRiemannianMetric I Q)
    (γ : ℝ → Q) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {a b V : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b, Real.sqrt (g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) ≤ V) :
    riemannianEDistOf g (γ a) (γ b) ≤ ENNReal.ofReal V * ENNReal.ofReal (b - a) := by
  let : RiemannianBundle (TangentSpace I : Q → Type _) := ⟨g.toRiemannianMetric⟩
  have hp := Manifold.riemannianEDist_le_pathELength (I := I) hγ.contMDiffOn rfl rfl hab
  change riemannianEDistOf g (γ a) (γ b) ≤ pathELength I γ a b at hp
  apply hp.trans
  calc
    pathELength I γ a b = ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) := by
      rw [pathELength_eq_lintegral_mfderiv_Icc]
      apply lintegral_congr
      intro t
      rw [← ofReal_norm, norm_eq_sqrt_real_inner]
      congr 2
    _ ≤ ∫⁻ _t in Icc a b, ENNReal.ofReal V :=
      setLIntegral_mono' measurableSet_Icc (fun t ht => ENNReal.ofReal_le_ofReal (hV t ht))
    _ = ENNReal.ofReal V * ENNReal.ofReal (b - a) := by
      rw [setLIntegral_const, Real.volume_Icc]


private theorem regularLoop_lipschitz_of_speed_bound
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q) {V : ℝ} (hV : 0 ≤ V)
    (hspeed : ∀ t ∈ Icc (-1 : ℝ) 2,
      Real.sqrt (g.inner (loopLift γ.toContinuousLoop t)
        (loopVelocity (I := I) γ.toContinuousLoop t)
        (loopVelocity (I := I) γ.toContinuousLoop t)) ≤ V) :
    ∀ x y : Surgery.Topology.Circle,
      riemannianEDistOf g (γ x) (γ y) ≤
        (let L : ℝ≥0 := ⟨V, hV⟩; (L : ℝ≥0∞)) * edist x y := by
  let L : ℝ≥0 := ⟨V, hV⟩
  intro x y
  obtain ⟨a, d, ha0, ha1, hd0, hd1, hay, hadx, hdist⟩ :=
    DifferentialGeometry.Topology.exists_short_circle_lifts x y
  have hbound : ∀ t ∈ Icc (min a (a + d)) (max a (a + d)),
      Real.sqrt (g.inner (loopLift γ.toContinuousLoop t)
        (loopVelocity (I := I) γ.toContinuousLoop t)
        (loopVelocity (I := I) γ.toContinuousLoop t)) ≤ V := by
    intro t ht
    apply hspeed t
    constructor
    · have hmin : (-1 : ℝ) ≤ min a (a + d) := le_min (by linarith) (by linarith)
      exact hmin.trans ht.1
    · have hmax : max a (a + d) ≤ (2 : ℝ) := max_le (by linarith) (by linarith)
      exact ht.2.trans hmax
  have hout : riemannianEDistOf g (γ.toContinuousLoop x) (γ.toContinuousLoop y) ≤
      ENNReal.ofReal V * ENNReal.ofReal |d| := by
    by_cases hd : 0 ≤ d
    · have hab : a ≤ a + d := by linarith
      have hp := riemannianEDistOf_le_speed_bound g (loopLift γ.toContinuousLoop)
        γ.contMDiff_lift hab (fun t ht => hbound t (by
          simpa only [min_eq_left hab, max_eq_right hab] using ht))
      rw [riemannianEDistOf_comm g (γ.toContinuousLoop x) (γ.toContinuousLoop y)]
      simpa only [loopLift, hay, hadx, add_sub_cancel_left, abs_of_nonneg hd] using hp
    · have hab : a + d ≤ a := by linarith
      have hp := riemannianEDistOf_le_speed_bound g (loopLift γ.toContinuousLoop)
        γ.contMDiff_lift hab (fun t ht => hbound t (by
          simpa only [min_eq_right hab, max_eq_left hab] using ht))
      have hdiff : a - (a + d) = -d := by ring
      simpa only [loopLift, hay, hadx, hdiff, abs_of_neg (lt_of_not_ge hd)] using hp
  calc
    riemannianEDistOf g (γ.toContinuousLoop x) (γ.toContinuousLoop y) ≤
        ENNReal.ofReal V * ENNReal.ofReal |d| := hout
    _ = (L : ℝ≥0∞) * edist x y := by
      rw [ENNReal.coe_nnreal_eq, edist_dist, hdist]
      rfl

private theorem regularLoop_speed_periodic (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) :
    Function.Periodic (fun t : ℝ => Real.sqrt (g.inner (loopLift γ.toContinuousLoop t)
      (loopVelocity (I := I) γ.toContinuousLoop t)
      (loopVelocity (I := I) γ.toContinuousLoop t))) 1 := by
  intro t
  let η : ℝ → ℝ := fun s => s + 1
  have hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 η :=
    contMDiff_id.add contMDiff_const
  have hfun : loopLift γ.toContinuousLoop ∘ η = loopLift γ.toContinuousLoop := by
    funext s
    exact congrArg γ.toContinuousLoop (AddCircle.coe_add_period (1 : ℝ) s)
  have hdη : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) η t = ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id t).add_const 1).fderiv
  have he := tangentMap_comp_at (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
    (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)
    (γ.contMDiff_lift.mdifferentiable one_ne_zero (η t))
    (hη.mdifferentiable one_ne_zero t)
  change tangentMap 𝓘(ℝ, ℝ) I (loopLift γ.toContinuousLoop ∘ η)
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) =
    tangentMap 𝓘(ℝ, ℝ) I (loopLift γ.toContinuousLoop)
      (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) η
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) at he
  rw [hfun] at he
  have h := congrArg (fun v : TangentBundle I Q => Real.sqrt (g.inner v.proj v.2 v.2)) he
  simp only [tangentMap, hdη, η] at h
  convert! h.symm using 1

private theorem regularLoop_speed_bounded (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ t ∈ Icc (-1 : ℝ) 2,
      Real.sqrt (g.inner (loopLift γ.toContinuousLoop t)
        (loopVelocity (I := I) γ.toContinuousLoop t)
        (loopVelocity (I := I) γ.toContinuousLoop t)) ≤ V := by
  have hj : Continuous (fun t : ℝ =>
      (⟨loopLift γ.toContinuousLoop t, loopVelocity (I := I) γ.toContinuousLoop t⟩ :
        TangentBundle I Q)) :=
    (γ.contMDiff_lift.continuous_tangentMap le_rfl).comp
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const))
  have hs := ((continuous_tangentMetricSpeed g).comp hj).comp
    (continuous_subtype_val : Continuous (fun t : Icc (-1 : ℝ) 2 => t.1))
  obtain ⟨V, hV⟩ := (isCompact_range hs).bddAbove
  refine ⟨max 0 V, le_max_left _ _, fun t ht => ?_⟩
  exact (hV ⟨⟨t, ht⟩, rfl⟩).trans (le_max_right _ _)

section LoopSmoothing

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace Q] [Nonempty Q]
  [T2Space Q]

private theorem exists_uniform_retraction_dist {Q F : Type*} [TopologicalSpace Q]
    [CompactSpace Q] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : Q → F} {r : F → Q} {U : Set F}
    (he : Continuous e) (hU : IsOpen U) (heU : range e ⊆ U) (hr : ContinuousOn r U)
    (hleft : ∀ q, r (e q) = q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q z, dist z (e q) < δ → z ∈ U ∧ dist (e (r z)) (e q) < ε := by
  have hS : IsCompact (range e) := isCompact_range he
  obtain ⟨η, hη, hηU⟩ := hS.exists_cthickening_subset_open hU heU
  obtain ⟨ρ, hρ, hρK⟩ := hS.exists_isCompact_cthickening
  let d := min η ρ
  have hd : 0 < d := lt_min hη hρ
  let K := Metric.cthickening d (range e)
  have hKU : K ⊆ U := (Metric.cthickening_mono (min_le_left η ρ) _).trans hηU
  have hK : IsCompact K := hρK.of_isClosed_subset Metric.isClosed_cthickening
    (Metric.cthickening_mono (min_le_right η ρ) _)
  have hcont : ContinuousOn (e ∘ r) K := he.comp_continuousOn (hr.mono hKU)
  have hur := hK.uniformContinuousOn_of_continuous hcont
  obtain ⟨τ, hτ, hτr⟩ := EMetric.uniformContinuousOn_iff.mp hur (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨a, ha, haτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hτ
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  refine ⟨min d (a : ℝ), lt_min hd ha0, fun q z hz => ?_⟩
  have hzK : z ∈ K := Metric.mem_cthickening_of_dist_le z (e q) d (range e)
    (mem_range_self q) (hz.trans_le (min_le_left _ _)).le
  have hqK : e q ∈ K := Metric.self_subset_cthickening (range e) (mem_range_self q)
  refine ⟨hKU hzK, ?_⟩
  have hdist : edist (e (r z)) (e (r (e q))) < ENNReal.ofReal ε := by
    apply hτr hzK hqK
    apply lt_trans _ haτ
    rw [edist_dist]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_lt_ofReal_iff ha0).mpr (hz.trans_le (min_le_right _ _))
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] at hdist
  rwa [hleft q] at hdist

omit [T2Space Q] in
theorem continuous_regularLoop_iff {K : Type*} [TopologicalSpace K] {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) (Γ : K → RegularLoop I Q) :
    Continuous Γ ↔
      Continuous (fun p : K × Surgery.Topology.Circle => e.map ((Γ p.1).toContinuousLoop p.2)) ∧
      Continuous (fun p : K × ℝ =>
        deriv (fun t : ℝ => e.map ((Γ p.1).toContinuousLoop (t : Surgery.Topology.Circle))) p.2) := by
  classical
  constructor
  · intro h
    have hinc : Continuous (fun k : K => (Γ k).toContinuousLoop) :=
      regularLoopInclusion.continuous.comp h
    have hv : Continuous (fun p : K × Surgery.Topology.Circle =>
        e.map ((Γ p.1).toContinuousLoop p.2)) :=
      e.smooth.continuous.comp (ContinuousMap.continuous_uncurry_of_continuous
        ⟨fun k : K => (Γ k).toContinuousLoop, hinc⟩)
    have hjet : Continuous (fun k : K => embeddingFirstJet (I := I) (Q := Q) e (Γ k)) :=
      (continuous_embeddingFirstJet (I := I) (Q := Q) e).comp h
    have hunc := ContinuousMap.continuous_uncurry_of_continuous
      ⟨fun k : K => embeddingFirstJet (I := I) (Q := Q) e (Γ k), hjet⟩
    have h2 : Continuous (fun p : K × Icc (0 : ℝ) 1 =>
        deriv (fun t : ℝ => e.map ((Γ p.1).toContinuousLoop (t : Surgery.Topology.Circle))) p.2) :=
      continuous_snd.comp hunc
    refine ⟨hv, ?_⟩
    refine DifferentialGeometry.Topology.continuous_of_continuousOn_Icc_of_add_one ?_ ?_
    · rw [continuousOn_iff_continuous_domRestrict]
      have hρ : Continuous (fun p : ↥(univ ×ˢ Icc (0 : ℝ) 1) =>
          ((p.val.1, (⟨p.val.2, (Set.mem_prod.mp p.2).2⟩ : Icc (0 : ℝ) 1)) : K × Icc (0 : ℝ) 1)) :=
        (continuous_subtype_val.fst).prodMk
          ((continuous_subtype_val.snd).subtype_mk fun p => (Set.mem_prod.mp p.2).2)
      exact (h2.comp hρ).congr fun p => rfl
    · intro k t
      have hp : Function.Periodic (fun t : ℝ =>
          e.map ((Γ k).toContinuousLoop (t : Surgery.Topology.Circle))) 1 := fun s => by
        simp only [Surgery.Topology.Circle]
        exact congrArg (fun z => e.map ((Γ k).toContinuousLoop z))
          (AddCircle.coe_add_period (1 : ℝ) s)
      simpa only [iteratedDeriv_one] using
        DifferentialGeometry.Topology.periodic_iteratedDeriv (n := 1) (T := 1) hp t
  · rintro ⟨hv, hd⟩
    rw [regularLoop_topology_eq_embedding (I := I) (Q := Q) e]
    refine continuous_induced_rng.mpr ?_
    refine ContinuousMap.continuous_of_continuous_uncurry
      (fun k : K => embeddingFirstJet (I := I) (Q := Q) e (Γ k)) ?_
    refine Continuous.prodMk ?_ ?_
    · exact hv.comp (continuous_fst.prodMk
        ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_subtype_val.comp continuous_snd)))
    · exact hd.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ Q] [CompactSpace Q]
  [Nonempty Q] [T2Space Q] in
theorem RegularLoop.embedded_contDiff {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) (γ : RegularLoop I Q) :
    ContDiff ℝ 1 (fun t : ℝ => e.map (γ.toContinuousLoop (t : Surgery.Topology.Circle))) :=
  ((e.smooth.of_le (by simp)).comp γ.contMDiff_lift).contDiff

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ Q] [CompactSpace Q]
  [Nonempty Q] [T2Space Q] in
theorem RegularLoop.toContinuousLoop_injective :
    Function.Injective (RegularLoop.toContinuousLoop (I := I) (Q := Q)) := by
  intro γ δ h
  obtain ⟨a, ha⟩ := γ
  obtain ⟨b, hb⟩ := δ
  obtain rfl := h
  exact congrArg (fun p => (⟨a, p⟩ : RegularLoop I Q)) (Subsingleton.elim ha hb)

omit [T2Space Q] in
theorem exists_regular_affine_homotopy {K : Type*} [TopologicalSpace K] {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    {r : EuclideanSpace ℝ (Fin N) → Q} {U : Set (EuclideanSpace ℝ (Fin N))}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I 1 r U)
    (hleft : ∀ q, r (e.map q) = q) (Γ : K → RegularLoop I Q)
    (hΓ : Continuous Γ)
    (B : C(K, ContinuousFreeLoop (EuclideanSpace ℝ (Fin N))))
    (hB : ∀ k, ContDiff ℝ 1 (fun t : ℝ => B k (t : Surgery.Topology.Circle)))
    (hdB : Continuous (fun p : K × ℝ =>
      deriv (fun t : ℝ => B p.1 (t : Surgery.Topology.Circle)) p.2))
    (hregion : ∀ (τ : unitInterval) k θ,
      e.map ((Γ k).toContinuousLoop θ) +
        (τ : ℝ) • (B k θ - e.map ((Γ k).toContinuousLoop θ)) ∈ U) :
    ∃ H : unitInterval × K → RegularLoop I Q,
      Continuous H ∧
      (∀ τ k θ, (H (τ, k)).toContinuousLoop θ =
        r (e.map ((Γ k).toContinuousLoop θ) +
          (τ : ℝ) • (B k θ - e.map ((Γ k).toContinuousLoop θ)))) ∧
      (∀ k, H (0, k) = Γ k) ∧
      (∀ k θ, (H (1, k)).toContinuousLoop θ = r (B k θ)) := by
  obtain ⟨hcA, hdA⟩ := (continuous_regularLoop_iff e Γ).mp hΓ
  let v : (unitInterval × K) × Surgery.Topology.Circle → EuclideanSpace ℝ (Fin N) := fun p =>
    e.map ((Γ p.1.2).toContinuousLoop p.2) +
      (p.1.1 : ℝ) • (B p.1.2 p.2 - e.map ((Γ p.1.2).toContinuousLoop p.2))
  have hproj : Continuous (fun p : (unitInterval × K) × Surgery.Topology.Circle =>
      (p.1.2, p.2)) :=
    (continuous_snd.comp continuous_fst).prodMk continuous_snd
  have hc : Continuous v := (hcA.comp hproj).add
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
      ((B.uncurry.continuous.comp hproj).sub (hcA.comp hproj)))
  have hvU (p : (unitInterval × K) × Surgery.Topology.Circle) : v p ∈ U := hregion p.1.1 p.1.2 p.2
  let J : C(unitInterval × K, ContinuousFreeLoop Q) :=
    (⟨r ∘ v, hr.continuousOn.comp_continuous hc hvU⟩ :
      C((unitInterval × K) × Surgery.Topology.Circle, Q)).curry
  have hv₁ (p : unitInterval × K) :
      ContDiff ℝ 1 (fun t : ℝ => v (p, (t : Surgery.Topology.Circle))) := by
    change ContDiff ℝ 1 (fun t : ℝ => e.map ((Γ p.2).toContinuousLoop (t : Surgery.Topology.Circle)) +
      (p.1 : ℝ) • (B p.2 (t : Surgery.Topology.Circle) -
        e.map ((Γ p.2).toContinuousLoop (t : Surgery.Topology.Circle))))
    exact (RegularLoop.embedded_contDiff e (Γ p.2)).add
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (p.1 : ℝ))).smul
        ((hB p.2).sub (RegularLoop.embedded_contDiff e (Γ p.2))))
  have hJ₁ (p : unitInterval × K) :
      ContMDiff 𝓘(ℝ, ℝ) I 1 (fun t : ℝ => J p (t : Surgery.Topology.Circle)) := by
    intro t
    change ContMDiffAt 𝓘(ℝ, ℝ) I 1
      (r ∘ fun s : ℝ => v (p, (s : Surgery.Topology.Circle))) t
    exact ((hr _ (hvU (p, (t : Surgery.Topology.Circle)))).contMDiffAt
      (hU.mem_nhds (hvU (p, (t : Surgery.Topology.Circle))))).comp t
        (hv₁ p).contMDiff.contMDiffAt
  let H : unitInterval × K → RegularLoop I Q := fun p => ⟨J p, hJ₁ p⟩
  refine ⟨H, ?_, fun _ _ _ => rfl, ?_, ?_⟩
  · apply (continuous_regularLoop_iff e H).mpr
    constructor
    · exact e.smooth.continuous.comp J.uncurry.continuous
    · have hcReal : Continuous (fun p : (unitInterval × K) × ℝ =>
          v (p.1, (p.2 : Surgery.Topology.Circle))) :=
        hc.comp (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
      have hdv : Continuous (fun p : (unitInterval × K) × ℝ =>
          deriv (fun t : ℝ => v (p.1, (t : Surgery.Topology.Circle))) p.2) := by
        change Continuous (fun p : (unitInterval × K) × ℝ =>
          deriv (fun t : ℝ => e.map ((Γ p.1.2).toContinuousLoop (t : Surgery.Topology.Circle)) +
            (p.1.1 : ℝ) • (B p.1.2 (t : Surgery.Topology.Circle) -
              e.map ((Γ p.1.2).toContinuousLoop (t : Surgery.Topology.Circle)))) p.2)
        exact DifferentialGeometry.Analysis.continuous_deriv_affine_family
          (f := fun p : K × ℝ => e.map ((Γ p.1).toContinuousLoop (p.2 : Surgery.Topology.Circle)))
          (g := fun p : K × ℝ => B p.1 (p.2 : Surgery.Topology.Circle))
          (a := fun τ : unitInterval => (τ : ℝ))
          (fun k => (RegularLoop.embedded_contDiff e (Γ k)).differentiable one_ne_zero)
          (fun k => (hB k).differentiable one_ne_zero) continuous_subtype_val hdA hdB
      exact DifferentialGeometry.Analysis.continuous_deriv_family_comp hU
        ((e.smooth.of_le (by simp)).comp_contMDiffOn hr).contDiffOn
        (fun p => (hv₁ p).differentiable one_ne_zero)
        hcReal hdv (fun p => hvU (p.1, (p.2 : Surgery.Topology.Circle)))
  · intro k
    apply RegularLoop.toContinuousLoop_injective
    apply ContinuousMap.ext
    intro θ
    change r (e.map ((Γ k).toContinuousLoop θ) + (0 : ℝ) • _) = (Γ k).toContinuousLoop θ
    rw [zero_smul, add_zero, hleft]
  · intro k θ
    change r (e.map ((Γ k).toContinuousLoop θ) +
      (1 : ℝ) • (B k θ - e.map ((Γ k).toContinuousLoop θ))) = r (B k θ)
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]

omit [T2Space Q] in
theorem exists_regular_nearby_homotopy_radius {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) :
    ∃ η : ℝ, 0 < η ∧ ∀ (K : Type*) [TopologicalSpace K]
      (Γ Δ : K → RegularLoop I Q),
      Continuous Γ → Continuous Δ →
      (∀ k θ, dist (e.map ((Δ k).toContinuousLoop θ))
        (e.map ((Γ k).toContinuousLoop θ)) < η) →
      ∃ R : unitInterval × K → RegularLoop I Q,
        Continuous R ∧ (∀ k, R (0, k) = Γ k) ∧ (∀ k, R (1, k) = Δ k) ∧
        (∀ k, Γ k = Δ k → ∀ τ, R (τ, k) = Γ k) := by
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction e.smooth
      e.isClosedEmbedding.isEmbedding e.injective_mfderiv
  obtain ⟨η, hη, hηU⟩ :=
    (isCompact_range e.smooth.continuous).exists_cthickening_subset_open hU heU
  refine ⟨η, hη, fun K _ Γ Δ hΓ hΔ hclose => ?_⟩
  obtain ⟨hcB, hdB⟩ := (continuous_regularLoop_iff e Δ).mp hΔ
  let B : C(K, ContinuousFreeLoop (EuclideanSpace ℝ (Fin N))) :=
    ⟨fun k => (⟨e.map, e.smooth.continuous⟩ :
        C(Q, EuclideanSpace ℝ (Fin N))).comp (Δ k).toContinuousLoop,
      (DifferentialGeometry.Topology.FreeLoop.continuous_family_iff _).mpr hcB⟩
  have hBval (k : K) (θ : Surgery.Topology.Circle) :
      B k θ = e.map ((Δ k).toContinuousLoop θ) := rfl
  have hregion (τ : unitInterval) (k : K) (θ : Surgery.Topology.Circle) :
      e.map ((Γ k).toContinuousLoop θ) +
        (τ : ℝ) • (B k θ - e.map ((Γ k).toContinuousLoop θ)) ∈ U := by
    apply hηU
    apply Metric.mem_cthickening_of_dist_le _ (e.map ((Γ k).toContinuousLoop θ)) η (range e.map)
      (mem_range_self _)
    have hb : ‖e.map ((Δ k).toContinuousLoop θ) -
        e.map ((Γ k).toContinuousLoop θ)‖ < η := by
      simpa only [dist_eq_norm] using hclose k θ
    rw [dist_eq_norm, hBval k θ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg τ.property.1]
    exact ((mul_le_of_le_one_left (norm_nonneg _) τ.property.2).trans_lt hb).le
  obtain ⟨R, hc, hformula, hz, ho⟩ := exists_regular_affine_homotopy e hU
    (hr.of_le (by exact_mod_cast le_top)) hleft Γ hΓ B
    (fun k => RegularLoop.embedded_contDiff e (Δ k)) hdB hregion
  refine ⟨R, hc, hz, ?_, ?_⟩
  · intro k
    apply RegularLoop.toContinuousLoop_injective
    apply ContinuousMap.ext
    intro θ
    rw [ho]
    exact hleft _
  · intro k hk τ
    apply RegularLoop.toContinuousLoop_injective
    apply ContinuousMap.ext
    intro θ
    rw [hformula]
    change r (e.map ((Γ k).toContinuousLoop θ) +
      (τ : ℝ) • (e.map ((Δ k).toContinuousLoop θ) - e.map ((Γ k).toContinuousLoop θ))) = _
    rw [← hk, sub_self, smul_zero, add_zero, hleft]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ Q] [CompactSpace Q]
  [Nonempty Q] [T2Space Q] in
private theorem isContractibleLoop_of_joined {γ δ : ContinuousFreeLoop Q}
    (h : Joined γ δ) (hγ : IsContractibleLoop γ) : IsContractibleLoop δ := by
  obtain ⟨q, hq⟩ := hγ
  exact ⟨q, ((DifferentialGeometry.Topology.homotopic_iff_joined γ δ).mpr h).symm.trans hq⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace Q] [T2Space Q] [Nonempty Q] in
theorem regular_homotopy_contractible {K : Type*} [TopologicalSpace K]
    (R : unitInterval × K → RegularLoop I Q) (hc : Continuous R)
    (hn : ∀ k, IsContractibleLoop ((R (0, k)).toContinuousLoop)) :
    ∀ p, IsContractibleLoop ((R p).toContinuousLoop) := by
  have hcont : Continuous (fun p : unitInterval × K => (R p).toContinuousLoop) :=
    regularLoopInclusion.continuous.comp hc
  rintro ⟨τ, k⟩
  have hp : Joined (0 : unitInterval) τ :=
    ⟨⟨⟨fun s => s * τ, continuous_id.mul continuous_const⟩, zero_mul τ, one_mul τ⟩⟩
  have hj : Joined (R (0, k)).toContinuousLoop (R (τ, k)).toContinuousLoop :=
    hp.map (hcont.comp (continuous_id.prodMk continuous_const))
  exact isContractibleLoop_of_joined ((DifferentialGeometry.Topology.homotopic_iff_joined _ _).mp
    ((DifferentialGeometry.Topology.homotopic_iff_joined _ _).mpr hj)) (hn k)

omit [T2Space Q] in
theorem exists_regular_contractible_nearby_homotopy_radius {K : Type*} [TopologicalSpace K]
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Γ Δ : C(K, ContractibleRegularLoop (I := I) (Q := Q))),
      (∀ k θ, dist (e.map ((Δ k).1.toContinuousLoop θ))
        (e.map ((Γ k).1.toContinuousLoop θ)) < ε) →
      ∃ H : Γ.Homotopy Δ, ∀ k, Γ k = Δ k → ∀ τ, H (τ, k) = Γ k := by
  obtain ⟨ε, hε, hR⟩ := exists_regular_nearby_homotopy_radius (I := I) (Q := Q) e
  refine ⟨ε, hε, fun Γ Δ hclose => ?_⟩
  obtain ⟨R, hc, hz, ho, hf⟩ := hR K (fun k => (Γ k).1) (fun k => (Δ k).1)
    (continuous_subtype_val.comp Γ.continuous) (continuous_subtype_val.comp Δ.continuous) hclose
  have hn : ∀ p, IsContractibleLoop ((R p).toContinuousLoop) :=
    regular_homotopy_contractible (I := I) (Q := Q) R hc (fun k => by rw [hz]; exact (Γ k).2)
  have hcn : Continuous (fun p => (⟨R p, hn p⟩ : ContractibleRegularLoop (I := I) (Q := Q))) :=
    hc.subtype_mk _
  let H : Γ.Homotopy Δ :=
    ⟨⟨fun p => ⟨R p, hn p⟩, hcn⟩, fun k => Subtype.ext (hz k), fun k => Subtype.ext (ho k)⟩
  exact ⟨H, fun k hk τ => Subtype.ext (hf k (congrArg Subtype.val hk) τ)⟩

omit [CompactSpace Q] [Nonempty Q] [T2Space Q] in
private theorem familyHomotopy_contractible {K : Type*} [TopologicalSpace K]
    {Γ S : C(K, ContinuousFreeLoop Q)} (H : Γ.Homotopy S)
    {k : K} (hk : IsContractibleLoop (Γ k)) (t : unitInterval) :
    IsContractibleLoop (H (t, k)) := by
  have hp : Joined (0 : unitInterval) t :=
    ⟨⟨⟨fun s => s * t, continuous_id.mul continuous_const⟩, zero_mul t, one_mul t⟩⟩
  have hj : Joined (H (0, k)) (H (t, k)) := hp.map
    (H.continuous.comp (continuous_id.prodMk continuous_const))
  exact isContractibleLoop_of_joined hj (H.apply_zero k ▸ hk)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ Q] [Nonempty Q] [T2Space Q] in
theorem exists_uniform_retracted_loop_homotopy {K : Type*} [TopologicalSpace K]
    [CompactSpace K] {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    {r : EuclideanSpace ℝ (Fin N) → Q} {U : Set (EuclideanSpace ℝ (Fin N))}
    (hU : IsOpen U) (heU : range e.map ⊆ U)
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ r U)
    (hleft : ∀ q, r (e.map q) = q) (Γ : C(K, ContinuousFreeLoop Q))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
      ∃ (S : C(K, ContinuousFreeLoop Q)) (H : Γ.Homotopy S),
        (∀ k, ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => S k (t : Surgery.Topology.Circle))) ∧
        (∀ (d : ℕ) (a : Q → EuclideanSpace ℝ (Fin d)),
          ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ a →
          ∀ j, Continuous (fun p : K × ℝ =>
            iteratedDeriv j (fun t : ℝ => a (S p.1 (t : Surgery.Topology.Circle))) p.2)) ∧
        (∀ t k θ, dist (e.map (H (t, k) θ)) (e.map (Γ k θ)) < ε) ∧
        (∀ k q, Γ k = .const Surgery.Topology.Circle q →
          ∀ t, H (t, k) = .const Surgery.Topology.Circle q) ∧
        (∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (H (t, k))) ∧
        (∀ k θ, S k θ = r (DifferentialGeometry.Topology.averagedLoop φ
          ((⟨e.map, e.smooth.continuous⟩ :
          C(Q, EuclideanSpace ℝ (Fin N))).comp (Γ k)) θ)) ∧
        (∀ t k θ, H (t, k) θ = r (e.map (Γ k θ) + (t : ℝ) •
          (DifferentialGeometry.Topology.averagedLoop φ ((⟨e.map, e.smooth.continuous⟩ :
            C(Q, EuclideanSpace ℝ (Fin N))).comp (Γ k)) θ - e.map (Γ k θ)))) := by
  obtain ⟨a, ha, har⟩ := exists_uniform_retraction_dist e.smooth.continuous hU heU hr.continuousOn
    hleft hε
  let ec : C(Q, EuclideanSpace ℝ (Fin N)) := ⟨e.map, e.smooth.continuous⟩
  let A : C(K, ContinuousFreeLoop (EuclideanSpace ℝ (Fin N))) :=
    (DifferentialGeometry.Topology.FreeLoop.postcompose ec).comp Γ
  obtain ⟨δ, hδ, hδA⟩ :=
    DifferentialGeometry.Topology.smoothPeriodic_uniform_approximation A.uncurry.continuous ha
  refine ⟨δ, hδ, fun φ hφ => ?_⟩
  let B : C(K, ContinuousFreeLoop (EuclideanSpace ℝ (Fin N))) :=
    ⟨fun k => DifferentialGeometry.Topology.averagedLoop φ (A k),
      DifferentialGeometry.Topology.averagedLoop_continuous_family φ A.continuous⟩
  have hclose (k : K) (θ : Surgery.Topology.Circle) : dist (B k θ) (e.map (Γ k θ)) < a := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact hδA φ hφ k t
  let v : (unitInterval × K) × Surgery.Topology.Circle → EuclideanSpace ℝ (Fin N) :=
    fun p => e.map (Γ p.1.2 p.2) + (p.1.1 : ℝ) • (B p.1.2 p.2 - e.map (Γ p.1.2 p.2))
  have hcA : Continuous (fun p : (unitInterval × K) × Surgery.Topology.Circle =>
      e.map (Γ p.1.2 p.2)) :=
    A.uncurry.continuous.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hcB : Continuous (fun p : (unitInterval × K) × Surgery.Topology.Circle =>
      B p.1.2 p.2) :=
    B.uncurry.continuous.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hcv : Continuous v := hcA.add
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul (hcB.sub hcA))
  have hvclose (p : (unitInterval × K) × Surgery.Topology.Circle) :
      dist (v p) (e.map (Γ p.1.2 p.2)) < a := by
    dsimp only [v]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg p.1.1.property.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) p.1.1.property.2).trans_lt (hclose p.1.2 p.2)
  have hvU (p : (unitInterval × K) × Surgery.Topology.Circle) : v p ∈ U :=
    (har (Γ p.1.2 p.2) (v p) (hvclose p)).1
  have hcH : Continuous (r ∘ v) := hr.continuousOn.comp_continuous hcv hvU
  let J : C(unitInterval × K, ContinuousFreeLoop Q) :=
    (⟨r ∘ v, hcH⟩ : C((unitInterval × K) × Surgery.Topology.Circle, Q)).curry
  let S : C(K, ContinuousFreeLoop Q) :=
    J.comp ⟨fun k => (1, k), continuous_const.prodMk continuous_id⟩
  have hJ0 (k : K) : J (0, k) = Γ k := by
    ext θ
    change r (e.map (Γ k θ) + (0 : ℝ) • _) = Γ k θ
    rw [zero_smul, add_zero, hleft]
  let H : Γ.Homotopy S := ⟨J, hJ0, fun _ => rfl⟩
  have hS (k : K) (θ : Surgery.Topology.Circle) : S k θ = r (B k θ) := by
    change r (e.map (Γ k θ) + (1 : ℝ) • (B k θ - e.map (Γ k θ))) = _
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]
  refine ⟨S, H, ?_, ?_, ?_, ?_,
    (fun k hk t => familyHomotopy_contractible H hk t), hS, fun _ _ _ => rfl⟩
  · intro k t
    have htU : B k (t : Surgery.Topology.Circle) ∈ U :=
      (har (Γ k (t : Surgery.Topology.Circle)) _ (hclose k _)).1
    have hB : ContDiff ℝ ∞
        (fun t : ℝ => B k (t : Surgery.Topology.Circle)) :=
      DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ
        ((A k).continuous.comp (AddCircle.continuous_mk' (1 : ℝ)))
    have hs := ((hr _ htU).contMDiffAt (hU.mem_nhds htU)).comp t hB.contMDiff.contMDiffAt
    simpa only [hS, Function.comp_def] using hs
  · intro d a ha j
    simp_rw [hS]
    have hAB : Continuous (fun p : K × ℝ => A p.1 (p.2 : Surgery.Topology.Circle)) :=
      A.uncurry.continuous.comp
        (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
    exact DifferentialGeometry.Analysis.continuous_iteratedDeriv_family_comp hU
      (ha.comp_contMDiffOn hr).contDiffOn
      (fun k => DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ
        ((A k).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))))
      (fun j => DifferentialGeometry.Analysis.continuous_iteratedDeriv_smoothPeriodic φ hAB j)
      (fun p => (har (Γ p.1 (p.2 : Surgery.Topology.Circle)) _ (hclose p.1 _)).1) j
  · intro t k θ
    exact (har (Γ k θ) (v ((t, k), θ)) (hvclose ((t, k), θ))).2
  · intro k q hk t
    have hAk : A k = .const Surgery.Topology.Circle (e.map q) := by
      apply ContinuousMap.ext
      intro θ
      change e.map (Γ k θ) = e.map q
      rw [hk]
      rfl
    have hBk : B k = .const Surgery.Topology.Circle (e.map q) := by
      change DifferentialGeometry.Topology.averagedLoop φ (A k) = _
      rw [hAk, DifferentialGeometry.Topology.averagedLoop_const]
    ext θ
    change r (e.map (Γ k θ) + (t : ℝ) • (B k θ - e.map (Γ k θ))) = q
    rw [hk, hBk]
    simp only [ContinuousMap.const_apply, sub_self, smul_zero, add_zero, hleft]

omit [T2Space Q] in
theorem exists_uniform_smooth_loop_homotopy {K : Type*} [TopologicalSpace K]
    [CompactSpace K] {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (Γ : C(K, ContinuousFreeLoop Q)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
      ∃ (S : C(K, ContinuousFreeLoop Q)) (H : Γ.Homotopy S),
        (∀ k, ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => S k (t : Surgery.Topology.Circle))) ∧
        (∀ (d : ℕ) (a : Q → EuclideanSpace ℝ (Fin d)),
          ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ a →
          ∀ j, Continuous (fun p : K × ℝ =>
            iteratedDeriv j (fun t : ℝ => a (S p.1 (t : Surgery.Topology.Circle))) p.2)) ∧
        (∀ t k θ, dist (e.map (H (t, k) θ)) (e.map (Γ k θ)) < ε) ∧
        (∀ k q, Γ k = .const Surgery.Topology.Circle q →
          ∀ t, H (t, k) = .const Surgery.Topology.Circle q) ∧
        (∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (H (t, k))) := by
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction e.smooth
    e.isClosedEmbedding.isEmbedding e.injective_mfderiv
  obtain ⟨δ, hδ, hδS⟩ := exists_uniform_retracted_loop_homotopy e hU heU hr hleft Γ hε
  refine ⟨δ, hδ, fun φ hφ => ?_⟩
  obtain ⟨S, H, hs, hj, hclose, hconst, hnull, _, _⟩ := hδS φ hφ
  exact ⟨S, H, hs, hj, hclose, hconst, hnull⟩

omit [T2Space Q] in
theorem exists_smooth_regular_family {K : Type*} [TopologicalSpace K] [CompactSpace K] {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (Γ : C(K, ContinuousFreeLoop Q)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : C(K, ContinuousFreeLoop Q))
      (hs : ∀ k, ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => S k (t : Surgery.Topology.Circle)))
      (H : Γ.Homotopy S),
      Continuous (fun k => (⟨S k, (hs k).of_le (by simp)⟩ : RegularLoop I Q)) ∧
      (∀ t k θ, dist (e.map (H (t, k) θ)) (e.map (Γ k θ)) < ε) ∧
      (∀ k q, Γ k = .const Surgery.Topology.Circle q →
        ∀ t, H (t, k) = .const Surgery.Topology.Circle q) ∧
      (∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (H (t, k))) := by
  obtain ⟨δ, hδ, hδS⟩ := exists_uniform_smooth_loop_homotopy (K := K) e Γ hε
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  obtain ⟨S, H, hs, hj, hclose, hconst, hnull⟩ := hδS φ (by dsimp [φ]; linarith)
  refine ⟨S, hs, H, ?_, hclose, hconst, hnull⟩
  apply (continuous_regularLoop_iff e (fun k => (⟨S k, (hs k).of_le (by simp)⟩ : RegularLoop I Q))).mpr
  constructor
  · have h0 : Continuous (fun p : K × ℝ =>
        e.map (S p.1 (p.2 : Surgery.Topology.Circle))) := by
      simpa only [iteratedDeriv_zero] using hj N e.map e.smooth 0
    have hcoe : IsOpenQuotientMap (fun s : ℝ => (s : Surgery.Topology.Circle)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    exact (IsOpenQuotientMap.id.prodMap hcoe).continuous_comp_iff.mp h0
  · have h1 : Continuous (fun p : K × ℝ =>
        iteratedDeriv 1 (fun t : ℝ => e.map (S p.1 (t : Surgery.Topology.Circle))) p.2) :=
      hj N e.map e.smooth 1
    simpa only [iteratedDeriv_one] using h1

omit [T2Space Q] in
theorem exists_regular_contractible_representative {K : Type*} [TopologicalSpace K]
    [CompactSpace K] {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (Γ : C(K, ContractibleContinuousLoop Q)) :
    ∃ (S : C(K, ContractibleRegularLoop (I := I) (Q := Q)))
      (H : Γ.Homotopy (contractibleRegularLoopInclusion.comp S)),
      (∀ k, ContMDiff 𝓘(ℝ, ℝ) I ∞
        (fun t : ℝ => (S k).1.toContinuousLoop (t : Surgery.Topology.Circle))) ∧
      (∀ k q, Γ k = (⟨constantLoops q, isContractibleLoop_constant q⟩ :
          ContractibleContinuousLoop Q) →
        ∀ t, H (t, k) = ⟨constantLoops q, isContractibleLoop_constant q⟩) := by
  obtain ⟨S₀, hs, H₀, hcont, hclose, hconst, hnull⟩ :=
    exists_smooth_regular_family (K := K) e
      (DifferentialGeometry.Topology.ContractibleLoop.inclusion.comp Γ) zero_lt_one
  have hSn (k : K) : IsContractibleLoop (S₀ k) := by
    simpa only [H₀.apply_one] using hnull k (Γ k).2 1
  let Sfun : K → ContractibleRegularLoop (I := I) (Q := Q) :=
    fun k => ⟨⟨S₀ k, (hs k).of_le (by simp)⟩, hSn k⟩
  have hS : Continuous Sfun := hcont.subtype_mk _
  let S : C(K, ContractibleRegularLoop (I := I) (Q := Q)) := ⟨Sfun, hS⟩
  let H : Γ.Homotopy (contractibleRegularLoopInclusion.comp S) :=
    ⟨⟨fun p => ⟨H₀ p, hnull p.2 (Γ p.2).2 p.1⟩, H₀.continuous.subtype_mk _⟩,
      fun k => Subtype.ext (H₀.apply_zero k), fun k => Subtype.ext (H₀.apply_one k)⟩
  refine ⟨S, H, ?_, ?_⟩
  · intro k
    simpa only [S, ContinuousMap.coe_mk, Sfun] using hs k
  · intro k q hk t
    apply Subtype.ext
    exact hconst k q (congrArg Subtype.val hk) t

omit [T2Space Q] in
theorem regular_contractible_homotopicRel_of_continuous {K : Type*} [TopologicalSpace K]
    [CompactSpace K] {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) :
    ∀ (Γ Δ : C(K, ContractibleRegularLoop (I := I) (Q := Q))) (A : Set K),
      (∀ k ∈ A, ∃ q, Γ k = constantContractibleRegularLoop q) →
      (contractibleRegularLoopInclusion.comp Γ).HomotopicRel
        (contractibleRegularLoopInclusion.comp Δ) A →
      Γ.HomotopicRel Δ A := by
  intro Γ Δ A hA ⟨Hc⟩
  obtain ⟨ε, hε, hnear⟩ := exists_regular_contractible_nearby_homotopy_radius (K := K) e
  let Ψ : C(unitInterval × K, ContinuousFreeLoop Q) :=
    ⟨fun p => (Hc p).1, continuous_subtype_val.comp Hc.continuous⟩
  obtain ⟨S₀, hs, F, hcont, hclose, hconst, hnull⟩ :=
    exists_smooth_regular_family e Ψ hε
  have hSn (p : unitInterval × K) : IsContractibleLoop (S₀ p) := by
    simpa only [F.apply_one] using hnull p (Hc p).2 1
  let Sfun : unitInterval × K → ContractibleRegularLoop (I := I) (Q := Q) :=
    fun p => ⟨⟨S₀ p, (hs p).of_le (by simp)⟩, hSn p⟩
  have hS : Continuous Sfun := hcont.subtype_mk _
  let S : C(unitInterval × K, ContractibleRegularLoop (I := I) (Q := Q)) := ⟨Sfun, hS⟩
  let Szero : C(K, ContractibleRegularLoop (I := I) (Q := Q)) :=
    ⟨fun k => S (0, k), S.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let Sone : C(K, ContractibleRegularLoop (I := I) (Q := Q)) :=
    ⟨fun k => S (1, k), S.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hzclose (k : K) (θ : Surgery.Topology.Circle) :
      dist (e.map ((Szero k).1.toContinuousLoop θ))
        (e.map ((Γ k).1.toContinuousLoop θ)) < ε := by
    have h := hclose 1 (0, k) θ
    rw [F.apply_one] at h
    change dist (e.map (S₀ (0, k) θ)) (e.map ((Hc (0, k)).1 θ)) < _ at h
    rw [Hc.apply_zero] at h
    exact h
  have hoclose (k : K) (θ : Surgery.Topology.Circle) :
      dist (e.map ((Sone k).1.toContinuousLoop θ))
        (e.map ((Δ k).1.toContinuousLoop θ)) < ε := by
    have h := hclose 1 (1, k) θ
    rw [F.apply_one] at h
    change dist (e.map (S₀ (1, k) θ)) (e.map ((Hc (1, k)).1 θ)) < _ at h
    rw [Hc.apply_one] at h
    exact h
  obtain ⟨Jzero, hJzero⟩ := hnear Γ Szero hzclose
  obtain ⟨Jone, hJone⟩ := hnear Δ Sone hoclose
  have hfix (t : unitInterval) (k : K) (hk : k ∈ A) : S (t, k) = Γ k := by
    obtain ⟨q, hq⟩ := hA k hk
    have hΨ : Ψ (t, k) = .const Surgery.Topology.Circle q := by
      change (Hc (t, k)).1 = _
      rw [Hc.eq_fst t hk]
      change ((Γ k).1).toContinuousLoop = _
      rw [hq]
      rfl
    apply Subtype.ext
    apply RegularLoop.toContinuousLoop_injective
    change S₀ (t, k) = (Γ k).1.toContinuousLoop
    rw [hq]
    exact (F.apply_one (t, k)) ▸ hconst (t, k) q hΨ 1
  have hΓΔ (k : K) (hk : k ∈ A) : Γ k = Δ k := by
    apply Subtype.ext
    apply RegularLoop.toContinuousLoop_injective
    exact congrArg (fun γ : ContractibleContinuousLoop Q => γ.1) (Hc.fst_eq_snd hk)
  let Jz : Γ.HomotopyRel Szero A :=
    ⟨Jzero, fun t k hk => hJzero k (hfix 0 k hk).symm t⟩
  let Jo : Δ.HomotopyRel Sone A :=
    ⟨Jone, fun t k hk => hJone k ((hΓΔ k hk).symm.trans (hfix 1 k hk).symm) t⟩
  let Jm : Szero.HomotopyRel Sone A :=
    ⟨⟨S, fun _ => rfl, fun _ => rfl⟩,
      fun t k hk => (hfix t k hk).trans (hfix 0 k hk).symm⟩
  exact ⟨Jz.trans (Jm.trans Jo.symm)⟩

end LoopSmoothing

variable [finiteDimensionalE : FiniteDimensional ℝ E] [boundarylessI : I.Boundaryless]
  [t2Q : T2Space Q] [compactQ : CompactSpace Q] [connectedQ : ConnectedSpace Q]

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ

omit boundarylessI connectedQ in
theorem smoothLoopEmbedding_exists :
    ∃ N : ℕ, Nonempty (SmoothLoopEmbedding (I := I) (Q := Q) N) := by
  obtain ⟨N, e, hs, he, hd⟩ := exists_embedding_euclidean_of_compact (I := I) (M := Q)
  exact ⟨N, ⟨e, hs, he, hd⟩⟩

omit t2Q in
theorem smoothTubularRetraction_exists {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) : Nonempty (SmoothTubularRetraction e) := by
  obtain ⟨r, U, hU, hrange, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction e.smooth
      e.isClosedEmbedding.isEmbedding e.injective_mfderiv
  exact ⟨⟨U, hU, hrange, r, hr, hleft⟩⟩

omit finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem RegularLoop.isLipschitz
    (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) : IsLipschitzLoop g γ.toContinuousLoop := by
  obtain ⟨V, hV, hspeed⟩ := regularLoop_speed_bounded g γ
  let L : ℝ≥0 := ⟨V, hV⟩
  refine ⟨L, ?_⟩
  exact regularLoop_lipschitz_of_speed_bound g γ hV hspeed

omit finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem regularFamily_uniform_bounds
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g : SmoothRiemannianMetric I Q) (Γ : RegularFamily (I := I) (Q := Q) K) :
    ∃ L : ℝ≥0, (∀ k x y, riemannianEDistOf g ((Γ k).1.toContinuousLoop x)
        ((Γ k).1.toContinuousLoop y) ≤ (L : ℝ≥0∞) * edist x y) ∧
      ∀ k, loopLength g (Γ k).1.toContinuousLoop ≤ (L : ℝ) := by
  obtain ⟨V, hV, hspeed⟩ := regularFamily_uniform_speed g Γ
  let L : ℝ≥0 := ⟨V, hV⟩
  refine ⟨L, ?_, ?_⟩
  · intro k
    apply regularLoop_lipschitz_of_speed_bound g (Γ k).1 hV
    intro t ht
    let s : ℝ → ℝ := fun r => Real.sqrt (g.inner (loopLift (Γ k).1.toContinuousLoop r)
      (loopVelocity (I := I) (Γ k).1.toContinuousLoop r)
      (loopVelocity (I := I) (Γ k).1.toContinuousLoop r))
    have hp : Function.Periodic s 1 := regularLoop_speed_periodic g (Γ k).1
    change s t ≤ V
    by_cases ht0 : 0 ≤ t
    · by_cases ht1 : t ≤ 1
      · exact hspeed k ⟨t, ht0, ht1⟩
      · have hb : s (t - 1) ≤ V := hspeed k ⟨t - 1, by constructor <;> linarith [ht.1, ht.2]⟩
        have he : s t = s (t - 1) := by simpa only [sub_add_cancel] using hp (t - 1)
        exact he.trans_le hb
    · have hb : s (t + 1) ≤ V := hspeed k ⟨t + 1, by constructor <;> linarith [ht.1, ht.2]⟩
      exact (hp t).symm.trans_le hb
  · intro k
    change (∫ t in Icc (0 : ℝ) 1,
      Real.sqrt (g.inner (loopLift (Γ k).1.toContinuousLoop t)
        (loopVelocity (I := I) (Γ k).1.toContinuousLoop t)
        (loopVelocity (I := I) (Γ k).1.toContinuousLoop t))) ≤ V
    calc
      _ ≤ ∫ _t in Icc (0 : ℝ) 1, V := by
        apply setIntegral_mono_on ((Γ k).1.integrable_speed g)
          (integrableOn_const (hs := by simp) (hC := by simp))
          measurableSet_Icc
        exact fun t ht => hspeed k ⟨t, ht⟩
      _ = V := by simp

omit finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
private theorem sqrt_metric_smul_tangent (g : SmoothRiemannianMetric I Q) (p : Q) (c : ℝ)
    (v : TangentSpace I p) :
    Real.sqrt (g.inner p (c • v) (c • v)) = |c| * Real.sqrt (g.inner p v v) := by
  have h : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

omit finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
private theorem exists_compact_source_metric_mfderiv_bound {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (g : SmoothRiemannianMetric I Q) {r : F → Q} {U S : Set F}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U) (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ C : ℝ≥0, ∀ x ∈ S, ∀ v : F,
      Real.sqrt (g.inner (r x) (mfderiv 𝓘(ℝ, F) I r x v) (mfderiv 𝓘(ℝ, F) I r x v)) ≤
        C * ‖v‖ := by
  let A : F × F → ℝ := fun p => Real.sqrt (g.inner (r p.1)
    (mfderiv 𝓘(ℝ, F) I r p.1 p.2) (mfderiv 𝓘(ℝ, F) I r p.1 p.2))
  have hcont : Continuous (fun z : TangentBundle I Q =>
      Real.sqrt (g.inner z.proj z.2 z.2)) := continuous_tangentMetricSpeed (I := I) g
  have hsrc : ContinuousOn (fun p : F × F =>
      (TotalSpace.mk' E (r p.1) (mfderiv 𝓘(ℝ, F) I r p.1 p.2) : TangentBundle I Q))
      (U ×ˢ univ) := DifferentialGeometry.Geometry.continuousOn_source_tangentMap hU hr
  have hc : ContinuousOn A (S ×ˢ Metric.closedBall (0 : F) 1) :=
    ((hcont.comp_continuousOn hsrc).mono (fun p hp => ⟨hSU hp.1, mem_univ _⟩)).congr
      (fun p _ => rfl)
  obtain ⟨B, hB⟩ :=
    ((hS.prod (isCompact_closedBall (0 : F) 1)).image_of_continuousOn hc).isBounded.exists_norm_le
  let C : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hC (x : F) (hx : x ∈ S) (v : F) (hv : ‖v‖ ≤ 1) : A (x, v) ≤ C := by
    have h := hB (A (x, v)) (mem_image_of_mem A
      (show (x, v) ∈ S ×ˢ Metric.closedBall (0 : F) 1 from
        ⟨hx, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv⟩))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  refine ⟨C, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · subst hv
    have h0 : mfderiv 𝓘(ℝ, F) I r x (0 : F) = 0 := map_zero _
    have h00 : g.inner (r x) (0 : TangentSpace I (r x)) 0 = 0 := by simp
    rw [h0, h00]
    simp
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : F := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvn, inv_mul_cancel₀ hvn.ne']
  have hnorm : v = ‖v‖ • w := by simp [w, smul_smul, hvn.ne']
  calc
    Real.sqrt (g.inner (r x) (mfderiv 𝓘(ℝ, F) I r x v) (mfderiv 𝓘(ℝ, F) I r x v))
        = ‖v‖ * A (x, w) := by
      conv_lhs => rw [hnorm]
      rw [show mfderiv 𝓘(ℝ, F) I r x (‖v‖ • w) =
        ‖v‖ • mfderiv 𝓘(ℝ, F) I r x w from map_smul _ _ _,
        sqrt_metric_smul_tangent, abs_of_pos hvn]
    _ ≤ ‖v‖ * C := mul_le_mul_of_nonneg_left (hC x hx w hw.le) hvn.le
    _ = C * ‖v‖ := mul_comm _ _

omit t2Q in
private theorem exists_regularized_loop_family {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    {r : EuclideanSpace ℝ (Fin N) → Q} {U : Set (EuclideanSpace ℝ (Fin N))}
    (hU : IsOpen U) (heU : range e.map ⊆ U)
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ r U)
    (hleft : ∀ q, r (e.map q) = q) (Γ : C(K, ContinuousFreeLoop Q))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
      ∃ (S : C(K, RegularLoop I Q))
        (H : ContinuousMap.Homotopy Γ (regularLoopInclusion.comp S)),
        HasContinuousSmoothJets e S ∧
        (∀ k q, Γ k = constantLoops q →
          (S k).toContinuousLoop = constantLoops q ∧ ∀ t, H (t, k) = constantLoops q) ∧
        (∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (H (t, k))) ∧
        (∀ k θ, (S k).toContinuousLoop θ = r (DifferentialGeometry.Topology.averagedLoop φ
          ((⟨e.map, e.smooth.continuous⟩ : C(Q, EuclideanSpace ℝ (Fin N))).comp (Γ k)) θ)) ∧
        (∀ k θ, dist (e.map ((S k).toContinuousLoop θ)) (e.map (Γ k θ)) < ε) := by
  obtain ⟨δ, hδ, hstep⟩ :=
    exists_uniform_retracted_loop_homotopy (I := I) (Q := Q) e hU heU hr hleft Γ hε
  refine ⟨δ, hδ, fun φ hφ => ?_⟩
  obtain ⟨S, H, hs, hj, hclose, hconst, hcontract, hformula, _⟩ := hstep φ hφ
  have hval : Continuous (fun p : K × Surgery.Topology.Circle => e.map (S p.1 p.2)) := by
    have h0 : Continuous (fun p : K × ℝ => e.map (S p.1 (p.2 : Surgery.Topology.Circle))) := by
      simpa only [iteratedDeriv_zero] using hj N e.map e.smooth 0
    exact (IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff.mp h0
  have hder : Continuous (fun p : K × ℝ =>
      deriv (fun t : ℝ => e.map (S p.1 (t : Surgery.Topology.Circle))) p.2) := by
    simpa only [iteratedDeriv_one] using hj N e.map e.smooth 1
  let X : C(K, RegularLoop I Q) :=
    ⟨fun k => ⟨S k, (hs k).of_le (by simp)⟩,
      (continuous_regularLoop_iff (I := I) (Q := Q) e _).mpr ⟨hval, hder⟩⟩
  have hXval (k : K) : (X k).toContinuousLoop = S k := rfl
  let H' : ContinuousMap.Homotopy Γ (regularLoopInclusion.comp X) :=
    { toContinuousMap := H.toContinuousMap
      map_zero_left := fun k => H.map_zero_left k
      map_one_left := fun k => H.map_one_left k }
  refine ⟨X, H', ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun k => ?_, fun j => ?_⟩
    · rw [hXval k]
      exact hs k
    · have hfun : ∀ p : K × ℝ, iteratedDeriv j (fun t : ℝ =>
          e.map (loopLift ((X p.1).toContinuousLoop) t)) p.2 =
        iteratedDeriv j (fun t : ℝ => e.map (S p.1 (t : Surgery.Topology.Circle))) p.2 :=
        fun p => rfl
      exact (hj N e.map e.smooth j).congr hfun
  · intro k q hk
    refine ⟨?_, fun t => hconst k q hk t⟩
    rw [hXval k]
    exact (H.apply_one k).symm.trans (hconst k q hk 1)
  · intro k hk t
    exact hcontract k hk t
  · intro k θ
    rw [hXval k]
    exact hformula k θ
  · intro k θ
    have h := hclose 1 k θ
    rw [H.apply_one] at h
    rwa [hXval k]

theorem rfs_loop_smoothing (g : SmoothRiemannianMetric I Q) {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) :
    ∃ Cq : ℝ≥0, 0 < Cq ∧
      ∀ (K : Type uK) [TopologicalSpace K] [CompactSpace K]
        (Γ : C(K, ContinuousFreeLoop Q)),
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ S : ℝ → C(K, RegularLoop I Q),
          (∀ ε ∈ Ioo (0 : ℝ) ε₀, HasContinuousSmoothJets e (S ε)) ∧
          Filter.Tendsto (fun ε => regularLoopInclusion.comp (S ε))
            (𝓝[>] (0 : ℝ)) (𝓝 Γ) ∧
          (∀ ε ∈ Ioo (0 : ℝ) ε₀,
            ∃ F : ContinuousMap.Homotopy Γ (regularLoopInclusion.comp (S ε)),
              (∀ k q, Γ k = constantLoops q →
                (S ε k).toContinuousLoop = constantLoops q ∧
                ∀ t, F (t, k) = constantLoops q) ∧
              ∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (F (t, k))) ∧
          (∀ Γ₁ : C(K, RegularLoop I Q), regularLoopInclusion.comp Γ₁ = Γ →
            Filter.Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 Γ₁) ∧
            ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∃ F : ContinuousMap.Homotopy Γ₁ (S ε),
              ∀ k q, (Γ₁ k).toContinuousLoop = constantLoops q →
                ∀ t, (F (t, k)).toContinuousLoop = constantLoops q) ∧
          (∀ V : ℝ≥0,
            (∀ k x y, riemannianEDistOf g (Γ k x) (Γ k y) ≤
              (V : ℝ≥0∞) * edist x y) →
            ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ k x y,
              riemannianEDistOf g ((S ε k).toContinuousLoop x) ((S ε k).toContinuousLoop y) ≤
                ((Cq * V : ℝ≥0) : ℝ≥0∞) * edist x y) := by
  classical
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction (I := I)
      (F := EuclideanSpace ℝ (Fin N)) e.smooth e.isClosedEmbedding.isEmbedding
      e.injective_mfderiv
  obtain ⟨Ce, hCe0, hCe⟩ :=
    DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff (I := I) (M := Q)
      (F := EuclideanSpace ℝ (Fin N)) g (e.smooth.of_le (by exact_mod_cast le_top))
  obtain ⟨ρ₀, hρ₀, hρ₀K, hρ₀U⟩ :=
    DifferentialGeometry.Analysis.exists_compact_cthickening_subset
      (isCompact_range e.smooth.continuous) hU heU
  obtain ⟨Cr, hCr⟩ := exists_compact_source_metric_mfderiv_bound (I := I) (Q := Q)
    (F := EuclideanSpace ℝ (Fin N)) g hU (hr.of_le (by simp)) hρ₀K hρ₀U
  refine ⟨Cr * Ce + 1, by positivity, ?_⟩
  intro K _ _ Γ
  let ec : C(Q, EuclideanSpace ℝ (Fin N)) := ⟨e.map, e.smooth.continuous⟩
  let A : C(K, ContinuousFreeLoop (EuclideanSpace ℝ (Fin N))) :=
    (DifferentialGeometry.Topology.FreeLoop.postcompose ec).comp Γ
  obtain ⟨δc, hδc, hδcA⟩ :=
    DifferentialGeometry.Topology.smoothPeriodic_uniform_approximation A.uncurry.continuous
      (show (0 : ℝ) < ρ₀ / 2 by positivity)
  obtain ⟨η₀, hη₀, hnear⟩ := exists_regular_nearby_homotopy_radius (I := I) (Q := Q) e
  have hpack : ∀ p : ℝ, 0 < p → ∃ δ : ℝ, 0 < δ ∧
      ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
        ∃ (S : C(K, RegularLoop I Q))
          (H : ContinuousMap.Homotopy Γ (regularLoopInclusion.comp S)),
          HasContinuousSmoothJets e S ∧
          (∀ k q, Γ k = constantLoops q →
            (S k).toContinuousLoop = constantLoops q ∧ ∀ t, H (t, k) = constantLoops q) ∧
          (∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (H (t, k))) ∧
          (∀ k θ, (S k).toContinuousLoop θ = r (DifferentialGeometry.Topology.averagedLoop φ
            (ec.comp (Γ k)) θ)) ∧
          (∀ k θ, dist (e.map ((S k).toContinuousLoop θ)) (e.map (Γ k θ)) < p) :=
    fun p hp => exists_regularized_loop_family (I := I) (Q := Q) e hU heU hr hleft Γ hp
  let pfun : ℝ → ℝ := fun ε => min ε (η₀ / 2)
  have hpfun : ∀ ε, 0 < ε → 0 < pfun ε := fun ε hε => lt_min hε (by positivity)
  let δret : ℝ → ℝ := fun ε =>
    if h : 0 < pfun ε then Classical.choose (hpack (pfun ε) h) else 1
  have hδret_def : ∀ ε (h : 0 < pfun ε), δret ε = Classical.choose (hpack (pfun ε) h) := by
    intro ε h
    dsimp only [δret]
    rw [dite_eq_left h]
  have hδret : ∀ ε (h : 0 < pfun ε), 0 < δret ε := by
    intro ε h
    rw [hδret_def ε h]
    exact (Classical.choose_spec (hpack (pfun ε) h)).1
  have hspec : ∀ ε (h : 0 < pfun ε) (φ : ContDiffBump (0 : ℝ)), φ.rOut < δret ε →
      (∃ (S : C(K, RegularLoop I Q))
        (H : ContinuousMap.Homotopy Γ (regularLoopInclusion.comp S)),
        HasContinuousSmoothJets e S ∧
        (∀ k q, Γ k = constantLoops q →
          (S k).toContinuousLoop = constantLoops q ∧ ∀ t, H (t, k) = constantLoops q) ∧
        (∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (H (t, k))) ∧
        (∀ k θ, (S k).toContinuousLoop θ = r (DifferentialGeometry.Topology.averagedLoop φ
          (ec.comp (Γ k)) θ)) ∧
        (∀ k θ, dist (e.map ((S k).toContinuousLoop θ)) (e.map (Γ k θ)) < pfun ε)) := by
    intro ε h φ hφ
    rw [hδret_def ε h] at hφ
    exact (Classical.choose_spec (hpack (pfun ε) h)).2 φ hφ
  let rad : ℝ → ℝ := fun ε =>
    if 0 < ε then min (min (δret ε) δc) (ε / 4) / 2 else min 1 δc / 2
  have hrad_def_pos : ∀ ε, 0 < ε → rad ε = min (min (δret ε) δc) (ε / 4) / 2 := by
    intro ε hε
    dsimp only [rad]
    rw [ite_eq_left hε]
  have hrad_def_neg : ∀ ε, ¬ 0 < ε → rad ε = min 1 δc / 2 := by
    intro ε hε
    dsimp only [rad]
    rw [ite_eq_right hε]
  have hradpos : ∀ ε, 0 < rad ε := by
    intro ε
    by_cases hε : 0 < ε
    · rw [hrad_def_pos ε hε]
      exact half_pos (lt_min (lt_min (hδret ε (hpfun ε hε)) hδc) (by positivity))
    · rw [hrad_def_neg ε hε]
      exact half_pos (lt_min zero_lt_one hδc)
  let φb : ℝ → ContDiffBump (0 : ℝ) :=
    fun ε => ⟨rad ε / 2, rad ε, half_pos (hradpos ε), by linarith [hradpos ε]⟩
  have hφr : ∀ ε, (φb ε).rOut = rad ε := fun _ => rfl
  have hrad_lt_ret : ∀ ε, 0 < ε → rad ε < δret ε := by
    intro ε hε
    rw [hrad_def_pos ε hε]
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ (by norm_num))
      (half_lt_self (hδret ε (hpfun ε hε)))
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hrad_lt_c : ∀ ε, rad ε < δc := by
    intro ε
    by_cases hε : 0 < ε
    · rw [hrad_def_pos ε hε]
      refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ (by norm_num)) (half_lt_self hδc)
      exact (min_le_left _ _).trans (min_le_right _ _)
    · rw [hrad_def_neg ε hε]
      refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ (by norm_num)) (half_lt_self hδc)
      exact min_le_right _ _
  have hrad_le : ∀ ε, 0 < ε → rad ε ≤ ε / 8 := by
    intro ε hε
    rw [hrad_def_pos ε hε]
    have h2 : min (min (δret ε) δc) (ε / 4) / 2 ≤ (ε / 4) / 2 :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  have hstep : ∀ ε : ℝ, ∃ S : C(K, RegularLoop I Q), 0 < ε →
      ∃ H : ContinuousMap.Homotopy Γ (regularLoopInclusion.comp S),
        HasContinuousSmoothJets e S ∧
        (∀ k q, Γ k = constantLoops q →
          (S k).toContinuousLoop = constantLoops q ∧ ∀ t, H (t, k) = constantLoops q) ∧
        (∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (H (t, k))) ∧
        (∀ k θ, (S k).toContinuousLoop θ = r (DifferentialGeometry.Topology.averagedLoop (φb ε)
          (ec.comp (Γ k)) θ)) ∧
        (∀ k θ, dist (e.map ((S k).toContinuousLoop θ)) (e.map (Γ k θ)) < pfun ε) := by
    intro ε
    by_cases hε : 0 < ε
    · have hlt : (φb ε).rOut < δret ε := by
        rw [hφr]
        exact hrad_lt_ret ε hε
      exact ⟨Classical.choose (hspec ε (hpfun ε hε) (φb ε) hlt),
        fun _ => Classical.choose_spec (hspec ε (hpfun ε hε) (φb ε) hlt)⟩
    · exact ⟨ContinuousMap.const K
          ⟨constantLoops (Classical.choice (inferInstance : Nonempty Q)), contMDiff_const⟩,
        fun h => absurd h hε⟩
  let S : ℝ → C(K, RegularLoop I Q) := fun ε => Classical.choose (hstep ε)
  have hS : ∀ ε (hε : 0 < ε), ∃ H : ContinuousMap.Homotopy Γ (regularLoopInclusion.comp (S ε)),
      HasContinuousSmoothJets e (S ε) ∧
      (∀ k q, Γ k = constantLoops q →
        (S ε k).toContinuousLoop = constantLoops q ∧ ∀ t, H (t, k) = constantLoops q) ∧
      (∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (H (t, k))) ∧
      (∀ k θ, (S ε k).toContinuousLoop θ = r (DifferentialGeometry.Topology.averagedLoop (φb ε)
        (ec.comp (Γ k)) θ)) ∧
      (∀ k θ, dist (e.map ((S ε k).toContinuousLoop θ)) (e.map (Γ k θ)) < pfun ε) :=
    fun ε hε => Classical.choose_spec (hstep ε) hε
  have hSjets : ∀ ε (hε : 0 < ε), HasContinuousSmoothJets e (S ε) := by
    intro ε hε
    obtain ⟨-, hA, -⟩ := hS ε hε
    exact hA
  have hShom : ∀ ε (hε : 0 < ε),
      ∃ H : ContinuousMap.Homotopy Γ (regularLoopInclusion.comp (S ε)),
        (∀ k q, Γ k = constantLoops q →
          (S ε k).toContinuousLoop = constantLoops q ∧ ∀ t, H (t, k) = constantLoops q) ∧
        (∀ k, IsContractibleLoop (Γ k) → ∀ t, IsContractibleLoop (H (t, k))) := by
    intro ε hε
    obtain ⟨H, -, hB, hC, -, -⟩ := hS ε hε
    exact ⟨H, hB, hC⟩
  have hSform : ∀ ε (hε : 0 < ε) (k : K) (θ : Surgery.Topology.Circle),
      (S ε k).toContinuousLoop θ = r (DifferentialGeometry.Topology.averagedLoop (φb ε)
        (ec.comp (Γ k)) θ) := by
    intro ε hε k θ
    obtain ⟨-, -, -, -, hD, -⟩ := hS ε hε
    exact hD k θ
  have hSclose : ∀ ε (hε : 0 < ε) (k : K) (θ : Surgery.Topology.Circle),
      dist (e.map ((S ε k).toContinuousLoop θ)) (e.map (Γ k θ)) < pfun ε := by
    intro ε hε k θ
    obtain ⟨-, -, -, -, -, hE⟩ := hS ε hε
    exact hE k θ
  refine ⟨1, one_pos, S, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    exact hSjets ε hε.1
  · have hemb : IsEmbedding (fun γ : ContinuousFreeLoop Q => ec.comp γ) :=
      ContinuousMap.isEmbedding_postcomp ec e.isClosedEmbedding.isEmbedding
    have hembK : IsEmbedding ((⟨fun γ : ContinuousFreeLoop Q => ec.comp γ,
        ContinuousMap.continuous_postcomp ec⟩ : C(ContinuousFreeLoop Q,
          ContinuousFreeLoop (EuclideanSpace ℝ (Fin N)))).comp :
        C(K, ContinuousFreeLoop Q) → C(K, ContinuousFreeLoop (EuclideanSpace ℝ (Fin N)))) :=
      ContinuousMap.isEmbedding_postcomp _ hemb
    rw [hembK.1.nhds_eq_comap Γ, Filter.tendsto_comap_iff]
    rw [ContinuousMap.tendsto_iff_tendstoUniformly, EMetric.tendstoUniformly_iff]
    intro η hη
    obtain ⟨η', hη'0, hη'lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hη
    have hη'p : (0 : ℝ) < η' := by exact_mod_cast hη'0
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) (η' : ℝ) := Ioo_mem_nhdsGT hη'p
    filter_upwards [hev] with ε hε k
    rw [edist_dist]
    refine lt_of_lt_of_le ?_ hη'lt.le
    rw [ENNReal.coe_nnreal_eq, ENNReal.ofReal_lt_ofReal_iff hη'p]
    refine (ContinuousMap.dist_lt_iff hη'p).mpr fun θ => ?_
    have hcl : dist (e.map (Γ k θ)) (e.map ((S ε k).toContinuousLoop θ)) < η' := by
      rw [dist_comm (e.map (Γ k θ)) (e.map ((S ε k).toContinuousLoop θ))]
      exact (hSclose ε hε.1 k θ).trans ((min_le_left _ _).trans_lt hε.2)
    exact hcl
  · intro ε hε
    exact hShom ε hε.1
  · intro Γ₁ hΓ₁
    have hΓk : ∀ k, Γ k = (Γ₁ k).toContinuousLoop := by
      intro k
      have h := congrArg (fun f : C(K, ContinuousFreeLoop Q) => f k) hΓ₁
      simpa only [ContinuousMap.comp_apply, regularLoopInclusion, ContinuousMap.coe_mk] using h.symm
    constructor
    · have hembJ : IsEmbedding (embeddingFirstJet (I := I) (Q := Q) e) :=
        ⟨⟨regularLoop_topology_eq_embedding (I := I) (Q := Q) e⟩, fun γ δ h => by
          apply RegularLoop.toContinuousLoop_injective
          apply ContinuousMap.ext
          intro θ
          let a := AddCircle.equivIco (1 : ℝ) 0 θ
          have ha : a.1 ∈ Icc (0 : ℝ) 1 := ⟨a.2.1, by linarith [a.2.2]⟩
          have hval : e.map (loopLift γ.toContinuousLoop a.1) =
              e.map (loopLift δ.toContinuousLoop a.1) :=
            congrArg (fun f : C(Icc (0 : ℝ) 1,
              EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) => (f ⟨a.1, ha⟩).1) h
          rw [loopLift, loopLift, AddCircle.coe_equivIco] at hval
          exact e.isClosedEmbedding.isEmbedding.injective hval⟩
      have hembK2 : IsEmbedding ((⟨embeddingFirstJet (I := I) (Q := Q) e,
          continuous_embeddingFirstJet (I := I) (Q := Q) e⟩ :
          C(RegularLoop I Q, C(Icc (0 : ℝ) 1,
            EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)))).comp :
        C(K, RegularLoop I Q) → C(K, C(Icc (0 : ℝ) 1,
          EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)))) :=
        ContinuousMap.isEmbedding_postcomp _ hembJ
      rw [hembK2.1.nhds_eq_comap Γ₁, Filter.tendsto_comap_iff]
      rw [ContinuousMap.tendsto_iff_tendstoUniformly, EMetric.tendstoUniformly_iff]
      intro η hη
      obtain ⟨η', hη'0, hη'lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hη
      have hη'p : (0 : ℝ) < η' := by exact_mod_cast hη'0
      obtain ⟨hAc, hAd⟩ := (continuous_regularLoop_iff (I := I) (Q := Q) e Γ₁).mp Γ₁.continuous
      have hAeq : ∀ k, A k = ec.comp ((Γ₁ k).toContinuousLoop) := by
        intro k
        apply ContinuousMap.ext
        intro θ
        simp only [A, ec, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
          DifferentialGeometry.Topology.FreeLoop.postcompose_apply, hΓk k]
      have hA1 : ∀ k, ContDiff ℝ 1 (fun t : ℝ => A k (t : Surgery.Topology.Circle)) := by
        intro k
        rw [hAeq k]
        exact RegularLoop.embedded_contDiff (I := I) (Q := Q) e (Γ₁ k)
      have hAd2 : Continuous (fun p : K × ℝ =>
          deriv (fun t : ℝ => A p.1 (t : Surgery.Topology.Circle)) p.2) := by
        refine hAd.congr fun p => ?_
        rw [hAeq p.1]
        rfl
      have hmapU : ∀ k θ, A k θ ∈ U := by
        intro k θ
        rw [hAeq k]
        exact heU (mem_range_self ((Γ₁ k).toContinuousLoop θ))
      have hR : ContDiffOn ℝ 1 (fun z : EuclideanSpace ℝ (Fin N) => e.map (r z)) U :=
        ((e.smooth.of_le (by simp)).comp_contMDiffOn (hr.of_le (by simp))).contDiffOn
      obtain ⟨δ1, hδ1, hδ1A⟩ :=
        DifferentialGeometry.Topology.smoothPeriodic_uniform_C1_superposition A hA1 hAd2
          hU hR hmapU hη'p
      have hmin : 0 < min (η' : ℝ) (8 * δ1) := lt_min hη'p (by linarith)
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) (min (η' : ℝ) (8 * δ1)) :=
        Ioo_mem_nhdsGT hmin
      filter_upwards [hev] with ε hε k
      rw [edist_dist]
      refine lt_of_lt_of_le ?_ hη'lt.le
      rw [ENNReal.coe_nnreal_eq, ENNReal.ofReal_lt_ofReal_iff hη'p]
      refine (ContinuousMap.dist_lt_iff hη'p).mpr fun t => ?_
      have hεδ : ε < 8 * δ1 := hε.2.trans_le (min_le_right _ _)
      have hlt : (φb ε).rOut < δ1 := by
        rw [hφr]
        exact lt_of_le_of_lt (hrad_le ε hε.1) (by linarith [hεδ])
      obtain ⟨-, hval1, hder1⟩ := hδ1A (φb ε) hlt k t.1
      have hsv : ∀ s : ℝ, (S ε k).toContinuousLoop (s : Surgery.Topology.Circle) =
          r (DifferentialGeometry.Analysis.smoothPeriodic (φb ε)
            (fun u : ℝ => A k (u : Surgery.Topology.Circle)) s) := by
        intro s
        rw [hSform ε hε.1 k (s : Surgery.Topology.Circle),
          DifferentialGeometry.Topology.averagedLoop_coe]
        rfl
      have htv : ∀ s : ℝ, (Γ₁ k).toContinuousLoop (s : Surgery.Topology.Circle) =
          r (A k (s : Surgery.Topology.Circle)) := by
        intro s
        have hA : A k (s : Surgery.Topology.Circle) =
            e.map ((Γ₁ k).toContinuousLoop (s : Surgery.Topology.Circle)) := by
          simp only [A, ec, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
            DifferentialGeometry.Topology.FreeLoop.postcompose_apply, hΓk k]
        rw [hA, hleft]
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · simp only [Function.comp_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
          embeddingFirstJet, loopLift]
        rw [hsv t.1, htv t.1]
        exact dist_comm (e.map (r (DifferentialGeometry.Analysis.smoothPeriodic (φb ε)
            (fun u : ℝ => A k (u : Surgery.Topology.Circle)) t.1)))
          (e.map (r (A k (t.1 : Surgery.Topology.Circle)))) ▸ hval1
      · simp only [Function.comp_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
          embeddingFirstJet]
        have hfun1 : e.map ∘ loopLift ((S ε k).toContinuousLoop) =
            fun s : ℝ => e.map (r (DifferentialGeometry.Analysis.smoothPeriodic (φb ε)
              (fun u : ℝ => A k (u : Surgery.Topology.Circle)) s)) := by
          funext s
          exact congrArg e.map (hsv s)
        have hfun2 : e.map ∘ loopLift ((Γ₁ k).toContinuousLoop) =
            fun s : ℝ => e.map (r (A k (s : Surgery.Topology.Circle))) := by
          funext s
          exact congrArg e.map (htv s)
        rw [hfun1, hfun2]
        exact dist_comm (deriv (fun x : ℝ => e.map (r (DifferentialGeometry.Analysis.smoothPeriodic
            (φb ε) (fun u : ℝ => A k (u : Surgery.Topology.Circle)) x))) t.1)
          (deriv (fun s : ℝ => e.map (r (A k (s : Surgery.Topology.Circle)))) t.1) ▸ hder1
    · intro ε hε
      have hclose' : ∀ k θ, dist (e.map ((S ε k).toContinuousLoop θ))
          (e.map ((Γ₁ k).toContinuousLoop θ)) < η₀ := by
        intro k θ
        have h := hSclose ε hε.1 k θ
        rw [hΓk k] at h
        exact h.trans_le (lt_of_le_of_lt (min_le_right _ _) (by linarith)).le
      obtain ⟨R, hRc, hR0, hR1, hRconst⟩ := hnear K (fun k => Γ₁ k) (fun k => S ε k)
        Γ₁.continuous (S ε).continuous hclose'
      refine ⟨⟨⟨R, hRc⟩, fun k => hR0 k, fun k => hR1 k⟩, ?_⟩
      intro k q hk t
      have hk' : Γ k = constantLoops q := by rw [hΓk k]; exact hk
      obtain ⟨H, hB, -⟩ := hShom ε hε.1
      have hSconst : (S ε k).toContinuousLoop = constantLoops q := (hB k q hk').1
      have heq : Γ₁ k = S ε k :=
        RegularLoop.toContinuousLoop_injective (by rw [hk, hSconst])
      change (R (t, k)).toContinuousLoop = constantLoops q
      rw [hRconst k heq t]
      exact hk
  · intro V hV ε hε k x y
    have hform : ∀ θ : Surgery.Topology.Circle, (S ε k).toContinuousLoop θ =
        r (DifferentialGeometry.Topology.averagedLoop (φb ε) (ec.comp (Γ k)) θ) :=
      fun θ => hSform ε hε.1 k θ
    have hmem : ∀ s : ℝ, DifferentialGeometry.Topology.averagedLoop (φb ε) (ec.comp (Γ k))
        (s : Surgery.Topology.Circle) ∈ Metric.cthickening ρ₀ (range e.map) := by
      intro s
      have h1 := hδcA (φb ε) (hrad_lt_c ε) k s
      have h2 : dist (DifferentialGeometry.Topology.averagedLoop (φb ε) (ec.comp (Γ k))
            (s : Surgery.Topology.Circle))
          (e.map (Γ k (s : Surgery.Topology.Circle))) < ρ₀ / 2 := by
        rw [DifferentialGeometry.Topology.averagedLoop_coe]
        exact h1
      refine Metric.mem_cthickening_of_dist_le _ (e.map (Γ k (s : Surgery.Topology.Circle)))
        ρ₀ (range e.map) (mem_range_self _) (le_of_lt ?_)
      linarith
    have hLipA : LipschitzWith (Ce * V)
        (fun θ : Surgery.Topology.Circle => e.map (Γ k θ)) := by
      intro x y
      calc edist (e.map (Γ k x)) (e.map (Γ k y))
          ≤ (Ce : ℝ≥0∞) * riemannianEDistOf g (Γ k x) (Γ k y) := hCe _ _
        _ ≤ (Ce : ℝ≥0∞) * ((V : ℝ≥0∞) * edist x y) := by
            gcongr
            exact hV k x y
        _ = ((Ce * V : ℝ≥0) : ℝ≥0∞) * edist x y := by rw [ENNReal.coe_mul, mul_assoc]
    have hLipR : LipschitzWith (Ce * V)
        (fun s : ℝ => e.map (Γ k (s : Surgery.Topology.Circle))) := by
      have h := hLipA.comp (Kf := Ce * V) (Kg := 1)
        DifferentialGeometry.Topology.loopCircle_projection_lipschitz
      simpa only [Function.comp_def, mul_one] using h
    have hLipB : LipschitzWith (Ce * V)
        (fun s : ℝ => DifferentialGeometry.Topology.averagedLoop (φb ε) (ec.comp (Γ k))
          (s : Surgery.Topology.Circle)) := by
      have hsrc : LipschitzWith (Ce * V)
          (fun s : ℝ => (ec.comp (Γ k)) (s : Surgery.Topology.Circle)) := by
        simpa only [ec, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using hLipR
      have h := DifferentialGeometry.Analysis.smoothPeriodic_lipschitz (φb ε) hsrc
      simpa only [DifferentialGeometry.Topology.averagedLoop_coe] using h
    have hspeed : ∀ t ∈ Icc (-1 : ℝ) 2,
        Real.sqrt (g.inner (loopLift ((S ε k).toContinuousLoop) t)
          (loopVelocity (I := I) ((S ε k).toContinuousLoop) t)
          (loopVelocity (I := I) ((S ε k).toContinuousLoop) t)) ≤
        (((Cr * Ce + 1) * V : ℝ≥0) : ℝ) := by
      intro t _
      have htU : DifferentialGeometry.Topology.averagedLoop (φb ε) (ec.comp (Γ k))
          (t : Surgery.Topology.Circle) ∈ U := hρ₀U (hmem t)
      let w : ℝ → EuclideanSpace ℝ (Fin N) := fun s : ℝ =>
        DifferentialGeometry.Topology.averagedLoop (φb ε) (ec.comp (Γ k))
          (s : Surgery.Topology.Circle)
      have hcd : ContDiff ℝ 1 w := by
        have hcont : Continuous (fun s : ℝ => (ec.comp (Γ k)) (s : Surgery.Topology.Circle)) :=
          ((ec.comp (Γ k)).continuous).comp (AddCircle.continuous_mk' (1 : ℝ))
        simpa only [w, DifferentialGeometry.Topology.averagedLoop_coe] using
          (DifferentialGeometry.Analysis.smoothPeriodic_contDiff (φb ε) hcont).of_le
            (by exact_mod_cast le_top)
      have hlift : loopLift ((S ε k).toContinuousLoop) t = r (w t) := hform (t : Surgery.Topology.Circle)
      have hvel : loopVelocity (I := I) ((S ε k).toContinuousLoop) t =
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I r (w t) (deriv w t) := by
        have hfun : loopLift ((S ε k).toContinuousLoop) = fun s : ℝ => r (w s) := by
          funext s
          exact hform (s : Surgery.Topology.Circle)
        rw [loopVelocity, hfun]
        exact congrArg (fun z : TangentBundle I Q => z.2)
          (DifferentialGeometry.Geometry.tangent_velocity_comp (I := I) (r := r) (v := w)
            (t := t) (((hr _ htU).contMDiffAt (hU.mem_nhds htU)).mdifferentiableAt (by simp))
            (hcd.differentiable one_ne_zero t))
      rw [hvel, hlift]
      calc Real.sqrt (g.inner (r (w t))
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I r (w t) (deriv w t))
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I r (w t) (deriv w t)))
          ≤ (Cr : ℝ) * ‖deriv w t‖ :=
            hCr _ (hmem t) _
        _ ≤ (Cr : ℝ) * (((Ce * V : ℝ≥0)) : ℝ) :=
            mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hLipB) (by positivity)
        _ ≤ (((Cr * Ce + 1) * V : ℝ≥0) : ℝ) := by
            have h1 : (Cr : ℝ) * (Ce : ℝ) ≤ ((Cr * Ce + 1 : ℝ≥0) : ℝ) := by
              rw [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
              linarith
            calc (Cr : ℝ) * (((Ce * V : ℝ≥0)) : ℝ)
                = ((Cr : ℝ) * (Ce : ℝ)) * (V : ℝ) := by
                  rw [NNReal.coe_mul]
                  ring
              _ ≤ (((Cr * Ce + 1 : ℝ≥0)) : ℝ) * (V : ℝ) :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
              _ = (((Cr * Ce + 1) * V : ℝ≥0) : ℝ) := by rw [NNReal.coe_mul]
    exact regularLoop_lipschitz_of_speed_bound g (S ε k) (by positivity) hspeed x y


theorem rfs_regular_class_correspondence :
    Function.Bijective
      (FreeHomotopyClass.map (X := Sphere 2)
        (contractibleRegularLoopInclusion (I := I) (Q := Q))) := by
  obtain ⟨N, ⟨e⟩⟩ := smoothLoopEmbedding_exists (I := I) (Q := Q)
  constructor
  · intro ξ ζ
    induction ξ using Quotient.inductionOn with
    | h Γ =>
      induction ζ using Quotient.inductionOn with
      | h Δ =>
        intro h
        have hc : (contractibleRegularLoopInclusion.comp Γ).Homotopic
            (contractibleRegularLoopInclusion.comp Δ) := Quotient.exact h
        have hr := regular_contractible_homotopicRel_of_continuous (K := Sphere 2) e Γ Δ ∅
          (fun k hk => (Set.notMem_empty k hk).elim)
          (ContinuousMap.homotopicRel_empty.mpr hc)
        exact (FreeHomotopyClass.mk_eq_mk_iff _ _).mpr
          (ContinuousMap.homotopicRel_empty.mp hr)
  · intro ξ
    obtain ⟨Γ, rfl⟩ := Quotient.exists_rep ξ
    obtain ⟨S, H, _, _⟩ := exists_regular_contractible_representative (K := Sphere 2) e Γ
    refine ⟨FreeHomotopyClass.mk S, ?_⟩
    rw [FreeHomotopyClass.map_mk]
    exact (FreeHomotopyClass.mk_eq_mk_iff _ _).mpr ⟨H.symm⟩


theorem regularRepresentative_nonempty (ξ : FreeContractibleSphereClass Q) :
    Nonempty (RegularRepresentative (I := I) ξ) := by
  obtain ⟨ξ₁, hξ₁⟩ := (rfs_regular_class_correspondence (I := I) (Q := Q)).surjective ξ
  obtain ⟨Γ, rfl⟩ := Quotient.exists_rep ξ₁
  exact ⟨Γ, hξ₁⟩

theorem regular_based_pi2_correspondence (q : Q) :
    ∃ e : HomotopyGroup (Fin 2) (ContractibleRegularLoop (I := I) (Q := Q))
        (constantContractibleRegularLoop q) ≃*
      HomotopyGroup (Fin 2) (ContractibleContinuousLoop Q)
        (contractibleRegularLoopInclusion (constantContractibleRegularLoop (I := I) q)),
      ∀ u : GenLoop (Fin 2) (ContractibleRegularLoop (I := I) (Q := Q))
          (constantContractibleRegularLoop q),
        e (Quotient.mk _ u) = Quotient.mk _ (regularGenLoopInclusion q u) := by
  obtain ⟨N, ⟨e⟩⟩ := smoothLoopEmbedding_exists (I := I) (Q := Q)
  let inc : C(ContractibleRegularLoop (I := I) (Q := Q), ContractibleContinuousLoop Q) :=
    contractibleRegularLoopInclusion
  have hbij : Function.Bijective
      (DifferentialGeometry.Topology.homotopyGroupMap (N := Fin 2) inc
        (constantContractibleRegularLoop q)) := by
    constructor
    · intro a b
      induction a using Quotient.inductionOn with
      | h p =>
        induction b using Quotient.inductionOn with
        | h r =>
          intro h
          have hc : (inc.comp p.1).HomotopicRel (inc.comp r.1) (Cube.boundary (Fin 2)) :=
            Quotient.exact h
          apply Quotient.sound
          exact regular_contractible_homotopicRel_of_continuous (K := Fin 2 → unitInterval) e
            p.1 r.1 (Cube.boundary (Fin 2)) (fun k hk => ⟨q, GenLoop.boundary p k hk⟩) hc
    · intro a
      induction a using Quotient.inductionOn with
      | h p =>
        obtain ⟨S, H, _, hfix⟩ := exists_regular_contractible_representative e p.1
        have hSb (k : Fin 2 → unitInterval) (hk : k ∈ Cube.boundary (Fin 2)) :
            S k = constantContractibleRegularLoop q := by
          have h := hfix k q (GenLoop.boundary p k hk) 1
          rw [H.apply_one] at h
          apply Subtype.ext
          apply RegularLoop.toContinuousLoop_injective
          exact congrArg Subtype.val h
        let r : GenLoop (Fin 2) (ContractibleRegularLoop (I := I) (Q := Q))
            (constantContractibleRegularLoop q) := ⟨S, hSb⟩
        let Hr : p.1.HomotopyRel (inc.comp S) (Cube.boundary (Fin 2)) :=
          ⟨H, fun t k hk => (hfix k q (GenLoop.boundary p k hk) t).trans
            (GenLoop.boundary p k hk).symm⟩
        refine ⟨Quotient.mk _ r, Quotient.sound ?_⟩
        exact ⟨Hr.symm⟩
  refine ⟨MulEquiv.ofBijective
    (DifferentialGeometry.Topology.homotopyGroupMapHom (N := Fin 2) inc
      (constantContractibleRegularLoop q)) hbij, ?_⟩
  intro u
  rfl

section TargetMaps

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P] [IsManifold J ∞ P]


def RegularLoop.postcompose (f : C(Q, P)) (hf : ContMDiff I J ∞ f)
    (γ : RegularLoop I Q) : RegularLoop J P :=
  ⟨f.comp γ.toContinuousLoop, (hf.of_le (by simp)).comp γ.contMDiff_lift⟩

omit finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem continuous_regularLoop_postcompose
    (f : C(Q, P)) (hf : ContMDiff I J ∞ f) :
    Continuous (RegularLoop.postcompose f hf) := by
  let T : C(TangentBundle I Q, TangentBundle J P) :=
    ⟨tangentMap I J f, hf.continuous_tangentMap (by simp)⟩
  have hjet (γ : RegularLoop I Q) :
      (γ.postcompose f hf).firstJetMap = T.comp γ.firstJetMap := by
    apply ContinuousMap.ext
    intro t
    change tangentMap 𝓘(ℝ, ℝ) J (f ∘ loopLift γ.toContinuousLoop)
      (⟨(t : ℝ), (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) =
      tangentMap I J f (tangentMap 𝓘(ℝ, ℝ) I (loopLift γ.toContinuousLoop)
        (⟨(t : ℝ), (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
    exact tangentMap_comp_at _ (hf.mdifferentiable (by simp) _)
      (γ.contMDiff_lift.mdifferentiable one_ne_zero _)
  have hv : Continuous (fun γ : RegularLoop I Q => f.comp γ.toContinuousLoop) :=
    (ContinuousMap.continuous_postcomp f).comp
      (continuous_fst.comp RegularLoop.continuous_value_jet)
  have ht : Continuous (fun γ : RegularLoop I Q => T.comp γ.firstJetMap) :=
    (ContinuousMap.continuous_postcomp T).comp
      (continuous_snd.comp RegularLoop.continuous_value_jet)
  apply continuous_induced_rng.mpr
  change Continuous (fun γ : RegularLoop I Q =>
    ((γ.postcompose f hf).toContinuousLoop, (γ.postcompose f hf).firstJetMap))
  exact hv.prodMk (ht.congr fun γ => (hjet γ).symm)

end TargetMaps

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
