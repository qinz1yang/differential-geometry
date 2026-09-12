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


private theorem exists_short_circle_lifts (x y : Surgery.Topology.Circle) :
    ∃ a d : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ -(1 / 2 : ℝ) ≤ d ∧ d ≤ 1 / 2 ∧
      (a : Surgery.Topology.Circle) = y ∧ ((a + d : ℝ) : Surgery.Topology.Circle) = x ∧
      dist x y = |d| := by
  let a := AddCircle.equivIco (1 : ℝ) 0 y
  let d := AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (x - y)
  have ha : 0 ≤ a.1 ∧ a.1 < 1 := by simpa using a.2
  have hd : -(1 / 2 : ℝ) ≤ d.1 ∧ d.1 < 1 / 2 := by convert! d.2 using 1; norm_num
  have haq : (a.1 : Surgery.Topology.Circle) = y := AddCircle.coe_equivIco
  have hdq : (d.1 : Surgery.Topology.Circle) = x - y := AddCircle.coe_equivIco
  have hadq : ((a.1 + d.1 : ℝ) : Surgery.Topology.Circle) = x := by
    rw [AddCircle.coe_add, haq, hdq]
    abel
  have hdabs : |d.1| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one, abs_le]
    exact ⟨hd.1, hd.2.le⟩
  have hnorm : ‖(d.1 : Surgery.Topology.Circle)‖ = |d.1| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hdabs
  refine ⟨a.1, d.1, ha.1, ha.2.le, hd.1, hd.2.le, haq, hadq, ?_⟩
  rw [dist_eq_norm, ← hdq]
  exact hnorm

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
  obtain ⟨a, d, ha0, ha1, hd0, hd1, hay, hadx, hdist⟩ := exists_short_circle_lifts x y
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
  sorry


theorem rfs_regular_class_correspondence :
    Function.Bijective
      (FreeHomotopyClass.map (X := Sphere 2)
        (contractibleRegularLoopInclusion (I := I) (Q := Q))) := by
  sorry


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
  sorry

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
