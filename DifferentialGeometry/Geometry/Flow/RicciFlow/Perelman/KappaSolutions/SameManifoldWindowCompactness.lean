import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.FlowLayerAncientLimit
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.RicciFromJets
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem exhaustsByOpen_univ (M : Type u) [TopologicalSpace M] :
    ExhaustsByOpen (fun _ : Nat => (Set.univ : Set M)) where
  isOpen _ := isOpen_univ
  mono_step _ := Set.subset_univ _
  subset K _ := ⟨0, fun _ _ => Set.subset_univ K⟩

theorem ExhaustsByOpen.iUnion_eq_univ {M : Type u} [TopologicalSpace M]
    {U : Nat -> Set M} (hU : ExhaustsByOpen U) :
    (⋃ k : Nat, U k) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨k, hk⟩ := hU.subset {x} isCompact_singleton
  exact Set.mem_iUnion.mpr ⟨k, hk k le_rfl (Set.mem_singleton x)⟩

theorem ExhaustsByOpen.exists_not_subset {M : Type u} [TopologicalSpace M]
    {U : Nat -> Set M} (hU : ExhaustsByOpen U)
    {S : Set M} (hS : S ≠ Set.univ) : exists k : Nat, ¬ U k ⊆ S := by
  by_contra hcon
  have hsub : Set.univ ⊆ S := by
    rw [← hU.iUnion_eq_univ]
    exact Set.iUnion_subset fun k => not_not.mp (not_exists.mp hcon k)
  exact hS (Set.eq_univ_of_univ_subset hsub)

noncomputable def PointedCGHMaps.ofDiffeomorphFamily
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (phi : forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      Diffeomorph I I P.M (X.term (subseq k)).M (∞ : WithTop ℕ∞))
    (hbase : forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      phi k P.basepoint = (X.term (subseq k)).basepoint) :
    PointedCGHMaps (I := I) X P subseq := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  let psi : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      PartialDiffeomorph I I P.M (X.term (subseq k)).M (∞ : WithTop ℕ∞) :=
    fun k => by
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      exact (phi k).toPartialDiffeomorph
  refine ⟨psi, ?_, ?_, ?_⟩
  · have hsrc : (fun k : Nat => (psi k).source) = fun _ : Nat => (Set.univ : Set P.M) := by
      funext k
      simp [psi, Diffeomorph.toPartialDiffeomorph]
    rw [hsrc]
    exact exhaustsByOpen_univ P.M
  · intro k
    have h : (psi k).source = (Set.univ : Set P.M) := by
      simp [psi, Diffeomorph.toPartialDiffeomorph]
    rw [h]
    exact Set.mem_univ _
  · intro k
    change (phi k) P.basepoint = (X.term (subseq k)).basepoint
    exact hbase k

@[simp] theorem PointedCGHMaps.ofDiffeomorphFamily_map
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (phi : forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      Diffeomorph I I P.M (X.term (subseq k)).M (∞ : WithTop ℕ∞))
    (hbase : forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      phi k P.basepoint = (X.term (subseq k)).basepoint)
    (k : Nat) (x : P.M) :
    (PointedCGHMaps.ofDiffeomorphFamily (I := I) phi hbase).map k x = phi k x :=
  rfl

end CheegerGromovCompactness
end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]

noncomputable def SameManifoldFlowSeq.windowPointedManifold
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (p : M) (g : SmoothRiemannianMetric I M) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) :=
  letI : T2Space (TangentBundle I M) := Y.t2TangentBundle
  { M := M, basepoint := p, metric := g }

theorem SameManifoldFlowSeq.nonempty_pointedCGHMaps_windowSeq_of_diffeomorphFamily
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop) (m : Nat)
    (p : M) (g : SmoothRiemannianMetric I M) (subseq : Nat -> Nat)
    (phi : Nat -> Diffeomorph I I M M (∞ : WithTop ℕ∞))
    (hbase : forall k : Nat,
      phi k p = (Y.toFiniteArcFlowSeq.windowSeq hT m).basepoint (subseq k)) :
    Nonempty (PointedCGHMaps (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m)
      (Y.windowPointedManifold p g) subseq) :=
  ⟨PointedCGHMaps.ofDiffeomorphFamily (I := I)
    (X := Y.toFiniteArcFlowSeq.windowSeq hT m) (fun k => phi k) hbase⟩

theorem SameManifoldFlowSeq.nonempty_pointedCGHMaps_windowSeq_of_basepoint_eq
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop) (m : Nat)
    (p : M) (g : SmoothRiemannianMetric I M) (subseq : Nat -> Nat)
    (hbase : forall k : Nat,
      (Y.toFiniteArcFlowSeq.windowSeq hT m).basepoint (subseq k) = p) :
    Nonempty (PointedCGHMaps (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m)
      (Y.windowPointedManifold p g) subseq) := by
  refine SameManifoldFlowSeq.nonempty_pointedCGHMaps_windowSeq_of_diffeomorphFamily
    (I := I) Y hT m p g subseq
    (fun _ => Diffeomorph.refl I M (∞ : WithTop ℕ∞)) ?_
  intro k
  rw [Diffeomorph.coe_refl]
  exact (hbase k).symm

theorem SameManifoldFlowSeq.basepoint_eq_map_basepoint
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop) (m : Nat)
    (p : M) (g : SmoothRiemannianMetric I M) {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m)
      (Y.windowPointedManifold p g) subseq) (k : Nat) :
    (Y.toFiniteArcFlowSeq.windowSeq hT m).basepoint (subseq k) = Phi.map k p :=
  (Phi.basepoint_map k).symm

theorem SameManifoldFlowSeq.basepoint_eq_of_map_basepoint_fixing
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop) (m : Nat)
    (p : M) (g : SmoothRiemannianMetric I M) {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m)
      (Y.windowPointedManifold p g) subseq)
    (hfix : forall k : Nat, Phi.map k p = p) (k : Nat) :
    (Y.toFiniteArcFlowSeq.windowSeq hT m).basepoint (subseq k) = p :=
  (SameManifoldFlowSeq.basepoint_eq_map_basepoint (I := I) Y hT m p g Phi k).trans (hfix k)

theorem SameManifoldFlowSeq.basepoints_eq_of_map_basepoint_fixing
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop) (m : Nat)
    (p : M) (g : SmoothRiemannianMetric I M) {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m)
      (Y.windowPointedManifold p g) subseq)
    (hfix : forall k : Nat, Phi.map k p = p) (k l : Nat) :
    (Y.toFiniteArcFlowSeq.windowSeq hT m).basepoint (subseq k) =
      (Y.toFiniteArcFlowSeq.windowSeq hT m).basepoint (subseq l) :=
  (SameManifoldFlowSeq.basepoint_eq_of_map_basepoint_fixing (I := I) Y hT m p g Phi hfix k).trans
    (SameManifoldFlowSeq.basepoint_eq_of_map_basepoint_fixing (I := I) Y hT m p g Phi hfix l).symm

theorem SameManifoldFlowSeq.false_of_map_basepoint_fixing_of_basepoint_ne
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop) (m : Nat)
    (p : M) (g : SmoothRiemannianMetric I M) {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m)
      (Y.windowPointedManifold p g) subseq)
    (hfix : forall k : Nat, Phi.map k p = p) (k : Nat)
    (hne : (Y.toFiniteArcFlowSeq.windowSeq hT m).basepoint (subseq k) ≠ p) : False :=
  hne (SameManifoldFlowSeq.basepoint_eq_of_map_basepoint_fixing (I := I) Y hT m p g Phi hfix k)

structure SameManifoldLimitEquationData
    (gInf : Real -> SmoothRiemannianMetric I M)
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) where
  solution : PDE.RicciFlow.SolutionOn (I := I) (M := M) D
  isSolution : PDE.RicciFlow.IsSolutionOn (I := I) solution
  agrees : forall t : Real, t ∈ D.carrier -> solution.family.metric t = gInf t

namespace SameManifoldLimitEquationData

omit [SigmaCompactSpace M] in
noncomputable def ofSolution (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (S : PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : PDE.RicciFlow.IsSolutionOn (I := I) S) :
    SameManifoldLimitEquationData (I := I) (fun t => S.family.metric t) D where
  solution := S
  isSolution := hS
  agrees _ _ := rfl

end SameManifoldLimitEquationData

noncomputable def SameManifoldFlowSeq.sameManifoldLimitEquationData_term
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (n : Nat) :
    SameManifoldLimitEquationData (I := I) (Y.metricFamily n) (arcInterval (Y.horizon n)) :=
  SameManifoldLimitEquationData.ofSolution (I := I) (arcInterval (Y.horizon n))
    (Y.solution n) (Y.isSolution n)

theorem tendsto_metricScalarAt_of_jetConvergence [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (gSeq : Nat -> SmoothRiemannianMetric I M) (gInf : SmoothRiemannianMetric I M)
    (lam B : Real) (hlam : 0 < lam) (hB : 0 <= B)
    (hlowSeq : forall k : Nat, forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= (gSeq k).inner x ξ ξ)
    (hlowInf : forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= gInf.inner x ξ ξ)
    (hbddSeq : forall k : Nat, forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a (gSeq k) gRef x <= B)
    (hbddInf : forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a gInf gRef x <= B)
    (hconv : forall ε : Real, 0 < ε -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= 2 -> metricDerivNorm (I := I) a (gSeq k) gInf gRef x < ε) :
    Tendsto (fun k : Nat => metricScalarAt (I := I) (gSeq k) x) atTop
      (nhds (metricScalarAt (I := I) gInf x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hconv' : forall δ : Real, 0 < δ -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall s : Real, s ∈ Set.Icc (0 : Real) 0 ->
        forall a : Nat, a <= 2 ->
          metricDerivNorm (I := I) a ((fun k _ => gSeq k) k s) ((fun _ => gInf) s) gRef x < δ := by
    intro δ hδ
    obtain ⟨k0, hk0⟩ := hconv δ hδ
    exact ⟨k0, fun k hk s _ a ha => hk0 k hk a ha⟩
  obtain ⟨k0, hk0⟩ :=
    scalarConvergence_of_dnConvergence (I := I) gRef x (fun k _ => gSeq k) (fun _ => gInf)
      (0 : Real) (0 : Real) lam B hlam hB
      (fun k _ _ => hlowSeq k) (fun _ _ => hlowInf)
      (fun k _ _ => hbddSeq k) (fun _ _ => hbddInf)
      hconv' ε hε
  refine ⟨k0, fun k hk => ?_⟩
  simpa [Real.dist_eq] using hk0 k hk (0 : Real) ⟨le_rfl, le_rfl⟩

theorem tendsto_ricciTensor_of_jetConvergence [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (gSeq : Nat -> SmoothRiemannianMetric I M) (gInf : SmoothRiemannianMetric I M)
    (lam B : Real) (hlam : 0 < lam) (hB : 0 <= B)
    (hlowSeq : forall k : Nat, forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= (gSeq k).inner x ξ ξ)
    (hlowInf : forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= gInf.inner x ξ ξ)
    (hbddSeq : forall k : Nat, forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a (gSeq k) gRef x <= B)
    (hbddInf : forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a gInf gRef x <= B)
    (hconv : forall ε : Real, 0 < ε -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= 2 -> metricDerivNorm (I := I) a (gSeq k) gInf gRef x < ε)
    (v w : TangentSpace I x) :
    Tendsto (fun k : Nat => ricciTensor (I := I) (gSeq k) x v w) atTop
      (nhds (ricciTensor (I := I) gInf x v w)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hconv' : forall δ : Real, 0 < δ -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall s : Real, s ∈ Set.Icc (0 : Real) 0 ->
        forall a : Nat, a <= 2 ->
          metricDerivNorm (I := I) a ((fun k _ => gSeq k) k s) ((fun _ => gInf) s) gRef x < δ := by
    intro δ hδ
    obtain ⟨k0, hk0⟩ := hconv δ hδ
    exact ⟨k0, fun k hk s _ a ha => hk0 k hk a ha⟩
  obtain ⟨k0, hk0⟩ :=
    ricciConvergence_of_dnConvergence (I := I) gRef x (fun k _ => gSeq k) (fun _ => gInf)
      (0 : Real) (0 : Real) lam B hlam hB
      (fun k _ _ => hlowSeq k) (fun _ _ => hlowInf)
      (fun k _ _ => hbddSeq k) (fun _ _ => hbddInf)
      hconv' v w ε hε
  refine ⟨k0, fun k hk => ?_⟩
  simpa [Real.dist_eq] using hk0 k hk (0 : Real) ⟨le_rfl, le_rfl⟩

theorem tendsto_metricRicciAt_of_jetConvergence [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (gSeq : Nat -> SmoothRiemannianMetric I M) (gInf : SmoothRiemannianMetric I M)
    (lam B : Real) (hlam : 0 < lam) (hB : 0 <= B)
    (hlowSeq : forall k : Nat, forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= (gSeq k).inner x ξ ξ)
    (hlowInf : forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= gInf.inner x ξ ξ)
    (hbddSeq : forall k : Nat, forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a (gSeq k) gRef x <= B)
    (hbddInf : forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a gInf gRef x <= B)
    (hconv : forall ε : Real, 0 < ε -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= 2 -> metricDerivNorm (I := I) a (gSeq k) gInf gRef x < ε)
    (v w : TangentSpace I x) :
    Tendsto (fun k : Nat => metricRicciAt (I := I) (gSeq k) x (vec2 v w)) atTop
      (nhds (metricRicciAt (I := I) gInf x (vec2 v w))) :=
  by
    simpa only [DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor] using
      tendsto_ricciTensor_of_jetConvergence (I := I) gRef x gSeq gInf lam B hlam hB
        hlowSeq hlowInf hbddSeq hbddInf hconv v w

theorem tendsto_metricRicciNormSq_of_jetConvergence [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (gSeq : Nat -> SmoothRiemannianMetric I M) (gInf : SmoothRiemannianMetric I M)
    (lam B : Real) (hlam : 0 < lam) (hB : 0 <= B)
    (hlowSeq : forall k : Nat, forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= (gSeq k).inner x ξ ξ)
    (hlowInf : forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= gInf.inner x ξ ξ)
    (hbddSeq : forall k : Nat, forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a (gSeq k) gRef x <= B)
    (hbddInf : forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a gInf gRef x <= B)
    (hconv : forall ε : Real, 0 < ε -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= 2 -> metricDerivNorm (I := I) a (gSeq k) gInf gRef x < ε) :
    Tendsto (fun k : Nat =>
        normSq0S (I := I) (gSeq k) x 2 (metricRicci (I := I) (M := M) (gSeq k) x)) atTop
      (nhds (normSq0S (I := I) gInf x 2 (metricRicci (I := I) (M := M) gInf x))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hconv' : forall δ : Real, 0 < δ -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall s : Real, s ∈ Set.Icc (0 : Real) 0 ->
        forall a : Nat, a <= 2 ->
          metricDerivNorm (I := I) a ((fun k _ => gSeq k) k s) ((fun _ => gInf) s) gRef x < δ := by
    intro δ hδ
    obtain ⟨k0, hk0⟩ := hconv δ hδ
    exact ⟨k0, fun k hk s _ a ha => hk0 k hk a ha⟩
  obtain ⟨k0, hk0⟩ :=
    ricNormConvergence_of_dn (I := I) gRef x (fun k _ => gSeq k) (fun _ => gInf)
      (0 : Real) (0 : Real) lam B hlam hB
      (fun k _ _ => hlowSeq k) (fun _ _ => hlowInf)
      (fun k _ _ => hbddSeq k) (fun _ _ => hbddInf)
      hconv' ε hε
  refine ⟨k0, fun k hk => ?_⟩
  simpa [Real.dist_eq] using hk0 k hk (0 : Real) ⟨le_rfl, le_rfl⟩

theorem SameManifoldFlowSeq.tendsto_scalar_of_jetConvergence [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (gRef : SmoothRiemannianMetric I M) (x : M)
    (gInf : SmoothRiemannianMetric I M) (subseq : Nat -> Nat) (t : Real)
    (lam B : Real) (hlam : 0 < lam) (hB : 0 <= B)
    (hlowSeq : forall k : Nat, forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= (((Y.solution (subseq k)).family.metric t).inner x ξ ξ))
    (hlowInf : forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= gInf.inner x ξ ξ)
    (hbddSeq : forall k : Nat, forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a ((Y.solution (subseq k)).family.metric t) gRef x <= B)
    (hbddInf : forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a gInf gRef x <= B)
    (hconv : forall ε : Real, 0 < ε -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= 2 ->
        metricDerivNorm (I := I) a ((Y.solution (subseq k)).family.metric t) gInf gRef x < ε) :
    Tendsto (fun k : Nat => (Y.solution (subseq k)).scalar t x) atTop
      (nhds (metricScalarAt (I := I) gInf x)) := by
  have h := tendsto_metricScalarAt_of_jetConvergence (I := I) gRef x
    (fun k => (Y.solution (subseq k)).family.metric t) gInf lam B hlam hB
    hlowSeq hlowInf hbddSeq hbddInf hconv
  simpa only [PDE.RicciFlow.SolutionOn.scalar, PDE.RicciFlow.SolutionFamily.scalar,
    PDE.RicciFlow.SolutionOn.family_metric] using h

theorem SameManifoldFlowSeq.tendsto_ricciAt_of_jetConvergence [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (gRef : SmoothRiemannianMetric I M) (x : M)
    (gInf : SmoothRiemannianMetric I M) (subseq : Nat -> Nat) (t : Real)
    (lam B : Real) (hlam : 0 < lam) (hB : 0 <= B)
    (hlowSeq : forall k : Nat, forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= (((Y.solution (subseq k)).family.metric t).inner x ξ ξ))
    (hlowInf : forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= gInf.inner x ξ ξ)
    (hbddSeq : forall k : Nat, forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a ((Y.solution (subseq k)).family.metric t) gRef x <= B)
    (hbddInf : forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a gInf gRef x <= B)
    (hconv : forall ε : Real, 0 < ε -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= 2 ->
        metricDerivNorm (I := I) a ((Y.solution (subseq k)).family.metric t) gInf gRef x < ε)
    (v w : TangentSpace I x) :
    Tendsto (fun k : Nat =>
        metricRicciAt (I := I) ((Y.solution (subseq k)).family.metric t) x (vec2 v w)) atTop
      (nhds (metricRicciAt (I := I) gInf x (vec2 v w))) :=
  tendsto_metricRicciAt_of_jetConvergence (I := I) gRef x
    (fun k => (Y.solution (subseq k)).family.metric t) gInf lam B hlam hB
    hlowSeq hlowInf hbddSeq hbddInf hconv v w

theorem SameManifoldFlowSeq.tendsto_ricciNorm_of_jetConvergence [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (gRef : SmoothRiemannianMetric I M) (x : M)
    (gInf : SmoothRiemannianMetric I M) (subseq : Nat -> Nat) (t : Real)
    (lam B : Real) (hlam : 0 < lam) (hB : 0 <= B)
    (hlowSeq : forall k : Nat, forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= (((Y.solution (subseq k)).family.metric t).inner x ξ ξ))
    (hlowInf : forall ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ <= gInf.inner x ξ ξ)
    (hbddSeq : forall k : Nat, forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a ((Y.solution (subseq k)).family.metric t) gRef x <= B)
    (hbddInf : forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a gInf gRef x <= B)
    (hconv : forall ε : Real, 0 < ε -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= 2 ->
        metricDerivNorm (I := I) a ((Y.solution (subseq k)).family.metric t) gInf gRef x < ε) :
    Tendsto (fun k : Nat => PDE.RicciFlow.ricciNorm (I := I) (Y.solution (subseq k)) t x) atTop
      (nhds (normSq0S (I := I) gInf x 2 (metricRicci (I := I) (M := M) gInf x))) := by
  have h := tendsto_metricRicciNormSq_of_jetConvergence (I := I) gRef x
    (fun k => (Y.solution (subseq k)).family.metric t) gInf lam B hlam hB
    hlowSeq hlowInf hbddSeq hbddInf hconv
  simpa only [PDE.RicciFlow.ricciNorm, PDE.RicciFlow.SolutionOn.ricci,
    PDE.RicciFlow.SolutionFamily.ricci, PDE.RicciFlow.SolutionOn.family_metric] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
