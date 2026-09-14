import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge

noncomputable section

open Metric Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

structure CutCapTransitionData (P Q D N : OrientedThreeStage.{u}) where
  trace : CutCapTopology P.Carrier Q.Carrier D.Carrier N.Carrier
  source_nonempty : Nonempty P.Carrier
  tube_smooth :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    ∀ a : trace.tubes.Index,
      IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (trace.tubes.tube a)
  [coreCharts : ChartedSpace (EuclideanHalfSpace 3) trace.tubes.core]
  [coreSmooth : IsManifold (𝓡∂ 3) ∞ trace.tubes.core]
  core_induced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
    (Subtype.val : trace.tubes.core → P.Carrier)
  core_boundary : (𝓡∂ 3).boundary trace.tubes.core =
    ⋃ b : trace.tubes.Boundary, Set.range (trace.tubes.coreBoundarySphere b)
  core_inclusion_smooth : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ trace.capping.coreInclusion
  cap_smooth : ∀ b, IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (trace.capping.cap b)
  attaching : ∀ _b : trace.tubes.Boundary, Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2
  attaching_eq : ∀ b, (attaching b : Sphere 2 → Sphere 2) = trace.capping.attaching b
  core_positive : ∀ x : trace.tubes.core, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : trace.tubes.core → P.Carrier) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel trace.capping.coreInclusion x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : trace.tubes.core → P.Carrier) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel trace.capping.coreInclusion x).toLinearMap hj))
        (P.orientation.orientation x.1) =
          N.orientation.orientation (trace.capping.coreInclusion x)
  cap_positive : ∀ b, ∀ x : ThreeBall, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : ThreeBall → ThreeSpace) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (trace.capping.cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel (trace.capping.cap b) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) ≠
          N.orientation.orientation (trace.capping.cap b x)
  presentation : N.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ (Q.Carrier ⊕ D.Carrier)
  presentation_eq : (presentation : N.Carrier → Q.Carrier ⊕ D.Carrier) = trace.presentation
  presentation_positive : ∀ x : N.Carrier,
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel presentation x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel presentation x).toLinearMap hf)
        (N.orientation.orientation x) =
          match presentation x with
          | Sum.inl q => Q.orientation.orientation q
          | Sum.inr d => D.orientation.orientation d

def CutCapTransitionData.toSmoothCutCapTransition {P Q D N : OrientedThreeStage.{u}}
    (S : CutCapTransitionData P Q D N) : SmoothCutCapTransition P Q D N where
  trace := S.trace
  source_nonempty := S.source_nonempty
  tube_smooth := S.tube_smooth
  coreCharts := S.coreCharts
  coreSmooth := S.coreSmooth
  core_induced := S.core_induced
  core_boundary := S.core_boundary
  core_inclusion_smooth := S.core_inclusion_smooth
  ballCharts := threeBallChartedSpace
  ballSmooth := threeBall_isManifold
  ball_induced := isSmoothEmbedding_threeBall_inclusion
  ball_boundary := threeBall_boundary_eq_sphere
  cap_smooth := S.cap_smooth
  attaching := S.attaching
  attaching_eq := S.attaching_eq
  core_positive := S.core_positive
  cap_positive := S.cap_positive
  presentation := S.presentation
  presentation_eq := S.presentation_eq
  presentation_positive := S.presentation_positive

theorem nonempty_smoothCutCapTransition_of_data {P Q D N : OrientedThreeStage.{u}}
    (S : CutCapTransitionData P Q D N) : Nonempty (SmoothCutCapTransition P Q D N) :=
  ⟨S.toSmoothCutCapTransition⟩

def emptyTubeSystem (M : Type*) [TopologicalSpace M] : TubeSystem M where
  Index := PEmpty
  finiteIndex := ⟨∅, fun x => PEmpty.elim x⟩
  tube := fun a => PEmpty.elim a
  embedding := fun a => PEmpty.elim a
  disjoint := fun a => PEmpty.elim a

theorem emptyTubeSystem_core (M : Type*) [TopologicalSpace M] :
    (emptyTubeSystem M).core = univ := by
  apply Set.eq_univ_of_forall
  intro x
  simp only [TubeSystem.core, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  intro a
  exact PEmpty.elim a

def emptyTubeCapping (N : Type*) [TopologicalSpace N] :
    Capping (emptyTubeSystem N) N where
  coreInclusion := ⟨Subtype.val, continuous_subtype_val⟩
  coreEmbedding := Topology.IsEmbedding.subtypeVal
  cap := fun b => PEmpty.elim b.1
  capEmbedding := fun b => PEmpty.elim b.1
  attaching := fun b => PEmpty.elim b.1
  boundary_eq := fun b => PEmpty.elim b.1
  exhaustive := by
    have hcap : (⋃ b : (emptyTubeSystem N).Boundary,
        Set.range (PEmpty.elim b.1 : C(ThreeBall, N))) = ∅ := by
      apply Set.iUnion_eq_empty.mpr
      intro b
      exact PEmpty.elim b.1
    rw [hcap, Set.union_empty]
    apply Set.range_eq_univ.mpr
    intro x
    exact ⟨⟨x, by rw [emptyTubeSystem_core]; exact Set.mem_univ x⟩, rfl⟩
  core_cap_intersection := fun b => PEmpty.elim b.1
  cap_disjoint := fun b => PEmpty.elim b.1

def discardedComponentCutCap (Q D : Type*) [TopologicalSpace Q] [TopologicalSpace D]
    (d : D) : CutCapTopology (Q ⊕ D) Q D (Q ⊕ D) where
  tubes := emptyTubeSystem (Q ⊕ D)
  capping := emptyTubeCapping (Q ⊕ D)
  presentation := Homeomorph.refl _
  nontrivial := Or.inr ⟨d⟩

theorem discardedComponentCutCap_retained (Q D : Type*) [TopologicalSpace Q]
    [TopologicalSpace D] (d : D) (q : Q) :
    (discardedComponentCutCap Q D d).presentation (Sum.inl q) = Sum.inl q ∧
      (discardedComponentCutCap Q D d).presentation (Sum.inr d) = Sum.inr d :=
  ⟨rfl, rfl⟩

theorem nonempty_retainedCore_of_discardedComponentCutCap (Q D : Type*)
    [TopologicalSpace Q] [TopologicalSpace D] (d : D) (q : Q) :
    Nonempty ((discardedComponentCutCap Q D d).retainedCore) := by
  refine ⟨⟨⟨Sum.inl q, ?_⟩, q, ?_⟩⟩
  · change Sum.inl q ∈ (emptyTubeSystem (Q ⊕ D)).core
    rw [emptyTubeSystem_core]
    exact Set.mem_univ _
  · rfl

structure CutCapTopologyIgnoringNontrivial (M Q D N : Type*) [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace D] [TopologicalSpace N] where
  tubes : TubeSystem M
  capping : Capping tubes N
  presentation : N ≃ₜ Q ⊕ D

def vacuousCutCapTopology (M : Type*) [TopologicalSpace M] :
    CutCapTopologyIgnoringNontrivial (M ⊕ PEmpty) M PEmpty (M ⊕ PEmpty) where
  tubes := emptyTubeSystem (M ⊕ PEmpty)
  capping := emptyTubeCapping (M ⊕ PEmpty)
  presentation := Homeomorph.refl _

theorem not_isEmpty_index_and_isEmpty_discarded {M Q D N : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace D] [TopologicalSpace N]
    (E : CutCapTopology M Q D N) (h₁ : IsEmpty E.tubes.Index) (h₂ : IsEmpty D) : False := by
  rcases E.nontrivial with h | h
  · exact h₁.false h.some
  · exact h₂.false h.some

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)

def snocR {n : ℕ} (f : Fin n → ℝ) (a : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) f a

@[simp] theorem snocR_castSucc {n : ℕ} (f : Fin n → ℝ) (a : ℝ) (i : Fin n) :
    snocR f a i.castSucc = f i := Fin.snoc_castSucc (α := fun _ => ℝ) a f i

@[simp] theorem snocR_last {n : ℕ} (f : Fin n → ℝ) (a : ℝ) :
    snocR f a (Fin.last n) = a := Fin.snoc_last (α := fun _ => ℝ) a f

def neckPoint (x : Sphere 2) (t : ℝ) : FourSpace :=
  WithLp.toLp 2 (snocR (fun i : Fin 3 => Real.sqrt (1 - (t / 4) ^ 2) * x.1 i) (t / 4))

theorem neckPoint_mem_sphere (x : Sphere 2) (t : Icc (-2 : ℝ) 2) :
    neckPoint x t.1 ∈ Sphere 3 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have habs : |t.1| ≤ 2 := abs_le.mpr ⟨t.2.1, t.2.2⟩
  have h4 : t.1 ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [habs, abs_nonneg t.1]
  have ht : (t.1 / 4) ^ 2 ≤ 1 := by nlinarith [h4]
  have hsqrt : Real.sqrt (1 - (t.1 / 4) ^ 2) ^ 2 = 1 - (t.1 / 4) ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    have h := x.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  have h2 : ‖neckPoint x t.1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [neckPoint, WithLp.ofLp_toLp]
    rw [Fin.sum_univ_castSucc]
    have h1 : (∑ i : Fin 3, ‖snocR (fun i : Fin 3 => Real.sqrt (1 - (t.1 / 4) ^ 2) * x.1 i)
        (t.1 / 4) i.castSucc‖ ^ 2)
        = (Real.sqrt (1 - (t.1 / 4) ^ 2)) ^ 2 * ∑ i : Fin 3, ‖x.1 i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [snocR_castSucc, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [h1, snocR_last, Real.norm_eq_abs, sq_abs,
      ← EuclideanSpace.norm_sq_eq (x : EuclideanSpace ℝ (Fin 3)), hx, hsqrt]
    ring
  nlinarith [norm_nonneg (neckPoint x t.1), h2]

def standardNeckTubeFun (z : TubeDomain) : Sphere 3 :=
  ⟨neckPoint z.1 z.2.1, neckPoint_mem_sphere z.1 z.2⟩

theorem continuous_snocR_family :
    Continuous fun z : TubeDomain =>
      (fun i : Fin 3 => Real.sqrt (1 - (z.2.1 / 4) ^ 2) * z.1.1 i) := by
  apply continuous_pi
  intro i
  have hc : Continuous fun z : TubeDomain => Real.sqrt (1 - (z.2.1 / 4) ^ 2) := by fun_prop
  have hx : Continuous fun z : TubeDomain => ((z.1 : Sphere 2) : EuclideanSpace ℝ (Fin 3)) i := by
    fun_prop
  exact hc.mul hx

theorem continuous_standardNeckTubeFun : Continuous standardNeckTubeFun := by
  apply Continuous.subtype_mk
  have hg : Continuous fun z : TubeDomain => z.2.1 / 4 :=
    (continuous_subtype_val.comp continuous_snd).div_const 4
  have hbase : Continuous fun z : TubeDomain =>
      snocR (fun i : Fin 3 => Real.sqrt (1 - (z.2.1 / 4) ^ 2) * z.1.1 i) (z.2.1 / 4) :=
    Continuous.finSnoc continuous_snocR_family hg
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp hbase

theorem standardNeckTubeFun_injective : Function.Injective standardNeckTubeFun := by
  intro z w hzw
  have hlast : z.2.1 / 4 = w.2.1 / 4 := by
    have h := congrArg (fun p : Sphere 3 => (p.1 : FourSpace).ofLp (Fin.last 3)) hzw
    simpa only [standardNeckTubeFun, neckPoint, WithLp.ofLp_toLp, snocR_last] using h
  have ht : z.2.1 = w.2.1 := by linarith
  have hpos : 0 < Real.sqrt (1 - (z.2.1 / 4) ^ 2) := by
    have habs : |z.2.1| ≤ 2 := abs_le.mpr ⟨z.2.2.1, z.2.2.2⟩
    have h4 : z.2.1 ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [habs, abs_nonneg z.2.1]
    apply Real.sqrt_pos.mpr
    nlinarith [h4]
  have hx : z.1 = w.1 := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    have h := congrArg (fun p : Sphere 3 => (p.1 : FourSpace).ofLp i.castSucc) hzw
    simp only [standardNeckTubeFun, neckPoint, WithLp.ofLp_toLp, snocR_castSucc] at h
    rw [← ht] at h
    exact mul_left_cancel₀ (ne_of_gt hpos) h
  exact Prod.ext hx (Subtype.ext ht)

theorem isEmbedding_standardNeckTubeFun : Topology.IsEmbedding standardNeckTubeFun :=
  (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_standardNeckTubeFun
    standardNeckTubeFun_injective
    fun _s hs => (hs.isCompact.image continuous_standardNeckTubeFun).isClosed).toIsEmbedding

def standardNeckTube : C(TubeDomain, Sphere 3) :=
  ⟨standardNeckTubeFun, continuous_standardNeckTubeFun⟩

def standardNeckTubeSystem : TubeSystem (Sphere 3) where
  Index := PUnit
  finiteIndex := inferInstance
  tube := fun _ => standardNeckTube
  embedding := fun _ => isEmbedding_standardNeckTubeFun
  disjoint := fun a b hab => (hab (Subsingleton.elim a b)).elim

theorem standardNeckTubeSystem_index_nonempty :
    Nonempty standardNeckTubeSystem.Index := ⟨PUnit.unit⟩

theorem standardNeckTubeSystem_boundary_nonempty :
    Nonempty standardNeckTubeSystem.Boundary := ⟨(PUnit.unit, false)⟩


theorem standardNeckTubeSystem_removedBand_nonempty :
    (standardNeckTubeSystem.removedBand PUnit.unit).Nonempty := by
  let x₀ : Sphere 2 := ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩
  let z₀ : TubeDomain := (x₀, ⟨0, by norm_num, by norm_num⟩)
  exact ⟨standardNeckTube z₀, z₀, ⟨by norm_num, by norm_num⟩, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
