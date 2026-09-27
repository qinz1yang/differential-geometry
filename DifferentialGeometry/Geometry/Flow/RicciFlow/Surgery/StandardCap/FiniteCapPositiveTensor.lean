import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteCapWitnessMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticOpenRetained
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapPositiveOverlap

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev TensorE3 := EuclideanSpace ℝ (Fin 3)
private abbrev TensorIC := (𝓡 2).prod 𝓘(ℝ)
private local instance staticChartedSpace {B : ℝ} {hB : 0 < B} : ChartedSpace TensorE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance staticIsManifold {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

theorem positiveCuttingCylinder_subset_insertion {A B r : ℝ} (hA : 0 < A) (hstatic : r ≤ B) :
    positiveCuttingCylinder r ≤ insertionCylinder A B := by
  intro q hq
  change 0 < q.2 ∧ q.2 < r at hq
  change -2 * A < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2.trans_le hstatic⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph TensorIC I ∞ (f i))
variable {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [Fact (Module.finrank ℝ F = 3)] [TopologicalSpace K] {J : ModelWithCorners ℝ F K} [J.Boundaryless]
variable [TopologicalSpace N] [ChartedSpace K N] [T2Space N] [IsManifold J ∞ N]
variable {g : SmoothRiemannianMetric J N} {x₀ : N} {δ : ℝ} {k : ℕ}
variable (d : normalizedDatum g x₀ δ k) {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : CanonicalStaticInsertionWitness d A hA D m ε)
variable (b : ι × Bool) (r : ℝ) (hfit : r ≤ cuttingCollarWidth (precision b.1)) (hstatic : r ≤ δ⁻¹)
local notation "TensorQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "TensorPatch" => finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b r

theorem finiteCapPositiveMap_toStatic (q : positiveCuttingCylinder r) :
    let : ChartedSpace TensorE3 TensorQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic
      (finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit q) =
        insertionQuotientCollarMap hA w.properties.cut_fit (inv_pos.mpr d.precision_pos)
          (Opens.inclusion (positiveCuttingCylinder_subset_insertion hA hstatic) q) := by
  let : ChartedSpace TensorE3 TensorQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let c : Metric.sphere (0 : TensorE3) 1 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)) := (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hfit⟩)
  have hc : finiteCoreInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b c) ∈ TensorPatch :=
    (finiteCapRestrictedNeighborhood_collar_iff transitionEnd_pos hδ f hf hdisj b r c).mpr q.property.2
  have hp : finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit q =
      ⟨finiteCoreInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b c), hc⟩ :=
    Subtype.ext (finiteCapPositiveMap_original I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit q)
  exact (congrArg (finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit
    (inv_pos.mpr d.precision_pos) hstatic) hp).trans
    ((finiteCapInsertionMap_collar I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit
      (inv_pos.mpr d.precision_pos) hstatic c q.property.2).trans
        (insertionQuotientCollarMap_retained hA w.properties.cut_fit (inv_pos.mpr d.precision_pos)
          (Opens.inclusion (positiveCuttingCylinder_subset_insertion hA hstatic) q) q.property.1.le).symm)

theorem finiteCapWitnessMetric_positive_inner :
    let : ChartedSpace TensorE3 TensorQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ TensorQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : positiveCuttingCylinder r) (v z : TangentSpace TensorIC q),
      (finiteCapWitnessMetric I hdim hδ f hf hdisj hs d w b r hfit hstatic).inner
        (finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit q)
        (mfderiv TensorIC (𝓡 3) (finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit) q v)
        (mfderiv TensorIC (𝓡 3) (finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit) q z) =
      g.inner (d.oriented.controlledMap
        (Opens.inclusion (insertionCylinder_subset_original w.properties.cut_fit)
          (Opens.inclusion (positiveCuttingCylinder_subset_insertion hA hstatic) q)))
        (mfderiv TensorIC J d.oriented.controlledMap
          (Opens.inclusion (insertionCylinder_subset_original w.properties.cut_fit)
            (Opens.inclusion (positiveCuttingCylinder_subset_insertion hA hstatic) q)) v)
        (mfderiv TensorIC J d.oriented.controlledMap
          (Opens.inclusion (insertionCylinder_subset_original w.properties.cut_fit)
            (Opens.inclusion (positiveCuttingCylinder_subset_insertion hA hstatic) q)) z) := by
  let : ChartedSpace TensorE3 TensorQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ TensorQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
  let beta := finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit
  let F := finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic
  let C := insertionQuotientCollarMap hA w.properties.cut_fit (inv_pos.mpr d.precision_pos)
  let i := Opens.inclusion (positiveCuttingCylinder_subset_insertion hA hstatic)
  have hb : ContMDiff TensorIC (𝓡 3) ∞ beta := contMDiff_finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F := contMDiff_finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic
  have hC : ContMDiff TensorIC (𝓡 3) ∞ C := contMDiff_insertionQuotientCollarMap hA w.properties.cut_fit (inv_pos.mpr d.precision_pos)
  have hi : ContMDiff TensorIC TensorIC ∞ i := contMDiff_inclusion (positiveCuttingCylinder_subset_insertion hA hstatic)
  have he : F ∘ beta = C ∘ i := funext (finiteCapPositiveMap_toStatic I hdim hδ f hf hdisj hs d w b r hfit hstatic)
  dsimp only
  intro q v z
  have hd : (mfderiv (𝓡 3) (𝓡 3) F (beta q)).comp (mfderiv TensorIC (𝓡 3) beta q) =
      mfderiv TensorIC (𝓡 3) C (i q) := by
    have hl := mfderiv_comp q (hF.mdifferentiable (by simp) (beta q)) (hb.mdifferentiable (by simp) q)
    have hr : mfderiv TensorIC (𝓡 3) (C ∘ i) q = mfderiv TensorIC (𝓡 3) C (i q) := by
      rw [mfderiv_comp q (hC.mdifferentiable (by simp) (i q)) (hi.mdifferentiable (by simp) q), mfderiv_opens_incl]
      rfl
    exact hl.symm.trans ((mfderiv_congr he).trans hr)
  have hv := congrArg (fun D => D v) hd
  have hz := congrArg (fun D => D z) hd
  have ht := finiteCapWitnessMetric_inner I hdim hδ f hf hdisj hs d w b r hfit hstatic
    (beta q) (mfderiv TensorIC (𝓡 3) beta q v) (mfderiv TensorIC (𝓡 3) beta q z)
  refine ht.trans ?_
  change w.data.outMetric.inner (F (beta q))
    (mfderiv (𝓡 3) (𝓡 3) F (beta q) (mfderiv TensorIC (𝓡 3) beta q v))
    (mfderiv (𝓡 3) (𝓡 3) F (beta q) (mfderiv TensorIC (𝓡 3) beta q z)) = _
  have hpoint : F (beta q) = C (i q) := congrFun he q
  dsimp only [TangentSpace] at hv hz ⊢
  erw [hv, hz, hpoint]
  exact staticWitness_openRetained d w (i q) q.property.1.le v z
end DifferentialGeometry.PDE.RicciFlow.StandardCap
