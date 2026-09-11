import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteOldMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteCapPositiveTensor
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteRetainedPositiveMap

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev AgreementE3 := EuclideanSpace ℝ (Fin 3)
private abbrev AgreementIC := (𝓡 2).prod 𝓘(ℝ)
private def controlledInclusion {A B r : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hstatic : r ≤ B) :
    positiveCuttingCylinder r → openCylinder B :=
  Opens.inclusion (le_trans (positiveCuttingCylinder_subset_insertion hA hstatic)
    (insertionCylinder_subset_original hAB))
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph AgreementIC I ∞ (f i))
local notation "AgreementQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (b : ι × Bool) (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R)
variable (r : ℝ) (hfit : r ≤ cuttingCollarWidth (precision b.1))
variable {x₀ : U} {δ : ℝ} {k : ℕ} (d : normalizedDatum g x₀ δ k)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ} (w : CanonicalStaticInsertionWitness d A hA D m ε)
variable (hstatic : r ≤ δ⁻¹)
local notation "AgreementPatch" => finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b r
local notation "AgreementOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
private def oldOverlapPoint (q : AgreementPatch)
    (hq : q.val ∈ finiteCoreInterior transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    AgreementOld := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  exact ⟨q.val, finiteCapRestrictedNeighborhood_subset_retained transitionEnd_pos hδ f hf hdisj R b hb r q.property, hq⟩

private theorem positive_inner
    (hmap : ∀ q : positiveCuttingCylinder r,
      (d.oriented.controlledMap (controlledInclusion hA w.properties.cut_fit hstatic q)).val =
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
          (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hfit⟩)).val)
    :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace AgreementE3 AgreementQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ AgreementQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
    ∀ (p : positiveCuttingCylinder r) (a c : TangentSpace AgreementIC p),
      (finiteOldMetric I hdim transitionEnd_pos hδ f hf hdisj hs U g R hRet).inner
        (finiteRetainedPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs R b hb r hfit p)
        (mfderiv AgreementIC (𝓡 3) (finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit) p a)
        (mfderiv AgreementIC (𝓡 3) (finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit) p c) =
      (finiteCapWitnessMetric I hdim hδ f hf hdisj hs d w b r hfit hstatic).inner
        (finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit p)
        (mfderiv AgreementIC (𝓡 3) (finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit) p a)
        (mfderiv AgreementIC (𝓡 3) (finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit) p c) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace AgreementE3 AgreementQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ AgreementQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
  dsimp only
  intro p a c
  let alpha := finiteRetainedPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs R b hb r hfit
  let beta := finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit
  let G := finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet
  let C := d.oriented.controlledMap
  let rho := controlledInclusion hA w.properties.cut_fit hstatic
  have ha : ContMDiff AgreementIC (𝓡 3) ∞ alpha :=
    contMDiff_finiteRetainedPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs R b hb r hfit
  have hG : ContMDiff (𝓡 3) I ∞ G :=
    contMDiff_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj I hdim hs U R hRet
  have hC : ContMDiff AgreementIC I ∞ C := d.oriented.controlledMap_smooth
  have hrho : ContMDiff AgreementIC AgreementIC ∞ rho := contMDiff_inclusion
    (le_trans (positiveCuttingCylinder_subset_insertion hA hstatic) (insertionCylinder_subset_original w.properties.cut_fit))
  have he : G ∘ alpha = C ∘ rho := by
    funext p
    apply Subtype.ext
    exact (finiteRetainedPositiveMap_original_point I hdim transitionEnd_pos hδ f hf hdisj hs R b hb r hfit U hRet p).trans (hmap p).symm
  have hab : mfderiv AgreementIC (𝓡 3) alpha p = mfderiv AgreementIC (𝓡 3) beta p :=
    finiteRetainedPositiveMap_mfderiv I hdim transitionEnd_pos hδ f hf hdisj hs R b hb r hfit p
  have hl := mfderiv_comp p (hG.mdifferentiable (by simp) (alpha p)) (ha.mdifferentiable (by simp) p)
  have hr : mfderiv AgreementIC I (C ∘ rho) p = mfderiv AgreementIC I C (rho p) := by
    rw [mfderiv_comp p (hC.mdifferentiable (by simp) (rho p)) (hrho.mdifferentiable (by simp) p)]
    dsimp only [rho, controlledInclusion]
    rw [mfderiv_opens_incl]
    rfl
  have hd : (mfderiv (𝓡 3) I G (alpha p)).comp (mfderiv AgreementIC (𝓡 3) beta p) =
      mfderiv AgreementIC I C (rho p) := by
    have h := hl.symm.trans ((mfderiv_congr he).trans hr)
    rw [hab] at h
    exact h
  have hva := congrArg (fun D => D a) hd
  have hvc := congrArg (fun D => D c) hd
  have ht := finiteOldMetric_inner I hdim transitionEnd_pos hδ f hf hdisj hs U g R hRet
    (alpha p) (mfderiv AgreementIC (𝓡 3) beta p a) (mfderiv AgreementIC (𝓡 3) beta p c)
  refine ht.trans ?_
  change g.inner (G (alpha p))
    (mfderiv (𝓡 3) I G (alpha p) (mfderiv AgreementIC (𝓡 3) beta p a))
    (mfderiv (𝓡 3) I G (alpha p) (mfderiv AgreementIC (𝓡 3) beta p c)) = _
  have hp : G (alpha p) = C (rho p) := congrFun he p
  dsimp only [TangentSpace] at hva hvc ⊢
  erw [hva, hvc, hp]
  exact (finiteCapWitnessMetric_positive_inner I hdim hδ f hf hdisj hs d w b r hfit hstatic p a c).symm

theorem finiteMetricOverlap_inner
    (hmap : ∀ q : positiveCuttingCylinder r,
      (d.oriented.controlledMap (controlledInclusion hA w.properties.cut_fit hstatic q)).val =
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
          (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hfit⟩)).val)
    :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace AgreementE3 AgreementQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ AgreementQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : AgreementPatch)
      (hq : q.val ∈ finiteCoreInterior transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj)
      (v z : TangentSpace (𝓡 3) q),
    (finiteOldMetric I hdim transitionEnd_pos hδ f hf hdisj hs U g R hRet).inner
      (oldOverlapPoint I hdim hδ f hf hdisj R b hb r q hq) v z =
        (finiteCapWitnessMetric I hdim hδ f hf hdisj hs d w b r hfit hstatic).inner q v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace AgreementE3 AgreementQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ AgreementQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
  dsimp only
  intro q hq v z
  let alpha := finiteRetainedPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs R b hb r hfit
  let beta := finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit
  have heq := positive_inner I hdim hδ f hf hdisj hs U g R hRet b hb r hfit d w hstatic hmap
  have hrange : range beta = {q : AgreementPatch | q.val ∈ finiteCoreInterior transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj} :=
    range_finiteCapPositiveMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit
  have hq' : q ∈ range beta := hrange.symm ▸ hq
  obtain ⟨p, hp⟩ := hq'
  have hsurj := finiteCapPositiveMap_mfderiv_surjective I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit p
  obtain ⟨a, ha'⟩ := hsurj v
  obtain ⟨c, hc'⟩ := hsurj z
  have halpha : alpha p = oldOverlapPoint I hdim hδ f hf hdisj R b hb r q hq :=
    Subtype.ext (congrArg (fun x : AgreementPatch => x.val) hp)
  have ht := heq p a c
  dsimp only [beta] at hp
  dsimp only [alpha] at halpha
  dsimp only [TangentSpace] at ha' hc' ht ⊢
  erw [ha', hc', hp, halpha] at ht
  exact ht
end DifferentialGeometry.PDE.RicciFlow.StandardCap
