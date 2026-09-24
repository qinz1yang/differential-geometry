import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricSeam
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
  DifferentialGeometry.Topology.ThreeManifold.Surgery
  DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f (fun i =>
  _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i)))
  hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Old" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "Boundary" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
variable (x₀ : ι → U) (order : ι → ℕ)
variable (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
variable (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
variable {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
variable (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision
  b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
variable (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
variable (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map =
  (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
variable (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d
  b).retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
  CanonicalStaticInsertionWitness (d b) A hA D m ε)

theorem finiteFullPreparedMetric_scalar_le_of_retained_bound {C : ℕ → ℝ}
    (hw : ∀ b : Boundary, StaticInsertionAdditionalProperties C (w b))
    (K : ℝ) (hin : ∀ p : retainedCore f R,
      metricScalarAt g (retainedCoreDomainMap f R U hRet p) ≤ K) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
      x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : Ret, metricScalarAt gRet q ≤
      max K (sSup (range (fun b : Boundary =>
        C 0 * metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))))) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q
  by_cases hold : q.val ∈ finiteCoreInterior transitionEnd_pos hδ f
      (fun i => (hf i).injective) hdisj
  · let p : Old := ⟨q.val, q.property, hold⟩
    have hscalar := (finiteFullPreparedMetric_curvature_retainedInterior I hδ f hf hdisj hs
      U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w p).1
    change metricScalarAt _ q = _ at hscalar
    rw [hscalar]
    let x := (finiteCoreInteriorHomeomorph transitionEnd_pos hδ f hf hdisj).symm
      (Opens.inclusion inf_le_right p)
    have hxR : (⟨x.val, interior_subset x.property⟩ : cutCore f) ∈ retainedCore f R := by
      change finiteCapComponentLabel transitionEnd_pos hδ f hf hdisj
        (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj x) ∈ R
      rw [finiteRetainedInterior_original_point]
      exact p.property.1
    exact (hin ⟨⟨x.val, interior_subset x.property⟩, hxR⟩).trans (le_max_left _ _)
  · have hcap : q.val ∈ range (finiteCapInclusion transitionEnd_pos hδ f
        (fun i => (hf i).injective) hdisj) := by
      rw [← finiteCap_compl_interior_core transitionEnd_pos hδ f hf hdisj,
        finiteCoreInclusion_interior_range transitionEnd_pos hδ f hf hdisj]
      exact hold
    obtain ⟨⟨b, x⟩, hx⟩ := hcap
    have hb : cuttingSphereComponent hδ f hf hdisj b ∈ R := by
      have hq := q.property
      rw [← hx] at hq
      exact hq
    let b' : Boundary := ⟨b, hb⟩
    have hplaced : finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b'
        ((w b').data.capMap x) = q := by
      rw [(w b').properties.capMap_eq, (w b').properties.capInclusion_eq]
      apply Subtype.ext
      exact (congrArg (fun p : finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj
          b ((c * precision b.1)⁻¹) => p.val)
        (finiteCapFullInsertionDiffeomorph_symm_cap I Fact.out transitionEnd_pos hδ f hf hdisj
          hs b (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).2.le
          (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1 x)).trans hx
    have hscalar := (finiteFullPreparedMetric_witness_scalar I hδ f hf hdisj hs U g R hRet
      c hc x₀ order d₀ hOriginal hrec d hmap hside w hw b').2
      ((w b').data.capMap x) ⟨x, rfl⟩
    rw [hplaced] at hscalar
    apply hscalar.trans
    have hsup : C 0 * metricScalarAt g
        ((d₀ b'.val.1).offsetPoint (cuttingSign_sq b'.val.2)) ≤
        sSup (range (fun b : Boundary => C 0 * metricScalarAt g
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)))) :=
      le_csSup (Set.finite_range _).bddAbove ⟨b', rfl⟩
    exact hsup.trans (le_max_right _ _)

theorem finiteFullPreparedMetric_scalar_le_of_neck_scale_bound {C : ℕ → ℝ}
    (hw : ∀ b : Boundary, StaticInsertionAdditionalProperties C (w b))
    (hC : 0 ≤ C 0)
    (hratio : ∀ b : Boundary,
      |metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
        metricScalarAt g (x₀ b.val.1) - 1| ≤ c * precision b.val.1)
    (K Qmax : ℝ) (hQmax : 0 ≤ Qmax)
    (hin : ∀ p : retainedCore f R,
      metricScalarAt g (retainedCoreDomainMap f R U hRet p) ≤ K)
    (hscale : ∀ b : Boundary, metricScalarAt g (x₀ b.val.1) ≤ Qmax) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
      x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : Ret, metricScalarAt gRet q ≤ max K (2 * C 0 * Qmax) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q
  apply (finiteFullPreparedMetric_scalar_le_of_retained_bound I hδ f hf hdisj hs
    U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w hw K hin q).trans
  apply max_le_max_left
  rcases isEmpty_or_nonempty Boundary with hempty | hnonempty
  · let _ := hempty
    simp only [Set.range_eq_empty, Real.sSup_empty]
    positivity
  · apply csSup_le (Set.range_nonempty _)
    rintro z ⟨b, rfl⟩
    have hQ : 0 < metricScalarAt g (x₀ b.val.1) := (d₀ b.val.1).scalar_pos
    have hsmall : c * precision b.val.1 < 1 := (d b).precision_lt_one
    have hupper : metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
        metricScalarAt g (x₀ b.val.1) ≤ 2 := by
      have hb := (abs_le.mp (hratio b)).2
      linarith
    have hoffset : metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) ≤
        2 * Qmax :=
      ((div_le_iff₀ hQ).mp hupper).trans (mul_le_mul_of_nonneg_left (hscale b) (by norm_num))
    calc
      C 0 * metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) ≤
          C 0 * (2 * Qmax) := mul_le_mul_of_nonneg_left hoffset hC
      _ = 2 * C 0 * Qmax := by ring

end DifferentialGeometry.PDE.RicciFlow.StandardCap
