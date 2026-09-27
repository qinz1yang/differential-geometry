import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricSeam
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricDerivatives
import DifferentialGeometry.Geometry.Curvature.EmbeddingCurvatureJets

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
  DifferentialGeometry.Topology.ThreeManifold.Surgery
  DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
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

theorem finiteFullPreparedMetric_curvature_jets_retainedInterior :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let Ψ := finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet
    ∀ (q : Old) (j : ℕ),
      Real.sqrt (normSq0S gRet (Opens.inclusion inf_le_left q) (4 + j)
        (iterCov gRet 4 (metricRm04 gRet) j (Opens.inclusion inf_le_left q))) =
      Real.sqrt (normSq0S g (Ψ q) (4 + j) (iterCov g 4 (metricRm04 g) j (Ψ q))) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let F := finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet
  have hlocal := isLocalDiffeomorph_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj I Fact.out hs U R hRet
  have hi : _root_.Topology.IsOpenEmbedding F :=
    .of_continuous_injective_isOpenMap hlocal.contMDiff.continuous
      (injective_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet) hlocal.isOpenMap
  let : SecondCountableTopology Old := hi.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace Old := ChartedSpace.locallyCompactSpace E3 Old
  let : SigmaCompactSpace Old := inferInstance
  let old := finiteOldMetric I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let inc : Old → Ret := Opens.inclusion inf_le_left
  have hi' : Injective inc := fun _ _ he => Subtype.ext (congrArg (fun q : Ret => q.val) he)
  have hl : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ inc := by
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (contMDiff_inclusion (n := ∞) (show Old ≤ Ret from inf_le_left)) _ rfl
    intro q
    rw [mfderiv_opens_incl]
    exact fun _ _ he => he
  have hm : ∀ (q : Old) (v z : TangentSpace (𝓡 3) q),
      old.inner q v z = gRet.inner (inc q) (mfderiv (𝓡 3) (𝓡 3) inc q v) (mfderiv (𝓡 3) (𝓡 3) inc q z) := by
    intro q v z
    dsimp only [inc]
    rw [mfderiv_opens_incl]
    exact (finiteGluedMetric_inner_old I hδ f hf hdisj hs U g R hRet
      (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)
      x₀ order d₀ hOriginal hrec d hmap hside w
      (fun b => (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)
      (fun _ => le_rfl) q v z).symm
  dsimp only
  intro q j
  have hglobal := curvature_jets_of_injective_local_isometry old gRet inc hl hi' hm j q
  have horiginal := curvature_jets_of_injective_local_isometry old g F hlocal
    (injective_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet)
    (finiteOldMetric_inner I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet) j q
  exact hglobal.symm.trans horiginal

theorem finiteFullPreparedMetric_curvature_jets_le_of_retained_bound {C : ℕ → ℝ}
    (hw : ∀ b : Boundary, StaticInsertionAdditionalProperties C (w b))
    (K : ℕ → ℝ) (hin : ∀ p : retainedCore f R, ∀ j ≤ m,
      Real.sqrt (normSq0S g (retainedCoreDomainMap f R U hRet p) (4 + j)
        (iterCov g 4 (metricRm04 g) j (retainedCoreDomainMap f R U hRet p))) ≤ K j) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
      x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ (q : Ret) (j : ℕ), j ≤ m →
      Real.sqrt (normSq0S gRet q (4 + j) (iterCov gRet 4 (metricRm04 gRet) j q)) ≤
        max (K j) (sSup (range (fun b : Boundary =>
          C j * (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) ^ (1 + (j : ℝ) / 2)))) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q j hj
  by_cases hold : q.val ∈ finiteCoreInterior transitionEnd_pos hδ f
      (fun i => (hf i).injective) hdisj
  · let p : Old := ⟨q.val, q.property, hold⟩
    have hscalar := finiteFullPreparedMetric_curvature_jets_retainedInterior I hδ f hf hdisj hs
      U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w p j
    have hpoint : Opens.inclusion (show Old ≤ Ret from inf_le_left) p = q := rfl
    rw [hpoint] at hscalar
    rw [hscalar]
    let x := (finiteCoreInteriorHomeomorph transitionEnd_pos hδ f hf hdisj).symm
      (Opens.inclusion inf_le_right p)
    have hxR : (⟨x.val, interior_subset x.property⟩ : cutCore f) ∈ retainedCore f R := by
      change finiteCapComponentLabel transitionEnd_pos hδ f hf hdisj
        (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj x) ∈ R
      rw [finiteRetainedInterior_original_point]
      exact p.property.1
    exact (hin ⟨⟨x.val, interior_subset x.property⟩, hxR⟩ j hj).trans (le_max_left _ _)
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
    have hscalar := finiteFullPreparedMetric_cap_derivatives I hδ f hf hdisj hs U g R hRet
      c hc x₀ order d₀ hOriginal hrec d hmap hside w hw b'
      ((w b').data.capMap x) ⟨x, rfl⟩ j hj
    rw [hplaced] at hscalar
    apply hscalar.trans
    have hsup : C j * (metricScalarAt g
        ((d₀ b'.val.1).offsetPoint (cuttingSign_sq b'.val.2))) ^ (1 + (j : ℝ) / 2) ≤
        sSup (range (fun b : Boundary => C j * (metricScalarAt g
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) ^ (1 + (j : ℝ) / 2))) :=
      le_csSup (Set.finite_range _).bddAbove ⟨b', rfl⟩
    exact hsup.trans (le_max_right _ _)

theorem finiteFullPreparedMetric_curvature_jets_le_of_neck_scale_bound {C : ℕ → ℝ}
    (hw : ∀ b : Boundary, StaticInsertionAdditionalProperties C (w b))
    (hC : ∀ j ≤ m, 0 ≤ C j)
    (hratio : ∀ b : Boundary,
      |metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
        metricScalarAt g (x₀ b.val.1) - 1| ≤ c * precision b.val.1)
    (K : ℕ → ℝ) (Qmax : ℝ) (hQmax : 0 ≤ Qmax)
    (hin : ∀ p : retainedCore f R, ∀ j ≤ m,
      Real.sqrt (normSq0S g (retainedCoreDomainMap f R U hRet p) (4 + j)
        (iterCov g 4 (metricRm04 g) j (retainedCoreDomainMap f R U hRet p))) ≤ K j)
    (hscale : ∀ b : Boundary, metricScalarAt g (x₀ b.val.1) ≤ Qmax) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
      x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ (q : Ret) (j : ℕ), j ≤ m →
      Real.sqrt (normSq0S gRet q (4 + j) (iterCov gRet 4 (metricRm04 gRet) j q)) ≤
        max (K j) (C j * (2 * Qmax) ^ (1 + (j : ℝ) / 2)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q j hj
  apply (finiteFullPreparedMetric_curvature_jets_le_of_retained_bound I hδ f hf hdisj hs
    U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w hw K hin q j hj).trans
  apply max_le_max_left
  rcases isEmpty_or_nonempty Boundary with hempty | hnonempty
  · let _ := hempty
    simp only [Set.range_eq_empty, Real.sSup_empty]
    exact mul_nonneg (hC j hj) (Real.rpow_nonneg (by positivity) _)
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
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (d b).scalar_pos.le hoffset (by positivity : (0 : ℝ) ≤ 1 + (j : ℝ) / 2))
      (hC j hj)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
