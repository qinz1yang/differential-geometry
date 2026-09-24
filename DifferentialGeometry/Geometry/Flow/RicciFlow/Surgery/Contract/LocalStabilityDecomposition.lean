import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.LocalStabilityInputWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WorldBridges

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry (SmoothRiemannianMetric euclideanMetric)
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry
  (euclideanMetric_ricciTensor euclideanMetric_metricRm04At_eq_zero)
open DifferentialGeometry.Geometry.Metric (metricDerivNorm_scaleMetric_self)
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem tendsto_zero_max_iff {a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    Tendsto (fun i => max (a i) (b i)) atTop (𝓝 0) ↔
      Tendsto a atTop (𝓝 0) ∧ Tendsto b atTop (𝓝 0) := by
  constructor
  · intro h
    exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
        (fun i => ha i) (fun i => le_max_left _ _),
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
        (fun i => hb i) (fun i => le_max_right _ _)⟩
  · rintro ⟨ha', hb'⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using ha'.add hb') (fun i => ?_) (fun i => ?_)
    · exact le_trans (ha i) (le_max_left _ _)
    · exact max_le (by linarith [hb i]) (by linarith [ha i])

theorem sSup_image_Icc_eq_max {g : ℝ → ℝ} {v δ : ℝ} (hv : 0 < v) (hδ : 0 < δ)
    (hA : BddAbove (g '' Set.Ioc (0 : ℝ) (min v δ)))
    (hB : BddAbove (g '' Set.Icc (min v δ) v)) :
    sSup (g '' Set.Icc (0 : ℝ) v) =
      max (g 0) (max (sSup (g '' Set.Ioc (0 : ℝ) (min v δ)))
        (sSup (g '' Set.Icc (min v δ) v))) := by
  have hmin0 : 0 ≤ min v δ := le_min hv.le hδ.le
  have hminpos : 0 < min v δ := lt_min hv hδ
  have hminv : min v δ ≤ v := min_le_left _ _
  have hIcc : Set.Icc (0 : ℝ) v =
      insert 0 (Set.Ioc (0 : ℝ) (min v δ) ∪ Set.Icc (min v δ) v) := by
    ext u
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro ⟨hu0, huv⟩
      by_cases h0 : u = 0
      · exact Or.inl h0
      · have hpos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm h0)
        by_cases hle : u ≤ min v δ
        · exact Or.inr (Or.inl ⟨hpos, hle⟩)
        · exact Or.inr (Or.inr ⟨(lt_of_not_ge hle).le, huv⟩)
    · intro h
      rcases h with rfl | h | h
      · exact ⟨le_rfl, hv.le⟩
      · exact ⟨h.1.le, h.2.trans hminv⟩
      · exact ⟨hmin0.trans h.1, h.2⟩
  have hneA : (g '' Set.Ioc (0 : ℝ) (min v δ)).Nonempty :=
    ⟨g (min v δ / 2), min v δ / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hneB : (g '' Set.Icc (min v δ) v).Nonempty :=
    ⟨g (min v δ), min v δ, ⟨le_rfl, hminv⟩, rfl⟩
  rw [hIcc, Set.image_insert_eq, Set.image_union,
    csSup_insert (hA.union hB) (hneA.inl), csSup_union hA hneA hB hneB]

theorem sSup_eq_of_const_on_nonempty {s : Set ℝ} (hs : s.Nonempty) {c : ℝ} :
    sSup {r : ℝ | ∃ u ∈ s, c = r} = c := by
  have hset : {r : ℝ | ∃ u ∈ s, c = r} = {c} := by
    ext r
    constructor
    · rintro ⟨u, hu, hcur⟩
      exact hcur.symm
    · intro h
      obtain ⟨u, hu⟩ := hs
      exact ⟨u, hu, h.symm⟩
  rw [hset, csSup_singleton]

def localStabilityTimeZeroJetControl
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m →
    Tendsto (fun i : ℕ => metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric 0)
      (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i)))) atTop (𝓝 0)

def localStabilityInitialWindowJetControl
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) (δ : ℝ) : Prop :=
  ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m →
    Tendsto (fun i : ℕ => sSup {r : ℝ | ∃ u ∈ Set.Ioc (0 : ℝ) (min (v i) δ),
      metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
        (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) = r})
      atTop (𝓝 0)

def localStabilityPositiveSlabJetControl
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) (δ : ℝ) : Prop :=
  ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m →
    Tendsto (fun i : ℕ => sSup {r : ℝ | ∃ u ∈ Set.Icc (min (v i) δ) (v i),
      metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
        (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) = r})
      atTop (𝓝 0)

def localStabilitySlabDerivativeBound
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) (v i),
      metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
        (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) ≤ C

def localStabilityConclusion
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m →
    Tendsto (fun i : ℕ => sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (v i),
      metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
      (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) = r})
      atTop (𝓝 0)


def IsLocalStabilityVanishingInput : Prop :=
  ∀ (θ : ℝ), 0 < θ → θ < 1 → ∀ (K : ℝ), 0 < K →
    ∀ (L : ℕ → ℝ) (_hLpos : ∀ i, 0 < L i) (_hLtop : Tendsto L atTop atTop)
      (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
      (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
      (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
        (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall (L i)),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (L i)))
            ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      localStabilityInitialJetHypothesis L v hv γ ℓ →
      localStabilityConclusion L v hv γ ℓ

def IsLocalStabilitySlabDerivativeBoundInput : Prop :=
  ∀ (θ : ℝ), 0 < θ → θ < 1 → ∀ (K : ℝ), 0 < K →
    ∀ (L : ℕ → ℝ) (_hLpos : ∀ i, 0 < L i) (_hLtop : Tendsto L atTop atTop)
      (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
      (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
      (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
        (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall (L i)),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (L i)))
            ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      localStabilityInitialJetHypothesis L v hv γ ℓ →
      localStabilitySlabDerivativeBound L v hv γ ℓ

def IsLocalStabilityWindowSlabInput (δ : ℝ) : Prop :=
  ∀ (θ : ℝ), 0 < θ → θ < 1 → ∀ (K : ℝ), 0 < K →
    ∀ (L : ℕ → ℝ) (_hLpos : ∀ i, 0 < L i) (_hLtop : Tendsto L atTop atTop)
      (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
      (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
      (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
        (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall (L i)),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (L i)))
            ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      localStabilityInitialJetHypothesis L v hv γ ℓ →
      localStabilityInitialWindowJetControl L v hv γ ℓ δ ∧
        localStabilityPositiveSlabJetControl L v hv γ ℓ δ

theorem localStabilityTimeZeroJetControl_of_initialJetHypothesis
    {L : ℕ → ℝ} {v : ℕ → ℝ} {hv : ∀ i, 0 < v i}
    {γ : SmoothRiemannianMetric ThreeModel ThreeSpace}
    {ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))}
    (h : localStabilityInitialJetHypothesis L v hv γ ℓ) :
    localStabilityTimeZeroJetControl L v hv γ ℓ :=
  fun A hA m _ => h A hA m

theorem localStabilityIntervalSup_eq_max
    {L : ℕ → ℝ} {v : ℕ → ℝ} {hv : ∀ i, 0 < v i}
    {γ : SmoothRiemannianMetric ThreeModel ThreeSpace}
    {ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))}
    (hb : localStabilitySlabDerivativeBound L v hv γ ℓ) {δ : ℝ} (hδ : 0 < δ)
    (A : Set ThreeSpace) (hA : IsCompact A) (m : ℕ) (hm : 4 ≤ m) (i : ℕ) :
    sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (v i),
        metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
          (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) = r} =
      max (metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric 0)
            (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))))
        (max (sSup {r : ℝ | ∃ u ∈ Set.Ioc (0 : ℝ) (min (v i) δ),
            metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
              (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) = r})
          (sSup {r : ℝ | ∃ u ∈ Set.Icc (min (v i) δ) (v i),
            metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
              (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) = r})) := by
  obtain ⟨C, _hC0, hC⟩ := hb A hA m hm
  have hbddA : BddAbove ((fun u : ℝ => metricDerivNormSupOn (Subtype.val ⁻¹' A) m
      ((ℓ i).base.metric u) (γ.restrictOpen (ModelBall (L i)))
      (γ.restrictOpen (ModelBall (L i)))) '' Set.Ioc (0 : ℝ) (min (v i) δ)) := by
    refine ⟨C, ?_⟩
    rintro r ⟨u, hu, rfl⟩
    exact hC i u ⟨hu.1.le, hu.2.trans (min_le_left _ _)⟩
  have hbddB : BddAbove ((fun u : ℝ => metricDerivNormSupOn (Subtype.val ⁻¹' A) m
      ((ℓ i).base.metric u) (γ.restrictOpen (ModelBall (L i)))
      (γ.restrictOpen (ModelBall (L i)))) '' Set.Icc (min (v i) δ) (v i)) := by
    refine ⟨C, ?_⟩
    rintro r ⟨u, hu, rfl⟩
    exact hC i u ⟨(le_min (hv i).le hδ.le).trans hu.1, hu.2⟩
  exact sSup_image_Icc_eq_max (hv i) hδ hbddA hbddB

theorem bddAbove_localStabilityIccValues
    {L : ℕ → ℝ} {v : ℕ → ℝ} {hv : ∀ i, 0 < v i}
    {γ : SmoothRiemannianMetric ThreeModel ThreeSpace}
    {ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))}
    (hb : localStabilitySlabDerivativeBound L v hv γ ℓ)
    (A : Set ThreeSpace) (hA : IsCompact A) (m : ℕ) (hm : 4 ≤ m) (i : ℕ) :
    BddAbove {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (v i),
      metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
        (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) = r} := by
  obtain ⟨C, _hC0, hC⟩ := hb A hA m hm
  exact ⟨C, fun r hr => by
    obtain ⟨u, hu, rfl⟩ := hr
    exact hC i u hu⟩

theorem localStabilityConclusion_iff_of_slabDerivativeBound
    {L : ℕ → ℝ} {v : ℕ → ℝ} {hv : ∀ i, 0 < v i}
    {γ : SmoothRiemannianMetric ThreeModel ThreeSpace}
    {ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))}
    (hb : localStabilitySlabDerivativeBound L v hv γ ℓ) {δ : ℝ} (hδ : 0 < δ) :
    localStabilityConclusion L v hv γ ℓ ↔
      localStabilityTimeZeroJetControl L v hv γ ℓ ∧
        localStabilityInitialWindowJetControl L v hv γ ℓ δ ∧
        localStabilityPositiveSlabJetControl L v hv γ ℓ δ := by
  constructor
  · intro h
    refine ⟨fun A hA m hm => ?_, fun A hA m hm => ?_, fun A hA m hm => ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h A hA m hm)
        (fun i => metricDerivNormSupOn_nonneg _ _ _ _ _) (fun i => ?_)
      exact le_csSup (bddAbove_localStabilityIccValues hb A hA m hm i)
        ⟨0, ⟨le_rfl, (hv i).le⟩, rfl⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h A hA m hm)
        (fun i => Real.sSup_nonneg (fun _ hr => by
          obtain ⟨u, _hu, rfl⟩ := hr
          exact metricDerivNormSupOn_nonneg _ _ _ _ _)) (fun i => ?_)
      refine Real.sSup_le (fun _ hr => ?_) (Real.sSup_nonneg (fun _ hr => by
        obtain ⟨u, _hu, rfl⟩ := hr
        exact metricDerivNormSupOn_nonneg _ _ _ _ _))
      obtain ⟨u, hu, rfl⟩ := hr
      exact le_csSup (bddAbove_localStabilityIccValues hb A hA m hm i)
        ⟨u, ⟨hu.1.le, hu.2.trans (min_le_left _ _)⟩, rfl⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h A hA m hm)
        (fun i => Real.sSup_nonneg (fun _ hr => by
          obtain ⟨u, _hu, rfl⟩ := hr
          exact metricDerivNormSupOn_nonneg _ _ _ _ _)) (fun i => ?_)
      refine Real.sSup_le (fun _ hr => ?_) (Real.sSup_nonneg (fun _ hr => by
        obtain ⟨u, _hu, rfl⟩ := hr
        exact metricDerivNormSupOn_nonneg _ _ _ _ _))
      obtain ⟨u, hu, rfl⟩ := hr
      exact le_csSup (bddAbove_localStabilityIccValues hb A hA m hm i)
        ⟨u, ⟨(le_min (hv i).le hδ.le).trans hu.1, hu.2⟩, rfl⟩
  · rintro ⟨h0, hw, hs⟩ A hA m hm
    refine tendsto_order.2 ⟨fun b hb' => ?_, fun b hb' => ?_⟩
    · filter_upwards with i
      refine lt_of_lt_of_le hb' (Real.sSup_nonneg (fun _ hr => ?_))
      obtain ⟨u, _hu, rfl⟩ := hr
      exact metricDerivNormSupOn_nonneg _ _ _ _ _
    · have hpos : 0 < b / 2 := half_pos hb'
      filter_upwards [(h0 A hA m hm).eventually (Iio_mem_nhds hpos),
        (hw A hA m hm).eventually (Iio_mem_nhds hpos),
        (hs A hA m hm).eventually (Iio_mem_nhds hpos)] with i h1 h2 h3
      rw [localStabilityIntervalSup_eq_max hb hδ A hA m hm i]
      exact lt_of_le_of_lt (max_le h1.le (max_le h2.le h3.le)) (by linarith)

theorem isLocalStabilityVanishingInput_iff_windowSlabInput_of_slabDerivativeBoundInput
    (hb : IsLocalStabilitySlabDerivativeBoundInput) {δ : ℝ} (hδ : 0 < δ) :
    IsLocalStabilityVanishingInput ↔ IsLocalStabilityWindowSlabInput δ := by
  constructor
  · intro h θ hθ hθ1 K hK L hLp hLt v hv hvθ γ ℓ h1 h2 h3
    have hc := (localStabilityConclusion_iff_of_slabDerivativeBound
      (hb θ hθ hθ1 K hK L hLp hLt v hv hvθ γ ℓ h1 h2 h3) hδ).mp
      (h θ hθ hθ1 K hK L hLp hLt v hv hvθ γ ℓ h1 h2 h3)
    exact ⟨hc.2.1, hc.2.2⟩
  · intro h θ hθ hθ1 K hK L hLp hLt v hv hvθ γ ℓ h1 h2 h3
    obtain ⟨hw, hs⟩ := h θ hθ hθ1 K hK L hLp hLt v hv hvθ γ ℓ h1 h2 h3
    exact (localStabilityConclusion_iff_of_slabDerivativeBound
      (hb θ hθ hθ1 K hK L hLp hLt v hv hvθ γ ℓ h1 h2 h3) hδ).mpr
      ⟨localStabilityTimeZeroJetControl_of_initialJetHypothesis h3, hw, hs⟩

theorem isLocalStabilityVanishingInput_of_windowSlabInput_of_slabDerivativeBoundInput
    (hb : IsLocalStabilitySlabDerivativeBoundInput) {δ : ℝ} (hδ : 0 < δ)
    (h : IsLocalStabilityWindowSlabInput δ) : IsLocalStabilityVanishingInput :=
  (isLocalStabilityVanishingInput_iff_windowSlabInput_of_slabDerivativeBoundInput hb hδ).mpr h


def shortEuclideanBallTime (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1 + 1)

theorem shortEuclideanBallTime_pos (i : ℕ) : 0 < shortEuclideanBallTime i := by
  simp only [shortEuclideanBallTime]
  positivity

theorem shortEuclideanBallTime_le_half (i : ℕ) : shortEuclideanBallTime i ≤ 1 / 2 := by
  rw [shortEuclideanBallTime, div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 1 + 1)]
  have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith

theorem tendsto_shortEuclideanBallTime : Tendsto shortEuclideanBallTime atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have heq : (fun i : ℕ => (1 : ℝ) / (((i + 1 : ℕ) : ℝ) + 1)) = shortEuclideanBallTime := by
    funext i
    simp only [shortEuclideanBallTime, Nat.cast_add, Nat.cast_one]
  rw [← heq]
  exact hbase.comp (tendsto_add_atTop_nat 1)

noncomputable abbrev constantBallSolution (i : ℕ) :
    SolutionOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (RealTimeInterval.closed (0 : ℝ) (flatBallTime i) (le_of_lt (flatBallTime_pos i))) :=
  SolutionOn.const (flatBallMetric (flatBallRadius i))
    (RealTimeInterval.closed (0 : ℝ) (flatBallTime i) (le_of_lt (flatBallTime_pos i)))

@[simp] theorem constantBallSolution_base_metric (i : ℕ) (u : ℝ) :
    (constantBallSolution i).base.metric u = flatBallMetric (flatBallRadius i) :=
  rfl

theorem isSolutionOn_constantBallSolution (i : ℕ) : IsSolutionOn (constantBallSolution i) :=
  isSolutionOn_const_of_ricciTensor_eq_zero (flatBallMetric (flatBallRadius i))
    (fun x v w => ricciTensor_flatBallMetric_eq_zero (flatBallRadius i) x v w)
    (RealTimeInterval.closed (0 : ℝ) (flatBallTime i) (le_of_lt (flatBallTime_pos i)))

theorem curvatureNormSq_constantBallSolution_le (i : ℕ)
    (x : ↥(ModelBall (flatBallRadius i))) :
    curvatureNormSq ((constantBallSolution i).base.metric (flatBallTime i)) x
      (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
        ((constantBallSolution i).base.metric (flatBallTime i)) x) ≤ (1 : ℝ) ^ 2 :=
  curvatureNormSq_flatBallSolution_le i x

theorem metricDerivNormSupOn_constantBallSolution_eq_zero (i : ℕ) (A : Set ThreeSpace)
    (m : ℕ) (u : ℝ) :
    metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' A) m ((constantBallSolution i).base.metric u)
      (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) = 0 := by
  rw [constantBallSolution_base_metric]
  exact metricDerivNormSupOn_self (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
    (Subtype.val ⁻¹' A) m _ _

theorem constantBall_metricDerivNormSupOn_tendsto_zero :
    localStabilityInitialJetHypothesis flatBallRadius flatBallTime flatBallTime_pos
      (euclideanMetric (E := ThreeSpace)) constantBallSolution := by
  intro A _ p
  have h : (fun i : ℕ => metricDerivNormSupOn (I := ThreeModel)
        (M := ↥(ModelBall (flatBallRadius i))) (Subtype.val ⁻¹' A) p
        ((constantBallSolution i).base.metric 0)
        ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
        ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i))))
      = fun _ => (0 : ℝ) := by
    funext i
    simpa only [flatBallMetric] using metricDerivNormSupOn_constantBallSolution_eq_zero i A p 0
  rw [h]
  exact tendsto_const_nhds

theorem constantBall_localStability_tendsto :
    localStabilityConclusion flatBallRadius flatBallTime flatBallTime_pos
      (euclideanMetric (E := ThreeSpace)) constantBallSolution := by
  intro A _ m _
  have h : (fun i : ℕ => sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
        metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
          (Subtype.val ⁻¹' A) m ((constantBallSolution i).base.metric u)
          ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
          ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i))) = r})
      = fun _ => (0 : ℝ) := by
    funext i
    have hset : {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
        metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
          (Subtype.val ⁻¹' A) m ((constantBallSolution i).base.metric u)
          ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
          ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i))) = r}
        = {0} := by
      ext r
      constructor
      · rintro ⟨u, _hu, hr⟩
        rw [← hr, Set.mem_singleton_iff]
        simpa only [flatBallMetric] using
          metricDerivNormSupOn_constantBallSolution_eq_zero i A m u
      · intro hr
        rw [Set.mem_singleton_iff] at hr
        subst hr
        exact ⟨0, ⟨le_rfl, (flatBallTime_pos i).le⟩,
          by simpa only [flatBallMetric] using
            metricDerivNormSupOn_constantBallSolution_eq_zero i A m 0⟩
    rw [hset, csSup_singleton]
  rw [h]
  exact tendsto_const_nhds

theorem constantBall_localStabilitySlabDerivativeBound :
    localStabilitySlabDerivativeBound flatBallRadius flatBallTime flatBallTime_pos
      (euclideanMetric (E := ThreeSpace)) constantBallSolution := by
  intro A _ m _
  refine ⟨1, by norm_num, fun i u _ => ?_⟩
  have h0 : metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' A) m ((constantBallSolution i).base.metric u)
      ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
      ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i))) = 0 := by
    simpa only [flatBallMetric] using metricDerivNormSupOn_constantBallSolution_eq_zero i A m u
  rw [h0]
  norm_num

noncomputable abbrev shortScaledBallSolution (i : ℕ) :
    SolutionOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (RealTimeInterval.closed (0 : ℝ) (shortEuclideanBallTime i)
        (le_of_lt (shortEuclideanBallTime_pos i))) :=
  SolutionOn.const (flatBallScaledMetric (flatBallRadius i) (flatBallRescale i)
      (flatBallRescale_pos i))
    (RealTimeInterval.closed (0 : ℝ) (shortEuclideanBallTime i)
      (le_of_lt (shortEuclideanBallTime_pos i)))

@[simp] theorem shortScaledBallSolution_base_metric (i : ℕ) (u : ℝ) :
    (shortScaledBallSolution i).base.metric u
      = flatBallScaledMetric (flatBallRadius i) (flatBallRescale i)
        (flatBallRescale_pos i) :=
  rfl

theorem isSolutionOn_shortScaledBallSolution (i : ℕ) :
    IsSolutionOn (shortScaledBallSolution i) :=
  isSolutionOn_const_of_ricciTensor_eq_zero
    (flatBallScaledMetric (flatBallRadius i) (flatBallRescale i) (flatBallRescale_pos i))
    (fun x v w => ricciTensor_flatBallScaledMetric_eq_zero (flatBallRadius i)
      (flatBallRescale i) (flatBallRescale_pos i) x v w)
    (RealTimeInterval.closed (0 : ℝ) (shortEuclideanBallTime i)
      (le_of_lt (shortEuclideanBallTime_pos i)))

theorem curvatureNormSq_shortScaledBallSolution_le (i : ℕ)
    (x : ↥(ModelBall (flatBallRadius i))) :
    curvatureNormSq ((shortScaledBallSolution i).base.metric (shortEuclideanBallTime i)) x
      (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
        ((shortScaledBallSolution i).base.metric (shortEuclideanBallTime i)) x)
      ≤ (1 : ℝ) ^ 2 := by
  have hz : Tensor0SBundle.normSq0S (I := ThreeModel)
      (M := ↥(ModelBall (flatBallRadius i)))
      (flatBallScaledMetric (flatBallRadius i) (flatBallRescale i) (flatBallRescale_pos i)) x 4
      (0 : Tensor0SBundle.Tensor0SSpace 4 ThreeModel x) = 0 :=
    (Tensor0SBundle.normSq0S_eq_zero_iff _ _ _ _).mpr rfl
  rw [shortScaledBallSolution_base_metric, metricRm04At_flatBallScaledMetric_eq_zero,
    curvatureNormSq, hz]
  norm_num

theorem metricDerivNormSupOn_shortScaledBallSolution_le (i : ℕ) (A : Set ThreeSpace)
    (m : ℕ) (u : ℝ) :
    metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' A) m ((shortScaledBallSolution i).base.metric u)
      (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i))
      ≤ |flatBallRescale i - 1| * Real.sqrt (Module.finrank ℝ ThreeSpace) := by
  rw [shortScaledBallSolution_base_metric]
  exact metricDerivNormSupOn_flatBallScaledMetric_le (flatBallRadius i) (flatBallRescale i)
    (flatBallRescale_pos i) (Subtype.val ⁻¹' A) m

theorem shortScaledBall_metricDerivNormSupOn_tendsto_zero :
    localStabilityInitialJetHypothesis flatBallRadius shortEuclideanBallTime
      shortEuclideanBallTime_pos (euclideanMetric (E := ThreeSpace)) shortScaledBallSolution := by
  intro A _ p
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_flatBallScaledFactor (fun i => metricDerivNormSupOn_nonneg _ _ _ _ _) (fun i => ?_)
  simpa only [flatBallMetric] using metricDerivNormSupOn_shortScaledBallSolution_le i A p 0

theorem shortScaledBall_localStability_tendsto :
    localStabilityConclusion flatBallRadius shortEuclideanBallTime shortEuclideanBallTime_pos
      (euclideanMetric (E := ThreeSpace)) shortScaledBallSolution := by
  intro A _ m _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_flatBallScaledFactor (fun i => Real.sSup_nonneg (fun _ hr => by
      obtain ⟨u, _hu, rfl⟩ := hr
      exact metricDerivNormSupOn_nonneg _ _ _ _ _)) (fun i => ?_)
  refine Real.sSup_le (fun _ hr => ?_) (by positivity)
  obtain ⟨u, _hu, rfl⟩ := hr
  simpa only [flatBallMetric] using metricDerivNormSupOn_shortScaledBallSolution_le i A m u

theorem shortScaledBall_localStabilitySlabDerivativeBound :
    localStabilitySlabDerivativeBound flatBallRadius shortEuclideanBallTime
      shortEuclideanBallTime_pos (euclideanMetric (E := ThreeSpace)) shortScaledBallSolution := by
  intro A _ m _
  refine ⟨2, by norm_num, fun i u _ => ?_⟩
  have habs : |flatBallRescale i - 1| ≤ 1 := by
    rw [flatBallRescale_sub_one,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / ((i : ℝ) + 1))]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))]
  have hsqrt : Real.sqrt (Module.finrank ℝ ThreeSpace) ≤ 2 := by
    rw [finrank_threeSpace_eq_three, Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num⟩
  have hstep : |flatBallRescale i - 1| * Real.sqrt (Module.finrank ℝ ThreeSpace) ≤ 2 :=
    (mul_le_mul habs hsqrt (Real.sqrt_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hbound : metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' A) m
      (flatBallScaledMetric (flatBallRadius i) (flatBallRescale i) (flatBallRescale_pos i))
      (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) ≤ 2 :=
    (metricDerivNormSupOn_flatBallScaledMetric_le (flatBallRadius i) (flatBallRescale i)
      (flatBallRescale_pos i) (Subtype.val ⁻¹' A) m).trans hstep
  rw [shortScaledBallSolution_base_metric]
  simpa only [flatBallMetric] using hbound

theorem modelBall_halfBall_nonempty (L : ℝ) (hL : 0 < L) :
    (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2) :
      Set ↥(ModelBall L)).Nonempty :=
  ⟨⟨(0 : ThreeSpace), Metric.mem_ball_self (x := (0 : ThreeSpace)) (ε := L) hL⟩,
    Metric.mem_closedBall_self (x := (0 : ThreeSpace)) (ε := (1 / 2 : ℝ)) (by norm_num)⟩

theorem shortScaledBall_conclusion_sup_pos (i : ℕ) :
    0 < sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (shortEuclideanBallTime i),
      metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
        (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
        ((shortScaledBallSolution i).base.metric u)
        (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) = r} := by
  obtain ⟨y, hy⟩ := modelBall_halfBall_nonempty (flatBallRadius i) (flatBallRadius_pos i)
  have hbdd : BddAbove {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (shortEuclideanBallTime i),
      metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
        (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
        ((shortScaledBallSolution i).base.metric u)
        (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) = r} :=
    ⟨2, fun r hr => by
      obtain ⟨u, _hu, rfl⟩ := hr
      have := metricDerivNormSupOn_flatBallScaledMetric_le (flatBallRadius i)
        (flatBallRescale i) (flatBallRescale_pos i)
        (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
      rw [shortScaledBallSolution_base_metric]
      refine this.trans ?_
      have habs : |flatBallRescale i - 1| ≤ 1 := by
        rw [flatBallRescale_sub_one,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / ((i : ℝ) + 1))]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
        linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))]
      have hsqrt : Real.sqrt (Module.finrank ℝ ThreeSpace) ≤ 2 := by
        rw [finrank_threeSpace_eq_three, Real.sqrt_le_iff]
        exact ⟨by norm_num, by norm_num⟩
      exact (mul_le_mul habs hsqrt (Real.sqrt_nonneg _) (by norm_num)).trans_eq (by norm_num)⟩
  have hmem : metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
      ((shortScaledBallSolution i).base.metric 0)
      (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) ∈
      {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (shortEuclideanBallTime i),
        metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
          (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
          ((shortScaledBallSolution i).base.metric u)
          (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) = r} :=
    ⟨0, ⟨le_rfl, (shortEuclideanBallTime_pos i).le⟩, rfl⟩
  have hpos : 0 < metricDerivNormSupOn (I := ThreeModel)
      (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
      ((shortScaledBallSolution i).base.metric 0)
      (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) := by
    rw [shortScaledBallSolution_base_metric]
    exact metricDerivNormSupOn_flatBallScaledMetric_pos i 4 ⟨y, hy⟩
  exact lt_of_lt_of_le hpos (le_csSup hbdd hmem)

noncomputable abbrev twoScaledBallSolution (i : ℕ) :
    SolutionOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (RealTimeInterval.closed (0 : ℝ) (flatBallTime i) (le_of_lt (flatBallTime_pos i))) :=
  SolutionOn.const (flatBallScaledMetric (flatBallRadius i) 2 (by norm_num))
    (RealTimeInterval.closed (0 : ℝ) (flatBallTime i) (le_of_lt (flatBallTime_pos i)))

@[simp] theorem twoScaledBallSolution_base_metric (i : ℕ) (u : ℝ) :
    (twoScaledBallSolution i).base.metric u
      = flatBallScaledMetric (flatBallRadius i) 2 (by norm_num) :=
  rfl

theorem isSolutionOn_twoScaledBallSolution (i : ℕ) : IsSolutionOn (twoScaledBallSolution i) :=
  isSolutionOn_const_of_ricciTensor_eq_zero
    (flatBallScaledMetric (flatBallRadius i) 2 (by norm_num))
    (fun x v w => ricciTensor_flatBallScaledMetric_eq_zero (flatBallRadius i) 2
      (by norm_num) x v w)
    (RealTimeInterval.closed (0 : ℝ) (flatBallTime i) (le_of_lt (flatBallTime_pos i)))

theorem curvatureNormSq_twoScaledBallSolution_le (i : ℕ)
    (x : ↥(ModelBall (flatBallRadius i))) :
    curvatureNormSq ((twoScaledBallSolution i).base.metric (flatBallTime i)) x
      (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
        ((twoScaledBallSolution i).base.metric (flatBallTime i)) x) ≤ (1 : ℝ) ^ 2 := by
  have hz : Tensor0SBundle.normSq0S (I := ThreeModel)
      (M := ↥(ModelBall (flatBallRadius i)))
      (flatBallScaledMetric (flatBallRadius i) 2 (by norm_num)) x 4
      (0 : Tensor0SBundle.Tensor0SSpace 4 ThreeModel x) = 0 :=
    (Tensor0SBundle.normSq0S_eq_zero_iff _ _ _ _).mpr rfl
  rw [twoScaledBallSolution_base_metric, metricRm04At_flatBallScaledMetric_eq_zero,
    curvatureNormSq, hz]
  norm_num

theorem metricDerivNormSupOn_twoScaledBallSolution_eq_sqrt_three (i : ℕ) :
    metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 0
      ((twoScaledBallSolution i).base.metric 0)
      ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
      ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
      = Real.sqrt 3 := by
  obtain ⟨y, hy⟩ := modelBall_halfBall_nonempty (flatBallRadius i) (flatBallRadius_pos i)
  have h : metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 0
      (flatBallScaledMetric (flatBallRadius i) 2 (by norm_num))
      (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) = Real.sqrt 3 := by
    rw [metricDerivNormSupOn_flatBallScaledMetric_eq (flatBallRadius i) 2 (by norm_num)
      (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) ⟨y, hy⟩ 0,
      finrank_threeSpace_eq_three]
    norm_num
  rw [twoScaledBallSolution_base_metric]
  simpa only [flatBallMetric] using h

theorem metricDerivNormSupOn_twoScaledBallSolution_eq_sqrt_three_four (i : ℕ)
    (u : ℝ) :
    metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
      ((twoScaledBallSolution i).base.metric u)
      ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
      ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
      = Real.sqrt 3 := by
  obtain ⟨y, hy⟩ := modelBall_halfBall_nonempty (flatBallRadius i) (flatBallRadius_pos i)
  have h : metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
      (flatBallScaledMetric (flatBallRadius i) 2 (by norm_num))
      (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) = Real.sqrt 3 := by
    rw [metricDerivNormSupOn_flatBallScaledMetric_eq (flatBallRadius i) 2 (by norm_num)
      (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) ⟨y, hy⟩ 4,
      finrank_threeSpace_eq_three]
    norm_num
  rw [twoScaledBallSolution_base_metric]
  simpa only [flatBallMetric] using h

theorem exists_localStability_input_witness :
    ∃ (θ K : ℝ), 0 < θ ∧ θ < 1 ∧ 0 < K ∧
      ∃ L : ℕ → ℝ, (∀ i, 0 < L i) ∧ Tendsto L atTop atTop ∧
        ∃ (v : ℕ → ℝ) (hv : ∀ i, 0 < v i), (∀ i, v i ≤ θ) ∧
          ∃ γ : SmoothRiemannianMetric ThreeModel ThreeSpace,
            ∃ ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
              (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i))),
              (∀ i, IsSolutionOn (ℓ i)) ∧
              (∀ i, ∀ x : ↥(ModelBall (L i)),
                curvatureNormSq ((ℓ i).base.metric (v i)) x
                  (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (L i)))
                    ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) ∧
              localStabilityInitialJetHypothesis L v hv γ ℓ ∧
              localStabilitySlabDerivativeBound L v hv γ ℓ ∧
              localStabilityConclusion L v hv γ ℓ := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, flatBallRadius,
    flatBallRadius_pos, tendsto_flatBallRadius_atTop, flatBallTime, flatBallTime_pos,
    flatBallTime_le_half, euclideanMetric (E := ThreeSpace), constantBallSolution,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact isSolutionOn_constantBallSolution
  · exact curvatureNormSq_constantBallSolution_le
  · exact constantBall_metricDerivNormSupOn_tendsto_zero
  · exact constantBall_localStabilitySlabDerivativeBound
  · exact constantBall_localStability_tendsto

theorem exists_localStability_vanishingDuration_witness :
    ∃ (θ K : ℝ), 0 < θ ∧ θ < 1 ∧ 0 < K ∧
      ∃ L : ℕ → ℝ, (∀ i, 0 < L i) ∧ Tendsto L atTop atTop ∧
        ∃ (v : ℕ → ℝ) (hv : ∀ i, 0 < v i),
          (∀ i, v i ≤ θ) ∧ Tendsto v atTop (𝓝 0) ∧
          ∃ γ : SmoothRiemannianMetric ThreeModel ThreeSpace,
            ∃ ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
              (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i))),
              (∀ i, IsSolutionOn (ℓ i)) ∧
              (∀ i, ∀ x : ↥(ModelBall (L i)),
                curvatureNormSq ((ℓ i).base.metric (v i)) x
                  (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (L i)))
                    ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) ∧
              localStabilityInitialJetHypothesis L v hv γ ℓ ∧
              localStabilitySlabDerivativeBound L v hv γ ℓ ∧
              localStabilityConclusion L v hv γ ℓ := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, flatBallRadius,
    flatBallRadius_pos, tendsto_flatBallRadius_atTop, shortEuclideanBallTime,
    shortEuclideanBallTime_pos, shortEuclideanBallTime_le_half, tendsto_shortEuclideanBallTime,
    euclideanMetric (E := ThreeSpace), shortScaledBallSolution, ?_, ?_, ?_, ?_, ?_⟩
  · exact isSolutionOn_shortScaledBallSolution
  · exact curvatureNormSq_shortScaledBallSolution_le
  · exact shortScaledBall_metricDerivNormSupOn_tendsto_zero
  · exact shortScaledBall_localStabilitySlabDerivativeBound
  · exact shortScaledBall_localStability_tendsto

theorem exists_localStability_hypotheses_not_conclusion :
    ∃ (θ K : ℝ), 0 < θ ∧ θ < 1 ∧ 0 < K ∧
      ∃ L : ℕ → ℝ, (∀ i, 0 < L i) ∧ Tendsto L atTop atTop ∧
        ∃ (v : ℕ → ℝ) (hv : ∀ i, 0 < v i), (∀ i, v i ≤ θ) ∧
          ∃ γ : SmoothRiemannianMetric ThreeModel ThreeSpace,
            ∃ ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
              (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i))),
              (∀ i, IsSolutionOn (ℓ i)) ∧
              (∀ i, ∀ x : ↥(ModelBall (L i)),
                curvatureNormSq ((ℓ i).base.metric (v i)) x
                  (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (L i)))
                    ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) ∧
              ¬ localStabilityInitialJetHypothesis L v hv γ ℓ ∧
              ¬ localStabilityConclusion L v hv γ ℓ := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, flatBallRadius,
    flatBallRadius_pos, tendsto_flatBallRadius_atTop, flatBallTime, flatBallTime_pos,
    flatBallTime_le_half, euclideanMetric (E := ThreeSpace), twoScaledBallSolution,
    ?_, ?_, ?_, ?_⟩
  · exact isSolutionOn_twoScaledBallSolution
  · exact curvatureNormSq_twoScaledBallSolution_le
  · intro hjet
    have hA : IsCompact (Metric.closedBall (0 : ThreeSpace) (1 / 2)) :=
      isCompact_closedBall (0 : ThreeSpace) (1 / 2)
    have htend := hjet (Metric.closedBall (0 : ThreeSpace) (1 / 2)) hA 0
    have hval : (fun i : ℕ => metricDerivNormSupOn (I := ThreeModel)
        (M := ↥(ModelBall (flatBallRadius i)))
        (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 0
        ((twoScaledBallSolution i).base.metric 0)
        ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
        ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i))))
        = fun _ : ℕ => Real.sqrt 3 := by
      funext i
      exact metricDerivNormSupOn_twoScaledBallSolution_eq_sqrt_three i
    rw [hval] at htend
    exact absurd (tendsto_nhds_unique tendsto_const_nhds htend)
      (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)).ne'
  · intro hcon
    have hA : IsCompact (Metric.closedBall (0 : ThreeSpace) (1 / 2)) :=
      isCompact_closedBall (0 : ThreeSpace) (1 / 2)
    have htend := hcon (Metric.closedBall (0 : ThreeSpace) (1 / 2)) hA 4 le_rfl
    have hval : (fun i : ℕ => sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
        metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
          (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
          ((twoScaledBallSolution i).base.metric u)
          ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
          ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i))) = r})
        = fun _ : ℕ => Real.sqrt 3 := by
      funext i
      have hset : {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
          metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall (flatBallRadius i)))
            (Subtype.val ⁻¹' Metric.closedBall (0 : ThreeSpace) (1 / 2)) 4
            ((twoScaledBallSolution i).base.metric u)
            ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i)))
            ((euclideanMetric (E := ThreeSpace)).restrictOpen (ModelBall (flatBallRadius i))) = r} =
          {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i), Real.sqrt 3 = r} := by
        ext r
        constructor
        · rintro ⟨u, hu, hru⟩
          exact ⟨u, hu,
            (metricDerivNormSupOn_twoScaledBallSolution_eq_sqrt_three_four i u).symm.trans hru⟩
        · rintro ⟨u, hu, hru⟩
          exact ⟨u, hu,
            (metricDerivNormSupOn_twoScaledBallSolution_eq_sqrt_three_four i u).trans hru⟩
      rw [hset, sSup_eq_of_const_on_nonempty (s := Set.Icc (0 : ℝ) (flatBallTime i))
        ⟨0, ⟨le_rfl, (flatBallTime_pos i).le⟩⟩]
    rw [hval] at htend
    exact absurd (tendsto_nhds_unique tendsto_const_nhds htend)
      (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)).ne'
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
