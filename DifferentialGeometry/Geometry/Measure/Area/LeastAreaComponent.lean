import DifferentialGeometry.Geometry.Measure.Area.LeastAreaAnnulus
import DifferentialGeometry.Geometry.Measure.Area.SpanningComponent

noncomputable section

open Bundle Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem riemannianCurveSpeed_subtypeVal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : TopologicalSpace.Opens M) (γ : ℝ → U) (t : ℝ) :
    riemannianCurveSpeed g (fun s => (γ s : M)) t =
      riemannianCurveSpeed (g.restrictOpen U) γ t := by
  unfold riemannianCurveSpeed
  rw [DifferentialGeometry.mfderiv_subtypeVal_comp (U := U) γ t,
    SmoothRiemannianMetric.restrictOpen_inner]
  rfl

theorem riemannianCurveELength_subtypeVal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : TopologicalSpace.Opens M) (γ : ℝ → U) (a b : ℝ) :
    riemannianCurveELength g (fun t => (γ t : M)) a b =
      riemannianCurveELength (g.restrictOpen U) γ a b := by
  unfold riemannianCurveELength
  apply lintegral_congr
  intro t
  rw [riemannianCurveSpeed_subtypeVal g U γ t]

theorem riemannianCurveLength_subtypeVal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : TopologicalSpace.Opens M) (γ : ℝ → U) (a b : ℝ) :
    riemannianCurveLength g (fun t => (γ t : M)) a b =
      riemannianCurveLength (g.restrictOpen U) γ a b := by
  unfold riemannianCurveLength
  rw [riemannianCurveELength_subtypeVal g U γ a b]

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem nullhomotopic_subtype_mk (U : TopologicalSpace.Opens M)
    (hU : IsClosed (U : Set M)) {γ : freeLoop M} (hsub : ∀ θ, γ θ ∈ U)
    (hγ : γ.Nullhomotopic) :
    (⟨fun θ => ⟨γ θ, hsub θ⟩, γ.continuous.subtype_mk _⟩ : freeLoop ↥U).Nullhomotopic := by
  obtain ⟨q, ⟨H⟩⟩ := hγ
  have hcl : IsClopen (U : Set M) := ⟨hU, U.isOpen⟩
  have hcomp : connectedComponent (γ 0) ⊆ (U : Set M) :=
    hcl.connectedComponent_subset (hsub 0)
  have h0 : H.toContinuousMap (0, 0) = γ 0 := H.apply_zero 0
  have hHU : ∀ p : unitInterval × loopCircle, H.toContinuousMap p ∈ U := fun p =>
    hcomp (map_mem_connectedComponent H.toContinuousMap (0, 0) (γ 0)
      (by rw [h0]; exact mem_connectedComponent) p)
  have hq : q ∈ U := by
    have h1 : H.toContinuousMap (1, 0) = q := H.apply_one 0
    have := hHU (1, 0)
    rwa [h1] at this
  exact ⟨⟨q, hq⟩, ⟨ContinuousMap.Homotopy.mk
    ⟨fun p => ⟨H.toContinuousMap p, hHU p⟩, H.continuous.subtype_mk _⟩
    (fun θ => Subtype.ext (H.apply_zero θ)) (fun θ => Subtype.ext (H.apply_one θ))⟩⟩

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem spanningDiskCompetitors_mapsTo_of_isClosed
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : TopologicalSpace.Opens M}
    (hU : IsClosed (U : Set M)) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ spanningDiskCompetitors g γ) (hsub : ∀ θ, γ θ ∈ U) :
    ∀ z, u z ∈ U := by
  obtain ⟨htrace, _⟩ := hu
  have hcl : IsClopen (U : Set M) := ⟨hU, U.isOpen⟩
  have hcomp : connectedComponent (γ 0) ⊆ (U : Set M) :=
    hcl.connectedComponent_subset (hsub 0)
  intro z
  refine hcomp (map_mem_connectedComponent u (diskBoundary 0) (γ 0) ?_ z)
  have h := congrArg (fun η : freeLoop M => η 0) htrace
  change u (diskBoundary 0) = γ 0 at h
  rw [h]
  exact mem_connectedComponent

def lipschitzContractibleLoopInOpen (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : TopologicalSpace.Opens M) (hU : IsClosed (U : Set M)) (γ : freeLoop M)
    (hγ : γ.Nullhomotopic) (hsub : ∀ θ, γ θ ∈ U) {L : ℝ≥0}
    (hLip : ∀ s t : loopCircle, riemannianEDistOf g (γ s) (γ t) ≤ (L : ℝ≥0∞) * edist s t) :
    lipschitzContractibleLoop (g.restrictOpen U) :=
  ⟨⟨⟨fun θ => ⟨γ θ, hsub θ⟩, γ.continuous.subtype_mk _⟩,
      nullhomotopic_subtype_mk (M := M) U hU hsub hγ⟩, L, fun s t => by
    rw [riemannianEDistOf_restrictOpen_of_isClosed g U hU]
    exact hLip s t⟩

@[simp] theorem lipschitzContractibleLoopInOpen_coe
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : TopologicalSpace.Opens M)
    (hU : IsClosed (U : Set M)) (γ : freeLoop M) (hγ : γ.Nullhomotopic)
    (hsub : ∀ θ, γ θ ∈ U) {L : ℝ≥0}
    (hLip : ∀ s t : loopCircle, riemannianEDistOf g (γ s) (γ t) ≤ (L : ℝ≥0∞) * edist s t)
    (θ : loopCircle) :
    ((lipschitzContractibleLoopInOpen g U hU γ hγ hsub hLip).val.val θ : M) = γ θ := rfl

theorem riemannianLoopDistance_restrictOpen (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : TopologicalSpace.Opens M} (hU : IsClosed (U : Set M)) (γ γ₀ : freeLoop ↥U) :
    riemannianLoopDistance (g.restrictOpen U) γ γ₀ =
      riemannianLoopDistance g
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, M)).comp γ)
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, M)).comp γ₀) := by
  unfold riemannianLoopDistance
  congr 1
  apply iSup_congr
  intro θ
  exact riemannianEDistOf_restrictOpen_of_isClosed g U hU (γ θ) (γ₀ θ)

theorem leastSpanningArea_eq_restrictOpen_of_isClosed [CompactSpace M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : TopologicalSpace.Opens M}
    (hU : IsClosed (U : Set M)) [ConnectedSpace ↥U] [CompactSpace ↥U]
    (γ : freeLoop M) (hγ : γ.Nullhomotopic) (hsub : ∀ θ, γ θ ∈ U) {L : ℝ≥0}
    (hLip : ∀ s t : loopCircle, riemannianEDistOf g (γ s) (γ t) ≤ (L : ℝ≥0∞) * edist s t) :
    leastSpanningArea g ⟨⟨γ, hγ⟩, L, hLip⟩ =
      leastSpanningArea (g.restrictOpen U)
        (lipschitzContractibleLoopInOpen g U hU γ hγ hsub hLip) := by
  set γU := lipschitzContractibleLoopInOpen g U hU γ hγ hsub hLip with hγU
  have hcoe : ∀ θ : loopCircle, ((γU.val.val θ : ↥U) : M) = γ θ :=
    fun θ => lipschitzContractibleLoopInOpen_coe g U hU γ hγ hsub hLip θ
  apply le_antisymm
  · refine le_csInf ((spanningDiskCompetitors_nonempty (g.restrictOpen U)
      γU.property.choose_spec γU.val.property).image _) ?_
    rintro a ⟨v, hv, rfl⟩
    have hloop : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, M)).comp γU.val.val = γ := by
      ext θ
      exact hcoe θ
    have hvM : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, M)).comp v ∈
        spanningDiskCompetitors g γ := by
      have h := spanningDiskCompetitor_open_inclusion g U hv
      rwa [hloop] at h
    have hle := leastSpanningArea_le_competitor g ⟨⟨γ, hγ⟩, L, hLip⟩ hvM
    have harea : riemannianDiskArea g
        ⇑((⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, M)).comp v) =
        riemannianDiskArea (g.restrictOpen U) v := by
      rw [riemannianDiskArea_restrictOpen g U v]
      congr 1
    change leastSpanningArea g ⟨⟨γ, hγ⟩, L, hLip⟩ ≤ riemannianDiskArea (g.restrictOpen U) v
    rw [← harea]
    exact hle
  · refine le_csInf ((spanningDiskCompetitors_nonempty_of_compact g hLip hγ).image _) ?_
    rintro a ⟨u, hu, rfl⟩
    obtain ⟨htrace, L', hL'⟩ := hu
    have him : ∀ z, u z ∈ U :=
      spanningDiskCompetitors_mapsTo_of_isClosed g hU ⟨htrace, L', hL'⟩ hsub
    let v : C(closedDisk, ↥U) := ⟨fun z => ⟨u z, him z⟩, u.continuous.subtype_mk _⟩
    have hv : v ∈ spanningDiskCompetitors (g.restrictOpen U) γU.val.val := by
      refine ⟨?_, L', ?_⟩
      · ext θ
        rw [hcoe θ]
        exact congrArg (fun η : freeLoop M => η θ) htrace
      · intro z w
        rw [riemannianEDistOf_restrictOpen_of_isClosed g U hU]
        exact hL' z w
    have hle := leastSpanningArea_le_competitor (g.restrictOpen U) γU hv
    have harea : riemannianDiskArea g ⇑u = riemannianDiskArea (g.restrictOpen U) v := by
      have hcomp : (Subtype.val ∘ ⇑v : closedDisk → M) = u := by
        funext z
        rfl
      rw [← hcomp, riemannianDiskArea_restrictOpen g U v]
    change leastSpanningArea (g.restrictOpen U) γU ≤ riemannianDiskArea g ⇑u
    rw [harea]
    exact hle

theorem exists_leastSpanningArea_annulus_bound_of_image_subset
    [CompactSpace M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : TopologicalSpace.Opens M}
    (hU : IsClosed (U : Set M)) [ConnectedSpace ↥U] [CompactSpace ↥U] :
    ∃ ρ C : ℝ≥0, 0 < ρ ∧ 0 < C ∧
      ∀ (γ₀ γ₁ : lipschitzContractibleLoop g) (hsub₀ : ∀ θ, γ₀.val.val θ ∈ U)
        (hsub₁ : ∀ θ, γ₁.val.val θ ∈ U),
      riemannianLoopDistance (g.restrictOpen U)
          (lipschitzContractibleLoopInOpen g U hU γ₀.val.val γ₀.val.property hsub₀
            γ₀.property.choose_spec).val.val
          (lipschitzContractibleLoopInOpen g U hU γ₁.val.val γ₁.val.property hsub₁
            γ₁.property.choose_spec).val.val < ρ →
      |leastSpanningArea g γ₀ - leastSpanningArea g γ₁| ≤
        C * riemannianLoopDistance g γ₀.val.val γ₁.val.val *
          (riemannianCurveLength g (fun t => γ₀.val.val (t : loopCircle)) 0 1 +
            riemannianCurveLength g (fun t => γ₁.val.val (t : loopCircle)) 0 1) := by
  obtain ⟨ρ, C, hρ, hC, hann⟩ := exists_leastSpanningArea_annulus_bound (g.restrictOpen U)
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro γ₀ γ₁ hsub₀ hsub₁ hnearU
  set γ₀U := lipschitzContractibleLoopInOpen g U hU γ₀.val.val γ₀.val.property hsub₀
    γ₀.property.choose_spec with hγ₀U
  set γ₁U := lipschitzContractibleLoopInOpen g U hU γ₁.val.val γ₁.val.property hsub₁
    γ₁.property.choose_spec with hγ₁U
  have l₀ : ∀ θ : loopCircle, ((γ₀U.val.val θ : ↥U) : M) = γ₀.val.val θ := by
    intro θ
    rw [hγ₀U]
    exact lipschitzContractibleLoopInOpen_coe g U hU γ₀.val.val γ₀.val.property hsub₀
      γ₀.property.choose_spec θ
  have l₁ : ∀ θ : loopCircle, ((γ₁U.val.val θ : ↥U) : M) = γ₁.val.val θ := by
    intro θ
    rw [hγ₁U]
    exact lipschitzContractibleLoopInOpen_coe g U hU γ₁.val.val γ₁.val.property hsub₁
      γ₁.property.choose_spec θ
  have hL₀ : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, M)).comp γ₀U.val.val = γ₀.val.val := by
    ext θ
    exact l₀ θ
  have hL₁ : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, M)).comp γ₁U.val.val = γ₁.val.val := by
    ext θ
    exact l₁ θ
  have hγ₀ : γ₀ = ⟨⟨γ₀.val.val, γ₀.val.property⟩, γ₀.property.choose,
      γ₀.property.choose_spec⟩ := Subtype.ext rfl
  have hA₀ : leastSpanningArea g γ₀ = leastSpanningArea (g.restrictOpen U) γ₀U := by
    rw [hγ₀, hγ₀U]
    exact leastSpanningArea_eq_restrictOpen_of_isClosed g hU γ₀.val.val γ₀.val.property
      hsub₀ γ₀.property.choose_spec
  have hγ₁ : γ₁ = ⟨⟨γ₁.val.val, γ₁.val.property⟩, γ₁.property.choose,
      γ₁.property.choose_spec⟩ := Subtype.ext rfl
  have hA₁ : leastSpanningArea g γ₁ = leastSpanningArea (g.restrictOpen U) γ₁U := by
    rw [hγ₁, hγ₁U]
    exact leastSpanningArea_eq_restrictOpen_of_isClosed g hU γ₁.val.val γ₁.val.property
      hsub₁ γ₁.property.choose_spec
  have hlen₀ : riemannianCurveLength (g.restrictOpen U)
      (fun t : ℝ => γ₀U.val.val (t : loopCircle)) 0 1 =
      riemannianCurveLength g (fun t : ℝ => γ₀.val.val (t : loopCircle)) 0 1 := by
    rw [← riemannianCurveLength_subtypeVal g U (fun t : ℝ => γ₀U.val.val (t : loopCircle)) 0 1]
    exact congrArg (fun f : ℝ → M => riemannianCurveLength g f 0 1)
      (funext fun t => l₀ (t : loopCircle))
  have hlen₁ : riemannianCurveLength (g.restrictOpen U)
      (fun t : ℝ => γ₁U.val.val (t : loopCircle)) 0 1 =
      riemannianCurveLength g (fun t : ℝ => γ₁.val.val (t : loopCircle)) 0 1 := by
    rw [← riemannianCurveLength_subtypeVal g U (fun t : ℝ => γ₁U.val.val (t : loopCircle)) 0 1]
    exact congrArg (fun f : ℝ → M => riemannianCurveLength g f 0 1)
      (funext fun t => l₁ (t : loopCircle))
  have h := hann γ₀U γ₁U hnearU
  rw [hA₀, hA₁, ← hlen₀, ← hlen₁, ← hL₀, ← hL₁, ← riemannianLoopDistance_restrictOpen g hU]
  exact h

omit [T2Space M] in
theorem leastSpanningArea_nonneg_of_nullhomotopic [CompactSpace M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g) :
    0 ≤ leastSpanningArea g γ := by
  obtain ⟨L, hL⟩ := γ.property
  refine le_csInf ((spanningDiskCompetitors_nonempty_of_compact g hL γ.val.property).image _) ?_
  rintro _ ⟨u, _, rfl⟩
  exact riemannianDiskArea_nonneg g u

end DifferentialGeometry.Geometry
