import DifferentialGeometry.Geometry.Hyperbolic.HaarCovolume
import DifferentialGeometry.Geometry.Hyperbolic.IsometryDescent
import DifferentialGeometry.Geometry.Hyperbolic.HomotopyIsometryLift
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Centralizer
import DifferentialGeometry.Geometry.Metric.Isometry.Covering
import DifferentialGeometry.Geometry.Hyperbolic.UniversalCoverMetric
import DifferentialGeometry.Geometry.Hyperbolic.ThickPart
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryNonElementary
import DifferentialGeometry.Geometry.Hyperbolic.Rigidity.MostowPrasad
import Mathlib.Topology.DiscreteSubset

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal
open DifferentialGeometry.ProjectiveOrthogonalGroup
open MeasureTheory

namespace DifferentialGeometry.Hyperboloid

local notation "H3" => Hyperboloid (EuclideanSpace ℝ (Fin 3))

private theorem exists_equivariant_isometry_of_projective_lattice_isomorphism
    {G K : Type*} [Group G] [Group K]
    (ρ : G →* (H3 ≃ᵢ H3)) (σ : K →* (H3 ≃ᵢ H3))
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ) (φ : G ≃* K)
    (hdiscρ : IsDiscrete (SetLike.coe ((projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp ρ).range))
    (hdiscσ : IsDiscrete (SetLike.coe ((projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp σ).range))
    [HasFundamentalDomain ((projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp ρ).range (PO 3 1)]
    [HasFundamentalDomain ((projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp σ).range (PO 3 1)]
    (hvolρ : covolume ((projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp ρ).range (PO 3 1) ≠ ⊤)
    (hvolσ : covolume ((projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp σ).range (PO 3 1) ≠ ⊤) :
    ∃ e : H3 ≃ᵢ H3,
      (∀ γ : G, σ (φ γ) = e * ρ γ * e⁻¹) ∧
      ∀ (γ : G) (x : H3), e (ρ γ x) = σ (φ γ) (e x) := by
  let ρ' := (projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp ρ
  let σ' := (projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp σ
  let a : G ≃* ρ'.range := MonoidHom.ofInjective (f := ρ') ((projectiveOrthogonalGroupEquiv 2).toMulEquiv.injective.comp hρ)
  let b : K ≃* σ'.range := MonoidHom.ofInjective (f := σ') ((projectiveOrthogonalGroupEquiv 2).toMulEquiv.injective.comp hσ)
  let f : ρ'.range ≃* σ'.range := a.symm.trans (φ.trans b)
  obtain ⟨g, hg⟩ := DifferentialGeometry.ProjectiveOrthogonalGroup.mostow_rigidity 3 (by norm_num) ρ'.range σ'.range
    hdiscρ hdiscσ hvolρ hvolσ f
  let e : H3 ≃ᵢ H3 := (projectiveOrthogonalGroupEquiv 2).toMulEquiv.symm g
  have hconj (γ : G) : σ (φ γ) = e * ρ γ * e⁻¹ := by
    apply (projectiveOrthogonalGroupEquiv 2).toMulEquiv.injective
    have h := hg ⟨ρ' γ, ⟨γ, rfl⟩⟩
    change (projectiveOrthogonalGroupEquiv 2).toMulEquiv (σ (φ (a.symm (a γ)))) = g * (projectiveOrthogonalGroupEquiv 2).toMulEquiv (ρ γ) * g⁻¹ at h
    rw [a.symm_apply_apply] at h
    simpa only [e, map_mul, map_inv, (projectiveOrthogonalGroupEquiv 2).toMulEquiv.apply_symm_apply] using h
  refine ⟨e, hconj, ?_⟩
  intro γ x
  rw [hconj]
  change e (ρ γ x) = e (ρ γ (e.symm (e x)))
  rw [e.symm_apply_apply]

end DifferentialGeometry.Hyperboloid

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  [ConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
  [LocallyPathConnectedSpace Y] [SemilocallySimplyConnectedSpace Y]

private theorem isometry_eq_of_homotopic_of_compact_thick_part
    (u : C(X, Y)) (x₀ : X)
    (eX : Hyperboloid E ≃ₜ @UniversalCover X _ ⟨x₀⟩)
    (eY : Hyperboloid F ≃ₜ @UniversalCover Y _ ⟨u x₀⟩)
    (hXball : ∀ x r, 0 < r →
      (fun z => @proj X _ ⟨x₀⟩ (eX z)) '' Metric.ball x r =
        Metric.eball (@proj X _ ⟨x₀⟩ (eX x)) (ENNReal.ofReal r))
    (hYball : ∀ y r, 0 < r →
      (fun z => @proj Y _ ⟨u x₀⟩ (eY z)) '' Metric.ball y r =
        Metric.eball (@proj Y _ ⟨u x₀⟩ (eY y)) (ENNReal.ofReal r))
    (ρ : FundamentalGroup X x₀ →* (Hyperboloid E ≃ᵢ Hyperboloid E))
    (hρ : ∀ (γ : FundamentalGroup X x₀) (z : Hyperboloid E),
      eX (ρ γ z) = @deckAct X _ ⟨x₀⟩ γ (eX z))
    (hthick : ∀ δ : ℝ, 0 < δ →
      IsCompact ((Quotient.mk (MulAction.orbitRel ρ.range (Hyperboloid E))) ''
        {x : Hyperboloid E | ∀ γ : ρ.range, γ ≠ 1 →
          δ ≤ dist x ((γ : Hyperboloid E ≃ᵢ Hyperboloid E) x)}))
    (hno : ¬ ∃ ξ : Metric.sphere (0 : E) 1,
      ∀ γ : ρ.range, Hyperboloid.boundaryHomeomorph
        (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ)
    (a b : X ≃ᵢ Y) (ha : u.Homotopic (a : C(X, Y)))
    (hb : u.Homotopic (b : C(X, Y))) : a = b := by
  let q : Hyperboloid E → X := fun z => @proj X _ ⟨x₀⟩ (eX z)
  have hq : IsCoveringMap q :=
    (@proj_isCoveringMap X _ ⟨x₀⟩ _ _).comp_homeomorph eX
  let _ : ConnectedSpace (Hyperboloid E) :=
    (Hyperboloid.spaceHomeomorph (E := E)).symm.surjective.connectedSpace
      (Hyperboloid.spaceHomeomorph (E := E)).symm.continuous
  have hpres (γ : ρ.range) (z : Hyperboloid E) :
      q ((γ : Hyperboloid E ≃ᵢ Hyperboloid E) z) = q z := by
    obtain ⟨η, hη⟩ := γ.property
    rw [← hη]
    change @proj X _ ⟨x₀⟩ (eX (ρ η z)) = @proj X _ ⟨x₀⟩ (eX z)
    rw [hρ]
    rfl
  let _ : DiscreteTopology ρ.range :=
    IsometryEquiv.discreteTopology_subgroup_of_isCoveringMap hq ρ.range hpres
  have hfree (γ : ρ.range) (hγ : γ ≠ 1) (z : Hyperboloid E)
      (hz : (γ : Hyperboloid E ≃ᵢ Hyperboloid E) z = z) : False := by
    have heq : ((γ : Hyperboloid E ≃ᵢ Hyperboloid E) : Hyperboloid E → Hyperboloid E) = id :=
      hq.eq_of_comp_eq (γ : Hyperboloid E ≃ᵢ Hyperboloid E).continuous
        continuous_id (funext (hpres γ)) z hz
    apply hγ
    apply Subtype.ext
    apply IsometryEquiv.ext
    exact congrFun heq
  obtain ⟨Ha⟩ := ha
  obtain ⟨Hb⟩ := hb
  obtain ⟨f, _, hfproj, hfmark⟩ :=
    exists_isometryEquiv_mapHomotopyEndpoint u a Ha x₀ eX eY hXball hYball
  obtain ⟨g, _, hgproj, hgmark⟩ :=
    exists_isometryEquiv_mapHomotopyEndpoint u b Hb x₀ eX eY hXball hYball
  have hsource (γ : FundamentalGroup X x₀) (z : Hyperboloid E) :
      eX.symm (@deckAct X _ ⟨x₀⟩ γ (eX z)) = ρ γ z := by
    rw [← hρ, eX.symm_apply_apply]
  have hf (γ : FundamentalGroup X x₀) (z : Hyperboloid E) :
      f (ρ γ z) =
        eY.symm (@deckAct Y _ ⟨u x₀⟩ (FundamentalGroup.map u x₀ γ) (eY (f z))) := by
    simpa only [hsource] using hfmark γ z
  have hg (γ : FundamentalGroup X x₀) (z : Hyperboloid E) :
      g (ρ γ z) =
        eY.symm (@deckAct Y _ ⟨u x₀⟩ (FundamentalGroup.map u x₀ γ) (eY (g z))) := by
    simpa only [hsource] using hgmark γ z
  have hcomm (γ : ρ.range) (z : Hyperboloid E) :
      (f.trans g.symm) ((γ : Hyperboloid E ≃ᵢ Hyperboloid E) z) =
        (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ((f.trans g.symm) z) := by
    obtain ⟨η, hη⟩ := γ.property
    rw [← hη]
    apply g.injective
    change g (g.symm (f (ρ η z))) = g (ρ η (g.symm (f z)))
    rw [g.apply_symm_apply, hf, hg, g.apply_symm_apply]
  have hc := Hyperboloid.eq_refl_of_commutes_of_compact_thick_part
    ρ.range hfree hthick hno (f.trans g.symm) hcomm
  have hfg : f = g := by
    apply IsometryEquiv.ext
    intro z
    have hz := congrArg (fun h : Hyperboloid E ≃ᵢ Hyperboloid E => g (h z)) hc
    change g (g.symm (f z)) = g z at hz
    simpa only [g.apply_symm_apply] using hz
  let _ : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  apply IsometryEquiv.ext
  intro x
  let p : @UniversalCover X _ ⟨x₀⟩ :=
    ⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)⟩
  let z := eX.symm p
  have hz : @proj X _ ⟨x₀⟩ (eX z) = x := by
    change @proj X _ ⟨x₀⟩ (eX (eX.symm p)) = x
    rw [eX.apply_symm_apply]
    rfl
  have hfa := hfproj z
  have hgb := hgproj z
  rw [hz] at hfa hgb
  exact hfa.symm.trans ((congrArg
    (fun k : Hyperboloid E ≃ᵢ Hyperboloid F => @proj Y _ ⟨u x₀⟩ (eY (k z))) hfg).trans hgb)

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

namespace DifferentialGeometry

open Geometry.Hyperbolic
open Geometry.Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => Hyperboloid E₃

private theorem universalCoverMap_equivariant
    {X Y A B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PseudoMetricSpace A] [PseudoMetricSpace B]
    (u : C(X, Y)) (x₀ : X)
    (eX : A ≃ₜ @UniversalCover X _ ⟨x₀⟩)
    (eY : B ≃ₜ @UniversalCover Y _ ⟨u x₀⟩)
    (ρ : FundamentalGroup X x₀ →* (A ≃ᵢ A))
    (σ : FundamentalGroup Y (u x₀) →* (B ≃ᵢ B))
    (φ : FundamentalGroup X x₀ → FundamentalGroup Y (u x₀))
    (hφ : ∀ γ, φ γ = FundamentalGroup.map u x₀ γ)
    (hρ : ∀ γ z, eX (ρ γ z) = @UniversalCover.deckAct X _ ⟨x₀⟩ γ (eX z))
    (hσ : ∀ γ z, eY (σ γ z) = @UniversalCover.deckAct Y _ ⟨u x₀⟩ γ (eY z))
    (γ : FundamentalGroup X x₀) (z : A) :
    eY.symm (UniversalCover.map u x₀ (eX (ρ γ z))) =
      σ (φ γ) (eY.symm (UniversalCover.map u x₀ (eX z))) := by
  apply eY.injective
  rw [eY.apply_symm_apply, hρ, hσ, eY.apply_symm_apply, hφ]
  exact UniversalCover.map_smul u x₀ γ (eX z)

private theorem universalCoverMap_projection
    {X Y A B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B]
    (u : C(X, Y)) (x₀ : X)
    (eX : A ≃ₜ @UniversalCover X _ ⟨x₀⟩)
    (eY : B ≃ₜ @UniversalCover Y _ ⟨u x₀⟩) (z : A) :
    @UniversalCover.proj Y _ ⟨u x₀⟩
      (eY (eY.symm (UniversalCover.map u x₀ (eX z)))) =
        u (@UniversalCover.proj X _ ⟨x₀⟩ (eX z)) := by
  rw [eY.apply_symm_apply]
  exact UniversalCover.proj_map u x₀ (eX z)

private theorem universalCoverRepresentation_free
    {X A : Type*} [TopologicalSpace X] [PseudoMetricSpace A]
    (x₀ : X) (eX : A ≃ₜ @UniversalCover X _ ⟨x₀⟩)
    (ρ : FundamentalGroup X x₀ →* (A ≃ᵢ A))
    (hρ : ∀ γ z, eX (ρ γ z) = @UniversalCover.deckAct X _ ⟨x₀⟩ γ (eX z))
    (a : ρ.range) (ha : a ≠ 1) (z : A) : (a : A ≃ᵢ A) z ≠ z := by
  intro hz
  obtain ⟨γ, hγ⟩ := a.property
  have hfix := congrArg eX hz
  rw [← hγ, hρ] at hfix
  let _ : Inhabited X := ⟨x₀⟩
  let _ : MulAction (FundamentalGroup X x₀) (UniversalCover X) :=
    @UniversalCover.deckMulAction X _ ⟨x₀⟩
  have hγ1 : γ = 1 := (UniversalCover.deckAct_eq_self_iff (eX z)).mp hfix
  apply ha
  apply Subtype.ext
  rw [← hγ, hγ1, map_one]
  rfl

universe u v

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace E₃ N] [IsManifold (𝓡 3) ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N] in
private theorem edistOf_scale_eq_iff
    (g : SmoothRiemannianMetric (𝓡 3) M) (h : SmoothRiemannianMetric (𝓡 3) N)
    (c : ℝ) (hc : 0 < c) (f : M → N) (x y : M) :
    riemannianEDistOf (scaleMetric c hc h) (f x) (f y) =
      riemannianEDistOf (scaleMetric c hc g) x y ↔
        riemannianEDistOf h (f x) (f y) = riemannianEDistOf g x y := by
  rw [edistOf_scale, edistOf_scale]
  have hzero : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
  constructor
  · intro heq
    have h := congrArg (fun t : ℝ≥0∞ => (ENNReal.ofReal (Real.sqrt c))⁻¹ * t) heq
    simpa only [ENNReal.inv_mul_cancel_left hzero ENNReal.ofReal_ne_top] using h
  · intro heq
    rw [heq]

private theorem isDiscrete_projective_range
    {G : Type*} [Group G] (ρ : G →* (H₃ ≃ᵢ H₃)) [DiscreteTopology ρ.range] :
    IsDiscrete (SetLike.coe
      ((Hyperboloid.projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp ρ).range) := by
  have h : IsDiscrete (ρ.range : Set (H₃ ≃ᵢ H₃)) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  rw [MonoidHom.range_comp]
  exact h.image (Hyperboloid.projectiveOrthogonalGroupEquiv 2).toHomeomorph.isInducing

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mostow_prasad_rigidity
    (g : SmoothRiemannianMetric (𝓡 3) M) (h : SmoothRiemannianMetric (𝓡 3) N)
    (κ : ℝ) (u : ContinuousMap.HomotopyEquiv M N)
    (hκ : κ < 0) (hg : RiemannianMetricComplete g) (hh : RiemannianMetricComplete h)
    (hvolg : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < (⊤ : ℝ≥0∞))
    (hvolh : Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < (⊤ : ℝ≥0∞))
    (hsecg : ∀ (p : M) (v w : TangentSpace (𝓡 3) p),
      Geometry.Curvature.metricRm04StandardAt g p v w w v =
        κ * (g.inner p v v * g.inner p w w - g.inner p v w * g.inner p v w))
    (hsech : ∀ (p : N) (v w : TangentSpace (𝓡 3) p),
      Geometry.Curvature.metricRm04StandardAt h p v w w v =
        κ * (h.inner p v v * h.inner p w w - h.inner p v w * h.inner p v w)) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    letI : PseudoMetricSpace N := h.toPseudoMetricSpace
    letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
    ∃! a : M ≃ᵢ N, ContinuousMap.Homotopic u.toFun (a : C(M, N)) := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  change ∃! a : M ≃ᵢ N, ContinuousMap.Homotopic u.toFun (a : C(M, N))
  let x₀ : M := Classical.choice inferInstance
  let _ : Inhabited M := ⟨x₀⟩
  let _ : Inhabited N := ⟨u x₀⟩
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E₃ M
  let _ : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace E₃ N
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := 𝓡 3)
  let _ : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := 𝓡 3)
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact E₃ M
  let _ : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact E₃ N
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let hN := scaleMetric (-κ) (neg_pos.mpr hκ) h
  let ĝ := UniversalCover.liftedMetric (I := 𝓡 3) gN
  let ĥ := UniversalCover.liftedMetric (I := 𝓡 3) hN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let hĥ : RiemannianMetricComplete ĥ := UniversalCover.liftedMetric_complete hN (hh.scaleMetric _ _)
  let _ : IsManifold (𝓡 3) 1 (UniversalCover M) :=
    IsManifold.of_le (I := 𝓡 3) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) :=
    Manifold.metrizableSpace (𝓡 3) (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : UniversalCover M → Type _) :=
    ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace (𝓡 3) : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  let _ : IsManifold (𝓡 3) 1 (UniversalCover N) :=
    IsManifold.of_le (I := 𝓡 3) (M := UniversalCover N) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover N) :=
    Manifold.metrizableSpace (𝓡 3) (UniversalCover N)
  let _ : T3Space (UniversalCover N) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : UniversalCover N → Type _) :=
    ⟨ĥ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace (𝓡 3) : UniversalCover N → Type _) :=
    ⟨⟨ĥ.inner, ĥ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover N) := EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover N)
  let _ : PseudoEMetricSpace (UniversalCover N) :=
    (EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover N)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover N) := hĥ.complete
  let bM : OrthonormalBasis (Fin 3) ℝ
      (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := M))) :=
    (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := M)))).reindex
      (finCongr (show Module.finrank ℝ
        (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := M))) = 3 from finrank_euclideanSpace_fin))
  let bN : OrthonormalBasis (Fin 3) ℝ
      (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := N))) :=
    (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := N)))).reindex
      (finCongr (show Module.finrank ℝ
        (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := N))) = 3 from finrank_euclideanSpace_fin))
  let iM := bM.repr.symm
  let iN := bN.repr.symm
  let eM := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsecg iM
  let eN := normalizedUniversalCoverIsometryEquiv h hh κ hκ (u x₀) hsech iN
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsecg iM
  let σ := normalizedUniversalCoverDeckRepresentation h hh κ hκ (u x₀) hsech iN
  have hρ : Function.Injective ρ :=
    normalizedUniversalCoverDeckRepresentation_injective g hg κ hκ x₀ hsecg iM
  have hσ : Function.Injective σ :=
    normalizedUniversalCoverDeckRepresentation_injective h hh κ hκ (u x₀) hsech iN
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsecg iM
  let _ : DiscreteTopology σ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation h hh κ hκ (u x₀) hsech iN
  let φ := Topology.fundamentalGroupMulEquivOfHomotopyEquiv u x₀ (u x₀) rfl
  have hφ (γ : FundamentalGroup M x₀) : φ γ = FundamentalGroup.map u.toFun x₀ γ := by
    change FundamentalGroup.mapOfEq u.toFun rfl γ = FundamentalGroup.map u.toFun x₀ γ
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  obtain ⟨hfdρ, hcvρ⟩ :=
    hasFundamentalDomain_and_covolume_ne_top_normalized_universal_cover g hg κ hκ x₀ hsecg hvolg iM
  obtain ⟨hfdσ, hcvσ⟩ :=
    hasFundamentalDomain_and_covolume_ne_top_normalized_universal_cover h hh κ hκ (u x₀) hsech hvolh iN
  let _ := hfdρ
  let _ := hfdσ
  obtain ⟨e, _, he⟩ := Hyperboloid.exists_equivariant_isometry_of_projective_lattice_isomorphism
    ρ σ hρ hσ φ (isDiscrete_projective_range ρ) (isDiscrete_projective_range σ) hcvρ hcvσ
  let p := normalizedUniversalCoverQuotientHomeomorph g hg κ hκ x₀ hsecg iM
  let q := normalizedUniversalCoverQuotientHomeomorph h hh κ hκ (u x₀) hsech iN
  let projM : H₃ → M := fun z => UniversalCover.proj (eM z)
  let projN : H₃ → N := fun z => UniversalCover.proj (eN z)
  have hp (z : H₃) : p (Quotient.mk (MulAction.orbitRel ρ.range H₃) z) = projM z :=
    normalizedUniversalCoverQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsecg iM z
  have hq (z : H₃) : q (Quotient.mk (MulAction.orbitRel σ.range H₃) z) = projN z :=
    normalizedUniversalCoverQuotientHomeomorph_apply_mk h hh κ hκ (u x₀) hsech iN z
  have heM (γ : FundamentalGroup M x₀) (z : H₃) :
      eM (ρ γ z) = @UniversalCover.deckAct M _ ⟨x₀⟩ γ (eM z) :=
    normalizedUniversalCoverIsometryEquiv_deckRepresentation g hg κ hκ x₀ hsecg iM γ z
  have heN (γ : FundamentalGroup N (u x₀)) (z : H₃) :
      eN (σ γ z) = @UniversalCover.deckAct N _ ⟨u x₀⟩ γ (eN z) :=
    normalizedUniversalCoverIsometryEquiv_deckRepresentation h hh κ hκ (u x₀) hsech iN γ z
  let U : C(H₃, H₃) := (eN.symm : C(UniversalCover N, H₃)).comp
    ((UniversalCover.map u.toFun x₀).comp (eM : C(H₃, UniversalCover M)))
  have hU (γ : FundamentalGroup M x₀) (z : H₃) : U (ρ γ z) = σ (φ γ) (U z) :=
    universalCoverMap_equivariant u.toFun x₀ eM.toHomeomorph eN.toHomeomorph
      ρ σ φ hφ heM heN γ z
  let rM : FundamentalGroup M x₀ ≃* ρ.range := MonoidHom.ofInjective (f := ρ) hρ
  let rN : FundamentalGroup N (u x₀) ≃* σ.range := MonoidHom.ofInjective (f := σ) hσ
  let φR : ρ.range ≃* σ.range := rM.symm.trans (φ.trans rN)
  have heR (γ : ρ.range) (z : H₃) : e (γ • z) = φR γ • e z := by
    obtain ⟨γ, rfl⟩ := rM.surjective γ
    change e (ρ γ z) = σ (φ (rM.symm (rM γ))) (e z)
    rw [rM.symm_apply_apply]
    exact he γ z
  have hUR (γ : ρ.range) (z : H₃) : U (γ • z) = φR γ • U z := by
    obtain ⟨γ, rfl⟩ := rM.surjective γ
    change U (ρ γ z) = σ (φ (rM.symm (rM γ))) (U z)
    rw [rM.symm_apply_apply]
    exact hU γ z
  have hUproj (z : H₃) : q (Quotient.mk (MulAction.orbitRel σ.range H₃) (U z)) =
      u.toFun (p (Quotient.mk (MulAction.orbitRel ρ.range H₃) z)) := by
    rw [hq, hp]
    exact universalCoverMap_projection u.toFun x₀ eM.toHomeomorph eN.toHomeomorph z
  have hpball (x : H₃) (r : ℝ) :
      projM '' Metric.ball x r = riemannianBallOf gN (projM x) r :=
    image_ball_proj_normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsecg iM x r
  have hqball (x : H₃) (r : ℝ) :
      projN '' Metric.ball x r = riemannianBallOf hN (projN x) r :=
    image_ball_proj_normalizedUniversalCoverIsometryEquiv h hh κ hκ (u x₀) hsech iN x r
  let _ : IsIsometricSMul σ.range H₃ := ⟨fun γ => γ.val.isometry⟩
  have hthick (δ : ℝ) (hδ : 0 < δ) :
      IsCompact ((Quotient.mk (MulAction.orbitRel ρ.range H₃)) ''
        {z : H₃ | ∀ γ : ρ.range, γ ≠ 1 → δ ≤ dist z ((γ : H₃ ≃ᵢ H₃) z)}) :=
    isCompact_image_setOf_le_normalized_deckRepresentation_displacement
      g hg κ hκ x₀ hsecg hvolg δ hδ iM
  have hfree (a : ρ.range) (ha : a ≠ 1) (z : H₃) :
      (a : H₃ ≃ᵢ H₃) z ≠ z :=
    universalCoverRepresentation_free x₀ eM.toHomeomorph ρ heM a ha z
  have hno : ¬ ∃ ξ : Metric.sphere (0 : E₃) 1,
      ∀ γ : ρ.range, Hyperboloid.boundaryHomeomorph (γ : H₃ ≃ᵢ H₃) ξ = ξ :=
    Hyperboloid.not_exists_common_boundary_fixed_of_isCompact_thick_part
      ρ.range hfree 1 (hthick 1 zero_lt_one)
  have hex : ∃ d : M ≃ₜ N,
      (∀ x y, riemannianEDistOf h (d x) (d y) = riemannianEDistOf g x y) ∧
        ContinuousMap.Homotopic u.toFun (d : C(M, N)) := by
    let _ : PseudoMetricSpace M := gN.toPseudoMetricSpace
    let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    let _ : PseudoMetricSpace N := hN.toPseudoMetricSpace
    let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
    have hgball (x : M) (r : ℝ) : riemannianBallOf gN x r = Metric.ball x r := by
      ext y
      change riemannianEDistOf gN x y < ENNReal.ofReal r ↔ dist y x < r
      rw [← SmoothRiemannianMetric.toPseudoMetricSpace_edist gN, edist_lt_ofReal, dist_comm]
    have hhball (x : N) (r : ℝ) : riemannianBallOf hN x r = Metric.ball x r := by
      ext y
      change riemannianEDistOf hN x y < ENNReal.ofReal r ↔ dist y x < r
      rw [← SmoothRiemannianMetric.toPseudoMetricSpace_edist hN, edist_lt_ofReal, dist_comm]
    obtain ⟨a, _, ha⟩ := Hyperboloid.exists_isometryEquiv_homotopic_of_equivariant_isometry
      φR φR.surjective e heR p q
      (fun x r _ => by simpa only [hp, hgball] using hpball x r)
      (fun x r _ => by simpa only [hq, hhball] using hqball x r)
      U hUR u.toFun hUproj
    refine ⟨a.toHomeomorph, ?_, ha⟩
    intro x y
    apply (edistOf_scale_eq_iff g h (-κ) (neg_pos.mpr hκ) a x y).mp
    change edist (a x) (a y) = edist x y
    exact a.edist_eq x y
  obtain ⟨d, hd, hu⟩ := hex
  let a : M ≃ᵢ N :=
    { d.toEquiv with
      isometry_toFun := fun x y => by
        change riemannianEDistOf h (d x) (d y) = riemannianEDistOf g x y
        exact hd x y }
  refine ⟨a, hu, ?_⟩
  intro b hb
  let aa : M ≃ N := a.toEquiv
  let bb : M ≃ N := b.toEquiv
  have haa (x y : M) : riemannianEDistOf h (aa x) (aa y) = riemannianEDistOf g x y :=
    a.edist_eq x y
  have hbb (x y : M) : riemannianEDistOf h (bb x) (bb y) = riemannianEDistOf g x y :=
    b.edist_eq x y
  have hfun : (bb : M → N) = (aa : M → N) := by
    let _ : PseudoMetricSpace M := gN.toPseudoMetricSpace
    let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    let _ : PseudoMetricSpace N := hN.toPseudoMetricSpace
    let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
    let aNorm : M ≃ᵢ N :=
      { aa with
        isometry_toFun := fun x y => by
          change riemannianEDistOf hN (aa x) (aa y) = riemannianEDistOf gN x y
          exact (edistOf_scale_eq_iff g h (-κ) (neg_pos.mpr hκ) aa x y).mpr (haa x y) }
    let bNorm : M ≃ᵢ N :=
      { bb with
        isometry_toFun := fun x y => by
          change riemannianEDistOf hN (bb x) (bb y) = riemannianEDistOf gN x y
          exact (edistOf_scale_eq_iff g h (-κ) (neg_pos.mpr hκ) bb x y).mpr (hbb x y) }
    have hgball (x : M) (r : ℝ) : riemannianBallOf gN x r = Metric.eball x (ENNReal.ofReal r) := by
      ext y
      change riemannianEDistOf gN x y < ENNReal.ofReal r ↔ edist y x < ENNReal.ofReal r
      rw [← SmoothRiemannianMetric.toPseudoMetricSpace_edist gN, edist_comm]
    have hhball (x : N) (r : ℝ) : riemannianBallOf hN x r = Metric.eball x (ENNReal.ofReal r) := by
      ext y
      change riemannianEDistOf hN x y < ENNReal.ofReal r ↔ edist y x < ENNReal.ofReal r
      rw [← SmoothRiemannianMetric.toPseudoMetricSpace_edist hN, edist_comm]
    have hba : bNorm = aNorm :=
      Geometry.Riemannian.Topology.UniversalCover.isometry_eq_of_homotopic_of_compact_thick_part
        u.toFun x₀ eM.toHomeomorph eN.toHomeomorph
        (fun x r _ => by simpa only [projM, hgball, IsometryEquiv.coe_toHomeomorph] using hpball x r)
        (fun x r _ => by simpa only [projN, hhball, IsometryEquiv.coe_toHomeomorph] using hqball x r)
        ρ heM hthick hno bNorm aNorm hb hu
    exact funext fun x => congrArg (fun f : M ≃ᵢ N => f x) hba
  apply IsometryEquiv.ext
  exact congrFun hfun

end DifferentialGeometry
