import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackgroundJetTransfer

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle

universe u

theorem partialDiffeomorph_trans_apply {n : WithTop ℕ∞}
    {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} {K : ModelWithCorners ℝ E'' H''}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    (Φ : PartialDiffeomorph I J M N n) (Ψ : PartialDiffeomorph J K N P n) (x : M) :
    (Φ.trans Ψ) x = Ψ (Φ x) := rfl

theorem partialDiffeomorph_trans_source {n : WithTop ℕ∞}
    {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} {K : ModelWithCorners ℝ E'' H''}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    (Φ : PartialDiffeomorph I J M N n) (Ψ : PartialDiffeomorph J K N P n) :
    (Φ.trans Ψ).source = Φ.source ∩ Φ ⁻¹' Ψ.source := rfl

theorem partialDiffeomorph_trans_target {n : WithTop ℕ∞}
    {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} {K : ModelWithCorners ℝ E'' H''}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    (Φ : PartialDiffeomorph I J M N n) (Ψ : PartialDiffeomorph J K N P n) :
    (Φ.trans Ψ).target = Ψ '' (Ψ.source ∩ Φ.target) := by
  rw [PartialDiffeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.trans_toPartialEquiv,
    PartialEquiv.trans_target'']
  rfl

theorem partialDiffeomorph_image_trans {n : WithTop ℕ∞}
    {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} {K : ModelWithCorners ℝ E'' H''}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    (Φ : PartialDiffeomorph I J M N n) (Ψ : PartialDiffeomorph J K N P n) (s : Set M) :
    (Φ.trans Ψ) '' s = Ψ '' (Φ '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Φ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, hz⟩
    exact ⟨x, hx, hz⟩

theorem homeomorph_image_connectedComponent {P : Type*} [TopologicalSpace P]
    {M : Type*} [TopologicalSpace M] (e : P ≃ₜ M) (p : P) :
    e '' connectedComponent p = connectedComponent (e p) := by
  refine subset_antisymm ?_ ?_
  · exact IsPreconnected.subset_connectedComponent
      (isPreconnected_connectedComponent.image e e.continuous.continuousOn)
      ⟨p, mem_connectedComponent, rfl⟩
  · have hcomp : e '' (e.symm '' connectedComponent (e p)) = connectedComponent (e p) := by
      rw [Set.image_image]
      have hid : (fun x => e (e.symm x)) = id := funext fun y => e.apply_symm_apply y
      rw [hid, Set.image_id]
    rw [← hcomp]
    exact Set.image_mono (IsPreconnected.subset_connectedComponent
      (isPreconnected_connectedComponent.image e.symm e.symm.continuous.continuousOn)
      ⟨e p, mem_connectedComponent, e.symm_apply_apply p⟩)

theorem diffeomorph_image_connectedComponent {P : Type*} [TopologicalSpace P]
    [ChartedSpace ThreeSpace P]
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (e : P ≃ₘ⟮I3, I3⟯ M) (p : P) :
    e '' connectedComponent p = connectedComponent (e p) :=
  homeomorph_image_connectedComponent (Diffeomorph.toHomeomorph e) p

theorem capCore_transport_of_partialDiffeomorph {P : Type u} {M : Type u}
    [TopologicalSpace P] [ChartedSpace ThreeSpace P]
    [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    {X : Set P} (c : CapCore (M := P) X) (e : PartialDiffeomorph I3 I3 P M ∞)
    (he : X ⊆ e.source) : Nonempty (CapCore (M := M) (e '' X)) := by
  cases c with
  | ball F h hx =>
    rw [← hx]
    exact ⟨CapCore.ball (PartialDiffeomorph.trans F e)
      (fun y hy => ⟨h hy, he (hx ▸ ⟨y, hy, rfl⟩)⟩)
      (by rw [partialDiffeomorph_image_trans])⟩
  | projective Z pr ball hb F hc hx =>
    rw [← hx]
    exact ⟨CapCore.projective Z pr ball hb (PartialDiffeomorph.trans F e)
      (fun y hy => ⟨hc hy, he (hx ▸ ⟨y, hy, rfl⟩)⟩)
      (by rw [partialDiffeomorph_image_trans])⟩

theorem nonempty_capCore_transport_of_image {M : Type}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (e : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (he : Metric.closedBall (0 : ThreeSpace) 1 ⊆ e.source) :
    Nonempty (CapCore (M := M) (e '' Metric.closedBall (0 : ThreeSpace) 1)) := by
  obtain ⟨c⟩ := capCore_closedBall_self
  exact capCore_transport_of_partialDiffeomorph c e he

theorem positiveComponent_transport_of_partialDiffeomorph {P : Type u} {M : Type u}
    [TopologicalSpace P] [ChartedSpace ThreeSpace P]
    [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    {U : Set P} (c : PositiveComponent (M := P) U)
    (e : PartialDiffeomorph I3 I3 P M ∞) (he : U ⊆ e.source) :
    Nonempty (PositiveComponent (M := M) (e '' U)) := by
  cases c with
  | sphere F hsrc htgt =>
    rw [← htgt]
    refine ⟨PositiveComponent.sphere (PartialDiffeomorph.trans F e) ?_ ?_⟩
    · rw [partialDiffeomorph_trans_source, hsrc, univ_inter]
      exact Set.eq_univ_of_forall fun z =>
        he (htgt ▸ PartialEquiv.map_source F.toPartialEquiv (hsrc.symm ▸ Set.mem_univ z))
    · rw [partialDiffeomorph_trans_target, htgt]
      exact congrArg (fun s => ↑e.toPartialEquiv '' s) (Set.inter_eq_self_of_subset_right he)
  | projective Z pr F hsrc htgt =>
    rw [← htgt]
    refine ⟨PositiveComponent.projective Z pr (PartialDiffeomorph.trans F e) ?_ ?_⟩
    · rw [partialDiffeomorph_trans_source, hsrc, univ_inter]
      exact Set.eq_univ_of_forall fun z =>
        he (htgt ▸ PartialEquiv.map_source F.toPartialEquiv (hsrc.symm ▸ Set.mem_univ z))
    · rw [partialDiffeomorph_trans_target, htgt]
      exact congrArg (fun s => ↑e.toPartialEquiv '' s) (Set.inter_eq_self_of_subset_right he)

theorem nonempty_positiveComponent_transport_sphereThree {M : Type}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (e : PartialDiffeomorph I3 I3 (Sphere 3) M ∞) (hsrc : e.source = Set.univ) :
    Nonempty (PositiveComponent (M := M) (e '' Set.univ)) := by
  obtain ⟨c⟩ := nonempty_positiveComponent_sphereThree
  exact positiveComponent_transport_of_partialDiffeomorph c e (by rw [hsrc])

theorem canonicalAlternative_transport_positive {P : Type u} [TopologicalSpace P]
    [ChartedSpace ThreeSpace P]
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {x : M} {t : ℝ} {eps C : ℝ} {U : Set P}
    (data : PositiveComponent (M := P) U) (e : PartialDiffeomorph I3 I3 P M ∞)
    (he : U ⊆ e.source) (hwhole : e '' U = connectedComponent x)
    (hsec : SecLower (S.base.metric t) (C⁻¹ * S.scalar t x) (e '' U)) :
    Nonempty (CanonicalAlternative S eps C x t (connectedComponent x)) := by
  obtain ⟨d⟩ := positiveComponent_transport_of_partialDiffeomorph data e he
  exact ⟨hwhole ▸ CanonicalAlternative.positive hwhole d hsec⟩


theorem roundComponent_transport_of_comparison {P : Type u} [TopologicalSpace P]
    [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P] [T2Space P] [SigmaCompactSpace P]
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {p : P} {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {x : M} {t : ℝ} {epsR : ℝ} {U V : Set P} {order' : ℕ} {eps : ℝ}
    (R : RoundComponent Sm epsR p 0 U) (hQ : 0 < S.scalar t x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn
      (fun _ => scaleMetric (I := I3) (Sm.scalar 0 p) R.Q_pos (Sm.base.metric 0))
      (fun _ => scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t))
      (Fmap : P → M) V {0} order' eps)
    (order : ℕ) (eps' : ℝ) (horderR : order ≤ ⌈epsR⁻¹⌉₊)
    (hepsR : 0 < epsR) (hepsR_small : epsR ≤ backgroundJetSmallness ThreeSpace order)
    (horder : order ≤ order') (heps : 0 ≤ eps)
    (hge : backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) * eps ≤ eps' - epsR)
    (horder' : ⌈eps'⁻¹⌉₊ ≤ order) (heps'half : eps' ≤ 1 / 2)
    (hbase : Fmap p = x) (hU_source : R.map.target ⊆ Fmap.source) (hUV : R.map.target ⊆ V) :
    letI : TopologicalSpace R.Z := R.topology
    letI : ChartedSpace ThreeSpace R.Z := R.charted
    letI : IsManifold I3 ∞ R.Z := R.smooth
    letI : T2Space R.Z := R.t2
    letI : CompactSpace R.Z := R.compact
    letI : ConnectedSpace R.Z := R.connected
    (Phi : R.Z ≃ₘ⟮I3, I3⟯ P) → (∀ y, Phi y = R.map y) →
      Nonempty (RoundComponent S eps' x t (Fmap '' U)) := by
  intro Phi hPhi
  refine ⟨?_⟩
  letI : TopologicalSpace R.Z := R.topology
  letI : ChartedSpace ThreeSpace R.Z := R.charted
  letI : IsManifold I3 ∞ R.Z := R.smooth
  letI : T2Space R.Z := R.t2
  letI : CompactSpace R.Z := R.compact
  letI : ConnectedSpace R.Z := R.connected
  have hmap_mem (y : R.Z) : R.map y ∈ R.map.target :=
    PartialEquiv.map_source R.map.toPartialEquiv (by rw [R.source_eq]; trivial)
  have hc₁ : MetricComparisonOn (fun _ => R.metric)
      (fun _ => scaleMetric (I := I3) (Sm.scalar 0 p) R.Q_pos (Sm.base.metric 0))
      (R.map : R.Z → P) Set.univ {0} order epsR :=
    R.comparison.mono (subset_refl _) horderR le_rfl
  have hV' : ∀ y ∈ (Set.univ : Set R.Z), Phi y ∈ V := fun y _ => hPhi y ▸ hUV (hmap_mem y)
  have hT := TransportedErrorTower.ofPullbackCrossOfClose cmp (fun _ => R.metric) Phi
    (R.map : R.Z → P) (fun y => (hPhi y).symm) hc₁ isOpen_univ hV' horder heps
    hepsR hepsR_small
    (fun _ _ _ _ _ _ _ => DifferentiableWithinAt.singleton)
  have hGV : ∀ y ∈ (Set.univ : Set R.Z), R.map y ∈ V := fun y _ => hUV (hmap_mem y)
  have hG : ∀ y ∈ (Set.univ : Set R.Z), MDifferentiableAt I3 I3 (R.map : R.Z → P) y :=
    fun y _ => R.map.mdifferentiableAt (by decide) (by rw [R.source_eq]; trivial)
  have hF : ∀ y ∈ (Set.univ : Set R.Z),
      MDifferentiableAt I3 I3 (Fmap : P → M) (R.map y) :=
    fun y _ => Fmap.mdifferentiableAt (by decide) (hU_source (hmap_mem y))
  have hcc := hc₁.trans cmp hT hGV hG hF
    (fun _ _ _ _ _ _ _ => DifferentiableWithinAt.singleton)
  have hcc' := hcc.mono (subset_refl _) horder' (by linarith)
  refine
    { Z := R.Z
      topology := R.topology
      charted := R.charted
      smooth := R.smooth
      t2 := R.t2
      compact := R.compact
      connected := R.connected
      metric := R.metric
      p := R.p
      scalar_one := R.scalar_one
      constant_curvature := R.constant_curvature
      map := PartialDiffeomorph.trans R.map Fmap
      source_eq := ?_
      target_eq := ?_
      center_eq := ?_
      Q_pos := hQ
      comparison := hcc'
      metric_bounds := ?_ }
  · rw [partialDiffeomorph_trans_source, R.source_eq, univ_inter]
    exact Set.eq_univ_of_forall fun z => hU_source (hmap_mem z)
  · rw [partialDiffeomorph_trans_target]
    rw [Set.inter_eq_self_of_subset_right hU_source, R.target_eq]
  · rw [partialDiffeomorph_trans_apply, R.center_eq, hbase]
  · intro z v
    rw [partialDiffeomorph_trans_apply]
    have hpb := hcc'.pullback_eq 0 z (Set.mem_univ z) (fun _ => v)
    have hcf := hcc'.equivalence 0 rfl z (Set.mem_univ z) v
    rw [hpb] at hcf
    rw [scaleMetric_inner] at hcf
    have hnn : 0 ≤ R.metric.inner z v v := inner_self_nonneg R.metric z v
    have h1 : (1 : ℝ) / 2 ≤ 1 - eps' := by linarith
    have h2 : 1 + eps' ≤ 2 := by linarith
    refine ⟨?_, ?_⟩
    · calc (1 / 2 : ℝ) * R.metric.inner z v v ≤ (1 - eps') * R.metric.inner z v v :=
          mul_le_mul_of_nonneg_right h1 hnn
        _ ≤ _ := hcf.1
    · calc _ ≤ (1 + eps') * R.metric.inner z v v := hcf.2
        _ ≤ 2 * R.metric.inner z v v := mul_le_mul_of_nonneg_right h2 hnn

theorem canonicalAlternative_transport_round {P : Type u} [TopologicalSpace P]
    [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P] [T2Space P] [SigmaCompactSpace P]
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {p : P} {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {x : M} {t : ℝ} {epsR : ℝ} {U V : Set P} {order' : ℕ} {eps C : ℝ}
    (R : RoundComponent Sm epsR p 0 U)
    (hQ : 0 < S.scalar t x) (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (hconn : Fmap '' U = connectedComponent x)
    (cmp : MetricComparisonOn
      (fun _ => scaleMetric (I := I3) (Sm.scalar 0 p) R.Q_pos (Sm.base.metric 0))
      (fun _ => scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t))
      (Fmap : P → M) V {0} order' eps)
    (order : ℕ) (eps' : ℝ) (horderR : order ≤ ⌈epsR⁻¹⌉₊)
    (hepsR : 0 < epsR) (hepsR_small : epsR ≤ backgroundJetSmallness ThreeSpace order)
    (horder : order ≤ order') (heps : 0 ≤ eps)
    (hge : backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) * eps ≤ eps' - epsR)
    (horder' : ⌈eps'⁻¹⌉₊ ≤ order) (heps'half : eps' ≤ 1 / 2)
    (hbase : Fmap p = x) (hU_source : R.map.target ⊆ Fmap.source) (hUV : R.map.target ⊆ V) :
    letI : TopologicalSpace R.Z := R.topology
    letI : ChartedSpace ThreeSpace R.Z := R.charted
    letI : IsManifold I3 ∞ R.Z := R.smooth
    letI : T2Space R.Z := R.t2
    letI : CompactSpace R.Z := R.compact
    letI : ConnectedSpace R.Z := R.connected
    (Phi : R.Z ≃ₘ⟮I3, I3⟯ P) → (∀ y, Phi y = R.map y) →
      Nonempty (CanonicalAlternative S eps' C x t (connectedComponent x)) := by
  intro Phi hPhi
  refine ⟨?_⟩
  letI : TopologicalSpace R.Z := R.topology
  letI : ChartedSpace ThreeSpace R.Z := R.charted
  letI : IsManifold I3 ∞ R.Z := R.smooth
  letI : T2Space R.Z := R.t2
  letI : CompactSpace R.Z := R.compact
  letI : ConnectedSpace R.Z := R.connected
  exact hconn ▸ CanonicalAlternative.round hconn
    (Classical.choice (roundComponent_transport_of_comparison R hQ Fmap cmp order eps'
      horderR hepsR hepsR_small horder heps hge horder' heps'half hbase hU_source hUV Phi hPhi))

theorem exists_round_transport_parameters (order : ℕ) (horder : 2 ≤ order) :
    ∃ epsR eps' eps : ℝ,
      0 < epsR ∧ epsR ≤ backgroundJetSmallness ThreeSpace order ∧
      0 < eps' ∧ eps' ≤ 1 / 2 ∧ 0 ≤ eps ∧
      backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) * eps ≤ eps' - epsR ∧
      order ≤ ⌈epsR⁻¹⌉₊ ∧ ⌈eps'⁻¹⌉₊ ≤ order := by
  have hord : (0 : ℝ) < (order : ℝ) := by exact_mod_cast (by omega : 0 < order)
  have hK : 0 < backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) :=
    mul_pos (backgroundJetConstant_pos ThreeSpace order) (by positivity)
  have hsmall_pos : 0 < backgroundJetSmallness ThreeSpace order / 2 := by
    have := backgroundJetSmallness_pos ThreeSpace order
    linarith
  have hhalf_inv_pos : 0 < (2 * (order : ℝ))⁻¹ := by positivity
  have h2inv : (2 * (order : ℝ))⁻¹ ≤ (order : ℝ)⁻¹ :=
    (inv_le_inv₀ (by positivity : (0 : ℝ) < 2 * order) hord).mpr (by linarith)
  have hmin_le : min ((2 * (order : ℝ))⁻¹) (backgroundJetSmallness ThreeSpace order / 2)
      ≤ (order : ℝ)⁻¹ :=
    (min_le_left _ _).trans h2inv
  have hinv_ge : (order : ℝ) ≤ (min ((2 * (order : ℝ))⁻¹)
      (backgroundJetSmallness ThreeSpace order / 2))⁻¹ := by
    have := (inv_le_inv₀ (inv_pos.mpr hord) (lt_min hhalf_inv_pos hsmall_pos)).mpr hmin_le
    rwa [inv_inv] at this
  refine ⟨min ((2 * (order : ℝ))⁻¹) (backgroundJetSmallness ThreeSpace order / 2),
    (order : ℝ)⁻¹,
    ((order : ℝ)⁻¹ - min ((2 * (order : ℝ))⁻¹) (backgroundJetSmallness ThreeSpace order / 2)) /
      (backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min hhalf_inv_pos hsmall_pos
  · exact (min_le_right _ _).trans (le_of_lt (by
      have := backgroundJetSmallness_pos ThreeSpace order
      linarith))
  · exact inv_pos.mpr hord
  · rw [← inv_eq_one_div]
    exact (inv_le_inv₀ hord (by norm_num : (0 : ℝ) < 2)).mpr (by exact_mod_cast horder)
  · exact div_nonneg (sub_nonneg.mpr hmin_le) hK.le
  · rw [mul_div_cancel₀ _ hK.ne']
  · calc order = ⌈(order : ℝ)⌉₊ := (Nat.ceil_natCast order).symm
      _ ≤ ⌈(min ((2 * (order : ℝ))⁻¹)
            (backgroundJetSmallness ThreeSpace order / 2))⁻¹⌉₊ := Nat.ceil_mono hinv_ge
  · rw [inv_inv, Nat.ceil_natCast]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
