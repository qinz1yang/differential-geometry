import DifferentialGeometry.Geometry.Comparison.Soul.SbrBusemannPairData
import DifferentialGeometry.Geometry.Comparison.Soul.SbrCorayAscent
import DifferentialGeometry.Geometry.Comparison.Soul.SbrRetraction

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem sharafutdinovLevelMap_image_busemann_level
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (c : ℝ≥0 → M) (hc : Isometry c) {c₁ c₂ m : ℝ} (hlevels : c₁ < c₂)
    (hF : LipschitzWith 1 (fun x => c₂ - busemann c x))
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => c₂ - busemann c (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ c₂ - busemann c z})
    (hTm : c₂ - c₁ ≤ m)
    (hmax : ∃ q : M, c₂ - busemann c q = m ∧ ∀ z : M, c₂ - busemann c z ≤ m) :
    sharafutdinovLevelMap g hEnorm (fun x => c₂ - busemann c x) 1 hF hconc hC hmax
      (c₂ - c₁) '' {x : M | busemann c x = c₂} = {x : M | busemann c x = c₁} := by
  let F := fun x => c₂ - busemann c x
  let T := c₂ - c₁
  let R := sharafutdinovLevelMap g hEnorm F 1 hF hconc hC hmax
  have hT : 0 < T := sub_pos.mpr hlevels
  have hTint : T ∈ Icc 0 m := ⟨hT.le, hTm⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxF : F x = 0 := sub_eq_zero.mpr hx.symm
    have hlev := sharafutdinovLevelMap_level g hEnorm F 1 hF hconc hC hmax hTint
      (show 0 ≤ F x by rw [hxF])
    rw [hxF, max_eq_right hT.le] at hlev
    change c₂ - busemann c (R T x) = c₂ - c₁ at hlev
    change busemann c (R T x) = c₁
    linarith
  · intro hy
    have hy' : busemann c y = c₁ := hy
    have hbelow : busemann c y < c₂ := hy'.trans_lt hlevels
    have hcoray := exists_busemann_reversed_coray_ascent g hEnorm c hc y c₂ hbelow hF hconc
    simp only [hy'] at hcoray
    obtain ⟨u, _hu, hδ, hstart, hend, hδlevel, _hδdist, hδder⟩ := hcoray
    rw [hy'] at hδder
    let δ := fun t => intrinsicGeodesic g hEnorm y u (T - t)
    have hxF : F (δ 0) = 0 := sub_eq_zero.mpr hstart.symm
    have hx0 : 0 ≤ F (δ 0) := hxF.ge
    have hsame := eqOn_normalized_intrinsicGeneralizedGradient_curves
      g hEnorm hF hconc (fun t => R t (δ 0)) δ
      ((sharafutdinovLevelMap_continuousOn_orbit g hEnorm F 1 hF hconc hC hmax hx0).mono
        (fun _ ht => ⟨ht.1, ht.2.trans hTm⟩))
      hδ.continuous.continuousOn
      (fun t ht => (sharafutdinovLevelMap_hasMFDerivWithinAt_orbit
        g hEnorm F 1 hF hconc hC hmax hx0 (by simpa only [hxF] using ht.1)
          (ht.2.trans_le hTm)).2)
      (fun t ht => (hδder t ht).2.2)
      (by
        intro t ht
        have ht' : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
        change F (R t (δ 0)) = F (δ t)
        rw [sharafutdinovLevelMap_level g hEnorm F 1 hF hconc hC hmax
          ⟨ht.1, ht.2.le.trans hTm⟩ hx0, hxF, max_eq_right ht.1]
        exact (hδlevel t ht').symm)
      (sharafutdinovLevelMap_of_le g hEnorm F 1 hF hconc hC hmax 0 (δ 0) hx0)
    refine ⟨δ 0, hstart, ?_⟩
    exact (hsame ⟨hT.le, le_rfl⟩).trans hend

variable [ConnectedSpace M]

theorem exists_surjective_nonexpanding_busemann_level_map
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {c : ℝ≥0 → M} (hc : Isometry c) {c₁ c₂ : ℝ} (hlevels : c₁ < c₂)
    (hne : ({x : M | busemann c x = c₁}).Nonempty)
    (hC : IsCompact {x : M | busemann c x ≤ c₂}) :
    ∃ R : M → M, R '' {x : M | busemann c x = c₂} = {x : M | busemann c x = c₁} ∧
      LipschitzOnWith 1 R {x : M | busemann c x = c₂} := by
  obtain ⟨m, _hm, hTm, hC', hF, hconc, hmax⟩ :=
    exists_busemann_pairwise_flow_data g hEnorm hsec hc hlevels hne hC
  refine ⟨sharafutdinovLevelMap g hEnorm (fun x => c₂ - busemann c x) 1
    hF hconc hC' hmax (c₂ - c₁), ?_, ?_⟩
  · exact sharafutdinovLevelMap_image_busemann_level
      g hEnorm c hc hlevels hF hconc hC' hTm hmax
  · apply (sharafutdinovLevelMap_lipschitzOnWith g hEnorm
      (fun x => c₂ - busemann c x) 1 hF hconc hC' hmax
      ⟨(sub_pos.mpr hlevels).le, hTm⟩).mono
    intro x hx
    change 0 ≤ c₂ - busemann c x
    rw [show busemann c x = c₂ from hx, sub_self]

theorem exists_surjective_lipschitz_busemann_level_map
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {c : ℝ≥0 → M} (hc : Isometry c) {c₁ c₂ : ℝ} (hlevels : c₁ < c₂)
    (hne : ({x : M | busemann c x = c₁}).Nonempty)
    (hC : IsCompact {x : M | busemann c x ≤ c₂}) :
    ∃ levelMap : {x : M // busemann c x = c₂} → {x : M // busemann c x = c₁},
      LipschitzWith 1 levelMap ∧ Function.Surjective levelMap := by
  obtain ⟨R, himage, hlip⟩ :=
    exists_surjective_nonexpanding_busemann_level_map g hEnorm hsec hc hlevels hne hC
  have hmem : ∀ x : {x : M // busemann c x = c₂}, busemann c (R x.1) = c₁ := by
    intro x
    have hx : R x.1 ∈ R '' {x : M | busemann c x = c₂} := ⟨x.1, x.2, rfl⟩
    rw [himage] at hx
    exact hx
  let levelMap : {x : M // busemann c x = c₂} → {x : M // busemann c x = c₁} :=
    fun x => ⟨R x.1, hmem x⟩
  refine ⟨levelMap, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hlip.dist_le_mul x.1 x.2 y.1 y.2
  · intro y
    have hy : y.1 ∈ R '' {x : M | busemann c x = c₂} := by
      rw [himage]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end DifferentialGeometry.Geometry.Topology

end
