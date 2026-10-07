import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollarProjectionR7E
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLipschitzR7E
import DifferentialGeometry.Geometry.Measure.Area.OpenTarget
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# O-MY-R7E G3：`K°` 上的 collar retraction（R-MY3 (1) carrier 定稿）

carrier：`N`（用时 `N := ↥U`）、`G`、光滑 `ρ`、`[−b−δ, −b]` 上 `dρ ≠ 0` 且 `Hess_G ρ > 0`、`{ρ ≤ −b+η}` 紧；
`K` 闭、`K ⊆ {ρ ≤ −b}`、`frontier K ⊆ {ρ = −b}`、`Ko = interior K`（R6a / ADP 的输出形）。

`exists_collar_retraction_R7E`：一族 `r c : C(Ko, Ko)`（`c ∈ [−b−δ, −b]`，`r c = R_c` 的 level projection）
* `{ρ ≤ c}` 上 `r c = id`（于是 `ρ ∘ Γ ≤ c` 时 trace 不变）；
* `ρ ∘ r c ≤ c`（`r c (Ko) ⊆ K ∩ {ρ ≤ c}`）；
* `G`-Lipschitz 盘 `v ↦ r c ∘ v` 仍 `G`-Lipschitz（两支粘合 + 局部—整体）；
* **面积不增**：对每个 `G`-Lipschitz 盘 `v`，`{c | A(r c ∘ v) > A(v)}` 可数（generic level：
  `{ρ ∘ v = c}` 零测时成立；interface 上 `r c` 不可微，故取 generic level——R-MY3 记录的偏差）。

不假设 `K` geodesically convex；Γ 在 `K°` 内部，不用 HS 2.9 boundary-embeddedness。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

section Interior

variable (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
  (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))
  {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ}
  (hdρ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y))
  (hβ0 : ∀ r, 0 ≤ β r) (hβ1 : ∀ r, β r ≤ 1) {a b : ℝ}
  (hβeq : ∀ r, a ≤ r → r ≤ b → β r = 1)

include hρ hdρ hβ0 hβ1 hβeq in
/-- level projection 保持 `interior K`：flow 线 `s ↦ D_s y` 落在 `{ρ < hi}` ⊆ `interior K ∪ Kᶜ`
（`frontier K ⊆ {ρ = hi}`），预连通 ⇒ 不离开 `interior K`。 -/
theorem collarProj_mem_interior_R7E {K : Set N} (hKcl : IsClosed K) {hi : ℝ} (hhib : hi ≤ b)
    (hKρ : K ⊆ {x | ρ x ≤ hi}) (hfr : frontier K ⊆ {x | ρ x = hi}) {c : ℝ} (hac : a ≤ c)
    {y : N} (hy : y ∈ interior K) : collarProj_R7E X hXc ρ c y ∈ interior K := by
  rcases le_total (ρ y) c with h | h
  · rw [collarProj_of_le_R7E X hXc h]
    exact hy
  · rw [collarProj_of_ge_R7E X hXc h]
    have hyK : ρ y ≤ hi := hKρ (interior_subset hy)
    let P : Set N := (fun s => collarFlow_R7E X hXc s y) '' Icc 0 (ρ y - c)
    have hPc : IsPreconnected P :=
      isPreconnected_Icc.image _ ((continuous_collarFlow_joint_R7E X hXc).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    have hPsub : P ⊆ interior K ∪ Kᶜ := by
      rintro _ ⟨s, hs, rfl⟩
      rcases hs.1.eq_or_lt with hs0 | hs0
      · left
        rw [← hs0]
        change collarFlow_R7E X hXc 0 y ∈ interior K
        rw [collarFlow_zero_R7E]
        exact hy
      · have hρs : ρ (collarFlow_R7E X hXc s y) = ρ y - s :=
          rho_collarFlow_R7E X hXc hρ hdρ hβ0 hβ1 hβeq (by linarith) hs.1 (by linarith [hs.2])
        by_contra hnot
        rw [mem_union, not_or, mem_compl_iff, not_not] at hnot
        have hfront : collarFlow_R7E X hXc s y ∈ frontier K := by
          rw [frontier, hKcl.closure_eq]
          exact ⟨hnot.2, hnot.1⟩
        have hfr' : ρ (collarFlow_R7E X hXc s y) = hi := hfr hfront
        linarith
    have hP := hPc.subset_left_of_subset_union isOpen_interior hKcl.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hPsub
      ⟨y, ⟨0, ⟨le_rfl, by linarith⟩, collarFlow_zero_R7E X hXc y⟩, hy⟩
    exact hP ⟨ρ y - c, ⟨by linarith, le_rfl⟩, rfl⟩

include hρ hdρ hβ0 hβ1 hβeq in
theorem collarProj_mem_Ko_R7E {K : Set N} (hKcl : IsClosed K) {hi : ℝ} (hhib : hi ≤ b)
    (hKρ : K ⊆ {x | ρ x ≤ hi}) (hfr : frontier K ⊆ {x | ρ x = hi})
    (Ko : TopologicalSpace.Opens N) (hKo : (Ko : Set N) = interior K) {c : ℝ} (hac : a ≤ c)
    (y : Ko) : collarProj_R7E X hXc ρ c y ∈ Ko := by
  change collarProj_R7E X hXc ρ c y ∈ (Ko : Set N)
  rw [hKo]
  exact collarProj_mem_interior_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr hac
    (by rw [← hKo]; exact y.2)

end Interior

/-- `K°` 上的 level projection `r_c`（`a ≤ c`）。 -/
def koProj_R7E (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
    (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ}
    (hdρ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y))
    (hβ0 : ∀ r, 0 ≤ β r) (hβ1 : ∀ r, β r ≤ 1) {a b : ℝ}
    (hβeq : ∀ r, a ≤ r → r ≤ b → β r = 1)
    {K : Set N} (hKcl : IsClosed K) {hi : ℝ} (hhib : hi ≤ b)
    (hKρ : K ⊆ {x | ρ x ≤ hi}) (hfr : frontier K ⊆ {x | ρ x = hi})
    (Ko : TopologicalSpace.Opens N) (hKo : (Ko : Set N) = interior K) {c : ℝ} (hac : a ≤ c) :
    C(Ko, Ko) :=
  ⟨fun y => ⟨collarProj_R7E X hXc ρ c y,
      collarProj_mem_Ko_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac y⟩,
    ((continuous_collarProj_R7E X hXc hρ.continuous c).comp continuous_subtype_val).subtype_mk _⟩

section KoLayer

variable (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
  (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))
  {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ}
  (hdρ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y))
  (hβ0 : ∀ r, 0 ≤ β r) (hβ1 : ∀ r, β r ≤ 1) {a b : ℝ}
  (hβeq : ∀ r, a ≤ r → r ≤ b → β r = 1)

variable {K : Set N} (hKcl : IsClosed K) {hi : ℝ} (hhib : hi ≤ b)
  (hKρ : K ⊆ {x | ρ x ≤ hi}) (hfr : frontier K ⊆ {x | ρ x = hi})
  (Ko : TopologicalSpace.Opens N) (hKo : (Ko : Set N) = interior K)

theorem koProj_val_R7E {c : ℝ} (hac : a ≤ c) (y : Ko) :
    ((koProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac y : Ko) : N) =
      collarProj_R7E X hXc ρ c y := rfl

theorem koProj_of_le_R7E {c : ℝ} (hac : a ≤ c) {y : Ko} (hy : ρ y ≤ c) :
    koProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac y = y :=
  Subtype.ext (collarProj_of_le_R7E X hXc hy)

theorem rho_koProj_le_R7E {c : ℝ} (hac : a ≤ c) (y : Ko) :
    ρ (koProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac y : N) ≤ c := by
  have hyK : (y : N) ∈ K := interior_subset (by rw [← hKo]; exact y.2)
  exact rho_collarProj_le_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hac ((hKρ hyK).trans hhib)

omit [T2Space N] in
include hKρ hKo in
theorem rho_le_of_mem_Ko_R7E (y : Ko) : ρ y ≤ hi :=
  hKρ (interior_subset (by rw [← hKo]; exact y.2))

/-- `K°` 上面积不增（generic level，`{ρ ∘ v = c}` 零测）。 -/
theorem area_koProj_le_R7E [T3Space N] (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (hperp : ∀ y (w : TangentSpace 𝓘(ℝ, E) y), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y w = 0 →
      G.inner y (X y) w = 0)
    {lo : ℝ} (hlie : ∀ x, lo ≤ ρ x → ρ x ≤ hi → ∀ w : TangentSpace 𝓘(ℝ, E) x,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x w = 0 → PDE.DeTurck.lieDerivMetric G X x w w ≤ 0)
    (hhib' : hi < b) {c : ℝ} (hac : a < c) (hlo : lo ≤ c) {v : C(closedDisk, Ko)} {L : ℝ≥0}
    (hv : ∀ z w, riemannianEDistOf (G.restrictOpen Ko) (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w)
    (hnull : volume ({z : ℂ | ρ (diskExtension (Subtype.val ∘ v) z) = c} ∩
      Metric.closedBall 0 1) = 0) :
    riemannianDiskArea (G.restrictOpen Ko)
        ((koProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac.le).comp v) ≤
      riemannianDiskArea (G.restrictOpen Ko) v := by
  rw [riemannianDiskArea_restrictOpen, riemannianDiskArea_restrictOpen]
  change riemannianDiskArea G (collarProj_R7E X hXc ρ c ∘ (Subtype.val ∘ v)) ≤ _
  exact riemannianDiskArea_collarProj_le_R7E X hXc G hρ hdρ hβ0 hβ1 hβeq hperp hac hlo hhib'
    hlie (V := Subtype.val ∘ v) (L := L)
    (fun z w => (riemannianEDistOf_le_restrictOpen G Ko (v z) (v w)).trans (hv z w))
    (fun z => rho_le_of_mem_Ko_R7E hKρ Ko hKo (v z)) hnull

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- `r_c ∘ v` 仍 `G`-Lipschitz：`{ρ ≤ c}` 支是 `v`，`{ρ ≥ c}` 支是光滑映射 `y ↦ D_{ρ y − c} y`
与 `v` 的复合（局部 Lipschitz），在球上粘合（`lipschitzOn_glue_closedDisk_R7E`），再局部—整体。 -/
theorem lipschitz_koProj_comp_R7E [T3Space N] (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {c : ℝ} (hac : a ≤ c) {v : C(closedDisk, Ko)} {L : ℝ≥0}
    (hv : ∀ z w, riemannianEDistOf (G.restrictOpen Ko) (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∃ K' : ℝ≥0, ∀ z w, riemannianEDistOf (G.restrictOpen Ko)
        ((koProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac).comp v z)
        ((koProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac).comp v w) ≤
      (K' : ℝ≥0∞) * edist z w := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Ko → Type _) :=
    ⟨(G.restrictOpen Ko).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : Ko → Type _) :=
    ⟨(G.restrictOpen Ko).inner, (G.restrictOpen Ko).contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace Ko := .ofRiemannianMetric 𝓘(ℝ, E) Ko
  set r := koProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac with hr
  have hvc : Continuous v := v.continuous
  have hψc : Continuous fun z => ρ (v z : N) :=
    hρ.continuous.comp (continuous_subtype_val.comp hvc)
  let R : N → N := fun y => collarFlow_R7E X hXc (ρ y - c) y
  have hRs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ R :=
    (contMDiff_collarFlow_joint_R7E X hXc).comp ((hρ.sub contMDiff_const).prodMk contMDiff_id)
  let f₂ : Ko → Ko := fun y => if h : R y ∈ Ko then ⟨R y, h⟩ else y
  have hwR : ∀ y : Ko, c ≤ ρ y → r y = f₂ y := by
    intro y hy
    have hmem : R y ∈ Ko := by
      have h := (r y).2
      rw [koProj_val_R7E, collarProj_of_ge_R7E X hXc hy] at h
      exact h
    apply Subtype.ext
    rw [koProj_val_R7E, collarProj_of_ge_R7E X hXc hy]
    change R y = ((if h : R y ∈ Ko then ⟨R y, h⟩ else y : Ko) : N)
    rw [dite_eq_left hmem]
  obtain ⟨K', hK'⟩ := lipschitz_of_local_closedDisk_R7E (r.comp v) (fun z₀ => by
    by_cases h0 : ρ (v z₀ : N) < c
    · refine ⟨{z | ρ (v z : N) < c}, (isOpen_lt hψc continuous_const).mem_nhds h0, L,
        fun x hx y hy => ?_⟩
      change edist (r (v x)) (r (v y)) ≤ _
      rw [koProj_of_le_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac (le_of_lt hx),
        koProj_of_le_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac (le_of_lt hy)]
      exact hv x y
    · have hc0 : c ≤ ρ (v z₀ : N) := le_of_not_gt h0
      have hRmem : R (v z₀) ∈ Ko := by
        have h := (r (v z₀)).2
        rw [koProj_val_R7E, collarProj_of_ge_R7E X hXc hc0] at h
        exact h
      have hO : IsOpen {y : Ko | R y ∈ Ko} :=
        Ko.isOpen.preimage (hRs.continuous.comp continuous_subtype_val)
      have hf₂ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f₂ (v z₀) := by
        rw [← contMDiffWithinAt_univ,
          ← DifferentialGeometry.Topology.contMDiffWithinAt_subtypeVal_comp_iff,
          contMDiffWithinAt_univ]
        have heq : (Subtype.val ∘ f₂) =ᶠ[𝓝 (v z₀)] R ∘ Subtype.val := by
          filter_upwards [hO.mem_nhds hRmem] with y hy
          change ((if h : R y ∈ Ko then ⟨R y, h⟩ else y : Ko) : N) = R y
          rw [dite_eq_left hy]
        exact (((hRs.comp contMDiff_subtype_val).of_le (by norm_num)).contMDiffAt
          ).congr_of_eventuallyEq heq
      obtain ⟨K₂, s₂, hs₂, hK₂⟩ := hf₂.exists_lipschitzOnWith
      obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (hvc.continuousAt.preimage_mem_nhds hs₂)
      refine ⟨ball z₀ ε, ball_mem_nhds z₀ hε, max L (K₂ * L), ?_⟩
      apply lipschitzOn_glue_closedDisk_R7E (w := r.comp v) (f₁ := v) (f₂ := f₂ ∘ v) hψc (c := c)
      · intro x hx
        exact koProj_of_le_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hac hx
      · intro x hx
        exact hwR (v x) hx
      · intro x _ y _ _ _
        exact (hv x y).trans (by gcongr; exact le_max_left _ _)
      · intro x hx y hy _ _
        refine (hK₂ (hεs hx) (hεs hy)).trans ?_
        calc (K₂ : ℝ≥0∞) * edist (v x) (v y) ≤ (K₂ : ℝ≥0∞) * ((L : ℝ≥0∞) * edist x y) := by
              gcongr
              exact hv x y
          _ = ((K₂ * L : ℝ≥0) : ℝ≥0∞) * edist x y := by rw [ENNReal.coe_mul, mul_assoc]
          _ ≤ ((max L (K₂ * L) : ℝ≥0) : ℝ≥0∞) * edist x y := by
              gcongr
              exact le_max_right _ _)
  exact ⟨K', fun z w => hK' z w⟩

end KoLayer

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

/-- **G3**（R-MY3 (1) carrier 形）：`K°` 上的 collar level projection 族 `r c`
（`c ∈ [−b−δ, −b]`）：`{ρ ≤ c}` 上恒等、`ρ ∘ r c ≤ c`、保 `G`-Lipschitz、对每个 `G`-Lipschitz 盘
`v` 除可数个 `c` 外 `A_G(r c ∘ v) ≤ A_G(v)`。 -/
theorem exists_collar_retraction_R7E [T3Space N] (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {b δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hcpt : IsCompact {x | ρ x ≤ -b + η})
    (hcoll : ∀ x, -b - δ ≤ ρ x → ρ x ≤ -b → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun G ρ x v v)
    {K : Set N} (hKcl : IsClosed K) (hKρ : K ⊆ {x | ρ x ≤ -b})
    (hfr : frontier K ⊆ {x | ρ x = -b}) (Ko : TopologicalSpace.Opens N)
    (hKo : (Ko : Set N) = interior K) :
    ∃ r : ℝ → C(Ko, Ko),
      (∀ c ∈ Icc (-b - δ) (-b), ∀ x : Ko, ρ x ≤ c → r c x = x) ∧
      (∀ c ∈ Icc (-b - δ) (-b), ∀ x : Ko, ρ (r c x : N) ≤ c) ∧
      (∀ c ∈ Icc (-b - δ) (-b), ∀ v : C(closedDisk, Ko),
        (∃ L : ℝ≥0, ∀ z w, riemannianEDistOf (G.restrictOpen Ko) (v z) (v w) ≤
          (L : ℝ≥0∞) * edist z w) →
        ∃ L : ℝ≥0, ∀ z w, riemannianEDistOf (G.restrictOpen Ko) ((r c).comp v z)
          ((r c).comp v w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      ∀ v : C(closedDisk, Ko),
        (∃ L : ℝ≥0, ∀ z w, riemannianEDistOf (G.restrictOpen Ko) (v z) (v w) ≤
          (L : ℝ≥0∞) * edist z w) →
        {c | c ∈ Icc (-b - δ) (-b) ∧ ¬ riemannianDiskArea (G.restrictOpen Ko) ((r c).comp v) ≤
          riemannianDiskArea (G.restrictOpen Ko) v}.Countable := by
  classical
  obtain ⟨X, hXc, β, ε, hε, hdρ, hβ0, hβ1, hβeq, hperp, hlie⟩ :=
    exists_collar_levelField_R7E G hρ (lo := -b - δ) (hi := -b) (by linarith) hη hcpt hcoll
  have hhib : -b ≤ -b + ε := by linarith
  let r : ℝ → C(Ko, Ko) := fun c => if hc : -b - δ - ε ≤ c then
    koProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hc else ContinuousMap.id Ko
  have hr : ∀ c (hc : -b - δ - ε ≤ c),
      r c = koProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo hc :=
    fun c hc => dite_eq_left hc
  have hcI : ∀ c ∈ Icc (-b - δ) (-b), -b - δ - ε ≤ c := fun c hc => by linarith [hc.1]
  refine ⟨r, fun c hc x hx => ?_, fun c hc x => ?_, fun c hc v hv => ?_, fun v hv => ?_⟩
  · rw [hr c (hcI c hc)]
    exact koProj_of_le_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo _ hx
  · rw [hr c (hcI c hc)]
    exact rho_koProj_le_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo _ x
  · obtain ⟨L, hL⟩ := hv
    rw [hr c (hcI c hc)]
    exact lipschitz_koProj_comp_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo G _ hL
  · obtain ⟨L, hL⟩ := hv
    refine (countable_not_null_level_R7E hρ.continuous (V := Subtype.val ∘ v)
      (continuous_subtype_val.comp v.continuous)).mono ?_
    rintro c ⟨hc, hbad⟩ hnull
    apply hbad
    rw [hr c (hcI c hc)]
    exact area_koProj_le_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib hKρ hfr Ko hKo G hperp
      (lo := -b - δ) hlie (by linarith) (by linarith [hc.1]) hc.1 hL hnull

end DifferentialGeometry.Geometry
