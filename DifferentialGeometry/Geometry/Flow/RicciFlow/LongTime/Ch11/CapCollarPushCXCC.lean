import DifferentialGeometry.Geometry.Metric.Distance.Boundary
import DifferentialGeometry.Topology.Manifold.CollarReparametrization

/-!
# CX-CAPCORE G1：collar-push 工具（后缀 `_CXCC`）

core-collar 延伸需要的两件通用工具：
* `riemannianEDistOf_add_le_of_frontier_CXCC`（**frontier split**）：`p ∈ A`（`A` closed）、`y ∉ A`，
  若每个 `q ∈ frontier A` 都有 `r ≤ d(p, q)` 且 `c ≤ d(q, y)`，则 `r + c ≤ d(p, y)`
  （近最短 path 的 first exit，同 `riemannianEDistOf_closedBall_subset_of_le_frontier_distance` 机制）。
* `exists_collar_translation_isotopy_CXCC`（**collar translation**）：树内
  `PartialDiffeomorph.exists_collar_reparametrization_isotopy` 的 `Icc` 版——在 product chart
  `e : N × ℝ → M` 的 band `univ ×ˢ Ioo l u` 内把整段 `Icc a b` 平移 `σ`（`b + σ < u`），
  得到 `M` 的 global diffeomorphism family，chart 内为 `(θ, t) ↦ (θ, φ t)`，band 外为恒等。
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **frontier split**：`p ∈ A`、`y ∉ A`（`A` closed），frontier 上的两侧下界相加给 `d(p, y)` 下界。 -/
theorem riemannianEDistOf_add_le_of_frontier_CXCC
    (g : SmoothRiemannianMetric I M) {A : Set M} (hA : IsClosed A) {p y : M}
    (hp : p ∈ A) (hy : y ∉ A) {r c : ℝ≥0∞}
    (hfront : ∀ q ∈ frontier A,
      r ≤ riemannianEDistOf g p q ∧ c ≤ riemannianEDistOf g q y) :
    r + c ≤ riemannianEDistOf g p y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  apply le_of_not_gt
  intro hlt
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_riemannianEDist_lt hlt
  obtain ⟨t, ht, _, hboundary⟩ :=
    exists_first_exit_frontier_of_mem hA zero_lt_one hγ.continuousOn
      (hγ0 ▸ hp) (hγ1 ▸ hy)
  have hleft : r ≤ pathELength I γ 0 t :=
    (hfront (γ t) hboundary).1.trans
      (riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2.le))
        hγ0 rfl ht.1)
  have hright : c ≤ pathELength I γ t 1 :=
    (hfront (γ t) hboundary).2.trans
      (riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc ht.1 le_rfl))
        rfl hγ1 ht.2.le)
  have htotal := add_le_add hleft hright
  rw [pathELength_add ht.1 ht.2.le] at htotal
  exact (not_lt_of_ge htotal) hlength

end DifferentialGeometry.Geometry.Metric

namespace PartialDiffeomorph

open DifferentialGeometry.Topology.Manifold

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [CompactSpace N]

/-- **collar translation**：band `univ ×ˢ Ioo l u ⊆ e.source` 内把 `Icc a b` 平移 `σ ≥ 0`
（`l < a`、`b + σ < u`）。chart 内 `F s (e z) = e (z.1, φ s z.2)`，`φ s` 在 `Icc a b` 上是 `+ s σ`、
导数处处为正、band 外为恒等；`F s` 在某紧集 `K ⊆ e '' band` 外为恒等。 -/
theorem exists_collar_translation_isotopy_CXCC
    (e : PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {l u a b σ : ℝ} (hla : l < a) (hσ : 0 ≤ σ) (hbu : b + σ < u)
    (hsource : univ ×ˢ Ioo l u ⊆ e.source) :
    ∃ φ : ℝ → ℝ ≃ₘ[ℝ] ℝ,
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc a b, φ s c = c + s * σ) ∧
      (∀ s c, 0 < deriv (φ s) c) ∧
      (∀ s, EqOn (φ s) id (Ioo l u)ᶜ ∧ EqOn (φ s).symm id (Ioo l u)ᶜ) ∧
      ∃ F : ℝ → M ≃ₘ⟮I, I⟯ M,
        (∀ s z, z ∈ e.source → F s (e z) = e (z.1, φ s z.2)) ∧
        (∀ s z, z ∈ e.source → (F s).symm (e z) = e (z.1, (φ s).symm z.2)) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ e '' (univ ×ˢ Ioo l u) ∧
          ∀ s, EqOn (F s) id Kᶜ ∧ EqOn (F s).symm id Kᶜ := by
  classical
  obtain ⟨φ, hφ, hφi, -, hmove, _, L, hL, hLU, hfix⟩ :=
    Diffeomorph.exists_isotopy_translation_in_open (isCompact_Icc (a := a) (b := b))
      isOpen_Ioo σ (by
        intro s hs c hc
        have h1 : 0 ≤ s * σ := mul_nonneg hs.1 hσ
        have h2 : s * σ ≤ σ := by nlinarith [hs.2]
        change l < c + s * σ ∧ c + s * σ < u
        constructor
        · linarith [hc.1]
        · linarith [hc.2])
  have hpositive (s c : ℝ) : 0 < deriv (φ s) c := by
    have h := (φ s).det_fderiv_pos_of_eqOn_compl_isCompact hL (hfix s).1 c
    simpa only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, fderiv_eq_smul_deriv,
      one_smul] using h
  let D (s : ℝ) : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), J.prod 𝓘(ℝ)⟯ N × ℝ :=
    (Diffeomorph.refl J N ∞).prodCongr (φ s)
  have hD : ContMDiff (𝓘(ℝ).prod (J.prod 𝓘(ℝ))) (J.prod 𝓘(ℝ)) ∞
      (fun q : ℝ × (N × ℝ) => D q.1 q.2) :=
    contMDiff_snd.fst.prodMk
      (hφ.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd.snd))
  have hDi : ContMDiff (𝓘(ℝ).prod (J.prod 𝓘(ℝ))) (J.prod 𝓘(ℝ)) ∞
      (fun q : ℝ × (N × ℝ) => (D q.1).symm q.2) :=
    contMDiff_snd.fst.prodMk
      (hφi.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd.snd))
  have hK : IsCompact (univ ×ˢ L : Set (N × ℝ)) := isCompact_univ.prod hL
  have hKs : univ ×ˢ L ⊆ e.source :=
    (Set.prod_mono (subset_refl _) hLU).trans hsource
  obtain ⟨F, -, -, heq, hFK, _, hFfix⟩ :=
    e.exists_diffeomorph_family_extension D hD hDi hK hKs (by
      intro s z hz
      have hzL : z.2 ∉ L := fun h => hz ⟨mem_univ _, h⟩
      exact Prod.ext rfl ((hfix s).1 hzL))
  refine ⟨φ, ?_, hpositive, ?_, F, ?_, ?_,
    e '' (univ ×ˢ L), hFK, Set.image_mono (Set.prod_mono (subset_refl _) hLU), ?_⟩
  · intro s hs c hc
    simpa only [smul_eq_mul] using hmove s hs c hc
  · intro s
    exact ⟨(hfix s).1.mono (compl_subset_compl.mpr hLU),
      (hfix s).2.mono (compl_subset_compl.mpr hLU)⟩
  · intro s z hz
    rw [(heq s (e z)).1, OpenPartialHomeomorph.extendById]
    change (if e z ∈ e.target then e (D s (e.symm (e z))) else e z) =
      e (z.1, φ s z.2)
    rw [ite_eq_left (e.map_source hz)]
    have hleft : e.symm (e z) = z := e.left_inv hz
    rw [hleft]
    rfl
  · intro s z hz
    rw [(heq s (e z)).2, OpenPartialHomeomorph.extendById]
    change (if e z ∈ e.target then e ((D s).symm (e.symm (e z))) else e z) =
      e (z.1, (φ s).symm z.2)
    rw [ite_eq_left (e.map_source hz)]
    have hleft : e.symm (e z) = z := e.left_inv hz
    rw [hleft]
    rfl
  · intro s
    exact ⟨fun y hy => (hFfix s y hy).1, fun y hy => (hFfix s y hy).2⟩

end PartialDiffeomorph
