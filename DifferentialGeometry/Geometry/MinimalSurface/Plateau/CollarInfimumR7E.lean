import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConfinedMorreyR7E
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

/-!
# O-MY-R7E G4：`K`-competitor 与 `K°`-competitor 的 infimum 相等

`K`-competitor：`v : C(closedDisk, N)`，像在 `K`（可以碰 `{ρ = −b}`），trace 类 `ι ∘ Γ`，`G`-Lipschitz；
`K°`-competitor：`w : C(closedDisk, K°)`，trace 类 `Γ`，`G|K°`-Lipschitz。

* (a) 每个 `K`-competitor `v` 经 generic level `c ∈ (−b−δ, −b)` 的 level projection `R_c`
  （`K` 是 `{ρ ≤ −b}` 的「连通闭」分支 `hKcomp` ⇒ `R_c(K) ⊆ K°`）给出 `K°`-competitor `w`，
  `A_{G|K°}(w) ≤ A_G(v)`；
* (b) 每个 `K°`-competitor `w` 经 inclusion 是 `K`-competitor，面积相等；
* (c) 两个 infimum（`sInf` of area images）相等。

`G|K°`-Lipschitz 由 `G`-Lipschitz 经树里 `exists_mem_nhds_riemannianEDistOf_restrictOpen_eq`
（`d_{K°} = d_N` 局部）+ `lipschitz_of_local_closedDisk_R7E` 得到。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- `R_c ∘ V` 仍 `G`-Lipschitz（`N` 上；两支粘合 + 局部—整体）。 -/
theorem lipschitz_collarProj_comp_R7E [T3Space N]
    (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
    (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (c : ℝ) {V : C(closedDisk, N)} {L : ℝ≥0}
    (hV : ∀ z w, riemannianEDistOf G (V z) (V w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∃ K' : ℝ≥0, ∀ z w, riemannianEDistOf G (collarProj_R7E X hXc ρ c (V z))
      (collarProj_R7E X hXc ρ c (V w)) ≤ (K' : ℝ≥0∞) * edist z w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : N → Type _) := ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : N → Type _) :=
    ⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric 𝓘(ℝ, E) N
  have hψc : Continuous fun z => ρ (V z) := hρ.continuous.comp V.continuous
  let R : N → N := fun y => collarFlow_R7E X hXc (ρ y - c) y
  have hRs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ R :=
    (contMDiff_collarFlow_joint_R7E X hXc).comp ((hρ.sub contMDiff_const).prodMk contMDiff_id)
  obtain ⟨K', hK'⟩ := lipschitz_of_local_closedDisk_R7E (collarProj_R7E X hXc ρ c ∘ V)
    (fun z₀ => by
      by_cases h0 : ρ (V z₀) < c
      · refine ⟨{z | ρ (V z) < c}, (isOpen_lt hψc continuous_const).mem_nhds h0, L,
          fun x hx y hy => ?_⟩
        change edist (collarProj_R7E X hXc ρ c (V x)) (collarProj_R7E X hXc ρ c (V y)) ≤ _
        rw [collarProj_of_le_R7E X hXc (le_of_lt hx), collarProj_of_le_R7E X hXc (le_of_lt hy)]
        exact hV x y
      · obtain ⟨K₂, s₂, hs₂, hK₂⟩ :=
          ((hRs (V z₀)).of_le (by norm_num)).exists_lipschitzOnWith
        obtain ⟨ε, hε, hεs⟩ :=
          Metric.mem_nhds_iff.mp (V.continuous.continuousAt.preimage_mem_nhds hs₂)
        refine ⟨ball z₀ ε, ball_mem_nhds z₀ hε, max L (K₂ * L), ?_⟩
        apply lipschitzOn_glue_closedDisk_R7E (w := collarProj_R7E X hXc ρ c ∘ V) (f₁ := V)
          (f₂ := R ∘ V) hψc (c := c)
        · intro x hx
          exact collarProj_of_le_R7E X hXc hx
        · intro x hx
          exact collarProj_of_ge_R7E X hXc hx
        · intro x _ y _ _ _
          exact (hV x y).trans (by gcongr; exact le_max_left _ _)
        · intro x hx y hy _ _
          refine (hK₂ (hεs hx) (hεs hy)).trans ?_
          calc (K₂ : ℝ≥0∞) * edist (V x) (V y) ≤ (K₂ : ℝ≥0∞) * ((L : ℝ≥0∞) * edist x y) := by
                gcongr
                exact hV x y
            _ = ((K₂ * L : ℝ≥0) : ℝ≥0∞) * edist x y := by rw [ENNReal.coe_mul, mul_assoc]
            _ ≤ ((max L (K₂ * L) : ℝ≥0) : ℝ≥0∞) * edist x y := by
                gcongr
                exact le_max_right _ _)
  exact ⟨K', fun z w => hK' z w⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- 像在开集 `O` 里的 `G`-Lipschitz 盘，其 lift 是 `G|O`-Lipschitz（`d_O = d_N` 局部 + 局部—整体）。 -/
theorem lipschitz_liftToOpen_R7E [T3Space N] (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (O : TopologicalSpace.Opens N) {V : C(closedDisk, N)} (hVO : Set.range V ⊆ O) {L : ℝ≥0}
    (hV : ∀ z w, riemannianEDistOf G (V z) (V w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∃ K' : ℝ≥0, ∀ z w, riemannianEDistOf (G.restrictOpen O) (liftToOpen_AT V hVO z)
      (liftToOpen_AT V hVO w) ≤ (K' : ℝ≥0∞) * edist z w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : O → Type _) :=
    ⟨(G.restrictOpen O).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : O → Type _) :=
    ⟨(G.restrictOpen O).inner, (G.restrictOpen O).contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace O := .ofRiemannianMetric 𝓘(ℝ, E) O
  obtain ⟨K', hK'⟩ := lipschitz_of_local_closedDisk_R7E (liftToOpen_AT V hVO) (fun z₀ => by
    obtain ⟨W, hW, heq⟩ := Metric.exists_mem_nhds_riemannianEDistOf_restrictOpen_eq G O
      (liftToOpen_AT V hVO z₀)
    have hW' : W ∈ 𝓝 (V z₀) := hW
    refine ⟨V ⁻¹' W, V.continuous.continuousAt.preimage_mem_nhds hW', L, fun x hx y hy => ?_⟩
    change riemannianEDistOf (G.restrictOpen O) (liftToOpen_AT V hVO x)
      (liftToOpen_AT V hVO y) ≤ _
    rw [heq (liftToOpen_AT V hVO x) (liftToOpen_AT V hVO y) hx hy]
    exact hV x y)
  exact ⟨K', fun z w => hK' z w⟩

section Component

variable (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
  (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))
  {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ}
  (hdρ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y))
  (hβ0 : ∀ r, 0 ≤ β r) (hβ1 : ∀ r, β r ≤ 1) {a b : ℝ}
  (hβeq : ∀ r, a ≤ r → r ≤ b → β r = 1)

include hρ hdρ hβ0 hβ1 hβeq in
/-- `K` 是 `{ρ ≤ hi}` 的「连通闭」部分（`hKcomp`）⇒ `c < hi` 时 `R_c(K) ⊆ interior K`。 -/
theorem collarProj_mem_interior_of_mem_R7E {K : Set N} (hKcl : IsClosed K) {hi : ℝ}
    (hhib : hi ≤ b) (hKρ : K ⊆ {x | ρ x ≤ hi}) (hfr : frontier K ⊆ {x | ρ x = hi})
    (hKcomp : ∀ S : Set N, IsPreconnected S → S ⊆ {x | ρ x ≤ hi} → (S ∩ K).Nonempty → S ⊆ K)
    {c : ℝ} (hac : a ≤ c) (hchi : c < hi) {y : N} (hy : y ∈ K) :
    collarProj_R7E X hXc ρ c y ∈ interior K := by
  have hint : ∀ z ∈ K, ρ z < hi → z ∈ interior K := by
    intro z hzK hz
    by_contra hnot
    have hfront : z ∈ frontier K := by
      rw [frontier, hKcl.closure_eq]
      exact ⟨hzK, hnot⟩
    have h1 : ρ z = hi := hfr hfront
    linarith
  have hyhi : ρ y ≤ hi := hKρ hy
  rcases le_total (ρ y) c with h | h
  · rw [collarProj_of_le_R7E X hXc h]
    exact hint y hy (by linarith)
  · rw [collarProj_of_ge_R7E X hXc h]
    have hρτ : ρ (collarFlow_R7E X hXc (ρ y - c) y) = c := by
      rw [rho_collarFlow_R7E X hXc hρ hdρ hβ0 hβ1 hβeq (by linarith) (by linarith)
        (by linarith)]
      ring
    let P : Set N := (fun s => collarFlow_R7E X hXc s y) '' Icc 0 (ρ y - c)
    have hPc : IsPreconnected P :=
      isPreconnected_Icc.image _ ((continuous_collarFlow_joint_R7E X hXc).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    have hPρ : P ⊆ {x | ρ x ≤ hi} := by
      rintro _ ⟨s, hs, rfl⟩
      have hρs : ρ (collarFlow_R7E X hXc s y) = ρ y - s :=
        rho_collarFlow_R7E X hXc hρ hdρ hβ0 hβ1 hβeq (by linarith) hs.1 (by linarith [hs.2])
      change ρ (collarFlow_R7E X hXc s y) ≤ hi
      linarith [hs.1]
    have hPK := hKcomp P hPc hPρ ⟨y, ⟨0, ⟨le_rfl, by linarith⟩, collarFlow_zero_R7E X hXc y⟩, hy⟩
    exact hint _ (hPK ⟨ρ y - c, ⟨by linarith, le_rfl⟩, rfl⟩) (by rw [hρτ]; exact hchi)

end Component

/-- **G4**：`K`-competitor 与 `K°`-competitor 的 infimum 相等（以及两向的逐个比较）。 -/
theorem inf_K_eq_inf_Ko_R7E [T3Space N] (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {b δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hcpt : IsCompact {x | ρ x ≤ -b + η})
    (hcoll : ∀ x, -b - δ ≤ ρ x → ρ x ≤ -b → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun G ρ x v v)
    {K : Set N} (hKcl : IsClosed K) (hKρ : K ⊆ {x | ρ x ≤ -b})
    (hfr : frontier K ⊆ {x | ρ x = -b})
    (hKcomp : ∀ S : Set N, IsPreconnected S → S ⊆ {x | ρ x ≤ -b} → (S ∩ K).Nonempty → S ⊆ K)
    (Ko : TopologicalSpace.Opens N) (hKo : (Ko : Set N) = interior K) {Γ : freeLoop Ko}
    (hΓρ : ∀ θ, ρ (Γ θ : N) < -b - δ) :
    let ι : C(Ko, N) := ⟨Subtype.val, continuous_subtype_val⟩
    let SK : Set C(closedDisk, N) := {v | Set.range v ⊆ K ∧ DiskWeakJordanTrace (ι.comp Γ) v ∧
      ∃ L : ℝ≥0, ∀ z w, riemannianEDistOf G (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w}
    let SKo : Set C(closedDisk, Ko) := {w | DiskWeakJordanTrace Γ w ∧
      ∃ L : ℝ≥0, ∀ z z', riemannianEDistOf (G.restrictOpen Ko) (w z) (w z') ≤
        (L : ℝ≥0∞) * edist z z'}
    (∀ v ∈ SK, ∃ w ∈ SKo, riemannianDiskArea (G.restrictOpen Ko) w ≤ riemannianDiskArea G v) ∧
    (∀ w ∈ SKo, ι.comp w ∈ SK ∧
      riemannianDiskArea G (ι.comp w) = riemannianDiskArea (G.restrictOpen Ko) w) ∧
    sInf ((fun v : C(closedDisk, N) => riemannianDiskArea G v) '' SK) =
      sInf ((fun w : C(closedDisk, Ko) => riemannianDiskArea (G.restrictOpen Ko) w) '' SKo) := by
  intro ι SK SKo
  obtain ⟨X, hXc, β, ε, hε, hdρ, hβ0, hβ1, hβeq, hperp, hlie⟩ :=
    exists_collar_levelField_R7E G hρ (lo := -b - δ) (hi := -b) (by linarith) hη hcpt hcoll
  have hhib : -b < -b + ε := by linarith
  have hΓfix : ∀ c, -b - δ ≤ c → ∀ θ, collarProj_R7E X hXc ρ c (ι.comp Γ θ) = ι.comp Γ θ :=
    fun c hc θ => collarProj_of_le_R7E X hXc (by
      change ρ (Γ θ : N) ≤ c
      linarith [hΓρ θ])
  -- (a)
  have hA : ∀ v ∈ SK, ∃ w ∈ SKo,
      riemannianDiskArea (G.restrictOpen Ko) w ≤ riemannianDiskArea G v := by
    rintro v ⟨hvK, hvt, L, hvL⟩
    obtain ⟨c, hc, hcS⟩ := exists_mem_Ioo_notMem_of_countable_R7E
      (countable_not_null_level_R7E hρ.continuous v.continuous)
      (show -b - δ < -b by linarith)
    have hnull : volume ({z : ℂ | ρ (diskExtension v z) = c} ∩ Metric.closedBall 0 1) = 0 := by
      by_contra h
      exact hcS h
    let Rv : C(closedDisk, N) :=
      ⟨collarProj_R7E X hXc ρ c ∘ v, (continuous_collarProj_R7E X hXc hρ.continuous c).comp
        v.continuous⟩
    have hRvO : Set.range Rv ⊆ Ko := by
      rintro _ ⟨z, rfl⟩
      change collarProj_R7E X hXc ρ c (v z) ∈ (Ko : Set N)
      rw [hKo]
      exact collarProj_mem_interior_of_mem_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hhib.le hKρ hfr
        hKcomp (by linarith [hc.1]) hc.2 (hvK ⟨z, rfl⟩)
    have hRvt : DiskWeakJordanTrace (ι.comp Γ) Rv :=
      diskWeakJordanTrace_comp_of_fix_R7E hvt
        ⟨collarProj_R7E X hXc ρ c, continuous_collarProj_R7E X hXc hρ.continuous c⟩
        (hΓfix c hc.1.le)
    obtain ⟨K₁, hK₁⟩ := lipschitz_collarProj_comp_R7E X hXc hρ G c hvL
    obtain ⟨K₂, hK₂⟩ := lipschitz_liftToOpen_R7E G Ko hRvO (V := Rv) (L := K₁) hK₁
    refine ⟨liftToOpen_AT Rv hRvO,
      ⟨diskWeakJordanTrace_liftToOpen_AT (fun θ => rfl) hRvt hRvO, K₂, hK₂⟩, ?_⟩
    rw [riemannianDiskArea_restrictOpen]
    change riemannianDiskArea G (collarProj_R7E X hXc ρ c ∘ v) ≤ _
    exact riemannianDiskArea_collarProj_le_R7E X hXc G hρ hdρ hβ0 hβ1 hβeq hperp
      (by linarith [hc.1]) hc.1.le hhib hlie hvL (fun z => hKρ (hvK ⟨z, rfl⟩)) hnull
  -- (b)
  have hB : ∀ w ∈ SKo, ι.comp w ∈ SK ∧
      riemannianDiskArea G (ι.comp w) = riemannianDiskArea (G.restrictOpen Ko) w := by
    rintro w ⟨hwt, L, hwL⟩
    refine ⟨⟨?_, diskWeakJordanTrace_comp_val_AT (fun θ => rfl) hwt, L, fun z z' =>
      (riemannianEDistOf_le_restrictOpen G Ko (w z) (w z')).trans (hwL z z')⟩, ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact interior_subset (show ((w z : Ko) : N) ∈ interior K by rw [← hKo]; exact (w z).2)
    · exact (riemannianDiskArea_restrictOpen G Ko w).symm
  refine ⟨hA, hB, ?_⟩
  -- (c)
  have hbddK : BddBelow ((fun v : C(closedDisk, N) => riemannianDiskArea G v) '' SK) :=
    ⟨0, by rintro _ ⟨v, -, rfl⟩; exact riemannianDiskArea_nonneg G v⟩
  have hbddKo : BddBelow ((fun w : C(closedDisk, Ko) =>
      riemannianDiskArea (G.restrictOpen Ko) w) '' SKo) :=
    ⟨0, by rintro _ ⟨w, -, rfl⟩; exact riemannianDiskArea_nonneg _ w⟩
  have hsub : (fun w : C(closedDisk, Ko) => riemannianDiskArea (G.restrictOpen Ko) w) '' SKo ⊆
      (fun v : C(closedDisk, N) => riemannianDiskArea G v) '' SK := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨ι.comp w, (hB w hw).1, (hB w hw).2⟩
  rcases ((fun v : C(closedDisk, N) => riemannianDiskArea G v) '' SK).eq_empty_or_nonempty with
    hemp | hne
  · have hemp' : (fun w : C(closedDisk, Ko) => riemannianDiskArea (G.restrictOpen Ko) w) '' SKo =
        ∅ := subset_empty_iff.mp (hemp ▸ hsub)
    rw [hemp, hemp']
  · have hne' : ((fun w : C(closedDisk, Ko) =>
        riemannianDiskArea (G.restrictOpen Ko) w) '' SKo).Nonempty := by
      obtain ⟨_, ⟨v, hv, rfl⟩⟩ := hne
      obtain ⟨w, hw, -⟩ := hA v hv
      exact ⟨_, w, hw, rfl⟩
    apply le_antisymm
    · exact csInf_le_csInf hbddK hne' hsub
    · apply le_csInf hne
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, hle⟩ := hA v hv
      exact (csInf_le hbddKo ⟨w, hw, rfl⟩).trans hle

end DifferentialGeometry.Geometry
