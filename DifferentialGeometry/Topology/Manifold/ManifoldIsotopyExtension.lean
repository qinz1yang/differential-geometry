import DifferentialGeometry.Topology.Manifold.BallChartStraightening
import DifferentialGeometry.Topology.Manifold.EmbeddedBallContraction
import DifferentialGeometry.Topology.Manifold.OrientedBallChartStraightening
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology (BallChart)

namespace DifferentialGeometry.Topology.Manifold

private abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

private def modelScaleDiffeomorph (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ where
  toEquiv :=
    { toFun := fun x => s • x
      invFun := fun x => s⁻¹ • x
      left_inv := fun x => by simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
      right_inv := fun x => by simp only [smul_smul, mul_inv_cancel₀ hs, one_smul] }
  contMDiff_toFun := (contDiff_const_smul s).contMDiff
  contMDiff_invFun := (contDiff_const_smul s⁻¹).contMDiff

private theorem modelScaleDiffeomorph_apply (n : ℕ) (s : ℝ) (hs : s ≠ 0) (x : Euc n) :
    modelScaleDiffeomorph n s hs x = s • x := rfl

private theorem det_comp_clm {n : ℕ} (f g : Euc n →L[ℝ] Euc n) :
    (f.comp g).det = f.det * g.det := by
  have hcoe : (((f.comp g : Euc n →L[ℝ] Euc n)) : Euc n →ₗ[ℝ] Euc n)
      = ((f : Euc n →ₗ[ℝ] Euc n)).comp (g : Euc n →ₗ[ℝ] Euc n) :=
    LinearMap.ext fun x => rfl
  change LinearMap.det ((f.comp g : Euc n →L[ℝ] Euc n) : Euc n →ₗ[ℝ] Euc n)
      = LinearMap.det (f : Euc n →ₗ[ℝ] Euc n) * LinearMap.det (g : Euc n →ₗ[ℝ] Euc n)
  rw [hcoe, LinearMap.det_comp]

private theorem det_smul_one_clm {n : ℕ} (c : ℝ) :
    (c • (1 : Euc n →L[ℝ] Euc n)).det = c ^ n := by
  change LinearMap.det (c • (1 : Euc n →ₗ[ℝ] Euc n)) = c ^ n
  rw [LinearMap.det_smul,
    show LinearMap.det (1 : Euc n →ₗ[ℝ] Euc n) = (1 : ℝ) from map_one _, mul_one,
    show Module.finrank ℝ (Euc n) = n from by simp]

theorem exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius {n : ℕ}
    (φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞)
    {ρ : ℝ} (hρ : 0 < ρ)
    (h₀ : closedBall (0 : Euc n) ρ ⊆ φ₀.source)
    (h₁ : closedBall (0 : Euc n) ρ ⊆ φ₁.source)
    {V : Set (Euc n)} (hV : IsOpen V)
    (hV₀ : φ₀ '' closedBall (0 : Euc n) ρ ⊆ V)
    (hV₁ : φ₁ '' closedBall (0 : Euc n) ρ ⊆ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • φ₀ 0 + t • φ₁ 0 ∈ V)
    (hori : 0 < (fderiv ℝ (φ₀ : Euc n → Euc n) 0).det *
      (fderiv ℝ (φ₁ : Euc n → Euc n) 0).det) :
    ∃ J : ℝ → Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞,
      ContDiff ℝ ∞ (fun q : ℝ × Euc n => J q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × Euc n => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl 𝓘(ℝ, Euc n) (Euc n) ∞ ∧
      (∀ x ∈ closedBall (0 : Euc n) ρ, J 1 (φ₀ x) = φ₁ x) ∧
      ∃ K : Set (Euc n), IsCompact K ∧ K ⊆ V ∧
        ∀ t y, y ∉ K → J t y = y ∧ (J t).symm y = y := by
  have hcpos : (0 : ℝ) < ρ / 2 := by linarith
  have hcne : ρ / 2 ≠ 0 := ne_of_gt hcpos
  let σ : PartialDiffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ :=
    (modelScaleDiffeomorph n (ρ / 2) hcne).toPartialDiffeomorph
  have hσcoe : (σ : Euc n → Euc n) = fun y => (ρ / 2) • y := rfl
  have hσ0 : σ (0 : Euc n) = 0 := by
    rw [hσcoe]
    simp
  have hsmul_mem : ∀ y : Euc n, ‖y‖ ≤ 2 → ‖(ρ / 2) • y‖ ≤ ρ := by
    intro y hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    have h := mul_le_mul_of_nonneg_left hy hcpos.le
    linarith
  have hφ₀diff : DifferentiableAt ℝ (φ₀ : Euc n → Euc n) (0 : Euc n) :=
    (φ₀.contMDiffOn_toFun.contDiffOn.contDiffAt
      (φ₀.open_source.mem_nhds (h₀ (mem_closedBall_self hρ.le)))).differentiableAt (by simp)
  have hφ₁diff : DifferentiableAt ℝ (φ₁ : Euc n → Euc n) (0 : Euc n) :=
    (φ₁.contMDiffOn_toFun.contDiffOn.contDiffAt
      (φ₁.open_source.mem_nhds (h₁ (mem_closedBall_self hρ.le)))).differentiableAt (by simp)
  have hσdiff : DifferentiableAt ℝ (fun y : Euc n => (ρ / 2) • y) (0 : Euc n) :=
    (ContinuousLinearMap.hasFDerivAt ((ρ / 2) • (1 : Euc n →L[ℝ] Euc n))
      (x := (0 : Euc n))).differentiableAt
  have hσfderiv : fderiv ℝ (fun y : Euc n => (ρ / 2) • y) (0 : Euc n)
      = (ρ / 2) • (1 : Euc n →L[ℝ] Euc n) :=
    (ContinuousLinearMap.hasFDerivAt ((ρ / 2) • (1 : Euc n →L[ℝ] Euc n))
      (x := (0 : Euc n))).fderiv
  have hdetσ : (fderiv ℝ (fun y : Euc n => (ρ / 2) • y) 0).det = (ρ / 2) ^ n := by
    rw [hσfderiv, det_smul_one_clm]
  have hφ₀diff' : DifferentiableAt ℝ (φ₀ : Euc n → Euc n) ((ρ / 2) • (0 : Euc n)) := by
    rw [smul_zero]
    exact hφ₀diff
  have hφ₁diff' : DifferentiableAt ℝ (φ₁ : Euc n → Euc n) ((ρ / 2) • (0 : Euc n)) := by
    rw [smul_zero]
    exact hφ₁diff
  have hchain₀ : fderiv ℝ ((σ.trans φ₀ : PartialDiffeomorph _ _ _ _ _) : Euc n → Euc n) 0
      = (fderiv ℝ (φ₀ : Euc n → Euc n) 0).comp
        (fderiv ℝ (fun y : Euc n => (ρ / 2) • y) 0) := by
    have hcoe : ((σ.trans φ₀ : PartialDiffeomorph _ _ _ _ _) : Euc n → Euc n)
        = fun y : Euc n => φ₀ ((ρ / 2) • y) := rfl
    rw [hcoe]
    have h := fderiv_comp (x := (0 : Euc n)) hφ₀diff' hσdiff
    simpa only [Function.comp_def, smul_zero] using h
  have hchain₁ : fderiv ℝ ((σ.trans φ₁ : PartialDiffeomorph _ _ _ _ _) : Euc n → Euc n) 0
      = (fderiv ℝ (φ₁ : Euc n → Euc n) 0).comp
        (fderiv ℝ (fun y : Euc n => (ρ / 2) • y) 0) := by
    have hcoe : ((σ.trans φ₁ : PartialDiffeomorph _ _ _ _ _) : Euc n → Euc n)
        = fun y : Euc n => φ₁ ((ρ / 2) • y) := rfl
    rw [hcoe]
    have h := fderiv_comp (x := (0 : Euc n)) hφ₁diff' hσdiff
    simpa only [Function.comp_def, smul_zero] using h
  have hdet₀ : (fderiv ℝ (((σ.trans φ₀ : PartialDiffeomorph _ _ _ _ _) :
        Euc n → Euc n)) 0).det
      = (fderiv ℝ (φ₀ : Euc n → Euc n) 0).det * (ρ / 2) ^ n := by
    rw [hchain₀, det_comp_clm, hdetσ]
  have hdet₁ : (fderiv ℝ (((σ.trans φ₁ : PartialDiffeomorph _ _ _ _ _) :
        Euc n → Euc n)) 0).det
      = (fderiv ℝ (φ₁ : Euc n → Euc n) 0).det * (ρ / 2) ^ n := by
    rw [hchain₁, det_comp_clm, hdetσ]
  have hpow : (0 : ℝ) < ((ρ / 2) ^ n) * ((ρ / 2) ^ n) := by positivity
  have hori' : 0 < (fderiv ℝ ((σ.trans φ₀ : PartialDiffeomorph _ _ _ _ _) :
        Euc n → Euc n) 0).det *
      (fderiv ℝ ((σ.trans φ₁ : PartialDiffeomorph _ _ _ _ _) : Euc n → Euc n) 0).det := by
    rw [hdet₀, hdet₁]
    nlinarith [hori, hpow]
  have h₀' : closedBall (0 : Euc n) 2 ⊆ (σ.trans φ₀).source := by
    intro y hy
    rw [PartialDiffeomorph.trans_source]
    refine ⟨mem_univ y, ?_⟩
    have hy' : ‖y‖ ≤ 2 := by simpa [mem_closedBall_zero_iff] using hy
    exact h₀ (by simpa [hσcoe, mem_closedBall_zero_iff] using hsmul_mem y hy')
  have h₁' : closedBall (0 : Euc n) 2 ⊆ (σ.trans φ₁).source := by
    intro y hy
    rw [PartialDiffeomorph.trans_source]
    refine ⟨mem_univ y, ?_⟩
    have hy' : ‖y‖ ≤ 2 := by simpa [mem_closedBall_zero_iff] using hy
    exact h₁ (by simpa [hσcoe, mem_closedBall_zero_iff] using hsmul_mem y hy')
  have hV₀' : (σ.trans φ₀) '' closedBall (0 : Euc n) 2 ⊆ V := by
    rintro y ⟨x, hx, rfl⟩
    refine hV₀ ⟨(ρ / 2) • x, ?_, rfl⟩
    have hx' : ‖x‖ ≤ 2 := by simpa [mem_closedBall_zero_iff] using hx
    simpa [mem_closedBall_zero_iff] using hsmul_mem x hx'
  have hV₁' : (σ.trans φ₁) '' closedBall (0 : Euc n) 2 ⊆ V := by
    rintro y ⟨x, hx, rfl⟩
    refine hV₁ ⟨(ρ / 2) • x, ?_, rfl⟩
    have hx' : ‖x‖ ≤ 2 := by simpa [mem_closedBall_zero_iff] using hx
    simpa [mem_closedBall_zero_iff] using hsmul_mem x hx'
  have hseg' : ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • (σ.trans φ₀) 0 + t • (σ.trans φ₁) 0 ∈ V := by
    intro t ht
    have h0 : (σ.trans φ₀) 0 = φ₀ 0 := by
      rw [PartialDiffeomorph.trans_apply, hσ0]
    have h1 : (σ.trans φ₁) 0 = φ₁ 0 := by
      rw [PartialDiffeomorph.trans_apply, hσ0]
    rw [h0, h1]
    exact hseg t ht
  obtain ⟨J, hJc, hJi, hJ0, hJact, K, hKc, hKV, hKfix⟩ :=
    exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset
      (σ.trans φ₀) (σ.trans φ₁) h₀' h₁' hV hV₀' hV₁' hseg' hori'
  refine ⟨J, hJc, hJi, hJ0, ?_, K, hKc, hKV, hKfix⟩
  intro x hx
  have hx' : ‖x‖ ≤ ρ := by simpa [mem_closedBall_zero_iff] using hx
  have hσinv : (ρ / 2) • ((ρ / 2)⁻¹ • x) = x := by
    exact smul_inv_smul₀ hcne x
  have hzmem : ‖(ρ / 2)⁻¹ • x‖ ≤ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    rw [inv_mul_le_iff₀ hcpos]
    linarith
  have h := hJact ((ρ / 2)⁻¹ • x) (by simpa [mem_closedBall_zero_iff] using hzmem)
  have hcoe₀ : ((σ.trans φ₀ : PartialDiffeomorph _ _ _ _ _) : Euc n → Euc n)
      = fun y : Euc n => φ₀ ((ρ / 2) • y) := rfl
  have hcoe₁ : ((σ.trans φ₁ : PartialDiffeomorph _ _ _ _ _) : Euc n → Euc n)
      = fun y : Euc n => φ₁ ((ρ / 2) • y) := rfl
  rw [hcoe₀, hcoe₁] at h
  simpa only [hσinv] using h

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology.Manifold
  (exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius) in
theorem exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius_satisfiable :
    ∃ (φ : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace ThreeSpace ∞)
      (J : ℝ → Diffeomorph ThreeModel ThreeModel ThreeSpace ThreeSpace ∞),
      Metric.closedBall (0 : ThreeSpace) 1 ⊆ φ.source ∧
      (∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1, J 1 (φ x) = φ x) ∧
      ∃ K : Set ThreeSpace, IsCompact K ∧ K ⊆ Set.univ ∧
        ∀ t y, y ∉ K → J t y = y ∧ (J t).symm y = y := by
  have hcoe : ((Diffeomorph.refl ThreeModel ThreeSpace ∞).toPartialDiffeomorph :
      ThreeSpace → ThreeSpace) = id := rfl
  have hdet : (fderiv ℝ ((Diffeomorph.refl ThreeModel ThreeSpace ∞).toPartialDiffeomorph :
      ThreeSpace → ThreeSpace) 0).det = 1 := by
    rw [hcoe, fderiv_id]
    change LinearMap.det (1 : ThreeSpace →ₗ[ℝ] ThreeSpace) = 1
    exact map_one _
  obtain ⟨J, -, -, -, hJact, K, hKc, hKV, hKfix⟩ :=
    exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius
      (ρ := 1)
      (Diffeomorph.refl ThreeModel ThreeSpace ∞).toPartialDiffeomorph
      (Diffeomorph.refl ThreeModel ThreeSpace ∞).toPartialDiffeomorph
      (by norm_num) (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
      isOpen_univ (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
      (fun _ _ => mem_univ _) (by rw [hdet]; norm_num)
  exact ⟨(Diffeomorph.refl ThreeModel ThreeSpace ∞).toPartialDiffeomorph, J,
    (fun _ _ => mem_univ _), hJact, K, hKc, hKV, hKfix⟩

def ballChartIsotopicAwayFromCompactOnClosedBall {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (b b' : BallChart 3 (𝓡 3) U) (C : Set U) (ρ : ℝ) : Prop :=
  ∃ (J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) (K : Set U),
    IsCompact K ∧ Disjoint K C ∧ J 0 = Diffeomorph.refl ThreeModel U ∞ ∧
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J q.1).symm q.2) ∧
    (∀ t, Set.EqOn (J t) (id : U → U) Kᶜ) ∧
    (∀ t, Set.EqOn (J t).symm (id : U → U) Kᶜ) ∧
    ∀ x ∈ Metric.closedBall (0 : ThreeSpace) ρ, J 1 (b.chart x) = b'.chart x

theorem ballChartIsotopicAwayFromCompactOnClosedBall_of_modelIsotopy {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [T2Space U]
    (b b' : BallChart 3 (𝓡 3) U) (C : Set U) (ρ : ℝ)
    (D : ℝ → Diffeomorph ThreeModel ThreeModel ThreeSpace ThreeSpace ∞)
    (hDc : ContDiff ℝ ∞ (fun q : ℝ × ThreeSpace => D q.1 q.2))
    (hDi : ContDiff ℝ ∞ (fun q : ℝ × ThreeSpace => (D q.1).symm q.2))
    (hD0 : D 0 = Diffeomorph.refl ThreeModel ThreeSpace ∞)
    {K : Set ThreeSpace} (hK : IsCompact K) (hKt : K ⊆ b'.chart.source)
    (hKfix : ∀ t z, z ∉ K → D t z = z ∧ (D t).symm z = z)
    (havoid : Disjoint (b'.chart '' K) C)
    (hover : b.chart '' Metric.closedBall (0 : ThreeSpace) ρ ⊆ b'.chart.target)
    (hact : ∀ x ∈ Metric.closedBall (0 : ThreeSpace) ρ,
      D 1 (b'.chart.symm (b.chart x)) = x) :
    ballChartIsotopicAwayFromCompactOnClosedBall b b' C ρ := by
  obtain ⟨J, hJc, hJi, hJe, hKc, -, hKfixU⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_partial_chart_family
      (P := ℝ) b'.chart.symm.toOpenPartialHomeomorph b'.chart.contMDiffOn_invFun
      b'.chart.contMDiffOn_toFun D hDc hDi hK hKt hKfix
  have hset : (b'.chart.symm.toOpenPartialHomeomorph.symm : OpenPartialHomeomorph ThreeSpace U) '' K
      = b'.chart '' K := rfl
  have hJ0 : J 0 = Diffeomorph.refl ThreeModel U ∞ := by
    apply Diffeomorph.ext
    intro y
    rw [(hJe 0 y).1]
    by_cases hy : y ∈ b'.chart.symm.toOpenPartialHomeomorph.source
    · have h1 : DifferentialGeometry.Topology.Manifold.extendChartById
            b'.chart.symm.toOpenPartialHomeomorph (D 0) y
          = b'.chart.symm.toOpenPartialHomeomorph.symm
            (b'.chart.symm.toOpenPartialHomeomorph y) := by
        rw [hD0]
        exact ite_eq_left hy
      rw [h1, OpenPartialHomeomorph.left_inv _ hy]
      simp only [Diffeomorph.coe_refl, id_eq]
    · have h2 : DifferentialGeometry.Topology.Manifold.extendChartById
            b'.chart.symm.toOpenPartialHomeomorph (D 0) y = y := by
        rw [hD0]
        exact ite_eq_right hy
      rw [h2]
      rfl
  refine ⟨J, b'.chart.symm.toOpenPartialHomeomorph.symm '' K, hKc, ?_, hJ0, hJc, hJi, ?_, ?_,
    ?_⟩
  · rw [hset]
    exact havoid
  · intro t x hx
    exact (hKfixU t x hx).1
  · intro t x hx
    exact (hKfixU t x hx).2
  · intro x hx
    rw [(hJe 1 (b.chart x)).1,
      DifferentialGeometry.Topology.extendChartById_chartSymm_of_target b' (D 1)
        (hover ⟨x, hx, rfl⟩),
      hact x hx]

open DifferentialGeometry.Topology.Manifold in
theorem ballChartIsotopicAwayFromCompactOnClosedBall_of_closedBallComparison_and_tube
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    [T2Space U] (b b' : BallChart 3 (𝓡 3) U) (C : Set U) {ρ : ℝ} (hρ : 0 < ρ)
    (hsrc : Metric.closedBall (0 : ThreeSpace) ρ ⊆ b.chart.source)
    (hsrc' : Metric.closedBall (0 : ThreeSpace) ρ ⊆ b'.chart.source)
    (hC : IsCompact C)
    (hcmp : b.chart '' Metric.closedBall (0 : ThreeSpace) ρ ⊆ b'.chart.target)
    (hdisj : Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) ρ) C)
    (hdisj' : Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) ρ) C)
    (hdet : 0 < (fderiv ℝ (fun x : ThreeSpace => b'.chart.symm (b.chart x)) 0).det)
    (htube : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 - t) • (b'.chart.symm (b.chart 0)) + t • (0 : ThreeSpace)
        ∈ b'.chart.source ∩ b'.chart ⁻¹' Cᶜ) :
    ballChartIsotopicAwayFromCompactOnClosedBall b b' C ρ := by
  classical
  let ψ : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace ThreeSpace ∞ :=
    b.chart.trans b'.chart.symm
  have hψcoe : (ψ : ThreeSpace → ThreeSpace)
      = fun y : ThreeSpace => b'.chart.symm (b.chart y) := rfl
  have hψ0 : ψ (0 : ThreeSpace) = b'.chart.symm (b.chart 0) := rfl
  have hψsrc : Metric.closedBall (0 : ThreeSpace) ρ ⊆ ψ.source := by
    intro y hy
    rw [PartialDiffeomorph.trans_source]
    exact ⟨hsrc hy, hcmp ⟨y, hy, rfl⟩⟩
  have hψcont : ContinuousOn (fun y : ThreeSpace => b'.chart.symm (b.chart y))
      (Metric.closedBall (0 : ThreeSpace) ρ) := by
    refine (b'.chart.symm.contMDiffOn_toFun.continuousOn).comp ?_ fun x hx => ?_
    · exact b.chart.contMDiffOn_toFun.continuousOn.mono fun x hx => hsrc hx
    · exact hcmp ⟨x, hx, rfl⟩
  have hsegcont : Continuous fun t : ℝ =>
      (1 - t) • (b'.chart.symm (b.chart 0)) + t • (0 : ThreeSpace) := by fun_prop
  let A : Set ThreeSpace := Metric.closedBall (0 : ThreeSpace) ρ ∪
    (fun y : ThreeSpace => b'.chart.symm (b.chart y)) '' Metric.closedBall (0 : ThreeSpace) ρ ∪
    (fun t : ℝ => (1 - t) • (b'.chart.symm (b.chart 0)) + t • (0 : ThreeSpace)) ''
      Set.Icc (0 : ℝ) 1
  have hAc : IsCompact A := by
    have h1 : IsCompact ((fun y : ThreeSpace => b'.chart.symm (b.chart y)) ''
        Metric.closedBall (0 : ThreeSpace) ρ) :=
      (isCompact_closedBall (0 : ThreeSpace) ρ).image_of_continuousOn hψcont
    have h2 : IsCompact ((fun t : ℝ =>
        (1 - t) • (b'.chart.symm (b.chart 0)) + t • (0 : ThreeSpace)) '' Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.image hsegcont
    exact ((isCompact_closedBall (0 : ThreeSpace) ρ).union h1).union h2
  have hAW : A ⊆ b'.chart.source ∩ b'.chart ⁻¹' Cᶜ := by
    rintro z ((hz1 | hz2) | hz3)
    · exact ⟨hsrc' hz1, Set.disjoint_left.mp hdisj' ⟨z, hz1, rfl⟩⟩
    · obtain ⟨y, hy, rfl⟩ := hz2
      have hytgt : b.chart y ∈ b'.chart.target := hcmp ⟨y, hy, rfl⟩
      refine ⟨PartialEquiv.map_target b'.chart.toPartialEquiv hytgt, ?_⟩
      simpa only [Set.mem_preimage] using by
        rw [PartialDiffeomorph.apply_symm_apply b'.chart hytgt]
        exact Set.disjoint_left.mp hdisj ⟨y, hy, rfl⟩
    · obtain ⟨t, ht, rfl⟩ := hz3
      exact htube t ht
  obtain ⟨δ, hδpos, hδsub⟩ := hAc.exists_cthickening_subset_open
    (b'.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage b'.chart.open_source
      hC.isClosed.isOpen_compl) hAW
  have hVW : Metric.thickening δ A ⊆ b'.chart.source ∩ b'.chart ⁻¹' Cᶜ :=
    fun z hz => hδsub (Metric.thickening_subset_cthickening δ A hz)
  have hAV : A ⊆ Metric.thickening δ A := Metric.self_subset_thickening hδpos A
  have hVA : Metric.closedBall (0 : ThreeSpace) ρ ⊆ Metric.thickening δ A :=
    fun z hz => hAV (Or.inl (Or.inl hz))
  let φ₁ : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace ThreeSpace ∞ :=
    (Diffeomorph.refl ThreeModel ThreeSpace ∞).toPartialDiffeomorph
  have hφ₁coe : (φ₁ : ThreeSpace → ThreeSpace) = id := rfl
  have hφ₁src : Metric.closedBall (0 : ThreeSpace) ρ ⊆ φ₁.source := fun _ _ => mem_univ _
  have hVψ : ψ '' Metric.closedBall (0 : ThreeSpace) ρ ⊆ Metric.thickening δ A :=
    fun z ⟨y, hy, hzy⟩ => hAV (Or.inl (Or.inr ⟨y, hy, hzy⟩))
  have hVid : φ₁ '' Metric.closedBall (0 : ThreeSpace) ρ ⊆ Metric.thickening δ A :=
    fun z ⟨y, hy, hzy⟩ => hzy ▸ hVA hy
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 - t) • ψ 0 + t • φ₁ 0 ∈ Metric.thickening δ A := by
    intro t ht
    have h0 : ψ (0 : ThreeSpace) = b'.chart.symm (b.chart 0) := rfl
    have h1 : φ₁ (0 : ThreeSpace) = 0 := rfl
    rw [h0, h1]
    exact hAV (Or.inr ⟨t, ht, rfl⟩)
  have hdetid : (fderiv ℝ (φ₁ : ThreeSpace → ThreeSpace) 0).det = 1 := by
    rw [hφ₁coe, fderiv_id]
    change LinearMap.det (1 : ThreeSpace →ₗ[ℝ] ThreeSpace) = 1
    exact map_one _
  have hori : 0 < (fderiv ℝ (ψ : ThreeSpace → ThreeSpace) 0).det *
      (fderiv ℝ (φ₁ : ThreeSpace → ThreeSpace) 0).det := by
    rw [hdetid, mul_one]
    rwa [hψcoe]
  obtain ⟨M, hMc, hMi, hM0, hMact, KM, hKMc, hKMV, hKMfix⟩ :=
    exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius
      ψ φ₁ hρ hψsrc hφ₁src Metric.isOpen_thickening hVψ hVid hseg hori
  refine ballChartIsotopicAwayFromCompactOnClosedBall_of_modelIsotopy b b' C ρ M hMc hMi hM0
    hKMc (fun z hz => (hVW (hKMV hz)).1) hKMfix ?_ hcmp ?_
  · rw [Set.disjoint_left]
    rintro z ⟨k, hk, rfl⟩ hzC
    exact (hVW (hKMV hk)).2 hzC
  · intro x hx
    exact hMact x hx

theorem orientedBallChartIsotopicAwayFromCompact_of_centerComparison_and_tube
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    [T2Space U] (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o)
    (C : Set U)
    (hC : IsCompact C)
    (hdisj : Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C)
    (hdisj' : Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C)
    (hcenter : b.chart 0 ∈ b'.chart.target)
    (hdet : 0 < (fderiv ℝ (fun x : ThreeSpace => b'.chart.symm (b.chart x)) 0).det)
    (htube : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 - t) • (b'.chart.symm (b.chart 0)) + t • (0 : ThreeSpace)
        ∈ b'.chart.source ∩ b'.chart ⁻¹' Cᶜ) :
    orientedBallChartIsotopicAwayFromCompact o b b' C := by
  classical
  have h0src : (0 : ThreeSpace) ∈ b.chart.source :=
    b.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hcontb : ContinuousAt (b.chart : ThreeSpace → U) (0 : ThreeSpace) :=
    b.chart.contMDiffOn_toFun.continuousOn.continuousAt (b.chart.open_source.mem_nhds h0src)
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ :=
    Metric.mem_nhds_iff.mp (hcontb (b'.chart.open_target.mem_nhds hcenter))
  set ε : ℝ := min ε₀ 1 / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    have : (0 : ℝ) < min ε₀ 1 := lt_min hε₀pos (by norm_num)
    linarith
  have hεlt : ε < ε₀ := by
    rw [hεdef]
    have hle : min ε₀ 1 ≤ ε₀ := min_le_left _ _
    linarith
  have hεle : ε ≤ 1 := by
    rw [hεdef]
    have := min_le_right ε₀ (1 : ℝ)
    linarith
  have hεcmp : b.chart '' Metric.closedBall (0 : ThreeSpace) ε ⊆ b'.chart.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact hε₀sub (Metric.closedBall_subset_ball hεlt hx)
  have hVbopen : IsOpen (b.chart.target ∩ Cᶜ) :=
    b.chart.open_target.inter hC.isClosed.isOpen_compl
  have hbVb : b.chart '' Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.chart.target ∩ Cᶜ :=
    fun z ⟨x, hx, hzx⟩ =>
      ⟨hzx ▸ PartialEquiv.map_source b.chart.toPartialEquiv
          (b.closedBall_subset_source (Metric.closedBall_subset_closedBall (by norm_num) hx)),
        Set.disjoint_left.mp hdisj ⟨x, hx, hzx⟩⟩
  have hVdopen : IsOpen (b'.chart.target ∩ Cᶜ) :=
    b'.chart.open_target.inter hC.isClosed.isOpen_compl
  have hdVd : b'.chart '' Metric.closedBall (0 : ThreeSpace) 1 ⊆ b'.chart.target ∩ Cᶜ :=
    fun z ⟨x, hx, hzx⟩ =>
      ⟨hzx ▸ PartialEquiv.map_source b'.chart.toPartialEquiv
          (b'.closedBall_subset_source (Metric.closedBall_subset_closedBall (by norm_num) hx)),
        Set.disjoint_left.mp hdisj' ⟨x, hx, hzx⟩⟩
  obtain ⟨A, hAc, hAi, hA0, hArad, KA, hKAc, hKAV, -, hKAfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorphs_contracting_embedded_closedBall
      b.chart (r := 1) (by norm_num)
      (fun z hz => b.closedBall_subset_source
        (Metric.closedBall_subset_closedBall (by norm_num) hz))
      hVbopen hbVb
  obtain ⟨Df, hDfc, hDfi, hDf0, hDfrad, KD, hKDc, hKDV, -, hKDfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorphs_contracting_embedded_closedBall
      b'.chart (r := 1) (by norm_num)
      (fun z hz => b'.closedBall_subset_source
        (Metric.closedBall_subset_closedBall (by norm_num) hz))
      hVdopen hdVd
  set s : ℝ := max 0 (Real.log (2 / ε)) with hsdef
  have hsnn : 0 ≤ s := le_max_left _ _
  have hexple : Real.exp (-s) ≤ ε / 2 := by
    have h1 : Real.log (2 / ε) ≤ s := le_max_right _ _
    have h2 : Real.exp (-s) ≤ Real.exp (-(Real.log (2 / ε))) := Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (-(Real.log (2 / ε))) = ε / 2 := by
      have h4 : -(Real.log (2 / ε)) = Real.log (ε / 2) := by
        rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hεpos.ne',
          Real.log_div hεpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      rw [h4, Real.exp_log (by positivity : (0 : ℝ) < ε / 2)]
    linarith [h2, h3.le, h3.ge]
  set ρ : ℝ := Real.exp (-s) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact Real.exp_pos _
  have hρε : ρ ≤ ε := by
    have := hexple
    linarith
  have hρ1 : ρ ≤ 1 := by
    have := hexple
    linarith
  have hsrcρ : Metric.closedBall (0 : ThreeSpace) ρ ⊆ b.chart.source := fun z hz =>
    b.closedBall_subset_source (Metric.closedBall_subset_closedBall (by linarith) hz)
  have hsrcρ' : Metric.closedBall (0 : ThreeSpace) ρ ⊆ b'.chart.source := fun z hz =>
    b'.closedBall_subset_source (Metric.closedBall_subset_closedBall (by linarith) hz)
  have hcmpρ : b.chart '' Metric.closedBall (0 : ThreeSpace) ρ ⊆ b'.chart.target :=
    fun z ⟨x, hx, hzx⟩ =>
      hεcmp ⟨x, Metric.closedBall_subset_closedBall hρε hx, hzx⟩
  have hdisjρ : Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) ρ) C :=
    hdisj.mono_left (Set.image_mono (Metric.closedBall_subset_closedBall hρ1))
  have hdisjρ' : Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) ρ) C :=
    hdisj'.mono_left (Set.image_mono (Metric.closedBall_subset_closedBall hρ1))
  obtain ⟨G, KG, hKGc, hKGdisj, hG0, hGc, hGi, hGfix, hGfixi, hGact⟩ :=
    ballChartIsotopicAwayFromCompactOnClosedBall_of_closedBallComparison_and_tube
      b.toBallChart b'.toBallChart C hρpos hsrcρ hsrcρ' hC hcmpρ hdisjρ hdisjρ' hdet htube
  set E : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞ := fun t => A (t * s) with hEdef
  set Fm : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞ :=
    fun t => (Df (t * s)).symm with hFdef
  set J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞ :=
    fun t => (E t).trans ((G t).trans (Fm t)) with hJdef
  have hJapply : ∀ t y, J t y = Fm t (G t (E t y)) := fun t y => rfl
  have hJ0 : J 0 = Diffeomorph.refl ThreeModel U ∞ := by
    apply Diffeomorph.ext
    intro y
    rw [hJapply, hEdef, hFdef]
    simp only [zero_mul, hA0, hG0, Diffeomorph.coe_refl, id_eq, hDf0]
    rfl
  have hJc : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J q.1 q.2) := by
    have hm : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × U => (q.1 * s, q.2)) :=
      (contMDiff_fst.mul contMDiff_const).prodMk contMDiff_snd
    have hEc : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => E q.1 q.2) := by
      have h := hAc.comp hm
      have he : (fun q : ℝ × U => E q.1 q.2) = fun q : ℝ × U => A (q.1 * s) q.2 := by
        funext q
        rw [hEdef]
      rw [he]
      exact h
    have hFc : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => Fm q.1 q.2) := by
      have h := hDfi.comp hm
      have he : (fun q : ℝ × U => Fm q.1 q.2) =
          fun q : ℝ × U => (Df (q.1 * s)).symm q.2 := by
        funext q
        rw [hFdef]
      rw [he]
      exact h
    have hm1 : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × U => (q.1, E q.1 q.2)) := contMDiff_fst.prodMk hEc
    have hinner : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => G q.1 (E q.1 q.2)) := hGc.comp hm1
    have hm2 : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × U => (q.1, G q.1 (E q.1 q.2))) := contMDiff_fst.prodMk hinner
    have h := hFc.comp hm2
    have he : (fun q : ℝ × U => J q.1 q.2) =
        fun q : ℝ × U => Fm q.1 (G q.1 (E q.1 q.2)) := by
      funext q
      exact hJapply q.1 q.2
    rw [he]
    exact h
  have hJsymm : ∀ t y, (J t).symm y = (E t).symm ((G t).symm ((Fm t).symm y)) := by
    intro t y
    have h : J t ((E t).symm ((G t).symm ((Fm t).symm y))) = y := by
      rw [hJapply]
      rw [Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply,
        Diffeomorph.apply_symm_apply]
    have hs := Diffeomorph.symm_apply_apply (J t) ((E t).symm ((G t).symm ((Fm t).symm y)))
    rw [h] at hs
    exact hs
  have hJi : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J q.1).symm q.2) := by
    have hm : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × U => (q.1 * s, q.2)) :=
      (contMDiff_fst.mul contMDiff_const).prodMk contMDiff_snd
    have hEi : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => (E q.1).symm q.2) := by
      have h := hAi.comp hm
      have he : (fun q : ℝ × U => (E q.1).symm q.2) =
          fun q : ℝ × U => (A (q.1 * s)).symm q.2 := by
        funext q
        rw [hEdef]
      rw [he]
      exact h
    have hFi : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => (Fm q.1).symm q.2) := by
      have h := hDfc.comp hm
      have he : (fun q : ℝ × U => (Fm q.1).symm q.2) =
          fun q : ℝ × U => Df (q.1 * s) q.2 := by
        funext q
        rw [hFdef]
        rfl
      rw [he]
      exact h
    have hm1 : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × U => (q.1, (Fm q.1).symm q.2)) := contMDiff_fst.prodMk hFi
    have hinner : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => (G q.1).symm ((Fm q.1).symm q.2)) := hGi.comp hm1
    have hm2 : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × U => (q.1, (G q.1).symm ((Fm q.1).symm q.2))) :=
      contMDiff_fst.prodMk hinner
    have h := hEi.comp hm2
    have he : (fun q : ℝ × U => (J q.1).symm q.2) =
        fun q : ℝ × U => (E q.1).symm ((G q.1).symm ((Fm q.1).symm q.2)) := by
      funext q
      exact hJsymm q.1 q.2
    rw [he]
    exact h
  have hfixJ : ∀ t, Set.EqOn (J t) (id : U → U) (KA ∪ KG ∪ KD)ᶜ := by
    intro t z hz
    have hzA : z ∉ KA := fun h => hz (Or.inl (Or.inl h))
    have hzG : z ∉ KG := fun h => hz (Or.inl (Or.inr h))
    have hzD : z ∉ KD := fun h => hz (Or.inr h)
    have hE : E t z = z := by
      rw [hEdef]
      exact (hKAfix (t * s) z hzA).1
    have hF : Fm t z = z := by
      rw [hFdef]
      exact (hKDfix (t * s) z hzD).2
    have hG : G t z = z := hGfix t hzG
    change J t z = z
    rw [hJapply, hE, hG, hF]
  have hfixJi : ∀ t, Set.EqOn (J t).symm (id : U → U) (KA ∪ KG ∪ KD)ᶜ := by
    intro t z hz
    have hzA : z ∉ KA := fun h => hz (Or.inl (Or.inl h))
    have hzG : z ∉ KG := fun h => hz (Or.inl (Or.inr h))
    have hzD : z ∉ KD := fun h => hz (Or.inr h)
    have hE : (E t).symm z = z := by
      rw [hEdef]
      exact (hKAfix (t * s) z hzA).2
    have hF : (Fm t).symm z = z := by
      rw [hFdef]
      exact (hKDfix (t * s) z hzD).1
    have hG : (G t).symm z = z := hGfixi t hzG
    change (J t).symm z = z
    rw [hJsymm t z, hF, hG, hE]
  have hJact : ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1, J 1 (b.chart x) = b'.chart x := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := by simpa [mem_closedBall_zero_iff] using hx
    have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hsnn)
    have hxA : E 1 (b.chart x) = b.chart (Real.exp (-s) • x) := by
      rw [hEdef]
      simp only [one_mul]
      exact hArad s x hsnn hx
    have hmem : Real.exp (-s) • x ∈ Metric.closedBall (0 : ThreeSpace) ρ := by
      rw [hρdef, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      nlinarith [hx1, Real.exp_pos (-s), norm_nonneg x]
    have hFm : Fm 1 (b'.chart (Real.exp (-s) • x)) = b'.chart x := by
      rw [hFdef]
      simp only [one_mul]
      have hD : Df s (b'.chart x) = b'.chart (Real.exp (-s) • x) := hDfrad s x hsnn hx
      rw [← hD, Diffeomorph.symm_apply_apply]
    have hG : G 1 (b.chart (Real.exp (-s) • x)) = b'.chart (Real.exp (-s) • x) := hGact _ hmem
    rw [hJapply, hxA, hG, hFm]
  have hKdisj : Disjoint (KA ∪ KG ∪ KD) C := by
    rw [Set.disjoint_left]
    rintro z ((hzA | hzG) | hzD) hzC
    · exact (hKAV hzA).2 hzC
    · exact Set.disjoint_left.mp hKGdisj hzG hzC
    · exact (hKDV hzD).2 hzC
  exact ⟨J, KA ∪ KG ∪ KD, (hKAc.union hKGc).union hKDc, hKdisj, hJ0, hJc, hJi, hfixJ, hfixJi,
    hJact⟩

theorem orientedBallChartIsotopicAwayFromCompact_centerComparison_hypotheses_satisfiable
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (b : OrientedBallEmbedding U o) :
    ∃ (b' : OrientedBallEmbedding U o) (C : Set U), IsCompact C ∧
      b.chart '' Metric.closedBall (0 : ThreeSpace) 1 ⊆ b'.chart.target ∧
      Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C ∧
      Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C ∧
      b.chart 0 ∈ b'.chart.target ∧
      0 < (fderiv ℝ (fun x : ThreeSpace => b'.chart.symm (b.chart x)) 0).det ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        (1 - t) • (b'.chart.symm (b.chart 0)) + t • (0 : ThreeSpace)
          ∈ b'.chart.source ∩ b'.chart ⁻¹' Cᶜ) ∧
      orientedBallChartIsotopicAwayFromCompact o b b' C := by
  have h0src : (0 : ThreeSpace) ∈ b.chart.source :=
    b.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hbimg : b.chart '' Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.chart.target :=
    fun z ⟨x, hx, hzx⟩ =>
      hzx ▸ PartialEquiv.map_source b.chart.toPartialEquiv
        (b.closedBall_subset_source (Metric.closedBall_subset_closedBall (by norm_num) hx))
  have hev : (fun x : ThreeSpace => b.chart.symm (b.chart x)) =ᶠ[𝓝 (0 : ThreeSpace)] id := by
    filter_upwards [b.chart.open_source.mem_nhds h0src] with y hy
    exact PartialDiffeomorph.symm_apply_apply b.chart hy
  have hdet : 0 < (fderiv ℝ (fun x : ThreeSpace => b.chart.symm (b.chart x)) 0).det := by
    rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_id]
    change (0 : ℝ) < LinearMap.det (1 : ThreeSpace →ₗ[ℝ] ThreeSpace)
    rw [map_one]
    norm_num
  have hsymm : b.chart.symm (b.chart 0) = 0 := PartialDiffeomorph.symm_apply_apply b.chart h0src
  have hcenter : b.chart 0 ∈ b.chart.target :=
    PartialEquiv.map_source b.chart.toPartialEquiv h0src
  exact ⟨b, ∅, isCompact_empty, hbimg, by simp, by simp,
    hcenter, hdet,
    fun t _ => by
      rw [hsymm]
      simp only [smul_zero, zero_add]
      exact ⟨h0src, by simp⟩,
    orientedBallChartIsotopicAwayFromCompact_self b ∅⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
