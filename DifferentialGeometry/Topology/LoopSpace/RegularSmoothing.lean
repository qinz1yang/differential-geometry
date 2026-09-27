import DifferentialGeometry.Topology.LoopSpace.RegularHomotopy
import DifferentialGeometry.Topology.LoopSpace.RegularMetric
import DifferentialGeometry.Topology.LoopSpace.SmoothingSuperposition
import DifferentialGeometry.Topology.LoopSpace.ManifoldSmoothing
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction










noncomputable section

open Set Function ContinuousMap Manifold Metric
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M]

omit [FiniteDimensional ℝ E] [Nonempty M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem exists_uniform_regular_retracted_loop_homotopy (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (r : F → M) (U : Set F) (hU : IsOpen U) (heU : range e ⊆ U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U) (hleft : ∀ q, r (e q) = q)
    (Γ : K → regularLoop E M)
    (hΓ : Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
      ∃ H : unitInterval × K → regularLoop E M,
        Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] H ∧
        (∀ k, H (0, k) = Γ k) ∧
        (∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => (H (1, k)).val (t : loopCircle))) ∧
        (∀ k, regularLoopDist e (he.of_le (by exact_mod_cast le_top)) (H (1, k)) (Γ k) < ε) ∧
        (∀ k q, (Γ k).val = .const loopCircle q → ∀ τ, (H (τ, k)).val = .const loopCircle q) ∧
        (∀ k, (Γ k).val.Nullhomotopic → ∀ τ, (H (τ, k)).val.Nullhomotopic) ∧
        (∀ τ k θ, (H (τ, k)).val θ = r (e ((Γ k).val θ) + (τ : ℝ) •
          (averagedLoop φ (regularLoopValue e (he.of_le (by exact_mod_cast le_top)) (Γ k)) θ -
            e ((Γ k).val θ)))) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he₁
  let hr₁ := hr.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  obtain ⟨hcA, hdA⟩ := (continuous_regularLoop_iff e he₁ Γ).mp hΓ
  let A : C(K, freeLoop F) := ⟨fun k => regularLoopValue e he₁ (Γ k),
    (FreeLoop.continuous_family_iff _).mpr hcA⟩
  have hA₁ (k : K) : ContDiff ℝ 1 (fun t : ℝ => A k (t : loopCircle)) :=
    regularLoop_embedded_contDiff e he₁ (Γ k)
  have hAU (k : K) (θ : loopCircle) : A k θ ∈ U := heU (mem_range_self _)
  have hR : ContDiffOn ℝ 1 (e ∘ r) U := (he₁.comp_contMDiffOn hr₁).contDiffOn
  obtain ⟨a, ha, haR⟩ := smoothPeriodic_uniform_C1_superposition A hA₁ hdA hU hR hAU
    (show 0 < ε / 4 by positivity)
  obtain ⟨η, hη, hηU⟩ := (isCompact_range he.continuous).exists_cthickening_subset_open hU heU
  obtain ⟨b, hb, hbA⟩ := smoothPeriodic_uniform_approximation A.uncurry.continuous hη
  refine ⟨min a b, lt_min ha hb, fun φ hφ => ?_⟩
  let B : C(K, freeLoop F) := ⟨fun k => averagedLoop φ (A k),
    averagedLoop_continuous_family φ A.continuous⟩
  have hBsmooth (k : K) : ContDiff ℝ ∞ (fun t : ℝ => B k (t : loopCircle)) :=
    DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ ((A k).continuous.comp (AddCircle.continuous_mk' (1 : ℝ)))
  have hdB : Continuous (fun p : K × ℝ => deriv (fun t : ℝ => B p.1 (t : loopCircle)) p.2) := by
    have hAlift : Continuous (fun p : K × ℝ => A p.1 (p.2 : loopCircle)) :=
      A.uncurry.continuous.comp
        (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
    change Continuous (fun p : K × ℝ => deriv
      (DifferentialGeometry.Analysis.smoothPeriodic φ (fun t : ℝ => A p.1 (t : loopCircle))) p.2)
    simpa only [iteratedDeriv_one] using DifferentialGeometry.Analysis.continuous_iteratedDeriv_smoothPeriodic φ
      hAlift 1
  have hclose (k : K) (θ : loopCircle) : dist (B k θ) (e ((Γ k).val θ)) < η := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact hbA φ (hφ.trans_le (min_le_right _ _)) k t
  have hregion (τ : unitInterval) (k : K) (θ : loopCircle) :
      e ((Γ k).val θ) + (τ : ℝ) • (B k θ - e ((Γ k).val θ)) ∈ U := by
    apply hηU
    apply mem_cthickening_of_dist_le _ (e ((Γ k).val θ)) η (range e) (mem_range_self _)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg τ.property.1]
    exact ((mul_le_of_le_one_left (norm_nonneg _) τ.property.2).trans_lt
      (by simpa only [dist_eq_norm] using hclose k θ)).le
  obtain ⟨H, hH, hformula, hzero, hone⟩ := exists_regular_affine_homotopy e he₁ hU hr₁ hleft Γ hΓ
    B (fun k => (hBsmooth k).of_le (by exact_mod_cast le_top)) hdB hregion
  have hBU (k : K) (θ : loopCircle) : B k θ ∈ U := by
    have h := hregion 1 k θ
    change e ((Γ k).val θ) + (1 : ℝ) • (B k θ - e ((Γ k).val θ)) ∈ U at h
    simpa only [one_smul, ← add_sub_assoc, add_sub_cancel_left] using h
  have hfix (k : K) : (fun t : ℝ => (e ∘ r) (A k (t : loopCircle))) =
      fun t : ℝ => A k (t : loopCircle) := by
    funext t
    change e (r (e ((Γ k).val (t : loopCircle)))) = _
    rw [hleft]
    rfl
  refine ⟨H, hH, hzero, ?_, ?_, ?_, ?_, hformula⟩
  · intro k t
    have hs := ((hr _ (hBU k (t : loopCircle))).contMDiffAt
      (hU.mem_nhds (hBU k (t : loopCircle)))).comp t (hBsmooth k).contMDiff.contMDiffAt
    simpa only [hone, Function.comp_def] using hs
  · intro k
    have hv : dist (regularLoopValue e he₁ (H (1, k))) (regularLoopValue e he₁ (Γ k)) ≤ ε / 4 := by
      apply (ContinuousMap.dist_le (by positivity)).mpr
      intro θ
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      have h := (haR φ (hφ.trans_le (min_le_left _ _)) k t).2.1.le
      change dist (e ((H (1, k)).val (t : loopCircle))) (e ((Γ k).val (t : loopCircle))) ≤ _
      rw [hone]
      change dist (e (r (B k (t : loopCircle)))) (e (r (e ((Γ k).val (t : loopCircle))))) ≤ _ at h
      simpa only [hleft] using h
    have hd : dist (regularLoopDerivative e he₁ (H (1, k))) (regularLoopDerivative e he₁ (Γ k)) ≤ ε / 4 := by
      apply (ContinuousMap.dist_le (by positivity)).mpr
      intro θ
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      have h := (haR φ (hφ.trans_le (min_le_left _ _)) k t).2.2.le
      rw [hfix] at h
      change dist (deriv (fun s : ℝ => e (r (B k (s : loopCircle)))) t)
        (deriv (fun s : ℝ => e ((Γ k).val (s : loopCircle))) t) ≤ _ at h
      simpa only [regularLoopDerivative_coe, hone] using h
    dsimp only [regularLoopDist]
    linarith
  · intro k q hk τ
    have hAk : A k = .const loopCircle (e q) := by
      apply ContinuousMap.ext
      intro θ
      change e ((Γ k).val θ) = e q
      rw [hk]
      rfl
    have hBk : B k = .const loopCircle (e q) := by
      change averagedLoop φ (A k) = _
      rw [hAk, averagedLoop_const]
    apply ContinuousMap.ext
    intro θ
    rw [hformula, hk, hBk]
    simp only [ContinuousMap.const_apply, sub_self, smul_zero, add_zero, hleft]
  · intro k hk τ
    have hcont : Continuous (fun p : unitInterval × K => (H p).val) :=
      (continuous_regularLoop_inclusion e he₁ hemb).comp hH
    have hp : Joined (0 : unitInterval) τ :=
      ⟨⟨⟨fun s => s * τ, continuous_id.mul continuous_const⟩, zero_mul τ, one_mul τ⟩⟩
    have hj : Joined (H (0, k)).val (H (τ, k)).val :=
      hp.map (hcont.comp (continuous_id.prodMk continuous_const))
    rw [hzero] at hj
    exact FreeLoop.nullhomotopic_of_homotopic ((FreeLoop.homotopic_iff_joined _ _).mpr hj) hk




theorem exists_uniform_regular_loop_homotopy (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) (Γ : K → regularLoop E M)
    (hΓ : Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
      ∃ H : unitInterval × K → regularLoop E M,
        Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] H ∧
        (∀ k, H (0, k) = Γ k) ∧
        (∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => (H (1, k)).val (t : loopCircle))) ∧
        (∀ k, regularLoopDist e (he.of_le (by exact_mod_cast le_top)) (H (1, k)) (Γ k) < ε) ∧
        (∀ k q, (Γ k).val = .const loopCircle q → ∀ τ, (H (τ, k)).val = .const loopCircle q) ∧
        (∀ k, (Γ k).val.Nullhomotopic → ∀ τ, (H (τ, k)).val.Nullhomotopic) := by
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb hi
  obtain ⟨δ, hδ, h⟩ := exists_uniform_regular_retracted_loop_homotopy
    e he hemb r U hU heU hr hleft Γ hΓ hε
  refine ⟨δ, hδ, fun φ hφ => ?_⟩
  obtain ⟨H, hc, hz, hs, hd, hf, hn, _⟩ := h φ hφ
  exact ⟨H, hc, hz, hs, hd, hf, hn⟩

end DifferentialGeometry.Topology
