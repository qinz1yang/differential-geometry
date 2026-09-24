import DifferentialGeometry.Geometry.Measure.Area.Convergence
import DifferentialGeometry.Analysis.Calculus.DiskTraceApproximation
import DifferentialGeometry.Topology.Manifold.Embedding.CompactRetraction
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors

section

noncomputable section

open Set Filter MeasureTheory Manifold Bundle Metric
open scoped ContDiff Topology NNReal ENNReal Manifold Bundle

private theorem exists_compact_target_for_uniform_tail
    {X F : Type*} [PseudoMetricSpace F] [LocallyCompactSpace F]
    {S : Set F} (hS : IsCompact S) {U : Set F} (hU : IsOpen U) (hSU : S ⊆ U)
    {D : Set X} {v : X → F} {u : ℕ → X → F} (hv : MapsTo v D S)
    (hu : TendstoUniformlyOn u v atTop D) :
    ∃ (K : Set F) (N : ℕ), IsCompact K ∧ K ⊆ U ∧ S ⊆ K ∧
      ∀ j ≥ N, MapsTo (u j) D K := by
  obtain ⟨η, hη, hηU⟩ := hS.exists_cthickening_subset_open hU hSU
  obtain ⟨ρ, hρ, hρK⟩ := hS.exists_isCompact_cthickening
  let K := cthickening (min η ρ) S
  have hK : IsCompact K := hρK.of_isClosed_subset isClosed_cthickening
    (cthickening_mono (min_le_right η ρ) S)
  have hnear : ∀ᶠ j in atTop, ∀ x ∈ D, dist (v x) (u j x) < min η ρ :=
    Metric.tendstoUniformlyOn_iff.mp hu _ (lt_min hη hρ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnear
  refine ⟨K, N, hK, (cthickening_mono (min_le_left η ρ) S).trans hηU,
    self_subset_cthickening S, ?_⟩
  intro j hj x hx
  exact mem_cthickening_of_dist_le (u j x) (v x) (min η ρ) S (hv hx)
    (by simpa only [dist_comm] using (hN j hj x hx).le)


namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

private theorem exists_embedded_disk_approximation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {v : C(closedDisk, M)} (hv : v ∈ spanningDiskCompetitors g γ) :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n))
      (r : EuclideanSpace ℝ (Fin n) → M) (U K : Set (EuclideanSpace ℝ (Fin n)))
      (w : ℕ → ℂ → EuclideanSpace ℝ (Fin n)) (B : ℝ) (L : ℝ≥0),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      IsOpen U ∧ IsCompact K ∧ K ⊆ U ∧ e '' Set.range v ⊆ K ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ r U ∧
      (∀ p ∈ Set.range v, r (e p) = p) ∧ LipschitzWith L (e ∘ diskExtension v) ∧ 0 ≤ B ∧
      (∀ j, ContDiff ℝ ∞ (w j)) ∧
      (∀ j, MapsTo (w j) (Metric.closedBall (0 : ℂ) 1) K) ∧
      (∀ j θ, w j (diskBoundary θ : ℂ) = e (γ θ)) ∧
      (∀ j z, ‖z‖ ≤ 1 → ‖fderiv ℝ (w j) z‖ ≤ B) ∧
      TendstoUniformlyOn w (e ∘ diskExtension v) atTop (Metric.closedBall (0 : ℂ) 1) ∧
      ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1),
        Tendsto (fun j => fderiv ℝ (w j) z) atTop (𝓝 (fderiv ℝ (e ∘ diskExtension v) z)) := by
  let _ : Nonempty M := ⟨v ⟨0, by simp⟩⟩
  obtain ⟨N, n, e, r, U, hNv, he, hesupp, _, _, hU, heNU, hr, hleftN⟩ :=
    exists_contMDiff_embedding_retraction_near_isCompact (I := 𝓘(ℝ, E))
      (isCompact_range v.continuous) (Set.range_nonempty v)
  have hleft (p : M) (hp : p ∈ Set.range v) : r (e p) = p := hleftN p (hNv hp)
  have heU : e '' Set.range v ⊆ U := image_mono hNv |>.trans heNU
  obtain ⟨C, _, hC⟩ := exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport g
    (he.of_le (by simp)) hesupp
  obtain ⟨htrace, Lv, hLv⟩ := hv
  have hLip : LipschitzWith (C * Lv) (e ∘ diskExtension v) := by
    apply diskExtension_lipschitz (u := fun z : closedDisk => e (v z))
    intro z w
    calc
      edist (e (v z)) (e (v w)) ≤ (C : ℝ≥0∞) * riemannianEDistOf g (v z) (v w) := hC _ _
      _ ≤ (C : ℝ≥0∞) * ((Lv : ℝ≥0∞) * edist z w) :=
        mul_le_mul_of_nonneg_left (hLv z w) (by positivity)
      _ = _ := by rw [ENNReal.coe_mul, mul_assoc]
  let γe : freeLoop (EuclideanSpace ℝ (Fin n)) := ⟨e ∘ γ, he.continuous.comp γ.continuous⟩
  have hγe : ContDiff ℝ ∞ (fun t : ℝ => γe (t : loopCircle)) := (he.comp hγ).contDiff
  have htre : ∀ θ, (e ∘ diskExtension v) (diskBoundary θ : ℂ) = γe θ := by
    intro θ
    change e (diskExtension v (diskBoundary θ : ℂ)) = e (γ θ)
    rw [diskExtension_coe]
    exact congrArg e (congrArg (fun f : freeLoop M => f θ) htrace)
  obtain ⟨w, B, hB, hws, hwtr, hwD, hwu, hwd⟩ :=
    exists_contDiff_diskTrace_tendstoUniformlyOn_fderiv hLip γe hγe htre
  obtain ⟨K, N, hK, hKU, heK, hwK⟩ := exists_compact_target_for_uniform_tail
    ((isCompact_range v.continuous).image he.continuous) hU heU
      (fun z _ => ⟨diskExtension v z, mem_range_self (diskRetraction z), rfl⟩) hwu
  refine ⟨n, e, r, U, K, fun j => w (j + N), B, C * Lv, he, hU, hK, hKU, heK,
    hr, hleft, hLip, hB, fun j => hws (j + N), fun j => hwK _ (Nat.le_add_left _ _),
    fun j θ => hwtr (j + N) θ, fun j z hz => hwD (j + N) z hz,
    (by
      intro W hW
      exact (tendsto_add_atTop_nat N).eventually (hwu W hW)), ?_⟩
  filter_upwards [hwd] with z hz
  exact hz.comp (tendsto_add_atTop_nat N)

theorem exists_smooth_disk_approximation_preserving_trace_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {v : C(closedDisk, M)} (hv : v ∈ spanningDiskCompetitors g γ) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) := by
  obtain ⟨n, e, r, U, K, w, B, L, _, hU, hK, hKU, heK, hr, hleft, hLip,
      _, hws, hwK, hwtr, hwD, hwu, hwd⟩ := exists_embedded_disk_approximation g hγ hv
  have hwU (j : ℕ) : MapsTo (w j) (Metric.closedBall (0 : ℂ) 1) U :=
    fun _ hz => hKU (hwK j hz)
  have hcont (j : ℕ) : Continuous (fun z : closedDisk => r (w j z)) :=
    hr.continuousOn.comp_continuous
      ((hws j).continuous.comp continuous_subtype_val) (fun z => hwU j z.property)
  let vj : ℕ → C(closedDisk, M) := fun j => ⟨fun z => r (w j z), hcont j⟩
  have hsm (j : ℕ) : SmoothDiskExtension (E := E) (vj j) (r ∘ w j) := by
    refine ⟨fun _ => rfl, w j ⁻¹' U, hU.preimage (hws j).continuous, hwU j, ?_⟩
    exact hr.comp (hws j).contMDiff.contMDiffOn (fun _ hz => hz)
  have htrace (j : ℕ) : diskTrace (vj j) = γ := by
    ext θ
    change r (w j (diskBoundary θ : ℂ)) = γ θ
    rw [hwtr]
    apply hleft
    have htrace := congrArg (fun η : freeLoop M => η θ) hv.1
    exact htrace ▸ mem_range_self (diskBoundary θ)
  refine ⟨vj, fun j => r ∘ w j, fun j => ⟨hsm j, htrace j⟩, ?_⟩
  have hbase : r ∘ (e ∘ diskExtension v) = diskExtension v := by
    funext z
    exact hleft _ (mem_range_self (diskRetraction z))
  have hareat := tendsto_riemannianArea_comp_of_fderiv_tendsto g hU
    (hr.of_le (by simp)) hK hKU measurableSet_closedBall
    (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
    (fun j _ _ => ((hws j).of_le (by simp)).contDiffAt)
    (ae_restrict_of_ae hLip.ae_differentiableAt) hwK
    (fun j z hz => hwD j z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz))
    (ae_restrict_of_forall_mem measurableSet_closedBall (fun _ hz => hwu.tendsto_at hz)) hwd
  have harea (j : ℕ) : riemannianDiskArea g (vj j) =
      riemannianArea g (r ∘ w j) (Metric.closedBall (0 : ℂ) 1) :=
    riemannianDiskArea_eq_of_extension g (vj j) (r ∘ w j) (hsm j).1
  change Tendsto _ atTop (𝓝 (riemannianArea g (diskExtension v) (Metric.closedBall (0 : ℂ) 1)))
  simpa only [harea, hbase] using hareat

end DifferentialGeometry.Geometry

end

end
