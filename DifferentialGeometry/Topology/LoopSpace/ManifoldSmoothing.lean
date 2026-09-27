import DifferentialGeometry.Topology.LoopSpace.PeriodicDescent
import DifferentialGeometry.Geometry.Metric.ManifoldApproximation
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families











noncomputable section

open Set Function ContinuousMap Manifold Bundle DifferentialGeometry
open scoped Topology ContDiff Manifold Bundle ENNReal NNReal

namespace DifferentialGeometry.Topology

variable {K Q : Type*} [TopologicalSpace K] [TopologicalSpace Q]


theorem familyHomotopy_nullhomotopic {Γ S : C(K, freeLoop Q)} (H : Γ.Homotopy S)
    {k : K} (hk : (Γ k).Nullhomotopic) (t : unitInterval) :
    (H (t, k)).Nullhomotopic := by
  have hp : Joined (0 : unitInterval) t :=
    ⟨⟨⟨fun s => s * t, continuous_id.mul continuous_const⟩, zero_mul t, one_mul t⟩⟩
  have hj : Joined (H (0, k)) (H (t, k)) := hp.map
    (H.continuous.comp (continuous_id.prodMk continuous_const))
  simp only [Homotopy.apply_zero] at hj
  exact FreeLoop.nullhomotopic_of_homotopic
    ((FreeLoop.homotopic_iff_joined _ _).mpr hj) hk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M] [Nonempty M] [CompactSpace K]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Nonempty M] [FiniteDimensional ℝ E] in
theorem exists_uniform_retracted_loop_homotopy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n)) (r : EuclideanSpace ℝ (Fin n) → M)
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hU : IsOpen U) (heU : range e ⊆ U)
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ r U)
    (hleft : ∀ q, r (e q) = q) (Γ : C(K, freeLoop M))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
      ∃ (S : C(K, freeLoop M)) (H : Γ.Homotopy S),
        (∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
          (fun t : ℝ => S k (t : loopCircle))) ∧
        (∀ (d : ℕ) (a : M → EuclideanSpace ℝ (Fin d)),
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ a →
          ∀ j, Continuous (fun p : K × ℝ =>
            iteratedDeriv j (fun t : ℝ => a (S p.1 (t : loopCircle))) p.2)) ∧
        (∀ t k θ, riemannianEDistOf g (H (t, k) θ) (Γ k θ) < ENNReal.ofReal ε) ∧
        (∀ k q, Γ k = .const loopCircle q →
          ∀ t, H (t, k) = .const loopCircle q) ∧
        (∀ k, (Γ k).Nullhomotopic → ∀ t, (H (t, k)).Nullhomotopic) ∧
        (∀ k θ, S k θ = r (averagedLoop φ ((⟨e, he.continuous⟩ : C(M, EuclideanSpace ℝ (Fin n))).comp (Γ k)) θ)) ∧
        (∀ t k θ, H (t, k) θ = r (e (Γ k θ) + (t : ℝ) •
          (averagedLoop φ ((⟨e, he.continuous⟩ : C(M, EuclideanSpace ℝ (Fin n))).comp (Γ k)) θ - e (Γ k θ)))) := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  obtain ⟨a, ha, har⟩ := DifferentialGeometry.Analysis.exists_uniform_retraction_radius
    he.continuous hU heU hr.continuousOn hleft (ENNReal.ofReal_pos.mpr hε)
  let A : C(K, freeLoop (EuclideanSpace ℝ (Fin n))) :=
    (FreeLoop.postcompose ⟨e, he.continuous⟩).comp Γ
  obtain ⟨δ, hδ, hδA⟩ := smoothPeriodic_uniform_approximation A.uncurry.continuous ha
  refine ⟨δ, hδ, fun φ hφ => ?_⟩
  let B : C(K, freeLoop (EuclideanSpace ℝ (Fin n))) :=
    ⟨fun k => averagedLoop φ (A k), averagedLoop_continuous_family φ A.continuous⟩
  have hclose (k : K) (θ : loopCircle) : dist (B k θ) (e (Γ k θ)) < a := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact hδA φ hφ k t
  let v : (unitInterval × K) × loopCircle → EuclideanSpace ℝ (Fin n) :=
    fun p => e (Γ p.1.2 p.2) + (p.1.1 : ℝ) • (B p.1.2 p.2 - e (Γ p.1.2 p.2))
  have hcA : Continuous (fun p : (unitInterval × K) × loopCircle => e (Γ p.1.2 p.2)) :=
    A.uncurry.continuous.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hcB : Continuous (fun p : (unitInterval × K) × loopCircle => B p.1.2 p.2) :=
    B.uncurry.continuous.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hcv : Continuous v := hcA.add
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul (hcB.sub hcA))
  have hvclose (p : (unitInterval × K) × loopCircle) :
      dist (v p) (e (Γ p.1.2 p.2)) < a := by
    dsimp only [v]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg p.1.1.property.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) p.1.1.property.2).trans_lt
      (hclose p.1.2 p.2)
  have hvU (p : (unitInterval × K) × loopCircle) : v p ∈ U :=
    (har (Γ p.1.2 p.2) (v p) (hvclose p)).1
  have hcH : Continuous (r ∘ v) :=
    hr.continuousOn.comp_continuous hcv hvU
  let J : C(unitInterval × K, freeLoop M) := (⟨r ∘ v, hcH⟩ :
    C((unitInterval × K) × loopCircle, M)).curry
  let S : C(K, freeLoop M) := J.comp ⟨fun k => (1, k), continuous_const.prodMk continuous_id⟩
  have hJ0 (k : K) : J (0, k) = Γ k := by
    ext θ
    change r (e (Γ k θ) + (0 : ℝ) • _) = Γ k θ
    rw [zero_smul, add_zero, hleft]
  let H : Γ.Homotopy S := ⟨J, hJ0, fun _ => rfl⟩
  have hS (k : K) (θ : loopCircle) : S k θ = r (B k θ) := by
    change r (e (Γ k θ) + (1 : ℝ) • (B k θ - e (Γ k θ))) = _
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]
  refine ⟨S, H, ?_, ?_, ?_, ?_, (fun k hk t => familyHomotopy_nullhomotopic H hk t), hS, fun _ _ _ => rfl⟩
  · intro k t
    have htU : B k (t : loopCircle) ∈ U := (har (Γ k (t : loopCircle)) _ (hclose k _)).1
    have hB : ContDiff ℝ ∞ (fun t : ℝ => B k (t : loopCircle)) :=
      DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ
        ((A k).continuous.comp (AddCircle.continuous_mk' (1 : ℝ)))
    have hs := ((hr _ htU).contMDiffAt (hU.mem_nhds htU)).comp t hB.contMDiff.contMDiffAt
    simpa only [hS, Function.comp_def] using hs
  · intro d a ha j
    simp_rw [hS]
    have hAB : Continuous (fun p : K × ℝ => A p.1 (p.2 : loopCircle)) :=
      A.uncurry.continuous.comp
        (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
    exact DifferentialGeometry.Analysis.continuous_iteratedDeriv_family_comp hU
      (ha.comp_contMDiffOn hr).contDiffOn
      (fun k => DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ
        ((A k).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))))
      (fun j => DifferentialGeometry.Analysis.continuous_iteratedDeriv_smoothPeriodic φ hAB j)
      (fun p => (har (Γ p.1 (p.2 : loopCircle)) _ (hclose p.1 _)).1) j
  · intro t k θ
    exact (har (Γ k θ) (v ((t, k), θ)) (hvclose ((t, k), θ))).2
  · intro k q hk t
    have hAk : A k = .const loopCircle (e q) := by
      apply ContinuousMap.ext
      intro θ
      change e (Γ k θ) = e q
      rw [hk]
      rfl
    have hBk : B k = .const loopCircle (e q) := by
      change averagedLoop φ (A k) = _
      rw [hAk, averagedLoop_const]
    ext θ
    change r (e (Γ k θ) + (t : ℝ) • (B k θ - e (Γ k θ))) = q
    rw [hk, hBk]
    simp only [ContinuousMap.const_apply, sub_self, smul_zero, add_zero, hleft]





theorem exists_uniform_smooth_loop_homotopy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (Γ : C(K, freeLoop M))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
      ∃ (S : C(K, freeLoop M)) (H : Γ.Homotopy S),
        (∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
          (fun t : ℝ => S k (t : loopCircle))) ∧
        (∀ (d : ℕ) (a : M → EuclideanSpace ℝ (Fin d)),
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ a →
          ∀ j, Continuous (fun p : K × ℝ =>
            iteratedDeriv j (fun t : ℝ => a (S p.1 (t : loopCircle))) p.2)) ∧
        (∀ t k θ, riemannianEDistOf g (H (t, k) θ) (Γ k θ) < ENNReal.ofReal ε) ∧
        (∀ k q, Γ k = .const loopCircle q →
          ∀ t, H (t, k) = .const loopCircle q) ∧
        (∀ k, (Γ k).Nullhomotopic → ∀ t, (H (t, k)).Nullhomotopic) := by
  obtain ⟨n, e, r, U, he, _, _, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_compact_embedding_and_retraction (E := E) (M := M)
  obtain ⟨δ, hδ, hδS⟩ := exists_uniform_retracted_loop_homotopy g e r U he hU heU hr hleft Γ hε
  refine ⟨δ, hδ, fun φ hφ => ?_⟩
  obtain ⟨S, H, hs, hj, hclose, hconst, hnull, _, _⟩ := hδS φ hφ
  exact ⟨S, H, hs, hj, hclose, hconst, hnull⟩

end DifferentialGeometry.Topology
