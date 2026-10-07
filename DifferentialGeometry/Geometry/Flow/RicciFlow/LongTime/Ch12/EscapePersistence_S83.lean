import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EscapeCore_S83

set_option autoImplicit false

/-! # CH12-S83 G2: `escape_persistence_S83` (EP, data-level version of the `hEP` binder of `hone_S72`)

`hEP` of `hone_S72` (S72 NEWESC-fin) is FALSE as stated for arbitrary `mold` (ESC constrains `mold` only at the
slice times of `S`).  EP therefore takes, AT THE GIVEN DATA `old Hold sold mold Rold H S Φ`, two extra premises:
`THINd` (HPI04: every point `mold i' t q`, `q ∈ B(Rold i') \ B(Rold i' - L i')`, `t ≥ Tb`, is `wstar`-thin; producer
`hpi04_thin_barrier_O27` + annulus-in-cusp-band geometry) and `HDd` (slow-patch drift, backwards over one dyadic
time step, margin `L`, `J0` depends on `L`), and concludes the `hEP` conclusion for this data, verbatim. -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem escape_persistence_S83 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (wstar a : ℝ) (ha : 0 < a) :
    ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
      (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id),
      IsWThickSequence_S13 S wstar → (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) →
      (∃ L : Fin old → ℝ, (∀ i', 0 < L i') ∧ ∃ Tb : ℝ,
      ∀ (i' : Fin old) (t : ℝ) (ht0 : 0 < t) (hi : sold i' ≤ t), Tb ≤ t →
        ∀ q ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i') \
            riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i' - L i'),
          ∀ r : ℝ, 0 < r →
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) (mold i' t hi q) =
              ENNReal.ofReal r →
            ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) (mold i' t hi q) r <
              ENNReal.ofReal (wstar * r ^ 3)) →
      (∀ (L : Fin old → ℝ), (∀ i', 0 < L i') → ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
        ∀ θ : ℝ → ℝ, (∀ s, θ s ∈ Icc (0 : ℝ) 1) → (∀ s, s ≤ 7 / 4 → θ s = 0) →
        (∀ s, 15 / 8 ≤ s → θ s = 1) →
        ∀ (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
          H.Carrier → (postStage F.observation t).Carrier)
        (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ),
                  ((∀ j, 0 ≤ η j) ∧ Filter.Tendsto η Filter.atTop (nhds 0) ∧ Monotone ρ ∧
        Filter.Tendsto ρ Filter.atTop Filter.atTop ∧ (∀ j, 0 < ρ j) ∧
        Monotone ν ∧ Filter.Tendsto ν Filter.atTop Filter.atTop ∧
        (∀ j, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j)) ∧
        (∀ j μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E j (μ, p)) ∧
          Function.Bijective (fun p => E j (μ, p))) ∧
        (∀ j p, E j (0, p) = p) ∧
        (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
          let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
          H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          ckErr_S45 H H.metric 1 (fun x => E j (μ, x)) k p ≤ η j) ∧
        (∀ j (h1 : 2 ^ (j + 1) * T ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T))
            (h2 : 2 ^ (j + 1) * T ∈ Icc (2 ^ (j + 1) * T) (2 ^ (j + 1 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j),
            f j _ h1 (E j (1, p)) = f (j + 1) _ h2 p) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          Set.InjOn (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j) ∧
        (∀ j (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
        ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (φ : H.Carrier →
            (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
            (hrs : (r : ℝ) ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
              HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                (φ p)) (f j r hrs p)) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (μ : ℝ),
          ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r)) →
          (∀ (h0 : 2 ^ 0 * T ∈ Icc (2 ^ 0 * T) (2 ^ (0 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0), HEq (f 0 _ h0 p) (sliceApprox_O32 S H Φ i p)) →
          ∀ (i' : Fin old) (r t : ℝ) (hr : T ≤ r) (ht : T ≤ t) (hri : sold i' ≤ r) (hti : sold i' ≤ t), r ≤ t → t ≤ 2 * r →
              smoothedPhysicalMap_CX5 H T hT θ f E t ht H.basepoint ∈
                mold i' t hti '' riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i' - L i') →
              smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint ∈
                mold i' r hri '' riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i')) →
      ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
        ∀ θ : ℝ → ℝ, (∀ s, θ s ∈ Icc (0 : ℝ) 1) → (∀ s, s ≤ 7 / 4 → θ s = 0) →
        (∀ s, 15 / 8 ≤ s → θ s = 1) →
        ∀ (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
          H.Carrier → (postStage F.observation t).Carrier)
        (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ),
                  ((∀ j, 0 ≤ η j) ∧ Filter.Tendsto η Filter.atTop (nhds 0) ∧ Monotone ρ ∧
        Filter.Tendsto ρ Filter.atTop Filter.atTop ∧ (∀ j, 0 < ρ j) ∧
        Monotone ν ∧ Filter.Tendsto ν Filter.atTop Filter.atTop ∧
        (∀ j, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j)) ∧
        (∀ j μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E j (μ, p)) ∧
          Function.Bijective (fun p => E j (μ, p))) ∧
        (∀ j p, E j (0, p) = p) ∧
        (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
          let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
          H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          ckErr_S45 H H.metric 1 (fun x => E j (μ, x)) k p ≤ η j) ∧
        (∀ j (h1 : 2 ^ (j + 1) * T ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T))
            (h2 : 2 ^ (j + 1) * T ∈ Icc (2 ^ (j + 1) * T) (2 ^ (j + 1 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j),
            f j _ h1 (E j (1, p)) = f (j + 1) _ h2 p) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          Set.InjOn (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j) ∧
        (∀ j (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
        ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (φ : H.Carrier →
            (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
            (hrs : (r : ℝ) ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
              HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                (φ p)) (f j r hrs p)) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (μ : ℝ),
          ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r)) →
          (∀ (h0 : 2 ^ 0 * T ∈ Icc (2 ^ 0 * T) (2 ^ (0 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0), HEq (f 0 _ h0 p) (sliceApprox_O32 S H Φ i p)) →
          ∀ (i' : Fin old), ∃ T' : ℝ, ∀ t (hTt : T ≤ t) (hi' : sold i' ≤ t), T' ≤ t →
              smoothedPhysicalMap_CX5 H T hT θ f E t hTt H.basepoint ∉
                mold i' t hi' '' riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i')  := by
  classical
  intro old Hold sold mold Rold H S Φ hW hESC hthin hD
  obtain ⟨L, hLpos, Tb, hband⟩ := hthin
  choose Jf hJf using fun i' : Fin old => hESC i' (Rold i')
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((S.times_tendsto.eventually_ge_atTop Tb).and
      (Filter.eventually_all.2 fun i' : Fin old => S.times_tendsto.eventually_ge_atTop (sold i'))).and
      (Filter.eventually_all.2 fun i' : Fin old => eventually_ge_atTop (Jf i')))
  obtain ⟨J3, hJ3⟩ := hD L hLpos
  refine ⟨max N J3, ?_⟩
  intro i hi T hTdef hT θ hθr hθ0 hθ1 f E η ρ ν hconj hanchor i'
  have hdr := hJ3 i ((le_max_right _ _).trans hi) T hTdef hT θ hθr hθ0 hθ1 f E η ρ ν hconj hanchor
  obtain ⟨⟨hTb, hsold⟩, hJi⟩ := hN i ((le_max_left _ _).trans hi)
  obtain ⟨hη, hηt, hρm, hρ, hρpos, -, hν, hE, hEb, hE0, hsupp, hispeed, hEclose, hend, hacc, hlift0,
    hthick⟩ := hconj
  have hbp : H.basepoint ∈ riemannianBallOf H.metric H.basepoint a := by
    change riemannianEDistOf H.metric H.basepoint H.basepoint < ENNReal.ofReal a
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr ha
  subst hTdef
  refine ⟨(S.slices i).time, fun t hTt hi' _ => ?_⟩
  have hanc := anchor_escape_S83 S H Φ i hT θ hθ0 f E ρ hρpos hE0 hanchor
  have hcore := no_reentry_dyadic_S83 (X := fun t => (postStage F.observation t).Carrier)
    (S.slices i).time hT
    (fun t ht => smoothedPhysicalMap_CX5 H (S.slices i).time hT θ f E t ht H.basepoint)
    (fun t => {y | ∃ hi : sold i' ≤ t, y ∈ mold i' t hi '' riemannianBallOf (Hold i').metric
      (Hold i').basepoint (Rold i' - L i')})
    (fun t => {y | ∃ hi : sold i' ≤ t, y ∈ mold i' t hi '' riemannianBallOf (Hold i').metric
      (Hold i').basepoint (Rold i')})
    ?_ ?_ ?_ t hTt
  · exact fun hmem => hcore ⟨hi', hmem⟩
  · rintro t ht ⟨hti, q, hq, hqx⟩
    by_cases hq0 : q ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i' - L i')
    · exact ⟨hti, q, hq0, hqx⟩
    · exfalso
      have ht0 : 0 < t := lt_of_lt_of_le hT ht
      have hthn := hband i' t ht0 hti (hTb.trans ht) q ⟨hq, hq0⟩
      have hthk := hthick (dyadicIndex_CX5 (S.slices i).time t) t
        ⟨(dyadicIndex_mem_CX5 hT ht).1, (dyadicIndex_mem_CX5 hT ht).2.le⟩
        (θ (t / dyadicTime_CX5 (S.slices i).time (dyadicIndex_CX5 (S.slices i).time t)))
        H.basepoint hbp
      rw [hqx] at hthn
      exact thick_thin_false_S83
        (fun y => curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) y)
        (fun y r => ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) y r)
        wstar _ hthk hthn
  · rintro r t hr ht h1 h2 ⟨hti, q, hq, hqx⟩
    exact ⟨(hsold i').trans hr, hdr i' r t hr ht ((hsold i').trans hr) hti h1 h2 ⟨q, hq, hqx⟩⟩
  · rintro ⟨hj, q, hq, hqx⟩
    exact hJf i' i (hJi i') hj ⟨mold i' _ hj q, ⟨q, hq, rfl⟩, hqx ▸ hanc⟩

end GC.LongTime.Ch12
