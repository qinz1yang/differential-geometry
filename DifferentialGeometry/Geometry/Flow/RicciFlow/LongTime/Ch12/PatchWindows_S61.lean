import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61

set_option autoImplicit false

/-! # CH12-S61 G1b: window core of `persistentModelPatch_of_windows_S61` (see PatchCore_S61). -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

theorem patch_core_S61 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (H : FiniteVolumeHyperbolicModel.{u}) {T start : ℝ} (hT : 0 < T) (hTs : T ≤ start)
    (α θ : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hθ : ContDiff ℝ ∞ θ)
    (hθrange : ∀ s, θ s ∈ Icc (0 : ℝ) 1) (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0)
    (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1) (hθderiv : ∀ s, |deriv θ s| ≤ B)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      H.Carrier → (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ)
    (hη : ∀ j, 0 ≤ η j)
    (hE : ∀ j, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j))
    (hbij : ∀ j μ, Function.Bijective (fun p => E j (μ, p)))
    (hE0 : ∀ j p, E j (0, p) = p)
    (hsupp : ∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p)
    (hispeed : ∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
      let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ (timeVector_CX5 μ);
      H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2)
    (hend : ∀ j (h1 : dyadicTime_CX5 T (j + 1) ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)))
      (h2 : dyadicTime_CX5 T (j + 1) ∈ Icc (dyadicTime_CX5 T (j + 1)) (dyadicTime_CX5 T (j + 1 + 1))),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j), f j _ h1 (E j (1, p)) = f (j + 1) _ h2 p)
    (hacc : ∀ j t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j)
    (hbudget : ∀ t, start ≤ t → 4 * B * η (dyadicIndex_CX5 T t) < α t)
    (Ω : TopologicalSpace.Opens (ℝ × H.Carrier)) (t₀ : ℝ) (p₀ : H.Carrier) (j m : ℕ)
    (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1)) (ordered : first ≤ last)
    (a b : ℝ) (ha : T < a) (hbefore : a < t₀) (hafter : t₀ < b)
    (horizon : b ≤ (F.tower.history n).horizon) (U : TopologicalSpace.Opens H.Carrier)
    (hp₀ : p₀ ∈ U) (hbox : ∀ t ∈ Ioo a b, (U : Set H.Carrier) ⊆ sourceSlice_CX5 Ω t)
    (hUm : (U : Set H.Carrier) ⊆ riemannianBallOf H.metric H.basepoint m)
    (hmρ : ∀ k, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) → (m : ℝ) ≤ ρ k)
    (hη1 : ∀ k, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) → η k ≤ 1)
    (stages : ∀ t : Icc (0 : ℝ) (F.tower.history n).horizon, (t : ℝ) ∈ Ioo a b →
      first ≤ (F.tower.history n).toHistory.activeStage t ∧
        (F.tower.history n).toHistory.activeStage t ≤ last)
    (hwin : (t₀ < dyadicTime_CX5 T (j + 1) ∧
        (∀ k : ℕ, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) → k = j) ∧
        (∀ k : ℕ, a < dyadicTime_CX5 T (k + 1) → dyadicTime_CX5 T (k + 1) < b → False)) ∨
       (t₀ = dyadicTime_CX5 T (j + 1) ∧
        (∀ k : ℕ, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) → k = j ∨ k = j + 1) ∧
        (∀ k : ℕ, a < dyadicTime_CX5 T (k + 1) → dyadicTime_CX5 T (k + 1) < b → k = j)))
    (φ₁ φ₂ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered)
    (h₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ₁ (riemannianBallOf H.metric H.basepoint (4 * ρ j)))
    (hraw₁ : ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
      (hrs : (r : ℝ) ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ₁ p))
          (f j r hrs p))
    (h₂ : dyadicTime_CX5 T (j + 1) < b → a < dyadicTime_CX5 T (j + 1 + 1) →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ₂ (riemannianBallOf H.metric H.basepoint (4 * ρ (j + 1))) ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
        (hrs : (r : ℝ) ∈ Icc (dyadicTime_CX5 T (j + 1)) (dyadicTime_CX5 T (j + 1 + 1))),
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ (j + 1)),
          HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
            ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ₂ p))
            (f (j + 1) r hrs p)) :
    Nonempty (PersistentModelPatch F H start α (sourceSlice_CX5 Ω)
      (fun t ht => smoothedPhysicalMap_CX5 H T hT θ f E t (hTs.trans ht)) t₀ p₀) := by
  classical
  have hk : ∀ k, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) → k = j ∨ k = j + 1 := by
    intro k h1 h2
    rcases hwin with ⟨_, h, _⟩ | ⟨_, h, _⟩
    · exact Or.inl (h k h1 h2)
    · exact h k h1 h2
  have hlast : ∀ k, a < dyadicTime_CX5 T (k + 1) → dyadicTime_CX5 T (k + 1) < b → k = j := by
    intro k h1 h2
    rcases hwin with ⟨_, _, h⟩ | ⟨_, _, h⟩
    · exact (h k h1 h2).elim
    · exact h k h1 h2
  let A : ℕ → TopologicalSpace.Opens H.Carrier := fun k =>
    ⟨riemannianBallOf H.metric H.basepoint (4 * ρ k), isOpen_riemannianBallOf_S61 H _⟩
  let φ : ℕ → H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered :=
    fun k => if k = j + 1 then φ₂ else φ₁
  have hφj : φ j = φ₁ := by simp [φ]
  have hφj1 : φ (j + 1) = φ₂ := by simp [φ]
  have hρpos : ∀ k, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) → 0 ≤ ρ k :=
    fun k h1 h2 => (Nat.cast_nonneg m).trans (hmρ k h1 h2)
  have hU4 : ∀ k, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) →
      (U : Set H.Carrier) ⊆ riemannianBallOf H.metric H.basepoint (4 * ρ k) := fun k h1 h2 =>
    hUm.trans (riemannianBallOf_mono _ _ ((hmρ k h1 h2).trans (by linarith [hρpos k h1 h2])))
  have hU2 : ∀ k, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) →
      (U : Set H.Carrier) ⊆ riemannianBallOf H.metric H.basepoint (2 * ρ k) := fun k h1 h2 =>
    hUm.trans (riemannianBallOf_mono _ _ ((hmρ k h1 h2).trans (by linarith [hρpos k h1 h2])))
  have himage : ∀ k, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) →
      ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, E k (μ, p) ∈ A k := by
    intro k h1 h2 μ _ p hp
    exact isotopy_mem_ball_S49 H (E k) (fun μ => (hbij k μ).1) (hsupp k) μ
      (r := 4 * ρ k) (by linarith [hρpos k h1 h2]) (hU4 k h1 h2 hp)
  have hφ : ∀ k, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (φ k) (A k) := by
    intro k h1 h2
    rcases hk k h1 h2 with h | h
    · rw [h, hφj]; exact h₁
    · rw [h, hφj1]; exact (h₂ (h ▸ h1) (h ▸ h2)).1
  have hjoin : ∀ k, a < dyadicTime_CX5 T (k + 1) → dyadicTime_CX5 T (k + 1) < b →
      ∀ p ∈ U, φ k (E k (1, p)) = φ (k + 1) p := by
    intro k h1 h2 p hp
    have hkj := hlast k h1 h2
    rw [hkj] at h1 h2
    rw [hkj, hφj, hφj1]
    have hj1 : dyadicTime_CX5 T j < b := (dyadicTime_strictMono_CX5 hT (Nat.lt_succ_self j)).trans h2
    have hj2 : a < dyadicTime_CX5 T (j + 1 + 1) :=
      h1.trans (dyadicTime_strictMono_CX5 hT (Nat.lt_succ_self (j + 1)))
    obtain ⟨_, h₂r⟩ := h₂ h2 hj2
    let r : Icc (0 : ℝ) (F.tower.history n).horizon :=
      ⟨dyadicTime_CX5 T (j + 1), (dyadicTime_pos_CX5 hT _).le, h2.le.trans horizon⟩
    have hr : (r : ℝ) ∈ Ioo a b := ⟨h1, h2⟩
    have hrs1 : (r : ℝ) ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) :=
      ⟨(dyadicTime_strictMono_CX5 hT (Nat.lt_succ_self j)).le, le_rfl⟩
    have hrs2 : (r : ℝ) ∈ Icc (dyadicTime_CX5 T (j + 1)) (dyadicTime_CX5 T (j + 1 + 1)) :=
      ⟨le_rfl, (dyadicTime_strictMono_CX5 hT (Nat.lt_succ_self (j + 1))).le⟩
    have hx := hraw₁ r hr hrs1 (E j (1, p))
      (himage j hj1 h1 1 ⟨zero_le_one, le_rfl⟩ p hp)
    have hy := h₂r r hr hrs2 p (hU4 (j + 1) h2 hj2 hp)
    have hu := hend j ⟨hrs1.1, hrs1.2⟩ ⟨hrs2.1, hrs2.2⟩ p (hU2 j hj1 h1 hp)
    exact survivor_join_S49 (F.tower.history n).toHistory ordered _ (stages r hr).1
      (stages r hr).2 _ _ _ _ hx hy hu
  have hraw0 : ∀ (t : Icc (0 : ℝ) (F.tower.history n).horizon) (ht : (t : ℝ) ∈ Ioo a b) (k : ℕ)
      (hk' : (t : ℝ) ∈ Ico (dyadicTime_CX5 T k) (dyadicTime_CX5 T (k + 1))), ∀ p ∈ A k,
      HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage t) (stages t ht).1 (stages t ht).2 (φ k p))
        (f k t ⟨hk'.1, hk'.2.le⟩ p) := by
    intro t ht k hk' p hp
    have h1 : dyadicTime_CX5 T k < b := hk'.1.trans_lt ht.2
    have h2 : a < dyadicTime_CX5 T (k + 1) := ht.1.trans_le hk'.2.le
    rcases hk k h1 h2 with h | h
    · subst h
      rw [hφj]
      exact hraw₁ t ht ⟨hk'.1, hk'.2.le⟩ p hp
    · subst h
      rw [hφj1]
      exact (h₂ h1 h2).2 t ht ⟨hk'.1, hk'.2.le⟩ p hp
  have hmetric : ∀ (t : Icc (0 : ℝ) (F.tower.history n).horizon) (ht : (t : ℝ) ∈ Ioo a b),
      ∀ k, (t : ℝ) ∈ Ico (dyadicTime_CX5 T k) (dyadicTime_CX5 T (k + 1)) →
      ∀ p ∈ A k, ∀ w : TangentSpace (𝓡 3) p,
        let history := (F.tower.history n).toHistory;
        let ψ := history.backwardSurvivorMap first last ordered (history.activeStage t)
          (stages t ht).1 (stages t ht).2 ∘ φ k;
        (history.stageMetric (history.activeStage t) t).inner (ψ p)
          (mfderiv (𝓡 3) (𝓡 3) ψ p w) (mfderiv (𝓡 3) (𝓡 3) ψ p w) ≤
            4 * (t : ℝ) * H.metric.inner p w w := by
    intro t ht k hk' p hp w
    have h1 : dyadicTime_CX5 T k < b := hk'.1.trans_lt ht.2
    have h2 : a < dyadicTime_CX5 T (k + 1) := ht.1.trans_le hk'.2.le
    exact hmetric_pt_S61 F H n first last ordered t ((hT.trans ha).trans ht.1) (stages t ht)
      (A k) (A k).isOpen (φ k) (f k t ⟨hk'.1, hk'.2.le⟩) (fun q hq => hraw0 t ht k hk' q hq)
      (fun q hq => ((hacc k t ⟨hk'.1, hk'.2.le⟩).2 0 (Nat.zero_le _) q hq).trans_le (hη1 k h1 h2))
      p hp w
  exact persistentModelPatch_of_dyadic_lifts_CX5 H hT hTs α θ B hB hθ hθrange hθ0 hθ1 hθderiv f E η
    hη Ω t₀ p₀ n first last ordered a b ha hbefore hafter horizon U hp₀ hbox stages A φ hφ hE
    himage (fun k _ _ p _ => hE0 k p) hjoin (fun k _ _ μ hμ p _ => hispeed k μ hμ p)
    (fun k t ht _ hs => by
      have := hbudget t hs
      rwa [dyadicIndex_eq_CX5 hT ht] at this)
    (fun t ht _ k hk' p hp => hraw0 t ht k hk' p hp) hmetric

end GC.LongTime.Ch12
