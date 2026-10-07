import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.NewSide_S115

set_option autoImplicit false

/-! # CH12-S123 G1b: the new half of `hSW` for `r ≤ t` in the CLOSED window `j` (`t = 2^{j+1}T` allowed)

`smoothedPhysicalMap_closed_S123`: `x s = f j s (E j (θ (s / (2^j T)), base))` for every `s` in the closed window
`j` (at `s = 2^{j+1}T` the dyadic index is `j+1`, and the formula is read through the seam `hend` at
`base ∈ B(2 ρ_j)`: `θ (2) = 1`, `θ (1) = 0`, `E_{j+1}(0, ·) = id`).
`newside_closed_S123` = `newside_same_window_S115` with the two dyadic-index hypotheses `hrj htj` replaced by the
two formulas `hxr hxt` (so `r`, `t` may be anywhere in the closed window). -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open Manifold GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.Ch12
universe u

theorem smoothedPhysicalMap_closed_S123 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (hT : 0 < T)
    (θ : ℝ → ℝ) (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0) (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) → H.Carrier →
      (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (ρ : ℕ → ℝ) (j : ℕ) (hρ : 0 < ρ j)
    (hE0 : ∀ p, E (j + 1) (0, p) = p)
    (hend : ∀ (h1 : 2 ^ (j + 1) * T ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T))
        (h2 : 2 ^ (j + 1) * T ∈ Icc (2 ^ (j + 1) * T) (2 ^ (j + 1 + 1) * T)),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j),
        f j _ h1 (E j (1, p)) = f (j + 1) _ h2 p)
    (t : ℝ) (htT : T ≤ t) (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) :
    smoothedPhysicalMap_CX5 H T hT θ f E t htT H.basepoint =
      f j t ht (E j (θ (t / (2 ^ j * T)), H.basepoint)) := by
  rcases ht.2.lt_or_eq with hlt | heq
  · exact smoothedPhysicalMap_eq_S115 H hT θ f E t htT j
      (dyadicIndex_eq_CX5 hT (j := j) ⟨ht.1, hlt⟩) ht H.basepoint
  · subst heq
    have hj1 : dyadicIndex_CX5 T (2 ^ (j + 1) * T) = j + 1 :=
      dyadicIndex_eq_CX5 hT (j := j + 1) ⟨le_rfl, by
        simp only [dyadicTime_CX5]
        have := pow_pos (two_pos : (0 : ℝ) < 2) (j + 1)
        rw [pow_succ _ (j + 1)]; nlinarith⟩
    have h2 : (2 : ℝ) ^ (j + 1) * T / (2 ^ j * T) = 2 := by
      have : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [this]; field_simp
    have h1 : (2 : ℝ) ^ (j + 1) * T / (2 ^ (j + 1) * T) = 1 := by
      have := pow_pos (two_pos : (0 : ℝ) < 2) (j + 1)
      field_simp
    have hbase : H.basepoint ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j) :=
      mem_riemannianBallOf_self_S33 H.metric H.basepoint (by linarith)
    have hmem2 : 2 ^ (j + 1) * T ∈ Icc (2 ^ (j + 1) * T) (2 ^ (j + 1 + 1) * T) :=
      ⟨le_rfl, by
        have := pow_pos (two_pos : (0 : ℝ) < 2) (j + 1)
        rw [pow_succ _ (j + 1)]; nlinarith⟩
    rw [smoothedPhysicalMap_eq_S115 H hT θ f E _ htT (j + 1) hj1 hmem2, h1, hθ0 1 (by norm_num),
      hE0, h2, hθ1 2 (by norm_num)]
    exact (hend ht hmem2 _ hbase).symm

theorem newside_closed_S123 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (hT : 0 < T)
    (θ : ℝ → ℝ) (hθ : ∀ s, θ s ∈ Icc (0 : ℝ) 1)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) → H.Carrier →
      (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (j : ℕ) (hρ : 0 < ρ j)
    (hE : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j))
    (hbij : ∀ μ, Function.Bijective (fun p => E j (μ, p)))
    (hsupp : ∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p)
    (hispeed : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
      let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
      H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2)
    (hlift : ∀ (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
      ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
        (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
        (_ : b ≤ (F.tower.history n).horizon)
        (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
          first ≤ (F.tower.history n).toHistory.activeStage r ∧
            (F.tower.history n).toHistory.activeStage r ≤ last)
        (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
        ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
          (hrs : (r : ℝ) ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
              (f j r hrs p))
    (r t : ℝ) (hr : r ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T))
    (hrT : T ≤ r) (htT : T ≤ t)
    (hxr : smoothedPhysicalMap_CX5 H T hT θ f E r hrT H.basepoint =
      f j r hr (E j (θ (r / (2 ^ j * T)), H.basepoint)))
    (hxt : smoothedPhysicalMap_CX5 H T hT θ f E t htT H.basepoint =
      f j t ht (E j (θ (t / (2 ^ j * T)), H.basepoint))) :
    ∃ (p : H.Carrier) (γ₁ γ₂ : ℝ → H.Carrier),
      p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ₁ (Icc 0 1) ∧ ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ₂ (Icc 0 1) ∧
      f j r hr (γ₁ 0) = smoothedPhysicalMap_CX5 H T hT θ f E r hrT H.basepoint ∧
      f j r hr (γ₁ 1) = f j r hr (γ₂ 0) ∧ γ₁ 1 = p ∧ γ₂ 1 = p ∧
      (∀ s ∈ Icc (0 : ℝ) 1, γ₁ s ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) ∧
        γ₂ s ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, H.metric.inner (γ₁ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₁ s 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₁ s 1) ≤ η j ^ 2 ∧
        H.metric.inner (γ₂ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₂ s 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₂ s 1) ≤ η j ^ 2) ∧
      f j t ht p = smoothedPhysicalMap_CX5 H T hT θ f E t htT H.basepoint ∧
      (∀ s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T),
        ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
            (hrW : (r : ℝ) ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
              (f j r hrW p)) := by
  have hbase : H.basepoint ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) :=
    mem_riemannianBallOf_self_S33 H.metric H.basepoint (by linarith)
  set μr := θ (r / (2 ^ j * T)) with hμr
  set μt := θ (t / (2 ^ j * T)) with hμt
  have hp : E j (μt, H.basepoint) ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) :=
    E_mem_ball_S101 H (E j) hbij hsupp μt hbase
  obtain ⟨γ₁, hγ₁, h10, h11, hγ₁B, hγ₁s⟩ := eseg_path_ball_S101 H (E j) hE hbij hsupp hbase
    (hispeed · · H.basepoint) (hθ (r / (2 ^ j * T))) (hθ (t / (2 ^ j * T)))
  obtain ⟨γ₂, hγ₂, h20, h21, hγ₂B, hγ₂s⟩ := eseg_path_ball_S101 H (E j) hE hbij hsupp hbase
    (hispeed · · H.basepoint) (hθ (t / (2 ^ j * T))) (hθ (t / (2 ^ j * T)))
  refine ⟨E j (μt, H.basepoint), γ₁, γ₂, hp, hγ₁, hγ₂, ?_, ?_, h11, h21,
    fun s hs => ⟨hγ₁B s hs, hγ₂B s hs⟩, fun s hs => ⟨hγ₁s s hs, hγ₂s s hs⟩, ?_, ?_⟩
  · rw [h10, hxr]
  · rw [h11, h20]
  · rw [hxt]
  · intro s hs
    obtain ⟨n, first, last, ordered, a, b, has, hsb, hb, stages, φ, -, hφ⟩ := hlift s hs
    exact ⟨n, first, last, ordered, a, b, has, hsb, hb, stages, φ (E j (μt, H.basepoint)),
      fun r' hr' hrW => hφ r' hr' hrW _ hp⟩

end GC.LongTime.Ch12
