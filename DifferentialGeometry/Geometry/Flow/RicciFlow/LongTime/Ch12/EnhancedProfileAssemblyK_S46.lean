import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallK_S44

/-!
# CH12-S46, group 1: `hW1_of_enhanced_O2` with the K-indexed micro glue

`hW1_of_enhanced_K_S46` is `hW1_of_enhanced_O2` (`EnhancedProfileAssembly.lean:80`) with the
micro-regime input `hMicro : ... → MicroWholeBall_O2 Hp` replaced by
`hMicroK : ... → MicroWholeBallK_S44 Hp K`: the late time `T` and the constants of the micro glue may
depend on the order cap `K` (derivative orders `k ≤ K`), which is what the recent-cap branch
supports (see "[FROZEN v2] CH12-S44").  The conclusion is the conclusion of `hW1_of_enhanced_O2`
verbatim.  The proof is copied: `K` is used only to feed `k ≤ K` to the micro bound; the macro
branch ignores it.  `microWholeBallK_of_microWholeBall_S46` shows the old `MicroWholeBall_O2 Hp`
implies `MicroWholeBallK_S44 Hp K` for every `K`, so every old `hMicro` yields an `hMicroK`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- The uniform micro glue `MicroWholeBall_O2 Hp` implies the order-capped one, for every `K`
(restrict to `k ≤ K`; same `b`, `T`, `A`). -/
theorem microWholeBallK_of_microWholeBall_S46 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (K : ℕ) (h : MicroWholeBall_O2 Hp) : MicroWholeBallK_S44 Hp K := by
  intro w hw Λ hΛ
  obtain ⟨b, T, A, hb, h'⟩ := h w hw Λ hΛ
  exact ⟨b, T, A, hb, fun s hs p ρ hρ hρb hrec hneg hsec hvol k _ q hq =>
    h' s hs p ρ hρ hρb hrec hneg hsec hvol k q hq⟩

/-- **WBD03, physical form, under P1–P4, with the K-indexed micro glue.**  Same conclusion as
`hW1_of_enhanced_O2` (second component = `hphysical` of
`UniformNormalizedDerivativeBounds.lean:21`); `hMicro` is replaced by `hMicroK`. -/
theorem hW1_of_enhanced_K_S46 (F : GC.Interface.RawSurgery P g) (K : ℕ) (δ : ℝ → ℝ)
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hP1 : P1_O2 Hp) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) (hP3 : P3_O2 Hp) (hP4 : P4_O2 Hp)
    (hW3 : MacroWholeBall_O2 Hp)
    (hMicroK : P2_O2 Hp Ctime → (∀ κ : ℝ, 0 < κ → ∀ (Cgrad : ℝ≥0) (phi : ℝ → ℝ),
        Perelman.AdmissiblePinchingFunction phi → W4Output_O2 Hp κ Ctime Cgrad phi) →
      (∀ N : ℕ, capWindowJets_O2 Hp N) → MicroWholeBallK_S44 Hp K) :
    ∃ (b T : ℝ → ℝ) (A : ℝ → ℕ → ℝ), (∀ w : ℝ, 0 < w → 0 < b w) ∧
      ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation,
        T w ≤ s.time → ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        ρ ≤ b w * Real.sqrt s.time →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.metric p ρ,
          curvatureDerivativeNorm s.metric k q ≤ A w k * (ρ ^ (k + 2))⁻¹ := by
  classical
  have hW4 : ∀ κ : ℝ, 0 < κ → ∀ (Cgrad : ℝ≥0) (phi : ℝ → ℝ),
      Perelman.AdmissiblePinchingFunction phi → W4Output_O2 Hp κ Ctime Cgrad phi :=
    fun κ hκ Cgrad _ hphi => W4_scalar_bound_O2 Hp hP4 κ hκ Ctime Cgrad hphi
  have hW5 : ∀ N : ℕ, capWindowJets_O2 Hp N := fun N => late_cap_window_jets_O2 Hp hdec hP1 hP3 N
  have hmicro := hMicroK hP2 hW4 hW5
  have key : ∀ w : ℝ, 0 < w → ∃ (b T : ℝ) (A : ℕ → ℝ), 0 < b ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.metric p ρ,
          curvatureDerivativeNorm s.metric k q ≤ A k * (ρ ^ (k + 2))⁻¹ := by
    intro w hw
    obtain ⟨Λ, b₁, T₁, A₁, hΛ, hb₁, h₁⟩ := hW3 w hw
    obtain ⟨b₂, T₂, A₂, hb₂, h₂⟩ := hmicro w hw Λ hΛ
    refine ⟨min b₁ b₂, max T₁ T₂, fun k => max (A₁ k) (A₂ k), lt_min hb₁ hb₂, ?_⟩
    intro s hs p ρ hρ hρb hneg hsec hvol k hk q hq
    have hpos : (0 : ℝ) ≤ (ρ ^ (k + 2))⁻¹ := inv_nonneg.mpr (pow_nonneg hρ.le _)
    have hsq := Real.sqrt_nonneg s.time
    by_cases hmac : ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
        ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ ρ
    · exact (h₁ s ((le_max_left _ _).trans hs) p ρ hρ
        (hρb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsq)) hmac hneg hsec hvol
        k q hq).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
    · push Not at hmac
      obtain ⟨n, i, hi, h, hlt⟩ := hmac
      exact (h₂ s ((le_max_right _ _).trans hs) p ρ hρ
        (hρb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hsq)) ⟨n, i, h, hi, hlt⟩
        hneg hsec hvol k hk q hq).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos)
  choose! b T A hb hbound using key
  exact ⟨b, T, A, hb, hbound⟩

end GC.LongTime.Ch12
