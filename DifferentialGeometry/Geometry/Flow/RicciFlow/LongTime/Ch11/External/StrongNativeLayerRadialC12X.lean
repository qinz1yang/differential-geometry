import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNativeLayerDeepC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceFinalC12X

/-!
# Uniform native strong-neck layer with the window input discharged (C12X, S16 round 3)

O-C12X-S16K G3c.  S16H G4e6 (`StrongWindowSpliceFinalC12X`) proves the window input
`HwinYoungDeep_C12X (RecordHypFar_C12X θ) ε D₀ θ₀ Cu` unconditionally for `1 < θ`
(`exists_hwinYoungDeep_theta_of_far_radial_C12X`).  Feeding it to the v3 engine
`native_strongFull_uniform_of_classFull_C12X` removes the window binder: the uniform constants
`Ccore Cu` are chosen once from `ε` (and `θ`), and the class conclusion only assumes the route β′
record hypothesis `RecordHypFar_C12X θ` of the native history.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **v3 engine, window input discharged** (main instance `θ = 5/4`). -/
theorem native_strongFull_uniform_of_classFull_radial_C12X {θ : ℝ} (hθ : 1 < θ) (ε : ℝ)
    (hε : 0 < ε) (hεs : ε ≤ εStrong_C12X.{u}) :
    ∃ Ccore Cu : ℝ, 1 ≤ Ccore ∧ 1 ≤ Cu ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (B : ℝ), 0 < B →
    ∀ (C1 C2 C1s C2s qcan qs τmin : ℝ) (Ctime Cgrad : ℝ≥0) (κ : ℝ),
      1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → qcan ≤ qs → 0 < τmin → 0 < κ →
    ∃ (qh δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      qs ≤ qh ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ K.toHistory →
      ∀ (pK : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        RecordHypFar_C12X θ K records →
        K.NoncollapsedBefore κ ε K.horizon →
        GC.GeneralFlow.NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad →
        K.EventSlabsStronglyCanonicalFull_C12X ε ε (max C1 (max Ccore Cu))
          (max C2 (max (max Ccore Cu) (Cgrad : ℝ))) qh (Fin.last K.eventCount) ∧
        ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
          K.StronglyCanonicalBeforeFull_C12X (Fin.last K.eventCount)
            ((K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε (max C1 (max Ccore Cu))
          (max C2 (max (max Ccore Cu) (Cgrad : ℝ))) qh
            K.horizon := by
  have hε11 : ε < 1 / 11 := (hεs.trans_lt εStrong_C12X_lt).trans (by norm_num)
  obtain ⟨D₀, θ₀, Cu, hD₀, -, hθ₀, hCu, hwin⟩ :=
    exists_hwinYoungDeep_theta_of_far_radial_C12X.{u} hε hε11 hθ
  obtain ⟨Ccore, hCcore, hU⟩ :=
    native_strongFull_uniform_of_classFull_C12X.{u} θ ε hε hεs D₀ θ₀ hD₀ hθ₀
  exact ⟨Ccore, Cu, hCcore, hCu, hU Cu hwin⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
