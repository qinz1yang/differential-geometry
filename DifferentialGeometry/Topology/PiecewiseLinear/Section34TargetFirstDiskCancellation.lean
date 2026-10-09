import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetDiskCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SupportedMotionInverse

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_relative_first_disk_cancellation {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPLBall 3 P) {A Ab B Bb C D F J Ω : Set M}
    (hA : IsPLCellOn 3 A Ab) (hAP : A ⊆ u '' P) (hB : IsPLCellOn 3 B Bb)
    (hC : IsPLCellOn 3 C (D ∪ F)) (hD : IsPLCellOn 2 D J) (hF : IsPLCellOn 2 F J)
    (hmeet : Ab ∩ C = F) (htrace : D ∩ Ab = J) (hDB : D ⊆ Bb)
    (hrest : IsClosed ((Ab \ C) ∩ Bb)) (hΩ : IsOpen Ω) (hCΩ : C ⊆ Ω)
    (hΩP : Ω ⊆ interior (u '' P)) :
    ∃ (K : Set M) (ψ : M ≃ₜ M), IsCompact K ∧ K ⊆ Ω ∧ EqOn ψ id Kᶜ ∧
      IsPLOn 3 3 ψ (interior (u '' P)) ∧
      Disjoint K ((Ab \ C) ∩ Bb) ∧
      (∀ x ∈ (Ab \ C) ∩ Bb, ψ =ᶠ[𝓝 x] id) ∧ ψ '' Ab ∩ Bb = (Ab \ C) ∩ Bb := by
  obtain ⟨K, ψ, hK, hKΩ, hfix, hψ, hdis, hgerm, hcancel⟩ :=
    hu.exists_relative_second_disk_cancellation hP hA hAP hB hC hD hF hmeet htrace hDB
      hrest hΩ hCΩ hΩP
  have hinv := hu.isPLOn_symm_of_supported_homeomorph hP ψ hK.isClosed
    (hKΩ.trans hΩP) hfix hψ
  have hfixinv : EqOn ψ.symm id Kᶜ :=
    fun x hx => ψ.symm_apply_eq.mpr (hfix hx).symm
  have hfixR : EqOn ψ id ((Ab \ C) ∩ Bb) :=
    fun x hx => (hgerm x hx).self_of_nhds
  have hfixRinv : EqOn ψ.symm id ((Ab \ C) ∩ Bb) :=
    fun x hx => ψ.symm_apply_eq.mpr (hfixR hx).symm
  refine ⟨K, ψ.symm, hK, hKΩ, hfixinv, hinv, hdis, ?_, ?_⟩
  · intro x hx
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds (disjoint_right.mp hdis hx)] with y hy
    exact hfixinv hy
  · apply Subset.antisymm
    · rintro x ⟨⟨a, ha, hax⟩, hxB⟩
      have hxA : ψ x ∈ Ab := by rw [← hax, ψ.apply_symm_apply]; exact ha
      have hxR := hcancel.subset ⟨hxA, x, hxB, rfl⟩
      have hxfix : ψ x = x := ψ.injective (hfixR hxR)
      exact hxfix ▸ hxR
    · exact fun x hx => ⟨⟨x, hx.1.1, hfixRinv hx⟩, hx.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
