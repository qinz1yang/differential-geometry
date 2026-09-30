import DifferentialGeometry.Topology.ClosedBall.RadialCompression
import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected
import Mathlib.Topology.Compactification.OnePoint.Basic

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology Filter

noncomputable section

theorem exists_compression_of_compl_singleton_homeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (q : X) (e : ({q}ᶜ : Set X) ≃ₜ E) {K U : Set X}
    (hK : IsCompact K) (hqK : q ∉ K) {a : X} (haq : a ≠ q)
    (hU : IsOpen U) (haU : a ∈ U) :
    ∃ h : X ≃ₜ X, h '' K ⊆ U ∧
      ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, h x = x := by
  let a' : ({q}ᶜ : Set X) := ⟨a, haq⟩
  let c : E ≃ₜ ({q}ᶜ : Set X) := (Homeomorph.addRight (e a')).trans e.symm
  let φ : E → X := fun x => (c x).1
  have hφ : IsOpenEmbedding φ :=
    (isOpen_compl_singleton.isOpenEmbedding_subtypeVal).comp c.isOpenEmbedding
  have hφrange : range φ = {q}ᶜ := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (c v).2
    · intro hx
      refine ⟨c.symm ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (c.apply_symm_apply ⟨x, hx⟩)
  have hφ0 : φ 0 = a := by
    change (e.symm (0 + e a')).1 = a
    rw [zero_add, e.symm_apply_apply]
  have hKφ : K ⊆ range φ := by
    rw [hφrange]
    intro x hx hxeq
    exact hqK (hxeq ▸ hx)
  have hKE : IsCompact (φ ⁻¹' K) := hφ.isInducing.isCompact_preimage' hK hKφ
  have hU0 : φ ⁻¹' U ∈ 𝓝 (0 : E) :=
    (hU.preimage hφ.continuous).mem_nhds (by simpa only [mem_preimage, hφ0] using haU)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU0
  obtain ⟨R, hεR, hKR⟩ := hKE.isBounded.subset_closedBall_lt ε (0 : E)
  obtain ⟨r, hrfix, hrK⟩ := exists_radial_compression
    (E := E) (δ := ε / 2) (by positivity) (by linarith) hεR
  let j : OnePoint E ≃ₜ X :=
    OnePoint.equivOfIsEmbeddingOfRangeEq q φ hφ.isEmbedding hφrange
  have hj (x : E) : j (x : OnePoint E) = φ x := rfl
  let h : X ≃ₜ X := (j.symm.trans r.onePointCongr).trans j
  have hh (x : E) : h (φ x) = φ (r x) := by
    change j (r.onePointCongr (j.symm (φ x))) = φ (r x)
    rw [← hj x, j.symm_apply_apply]
    exact hj (r x)
  refine ⟨h, ?_, φ '' ball 0 (ε / 2), hφ.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, rfl⟩ := hKφ hx
    rw [hh]
    exact hεU (hrK (hKR hx))
  · exact ⟨0, mem_ball_self (by positivity), hφ0⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hh, hrfix x (mem_ball_zero_iff.mp hx).le]

theorem exists_sphere_compression {n : ℕ}
    {K U : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}
    (hK : IsCompact K) (hproper : K ≠ univ)
    {a : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1} (ha : a ∈ K)
    (hU : IsOpen U) (haU : a ∈ U) :
    ∃ h : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₜ
        sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      h '' K ⊆ U ∧ ∃ V, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, h x = x := by
  obtain ⟨q, hq⟩ := Set.nonempty_compl.mpr hproper
  exact exists_compression_of_compl_singleton_homeomorph q (sphereComplSingletonHomeomorph q)
    hK hq (fun heq => hq (heq ▸ ha)) hU haU

end

end DifferentialGeometry.Topology
