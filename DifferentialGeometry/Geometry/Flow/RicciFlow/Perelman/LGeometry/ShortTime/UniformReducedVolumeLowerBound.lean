import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.LowerSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedVolumeLimit
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private theorem exists_redVolume_gt_half_nhds
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (rho : Real) (hrho : 0 < rho)
    (hreg : Icc (T - rho) T ⊆ D.regular) :
    ∃ tau : Real, 0 < tau ∧ tau < rho ∧
      {p : Real × M |
        (1 / 2 : ENNReal) < redVolume S p.1 p.2 tau} ∈ 𝓝 (T, x) := by
  have hTreg : T ∈ D.regular := by
    apply hreg
    exact ⟨by linarith, le_rfl⟩
  have hhalf : (1 / 2 : ENNReal) < 1 := by
    simpa only [one_div] using ENNReal.one_half_lt_one
  have hvol : ∀ᶠ tau in 𝓝[>] (0 : Real),
      (1 / 2 : ENNReal) < redVolume S T x tau :=
    (tendsto_redVolume_at_zero (I := I) S hS T x hTreg)
      (Ioi_mem_nhds hhalf)
  have hsmall : ∀ᶠ tau in 𝓝[>] (0 : Real), tau < rho :=
    (tendsto_order.1
      (tendsto_id.mono_left nhdsWithin_le_nhds)).2 rho hrho
  have hpos : ∀ᶠ tau : Real in 𝓝[>] (0 : Real), 0 < tau := by
    change Ioi (0 : Real) ∈ 𝓝[>] (0 : Real)
    exact self_mem_nhdsWithin
  obtain ⟨tau, htau, hvoltau, htaurho⟩ :=
    (hpos.and (hvol.and hsmall)).exists
  have hslab : Icc (T - tau) T ⊆ D.regular := by
    intro r hr
    apply hreg
    exact ⟨(sub_le_sub_left htaurho.le T).trans hr.1, hr.2⟩
  have hnhds :=
    redVolume_lsc (I := I) S hS T x tau htau hslab
      (1 / 2 : ENNReal) hvoltau
  exact ⟨tau, htau, htaurho, hnhds⟩

theorem exists_uniform_redVolume_gt_half
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (a b rho : Real) (hab : a ≤ b) (hrho : 0 < rho)
    (hreg : ∀ T ∈ Icc a b, Icc (T - rho) T ⊆ D.regular) :
    ∃ tau₀ : Real, 0 < tau₀ ∧ tau₀ < rho ∧
      ∀ T ∈ Icc a b, ∀ x : M, ∀ tau : Real,
        0 < tau → tau ≤ tau₀ →
          (1 / 2 : ENNReal) < redVolume S T x tau := by
  classical
  let K : Set (Real × M) := Icc a b ×ˢ (univ : Set M)
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hlocal : ∀ p : K,
      ∃ tau : Real, 0 < tau ∧ tau < rho ∧
        {q : Real × M |
          (1 / 2 : ENNReal) < redVolume S q.1 q.2 tau} ∈ 𝓝 (p : Real × M) := by
    intro p
    exact exists_redVolume_gt_half_nhds (I := I) S hS p.1.1 p.1.2 rho hrho
      (hreg p.1.1 p.2.1)
  choose tau htau_pos htau_lt hU using hlocal
  let U : K → Set (Real × M) := fun p ↦
    {q : Real × M |
      (1 / 2 : ENNReal) < redVolume S q.1 q.2 (tau p)}
  obtain ⟨s, hs_cover⟩ :=
    hKcompact.elim_nhds_subcover'
      (fun p hp ↦ U ⟨p, hp⟩) (fun p hp ↦ hU ⟨p, hp⟩)
  have hKne : K.Nonempty := by
    refine ⟨(a, Classical.arbitrary M), ?_⟩
    exact ⟨⟨le_rfl, hab⟩, mem_univ _⟩
  have hs_ne : s.Nonempty := by
    obtain ⟨p, hpK⟩ := hKne
    have hp_cover := hs_cover hpK
    rw [Set.mem_iUnion₂] at hp_cover
    obtain ⟨q, hqs, _hpq⟩ := hp_cover
    exact ⟨q, hqs⟩
  let tau₀ : Real := s.inf' hs_ne tau
  have htau₀_pos : 0 < tau₀ := by
    rw [show tau₀ = s.inf' hs_ne tau from rfl,
      Finset.lt_inf'_iff]
    intro p _hp
    exact htau_pos p
  have htau₀_le : ∀ p ∈ s, tau₀ ≤ tau p := by
    intro p hp
    exact Finset.inf'_le _ hp
  have htau₀_rho : tau₀ < rho := by
    obtain ⟨p, hp⟩ := hs_ne
    exact (htau₀_le p hp).trans_lt (htau_lt p)
  refine ⟨tau₀, htau₀_pos, htau₀_rho, ?_⟩
  intro T hT x tau' htau' htau'₀
  have hTxK : (T, x) ∈ K := ⟨hT, mem_univ x⟩
  have hTx_cover := hs_cover hTxK
  rw [Set.mem_iUnion₂] at hTx_cover
  obtain ⟨p, hp, hTxp⟩ := hTx_cover
  dsimp only [U] at hTxp
  have hslabp :
      Icc (T - tau p) T ⊆ D.regular := by
    intro r hr
    apply hreg T hT
    exact ⟨(sub_le_sub_left (htau_lt p).le T).trans hr.1,
      hr.2⟩
  have hslab₀ : Icc (T - tau₀) T ⊆ D.regular := by
    intro r hr
    apply hreg T hT
    exact ⟨(sub_le_sub_left htau₀_rho.le T).trans hr.1, hr.2⟩
  have hp_to_floor :
      redVolume S T x (tau p) ≤ redVolume S T x tau₀ :=
    redVolume_anti (I := I) S hS T x htau₀_pos
      (htau₀_le p hp) hslabp
  have hfloor_to_tau : redVolume S T x tau₀ ≤ redVolume S T x tau' :=
    redVolume_anti (I := I) S hS T x htau' htau'₀ hslab₀
  exact hTxp.trans_le (hp_to_floor.trans hfloor_to_tau)

end DifferentialGeometry.PDE.RicciFlow.Perelman
