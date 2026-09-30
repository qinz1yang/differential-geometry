import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ReservedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCanonicalContinuation
set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff NNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

def ReservedBefore (ε C1 C2 ν q t₀ : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), t ∈ Ioo a t₀ → q < G.flow.scalar t y →
    Nonempty (ReservedCanonicalWitness (G.flow.base.metric t) ε C1 C2 ν y)

def ReservedOn (ε C1 C2 ν q t₀ η : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), a < t → t₀ ≤ t → t < t₀+η → t < s →
    q < G.flow.scalar t y →
    Nonempty (ReservedCanonicalWitness (G.flow.base.metric t) ε C1 C2 ν y)

theorem reservedBefore_start (ε C1 C2 ν q : ℝ) : ReservedBefore G ε C1 C2 ν q a := by
  intro y t ht
  exact (not_lt_of_ge ht.1.le ht.2).elim

theorem reservedBefore_forget {ε C1 C2 ν q t₀ : ℝ}
    (h : ReservedBefore G ε C1 C2 ν q t₀) : G.SpatiallyCanonicalBefore ε C1 C2 q t₀ := by
  intro y t ht hq
  obtain ⟨V⟩ := h y t ht hq
  exact ⟨V.witness,V.cap_neck⟩

theorem canonicalBefore_end_of_continuation_reserved {ε C1 C2 C1s C2s qcan qs τmin : ℝ}
    {ν : ℝ} {Ctime Cgrad : ℝ≥0} (N : ℝ → Prop)
    (hN : ∀ t₀ ∈ Ioo a s, G.CanonicalBefore ε C1 C2 qcan τmin t₀ →
      G.DerivativeBoundBefore Ctime qcan t₀ → G.GradientBoundBefore Cgrad qcan t₀ →
      ReservedBefore G ε C1s C2s ν qs t₀ → N t₀)
    (hNa : N a)
    (hcont : ∀ t₀ ∈ Ico a s, G.CanonicalBefore ε C1 C2 qcan τmin t₀ →
      G.DerivativeBoundBefore Ctime qcan t₀ → G.GradientBoundBefore Cgrad qcan t₀ →
      ReservedBefore G ε C1s C2s ν qs t₀ → N t₀ →
      ∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧ G.GradientBoundOn Cgrad qcan t₀ η ∧
        G.CanonicalOn ε C1 C2 qcan τmin t₀ η ∧ ReservedOn G ε C1s C2s ν qs t₀ η) :
    G.CanonicalBefore ε C1 C2 qcan τmin s ∧ G.DerivativeBoundBefore Ctime qcan s ∧
      G.GradientBoundBefore Cgrad qcan s ∧ ReservedBefore G ε C1s C2s ν qs s := by
  set A : Set ℝ := {τ | τ ∈ Icc a s ∧ G.CanonicalBefore ε C1 C2 qcan τmin τ ∧
    G.DerivativeBoundBefore Ctime qcan τ ∧ G.GradientBoundBefore Cgrad qcan τ ∧
    ReservedBefore G ε C1s C2s ν qs τ}
  have hmemA : a ∈ A :=
    ⟨⟨le_rfl, G.lt.le⟩, G.canonicalBefore_start ε C1 C2 qcan τmin,
      G.derivativeBoundBefore_start Ctime qcan, G.gradientBoundBefore_start Cgrad qcan,
      reservedBefore_start G ε C1s C2s ν qs⟩
  have hne : A.Nonempty := ⟨_, hmemA⟩
  have hbdd : BddAbove A := ⟨s, fun τ hτ => hτ.1.2⟩
  have hTa : a ≤ sSup A := le_csSup hbdd hmemA
  have hTs : sSup A ≤ s := csSup_le hne fun τ hτ => hτ.1.2
  have hcanT : G.CanonicalBefore ε C1 C2 qcan τmin (sSup A) := by
    intro y t ht hR hτ
    obtain ⟨τ, hτA, htτ⟩ := exists_lt_of_lt_csSup hne ht.2
    exact hτA.2.1 y t ⟨ht.1, htτ⟩ hR hτ
  have hderT : G.DerivativeBoundBefore Ctime qcan (sSup A) := by
    intro y t ht hR
    obtain ⟨τ, hτA, htτ⟩ := exists_lt_of_lt_csSup hne ht.2
    exact hτA.2.2.1 y t ⟨ht.1, htτ⟩ hR
  have hgradT : G.GradientBoundBefore Cgrad qcan (sSup A) := by
    intro y t ht hR
    obtain ⟨τ, hτA, htτ⟩ := exists_lt_of_lt_csSup hne ht.2
    exact hτA.2.2.2.1 y t ⟨ht.1, htτ⟩ hR
  have hspatT : ReservedBefore G ε C1s C2s ν qs (sSup A) := by
    intro y t ht hR
    obtain ⟨τ, hτA, htτ⟩ := exists_lt_of_lt_csSup hne ht.2
    exact hτA.2.2.2.2 y t ⟨ht.1, htτ⟩ hR
  rcases hTs.lt_or_eq with hlt | heq
  · exfalso
    have hNT : N (sSup A) := by
      rcases hTa.lt_or_eq with hlt' | heq'
      · exact hN (sSup A) ⟨hlt', hlt⟩ hcanT hderT hgradT hspatT
      · rw [← heq']
        exact hNa
    obtain ⟨η, hη, hder, hgrad, hcan, hspat⟩ :=
      hcont (sSup A) ⟨hTa, hlt⟩ hcanT hderT hgradT hspatT hNT
    have hmem : min (sSup A + η) s ∈ A := by
      refine ⟨⟨le_min (by linarith) G.lt.le, min_le_right _ _⟩, ?_, ?_, ?_, ?_⟩
      · intro y t ht hR hτ
        rcases lt_or_ge t (sSup A) with htT | hTt
        · exact hcanT y t ⟨ht.1, htT⟩ hR hτ
        · exact hcan y t ht.1 hTt (lt_of_lt_of_le ht.2 (min_le_left _ _))
            (lt_of_lt_of_le ht.2 (min_le_right _ _)) hR hτ
      · intro y t ht hR
        rcases lt_or_ge t (sSup A) with htT | hTt
        · exact hderT y t ⟨ht.1, htT⟩ hR
        · exact hder y t ht.1 hTt (lt_of_lt_of_le ht.2 (min_le_left _ _))
            (lt_of_lt_of_le ht.2 (min_le_right _ _)) hR
      · intro y t ht hR
        rcases lt_or_ge t (sSup A) with htT | hTt
        · exact hgradT y t ⟨ht.1, htT⟩ hR
        · exact hgrad y t ht.1 hTt (lt_of_lt_of_le ht.2 (min_le_left _ _))
            (lt_of_lt_of_le ht.2 (min_le_right _ _)) hR
      · intro y t ht hR
        rcases lt_or_ge t (sSup A) with htT | hTt
        · exact hspatT y t ⟨ht.1, htT⟩ hR
        · exact hspat y t ht.1 hTt (lt_of_lt_of_le ht.2 (min_le_left _ _))
            (lt_of_lt_of_le ht.2 (min_le_right _ _)) hR
    have hle : min (sSup A + η) s ≤ sSup A := le_csSup hbdd hmem
    have hgt : sSup A < min (sSup A + η) s := lt_min (by linarith) hlt
    exact absurd hle (not_le.mpr hgt)
  · rw [heq] at hcanT hderT hgradT hspatT
    exact ⟨hcanT, hderT, hgradT, hspatT⟩

theorem reservedContinuation_ballConsumer {ε C1 C2 C1s C2s qcan qs τmin : ℝ}
    {ν : ℝ} {Ctime Cgrad : ℝ≥0} (hν : 0 < ν) (N : ℝ → Prop)
    (hN : ∀ t₀ ∈ Ioo a s, G.CanonicalBefore ε C1 C2 qcan τmin t₀ →
      G.DerivativeBoundBefore Ctime qcan t₀ → G.GradientBoundBefore Cgrad qcan t₀ →
      ReservedBefore G ε C1s C2s ν qs t₀ → N t₀)
    (hNa : N a)
    (hcont : ∀ t₀ ∈ Ico a s, G.CanonicalBefore ε C1 C2 qcan τmin t₀ →
      G.DerivativeBoundBefore Ctime qcan t₀ → G.GradientBoundBefore Cgrad qcan t₀ →
      ReservedBefore G ε C1s C2s ν qs t₀ → N t₀ →
      ∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧ G.GradientBoundOn Cgrad qcan t₀ η ∧
        G.CanonicalOn ε C1 C2 qcan τmin t₀ η ∧ ReservedOn G ε C1s C2s ν qs t₀ η) :
    ∃ k : ℝ, 0 < k ∧ ∀ (y : P.Carrier) (t : ℝ), t ∈ Ioo a s →
      qs < G.flow.scalar t y → ∀ r : ℝ, 0 < r →
      r^4 * normSq0S (G.flow.base.metric t) y 4
        (metricRm04At (G.flow.base.metric t) y) ≤ 1 →
      ENNReal.ofReal (k*r^3) ≤ riemannianVolumeMeasure I3 P.Carrier
        (G.flow.base.metric t) (riemannianBallOf (G.flow.base.metric t) y r) := by
  have hend := canonicalBefore_end_of_continuation_reserved G N hN hNa hcont
  obtain ⟨k,hk,hball⟩ := reservedCanonicalBallConsumer.{u} ε C1s C2s ν hν
  refine ⟨k,hk,?_⟩
  intro y t ht hq r hr hcurv
  obtain ⟨V⟩ := hend.2.2.2 y t ht hq
  exact hball V r hr hcurv

end GC.GeneralFlow
