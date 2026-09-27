import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCanonicalContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSpatialCanonicalWitness

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem derivativeBoundBefore_of_derivativeBoundOn {Ctime : ℝ≥0} {qcan t₀ η t : ℝ}
    (hB : G.DerivativeBoundBefore Ctime qcan t₀) (hO : G.DerivativeBoundOn Ctime qcan t₀ η)
    (htη : t ≤ t₀ + η) (hts : t ≤ s) : G.DerivativeBoundBefore Ctime qcan t := by
  intro y t' ht' hR
  rcases lt_or_ge t' t₀ with h | h
  · exact hB y t' ⟨ht'.1, h⟩ hR
  · exact hO y t' ht'.1 h (ht'.2.trans_le htη) (ht'.2.trans_le hts) hR

theorem exists_spatialCanonicalWitness_of_canonicalOn {ε C1 C2 C1s C2s qcan qs τmin t₀ η : ℝ}
    (h1 : C1 ≤ C1s) (h2 : C2 ≤ C2s) (hq : qcan ≤ qs)
    (hcan : G.CanonicalOn ε C1 C2 qcan τmin t₀ η) {y : P.Carrier} {t : ℝ} (hat : a < t)
    (ht₀ : t₀ ≤ t) (htη : t < t₀ + η) (hts : t < s) (hR : qs < G.flow.scalar t y)
    (hold : τmin ≤ G.flow.scalar t y * (t - a)) :
    ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1s C2s y, W.capTubeHasNeckChart ε := by
  obtain ⟨W, hW⟩ := hcan y t hat ht₀ htη hts (hq.trans_lt hR) hold
  exact ⟨W.toSpatial.enlargeConstants h1 h2,
    (W.capTubeHasNeckChart_toSpatial hW).enlarge_constants h1 h2⟩

end OrientedThreeStage.IncomingSlab

theorem spatialCanonicalContinuation_of_spatialCrossing
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (hX : SpatialCrossingContinuation P₀ g₀) :
    SpatialCanonicalContinuation P₀ g₀ := by
  obtain ⟨εbar, hεbar, -, hX⟩ := hX
  refine ⟨εbar, hεbar, ?_⟩
  intro B ε hB hε hε' hεb C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
  obtain ⟨Cx, hCx, hX⟩ := hX ε hε hε' hεb
  obtain ⟨Cw, hCw, hM5⟩ :=
    RetainedCoreHistory.exists_capWindowPoint_spatialCanonicalWitness P₀ g₀ hε hε'
  have hA1 : C1 ≤ max C1 (max Cw Cx) := le_max_left _ _
  have hA2 : C2 ≤ max C2 (max (max Cw (Cgrad : ℝ)) Cx) := le_max_left _ _
  have hB1 : Cw ≤ max C1 (max Cw Cx) := (le_max_left _ _).trans (le_max_right _ _)
  have hB2 : max Cw (Cgrad : ℝ) ≤ max C2 (max (max Cw (Cgrad : ℝ)) Cx) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hX1 : Cx ≤ max C1 (max Cw Cx) := (le_max_right _ _).trans (le_max_right _ _)
  have hX2 : Cx ≤ max C2 (max (max Cw (Cgrad : ℝ)) Cx) :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max C1 (max Cw Cx), max C2 (max (max Cw (Cgrad : ℝ)) Cx), 1, hC1.trans hA1,
    hC2.trans hA2, le_rfl, ?_⟩
  intro κ phi hκ hphi
  obtain ⟨Dx, θcap, qx, mx, hDx, hθcap, hqx, hXq⟩ :=
    hX B hB C1 C2 τmin Ctime Cgrad hC1 hC2 hτ _ _ 1 (hC1.trans hA1) (hC2.trans hA2) le_rfl
      κ phi τmin hκ hphi hτ
  obtain ⟨Rcap, mw, hRcap, hM5q⟩ := hM5 Ctime Cgrad Dx θcap hDx hθcap
  refine ⟨qx, hqx, fun qcan hqcan => ?_⟩
  obtain ⟨δx, ρx, εx, hδx, hρx, hεx, hXs⟩ := hXq qcan hqcan
  obtain ⟨δw, ρw, εw, hδw, hρw, hεw, hM5s⟩ := hM5q qcan (hqx.trans_le hqcan)
  refine ⟨qcan, min δx δw, min ρx ρw, min εx εw, max Dx Rcap, max mx mw, le_rfl,
    (one_mul qcan).ge, lt_min hδx hδw, lt_min hρx hρw, lt_min hεx hεw, lt_max_of_lt_left hDx, ?_⟩
  intro p₀ δbound ρbound hacc hD hm hδ hρ H hH hpinch
  obtain ⟨p, records, hrec⟩ :=
    (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mp
      hH.2.2.2.1
  have hXH := hXs qcan le_rfl (one_mul qcan).ge p₀ δbound ρbound (hacc.trans (min_le_left _ _))
    ((le_max_left _ _).trans hD) ((le_max_left _ _).trans hm) (hδ.trans (min_le_left _ _))
    (hρ.trans (min_le_left _ _)) H hH p records hrec hpinch
  have hW := hM5s p₀ δbound ρbound (hacc.trans (min_le_right _ _)) ((le_max_right _ _).trans hD)
    ((le_max_right _ _).trans hm) (hδ.trans (min_le_right _ _)) (hρ.trans (min_le_right _ _))
    H hH.1 hH.2.2.2.2 p records hrec
  refine ⟨fun j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn hC3 => ?_,
    fun s G hG hpinchG hcanL hderL hgradL hspatL hncL t₀ ht₀ hc hd hg hsp hn hC3 => ?_⟩
  · obtain ⟨η₃, hη₃, hdOn, hgOn, hcOn⟩ := hC3
    obtain ⟨η, hη, hηη₃, -, hYoung⟩ :=
      hXH.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn η₃ hη₃ hdOn hgOn hcOn
    refine ⟨η, hη, fun y t hat ht₀' htη hts hR => ?_⟩
    have htη₃ : t < t₀ + η₃ := htη.trans_le (by linarith)
    rcases le_or_gt τmin
        ((H.toHistory.event j).incoming.flow.scalar t y * (t - H.time j.castSucc)) with
      hold | hyoung
    · exact (H.toHistory.event j).incoming.exists_spatialCanonicalWitness_of_canonicalOn hA1 hA2
        le_rfl hcOn hat ht₀' htη₃ hts hR hold
    by_cases hcw : H.CapWindowPoint records j.castSucc y t Dx θcap
    · obtain ⟨W, hW'⟩ := hW j.castSucc (H.time j.succ) (H.toHistory.event j).incoming
        (H.event_initial j) hderP t hat hts
        ((H.toHistory.event j).incoming.derivativeBoundBefore_of_derivativeBoundOn hd hdOn
          htη₃.le hts.le) y hcw hR (hgOn y t hat ht₀' htη₃ hts hR)
      exact ⟨W.enlargeConstants hB1 hB2, hW'.enlarge_constants hB1 hB2⟩
    · obtain ⟨W, hW'⟩ := hYoung y t hat ht₀' htη hts hR hyoung hcw
      exact ⟨W.enlargeConstants hX1 hX2, hW'.enlarge_constants hX1 hX2⟩
  · obtain ⟨η₃, hη₃, hdOn, hgOn, hcOn⟩ := hC3
    obtain ⟨η, hη, hηη₃, -, hYoung⟩ :=
      hXH.2 s G hG hpinchG hcanL hderL hgradL hspatL hncL t₀ ht₀ hc hd hg hsp hn η₃ hη₃ hdOn hgOn
        hcOn
    refine ⟨η, hη, fun y t hat ht₀' htη hts hR => ?_⟩
    have htη₃ : t < t₀ + η₃ := htη.trans_le (by linarith)
    rcases le_or_gt τmin (G.flow.scalar t y * (t - H.time (Fin.last H.eventCount))) with
      hold | hyoung
    · exact G.exists_spatialCanonicalWitness_of_canonicalOn hA1 hA2 le_rfl hcOn hat ht₀' htη₃ hts
        hR hold
    by_cases hcw : H.CapWindowPoint records (Fin.last H.eventCount) y t Dx θcap
    · obtain ⟨W, hW'⟩ := hW (Fin.last H.eventCount) s G hG.2 hderL t hat hts
        (G.derivativeBoundBefore_of_derivativeBoundOn hd hdOn htη₃.le hts.le) y hcw hR
        (hgOn y t hat ht₀' htη₃ hts hR)
      exact ⟨W.enlargeConstants hB1 hB2, hW'.enlarge_constants hB1 hB2⟩
    · obtain ⟨W, hW'⟩ := hYoung y t hat ht₀' htη hts hR hyoung hcw
      exact ⟨W.enlargeConstants hX1 hX2, hW'.enlarge_constants hX1 hX2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
