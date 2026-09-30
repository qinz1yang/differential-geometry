import DifferentialGeometry.Analysis.Calculus.TimeJet.JetPDE
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundaryDerivLimit
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.Piecewise

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ E] in
private theorem continuousOn_ite_le_seam {Y : Type*} [TopologicalSpace Y]
    {a c b : ℝ} {V : Set E}
    (fL fR : ℝ × E → Y)
    (hL : ContinuousOn fL (Icc a c ×ˢ V))
    (hR : ContinuousOn fR (Icc c b ×ˢ V))
    (hmatch : ∀ x ∈ V, fL (c, x) = fR (c, x)) :
    ContinuousOn (fun p : ℝ × E => if p.1 ≤ c then fL p else fR p) (Icc a b ×ˢ V) := by
  apply ContinuousOn.if
  · intro p hp
    have heq : p.1 = c :=
      frontier_le_subset_eq continuous_fst continuous_const hp.2
    simpa only [← heq] using hmatch p.2 hp.1.2
  · apply hL.mono
    intro p hp
    have hpc : p.1 ≤ c := by
      have hh : IsClosed {p : ℝ × E | p.1 ≤ c} :=
        isClosed_le continuous_fst continuous_const
      have hx := hp.2
      rw [hh.closure_eq] at hx
      exact hx
    exact ⟨⟨hp.1.1.1, hpc⟩, hp.1.2⟩
  · apply hR.mono
    intro p hp
    have hpc : c ≤ p.1 := by
      exact closure_lt_subset_le
        (continuous_const : Continuous (fun _ : ℝ × E => c)) continuous_fst
        (by simpa only [not_le] using hp.2)
    exact ⟨⟨hpc, hp.1.1.2⟩, hp.1.2⟩


omit [CompleteSpace F] in
private theorem jet2_eq_of_eqOn {f g : E → F} {V : Set E}
    (hV : IsOpen V) (hfg : EqOn f g V) {x : E} (hx : x ∈ V) :
    jet2 f x = jet2 g x := by
  have hev : f =ᶠ[𝓝 x] g := eventuallyEq_of_mem (hV.mem_nhds hx) hfg
  exact Prod.ext (hfg hx) (Prod.ext hev.fderiv_eq hev.fderiv.fderiv_eq)

omit [CompleteSpace F] in
private theorem continuousOn_spatial_ite
    {gL gR : ℝ → E → F} {a c b : ℝ} {V : Set E}
    (ha : a < c) (hb : c < b) (hV : IsOpen V)
    (hL : ContDiffOn ℝ ∞ (Function.uncurry gL) (Icc a c ×ˢ V))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry gR) (Icc c b ×ˢ V))
    (hmatch : EqOn (gL c) (gR c) V) (m : ℕ) :
    ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ m
      (if q.1 ≤ c then gL q.1 else gR q.1) q.2) (Icc a b ×ˢ V) := by
  have hGL := continuousOn_iteratedFDeriv_spatial_Icc ha hV hL m
    (by exact_mod_cast le_top)
  have hGR := continuousOn_iteratedFDeriv_spatial_Icc hb hV hR m
    (by exact_mod_cast le_top)
  have hh := continuousOn_ite_le_seam
    (fun q : ℝ × E => iteratedFDeriv ℝ m (gL q.1) q.2)
    (fun q : ℝ × E => iteratedFDeriv ℝ m (gR q.1) q.2) hGL hGR
    (fun x hx => ((eventuallyEq_of_mem (hV.mem_nhds hx) hmatch).iteratedFDeriv ℝ m).self_of_nhds)
  exact hh.congr fun q _ => by
    dsimp only
    split_ifs <;> rfl

omit [CompleteSpace F] in
private theorem continuousOn_jet2_time
    {glued : ℝ → E → F} {a b : ℝ} {V : Set E}
    (hab : a < b) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry glued) (Icc a b ×ˢ V)) {x : E} (hx : x ∈ V) :
    ContinuousOn (fun t => jet2 (glued t) x) (Icc a b) := by
  have hjets (m : ℕ) : ContinuousOn (fun t => iteratedFDeriv ℝ m (glued t) x) (Icc a b) :=
    (continuousOn_iteratedFDeriv_spatial_Icc hab hV hG m (by exact_mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, hx⟩)
  exact jet2_contOn (hjets 0) (hjets 1) (hjets 2)

theorem contDiffOn_ite_of_jet_pde
    {gL gR : ℝ → E → F} {a c b : ℝ} {V : Set E}
    {Ω : Set (F × (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F))}
    {Φ : (F × (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)) → F}
    (ha : a < c) (hb : c < b) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hL : ContDiffOn ℝ ∞ (Function.uncurry gL) (Icc a c ×ˢ V))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry gR) (Icc c b ×ˢ V))
    (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hmapL : MapsTo (fun q : ℝ × E => jet2 (gL q.1) q.2) (Icc a c ×ˢ V) Ω)
    (hmapR : MapsTo (fun q : ℝ × E => jet2 (gR q.1) q.2) (Icc c b ×ˢ V) Ω)
    (hpdeL : ∀ t ∈ Ioo a c, ∀ x ∈ V,
      HasDerivAt (fun u => gL u x) (Φ (jet2 (gL t) x)) t)
    (hpdeR : ∀ t ∈ Ioo c b, ∀ x ∈ V,
      HasDerivAt (fun u => gR u x) (Φ (jet2 (gR t) x)) t)
    (hmatch : EqOn (gL c) (gR c) V) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => if q.1 ≤ c then gL q.1 q.2 else gR q.1 q.2)
      (Icc a b ×ˢ V) := by
  let glued := fun t => if t ≤ c then gL t else gR t
  have hGL (t : ℝ) (ht : t ∈ Icc a c) : ContDiffOn ℝ ∞ (gL t) V :=
    hL.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => ⟨ht, hx⟩)
  have hGR (t : ℝ) (ht : t ∈ Icc c b) : ContDiffOn ℝ ∞ (gR t) V :=
    hR.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => ⟨ht, hx⟩)
  have hmap : MapsTo (fun q : ℝ × E => jet2 (glued q.1) q.2) (Icc a b ×ˢ V) Ω := by
    intro q hq
    by_cases hqc : q.1 ≤ c
    · change jet2 (glued q.1) q.2 ∈ Ω
      rw [show glued q.1 = gL q.1 from ite_eq_left hqc]
      exact hmapL ⟨⟨hq.1.1, hqc⟩, hq.2⟩
    · change jet2 (glued q.1) q.2 ∈ Ω
      rw [show glued q.1 = gR q.1 from ite_eq_right hqc]
      exact hmapR ⟨⟨(lt_of_not_ge hqc).le, hq.1.2⟩, hq.2⟩
  have hGs : ∀ t ∈ Icc a b, ContDiffOn ℝ ∞ (glued t) V := by
    intro t ht
    by_cases htc : t ≤ c
    · change ContDiffOn ℝ ∞ (if t ≤ c then gL t else gR t) V
      rw [ite_eq_left htc]
      exact hGL t ⟨ht.1, htc⟩
    · change ContDiffOn ℝ ∞ (if t ≤ c then gL t else gR t) V
      rw [ite_eq_right htc]
      exact hGR t ⟨(lt_of_not_ge htc).le, ht.2⟩
  have htime : ∀ t ∈ Ioo a b, ∀ x ∈ V,
      HasDerivAt (fun u => glued u x) (Φ (jet2 (glued t) x)) t := by
    intro t ht x hx
    rcases lt_trichotomy t c with htc | heq | hct
    · have heq : (fun u => glued u x) =ᶠ[𝓝 t] (fun u => gL u x) :=
        eventuallyEq_of_mem (Iio_mem_nhds htc) fun u hu => by simp only [glued, ite_eq_left (show u ≤ c from (mem_Iio.mp hu).le)]
      simpa only [glued, ite_eq_left htc.le] using
        (hpdeL t ⟨ht.1, htc⟩ x hx).congr_of_eventuallyEq heq
    · subst t
      have hcL : ContinuousOn (fun u => gL u x) (Icc a c) :=
        hL.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun u hu => ⟨hu, hx⟩)
      have hcR : ContinuousOn (fun u => gR u x) (Icc c b) :=
        hR.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun u hu => ⟨hu, hx⟩)
      have hFL : ContinuousOn (fun u => Φ (jet2 (gL u) x)) (Icc a c) :=
        hΦ.continuousOn.comp (continuousOn_jet2_time ha hV hL hx)
          (fun u hu => hmapL (x := (u, x)) ⟨hu, hx⟩)
      have hFR : ContinuousOn (fun u => Φ (jet2 (gR u) x)) (Icc c b) :=
        hΦ.continuousOn.comp (continuousOn_jet2_time hb hV hR hx)
          (fun u hu => hmapR (x := (u, x)) ⟨hu, hx⟩)
      have hd := Calculus.SmoothExtension.hasDerivAt_ite_of_continuous_derivatives ha hb
        (hcL c ⟨ha.le, le_rfl⟩) (hcR c ⟨le_rfl, hb.le⟩)
        (fun u hu => hpdeL u hu x hx) (fun u hu => hpdeR u hu x hx) (hmatch hx)
        (hFL c ⟨ha.le, le_rfl⟩) (hFR c ⟨le_rfl, hb.le⟩)
        (congrArg Φ (jet2_eq_of_eqOn hV hmatch hx))
      simpa only [glued, ite_apply, ite_eq_left le_rfl] using hd
    · have heq : (fun u => glued u x) =ᶠ[𝓝 t] (fun u => gR u x) :=
        eventuallyEq_of_mem (Ioi_mem_nhds hct) fun u hu => by simp only [glued, ite_eq_right (not_le.mpr (mem_Ioi.mp hu))]
      simpa only [glued, ite_eq_right (not_le.mpr hct)] using
        (hpdeR t ⟨hct, ht.2⟩ x hx).congr_of_eventuallyEq heq
  have hh := contDiffOn_of_closed_jet_pde
    (ha.trans hb) hV hΩ hGs hΦ hmap (continuousOn_spatial_ite ha hb hV hL hR hmatch) htime
  exact hh.congr fun q _ => by
    dsimp only [Function.uncurry, glued]
    split_ifs <;> rfl

omit [CompleteSpace F] in
private theorem iteratedDerivWithin_eq_of_contDiffOn_ite
    {gL gR : ℝ → E → F} {a c b : ℝ} {V : Set E}
    (ha : a < c) (hb : c < b) (hV : IsOpen V)
    (hmatch : EqOn (gL c) (gR c) V)
    (hglue : ContDiffOn ℝ ∞
      (fun q : ℝ × E => if q.1 ≤ c then gL q.1 q.2 else gR q.1 q.2) (Icc a b ×ˢ V))
    (m : ℕ) {x : E} (hx : x ∈ V) :
    iteratedDerivWithin m (fun t => gL t x) (Icc a c) c =
      iteratedDerivWithin m (fun t => gR t x) (Icc c b) c := by
  let f := fun t => if t ≤ c then gL t x else gR t x
  have hfc : ContDiffAt ℝ ∞ f c :=
    (hglue.contDiffAt (prod_mem_nhds (Icc_mem_nhds ha hb) (hV.mem_nhds hx))).comp c
      (contDiffAt_id.prodMk contDiffAt_const)
  have hleft : EqOn f (fun t => gL t x) (Icc a c) := fun t ht => ite_eq_left ht.2
  have hright : EqOn f (fun t => gR t x) (Icc c b) := by
    intro t ht
    by_cases htc : t ≤ c
    · have htEq : t = c := le_antisymm htc ht.1
      subst t
      exact (ite_eq_left le_rfl).trans (hmatch hx)
    · exact ite_eq_right htc
  rw [← iteratedDerivWithin_congr hleft ⟨ha.le, le_rfl⟩,
    ← iteratedDerivWithin_congr hright ⟨le_rfl, hb.le⟩]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ha)
      (hfc.of_le (by exact_mod_cast le_top)) ⟨ha.le, le_rfl⟩,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb)
      (hfc.of_le (by exact_mod_cast le_top)) ⟨le_rfl, hb.le⟩]


theorem iteratedDerivWithin_eq_of_jet_pde
    {gL gR : ℝ → E → F} {a c b : ℝ} {V : Set E}
    {Ω : Set (F × (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F))}
    {Φ : (F × (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)) → F}
    (ha : a < c) (hb : c < b) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hL : ContDiffOn ℝ ∞ (Function.uncurry gL) (Icc a c ×ˢ V))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry gR) (Icc c b ×ˢ V))
    (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hmapL : MapsTo (fun q : ℝ × E => jet2 (gL q.1) q.2) (Icc a c ×ˢ V) Ω)
    (hmapR : MapsTo (fun q : ℝ × E => jet2 (gR q.1) q.2) (Icc c b ×ˢ V) Ω)
    (hpdeL : ∀ t ∈ Ioo a c, ∀ x ∈ V,
      HasDerivAt (fun u => gL u x) (Φ (jet2 (gL t) x)) t)
    (hpdeR : ∀ t ∈ Ioo c b, ∀ x ∈ V,
      HasDerivAt (fun u => gR u x) (Φ (jet2 (gR t) x)) t)
    (hmatch : EqOn (gL c) (gR c) V) (m : ℕ) {x : E} (hx : x ∈ V) :
    iteratedDerivWithin m (fun t => gL t x) (Icc a c) c =
      iteratedDerivWithin m (fun t => gR t x) (Icc c b) c :=
  iteratedDerivWithin_eq_of_contDiffOn_ite ha hb hV hmatch
    (contDiffOn_ite_of_jet_pde ha hb hV hΩ hL hR hΦ hmapL hmapR hpdeL hpdeR hmatch) m hx

end DifferentialGeometry.Analysis
