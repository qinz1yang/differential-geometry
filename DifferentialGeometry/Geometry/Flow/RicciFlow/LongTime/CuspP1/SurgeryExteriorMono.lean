import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorKernel

/-!
# CP1-D8 (G5a): monotonicity of the exterior kernel from local data

Real induction: right-local equality (D7), non-surgery two-sided equality (D7), left inclusion at
surgery times (`hresLeft`), right equality at the boundary time (`hresBoundary`) give
`ker_s ⊆ ker_t` for `E.start ≤ s ≤ t`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem hmono_of_residual_CPD8 {L : LateCutFamily F K slices}
    (hresLeft : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start),
      L.cores.start < τ.1 → ¬ NonSurgeryTime_CPD7 F.observation τ.1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, τ.1 - ε < s.1 → s.1 < τ.1 →
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker ≤
          (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker)
    (hresBoundary : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus),
      ¬ L.cores.start < E.start →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, s.1 < E.start + ε →
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
          (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q E.start le_rfl) x).ker)
    (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
    (q : Fin (E.truncation i).count) (x : Torus) {s t : ℝ} (hs : E.start ≤ s) (hst : s ≤ t) :
    (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s hs) x).ker ≤
      (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q t (hs.trans hst)) x).ker := by
  classical
  let kr : ∀ r : ℝ, E.start ≤ r → Subgroup (FundamentalGroup Torus x) := fun r hr =>
    (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q r hr) x).ker
  let S : Set ℝ := {r | ∀ hr : E.start ≤ r, kr s hs ≤ kr r hr}
  have hcs : L.cores.start ≤ E.start := E.after_cores
  -- extract metric balls from filter statements on the subtype
  have hball : ∀ (τ : Ici E.start) (P' : Ici E.start → Prop), (∀ᶠ r in 𝓝 τ, P' r) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : Ici E.start, |r.1 - τ.1| < ε → P' r := by
    intro τ P' h
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, h⟩ := h
    exact ⟨ε, hε, fun r hr => h (by rw [Subtype.dist_eq, Real.dist_eq]; exact hr)⟩
  -- Claim L: local inclusion into the value at `r > E.start`
  have hL : ∀ (r : Ici E.start), E.start < r.1 → ∃ ε : ℝ, 0 < ε ∧ ∀ r' : Ici E.start,
      |r'.1 - r.1| < ε → kr r'.1 r'.2 ≤ kr r.1 r.2 := by
    intro r hr
    have hcr : L.cores.start < r.1 := lt_of_le_of_lt hcs hr
    by_cases hne : NonSurgeryTime_CPD7 F.observation r.1
    · exact hball r _ ((hlocal_nonSurgery_CPD7 E i q x r hcr hne).mono fun r' h => h.le)
    · obtain ⟨ε₁, hε₁, h₁⟩ := hlocal_right_CPD7 E i q x r hcr
      obtain ⟨ε₂, hε₂, h₂⟩ := hresLeft E i q x r hcr hne
      refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r' hr' => ?_⟩
      rw [abs_lt] at hr'
      rcases le_or_gt r.1 r'.1 with h | h
      · exact (h₁ r' h (by linarith [hr'.2, min_le_left ε₁ ε₂])).le
      · exact h₂ r' (by linarith [hr'.1, min_le_right ε₁ ε₂]) h
  -- Claim R: right equality at every `r ≥ E.start`
  have hR : ∀ (r : Ici E.start), ∃ ε : ℝ, 0 < ε ∧ ∀ r' : Ici E.start, r.1 ≤ r'.1 →
      r'.1 < r.1 + ε → kr r'.1 r'.2 = kr r.1 r.2 := by
    intro r
    by_cases hcr : L.cores.start < r.1
    · exact hlocal_right_CPD7 E i q x r hcr
    · have hr : r.1 = E.start := le_antisymm (by linarith [not_lt.mp hcr, hcs]) r.2
      obtain ⟨ε, hε, h⟩ := hresBoundary E i q x (by intro hlt; exact hcr (by rw [hr]; exact hlt))
      refine ⟨ε, hε, fun r' _ h2 => ?_⟩
      have h3 := h r' (by linarith [h2, hr])
      have e : (⟨E.start, Set.mem_Ici.mpr le_rfl⟩ : Ici E.start) = r := Subtype.ext hr.symm
      have h4 : kr r.1 r.2 = kr E.start le_rfl := by subst e; rfl
      exact h3.trans h4.symm
  have hsS : s ∈ S := fun hr => le_rfl
  have hclosed : IsClosed (S ∩ Icc s t) := by
    refine isClosed_of_closure_subset fun r hr => ?_
    have hrc : r ∈ closure (Icc s t) :=
      closure_mono (inter_subset_right : S ∩ Icc s t ⊆ Icc s t) hr
    have hrI : r ∈ Icc s t := closure_minimal subset_rfl isClosed_Icc hrc
    refine ⟨?_, hrI⟩
    rcases eq_or_lt_of_le hrI.1 with h | h
    · rw [← h]; exact hsS
    · have hEr : E.start < r := lt_of_le_of_lt hs h
      obtain ⟨ε, hε, hLε⟩ := hL ⟨r, hEr.le⟩ hEr
      obtain ⟨r', ⟨hr'S, hr'I⟩, hr'd⟩ := Metric.mem_closure_iff.mp hr ε hε
      intro hrE
      have hr'E : E.start ≤ r' := hs.trans hr'I.1
      have := hLε ⟨r', hr'E⟩ (by rw [← Real.dist_eq]; rw [dist_comm]; exact hr'd)
      exact (hr'S hr'E).trans this
  have hstep : ∀ r ∈ S ∩ Ico s t, S ∈ 𝓝[>] r := by
    rintro r ⟨hrS, hr1, hr2⟩
    have hrE : E.start ≤ r := hs.trans hr1
    obtain ⟨ε, hε, hRε⟩ := hR ⟨r, hrE⟩
    have : Ioo r (r + ε) ⊆ S := by
      intro r' hr' hr'E
      have := hRε ⟨r', hr'E⟩ hr'.1.le hr'.2
      exact (hrS hrE).trans (le_of_eq this.symm)
    exact mem_of_superset (Ioo_mem_nhdsGT (by linarith)) this
  have := hclosed.Icc_subset_of_forall_mem_nhdsWithin hsS hstep
  exact this ⟨hst, le_rfl⟩ (hs.trans hst)

end GC.LongTime.CuspP1
