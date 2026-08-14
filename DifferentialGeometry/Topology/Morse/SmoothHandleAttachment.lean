import DifferentialGeometry.Topology.Morse.ManifoldCellAttachment

namespace DifferentialGeometry.Topology.Morse

open Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Topology.Homotopy
open DifferentialGeometry.Analysis.ODE
open scoped Topology Manifold ContDiff

noncomputable section

namespace ManifoldCellAttachment

open CellAttachment

noncomputable def sublevelCellAdjunctionHomotopyEquivUnderOfMorseChart {n : ℕ} {H : Type}
    [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (data : MorseChart n k hk c I f)
    (g : M → ℝ) (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hg_le : ∀ x : M, g x ≤ f x)
    (hlow : HomotopyEquivUnder
      (X := SublevelSpace f (c - data.ε))
      (Y := SublevelSpace g (c - data.ε))
      (Z := {x : M // x ∈ sublevel f (c - data.ε) ∪ data.χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))))})
      (toBase := sublevelInclusionLE hg_le (c - data.ε))
      (fromBase := sublevelUnionInclusion (c - data.ε) (data.χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)))))))
    (hcell : cellImage hk c data = data.χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)))))
    (hunion_sub : ∀ x : M, x ∈ sublevel f (c - data.ε) ∪ data.χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)))) → g x ≤ c - data.ε)
    (hlow_invFun_val : ∀ z : {x : M // x ∈ sublevel f (c - data.ε) ∪ data.χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))))},
      (hlow.invFun z).1 = z.1)
    (hgup : {x : M | g x ≤ c + data.ε} = sublevel f (c + data.ε))
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ g ⁻¹' Set.Icc (c - data.ε) (c + data.ε),
      (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ∧
      (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ≤ 0) :
    HomotopyEquivUnder
      (X := SublevelSpace f (c - data.ε)) (Y := SublevelSpace f (c + data.ε))
      (Z := CellAdjunctionSpace k (cellAttachingMap hk c data))
      (toBase := sublevelInclusion f (by linarith [data.hεpos]))
      (fromBase := ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data))
        (continuous_adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data))) := by
  let E : Set M := cellImage hk c data
  let φ : C(CellBoundary k, SublevelSpace f (c - data.ε)) := cellAttachingMap hk c data
  let U₀ : Set M := data.χ '' (Set.range (fun z : ClosedCell k =>
    cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))))
  let Z₀ : Type := {x : M // x ∈ sublevel f (c - data.ε) ∪ U₀}
  let Z' : Type := {x : M // x ∈ sublevel f (c - data.ε) ∪ E}
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let T : M → ℝ := fun x => max (g x - (c - data.ε)) 0
  let ι : C(SublevelSpace f (c - data.ε), SublevelSpace f (c + data.ε)) :=
    sublevelInclusion f (by linarith [data.hεpos])
  let j : C(SublevelSpace f (c - data.ε), CellAdjunctionSpace k φ) :=
    ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φ)
      (continuous_adjunctionLower (i := cellBoundaryInclusion k) φ)
  have hup_iff : ∀ x : M, g x ≤ c + data.ε ↔ f x ≤ c + data.ε := by
    intro x
    change (x ∈ {y : M | g y ≤ c + data.ε}) ↔ (x ∈ sublevel f (c + data.ε))
    rw [← hgup]
  have hT_nonneg : ∀ x : M, 0 ≤ T x := by
    intro x
    dsimp [T]
    exact le_max_right (g x - (c - data.ε)) 0
  have hT_zero : ∀ x : M, g x ≤ c - data.ε → T x = 0 := by
    intro x hx
    dsimp [T]
    rw [max_eq_right (by linarith)]
  have hT_pos : ∀ x : M, c - data.ε ≤ g x → T x = g x - (c - data.ε) := by
    intro x hx
    dsimp [T]
    rw [max_eq_left (by linarith)]
  have hretr_mem : ∀ y : SublevelSpace f (c + data.ε),
      g (curveAt v hcomplete y.1 (T y.1)) ≤ c - data.ε := by
    intro y
    by_cases hy : c - data.ε ≤ g y.1
    · let s : ℝ := g y.1 - (c - data.ε)
      have hs : 0 ≤ s := by dsimp [s]; linarith
      have hT : T y.1 = s := by
        rw [hT_pos y.1 hy]
      have hstay : ∀ u ∈ Set.Icc (0 : ℝ) s,
          curveAt v hcomplete y.1 u ∈ g ⁻¹' Set.Icc (c - data.ε) (c + data.ε) := by
        intro u hu
        have hrb := f_rate_bounds_of_integralCurve g hg v hrate
          (hγ := curveAt_integralCurve v hcomplete y.1) (t := u) hu.1
        have hglo : g y.1 - u ≤ g (curveAt v hcomplete y.1 u) := by
          simpa [curveAt_zero v hcomplete y.1] using hrb.1
        have hgup'' : g (curveAt v hcomplete y.1 u) ≤ g y.1 := by
          simpa [curveAt_zero v hcomplete y.1] using hrb.2
        have hgy : g y.1 ≤ c + data.ε := by
          exact le_trans (hg_le y.1) (by change f y.1 ≤ c + data.ε; exact y.2)
        constructor
        · change c - data.ε ≤ g (curveAt v hcomplete y.1 u)
          have hle : c - data.ε ≤ g y.1 - u := by
            have hu2 : u ≤ g y.1 - (c - data.ε) := by simpa [s] using hu.2
            linarith
          exact le_trans hle hglo
        · change g (curveAt v hcomplete y.1 u) ≤ c + data.ε
          exact le_trans hgup'' hgy
      have heq := f_eq_sub_of_integralCurve_on_strip g hg v hdfOn
        (hγ := curveAt_integralCurve v hcomplete y.1) (t := s) hs hstay
      have hval : g (curveAt v hcomplete y.1 s) = c - data.ε := by
        have hmain : g (curveAt v hcomplete y.1 s) = g y.1 - s := by
          simpa [curveAt_zero v hcomplete y.1] using heq
        dsimp [s] at hmain ⊢
        linarith
      rw [hT]
      exact le_of_eq hval
    · have hT : T y.1 = 0 := hT_zero y.1 (le_of_not_ge hy)
      rw [hT, curveAt_zero v hcomplete y.1]
      exact le_of_not_ge hy
  have hTcont : Continuous T := by
    dsimp [T]
    exact continuous_max.comp ((hg.continuous.sub continuous_const).prodMk continuous_const)
  let flowRetract : C(SublevelSpace f (c + data.ε), SublevelSpace g (c - data.ε)) :=
    ContinuousMap.mk
      (fun y => ⟨curveAt v hcomplete y.1 (T y.1), hretr_mem y⟩)
      (by
        have hpair : Continuous (fun y : SublevelSpace f (c + data.ε) => (T y.1, y.1)) :=
          (hTcont.comp continuous_subtype_val).prodMk continuous_subtype_val
        have hmain : Continuous (fun y : SublevelSpace f (c + data.ε) =>
            curveAt v hcomplete y.1 (T y.1)) :=
          (continuous_globalFlow_of_compactSupport v hv hsupp).comp hpair
        exact Continuous.subtype_mk hmain (by intro y; exact hretr_mem y))
  let intoUpper : C(SublevelSpace g (c - data.ε), SublevelSpace f (c + data.ε)) :=
    ContinuousMap.mk
      (fun y => ⟨y.1, (hup_iff y.1).1 (by
        have hy' : g y.1 ≤ c - data.ε := by
          change y.1 ∈ sublevel g (c - data.ε)
          exact y.2
        have hle : g y.1 ≤ c + data.ε := by linarith [data.hεpos]
        exact hle)⟩)
      (by
        exact Continuous.subtype_mk continuous_subtype_val (by
          intro y
          exact (hup_iff y.1).1 (by
            have hy' : g y.1 ≤ c - data.ε := by
              change y.1 ∈ sublevel g (c - data.ε)
              exact y.2
            have hle : g y.1 ≤ c + data.ε := by linarith [data.hεpos]
            exact hle)))
  let hset : sublevel f (c - data.ε) ∪ U₀ = sublevel f (c - data.ε) ∪ E := by
    simp [E, U₀, hcell]
  let hcast : Z₀ ≃ₜ Z' := subtypeSetHomeomorph hset
  let hAdj : CellAdjunctionSpace k φ ≃ₜ Z' := by
    simpa [E, φ] using (cellAdjunctionSpaceHomeomorphLowerUnion (I := I) (hf := hf) (data := data))
  have hAdjLower : ∀ x : SublevelSpace f (c - data.ε),
      hAdj (adjunctionLower (i := cellBoundaryInclusion k) φ x) = ⟨x.1, Or.inl x.2⟩ := by
    intro x
    change adjunctionRealization (sublevel f (c - data.ε)) (cellBoundaryInclusion k)
      (cellEmbedding hk c data)
      (fun b : CellBoundary k => cellAttachingMap hk c data b) (by intro b; rfl)
      (adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data) x) =
      ⟨x.1, Or.inl x.2⟩
    exact adjunctionRealization_lower (i := cellBoundaryInclusion k)
      (c := cellEmbedding hk c data) (by intro b; rfl) x
  let toFun : C(SublevelSpace f (c + data.ε), CellAdjunctionSpace k φ) :=
    ContinuousMap.mk
      (fun y => hAdj.symm (hcast (hlow.toFun (flowRetract y))))
      (by
        exact (hAdj.symm.continuous_toFun.comp (hcast.continuous_toFun.comp
          (hlow.toFun.continuous.comp flowRetract.continuous))))
  let invFun : C(CellAdjunctionSpace k φ, SublevelSpace f (c + data.ε)) :=
    ContinuousMap.mk
      (fun z => intoUpper (hlow.invFun (hcast.symm (hAdj z))))
      (by
        exact (intoUpper.continuous.comp (hlow.invFun.continuous.comp
          (hcast.symm.continuous_toFun.comp hAdj.continuous_toFun))))
  let H₂ : ContinuousMap.HomotopyRel (intoUpper.comp flowRetract)
      (ContinuousMap.id (SublevelSpace f (c + data.ε))) (Set.range ι) := by
    have hGmem : ∀ p : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε),
        f (curveAt v hcomplete p.2.1 (T p.2.1 * (1 - (p.1 : ℝ)))) ≤ c + data.ε := by
      intro p
      have ht : 0 ≤ T p.2.1 * (1 - (p.1 : ℝ)) := by
        exact mul_nonneg (hT_nonneg p.2.1) (sub_nonneg.mpr p.1.2.2)
      have hrb := f_rate_bounds_of_integralCurve g hg v hrate
        (hγ := curveAt_integralCurve v hcomplete p.2.1) (t := T p.2.1 * (1 - (p.1 : ℝ))) ht
      have hgz : g (curveAt v hcomplete p.2.1 (T p.2.1 * (1 - (p.1 : ℝ)))) ≤ g p.2.1 := by
        simpa [curveAt_zero v hcomplete p.2.1] using hrb.2
      have hgy : g p.2.1 ≤ c + data.ε := by
        exact le_trans (hg_le p.2.1) (by change f p.2.1 ≤ c + data.ε; exact p.2.2)
      exact (hup_iff _).1 (le_trans hgz hgy)
    let G : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) → SublevelSpace f (c + data.ε) :=
      fun p => ⟨curveAt v hcomplete p.2.1 (T p.2.1 * (1 - (p.1 : ℝ))), hGmem p⟩
    have hGcont : Continuous G := by
      have hpair : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) =>
          (T p.2.1 * (1 - (p.1 : ℝ)), p.2.1)) := by
        fun_prop
      have hmain : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) =>
          curveAt v hcomplete p.2.1 (T p.2.1 * (1 - (p.1 : ℝ)))) :=
        (continuous_globalFlow_of_compactSupport v hv hsupp).comp hpair
      exact Continuous.subtype_mk hmain (by intro p; exact hGmem p)
    refine { toHomotopy := { toFun := ContinuousMap.mk G hGcont, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }
    · intro y
      apply Subtype.ext
      change curveAt v hcomplete y.1 (T y.1 * (1 - (0 : ℝ))) = curveAt v hcomplete y.1 (T y.1)
      simp
    · intro y
      apply Subtype.ext
      change curveAt v hcomplete y.1 (T y.1 * (1 - (1 : ℝ))) = y.1
      simp [curveAt_zero v hcomplete y.1]
    · intro t x hx
      rcases hx with ⟨y, rfl⟩
      apply Subtype.ext
      have hT0 : T y.1 = 0 := hT_zero y.1 (by
        exact le_trans (hg_le y.1) (by change f y.1 ≤ c - data.ε; exact y.2))
      change curveAt v hcomplete y.1 (T y.1 * (1 - (t : ℝ))) = curveAt v hcomplete y.1 (T y.1)
      simp [hT0, curveAt_zero v hcomplete y.1]
  let H₁ : ContinuousMap.HomotopyRel
      ((intoUpper.comp (hlow.invFun.comp hlow.toFun)).comp flowRetract)
      (intoUpper.comp flowRetract) (Set.range ι) := by
    let P : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) → SublevelSpace f (c + data.ε) :=
      fun p => intoUpper (hlow.left_inv (p.1, flowRetract p.2))
    have hPcont : Continuous P := by
      have hpair : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) =>
          (p.1, flowRetract p.2)) := by
        exact continuous_fst.prodMk (flowRetract.continuous.comp continuous_snd)
      exact intoUpper.continuous.comp (hlow.left_inv.toHomotopy.continuous.comp hpair)
    refine { toHomotopy := { toFun := ContinuousMap.mk P hPcont, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }
    · intro y
      change intoUpper (hlow.left_inv (0, flowRetract y)) =
        intoUpper ((hlow.invFun.comp hlow.toFun) (flowRetract y))
      exact congrArg intoUpper (hlow.left_inv.map_zero_left (flowRetract y))
    · intro y
      change intoUpper (hlow.left_inv (1, flowRetract y)) = intoUpper (flowRetract y)
      exact congrArg intoUpper (hlow.left_inv.map_one_left (flowRetract y))
    · intro t x hx
      rcases hx with ⟨y, rfl⟩
      change intoUpper (hlow.left_inv (t, flowRetract (ι y))) =
        intoUpper ((hlow.invFun.comp hlow.toFun) (flowRetract (ι y)))
      have hfr : flowRetract (ι y) = sublevelInclusionLE hg_le (c - data.ε) y := by
        apply Subtype.ext
        change curveAt v hcomplete y.1 (T y.1) = y.1
        rw [hT_zero y.1 (by
          exact le_trans (hg_le y.1) (by change f y.1 ≤ c - data.ε; exact y.2)),
          curveAt_zero v hcomplete y.1]
      have hz : flowRetract (ι y) ∈ Set.range (sublevelInclusionLE hg_le (c - data.ε)) := by
        rw [hfr]
        exact Set.mem_range.mpr ⟨y, rfl⟩
      exact congrArg intoUpper (hlow.left_inv.prop t (flowRetract (ι y)) hz)
  let L : ContinuousMap.HomotopyRel
      ((intoUpper.comp (hlow.invFun.comp hlow.toFun)).comp flowRetract)
      (ContinuousMap.id (SublevelSpace f (c + data.ε))) (Set.range ι) :=
    H₁.trans H₂
  have h₀ : invFun.comp toFun =
      ((intoUpper.comp (hlow.invFun.comp hlow.toFun)).comp flowRetract) := by
    ext y
    exact congrArg (fun w : SublevelSpace g (c - data.ε) => (w : M)) (congrArg hlow.invFun (by
      calc
        hcast.symm (hAdj (hAdj.symm (hcast (hlow.toFun (flowRetract y))))) =
            hcast.symm (hcast (hlow.toFun (flowRetract y))) := by
          exact congrArg hcast.symm (hAdj.right_inv (hcast (hlow.toFun (flowRetract y))))
        _ = hlow.toFun (flowRetract y) := hcast.left_inv (hlow.toFun (flowRetract y))))
  let H₃ : ContinuousMap.HomotopyRel (toFun.comp invFun)
      (ContinuousMap.id (CellAdjunctionSpace k φ)) (Set.range j) := by
    let Q : (Set.Icc (0 : ℝ) 1) × CellAdjunctionSpace k φ → CellAdjunctionSpace k φ :=
      fun p => hAdj.symm (hcast (hlow.right_inv (p.1, hcast.symm (hAdj p.2))))
    have hQcont : Continuous Q := by
      have hpair : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × CellAdjunctionSpace k φ =>
          (p.1, hcast.symm (hAdj p.2))) := by
        exact continuous_fst.prodMk (hcast.symm.continuous_toFun.comp (hAdj.continuous_toFun.comp continuous_snd))
      exact (hAdj.symm.continuous_toFun.comp (hcast.continuous_toFun.comp
        (hlow.right_inv.toHomotopy.continuous.comp hpair)))
    refine { toHomotopy := { toFun := ContinuousMap.mk Q hQcont, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }
    · intro z
      change hAdj.symm (hcast (hlow.right_inv (0, hcast.symm (hAdj z)))) =
        hAdj.symm (hcast (hlow.toFun (flowRetract (intoUpper (hlow.invFun (hcast.symm (hAdj z)))))))
      have hflowfix : flowRetract (intoUpper (hlow.invFun (hcast.symm (hAdj z)))) =
          hlow.invFun (hcast.symm (hAdj z)) := by
        apply Subtype.ext
        dsimp [flowRetract, intoUpper]
        change curveAt v hcomplete ((hlow.invFun (hcast.symm (hAdj z))).1)
            (T ((hlow.invFun (hcast.symm (hAdj z))).1)) = (hlow.invFun (hcast.symm (hAdj z))).1
        rw [hT_zero ((hlow.invFun (hcast.symm (hAdj z))).1) (hunion_sub ((hlow.invFun (hcast.symm (hAdj z))).1) (by
          rw [hlow_invFun_val (hcast.symm (hAdj z))]
          exact (hcast.symm (hAdj z)).2)),
          curveAt_zero v hcomplete ((hlow.invFun (hcast.symm (hAdj z))).1)]
      calc
        hAdj.symm (hcast (hlow.right_inv (0, hcast.symm (hAdj z)))) =
            hAdj.symm (hcast ((hlow.toFun.comp hlow.invFun) (hcast.symm (hAdj z)))) := by
          exact congrArg (fun w => hAdj.symm (hcast w)) (hlow.right_inv.map_zero_left (hcast.symm (hAdj z)))
        _ = hAdj.symm (hcast (hlow.toFun (hlow.invFun (hcast.symm (hAdj z))))) := rfl
        _ = hAdj.symm (hcast (hlow.toFun (flowRetract
              (intoUpper (hlow.invFun (hcast.symm (hAdj z))))))) := by rw [hflowfix]
        _ = toFun (invFun z) := rfl
    · intro z
      change hAdj.symm (hcast (hlow.right_inv (1, hcast.symm (hAdj z)))) = z
      calc
        hAdj.symm (hcast (hlow.right_inv (1, hcast.symm (hAdj z)))) =
            hAdj.symm (hcast (hcast.symm (hAdj z))) := by
          exact congrArg (fun w => hAdj.symm (hcast w)) (hlow.right_inv.map_one_left (hcast.symm (hAdj z)))
        _ = hAdj.symm (hAdj z) := by
          exact congrArg hAdj.symm (hcast.right_inv (hAdj z))
        _ = z := hAdj.left_inv z
    · intro t z hz
      rcases hz with ⟨x, rfl⟩
      change hAdj.symm (hcast (hlow.right_inv (t, hcast.symm (hAdj (j x))))) =
        hAdj.symm (hcast (hlow.toFun (flowRetract (intoUpper (hlow.invFun (hcast.symm (hAdj (j x))))))))
      have hz₀ : hcast.symm (hAdj (j x)) = sublevelUnionInclusion (c - data.ε) U₀ x := by
        apply Subtype.ext
        change (hAdj (j x)).1 = x.1
        simpa [j] using congrArg Subtype.val (hAdjLower x)
      have hrel : hlow.right_inv (t, hcast.symm (hAdj (j x))) =
          (hlow.toFun.comp hlow.invFun) (hcast.symm (hAdj (j x))) := by
        have hmem : hcast.symm (hAdj (j x)) ∈ Set.range (sublevelUnionInclusion (c - data.ε) U₀) := by
          rw [hz₀]
          exact Set.mem_range.mpr ⟨x, rfl⟩
        exact hlow.right_inv.prop t (hcast.symm (hAdj (j x))) hmem
      have hflowfix : flowRetract (intoUpper (hlow.invFun (hcast.symm (hAdj (j x))))) =
          hlow.invFun (hcast.symm (hAdj (j x))) := by
        apply Subtype.ext
        dsimp [flowRetract, intoUpper]
        change curveAt v hcomplete ((hlow.invFun (hcast.symm (hAdj (j x)))).1)
            (T ((hlow.invFun (hcast.symm (hAdj (j x)))).1)) = (hlow.invFun (hcast.symm (hAdj (j x)))).1
        rw [hT_zero ((hlow.invFun (hcast.symm (hAdj (j x)))).1) (hunion_sub ((hlow.invFun (hcast.symm (hAdj (j x)))).1) (by
          rw [hlow_invFun_val (hcast.symm (hAdj (j x)))]
          exact (hcast.symm (hAdj (j x))).2)),
          curveAt_zero v hcomplete ((hlow.invFun (hcast.symm (hAdj (j x)))).1)]
      calc
        hAdj.symm (hcast (hlow.right_inv (t, hcast.symm (hAdj (j x))))) =
            hAdj.symm (hcast ((hlow.toFun.comp hlow.invFun) (hcast.symm (hAdj (j x))))) := by
          exact congrArg (fun w => hAdj.symm (hcast w)) hrel
        _ = hAdj.symm (hcast (hlow.toFun (hlow.invFun (hcast.symm (hAdj (j x)))))) := rfl
        _ = hAdj.symm (hcast (hlow.toFun (flowRetract
              (intoUpper (hlow.invFun (hcast.symm (hAdj (j x)))))))) := by rw [hflowfix]
        _ = toFun (invFun (j x)) := rfl
  exact
    { toFun := toFun
      invFun := invFun
      map_toBase := by
        ext x
        calc
          toFun (ι x) = hAdj.symm (hcast (hlow.toFun (flowRetract (ι x)))) := rfl
          _ = hAdj.symm (hcast (hlow.toFun (sublevelInclusionLE hg_le (c - data.ε) x))) := by
            exact congrArg (fun w => hAdj.symm (hcast (hlow.toFun w))) (by
              apply Subtype.ext
              dsimp [flowRetract, sublevelInclusionLE, ι]
              change curveAt v hcomplete x.1 (T x.1) = x.1
              rw [hT_zero x.1 (by
                exact le_trans (hg_le x.1) (by change f x.1 ≤ c - data.ε; exact x.2)),
                curveAt_zero v hcomplete x.1])
          _ = hAdj.symm (hcast (sublevelUnionInclusion (c - data.ε) U₀ x)) := by
            exact congrArg (fun w => hAdj.symm (hcast w)) (hlow.map_toBase_apply x)
          _ = hAdj.symm (⟨x.1, Or.inl x.2⟩ : Z') := by
            exact congrArg hAdj.symm (by
              apply Subtype.ext
              rfl)
          _ = j x := by
            have hh0 : hAdj.symm (⟨x.1, Or.inl x.2⟩ : Z') = j x := by
              have h := hAdj.left_inv (j x)
              rw [show hAdj.toFun (j x) = (⟨x.1, Or.inl x.2⟩ : Z') from by simpa [j] using hAdjLower x] at h
              exact h
            exact hh0
      map_fromBase := by
        ext x
        exact congrArg Subtype.val (by
          calc
            invFun (j x) = intoUpper (hlow.invFun (hcast.symm (hAdj (j x)))) := rfl
            _ = intoUpper (hlow.invFun (hcast.symm (⟨x.1, Or.inl x.2⟩ : Z'))) := by
              exact congrArg (fun w => intoUpper (hlow.invFun (hcast.symm w))) (hAdjLower x)
            _ = intoUpper (hlow.invFun (sublevelUnionInclusion (c - data.ε) U₀ x)) := by
              exact congrArg (fun w => intoUpper (hlow.invFun w)) (by
                apply Subtype.ext
                rfl)
            _ = intoUpper (sublevelInclusionLE hg_le (c - data.ε) x) := by
              exact congrArg intoUpper (hlow.map_fromBase_apply x)
            _ = ι x := by
              exact Subtype.ext (by rfl))
      left_inv := L.cast h₀.symm rfl
      right_inv := H₃ }

theorem sublevelTransport_diffeomorph_of_setImage {m : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g f : M → ℝ) (a b : ℝ)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg_g : ∀ x : M, g x = a → ¬ IsCriticalPointAt I g x)
    (hreg_f : ∀ x : M, f x = b → ¬ IsCriticalPointAt I f x)
    (Φ : Diffeomorph I I M M (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (htransport : Φ.toEquiv '' sublevel g a = sublevel f b)
    (hbnd : ∀ x : M, g x = a → f (Φ x) = b)
    (hstrict : ∀ x : M, g x < a → f (Φ x) < b)
    (hbnd' : ∀ x : M, f x = b → g (Φ.symm x) = a)
    (hstrict' : ∀ x : M, f x < b → g (Φ.symm x) < a) :
    Nonempty (@Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace g a) _ (manifoldSublevelChartedSpace I g a hg hreg_g)
      (SublevelSpace f b) _ (manifoldSublevelChartedSpace I f b hf hreg_f)
      (⊤ : ℕ∞)) := by
  have hmap : ∀ x : M, g x ≤ a → f (Φ x) ≤ b := by
    intro x hx
    have hmem : Φ x ∈ sublevel f b := by
      rw [← htransport]
      exact ⟨x, hx, rfl⟩
    exact hmem
  have hmap' : ∀ x : M, f x ≤ b → g (Φ.symm x) ≤ a := by
    intro x hx
    have himg : Φ.symm '' sublevel f b = sublevel g a := by
      have h := congrArg (fun s : Set M => Φ.toEquiv.symm '' s) htransport
      simpa using h.symm
    have hmem : Φ.symm x ∈ sublevel g a := by
      rw [← himg]
      exact ⟨x, hx, rfl⟩
    exact hmem
  exact manifoldSublevelDiffeomorphOfDiffeomorph (I := I) g f a b hg hf hreg_g hreg_f Φ
    hmap hbnd hstrict hmap' hbnd' hstrict'

private theorem morse_smooth_handle_attachment_relative {m : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ m + 1)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c)
    (a : ℝ) (ha : 0 < a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ _ : ε ≤ a,
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g,
      (∀ x : M, g x ≤ f x) ∧
      ({x : M | g x ≤ c + ε} = sublevel f (c + ε)) ∧
      (∀ x : M, f x ≤ c - ε → g x ≤ c - ε) ∧
      ∃ v : (x : M) → TangentSpace I x,
        ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) ∧
        IsCompact (tsupport v) ∧
        (∀ x ∈ g ⁻¹' Set.Icc (c - ε) (c + ε),
          (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) = -1) ∧
        (∀ x,
          -1 ≤ (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ∧
          (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ≤ 0) ∧
        ∃ Φ : Diffeomorph I I M M (↑(⊤ : ℕ∞) : WithTop ℕ∞),
          Φ.toEquiv '' sublevel g (c - ε) = sublevel f (c + ε) ∧
          (∀ x : M, x ∉ tsupport v → Φ.toEquiv x = x) ∧
          (∃ η : ℝ, 0 < η ∧ ∀ x : M, g x ≤ c - ε - η → Φ.toEquiv x = x) ∧
          ∃ r : ℝ, ∃ hr : r ≠ 0, ∃ _ : r ^ 2 = 2 * ε,
          ∃ δ₁ : ℝ, ∃ hδ₁₀ : 0 < δ₁, ∃ hδ₁r : δ₁ < r ^ 2,
          ∃ φ : AttachingRegion k (m + 1 - k) → SublevelSpace f (c - ε),
            (∀ p : AttachingRegion k (m + 1 - k), f (φ p).1 = c - ε) ∧
            Function.Injective φ ∧
            Topology.IsClosedEmbedding φ ∧
            (∀ hk0 : NeZero k, ∀ hl0 : NeZero (m + 1 - k),
              ∃ hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x,
                ∃ φ₀ : AttachingRegion k (m + 1 - k) → LevelSetSpace f (c - ε),
                  @ContMDiff ℝ _
                    (EuclideanSpace ℝ (Fin (k - 1)) ×
                      EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) _ _
                    (ModelProd (EuclideanSpace ℝ (Fin (k - 1)))
                      (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
                    ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
                    (AttachingRegion k (m + 1 - k)) _ (attachingRegionChartedSpace k (m + 1 - k))
                    (MorseModel m) _ _ (MorseModel m) _
                    (𝓘(ℝ, MorseModel m)) (LevelSetSpace f (c - ε)) _
                    (manifoldLevelSetChartedSpace I f (c - ε) (hf.of_le le_top) hreg_f)
                    (⊤ : ℕ∞)
                    φ₀ ∧
                  Topology.IsClosedEmbedding φ₀ ∧
                  ∀ p : AttachingRegion k (m + 1 - k), (φ₀ p).1 = (φ p).1) ∧
            @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
              (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
              (morseAttachedSpace hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr) _
              (morseAttachedChartedSpace hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr) ∧
            ∃ Ψ : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
              (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
              (morseModelWithCornersHalfSpace m)
              (morseAttachedSpace hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr) _
              (morseAttachedChartedSpace hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr)
              (morseUpperSublevel hk c r) _ (morseUpperChartedSpace hk c r hr)
              (⊤ : ℕ∞),
              morseAttachedDiffeomorphRelative hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr
                (Ψ := Ψ) ∧
            ∃ φc : C(CellBoundary k, SublevelSpace f (c - ε)),
                Nonempty (HomotopyEquivUnder
                  (X := SublevelSpace f (c - ε)) (Y := SublevelSpace f (c + ε))
                  (Z := CellAdjunctionSpace k φc)
                  (toBase := sublevelInclusion f (by linarith [hε]))
                  (fromBase := ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φc)
                    (continuous_adjunctionLower (i := cellBoundaryInclusion k) φc))) := by
  rcases morse_lemma I f hf p k hk hnd hindex with
    ⟨R, hRpos, χ, hχ0src, hχ0tgt, hχ0val, hχsrc, hnorm0, hχmd, hχsmd,
      R', hR'pos, hχon, hχsymmOn⟩
  have hnorm : ∀ y : MorseModel (m + 1), morseNorm (m + 1) y ≤ R → f (χ y) = morseNormalForm hk c y := by
    intro y hy
    rw [← hfp]
    exact hnorm0 y hy
  let ε₀ : ℝ := min a (min (R ^ 2) (R' ^ 2)) / 16
  let δ₀ : ℝ := Real.sqrt ε₀ / 4
  have hminpos : 0 < min a (min (R ^ 2) (R' ^ 2)) := by
    exact lt_min ha (lt_min (sq_pos_of_pos hRpos) (sq_pos_of_pos hR'pos))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    have hsqrt : 0 < Real.sqrt ε₀ := Real.sqrt_pos.2 hε₀
    nlinarith
  have hεa : ε₀ ≤ a := by
    dsimp [ε₀]
    have h1 : min a (min (R ^ 2) (R' ^ 2)) / 16 ≤ min a (min (R ^ 2) (R' ^ 2)) := by
      exact div_le_self (le_of_lt hminpos) (by norm_num : (1 : ℝ) ≤ 16)
    exact le_trans h1 (min_le_left a (min (R ^ 2) (R' ^ 2)))
  have hεmin : ε₀ ≤ min (R ^ 2) (R' ^ 2) / 16 := by
    dsimp [ε₀]
    have hle := min_le_right a (min (R ^ 2) (R' ^ 2))
    have hdiv : min a (min (R ^ 2) (R' ^ 2)) / 16 ≤ min (R ^ 2) (R' ^ 2) / 16 := by
      exact div_le_div_of_nonneg_right hle (by norm_num : (0 : ℝ) ≤ 16)
    exact hdiv
  have hsqδ : δ₀ ^ 2 = ε₀ / 16 := by
    dsimp [δ₀]
    rw [div_pow]
    rw [Real.sq_sqrt (le_of_lt hε₀)]
    ring
  have hR' : 4 * ε₀ + 9 * δ₀ ^ 2 / 4 < R ^ 2 := by
    rw [hsqδ]
    have hbound : 4 * ε₀ + 9 * (ε₀ / 16) / 4 ≤ 265 * (min (R ^ 2) (R' ^ 2) / 16) / 64 := by
      nlinarith [hεmin]
    have h265 : 265 * (min (R ^ 2) (R' ^ 2) / 16) / 64 < R ^ 2 := by
      have h1 : min (R ^ 2) (R' ^ 2) ≤ R ^ 2 := min_le_left (R ^ 2) (R' ^ 2)
      nlinarith [h1, sq_pos_of_pos hRpos]
    exact lt_of_le_of_lt hbound h265
  have hΦr : 4 * ε₀ + 9 * δ₀ ^ 2 / 4 < R' ^ 2 := by
    rw [hsqδ]
    have hbound : 4 * ε₀ + 9 * (ε₀ / 16) / 4 ≤ 265 * (min (R ^ 2) (R' ^ 2) / 16) / 64 := by
      nlinarith [hεmin]
    have h265 : 265 * (min (R ^ 2) (R' ^ 2) / 16) / 64 < R' ^ 2 := by
      have h1 : min (R ^ 2) (R' ^ 2) ≤ R' ^ 2 := min_le_right (R ^ 2) (R' ^ 2)
      nlinarith [h1, sq_pos_of_pos hR'pos]
    exact lt_of_le_of_lt hbound h265
  have hδε : 9 * δ₀ ^ 2 < 4 * ε₀ := by
    rw [hsqδ]
    nlinarith [hε₀]
  have hεR : Real.sqrt (2 * ε₀) ≤ R := by
    have hsq : (Real.sqrt (2 * ε₀)) ^ 2 ≤ R ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε₀)]
      have hle : 2 * ε₀ ≤ R ^ 2 := by
        have h1 : ε₀ ≤ R ^ 2 / 16 := le_trans hεmin (by
          have hle' := min_le_left (R ^ 2) (R' ^ 2)
          nlinarith)
        nlinarith [h1]
      nlinarith [hle]
    have hnonneg : 0 ≤ Real.sqrt (2 * ε₀) := Real.sqrt_nonneg _
    have habs := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hnonneg, abs_of_nonneg (le_of_lt hRpos)] at habs
  let g : M → ℝ := morseModifiedFunction (M := M) hk c ε₀ δ₀ R χ f
  have hgmd : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g := by
    dsimp [g]
    exact contMDiff_morseModifiedFunction (H := H) (M := M) hk c ε₀ δ₀ R R' hε₀ hδ₀
      hR' hΦr hRpos hR'pos I f hf χ hnorm hχsrc hχsymmOn
  have hg : Continuous g := hgmd.continuous
  have hg_le : ∀ x : M, g x ≤ f x := by
    intro x
    dsimp [g]
    exact morseModifiedFunction_le_f (M := M) hk c ε₀ δ₀ R hε₀ χ f hnorm x
  have hgup : {x : M | g x ≤ c + ε₀} = sublevel f (c + ε₀) := by
    dsimp [g]
    exact sublevel_upper_identity_morseModifiedFunction (M := M) hk c ε₀ δ₀ R hε₀ hδ₀
      hδε χ f hnorm
  have hcompactG : IsCompact (g ⁻¹' Set.Icc (c - ε₀) (c + ε₀)) := by
    dsimp [g]
    exact isCompact_strip_morseModifiedFunction (M := M) hk c ε₀ δ₀ R a hε₀ hδ₀ hδε hεa
      χ f hf.continuous hnorm hg hcompact
  have hregularG : ∀ x : M, x ∈ g ⁻¹' Set.Icc (c - ε₀) (c + ε₀) →
      ¬ IsCriticalPointAt I g x := by
    intro x hx
    dsimp [g] at hx ⊢
    exact no_critical_point_morseModifiedFunction (H := H) (M := M) hk c ε₀ δ₀ R R' a hε₀ hδ₀ hδε
      hR' hΦr hRpos hR'pos hεa I f p χ hχ0val hnorm hχsrc hχsymmOn hχon hunique hx
  have hreg_low : ∀ x : M, g x = c - ε₀ → ¬ IsCriticalPointAt I g x := by
    intro x hx
    exact hregularG x (by
      change g x ∈ Set.Icc (c - ε₀) (c + ε₀)
      exact ⟨le_of_eq hx.symm, by linarith⟩)
  have hreg_up : ∀ x : M, g x = c + ε₀ → ¬ IsCriticalPointAt I g x := by
    intro x hx
    exact hregularG x (by
      change g x ∈ Set.Icc (c - ε₀) (c + ε₀)
      exact ⟨by linarith, le_of_eq hx⟩)
  rcases no_critical_value_transport (I := I) (f := g) hgmd (by linarith : c - ε₀ ≤ c + ε₀)
      hcompactG hregularG with
    ⟨v, Φ, hv, hsupp, hdfOn, hrate, ⟨hcomplete, htransport, htie⟩,
      hbnd, hstrict, hbnd', hstrict'⟩
  have hdiff : Nonempty (@Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace g (c - ε₀)) _ (manifoldSublevelChartedSpace I g (c - ε₀) hgmd hreg_low)
      (SublevelSpace g (c + ε₀)) _ (manifoldSublevelChartedSpace I g (c + ε₀) hgmd hreg_up)
      (⊤ : ℕ∞)) :=
    sublevelTransport_diffeomorph_of_setImage (I := I) g g (c - ε₀) (c + ε₀) hgmd hgmd
      hreg_low hreg_up Φ htransport hbnd hstrict hbnd' hstrict'
  rcases hdiff with ⟨Θ⟩
  let r₀ : ℝ := Real.sqrt (2 * ε₀)
  let δ₁ : ℝ := 3 * ε₀ / 2
  have hr₀ : r₀ ≠ 0 := by
    dsimp [r₀]
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < 2 * ε₀))
  have hr₀sq : r₀ ^ 2 = 2 * ε₀ := by
    dsimp [r₀]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε₀)]
  have hδ₁₀ : 0 < δ₁ := by
    dsimp [δ₁]
    positivity
  have hδ₁r : δ₁ < r₀ ^ 2 := by
    rw [hr₀sq]
    dsimp [δ₁]
    nlinarith [hε₀]
  have hεr₀ : Real.sqrt (2 * ε₀ + 2 * r₀ ^ 2) ≤ R := by
    rw [hr₀sq]
    have hsix : 2 * ε₀ + 2 * (2 * ε₀) = 6 * ε₀ := by ring
    rw [hsix]
    have hsq : (Real.sqrt (6 * ε₀)) ^ 2 ≤ R ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 6 * ε₀)]
      have h1 : ε₀ ≤ R ^ 2 / 16 := le_trans hεmin (by
        have hle' := min_le_left (R ^ 2) (R' ^ 2)
        nlinarith)
      nlinarith [h1]
    exact le_of_sq_le_sq hsq (le_of_lt hRpos)
  let data : MorseChart (m + 1) k hk c I f :=
    { p := p, R := R, R' := R', ε := ε₀, χ := χ, hχ0 := hχ0val, hRpos := hRpos,
      hR'pos := hR'pos, hεpos := hε₀, hεR := hεR, hnorm := hnorm, hχsrc := hχsrc,
      hχon := hχon, hχsymmOn := hχsymmOn }
  let φ : AttachingRegion k (m + 1 - k) → SublevelSpace f (c - ε₀) :=
    fun p => ⟨(cocoreAttachingEmbedding hk c ε₀ r₀ data hε₀ hεr₀ p).1,
      le_of_eq (cocoreAttachingEmbedding_value hk c ε₀ r₀ data hε₀ hεr₀ p)⟩
  have hφ_boundary : ∀ p : AttachingRegion k (m + 1 - k), f (φ p).1 = c - ε₀ := by
    intro p
    dsimp [φ]
    exact cocoreAttachingEmbedding_value hk c ε₀ r₀ data hε₀ hεr₀ p
  have hφ_inj : Function.Injective φ := by
    intro p q h
    have h' : (cocoreAttachingEmbedding hk c ε₀ r₀ data hε₀ hεr₀ p).1 =
        (cocoreAttachingEmbedding hk c ε₀ r₀ data hε₀ hεr₀ q).1 := by
      change (φ p).1 = (φ q).1
      exact congrArg Subtype.val h
    exact cocoreAttachingEmbedding_injective hk c ε₀ r₀ data hε₀ hr₀ hεr₀
      (Subtype.ext h')
  have hcontModel : Continuous (fun p : AttachingRegion k (m + 1 - k) =>
      (cocoreModelPoint hk ε₀ r₀ p : MorseModel (m + 1))) := by
    have hrew : (fun p : AttachingRegion k (m + 1 - k) =>
        (cocoreModelPoint hk ε₀ r₀ p : MorseModel (m + 1))) =
        fun p : AttachingRegion k (m + 1 - k) =>
          recombine hk
            ((Real.sqrt (2 * ε₀ + r₀ ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2)) •
              (p.1 : EuclideanSpace ℝ (Fin k)))
            (r₀ • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))) := by
      funext p
      dsimp [cocoreModelPoint]
      rw [negPart_cellMap_smul hk]
    rw [hrew]
    have hpair : Continuous (fun p : AttachingRegion k (m + 1 - k) =>
        ((Real.sqrt (2 * ε₀ + r₀ ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2)) •
          (p.1 : EuclideanSpace ℝ (Fin k)),
         r₀ • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))) := by
      fun_prop
    exact continuous_recombine hk |>.comp hpair
  have hφ_cont : Continuous φ := by
    have hχon : ContinuousOn χ (Set.range (fun p : AttachingRegion k (m + 1 - k) =>
        cocoreModelPoint hk ε₀ r₀ p)) := by
      refine χ.continuousOn_toFun.mono ?_
      intro y hy
      rcases hy with ⟨p, hp⟩
      rw [← hp]
      exact data.hχsrc (cocoreModelPoint hk ε₀ r₀ p)
        (le_trans (cocoreModelPoint_norm_le hk ε₀ r₀ (le_of_lt hε₀) p) hεr₀)
    have hmap : Set.MapsTo (fun p : AttachingRegion k (m + 1 - k) =>
        cocoreModelPoint hk ε₀ r₀ p) Set.univ
        (Set.range (fun p : AttachingRegion k (m + 1 - k) => cocoreModelPoint hk ε₀ r₀ p)) := by
      intro p hp
      exact Set.mem_range_self p
    have hmain : Continuous (fun p : AttachingRegion k (m + 1 - k) =>
        data.χ (cocoreModelPoint hk ε₀ r₀ p)) := by
      have hstep := ContinuousOn.comp' hχon hcontModel.continuousOn hmap
      exact (continuousOn_univ.mp hstep)
    exact Continuous.subtype_mk hmain (by
      intro p
      exact le_of_eq (cocoreAttachingEmbedding_value hk c ε₀ r₀ data hε₀ hεr₀ p))
  have hφ_closed : Topology.IsClosedEmbedding φ := by
    letI : CompactSpace (AttachingRegion k (m + 1 - k)) := inferInstance
    letI : T2Space (SublevelSpace f (c - ε₀)) := inferInstance
    exact hφ_cont.isClosedEmbedding hφ_inj
  let Ψ : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (morseAttachedSpace hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀) _
      (morseAttachedChartedSpace hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀)
      (morseUpperSublevel hk c r₀) _ (morseUpperChartedSpace hk c r₀ hr₀)
      (⊤ : ℕ∞) :=
    morseAttachedDiffeomorphUpper hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀
  have hrelative : morseAttachedDiffeomorphRelative hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀
      (Ψ := Ψ) := by
    dsimp [morseAttachedDiffeomorphRelative]
    constructor
    · intro a
      change morseAttachedToUpper hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀
        (DifferentialGeometry.Topology.adjunctionCell
          (i := fun a : morseLowerSublevel hk c ε₀ => a)
          (morseHandleGlueMap hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀) a) =
        (⟨a.1, morseLowerSublevel_mem_upper hk c ε₀ r₀ (le_of_lt hε₀) a⟩ :
          morseUpperSublevel hk c r₀)
      exact morseAttachedToUpper_lower hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀ a
    · intro p
      change morseAttachedToUpper hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀
        (morseHandleEmbeddingAttached hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀ p) =
        (⟨CellAttachment.modelHandleMap hk ε₀ r₀ p,
          CellAttachment.modelHandleMap_mem_upper hk c ε₀ r₀ (le_of_lt hε₀) p⟩ :
          morseUpperSublevel hk c r₀)
      exact morseAttachedToUpper_handleEmbedding hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀ p
  have hmin : ∃ m : ℝ, ∀ x ∈ tsupport v, m ≤ g x := by
    by_cases hS : (tsupport v).Nonempty
    · rcases hsupp.exists_isMinOn hS hg.continuousOn with ⟨x₀, hx₀, hmin⟩
      exact ⟨g x₀, hmin⟩
    · exact ⟨c - ε₀, by intro x hx; exact False.elim (hS ⟨x, hx⟩)⟩
  rcases hmin with ⟨m, hgm⟩
  let η : ℝ := max (c - ε₀ - m) 0 + 1
  have hηpos : 0 < η := by
    have h : 0 ≤ max (c - ε₀ - m) 0 := le_max_right (c - ε₀ - m) 0
    dsimp [η]
    linarith
  have hηmain : ∀ x : M, g x ≤ c - ε₀ - η → Φ.toEquiv x = x := by
    intro x hx
    have hnot : x ∉ tsupport v := by
      intro hxv
      have hle : m ≤ g x := hgm x hxv
      have hlt : c - ε₀ - η < m := by
        dsimp [η]
        by_cases hm : c - ε₀ - m ≤ 0
        · have hmax : max (c - ε₀ - m) 0 = 0 := by
            rw [max_eq_right hm]
          rw [hmax]
          linarith
        · have hmax : max (c - ε₀ - m) 0 = c - ε₀ - m := by
            rw [max_eq_left (le_of_not_ge hm)]
          rw [hmax]
          linarith
      exact (not_lt_of_ge hle) (lt_of_le_of_lt hx hlt)
    have hflow : curveAt v hcomplete x ((c - ε₀) - (c + ε₀)) = x := by
      exact curveAt_eq_self_of_not_mem_tsupport v hv hcomplete hnot _
    exact (htie x).trans hflow
  let hlow0 : HomotopyEquivUnder
      (X := SublevelSpace f (c - ε₀))
      (Y := SublevelSpace g (c - ε₀))
      (Z := {x : M // x ∈ sublevel f (c - ε₀) ∪ χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k))))})
      (toBase := sublevelInclusionLE hg_le (c - ε₀))
      (fromBase := sublevelUnionInclusion (c - ε₀) (χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))))) :=
    morseModifiedLowerSublevelHomotopyEquivUnder (M := M) hk c ε₀ δ₀ R hε₀ hδ₀ hR'
      hRpos hεR χ f hg hnorm hχsrc
  have hcell : cellImage hk c data = χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))) := by
    change Set.range (fun z : ClosedCell k =>
        χ (cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))) =
      χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k))))
    exact Set.range_comp (g := fun y => χ y)
      (f := fun z : ClosedCell k => cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))
  have hunion_sub : ∀ x : M, x ∈ sublevel f (c - ε₀) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))) → g x ≤ c - ε₀ := by
    intro x hx
    change g x ≤ c - ε₀
    dsimp [g]
    exact lowerUnionCellImage_subset_modifiedSublevel (M := M) hk c ε₀ δ₀ R hε₀ hδ₀ hεR
      χ f hnorm hχsrc hx
  have hlow_invFun_val : ∀ z : {x : M // x ∈ sublevel f (c - ε₀) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k))))}, (hlow0.invFun z).1 = z.1 := by
    intro z
    rfl
  have hcelladj : Nonempty (HomotopyEquivUnder
      (X := SublevelSpace f (c - ε₀)) (Y := SublevelSpace f (c + ε₀))
      (Z := CellAdjunctionSpace k (cellAttachingMap hk c data))
      (toBase := sublevelInclusion f (by linarith [hε₀]))
      (fromBase := ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k)
        (cellAttachingMap hk c data))
        (continuous_adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data)))) :=
    ⟨sublevelCellAdjunctionHomotopyEquivUnderOfMorseChart (I := I) (hf := hf)
      (f := f) (c := c) (k := k) (hk := hk) (data := data) (g := g) hgmd hg_le hlow0 hcell hunion_sub
      hlow_invFun_val hgup v hv hsupp hdfOn hrate⟩
  refine ⟨ε₀, hε₀, hεa, g, hgmd, hg_le, ?_, ?_, v, hv, hsupp, ?_, hrate, Φ, ?_, ?_, ⟨η, hηpos, hηmain⟩,
    r₀, hr₀, hr₀sq, δ₁, hδ₁₀, hδ₁r, φ, hφ_boundary, hφ_inj, hφ_closed,
    (by
      intro hk0 hl0
      letI := hk0
      letI := hl0
      have hεr₀' : Real.sqrt (2 * ε₀ + 2 * r₀ ^ 2) < data.R' := by
        rw [hr₀sq]
        have hsix : 2 * ε₀ + 2 * (2 * ε₀) = 6 * ε₀ := by ring
        rw [hsix]
        have hsq : (Real.sqrt (6 * ε₀)) ^ 2 < data.R' ^ 2 := by
          rw [Real.sq_sqrt (by positivity : 0 ≤ 6 * ε₀)]
          have h1 : ε₀ ≤ R' ^ 2 / 16 := le_trans hεmin (by
            have hle' := min_le_right (R ^ 2) (R' ^ 2)
            nlinarith)
          nlinarith [h1, sq_pos_of_pos hR'pos]
        have hlt : |Real.sqrt (6 * ε₀)| < data.R' :=
          abs_lt_of_sq_lt_sq hsq (le_of_lt hR'pos)
        have hnonneg : 0 ≤ Real.sqrt (6 * ε₀) := Real.sqrt_nonneg _
        rwa [abs_of_nonneg hnonneg] at hlt
      have hreg_f : ∀ x : M, f x = c - ε₀ → ¬ IsCriticalPointAt I f x := by
        intro x hx
        rcases hunique x (by
          rw [hx]
          constructor <;> linarith [hεa]) with hxp | hcrit
        · exfalso
          have hc' : f x = c := by rw [hxp, hfp]
          linarith
        · exact hcrit
      rcases morse_smooth_handle_attachment_cell hk c ε₀ r₀ I f data hε₀ hr₀ hεr₀ hεr₀'
        (hf.of_le le_top) hreg_f with
        ⟨φ₀, hφ₀md, hφ₀cl, hφ₀rel⟩
      exact ⟨hreg_f, φ₀, hφ₀md, hφ₀cl, fun p => by
        have hrel := hφ₀rel p
        change (φ₀ p).1 = (φ p).1
        rw [hrel]⟩),
    (morseAttachedIsManifold hk c ε₀ r₀ δ₁ (le_of_lt hε₀) hδ₁₀ hδ₁r hr₀), Ψ, hrelative,
    ⟨cellAttachingMap hk c data, hcelladj⟩⟩
  · exact hgup
  · intro x hx
    exact le_trans (hg_le x) hx
  · intro x hx
    exact hdfOn x hx
  · exact htransport.trans hgup
  · intro x hx
    have hflow : curveAt v hcomplete x ((c - ε₀) - (c + ε₀)) = x := by
      exact curveAt_eq_self_of_not_mem_tsupport v hv hcomplete hx _
    exact (htie x).trans hflow

private theorem morse_smooth_handle_attachment_relative_natural {m : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ m + 1)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c)
    (a : ℝ) (ha : 0 < a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ _ : ε ≤ a,
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g,
      (∀ x : M, g x ≤ f x) ∧
      ({x : M | g x ≤ c + ε} = sublevel f (c + ε)) ∧
      (∀ x : M, f x ≤ c - ε → g x ≤ c - ε) ∧
      ∃ v : (x : M) → TangentSpace I x,
        ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) ∧
        IsCompact (tsupport v) ∧
        (∀ x ∈ g ⁻¹' Set.Icc (c - ε) (c + ε),
          (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) = -1) ∧
        (∀ x,
          -1 ≤ (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ∧
          (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ≤ 0) ∧
        ∃ Φ : Diffeomorph I I M M (↑(⊤ : ℕ∞) : WithTop ℕ∞),
          Φ.toEquiv '' sublevel g (c - ε) = sublevel f (c + ε) ∧
          (∀ x : M, x ∉ tsupport v → Φ.toEquiv x = x) ∧
          (∃ η : ℝ, 0 < η ∧ ∀ x : M, g x ≤ c - ε - η → Φ.toEquiv x = x) ∧
          ∃ r : ℝ, ∃ hr : r ≠ 0, ∃ _ : r ^ 2 = 2 * ε,
          ∃ δ₁ : ℝ, ∃ hδ₁₀ : 0 < δ₁, ∃ hδ₁r : δ₁ < r ^ 2,
          ∃ φ : AttachingRegion k (m + 1 - k) → SublevelSpace f (c - ε),
            (∀ p : AttachingRegion k (m + 1 - k), f (φ p).1 = c - ε) ∧
            Function.Injective φ ∧
            Topology.IsClosedEmbedding φ ∧
            (∀ hk0 : NeZero k, ∀ hl0 : NeZero (m + 1 - k),
              ∃ hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x,
                ∃ φ₀ : AttachingRegion k (m + 1 - k) → LevelSetSpace f (c - ε),
                  @ContMDiff ℝ _
                    (EuclideanSpace ℝ (Fin (k - 1)) ×
                      EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) _ _
                    (ModelProd (EuclideanSpace ℝ (Fin (k - 1)))
                      (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
                    ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
                    (AttachingRegion k (m + 1 - k)) _ (attachingRegionChartedSpace k (m + 1 - k))
                    (MorseModel m) _ _ (MorseModel m) _
                    (𝓘(ℝ, MorseModel m)) (LevelSetSpace f (c - ε)) _
                    (manifoldLevelSetChartedSpace I f (c - ε) (hf.of_le le_top) hreg_f)
                    (⊤ : ℕ∞)
                    φ₀ ∧
                  Topology.IsClosedEmbedding φ₀ ∧
                  ∀ p : AttachingRegion k (m + 1 - k), (φ₀ p).1 = (φ p).1) ∧
            @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
              (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
              (morseAttachedSpace hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr) _
              (morseAttachedNaturalChartedSpace hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr) ∧
            ∃ Ψ : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
              (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
              (morseModelWithCornersHalfSpace m)
              (morseAttachedSpace hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr) _
              (morseAttachedNaturalChartedSpace hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr)
              (morseUpperSublevel hk c r) _ (morseUpperChartedSpace hk c r hr)
              (⊤ : ℕ∞),
              morseAttachedDiffeomorphRelative hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr
                (hcs₁ := morseAttachedNaturalChartedSpace hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr)
                (hcs₂ := morseUpperChartedSpace hk c r hr)
                (Ψ := Ψ) ∧
            ∃ φc : C(CellBoundary k, SublevelSpace f (c - ε)),
                Nonempty (HomotopyEquivUnder
                  (X := SublevelSpace f (c - ε)) (Y := SublevelSpace f (c + ε))
                  (Z := CellAdjunctionSpace k φc)
                  (toBase := sublevelInclusion f (by linarith [hε]))
                  (fromBase := ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φc)
                    (continuous_adjunctionLower (i := cellBoundaryInclusion k) φc)))  := by
  rcases morse_smooth_handle_attachment_relative (m := m) (H := H) (M := M) I f hf p c k hk hnd hindex
    hfp a ha hcompact hunique with
    ⟨ε, hε, hεa, g, hg, hg_le, hgup, hglow, v, hv, hsupp, hdf, hrate, Φ, htransport, htie,
      ⟨η, hη, hηmain⟩, r, hr, hrsq, δ₁, hδ₁₀, hδ₁r, φ, hφb, hφinj, hφcl, hsmooth, hmani,
      Ψ₀, hrel₀, ⟨φc, hcelladj⟩⟩
  refine ⟨ε, hε, hεa, g, hg, hg_le, hgup, hglow, v, hv, hsupp, hdf, hrate, Φ, htransport, htie,
    ⟨η, hη, hηmain⟩, r, hr, hrsq, δ₁, hδ₁₀, hδ₁r, φ, hφb, hφinj, hφcl, hsmooth, ?_, ?_⟩
  · exact morseAttachedNaturalIsManifold hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr
  · refine ⟨morseAttachedNaturalDiffeomorphUpper hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr,
      morseAttachedNaturalDiffeomorphRelative hk c ε r δ₁ (le_of_lt hε) hδ₁₀ hδ₁r hr,
      ⟨φc, hcelladj⟩⟩

theorem one_critical_point_cell_attachment {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ m + 1)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c)
    (a : ℝ) (ha : 0 < a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ε ≤ a ∧
    ∃ φ : C(CellBoundary k, SublevelSpace f (c - ε)),
      Nonempty (HomotopyEquivUnder
        (X := SublevelSpace f (c - ε)) (Y := SublevelSpace f (c + ε))
        (Z := CellAdjunctionSpace k φ)
        (toBase := sublevelInclusion f (by linarith [hε]))
        (fromBase := ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φ)
          (continuous_adjunctionLower (i := cellBoundaryInclusion k) φ))) := by
  rcases morse_smooth_handle_attachment_relative (m := m) (H := H) (M := M) I f hf p c k hk hnd hindex
    hfp a ha hcompact hunique with
    ⟨ε, hε, hεa, g, hg, hg_le, hgup, hglow, v, hv, hsupp, hdf, hrate, Φ, htransport, htie, ⟨η, hη, hηmain⟩, r, hr,
      hrsq, δ₁, hδ₁₀, hδ₁r, φ, hφb, hφinj, hφcl, hsmooth, hmani, Ψ, hrel, ⟨φc, hcelladj⟩⟩
  exact ⟨ε, hε, hεa, φc, hcelladj⟩

theorem morse_smooth_attaching_embedding {m : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ m + 1)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c)
    (a : ℝ) (ha : 0 < a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x) [NeZero k] [NeZero (m + 1 - k)] :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ a ∧
    ∃ φ : AttachingRegion k (m + 1 - k) → SublevelSpace f (c - ε),
      (∀ p : AttachingRegion k (m + 1 - k), f (φ p).1 = c - ε) ∧
      Function.Injective φ ∧
      Topology.IsClosedEmbedding φ ∧
      (∃ hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x,
        ∃ φ₀ : AttachingRegion k (m + 1 - k) → LevelSetSpace f (c - ε),
          @ContMDiff ℝ _
            (EuclideanSpace ℝ (Fin (k - 1)) ×
              EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) _ _
            (ModelProd (EuclideanSpace ℝ (Fin (k - 1)))
              (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
            ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
            (AttachingRegion k (m + 1 - k)) _ (attachingRegionChartedSpace k (m + 1 - k))
            (MorseModel m) _ _ (MorseModel m) _
            (𝓘(ℝ, MorseModel m)) (LevelSetSpace f (c - ε)) _
            (manifoldLevelSetChartedSpace I f (c - ε) (hf.of_le le_top) hreg_f)
            (⊤ : ℕ∞)
            φ₀ ∧
          Topology.IsClosedEmbedding φ₀ ∧
          ∀ p : AttachingRegion k (m + 1 - k), (φ₀ p).1 = (φ p).1) := by
  rcases morse_smooth_handle_attachment_relative (m := m) (H := H) (M := M) I f hf p c k hk hnd hindex
    hfp a ha hcompact hunique with
    ⟨ε, hε, hεa, g, hg, hg_le, hgup, hglow, v, hv, hsupp, hdf, hrate, Φ, htransport, htie, ⟨η, hη, hηmain⟩, r, hr,
      hrsq, δ₁, hδ₁₀, hδ₁r, φ, hφb, hφinj, hφcl, hsmooth, hmani, Ψ, hrel, ⟨φc, hcelladj⟩⟩
  exact ⟨ε, hε, hεa, φ, hφb, hφinj, hφcl,
    hsmooth (inferInstance : NeZero k) (inferInstance : NeZero (m + 1 - k))⟩

end ManifoldCellAttachment


end
end DifferentialGeometry.Topology.Morse
