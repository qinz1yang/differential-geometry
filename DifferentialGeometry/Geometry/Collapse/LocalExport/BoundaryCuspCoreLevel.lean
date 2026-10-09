import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreDefs
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightGeometry

/-!
# BCG06, G2: the kept inner-collar certificate, the height-unit vector, Fermat (lane BCG6-K)

Draft 61 §4.2–§4.4, disposition D61-9. Three local inputs of the whole-core proof:

* From the KEPT smooth inner-collar pair certificate `P.retained b`
  (`D : T² × [a, 90] ≅ {level ≤ 90}`, `level ∘ D = pr₂`, `D p ∈ ∂_b W ↔ p.2 = a`):
  - `level_eq_levelBase_of_mem_component_BCG6K`: `level = a` on `∂_b W`;
  - `level_lt_of_height_le_two_BCG6K`, `levelBase_lt_thirtyNine_BCG6K`: a collar point of height
    `z ≤ 2` has `level < 39` (connectedness of `D(T² × [39, 90])`, which lies in `e(38 ≤ z ≤ 95)`);
  - `mfderiv_level_ne_zero_BCG6K`: `level` has no critical point on `{level ≤ 90}` (chain rule
    through `D` and `mfderiv_subtypeVal_Icc_one`).
* The height-unit vector (in place of `X_b = ∇η_b / |dη_b|²`):
  `exists_heightUnit_BCG6K` — at a band point some `w` has `dη_b(w) = 1`, `|w|_g ≤ 1.01`
  (BCP01.b, `CuspEmbedding.bcp01b_differential_of_contract`); `heightUnit_du_gt_BCG6K` — with
  the BCG04 differential estimate `|d(u - η_b)| ≤ c₃ |·|_g`: `du(w) > 1 - 1.02 c₃`, and
  `> .99` for `c₃ < 10⁻⁵`.
* Fermat at interior points of `W` (`mfderiv_eq_zero_of_isLocalMax_BCG6K`) and its use
  `exists_gt_of_mfderiv_ne_zero_BCG6K`; collar points of positive height are interior
  (`isInteriorPoint_of_height_pos_BCG6K`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

section Fermat

variable {W : CompactCarrier.{u}}

/-- **Fermat at an interior point of `W`**: a real function with a local maximum at an interior
point has zero differential there. -/
theorem mfderiv_eq_zero_of_isLocalMax_BCG6K {f : W.Carrier → ℝ} {x : W.Carrier}
    (hx : W.model.IsInteriorPoint x) (hf : IsLocalMax f x) :
    mfderiv W.model 𝓘(ℝ, ℝ) f x = 0 := by
  by_cases hd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) f x
  · rw [hd.mfderiv]
    have h0 : fderivWithin ℝ (writtenInExtChartAt W.model 𝓘(ℝ, ℝ) x f) (range W.model)
        ((extChartAt W.model x) x) = 0 := by
      rw [fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)]
      apply IsLocalMax.fderiv_eq_zero
      have hw : writtenInExtChartAt W.model 𝓘(ℝ, ℝ) x f = f ∘ (extChartAt W.model x).symm := by
        ext y
        simp [writtenInExtChartAt]
      rw [hw]
      apply IsLocalMax.comp_continuous
      · rw [extChartAt_to_inv]
        exact hf
      · exact continuousAt_extChartAt_symm x
    rw [h0]
    ext v
    simp
  · exact mfderiv_zero_of_not_mdifferentiableAt hd

/-- A real function with nonzero differential at an interior point takes larger values in every
neighbourhood. -/
theorem exists_gt_of_mfderiv_ne_zero_BCG6K {f : W.Carrier → ℝ} {x : W.Carrier}
    (hx : W.model.IsInteriorPoint x) (hf : mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    {U : Set W.Carrier} (hU : U ∈ 𝓝 x) : ∃ y ∈ U, f x < f y := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  exact hf (mfderiv_eq_zero_of_isLocalMax_BCG6K hx (Filter.mem_of_superset hU h))

end Fermat

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- Collar points of positive height are interior points of `W`. -/
theorem isInteriorPoint_of_height_pos_BCG6K {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hz : 0 < p.2.val 0) : W.model.IsInteriorPoint (e.toFun p) := by
  refine (W.model.isInteriorPoint_or_isBoundaryPoint (e.toFun p)).resolve_right fun hb => ?_
  have h := (e.boundary_preimage hp).mp hb
  linarith

namespace BoundaryCollarPacket

variable (P : BoundaryCollarPacket W g K A w₀ ε) (b : Fin P.cusp.count)

/-- A collar point of height `≤ 2` is in the retained sublevel `{level ≤ 90}`. -/
theorem level_le_ninety_of_height_le_two_BCG6K {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (h2 : p.2.val 0 ≤ 2) : P.level b ((P.cusp.collar b).toFun p) ≤ 90 := by
  have h : (P.cusp.collar b).toFun p ∈ {y | P.level b y ≤ 90} := by
    rw [P.level_sublevel_eq b]
    exact ⟨p, ⟨hp, Or.inl h2⟩, rfl⟩
  exact h

/-- **(R1)** The level function equals its base value `a` on `∂_b W`. -/
theorem level_eq_levelBase_of_mem_component_BCG6K {x : W.Carrier}
    (hx : x ∈ P.cusp.component b) : P.level b x = P.levelBase b := by
  obtain ⟨t, rfl⟩ := (Set.ext_iff.mp (P.cusp.collar b).boundary_image x).mpr hx
  change (P.cusp.collar b).toFun (t, halfZero) ∈ P.cusp.component b at hx
  change P.level b ((P.cusp.collar b).toFun (t, halfZero)) = P.levelBase b
  have hle := P.level_le_ninety_of_height_le_two_BCG6K b (mem_cuspDomain_halfZero t)
    (by rw [halfZero_val_zero]; norm_num)
  have : Fact (P.levelBase b < 90) := ⟨P.levelBase_lt b⟩
  obtain ⟨cs, -, -, -, D, hDF, hDX⟩ := P.retained b
  let := cs
  set y : {x : W.Carrier // P.level b x ≤ 90} := ⟨_, hle⟩ with hy
  have hDy : (D (D.symm y)).1 = (P.cusp.collar b).toFun (t, halfZero) := by
    rw [D.apply_symm_apply]
  have hX : (D (D.symm y)).1 ∈ P.cusp.component b := by
    rw [hDy]
    exact hx
  rw [← hDy, hDF, (hDX _).mp hX]

/-- The two closed bands used in the connectedness argument are disjoint. -/
theorem collar_bands_disjoint_BCG6K {q q' : CuspHalfSpace} (hq : q ∈ cuspDomain)
    (hq' : q' ∈ cuspDomain) (h : (P.cusp.collar b).toFun q = (P.cusp.collar b).toFun q') :
    q = q' := by
  have h' : (⟨q, hq⟩ : cuspDomain) = ⟨q', hq'⟩ := (P.cusp.collar b).isEmbedding.injective h
  exact congrArg Subtype.val h'

/-- **(R2)** A collar point of height `z ≤ 2` has `level < 39`: the connected set
`D(T² × [max a 39, 90])` lies in the band `e(38 ≤ z ≤ 95)`, which is disjoint from `e(z ≤ 2)`. -/
theorem level_lt_of_height_le_two_BCG6K {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (h2 : p.2.val 0 ≤ 2) : P.level b ((P.cusp.collar b).toFun p) < 39 := by
  set e := P.cusp.collar b with he
  have hε1 := P.tolerance_le_one
  have : Fact (P.levelBase b < 90) := ⟨P.levelBase_lt b⟩
  obtain ⟨cs, -, hι, -, D, hDF, -⟩ := P.retained b
  let := cs
  set a := P.levelBase b with ha
  have hab : a ≤ 90 := (P.levelBase_lt b).le
  set φ : Torus × ℝ → W.Carrier := fun q => (D (q.1, Set.projIcc a 90 hab q.2)).1 with hφ
  have hφc : Continuous φ := by
    have h1 : Continuous fun q : Torus × ℝ => ((q.1, Set.projIcc a 90 hab q.2) : Torus × Icc a 90) :=
      continuous_fst.prodMk ((continuous_projIcc).comp continuous_snd)
    exact continuous_subtype_val.comp (D.continuous.comp h1)
  set S := φ '' (univ ×ˢ Icc (max a 39) 90) with hS
  have hSc : IsPreconnected S :=
    (isPreconnected_univ.prod isPreconnected_Icc).image φ hφc.continuousOn
  set Aset := e.toFun '' {q : CuspHalfSpace | 0 ≤ q.2.val 0 ∧ q.2.val 0 ≤ 2} with hA
  set Bset := e.toFun '' {q : CuspHalfSpace | 38 ≤ q.2.val 0 ∧ q.2.val 0 ≤ 95} with hB
  have hAc : IsClosed Aset := (e.isCompact_image_band (by norm_num [cuspDepth])).isClosed
  have hBc : IsClosed Bset := (e.isCompact_image_band (by norm_num [cuspDepth])).isClosed
  -- membership in `S` of every retained point of level `≥ 39`
  have hmemS : ∀ y : {x : W.Carrier // P.level b x ≤ 90}, 39 ≤ P.level b y.1 → y.1 ∈ S := by
    intro y hy
    refine ⟨((D.symm y).1, ((D.symm y).2 : ℝ)), ⟨mem_univ _, ?_, (D.symm y).2.2.2⟩, ?_⟩
    · have hl : P.level b (D (D.symm y)).1 = ((D.symm y).2 : ℝ) := hDF _
      rw [D.apply_symm_apply] at hl
      exact max_le (D.symm y).2.2.1 (hl ▸ hy)
    · change (D ((D.symm y).1, Set.projIcc a 90 hab ((D.symm y).2 : ℝ))).1 = y.1
      rw [Set.projIcc_val, Prod.mk.eta, D.apply_symm_apply]
  -- `S` lies in `A ∪ B`
  have hSAB : S ⊆ Aset ∪ Bset := by
    rintro _ ⟨q, ⟨-, hq1, hq2⟩, rfl⟩
    have hlev : P.level b (φ q) = q.2 := by
      change P.level b (D (q.1, Set.projIcc a 90 hab q.2)).1 = q.2
      rw [hDF, Set.projIcc_of_mem hab ⟨(le_max_left a 39).trans hq1, hq2⟩]
    have hle : φ q ∈ {y | P.level b y ≤ 90} := by
      change P.level b (φ q) ≤ 90
      rw [hlev]
      exact hq2
    rw [P.level_sublevel_eq b] at hle
    obtain ⟨q', ⟨hq'd, hq'⟩, hq'eq⟩ := hle
    rcases hq' with hz | ⟨h98, hη⟩
    · exact Or.inl ⟨q', ⟨q'.2.2, hz⟩, hq'eq⟩
    · rcases le_or_gt (q'.2.val 0) 2 with hz2 | hz2
      · exact Or.inl ⟨q', ⟨q'.2.2, hz2⟩, hq'eq⟩
      have hc := abs_lt.mp (P.height_contract b q' hq'd hz2.le h98).1
      rcases le_or_gt (q'.2.val 0) 95 with hz95 | hz95
      · have hl := P.level_eq_height b q' hz2.le hz95
        rw [hq'eq, hlev] at hl
        have h39 : 39 ≤ q.2 := (le_max_right a 39).trans hq1
        refine Or.inr ⟨q', ⟨?_, hz95⟩, hq'eq⟩
        rw [hq'eq] at hc
        linarith
      · exfalso
        linarith
  have hdisj : ∀ x, x ∈ Aset → x ∈ Bset → False := by
    rintro _ ⟨q1, hq1, rfl⟩ ⟨q2, hq2, h12⟩
    have := P.collar_bands_disjoint_BCG6K b
      (cusp_mem_cuspDomain_of_le (b := 95) (by norm_num [cuspDepth]) hq2.2)
      (cusp_mem_cuspDomain_of_le (b := 2) (by norm_num [cuspDepth]) hq1.2) h12
    rw [this] at hq2
    linarith [hq1.2, hq2.1]
  have hsplit := (isPreconnected_iff_subset_of_disjoint_closed.mp hSc) Aset Bset hAc hBc hSAB
    (by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro _ hxA hxB
      exact hdisj x hxA hxB)
  -- a point of `S` in `B`: the collar point at height `50`
  obtain ⟨θ₀⟩ := (inferInstance : Nonempty Torus)
  set q₀ : CuspHalfSpace := (θ₀, halfSpaceOneLift 50) with hq₀
  have hz₀ : q₀.2.val 0 = 50 := by
    rw [hq₀]
    change (halfSpaceOneLift 50).1 0 = 50
    rw [halfSpaceOneLift_val_zero]
    norm_num
  have hq₀d : q₀ ∈ cuspDomain := cusp_mem_cuspDomain_of_le (b := 50) (by norm_num [cuspDepth])
    hz₀.le
  have hc₀ := abs_lt.mp (P.height_contract b q₀ hq₀d (by rw [hz₀]; norm_num)
    (by rw [hz₀]; norm_num)).1
  have hl₀ := P.level_eq_height b q₀ (by rw [hz₀]; norm_num) (by rw [hz₀]; norm_num)
  rw [hz₀] at hc₀
  have hle₀ : P.level b (e.toFun q₀) ≤ 90 := by rw [hl₀]; linarith
  have hS₀ : e.toFun q₀ ∈ S :=
    hmemS ⟨_, hle₀⟩ (by change 39 ≤ P.level b (e.toFun q₀); rw [hl₀]; linarith)
  have hB₀ : e.toFun q₀ ∈ Bset := ⟨q₀, ⟨by rw [hz₀]; norm_num, by rw [hz₀]; norm_num⟩, rfl⟩
  have hSB : S ⊆ Bset := by
    rcases hsplit with hSA | hSB
    · exact (hdisj _ (hSA hS₀) hB₀).elim
    · exact hSB
  by_contra hcon
  have hle := P.level_le_ninety_of_height_le_two_BCG6K b hp h2
  have hpS := hmemS ⟨_, hle⟩ (not_lt.mp hcon)
  exact hdisj _ ⟨p, ⟨p.2.2, h2⟩, rfl⟩ (hSB hpS)

/-- The base value of the level function is `< 39`. -/
theorem levelBase_lt_thirtyNine_BCG6K : P.levelBase b < 39 := by
  obtain ⟨θ₀⟩ := (inferInstance : Nonempty Torus)
  have hX : (P.cusp.collar b).toFun (θ₀, halfZero) ∈ P.cusp.component b :=
    (Set.ext_iff.mp (P.cusp.collar b).boundary_image _).mp ⟨θ₀, rfl⟩
  rw [← P.level_eq_levelBase_of_mem_component_BCG6K b hX]
  exact P.level_lt_of_height_le_two_BCG6K b (mem_cuspDomain_halfZero θ₀)
    (by rw [halfZero_val_zero]; norm_num)

/-- **(R3)** The level function has no critical point on the retained sublevel `{level ≤ 90}`:
`level ∘ D = pr₂` and the derivative of `pr₂` in the direction `(0, 1)` is `1`. -/
theorem mfderiv_level_ne_zero_BCG6K {x : W.Carrier} (hx : P.level b x ≤ 90) :
    mfderiv W.model 𝓘(ℝ, ℝ) (P.level b) x ≠ 0 := by
  have : Fact (P.levelBase b < 90) := ⟨P.levelBase_lt b⟩
  obtain ⟨cs, hman, hι, -, D, hDF, -⟩ := P.retained b
  let := cs
  have := hman
  set y : {x : W.Carrier // P.level b x ≤ 90} := ⟨x, hx⟩ with hy
  set p := D.symm y with hp
  have hDp : (D p).1 = x := by rw [hp, D.apply_symm_apply]
  have hcomp : (fun q : Torus × Icc (P.levelBase b) 90 => (q.2 : ℝ)) =
      P.level b ∘ (fun q => (D q).1) := by
    funext q
    exact (hDF q).symm
  have hlev : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.level b) ((fun q => (D q).1) p) :=
    ((P.contMDiff_level b) _).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt (torusModel.prod (𝓡∂ 1)) W.model (fun q => (D q).1) p :=
    ((hι.comp D.contMDiff) p).mdifferentiableAt (by simp)
  set v : TangentSpace (torusModel.prod (𝓡∂ 1)) p :=
    ((0 : TangentSpace torusModel p.1), (1 : TangentSpace (𝓡∂ 1) p.2)) with hv
  have hone : mfderiv (torusModel.prod (𝓡∂ 1)) 𝓘(ℝ, ℝ)
      (fun q : Torus × Icc (P.levelBase b) 90 => (q.2 : ℝ)) p v = (1 : ℝ) := by
    have hc : (fun q : Torus × Icc (P.levelBase b) 90 => (q.2 : ℝ)) =
        (Subtype.val : Icc (P.levelBase b) 90 → ℝ) ∘ Prod.snd := rfl
    rw [hc, mfderiv_comp p ((contMDiff_subtypeVal_Icc (n := 1)).mdifferentiableAt one_ne_zero)
      mdifferentiableAt_snd, mfderiv_snd]
    exact mfderiv_subtypeVal_Icc_one p.2
  intro h0
  have h := mfderiv_comp p hlev hval
  rw [← hcomp, hDp, h0] at h
  rw [h] at hone
  have h01 : (0 : ℝ) = 1 := hone
  norm_num at h01

/-- **The height-unit vector** (replacing `X_b = ∇η_b / |dη_b|²`): at a band point some tangent
vector `w` has `dη_b(w) = 1` and `|w|_g ≤ 1.01` (BCP01.b for `ε ≤ 1/1000`). -/
theorem exists_heightUnit_BCG6K (hε : ε ≤ 1 / 1000) {x : W.Carrier}
    (hx : x ∈ P.collarBand_BAUGA b) :
    ∃ w : TangentSpace W.model x, mvfderiv W.model (P.height b) x w = 1 ∧
      Real.sqrt (g.inner x w w) ≤ 101 / 100 := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hpd : p ∈ cuspDomain :=
    cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
  have hδ : w₀ ≤ 1 / 1000 := P.threshold.trans (by norm_num)
  obtain ⟨-, ⟨w', hpos, hle⟩, -⟩ := (P.cusp.collar b).bcp01b_differential_of_contract hδ
    (P.contMDiff_height b) P.tolerance_pos.le hε hpd
    (P.height_contract b p hpd hp.1.le hp.2.le).2.1
  set c := mvfderiv W.model (P.height b) ((P.cusp.collar b).toFun p) w' with hc
  refine ⟨c⁻¹ • w', ?_, ?_⟩
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hpos.ne']
  · have hinner : g.inner ((P.cusp.collar b).toFun p) (c⁻¹ • w') (c⁻¹ • w') =
        c⁻¹ ^ 2 * g.inner ((P.cusp.collar b).toFun p) w' w' := by
      rw [map_smul, map_smul]
      simp only [smul_apply, smul_eq_mul]
      ring
    rw [hinner, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hpos.le)]
    rw [inv_mul_le_iff₀ hpos]
    have hs := Real.sqrt_nonneg (g.inner ((P.cusp.collar b).toFun p) w' w')
    nlinarith

variable {P b}

/-- **The height derivative of `u`** along the height-unit vector: with the BCG04 differential
estimate `|d(u - η_b)(w)| ≤ c₃ |w|_g` at the point, `du(w) > 1 - 1.02 c₃` (`c₃ > 0`). -/
theorem heightUnit_du_gt_BCG6K {u : W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u)
    {c₃ : ℝ} (hc₃ : 0 < c₃) {x : W.Carrier} {w : TangentSpace W.model x}
    (hw1 : mvfderiv W.model (P.height b) x w = 1) (hw2 : Real.sqrt (g.inner x w w) ≤ 101 / 100)
    (hBD : |mvfderiv W.model (fun y => u y - P.height b y) x w| ≤
      c₃ * Real.sqrt (g.inner x w w)) :
    1 - 102 / 100 * c₃ < mvfderiv W.model u x w := by
  have hud : MDifferentiableAt W.model 𝓘(ℝ, ℝ) u x := (hu x).mdifferentiableAt (by simp)
  have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.height b) x :=
    ((P.contMDiff_height b) x).mdifferentiableAt (by simp)
  have hsplit : mvfderiv W.model u x w =
      mvfderiv W.model (fun y => u y - P.height b y) x w + mvfderiv W.model (P.height b) x w := by
    rw [mvfderiv_fun_sub hud hηd, sub_apply]
    ring
  rw [hsplit, hw1]
  have h1 := (abs_le.mp hBD).1
  nlinarith

/-- Numerical form: for `0 < c₃ < 10⁻⁵`, `1 - 1.02 c₃ > .99`. -/
theorem one_sub_mul_c₃_gt_BCG6K {c₃ : ℝ} (h : c₃ < 1 / 100000) : 99 / 100 < 1 - 102 / 100 * c₃ := by
  linarith

end BoundaryCollarPacket

end DifferentialGeometry.Geometry.Collapse
