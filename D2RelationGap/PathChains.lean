import D2RelationGap.BasedLoops

/-!
Actual finite-path weighted chains and the degree-one rank input for the tower.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
construction and obstruction. These are actual ordered-face chain statements;
presentation/character/geometric adequacy and the full tower remain open.
-/
noncomputable section
namespace D2RelationGap.PathChains
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops
variable {V K : Type*} [LinearOrder V] [Field K]

def chain {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v : V} : Path A u v → Edge A →₀ K
  | .refl _ _ => 0
  | @Path.cons _ _ _ u w _ h p => edge tau u w h + coeff tau u w • chain tau p

/-- Prefix coefficients and the checked reversal rule telescope on actual paths. -/
theorem chain_boundary {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v : V} (p : Path A u v) :
    boundaryOne A (coeff tau) (chain tau p) =
      (value tau p : K) • point v (endActive p) - point u (startActive p) := by
  induction p with
  | refl => simp [chain, value]
  | @cons u v w h p ih =>
      simp only [chain, map_add, map_smul, edge_boundary, ih, smul_sub, smul_smul]
      simp only [value, Units.val_mul, coeff]
      abel

theorem chain_append {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v w : V} (p : Path A u v) (q : Path A v w) :
    chain tau (append p q) = chain tau p + (value tau p : K) • chain tau q := by
  induction p with
  | refl => simp [chain, value, append]
  | cons h p ih => simp [chain, append, ih, value, smul_add, smul_smul, coeff, add_assoc]

/-- A literal finite-support filling computed from the finite move derivation.
Triangle moves use only their witnessed faces, with the existing orientation rules. -/
def filling {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v : V} {p q : Path A u v} (m : Moves p q) : Triangle A →₀ K := by
  induction m with
  | refl => exact 0
  | symm m ih => exact -ih
  | trans m n ih jh => exact ih + jh
  | stutter => exact 0
  | backtrack => exact 0
  | @triangle u v w z h p => exact triangle tau u v w h
  | @prepend u v w h p q m ih => exact coeff tau u v • ih
  | suffix r m ih => exact ih

theorem filling_boundary {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v : V} {p q : Path A u v} (m : Moves p q) :
    boundaryTwo A (coeff tau) (filling tau m) = chain tau p - chain tau q := by
  induction m with
  | refl => simp [filling]
  | symm m ih =>
      change boundaryTwo A (coeff tau) (-filling tau m) = _
      rw [map_neg, ih]
      abel
  | trans m n ih jh =>
      change boundaryTwo A (coeff tau) (filling tau m + filling tau n) = _
      rw [map_add, ih, jh]
      abel
  | stutter h p => simp [filling, chain, edge_collapsed, coeff_diagonal tau _ h]
  | @backtrack u v w h p =>
      rw [filling, map_zero]
      simp [chain, edge_reverse tau u v h, smul_add, smul_smul,
        coeff_inverse_mul tau u v h]
  | @triangle u v w z h p =>
      rw [filling, triangle_boundary]
      simp only [chain, smul_add, smul_smul,
        coeff_flat tau u v w h]
      abel
  | @prepend u v w h p q m ih =>
      change boundaryTwo A (coeff tau) (coeff tau u v • filling tau m) = _
      rw [map_smul, ih]
      simp [chain, smul_sub]
  | suffix r m ih =>
      change boundaryTwo A (coeff tau) (filling tau m) = _
      rw [ih]
      simp [chain_append, value_moves tau m]

theorem chain_difference_mem_range {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) {u v : V} {p q : Path A u v} (m : Moves p q) :
    chain tau p - chain tau q ∈ (boundaryTwo A (coeff tau)).range :=
  ⟨filling tau m, filling_boundary tau m⟩

/-- Choice obtains a finite witness from equality in precisely the checked quotient.
This does not provide an oracle for equality in the original group or geometric pi1. -/
def fillingOfClassEq {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v : V} (p q : Path A u v)
    (he : Quotient.mk (pathSetoid A u v) p = Quotient.mk _ q) : Triangle A →₀ K :=
  filling tau (movesOfClassEq p q he)

theorem fillingOfClassEq_boundary {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) {u v : V} (p q : Path A u v)
    (he : Quotient.mk (pathSetoid A u v) p = Quotient.mk _ q) :
    boundaryTwo A (coeff tau) (fillingOfClassEq tau p q he) = chain tau p - chain tau q :=
  filling_boundary tau _

theorem null_loop_chain_is_boundary {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) (r : Vertex A) (p : Path A r.val r.val)
    (he : (Quotient.mk _ p : Loop A r) = 1) :
    ∃ c : Triangle A →₀ K, boundaryTwo A (coeff tau) c = chain tau p := by
  refine ⟨fillingOfClassEq tau p (.refl r.val r.property) he, ?_⟩
  simpa [chain] using fillingOfClassEq_boundary tau p (.refl r.val r.property) he

/-- Uniqueness is proved only under the explicitly supplied d2 injectivity. -/
theorem filling_unique_of_injective {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) (h2 : Function.Injective (boundaryTwo A (coeff tau)))
    {u v : V} {p q : Path A u v} (m n : Moves p q) : filling tau m = filling tau n := by
  apply h2
  rw [filling_boundary, filling_boundary]

theorem filling_eq_zero_iff_of_injective {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) (h2 : Function.Injective (boundaryTwo A (coeff tau)))
    {u v : V} {p q : Path A u v} (m : Moves p q) :
    filling tau m = 0 ↔ chain tau p = chain tau q := by
  constructor
  · intro h
    have hb := filling_boundary tau m
    rw [h, map_zero] at hb
    exact sub_eq_zero.mp hb.symm
  · intro h
    apply h2
    rw [filling_boundary, h, sub_self, map_zero]

/-- No finiteness, tree choice or homology-adequacy hypothesis is needed. -/
theorem point_in_range_of_loop {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) (r : Vertex A) (p : Path A r.val r.val)
    (hp : value tau p ≠ 1) : point r.val r.property ∈ (boundaryOne A (coeff tau)).range := by
  have hc : (value tau p : K) - 1 ≠ 0 := by
    intro he
    apply hp
    apply Units.ext
    exact sub_eq_zero.mp he
  refine ⟨((value tau p : K) - 1)⁻¹ • chain tau p, ?_⟩
  rw [map_smul, chain_boundary]
  change ((value tau p : K) - 1)⁻¹ •
    ((value tau p : K) • point r.val r.property - point r.val r.property) = _
  have hs : (value tau p : K) • point (K := K) r.val r.property - point r.val r.property =
      ((value tau p : K) - 1) • point r.val r.property := by rw [sub_smul, one_smul]
  rw [hs, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Connectedness is supplied as actual root-to-active-vertex paths. -/
theorem all_points_in_range {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) (r : Vertex A)
    (paths : ∀ v : Vertex A, Path A r.val v.val) (p : Path A r.val r.val)
    (hp : value tau p ≠ 1) :
    ∀ v : Vertex A, point v.val v.property ∈ (boundaryOne A (coeff tau)).range := by
  intro v
  have hr := point_in_range_of_loop tau r p hp
  have hpath : boundaryOne A (coeff tau) (chain tau (paths v)) ∈
      (boundaryOne A (coeff tau)).range := ⟨_, rfl⟩
  have hv : (value tau (paths v) : K) • point v.val v.property ∈
      (boundaryOne A (coeff tau)).range := by
    simpa [chain_boundary] using (boundaryOne A (coeff tau)).range.add_mem hpath hr
  have hn : (value tau (paths v) : K) ≠ 0 := (value tau (paths v)).ne_zero
  simpa [smul_smul, inv_mul_cancel₀ hn] using
    (boundaryOne A (coeff tau)).range.smul_mem ((value tau (paths v) : K)⁻¹) hv

theorem boundaryOne_surjective {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) (r : Vertex A)
    (paths : ∀ v : Vertex A, Path A r.val v.val) (p : Path A r.val r.val)
    (hp : value tau p ≠ 1) : Function.Surjective (boundaryOne A (coeff tau)) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro x _
  induction x using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | @single_add v c x hv hc ih =>
      apply Submodule.add_mem _
      · have h := (boundaryOne A (coeff tau)).range.smul_mem c
          (all_points_in_range tau r paths p hp v)
        simpa [point, Finsupp.smul_single] using h
      · exact ih (Submodule.mem_top)

theorem boundaryOne_surjective_of_holonomy {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) (r : Vertex A)
    (paths : ∀ v : Vertex A, Path A r.val v.val) (c : Loop A r)
    (hc : holonomy tau r c ≠ 1) : Function.Surjective (boundaryOne A (coeff tau)) := by
  revert hc
  refine Quotient.inductionOn c ?_
  intro p hp
  exact boundaryOne_surjective tau r paths p hp

/-- A rank inequality for the actual ordered chains, not geometric homology. -/
theorem finite_cell_bound {A : PreAbstractSimplicialComplex V}
    [Fintype (Vertex A)] [Fintype (Edge A)] [Fintype (Triangle A)]
    (tau : Transport (K := K) A) (r : Vertex A)
    (paths : ∀ v : Vertex A, Path A r.val v.val) (c : Loop A r)
    (hc : holonomy tau r c ≠ 1) (h2 : Function.Injective (boundaryTwo A (coeff tau))) :
    Fintype.card (Vertex A) + Fintype.card (Triangle A) ≤ Fintype.card (Edge A) := by
  have hle : (boundaryTwo A (coeff tau)).range ≤ (boundaryOne A (coeff tau)).ker := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact DFunLike.congr_fun (unit_boundary_chain tau) y
  have hdim := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj h2, Module.finrank_finsupp_self] at hdim
  have hn := (boundaryOne A (coeff tau)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (boundaryOne_surjective_of_holonomy tau r paths c hc),
    finrank_top, Module.finrank_finsupp_self, Module.finrank_finsupp_self] at hn
  omega

/-- Exact transports have trivial loop values; connectedness alone is insufficient. -/
def trivialTransport (A : PreAbstractSimplicialComplex V) : Transport (K := K) A :=
  gaugeTransport A (fun _ => 1)

theorem trivial_boundary_not_surjective (A : PreAbstractSimplicialComplex V) (r : Vertex A) :
    ¬ Function.Surjective (boundaryOne A (coeff (trivialTransport (K := K) A))) := by
  let aug : (Vertex A →₀ K) →ₗ[K] K := Finsupp.linearCombination K (fun _ => 1)
  have ha : aug.comp (boundaryOne A (coeff (trivialTransport (K := K) A))) = 0 := by
    apply Finsupp.lhom_ext
    intro e c
    simp [aug, boundaryOne, VoltageChains.baseOne, incidence, trivialTransport,
      coeff, gaugeTransport]
  intro hs
  obtain ⟨x, hx⟩ := hs (point r.val r.property)
  have h := DFunLike.congr_fun ha x
  change aug (boundaryOne A (coeff (trivialTransport (K := K) A)) x) = 0 at h
  rw [hx] at h
  simp [aug, point] at h

def prefixGauge : Transport (K := ℚ) cycleComplex :=
  gaugeTransport cycleComplex (fun v => if v = 0 then 1 else
    if v = 1 then Units.mk0 2 (by norm_num) else Units.mk0 6 (by norm_num))

def prefixPath : Path cycleComplex 0 2 :=
  .cons (u := 0) (v := 1) (by change ({0, 1} : Finset (Fin 3)).Nonempty ∧ _; decide)
    (.cons (by change ({1, 2} : Finset (Fin 3)).Nonempty ∧ _; decide)
      (.refl 2 (by change ({2} : Finset (Fin 3)).Nonempty ∧ _; decide)))

/-- The naive sum misses the factor 2 on the second edge of this actual path. -/
theorem missing_prefix_transport_rejected :
    edge prefixGauge 0 1 (by change ({0, 1} : Finset (Fin 3)).Nonempty ∧ _; decide) +
      edge prefixGauge 1 2 (by change ({1, 2} : Finset (Fin 3)).Nonempty ∧ _; decide) ≠
        chain prefixGauge prefixPath := by
  intro he
  let e : Edge cycleComplex := ⟨1, 2, by decide,
    by change ({1, 2} : Finset (Fin 3)).Nonempty ∧ _; decide⟩
  have h := congrArg (fun c : Edge cycleComplex →₀ ℚ => c e) he
  norm_num [chain, prefixPath, prefixGauge, gaugeTransport, coeff, edge, e,
    Finsupp.single_apply] at h

/-- Reversing the filling sign gives the wrong actual boundary. -/
theorem corrupted_filling_sign_rejected :
    let A : PreAbstractSimplicialComplex (Fin 3) := ⊤
    let tau := trivialTransport (K := ℚ) A
    let p : Path A 2 2 := .refl 2 (Finset.singleton_nonempty _)
    let m := Moves.triangle (u := 0) (v := 1) (w := 2)
      (Finset.insert_nonempty _ _) p
    boundaryTwo A (coeff tau) (-filling tau m) ≠ boundaryTwo A (coeff tau) (filling tau m) := by
  dsimp only
  intro he
  let e : Edge (⊤ : PreAbstractSimplicialComplex (Fin 3)) :=
    ⟨0, 1, by decide, Finset.insert_nonempty _ _⟩
  have h := congrArg (fun c : Edge (⊤ : PreAbstractSimplicialComplex (Fin 3)) →₀ ℚ => c e) he
  norm_num [map_neg, filling, triangle, trivialTransport, coeff, gaugeTransport,
    boundaryTwo, VoltageChains.baseTwo, incidence, face01, face02, face12, e,
    Finsupp.single_apply] at h

/-- Prefixing a triangle move multiplies its filling by the actual edge transport. -/
theorem missing_prepend_filling_transport_rejected :
    let A : PreAbstractSimplicialComplex (Fin 4) := ⊤
    let tau := gaugeTransport A (fun v => if v = 0 then (1 : ℚˣ)
      else Units.mk0 2 (by norm_num))
    let p : Path A 3 3 := .refl 3 (Finset.singleton_nonempty _)
    let m := Moves.triangle (u := 1) (v := 2) (w := 3)
      (Finset.insert_nonempty _ _) p
    filling tau (.prepend (u := 0) (Finset.insert_nonempty _ _) m) ≠ filling tau m := by
  dsimp only
  intro he
  let t : Triangle (⊤ : PreAbstractSimplicialComplex (Fin 4)) :=
    ⟨1, 2, 3, by decide, by decide, Finset.insert_nonempty _ _⟩
  have h := congrArg (fun c : Triangle (⊤ : PreAbstractSimplicialComplex (Fin 4)) →₀ ℚ => c t) he
  norm_num [filling, triangle, coeff, gaugeTransport, t, Finsupp.single_apply] at h

end D2RelationGap.PathChains
