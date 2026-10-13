import D2RelationGap.PresentationTransport
import D2RelationGap.LocalTraceUpdate

/-!
Actual finite relator contractions on the SAME privately tagged target, the one-way
loop evaluation kernel containment N <= ker E, an actual finite x1-square TARGET
move witness, and its consequence for the DEFINED weighted d2 of this target.
Credit: OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
groups, character, Fox data and the torsion obstruction. The one-way route follows
the reviewed isolated AC-0005 draft. The degree-two filling/Fox comparison
(target d2 injective from algebraic Fox injectivity) remains OPEN; no relation-gap
theorem is asserted here.
-/
noncomputable section
namespace D2RelationGap.PresentationMoves
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops
open PresentationCells PresentationTransport

section Generic
variable {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}

omit [LinearOrder V] in
theorem mem_of_eq {s t : Finset V} (h : s ∈ A) (he : s = t) : t ∈ A := he ▸ h

/-- The literal top chain `T 0, T 1, ..., T L` through supplied actual edges. -/
def chain (T : ℕ → V) : (L : ℕ) → (∀ i < L, ({T i, T (i+1)} : Finset V) ∈ A) →
    ({T 0} : Finset V) ∈ A → Path A (T 0) (T L)
  | 0, _, h0 => .refl (T 0) h0
  | L+1, hT, _ => .cons (hT 0 (by omega))
      (chain (fun i => T (i+1)) L (fun i hi => hT (i+1) (by omega))
        (vertex_mem_of_face A _ (hT 0 (by omega)) _ (by simp)))

/-- Slide a path across its wall/upper collar, one actual triangle pair per edge. -/
theorem slide {x y : V} (p : Path A x y) (T : ℕ → V)
    (hwall : ∀ i < PolygonSource.length p,
      ({T i, PolygonSource.node p i, PolygonSource.node p (i+1)} : Finset V) ∈ A)
    (hupper : ∀ i < PolygonSource.length p,
      ({T i, T (i+1), PolygonSource.node p (i+1)} : Finset V) ∈ A)
    (hT : ∀ i < PolygonSource.length p, ({T i, T (i+1)} : Finset V) ∈ A)
    (hv : ({T 0, x} : Finset V) ∈ A)
    (hend : ({T (PolygonSource.length p), y} : Finset V) ∈ A) :
    Nonempty (Moves (.cons hv p)
      (append (chain T (PolygonSource.length p) hT (vertex_mem_of_face A _ hv _ (by simp)))
        (single hend))) := by
  induction p generalizing T with
  | refl x hx => exact ⟨.refl _⟩
  | @cons x x' y h p ih =>
    have hW : ({T 0, x, x'} : Finset V) ∈ A := by
      have h1 := hwall 0 (by simp [PolygonSource.length])
      change ({T 0, x, PolygonSource.node p 0} : Finset V) ∈ A at h1
      rwa [PolygonSource.node_zero] at h1
    have hU : ({T 0, T 1, x'} : Finset V) ∈ A := by
      have h1 := hupper 0 (by simp [PolygonSource.length])
      change ({T 0, T 1, PolygonSource.node p 0} : Finset V) ∈ A at h1
      rwa [PolygonSource.node_zero] at h1
    have hv' : ({T 1, x'} : Finset V) ∈ A := pair_mem_of_face A _ hU _ _ (by simp) (by simp)
    obtain ⟨m⟩ := ih (fun i => T (i+1))
      (fun i hi => hwall (i+1) (by simp only [PolygonSource.length]; omega))
      (fun i hi => hupper (i+1) (by simp only [PolygonSource.length]; omega))
      (fun i hi => hT (i+1) (by simp only [PolygonSource.length]; omega)) hv' hend
    exact ⟨(Moves.triangle hW p).trans ((Moves.triangle hU p).symm.trans
      (Moves.prepend (hT 0 (by simp [PolygonSource.length])) m))⟩

/-- Contract the top chain through its cap triangles. -/
theorem cone (T : ℕ → V) (c : V) (L : ℕ)
    (hcap : ∀ i < L, ({c, T i, T (i+1)} : Finset V) ∈ A)
    (hT : ∀ i < L, ({T i, T (i+1)} : Finset V) ∈ A) (h0 : ({T 0} : Finset V) ∈ A)
    (hc : ({c, T 0} : Finset V) ∈ A) (hcL : ({c, T L} : Finset V) ∈ A) :
    Nonempty (Moves (.cons hc (chain T L hT h0)) (single hcL)) := by
  induction L generalizing T with
  | zero => exact ⟨.refl _⟩
  | succ L ih =>
    have hC := hcap 0 (by omega)
    obtain ⟨m⟩ := ih (fun i => T (i+1)) (fun i hi => hcap (i+1) (by omega))
      (fun i hi => hT (i+1) (by omega)) (vertex_mem_of_face A _ (hT 0 (by omega)) _ (by simp))
      (pair_mem_of_face A _ hC _ _ (by simp) (by simp)) hcL
    exact ⟨(Moves.triangle hC _).trans m⟩

/-- Two literal backtracks, with the wraparound vertex identified only by `hb`. -/
theorem wrap {a b c b' : V} (hb : b' = b) (h1 : ({a, b} : Finset V) ∈ A)
    (h2 : ({b, c} : Finset V) ∈ A) (h3 : ({c, b'} : Finset V) ∈ A)
    (h4 : ({b', a} : Finset V) ∈ A) (ha : ({a} : Finset V) ∈ A) :
    Nonempty (Moves (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.refl a ha))))) (.refl a ha)) := by
  subst hb
  exact ⟨(Moves.prepend h1 (Moves.backtrack h2 _)).trans (Moves.backtrack h1 _)⟩

/-- Generic collar contraction: enter, slide, cone, wrap and leave. Every step is an
actual local move in `A`; no holonomy or character value is used. -/
theorem contract {x : V} (p : Path A x x) (T : ℕ → V) (c : V)
    (hwall : ∀ i < PolygonSource.length p,
      ({T i, PolygonSource.node p i, PolygonSource.node p (i+1)} : Finset V) ∈ A)
    (hupper : ∀ i < PolygonSource.length p,
      ({T i, T (i+1), PolygonSource.node p (i+1)} : Finset V) ∈ A)
    (hcap : ∀ i < PolygonSource.length p, ({c, T i, T (i+1)} : Finset V) ∈ A)
    (hT : ∀ i < PolygonSource.length p, ({T i, T (i+1)} : Finset V) ∈ A)
    (hv : ({T 0, x} : Finset V) ∈ A)
    (hend : ({T (PolygonSource.length p), x} : Finset V) ∈ A)
    (hc : ({c, T 0} : Finset V) ∈ A) (hcL : ({c, T (PolygonSource.length p)} : Finset V) ∈ A)
    (hwrap : T (PolygonSource.length p) = T 0) (hx : ({x} : Finset V) ∈ A) :
    Nonempty (Moves p (.refl x hx)) := by
  have hxT : ({x, T 0} : Finset V) ∈ A := by rwa [Finset.pair_comm] at hv
  have hTc : ({T 0, c} : Finset V) ∈ A := by rwa [Finset.pair_comm] at hc
  have h0 : ({T 0} : Finset V) ∈ A := vertex_mem_of_face A _ hv _ (by simp)
  obtain ⟨ms⟩ := slide p T hwall hupper hT hv hend
  obtain ⟨mc⟩ := cone T c (PolygonSource.length p) hcap hT h0 hc hcL
  obtain ⟨mw⟩ := wrap hwrap hxT hTc hcL hend hx
  let s := single hend
  exact ⟨(Moves.backtrack hxT p).symm.trans ((Moves.prepend hxT ms).trans
    ((Moves.prepend hxT ((Moves.backtrack hTc _).symm.trans
      (Moves.prepend hTc (Moves.suffix s mc)))).trans mw))⟩

theorem node_map {U : Type*} [LinearOrder U] {B : PreAbstractSimplicialComplex U}
    (f : V → U) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (i : ℕ) :
    PolygonSource.node (mapPath f hf p) i = f (PolygonSource.node p i) := by
  induction p generalizing i with
  | refl => rfl
  | cons h p ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

end Generic

variable {k : ℕ} (w : Fin k → Word)

/-- Cyclic private top labels of block `j`; `n` and `0` name the SAME top vertex. -/
def tops (j : Fin k) (i : ℕ) : Ambient := top j (i % (3*(w j).length))

theorem next_val {j : Fin k} (i : Position w j) : (next w i).val = (i.val+1) % (3*(w j).length) := by
  unfold next
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · have hn : i.val+1 = 3*(w j).length := by have hh := i.isLt; omega
    simp [hn]

theorem tops_lt {j : Fin k} (i : Position w j) : tops w j i.val = top j i.val := by
  simp [tops, Nat.mod_eq_of_lt i.isLt]

theorem tops_succ {j : Fin k} (i : Position w j) : tops w j (i.val+1) = top j (next w i).val := by
  rw [tops, next_val]

theorem tops_end (j : Fin k) : tops w j (3*(w j).length) = top j 0 := by simp [tops]
theorem tops_zero (j : Fin k) : tops w j 0 = top j 0 := by simp [tops]

theorem mapped_node (j : Fin k) (i : ℕ) :
    PolygonSource.node (mappedWord w j) i = base (bottom w j i) :=
  node_map base (baseMap w) _ i

theorem length_mapPath {U : Type*} [LinearOrder U] {B : PreAbstractSimplicialComplex U}
    {A : PreAbstractSimplicialComplex Ambient} (f : U → Ambient) (hf : B.map f ≤ A)
    {u v : U} (p : Path B u v) : PolygonSource.length (mapPath f hf p) = PolygonSource.length p := by
  induction p with
  | refl => rfl
  | cons h p ih => simp only [mapPath, PolygonSource.length, ih]

/-- Actual finite contraction of a NONEMPTY raw relator path in ANY complex containing
the rose and the block's wall/upper/cap cells (for instance the SAME target, or its
block subcomplex). Repeated letters, raw cancellations and `n = 3` are included. -/
theorem relator_moves_in (j : Fin k) (A : PreAbstractSimplicialComplex Ambient)
    (hbase : PresentationRose.rose.map base ≤ A)
    (hwall : ∀ q : Position w j, wall w q ∈ A) (hupper : ∀ q : Position w j, upper w q ∈ A)
    (hcap : ∀ q : Position w j, cap w q ∈ A) (he : w j ≠ [])
    (h0 : ({base 0} : Finset Ambient) ∈ A) :
    Nonempty (Moves (mapPath base hbase (PresentationRose.wordPath (w j))) (.refl (base 0) h0)) := by
  have hn : 0 < 3*(w j).length := by have := List.length_pos_iff_ne_nil.mpr he; omega
  let p0 : Position w j := ⟨0, hn⟩
  let p := mapPath base hbase (PresentationRose.wordPath (w j))
  have hlen : PolygonSource.length p = 3*(w j).length := by
    rw [length_mapPath, PresentationRose.word_length]
  have hnode : ∀ i, PolygonSource.node p i = base (bottom w j i) := fun i => node_map base hbase _ i
  have hverti : ∀ q : Position w j, ({top j q.val, base (bottom w j q.val)} : Finset Ambient) ∈ A :=
    fun q => pair_mem_of_face A _ (hwall q) _ _ (by simp [wall]) (by simp [wall])
  have hradi : ∀ q : Position w j, ({center j, top j q.val} : Finset Ambient) ∈ A :=
    fun q => pair_mem_of_face A _ (hcap q) _ _ (by simp [cap]) (by simp [cap])
  have htopi : ∀ q : Position w j, ({top j q.val, top j (next w q).val} : Finset Ambient) ∈ A :=
    fun q => pair_mem_of_face A _ (hupper q) _ _ (by simp [upper]) (by simp [upper])
  have hvert : ({tops w j 0, base 0} : Finset Ambient) ∈ A := by
    have h := hverti p0
    rwa [bottom_zero, ← tops_zero] at h
  have hvend : ({tops w j (PolygonSource.length p), base 0} : Finset Ambient) ∈ A := by
    rwa [hlen, tops_end, ← tops_zero]
  have hrad : ({center j, tops w j 0} : Finset Ambient) ∈ A := by
    rw [tops_zero]; exact hradi p0
  have hradend : ({center j, tops w j (PolygonSource.length p)} : Finset Ambient) ∈ A := by
    rwa [hlen, tops_end, ← tops_zero]
  apply contract p (tops w j) (center j)
  · intro i hi
    rw [hlen] at hi
    let q : Position w j := ⟨i, hi⟩
    rw [hnode, hnode, show i = q.val from rfl, tops_lt, ← bottom_next]
    exact mem_of_eq (hwall q) (by
      ext x; simp only [wall, Finset.mem_insert, Finset.mem_singleton]; tauto)
  · intro i hi
    rw [hlen] at hi
    let q : Position w j := ⟨i, hi⟩
    rw [hnode, show i = q.val from rfl, tops_lt, tops_succ, ← bottom_next]
    exact hupper q
  · intro i hi
    rw [hlen] at hi
    let q : Position w j := ⟨i, hi⟩
    rw [show i = q.val from rfl, tops_lt, tops_succ]
    exact hcap q
  · intro i hi
    rw [hlen] at hi
    let q : Position w j := ⟨i, hi⟩
    rw [show i = q.val from rfl, tops_lt, tops_succ]
    exact htopi q
  · exact hvert
  · exact hvend
  · exact hrad
  · exact hradend
  · rw [hlen, tops_end, tops_zero]

/-- Actual finite contraction of EVERY raw relator path in the SAME target,
including repeated letters, raw cancellations, `n = 3` and empty words. -/
theorem relator_moves (j : Fin k) :
    Nonempty (Moves (mappedWord w j) (.refl (base 0) (root w).property)) := by
  by_cases he : w j = []
  · have hp : PresentationRose.wordPath (w j) = PresentationRose.wordPath [] := by rw [he]
    unfold mappedWord
    rw [hp]
    exact ⟨.refl _⟩
  exact relator_moves_in w j (target w) (baseMap w) (wall_face w) (upper_face w) (cap_face w) he _

theorem relator_class (j : Fin k) :
    (Quotient.mk _ (mappedWord w j) : Loop (target w) (root w)) = 1 :=
  (null_iff_finite_moves (root w) _).mpr (relator_moves w j)

/-- The one-way evaluation kills each raw relator word, via actual moves only. -/
theorem eval_relator (j : Fin k) : evalLoops w (Targets.freeWord (w j)) = 1 := by
  rw [← class_word]
  exact relator_class w j

/-- `N <= ker E` from normal generation; no inverse map or Loop ~= G is used. -/
theorem kernel_contains (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) : Targets.N ≤ (evalLoops w).ker := by
  rw [← hv]
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨j, rfl⟩
  show v j ∈ (evalLoops w).ker
  rw [MonoidHom.mem_ker, ← hrep j]
  exact eval_relator w j

theorem x1_square_mem : (FreeGroup.of Gen.x1) ^ 2 ∈ Targets.N := by
  rw [MonoidHom.mem_ker, map_pow]
  exact Character.x1_square

theorem x1_square_class (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    (Quotient.mk _ (append (generatorLoop w .x1) (generatorLoop w .x1)) : Loop (target w) (root w)) = 1 := by
  have h := MonoidHom.mem_ker.mp (kernel_contains w v hv hrep x1_square_mem)
  rw [map_pow, evalLoops, FreeGroup.lift_apply_of, pow_two] at h
  exact h

/-- An actual finite x1-square TARGET move witness, extracted from the defined quotient. -/
def x1SquareMoves (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    Moves (append (generatorLoop w .x1) (generatorLoop w .x1)) (.refl (base 0) (root w).property) :=
  movesOfClassEq _ _ (x1_square_class w v hv hrep)

theorem x1_value_ne_one (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    value (tupleTransport w v hv hrep) (generatorLoop w .x1) ≠ 1 := by
  intro h
  have hd := original_x1_detected w v hv hrep
  rw [h] at hd
  norm_num at hd

/-- The x1 generator loop is NOT trivial in the actual loop group, but its square is. -/
theorem x1_class_ne_one (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    (Quotient.mk _ (generatorLoop w .x1) : Loop (target w) (root w)) ≠ 1 := by
  intro h
  apply x1_value_ne_one w v hv hrep
  have hh := congrArg (holonomy (tupleTransport w v hv hrep) (root w)) h
  rw [map_one] at hh
  exact hh

/-- For EVERY normally generating tuple with raw representatives, the DEFINED weighted
d2 of the SAME actual tagged target with ORIGINAL-character transport is NOT injective.
This is the target half of the fixed-presentation argument; the converse comparison
(algebraic Fox injectivity implies this d2 injective) remains open. -/
theorem target_d2_not_injective (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    ¬ Function.Injective (boundaryTwo (target w) (coeff (tupleTransport w v hv hrep))) :=
  LocalTraceUpdate.target_square_forces_noninjective (target w) (tupleTransport w v hv hrep)
    (generatorLoop w .x1) (x1SquareMoves w v hv hrep) (x1_value_ne_one w v hv hrep)

/-! Guards. -/

/-- Dropping the cap center is fatal: with no relators there are no triangles at all,
so scalar killing cannot substitute for the actual cap/wall/upper cells. -/
theorem relator_moves_need_cells : IsEmpty (Triangle (target (fun _ : Fin 0 => ([] : Word)))) :=
  no_relators_no_triangles _

/-- The wraparound top vertex is the SAME private vertex, not a fresh copy. -/
theorem wraparound_identified (j : Fin k) : tops w j (3*(w j).length) = tops w j 0 := by
  rw [tops_end, tops_zero]

/-- A raw x1 relator word stays nontrivial in the rose: scalar killing by a sign
character does not provide relator moves there (actual cells are required). -/
theorem rose_x1_relator_unkilled :
    (Quotient.mk _ (PresentationRose.generatorLoop .x1) : Loop PresentationRose.rose PresentationRose.root) ≠ 1 := by
  intro h
  have hh := congrArg (holonomy PresentationRose.originalTransport PresentationRose.root) h
  rw [map_one] at hh
  change value PresentationRose.originalTransport (PresentationRose.generatorLoop .x1) = 1 at hh
  have hd := PresentationRose.x1_detected
  rw [hh] at hd
  norm_num at hd

end D2RelationGap.PresentationMoves
