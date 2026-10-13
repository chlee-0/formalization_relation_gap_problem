import D2RelationGap.ArbTransport
import D2RelationGap.PresentationMoves

/-!
Actual finite relator contractions on the arbitrary-rank tagged target, the one-way
kernel containment, the detecting square and non-injectivity of the defined d2.
Ports the specialisation part of `PresentationMoves`; the generic collar contraction
`PresentationMoves.contract` is reused unchanged. OpenAI, "A Counterexample to Wall's
D(2) Problem" (October 6, 2026), openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
-/
noncomputable section
namespace D2RelationGap.ArbMoves
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops
open ArbCells ArbTransport
open PresentationMoves (contract node_map mem_of_eq)
variable {m k : ℕ} (w : Fin k → ArbRose.AWord m)

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
    (hbase : (ArbRose.rose m).map base ≤ A)
    (hwall : ∀ q : Position w j, wall w q ∈ A) (hupper : ∀ q : Position w j, upper w q ∈ A)
    (hcap : ∀ q : Position w j, cap w q ∈ A) (he : w j ≠ [])
    (h0 : ({base 0} : Finset Ambient) ∈ A) :
    Nonempty (Moves (mapPath base hbase (ArbRose.wordPath (w j))) (.refl (base 0) h0)) := by
  have hn : 0 < 3*(w j).length := by have := List.length_pos_iff_ne_nil.mpr he; omega
  let p0 : Position w j := ⟨0, hn⟩
  let p := mapPath base hbase (ArbRose.wordPath (w j))
  have hlen : PolygonSource.length p = 3*(w j).length := by
    rw [length_mapPath, ArbRose.word_length]
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
  · have hp : ArbRose.wordPath (w j) = ArbRose.wordPath [] := by rw [he]
    unfold mappedWord
    rw [hp]
    exact ⟨.refl _⟩
  exact relator_moves_in w j (target w) (baseMap w) (wall_face w) (upper_face w) (cap_face w) he _

theorem relator_class (j : Fin k) :
    (Quotient.mk _ (mappedWord w j) : Loop (target w) (root w)) = 1 :=
  (null_iff_finite_moves (root w) _).mpr (relator_moves w j)

theorem eval_relator (j : Fin k) : evalLoops w (ArbRose.freeWord (w j)) = 1 := by
  rw [← class_word]
  exact relator_class w j

/-- The one-way evaluation kills the normal closure of the raw relators. -/
theorem kernel_contains (v : Fin k → FreeGroup (Fin m))
    (hrep : ∀ j, ArbRose.freeWord (w j) = v j) :
    Subgroup.normalClosure (Set.range v) ≤ (evalLoops w).ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨j, rfl⟩
  show v j ∈ (evalLoops w).ker
  rw [MonoidHom.mem_ker, ← hrep j]
  exact eval_relator w j

theorem rose_wordPath_append (u v : ArbRose.AWord m) :
    ArbRose.wordPath (u ++ v) = append (ArbRose.wordPath u) (ArbRose.wordPath v) := by
  induction u with
  | nil => rfl
  | cons l u ih => simp only [List.cons_append, ArbRose.wordPath, ih, append_assoc]

theorem freeWord_append (u v : ArbRose.AWord m) :
    ArbRose.freeWord (u ++ v) = ArbRose.freeWord u * ArbRose.freeWord v := by
  simp [ArbRose.freeWord, List.map_append, List.prod_append]

/-- Actual finite TARGET moves for the doubled raw-word loop of any word whose square
lies in the evaluation kernel. -/
theorem square_moves (u : ArbRose.AWord m) (h : (ArbRose.freeWord u)^2 ∈ (evalLoops w).ker) :
    Nonempty (Moves (append (wordPath w u) (wordPath w u)) (.refl (base 0) (root w).property)) := by
  have hc : (Quotient.mk _ (wordPath w (u ++ u)) : Loop (target w) (root w)) = 1 := by
    rw [class_word, freeWord_append, ← pow_two]
    exact MonoidHom.mem_ker.mp h
  have hp : wordPath w (u ++ u) = append (wordPath w u) (wordPath w u) := by
    unfold wordPath
    rw [rose_wordPath_append, mapPath_append]
  rw [hp] at hc
  exact (null_iff_finite_moves (root w) _).mp hc

/-- A detecting square-null raw-word loop makes the defined weighted d2 NOT injective. -/
theorem d2_not_injective {K : Type} [Field K] (q : Fin m → Kˣ)
    (hk : ∀ j, value (ArbRose.transport q) (ArbRose.wordPath (w j)) = 1) (u : ArbRose.AWord m)
    (hsq : (ArbRose.freeWord u)^2 ∈ (evalLoops w).ker)
    (hd : value (transport w q hk) (wordPath w u) ≠ 1) :
    ¬ Function.Injective (boundaryTwo (target w) (coeff (transport w q hk))) := by
  obtain ⟨mv⟩ := square_moves w u hsq
  exact LocalTraceUpdate.target_square_forces_noninjective (target w) (transport w q hk) _ mv hd

end D2RelationGap.ArbMoves
