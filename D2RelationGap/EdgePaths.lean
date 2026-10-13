import D2RelationGap.SimplicialTransport
import Mathlib.Tactic.FinCases

/-!
Finite paths in actual simplicial faces, finite move witnesses and unit holonomy.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying groups, character/Fox data and tower obstruction. Presentation/geometry
adequacy and transport from original G remain open; no relation-gap theorem is asserted.
-/
noncomputable section
namespace D2RelationGap.EdgePaths
open OrientedSimplices SimplicialTransport
variable {V K : Type*} [LinearOrder V] [Field K]

/-- A genuinely finite sequence of actual edges with specified endpoints.
Repeated consecutive vertices are allowed; even a constant path has an active vertex. -/
inductive Path (A : PreAbstractSimplicialComplex V) : V → V → Type _
  | refl (u : V) (hu : ({u} : Finset V) ∈ A) : Path A u u
  | cons {u v w : V} (h : ({u, v} : Finset V) ∈ A) (p : Path A v w) : Path A u w

def append {A : PreAbstractSimplicialComplex V} {u v w : V}
    (p : Path A u v) (q : Path A v w) : Path A u w :=
  match p with
  | .refl _ _ => q
  | .cons h r => .cons h (append r q)

def value {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v : V} : Path A u v → Kˣ
  | .refl _ _ => 1
  | @Path.cons _ _ _ u w _ _ p => tau.unit u w * value tau p

theorem value_append {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v w : V} (p : Path A u v) (q : Path A v w) :
    value tau (append p q) = value tau p * value tau q := by
  induction p with
  | refl => simp [append, value]
  | cons h p ih => simp [append, value, ih, mul_assoc]

/-- Finite derivations from actual local moves, not a homotopy or nullhomotopy oracle. -/
inductive Moves {A : PreAbstractSimplicialComplex V} :
    {u v : V} → Path A u v → Path A u v → Type _
  | refl {u v} (p : Path A u v) : Moves p p
  | symm {u v} {p q : Path A u v} : Moves p q → Moves q p
  | trans {u v} {p q r : Path A u v} : Moves p q → Moves q r → Moves p r
  | stutter {u v} (h : ({u} : Finset V) ∈ A) (p : Path A u v) :
      Moves (.cons (by simpa using h) p) p
  | backtrack {u v w} (h : ({u, v} : Finset V) ∈ A) (p : Path A u w) :
      Moves (.cons h (.cons (by simpa [Finset.pair_comm] using h) p)) p
  | triangle {u v w z} (h : ({u, v, w} : Finset V) ∈ A) (p : Path A w z) :
      Moves (.cons (pair_mem_of_face A _ h u v (by simp) (by simp))
        (.cons (pair_mem_of_face A _ h v w (by simp) (by simp)) p))
        (.cons (pair_mem_of_face A _ h u w (by simp) (by simp)) p)
  | prepend {u v w} (h : ({u, v} : Finset V) ∈ A) {p q : Path A v w} :
      Moves p q → Moves (.cons h p) (.cons h q)
  | suffix {u v w} {p q : Path A u v} (r : Path A v w) :
      Moves p q → Moves (append p r) (append q r)

theorem value_moves {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v : V} {p q : Path A u v} (m : Moves p q) : value tau p = value tau q := by
  induction m with
  | refl => rfl
  | symm m ih => exact ih.symm
  | trans m n ih jh => exact ih.trans jh
  | stutter h p => simp [value, diagonal_unit tau _ h]
  | backtrack h p => simp [value, unit_reverse tau _ _ h, ← mul_assoc]
  | triangle h p => simp [value, ← mul_assoc, tau.flat _ _ _ h]
  | prepend h m ih => simp [value, ih]
  | suffix r m ih => simp [value_append, ih]

def pathSetoid (A : PreAbstractSimplicialComplex V) (u v : V) : Setoid (Path A u v) where
  r p q := Nonempty (Moves p q)
  iseqv := ⟨fun p => ⟨.refl p⟩, fun ⟨m⟩ => ⟨.symm m⟩,
    fun ⟨m⟩ ⟨n⟩ => ⟨.trans m n⟩⟩

abbrev PathClass (A : PreAbstractSimplicialComplex V) (u v : V) := Quotient (pathSetoid A u v)

theorem class_eq_iff_moves {A : PreAbstractSimplicialComplex V} {u v : V}
    (p q : Path A u v) : Quotient.mk (pathSetoid A u v) p = Quotient.mk _ q ↔
      Nonempty (Moves p q) := Quotient.eq

/-- Quotient equality supplies an actual finite move derivation by choice.
This is adequacy ONLY for the defined finite-path quotient, not for pi1 or G. -/
def movesOfClassEq {A : PreAbstractSimplicialComplex V} {u v : V} (p q : Path A u v)
    (he : Quotient.mk (pathSetoid A u v) p = Quotient.mk _ q) : Moves p q :=
  Classical.choice ((class_eq_iff_moves p q).mp he)

def classValue {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v : V} : PathClass A u v → Kˣ :=
  Quotient.lift (value tau) (fun _ _ ⟨m⟩ => value_moves tau m)

theorem classValue_mk {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {u v : V} (p : Path A u v) : classValue tau (Quotient.mk _ p) = value tau p := rfl

section Maps
variable {U : Type*} [LinearOrder U]
def mapPath {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) {u v : U} : Path A u v → Path B (f u) (f v)
  | .refl u hu => .refl (f u) (by simpa using image_mem f hf {u} hu)
  | .cons h p => .cons (by simpa using image_mem f hf _ h) (mapPath f hf p)

theorem value_mapPath {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B)
    {u v : U} (p : Path A u v) : value tau (mapPath f hf p) = value (pullback tau f hf) p := by
  induction p with
  | refl => rfl
  | cons h p ih => simp [mapPath, value, pullback, ih]
theorem mapPath_append {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) {u v w : U} (p : Path A u v) (q : Path A v w) :
    mapPath f hf (append p q) = append (mapPath f hf p) (mapPath f hf q) := by
  induction p with
  | refl => rfl
  | cons h p ih => simp [append, mapPath, ih]

def mapMoves {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) {u v : U} {p q : Path A u v} (m : Moves p q) :
    Moves (mapPath f hf p) (mapPath f hf q) := by
  induction m with
  | refl => exact .refl _
  | symm m ih => exact .symm ih
  | trans m n ih jh => exact .trans ih jh
  | stutter h p => exact .stutter (by simpa using image_mem f hf _ h) _
  | backtrack h p => exact .backtrack (by simpa using image_mem f hf _ h) _
  | triangle h p => exact .triangle (by simpa using image_mem f hf _ h) _
  | prepend h m ih => exact .prepend (by simpa using image_mem f hf _ h) ih
  | suffix r m ih => simpa [mapPath_append] using Moves.suffix (mapPath f hf r) ih

def mapClass {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) {u v : U} : PathClass A u v → PathClass B (f u) (f v) :=
  Quotient.map (mapPath f hf) (fun _ _ ⟨m⟩ => ⟨mapMoves f hf m⟩)

theorem classValue_mapClass {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B)
    {u v : U} (c : PathClass A u v) :
    classValue tau (mapClass f hf c) = classValue (pullback tau f hf) c := by
  refine Quotient.inductionOn c ?_
  intro p
  exact value_mapPath tau f hf p

end Maps

/-- Three edges with NO filled triangle; a nontrivial loop must not be shortened
across a nonexistent face. -/
def cycleComplex : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s.card ≤ 2}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, (Finset.card_le_card hts).trans hs.2⟩

def cycleTransport : Transport (K := ℚ) cycleComplex where
  unit u v := if (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) then -1 else 1
  flat := by
    intro u v w h
    change ({u, v, w} : Finset (Fin 3)).Nonempty ∧ ({u, v, w} : Finset (Fin 3)).card ≤ 2 at h
    fin_cases u <;> fin_cases v <;> fin_cases w <;>
      simp_all

def cycleLoop : Path cycleComplex 0 0 :=
  .cons (u := 0) (v := 1) (by change ({0, 1} : Finset (Fin 3)).Nonempty ∧ _; decide)
    (.cons (v := 2) (by change ({1, 2} : Finset (Fin 3)).Nonempty ∧ _; decide)
      (.cons (by change ({2, 0} : Finset (Fin 3)).Nonempty ∧ _; decide)
        (.refl 0 (by change ({0} : Finset (Fin 3)).Nonempty ∧ _; decide))))

theorem cycleLoop_value : value cycleTransport cycleLoop = -1 := by
  norm_num [value, cycleTransport, cycleLoop]

theorem nonexistent_triangle_shortcut_rejected :
    ¬ Nonempty (Moves cycleLoop (Path.refl 0 (by change ({0} : Finset (Fin 3)).Nonempty ∧ _; decide))) := by
  rintro ⟨m⟩
  have h := value_moves cycleTransport m
  have hc := congrArg (fun x : ℚˣ => (x : ℚ)) h
  norm_num [cycleLoop_value, value] at hc

end D2RelationGap.EdgePaths
