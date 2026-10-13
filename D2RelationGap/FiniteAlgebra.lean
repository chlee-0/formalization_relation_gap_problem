import D2RelationGap.Words

/-! Closed integer-pair computations for Z[z]/(z^2+z+1).
Cyclotomic and ComplexCharacter prove the faithful field/complex interpretation.
FoxSemantics proves the scan computes the actual evaluated free-group cocycle;
FoxRank identifies the distinguished determinant with Matrix.det and proves rank four. -/
namespace D2RelationGap

structure CycloPair where
  a : Int
  b : Int
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace CycloPair

def zero : CycloPair := ⟨0, 0⟩
def one : CycloPair := ⟨1, 0⟩
def zeta : CycloPair := ⟨0, 1⟩
def add (x y : CycloPair) : CycloPair := ⟨x.a + y.a, x.b + y.b⟩
def neg (x : CycloPair) : CycloPair := ⟨-x.a, -x.b⟩
def sub (x y : CycloPair) : CycloPair := add x (neg y)
def mul (x y : CycloPair) : CycloPair :=
  ⟨x.a*y.a-x.b*y.b, x.a*y.b+x.b*y.a-x.b*y.b⟩
def conj (x : CycloPair) : CycloPair := ⟨x.a-x.b, -x.b⟩

def rho : Gen → CycloPair
  | .x1 => ⟨-1, 0⟩
  | .a1 => zeta
  | .x2 => ⟨-1, -1⟩
  | .a2 => ⟨-1, 0⟩
  | .s => one

def letterValue (l : Letter) : CycloPair :=
  if l.positive then rho l.gen else conj (rho l.gen)

def wordValue (w : Word) : CycloPair :=
  w.foldl (fun p l => mul p (letterValue l)) one

abbrev Row := Gen → CycloPair

def scanStep (state : CycloPair × Row) (l : Letter) : CycloPair × Row :=
  let p' := mul state.1 (letterValue l)
  let contribution := if l.positive then state.1 else neg p'
  (p', fun g => if g = l.gen then add (state.2 g) contribution else state.2 g)

def foxRow (w : Word) : Row := (w.foldl scanStep (one, fun _ => zero)).2

def foxTable : List (List CycloPair) :=
  sourceWords.map (fun w => allGens.map (foxRow w))

def expectedFox : List (List CycloPair) :=
  [[⟨1,-1⟩, ⟨-2,0⟩, zero, zero, zero],
   [zero, zero, ⟨2,0⟩, ⟨-2,-1⟩, zero],
   [one, zero, zero, ⟨-1,0⟩, zero],
   [zero, ⟨-1,-1⟩, one, zero, ⟨2,1⟩]]

def dot (x y : Row) : CycloPair :=
  allGens.foldl (fun a g => add a (mul (x g) (y g))) zero

def boundaryOne (g : Gen) : CycloPair := sub (rho g) one

def eraseAt {α : Type} (i : Nat) (xs : List α) : List α :=
  xs.take i ++ xs.drop (i+1)

/-- Total recursive determinant. Dimension checks precede its mathematical use. -/
def det : Nat → List (List CycloPair) → CycloPair
  | 0, _ => one
  | _n+1, [] => zero
  | n+1, row :: rows =>
    (List.range (n+1)).foldl (fun a j =>
      let term := mul (row.getD j zero) (det n (rows.map (eraseAt j)))
      add a (if j % 2 = 0 then term else neg term)) zero

def maximalMinors : List CycloPair :=
  (List.range 5).map (fun j => det 4 (foxTable.map (eraseAt j)))

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem roots_are_units :
    allGens.all (fun g => mul (rho g) (conj (rho g)) == one) = true := by decide

theorem relators_evaluate_to_one : allWords.map wordValue = List.replicate 6 one := by decide

theorem fox_table_agrees : foxTable = expectedFox := by decide

theorem fox_chain_check :
    allWords.map (fun w => dot (foxRow w) boundaryOne) = List.replicate 6 zero := by decide

theorem maximal_minors_agree :
    maximalMinors = [⟨8,4⟩, ⟨-6,0⟩, ⟨6,6⟩, ⟨-8,-4⟩, zero] := by decide

theorem distinguished_minor :
    det 4 (foxTable.map (eraseAt 3)) = ⟨-8,-4⟩ := by decide

theorem distinguished_minor_encoding_nonzero : (⟨-8,-4⟩ : CycloPair) ≠ zero := by decide

/-- Corrupt the expected derivative with respect to a1. -/
theorem corrupted_fox_entry_rejected : foxRow r1 .a1 ≠ ⟨-1,0⟩ := by decide

/-- Removing one occurrence of a2 from r3 changes its character value. -/
theorem corrupted_relator_rejected :
    wordValue ([pos .x1] ++ List.replicate 12 (D2RelationGap.neg .a2)) ≠ one := by decide

/-- Reverse the sign of the distinguished minor. -/
theorem corrupted_minor_rejected :
    det 4 (foxTable.map (eraseAt 3)) ≠ ⟨8,4⟩ := by decide

end CycloPair
end D2RelationGap
