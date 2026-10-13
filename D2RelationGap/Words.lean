import Std

/-! Executable words; the semantic bridge is proved in WordSemantics and SourceIdentities.
Generator order and all relations are OpenAI's, pinned in dependencies.json.
No arbitrary integer is silently interpreted as a valid generator. -/
namespace D2RelationGap

inductive Gen where
  | x1 | a1 | x2 | a2 | s
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

structure Letter where
  gen : Gen
  positive : Bool
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

abbrev Word := List Letter

def pos (g : Gen) : Letter := ⟨g, true⟩
def neg (g : Gen) : Letter := ⟨g, false⟩
def invert (l : Letter) : Letter := ⟨l.gen, !l.positive⟩
def inverseWord (w : Word) : Word := w.reverse.map invert

def reducePush (stack : Word) (l : Letter) : Word :=
  match stack with
  | [] => [l]
  | h :: t => if h == invert l then t else l :: stack

def reduceWord (w : Word) : Word := (w.foldl reducePush []).reverse

def wordPower (w : Word) (n : Nat) : Word :=
  reduceWord ((List.replicate n w).flatten)

def r1 : Word := [pos .x1, pos .a1, neg .x1] ++ List.replicate 4 (neg .a1)
def r2 : Word := [pos .x2, pos .a2, neg .x2] ++ List.replicate 3 (neg .a2)
def r3 : Word := [pos .x1] ++ List.replicate 13 (neg .a2)
def r4 : Word := [pos .s, pos .x2, neg .s] ++ List.replicate 5 (neg .a1)
def t1 : Word := List.replicate 2 (pos .x1)
def t2 : Word := List.replicate 3 (pos .x2)
def sourceWords : List Word := [r1, r2, r3, r4]
def allWords : List Word := sourceWords ++ [t1, t2]
def allGens : List Gen := [.x1, .a1, .x2, .a2, .s]

def rules : List (Word × Word) :=
  [([pos .x1, pos .a1, neg .x1], List.replicate 4 (pos .a1)),
   ([pos .x2, pos .a2, neg .x2], List.replicate 3 (pos .a2)),
   ([pos .x1], List.replicate 13 (pos .a2)),
   ([pos .s, pos .x2, neg .s], List.replicate 5 (pos .a1))]

structure RewriteStep where
  rule : Nat
  power : Nat
  position : Nat
  reverse : Bool
  deriving DecidableEq, BEq, Repr

structure WordTrace where
  start : Word
  target : Word
  steps : List RewriteStep
  deriving DecidableEq, BEq, Repr

def rewriteStep (w : Word) (s : RewriteStep) : Option Word := do
  let (a, b) ← rules[s.rule]?
  if s.power == 0 then none else do
    let a := wordPower a s.power
    let b := wordPower b s.power
    let (lhs, rhs) := if s.reverse then (b, a) else (a, b)
    if (w.drop s.position).take lhs.length == lhs then
      some (reduceWord (w.take s.position ++ rhs ++ w.drop (s.position + lhs.length)))
    else none

def replay (w : Word) : List RewriteStep → Option Word
  | [] => some (reduceWord w)
  | s :: ss => (rewriteStep (reduceWord w) s).bind (fun w' => replay w' ss)

def checkTrace (t : WordTrace) : Bool := replay t.start t.steps == some (reduceWord t.target)

end D2RelationGap
